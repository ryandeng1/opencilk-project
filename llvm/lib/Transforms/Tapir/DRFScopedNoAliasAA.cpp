//===- DRFScopedNoAliasAA.cpp - DRF-based scoped-noalias metadata ---------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Adds scoped-noalias metadata to memory accesses based on Tapir's parallel
// control flow constructs and the assumption that the function is data-race
// free.
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Tapir/DRFScopedNoAliasAA.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/MapVector.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/DataRaceFreeAliasAnalysis.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/MemoryLocation.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/Analysis/TapirTaskInfo.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/IR/Metadata.h"
#include "llvm/InitializePasses.h"
#include "llvm/Pass.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/Tapir.h"
#include <algorithm>
#include <memory>
#include <tuple>

#define DEBUG_TYPE "drf-scoped-noalias"

using namespace llvm;

static cl::opt<bool> EnableDRFAATaskScopeMetadata(
    "enable-drf-aa-task-scope-metadata", cl::init(true), cl::Hidden,
    cl::desc("Materialize task-structure scoped-noalias metadata for ordinary "
             "memory accesses (default = on)"));

static cl::opt<bool> EnableDRFAAProvenPairMetadata(
    "enable-drf-aa-proven-pair-metadata", cl::init(true), cl::Hidden,
    cl::desc("Materialize pair-specific scoped-noalias metadata for "
             "DRFAA-proven memory access pairs (default = on)"));

static cl::opt<bool> EnableDRFAASiblingWitnessMetadata(
    "enable-drf-aa-sibling-witness-metadata", cl::init(true), cl::Hidden,
    cl::desc("Materialize the DRF sibling-witness access-pair proofs as "
             "scoped-noalias metadata so that later passes inherit them "
             "(default = on; needs -enable-drf-aa-sibling-witness)"));

static cl::opt<unsigned> MaxDRFAAProvenPairAccessesPerTask(
    "drf-aa-proven-pair-max-accesses-per-task", cl::init(512), cl::Hidden,
    cl::desc("Maximum simple memory accesses retained per DRF proof bucket "
             "when materializing pair metadata"));

static cl::opt<unsigned> MaxDRFAAProvenPairChecksPerTask(
    "drf-aa-proven-pair-max-checks-per-task", cl::init(65536), cl::Hidden,
    cl::desc("Maximum access pairs inspected for each pair of DRF proof "
             "buckets when materializing pair metadata"));

static cl::opt<unsigned> MaxDRFAAProvenPairChecksPerParallelLoop(
    "drf-aa-proven-pair-max-checks-per-parallel-loop", cl::init(65536),
    cl::Hidden,
    cl::desc("Maximum total DRF pair-proof queries in one logically-parallel "
             "loop context"));

STATISTIC(NumSiblingWitnessPairsMaterialized,
          "Number of DRF sibling-witness access pairs turned into metadata");
STATISTIC(NumSiblingWitnessPairsAlreadyEncoded,
          "Number of DRF sibling-witness access pairs already in metadata");
STATISTIC(NumTaskScopeAccessesConsidered,
          "Number of ordinary accesses considered for DRF task scopes");
STATISTIC(NumTaskScopeAccessesAnnotated,
          "Number of accesses annotated with DRF task scopes");
STATISTIC(NumTaskScopeAccessesRejected,
          "Number of non-ordinary accesses rejected from DRF task scopes");
STATISTIC(NumPairAccessesBucketed,
          "Number of accesses retained in DRF pair-proof buckets");
STATISTIC(NumPairAccessBudgetDrops,
          "Number of accesses dropped by a DRF pair-proof bucket cap");
STATISTIC(NumPairCandidateChecks,
          "Number of distinct DRF pair-proof queries performed");
STATISTIC(NumPairCheckBudgetDrops,
          "Number of DRF bucket pairs truncated by the pair-check cap");
STATISTIC(NumPairContextBudgetDrops,
          "Number of DRF parallel-loop contexts truncated by the total cap");
STATISTIC(NumPairNoAliasProofs,
          "Number of DRF NoAlias pair proofs materialized");
STATISTIC(NumPairNoCrossIterationOnly,
          "Number of DRF pairs classified only NoCrossIteration");
STATISTIC(NumPairScopesMaterialized,
          "Number of compact DRF per-access alias scopes materialized");
STATISTIC(NumGeneratedMetadataOperandsRemoved,
          "Number of stale DRF metadata operands removed before rebuilding");

static constexpr StringLiteral GeneratedDomainsMDName =
    "drfaa.generated.alias.scope.domains";
static constexpr StringLiteral LegacyPairDoneMDName =
    "drfaa.proven.pair.noalias.done";

struct TaskAliasScopeInfo {
  Metadata *AllAccesses = nullptr;
  Metadata *Writes = nullptr;
};

struct ActiveTaskAliasScopes {
  SmallVector<Metadata *, 4> AllAccesses;
  SmallVector<Metadata *, 4> Writes;
  SmallVector<Metadata *, 4> ParallelAllAccesses;
  SmallVector<Metadata *, 4> ParallelWrites;
};

/// Materialize task-structural and pair-proven DRF scoped-noalias metadata.
class DRFScopedNoAliasImpl {
public:
  DRFScopedNoAliasImpl(Function &F, TaskInfo &TI, LoopInfo *LI,
                       ScalarEvolution &SE)
      : F(F), TI(TI), LI(LI), SE(SE) {}

  ~DRFScopedNoAliasImpl() {
    destroyDRFAADeltaSetProofCache(DeltaSetProofCache);
  }

  bool run();

private:
  bool removeGeneratedMetadata();
  bool recordGeneratedDomains();
  bool populateTaskScopeNoAlias();
  bool populateProvenPairNoAlias();
  bool populateSiblingWitnessNoAlias();

  bool populateSubTaskScopeNoAlias(
      const Task *T, ActiveTaskAliasScopes &ActiveScopes,
      DenseMap<const Task *, TaskAliasScopeInfo> &TaskToScopes);

  bool populateTaskScopeNoAliasInBlock(const Task *T, BasicBlock *BB,
                                       ActiveTaskAliasScopes &ActiveScopes);

  Function &F;
  TaskInfo &TI;
  LoopInfo *LI;
  ScalarEvolution &SE;
  DRFAADeltaSetProofCache *DeltaSetProofCache = nullptr;
  SmallVector<Metadata *, 16> GeneratedDomains;

  MaybeParallelTasks MPTasks;
};

namespace {
struct DRFScopedNoAliasWrapperPass : public FunctionPass {
  static char ID; // Pass identification, replacement for typeid
  explicit DRFScopedNoAliasWrapperPass() : FunctionPass(ID) {
    initializeDRFScopedNoAliasWrapperPassPass(*PassRegistry::getPassRegistry());
  }

  StringRef getPassName() const override {
    return "Assume DRF to Add Scoped-No-Alias Metadata";
  }

  bool runOnFunction(Function &F) override;

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<LoopInfoWrapperPass>();
    AU.addPreserved<LoopInfoWrapperPass>();
    AU.addRequired<ScalarEvolutionWrapperPass>();
    AU.addPreserved<ScalarEvolutionWrapperPass>();
    AU.addRequired<TaskInfoWrapperPass>();
    AU.addPreserved<TaskInfoWrapperPass>();
  }
};
} // End of anonymous namespace

char DRFScopedNoAliasWrapperPass::ID = 0;
INITIALIZE_PASS_BEGIN(DRFScopedNoAliasWrapperPass, "drf-scoped-noalias",
                      "Add DRF-based scoped-noalias metadata", false, false)
INITIALIZE_PASS_DEPENDENCY(LoopInfoWrapperPass)
INITIALIZE_PASS_DEPENDENCY(ScalarEvolutionWrapperPass)
INITIALIZE_PASS_DEPENDENCY(TaskInfoWrapperPass)
INITIALIZE_PASS_END(DRFScopedNoAliasWrapperPass, "drf-scoped-noalias",
                    "Add DRF-based scoped-noalias metadata", false, false)

static MDNode *
removeScopesFromDomains(MDNode *Scopes,
                        const SmallPtrSetImpl<const MDNode *> &GeneratedDomains,
                        unsigned &NumRemoved) {
  if (!Scopes)
    return nullptr;

  SmallVector<Metadata *, 8> Kept;
  for (const MDOperand &Op : Scopes->operands()) {
    Metadata *MD = Op.get();
    const auto *Scope = dyn_cast_or_null<MDNode>(MD);
    const MDNode *Domain = Scope ? AliasScopeNode(Scope).getDomain() : nullptr;
    if (Domain && GeneratedDomains.contains(Domain)) {
      ++NumRemoved;
      continue;
    }
    Kept.push_back(MD);
  }

  if (Kept.size() == Scopes->getNumOperands())
    return Scopes;
  return Kept.empty() ? nullptr : MDNode::get(Scopes->getContext(), Kept);
}

bool DRFScopedNoAliasImpl::removeGeneratedMetadata() {
  MDNode *DomainsMD = F.getMetadata(GeneratedDomainsMDName);
  bool Changed = false;
  if (DomainsMD) {
    SmallPtrSet<const MDNode *, 16> Domains;
    for (const MDOperand &Op : DomainsMD->operands())
      if (const auto *Domain = dyn_cast_or_null<MDNode>(Op.get()))
        Domains.insert(Domain);

    unsigned NumRemoved = 0;
    for (BasicBlock &BB : F) {
      for (Instruction &I : BB) {
        for (unsigned Kind :
             {LLVMContext::MD_alias_scope, LLVMContext::MD_noalias}) {
          MDNode *Old = I.getMetadata(Kind);
          MDNode *New = removeScopesFromDomains(Old, Domains, NumRemoved);
          if (New != Old) {
            I.setMetadata(Kind, New);
            Changed = true;
          }
        }
      }
    }
    NumGeneratedMetadataOperandsRemoved += NumRemoved;
    F.setMetadata(GeneratedDomainsMDName, nullptr);
    Changed = true;
  }

  // Older revisions used a permanent done bit.  Clear it so the metadata can
  // be reconstructed from the current IR, although legacy scopes themselves
  // cannot be identified reliably without their owning-domain marker.
  if (F.getMetadata(LegacyPairDoneMDName)) {
    F.setMetadata(LegacyPairDoneMDName, nullptr);
    Changed = true;
  }
  return Changed;
}

bool DRFScopedNoAliasImpl::recordGeneratedDomains() {
  if (GeneratedDomains.empty())
    return false;
  F.setMetadata(GeneratedDomainsMDName,
                MDNode::get(F.getContext(), GeneratedDomains));
  return true;
}

bool DRFScopedNoAliasImpl::populateTaskScopeNoAliasInBlock(
    const Task *T, BasicBlock *BB, ActiveTaskAliasScopes &ActiveScopes) {
  LLVM_DEBUG(dbgs() << "Processing block " << BB->getName() << " in task "
                    << T->getEntry()->getName() << "\n");
  bool Changed = false;
  for (Instruction &I : *BB) {
    if (!I.mayReadOrWriteMemory())
      continue;

    // Scoped noalias is a whole-location assertion.  Calls, atomics, volatile
    // accesses, and hyperobject views have synchronization or view semantics
    // that the task-structure proof does not model, so never annotate them.
    if (!isOrdinaryDRFMemoryAccess(&I)) {
      ++NumTaskScopeAccessesRejected;
      continue;
    }
    ++NumTaskScopeAccessesConsidered;

    const Value *Ptr = getLoadStorePointerOperand(&I);
    SmallVector<const Value *, 4> Objects;
    getUnderlyingObjects(const_cast<Value *>(Ptr), Objects, LI);
    bool UsesObjectOutsideTask = false;
    for (const Value *O : Objects) {
      LLVM_DEBUG(dbgs() << "Checking object " << *O << "\n");
      if (const Instruction *OI = dyn_cast<Instruction>(O))
        if (TI.getTaskFor(OI->getParent()) == T)
          continue;

      UsesObjectOutsideTask = true;
      break;
    }

    if (!UsesObjectOutsideTask) {
      LLVM_DEBUG(dbgs() << "Instruction " << I
                        << " does not use object outside of task "
                        << T->getEntry()->getName() << "\n");
      continue;
    }

    bool IsWrite = isa<StoreInst>(I);
    ArrayRef<Metadata *> NoAliasScopes = IsWrite
                                             ? ActiveScopes.ParallelAllAccesses
                                             : ActiveScopes.ParallelWrites;
    bool Attached = false;
    if (!NoAliasScopes.empty()) {
      I.setMetadata(
          LLVMContext::MD_noalias,
          MDNode::concatenate(I.getMetadata(LLVMContext::MD_noalias),
                              MDNode::get(F.getContext(), NoAliasScopes)));
      Attached = true;
    }

    // Two scopes per task encode the DRF rule without separating legal
    // read/read pairs.  Every access enters the all-access scope, while only
    // stores enter the write scope.  A parallel read excludes write scopes;
    // a parallel write excludes all-access scopes.
    SmallVector<Metadata *, 8> AliasScopes(ActiveScopes.AllAccesses.begin(),
                                           ActiveScopes.AllAccesses.end());
    if (IsWrite)
      AliasScopes.append(ActiveScopes.Writes.begin(),
                         ActiveScopes.Writes.end());
    if (!AliasScopes.empty()) {
      I.setMetadata(
          LLVMContext::MD_alias_scope,
          MDNode::concatenate(I.getMetadata(LLVMContext::MD_alias_scope),
                              MDNode::get(F.getContext(), AliasScopes)));
      Attached = true;
    }

    if (Attached) {
      ++NumTaskScopeAccessesAnnotated;
      Changed = true;
    }
  }
  return Changed;
}

bool DRFScopedNoAliasImpl::populateSubTaskScopeNoAlias(
    const Task *T, ActiveTaskAliasScopes &ActiveScopes,
    DenseMap<const Task *, TaskAliasScopeInfo> &TaskToScopes) {
  bool Changed = false;
  size_t OrigParallelAllSize = ActiveScopes.ParallelAllAccesses.size();
  size_t OrigParallelWriteSize = ActiveScopes.ParallelWrites.size();

  // FIXME? Separately handle shared EH spindles.
  for (Spindle *S : depth_first<InTask<Spindle *>>(T->getEntrySpindle())) {
    for (const Task *MPT : MPTasks.TaskList[S]) {
      // Don't record noalias scopes for maybe-parallel tasks that enclose the
      // spindle.  These cases arise from parallel loops, which need special
      // alias analysis anyway (e.g., LoopAccessAnalysis).
      if (MPT->encloses(S->getEntry()))
        continue;
      auto ScopeIt = TaskToScopes.find(MPT);
      assert(ScopeIt != TaskToScopes.end() && "missing task alias scopes");
      ActiveScopes.ParallelAllAccesses.push_back(ScopeIt->second.AllAccesses);
      ActiveScopes.ParallelWrites.push_back(ScopeIt->second.Writes);
    }
    // Populate instructions in spindle with scoped-noalias information.
    for (BasicBlock *BB : S->blocks())
      Changed |= populateTaskScopeNoAliasInBlock(T, BB, ActiveScopes);

    // Remove the noalias scopes for this spindle.
    ActiveScopes.ParallelAllAccesses.erase(
        ActiveScopes.ParallelAllAccesses.begin() + OrigParallelAllSize,
        ActiveScopes.ParallelAllAccesses.end());
    ActiveScopes.ParallelWrites.erase(ActiveScopes.ParallelWrites.begin() +
                                          OrigParallelWriteSize,
                                      ActiveScopes.ParallelWrites.end());

    // For each successor spindle in a subtask, recursively populate the
    // scoped-noalias information in that subtask.
    for (Spindle *Succ : successors(S)) {
      if (S->succInSubTask(Succ)) {
        auto ScopeIt = TaskToScopes.find(Succ->getParentTask());
        assert(ScopeIt != TaskToScopes.end() && "missing subtask alias scopes");
        const TaskAliasScopeInfo &SubTaskScopes = ScopeIt->second;
        ActiveScopes.AllAccesses.push_back(SubTaskScopes.AllAccesses);
        ActiveScopes.Writes.push_back(SubTaskScopes.Writes);
        Changed |= populateSubTaskScopeNoAlias(Succ->getParentTask(),
                                               ActiveScopes, TaskToScopes);
        ActiveScopes.AllAccesses.pop_back();
        ActiveScopes.Writes.pop_back();
      }
    }
  }

  return Changed;
}

static void createTaskDomainsAndFullScopes(
    const Task *T, MDBuilder &MDB, const Twine ParentName,
    DenseMap<const Task *, MDNode *> &TaskToDomain,
    DenseMap<const Task *, TaskAliasScopeInfo> &TaskToScopes,
    SmallVectorImpl<Metadata *> &TaskDomains) {
  // Within the domain of T, create a scope and domain for each subtask.
  for (const Task *SubT : T->subtasks()) {
    const Twine Name = ParentName + "_" + SubT->getEntry()->getName();

    TaskToScopes[SubT] = {
        MDB.createAnonymousAliasScope(TaskToDomain[T],
                                      ("taskscp_all_" + Name).str()),
        MDB.createAnonymousAliasScope(TaskToDomain[T],
                                      ("taskscp_write_" + Name).str())};
    MDNode *NewDomain =
        MDB.createAnonymousAliasScopeDomain(("taskdom_" + Name).str());
    TaskToDomain[SubT] = NewDomain;
    TaskDomains.push_back(NewDomain);

    // Recursively create domains and scopes for subtasks.
    createTaskDomainsAndFullScopes(SubT, MDB, Name, TaskToDomain, TaskToScopes,
                                   TaskDomains);
  }
}

bool DRFScopedNoAliasImpl::populateTaskScopeNoAlias() {
  // Create a domain for the task scopes.
  MDBuilder MDB(F.getContext());
  if (!EnableDRFAATaskScopeMetadata || TI.isSerial())
    return false;
  TI.evaluateParallelState<MaybeParallelTasks>(MPTasks);

  DenseMap<const Task *, MDNode *> TaskToDomain;
  DenseMap<const Task *, TaskAliasScopeInfo> TaskToScopes;
  SmallVector<Metadata *, 8> TaskDomains;

  // Create a domain and scope for the root task.
  MDNode *NewDomain =
      MDB.createAnonymousAliasScopeDomain(("dom_" + F.getName()).str());
  TaskToDomain[TI.getRootTask()] = NewDomain;
  TaskDomains.push_back(NewDomain);
  TaskToScopes[TI.getRootTask()] = {
      MDB.createAnonymousAliasScope(NewDomain,
                                    ("scp_all_" + F.getName()).str()),
      MDB.createAnonymousAliasScope(NewDomain,
                                    ("scp_write_" + F.getName()).str())};

  // Recursively create task domains and scopes for subtasks.
  createTaskDomainsAndFullScopes(TI.getRootTask(), MDB, F.getName(),
                                 TaskToDomain, TaskToScopes, TaskDomains);

  ActiveTaskAliasScopes ActiveScopes;
  bool Changed =
      populateSubTaskScopeNoAlias(TI.getRootTask(), ActiveScopes, TaskToScopes);
  if (Changed)
    GeneratedDomains.append(TaskDomains.begin(), TaskDomains.end());
  return Changed;
}

static bool simpleAccessMayRace(const Instruction &I) {
  // The shared candidate filter admits only ordinary loads and stores, so a
  // store is the only remaining way for a pair to witness a data race.
  return isa<StoreInst>(&I);
}

static MemoryLocation getSimpleAccessLocation(const Instruction *I) {
  if (const auto *LI = dyn_cast<LoadInst>(I))
    return MemoryLocation::get(LI);
  return MemoryLocation::get(cast<StoreInst>(I));
}

static void appendScopedMetadata(Instruction &I, unsigned Kind,
                                 ArrayRef<Metadata *> Scopes) {
  if (Scopes.empty())
    return;
  MDNode *NewMD = MDNode::get(I.getContext(), Scopes);
  I.setMetadata(Kind, MDNode::concatenate(I.getMetadata(Kind), NewMD));
}

static const SCEV *getAccessVariationSignature(Instruction &I, const Loop *L,
                                               ScalarEvolution &SE) {
  const SCEV *PointerExpr = SE.getSCEV(getLoadStorePointerOperand(&I));
  if (SE.isLoopInvariant(PointerExpr, L))
    return nullptr;
  if (const auto *AR = dyn_cast<SCEVAddRecExpr>(PointerExpr))
    if (AR->getLoop() == L)
      return AR->getStepRecurrence(SE);
  return PointerExpr;
}

bool DRFScopedNoAliasImpl::populateProvenPairNoAlias() {
  if (!EnableDRFAAProvenPairMetadata || !LI)
    return false;
  if (!DeltaSetProofCache)
    DeltaSetProofCache = createDRFAADeltaSetProofCache();

  enum class AccessKind : uint8_t { Read, Write };
  using ProofContext = std::pair<const Task *, const Loop *>;
  using AccessBucketKey = std::tuple<const Value *, const SCEV *, AccessKind>;
  using AccessBuckets =
      MapVector<AccessBucketKey, SmallVector<Instruction *, 8>>;
  MapVector<ProofContext, AccessBuckets> AccessesByContext;

  // An access is placed in each enclosing logically-parallel loop context.
  // Object, read/write role, and SCEV shape keep common profitable pairs in
  // small buckets without letting one large task suppress all proof work.
  for (BasicBlock &BB : F) {
    const Task *T = TI.getTaskFor(&BB);
    if (!T)
      continue;

    for (Instruction &I : BB) {
      if (!isOrdinaryDRFMemoryAccess(&I))
        continue;

      const Value *Ptr = getLoadStorePointerOperand(&I);
      const Value *Object = getUnderlyingObject(Ptr);
      AccessKind Kind =
          simpleAccessMayRace(I) ? AccessKind::Write : AccessKind::Read;
      for (Loop *L = LI->getLoopFor(&BB); L; L = L->getParentLoop()) {
        if (!isDRFLogicallyParallelLoop(L, &TI))
          continue;

        const SCEV *Variation = getAccessVariationSignature(I, L, SE);
        auto &Bucket = AccessesByContext[{T, L}][{Object, Variation, Kind}];
        if (Bucket.size() >= MaxDRFAAProvenPairAccessesPerTask) {
          ++NumPairAccessBudgetDrops;
          continue;
        }
        Bucket.push_back(&I);
        ++NumPairAccessesBucketed;
      }
    }
  }

  using AccessPair = std::pair<Instruction *, Instruction *>;
  DenseSet<AccessPair> EvaluatedPairs;
  SmallVector<AccessPair, 32> ProvenPairs;

  for (auto &ContextEntry : AccessesByContext) {
    const Loop *ParallelLoop = ContextEntry.first.second;
    AccessBuckets &Buckets = ContextEntry.second;
    auto GetBucketPairPriority = [&](unsigned BI, unsigned BJ) {
      const AccessBucketKey &AKey = Buckets.getArrayRef()[BI].first;
      const AccessBucketKey &BKey = Buckets.getArrayRef()[BJ].first;
      bool AInvariant = std::get<1>(AKey) == nullptr;
      bool BInvariant = std::get<1>(BKey) == nullptr;
      if (AInvariant != BInvariant)
        return 0u;
      if (std::get<2>(AKey) != std::get<2>(BKey))
        return 1u;
      if (std::get<0>(AKey) != std::get<0>(BKey))
        return 2u;
      return 3u;
    };

    uint64_t PairCandidatesInContext = 0;
    bool ContextTruncated = false;
    // Invariant/varying pairs are the most common full DRF NoAlias proof,
    // followed by read/write and distinct-object pairs.  Visit those shapes
    // first so a bounded analysis spends its budget on likely wins.
    for (unsigned Priority = 0; Priority != 4 && !ContextTruncated;
         ++Priority) {
      for (unsigned WriteBucket = 0;
           WriteBucket != Buckets.size() && !ContextTruncated; ++WriteBucket) {
        if (std::get<2>(Buckets.getArrayRef()[WriteBucket].first) !=
            AccessKind::Write)
          continue;

        for (unsigned OtherBucket = 0;
             OtherBucket != Buckets.size() && !ContextTruncated;
             ++OtherBucket) {
          bool OtherIsWrite =
              std::get<2>(Buckets.getArrayRef()[OtherBucket].first) ==
              AccessKind::Write;
          // A write/write bucket pair is visited from its lower-numbered
          // endpoint only.  Read/read pairs are never enumerated at all.
          if (OtherIsWrite && OtherBucket < WriteBucket)
            continue;

          unsigned BI = std::min(WriteBucket, OtherBucket);
          unsigned BJ = std::max(WriteBucket, OtherBucket);
          if (GetBucketPairPriority(BI, BJ) != Priority)
            continue;

          ArrayRef<Instruction *> AAccesses = Buckets.getArrayRef()[BI].second;
          ArrayRef<Instruction *> BAccesses = Buckets.getArrayRef()[BJ].second;
          unsigned ChecksInBucketPair = 0;
          bool BucketPairTruncated = false;
          for (unsigned AI = 0; AI != AAccesses.size() &&
                                !BucketPairTruncated && !ContextTruncated;
               ++AI) {
            unsigned BBegin = BI == BJ ? AI + 1 : 0;
            for (unsigned BIndex = BBegin; BIndex != BAccesses.size();
                 ++BIndex) {
              Instruction *A = AAccesses[AI];
              Instruction *B = BAccesses[BIndex];
              if (A == B)
                continue;
              if (std::less<Instruction *>()(B, A))
                std::swap(A, B);
              AccessPair Pair(A, B);
              if (EvaluatedPairs.contains(Pair))
                continue;

              if (PairCandidatesInContext >=
                  MaxDRFAAProvenPairChecksPerParallelLoop) {
                ContextTruncated = true;
                break;
              }
              ++PairCandidatesInContext;

              if (ChecksInBucketPair >= MaxDRFAAProvenPairChecksPerTask) {
                BucketPairTruncated = true;
                break;
              }
              ++ChecksInBucketPair;
              ++NumPairCandidateChecks;
              EvaluatedPairs.insert(Pair);

              DRFProofKind Proof = classifyDRFAliasProof(
                  TI, getSimpleAccessLocation(A), getSimpleAccessLocation(B), A,
                  B, SE, DeltaSetProofCache);
              if (Proof == DRFProofKind::NoAlias) {
                ProvenPairs.push_back(Pair);
                ++NumPairNoAliasProofs;
                LLVM_DEBUG(dbgs() << "DRFScopedNoAlias: proved pair NoAlias\n"
                                  << "  A: " << *A << "\n"
                                  << "  B: " << *B << "\n");
                continue;
              }

              // Keep this weaker fact visible in attribution statistics, but
              // do not turn it into noalias metadata: same-iteration aliasing
              // is still possible and must remain visible to scalar
              // optimizations.
              if (classifyDRFLoopDependence(ParallelLoop, &TI, A, B) ==
                  DRFProofKind::NoCrossIteration)
                ++NumPairNoCrossIterationOnly;
            }
          }
          if (BucketPairTruncated)
            ++NumPairCheckBudgetDrops;
        }
      }
    }
    if (ContextTruncated)
      ++NumPairContextBudgetDrops;
  }

  if (ProvenPairs.empty())
    return false;

  // Use one scope per participating access and encode the proven graph in the
  // noalias adjacency lists.  This is equivalent to two scopes per edge but
  // grows as O(accesses + edges), not O(2 * edges) distinct scope nodes.
  LLVMContext &Ctx = F.getContext();
  MDBuilder MDB(Ctx);
  MDNode *Domain = MDB.createAnonymousAliasScopeDomain(
      ("drfaa_pairdom_" + F.getName()).str());
  GeneratedDomains.push_back(Domain);

  DenseSet<Instruction *> ProvenAccesses;
  for (const AccessPair &Pair : ProvenPairs) {
    ProvenAccesses.insert(Pair.first);
    ProvenAccesses.insert(Pair.second);
  }

  DenseMap<Instruction *, MDNode *> AccessScopes;
  unsigned AccessID = 0;
  for (BasicBlock &BB : F) {
    for (Instruction &I : BB) {
      if (!ProvenAccesses.contains(&I))
        continue;
      MDNode *Scope = MDB.createAnonymousAliasScope(
          Domain, ("drfaa_access_" + Twine(AccessID++)).str());
      AccessScopes[&I] = Scope;
      Metadata *ScopeMD[] = {Scope};
      appendScopedMetadata(I, LLVMContext::MD_alias_scope, ScopeMD);
      ++NumPairScopesMaterialized;
    }
  }

  DenseMap<Instruction *, SmallVector<Metadata *, 4>> NoAliasScopes;
  for (const AccessPair &Pair : ProvenPairs) {
    NoAliasScopes[Pair.first].push_back(AccessScopes[Pair.second]);
    NoAliasScopes[Pair.second].push_back(AccessScopes[Pair.first]);
  }
  for (auto &Entry : NoAliasScopes)
    appendScopedMetadata(*Entry.first, LLVMContext::MD_noalias, Entry.second);

  return true;
}

// The sibling-witness proof relates two accesses of one fork-phase leaf: the
// written bytes of the output access, over every instance of the leaf's own
// loops, are disjoint from the bytes a logically parallel sibling reads, which
// cover every instance of the input access. The fact is therefore complete
// over the phase and context-free within the function, so unlike the loop
// proofs above it is never stripped: it stays valid after unrolling, hoisting
// and vectorization clone or move the accesses, and it keeps answering after
// those passes have changed the leaf beyond what the matcher re-accepts.
// Encoding: one persistent domain per function, one scope per output access,
// and the scope on the input access's noalias list (that direction suffices
// for ScopedNoAliasAA). Re-runs only add scopes for pairs not yet encoded.
static constexpr StringLiteral SiblingWitnessDomainMDName =
    "drfaa.sibling.witness.domain";

static MDNode *scopeInDomain(const Instruction *I, const MDNode *Domain) {
  MDNode *Scopes = I->getMetadata(LLVMContext::MD_alias_scope);
  if (!Scopes)
    return nullptr;
  for (const MDOperand &Op : Scopes->operands()) {
    auto *Scope = dyn_cast<MDNode>(Op.get());
    if (Scope && Scope->getNumOperands() >= 2 &&
        Scope->getOperand(1).get() == Domain)
      return Scope;
  }
  return nullptr;
}

static bool hasNoAliasScope(const Instruction *I, const MDNode *Scope) {
  MDNode *NoAlias = I->getMetadata(LLVMContext::MD_noalias);
  if (!NoAlias)
    return false;
  for (const MDOperand &Op : NoAlias->operands())
    if (Op.get() == Scope)
      return true;
  return false;
}

bool DRFScopedNoAliasImpl::populateSiblingWitnessNoAlias() {
  if (!EnableDRFAASiblingWitnessMetadata || !isDRFAASiblingWitnessEnabled())
    return false;
  DRFSiblingWitnessInfo Witness(F);
  ArrayRef<DRFSiblingWitnessInfo::AccessPair> Pairs = Witness.getNoAliasPairs();
  if (Pairs.empty())
    return false;

  LLVMContext &Ctx = F.getContext();
  MDBuilder MDB(Ctx);
  MDNode *Domain = nullptr;
  if (MDNode *Record = F.getMetadata(SiblingWitnessDomainMDName))
    if (Record->getNumOperands() == 1)
      Domain = dyn_cast_or_null<MDNode>(Record->getOperand(0).get());
  if (!Domain) {
    Domain = MDB.createAnonymousAliasScopeDomain(
        ("drfaa_siblingdom_" + F.getName()).str());
    Metadata *DomainMD[] = {Domain};
    F.setMetadata(SiblingWitnessDomainMDName, MDNode::get(Ctx, DomainMD));
  }

  bool Changed = false;
  unsigned ScopeID = 0;
  for (const DRFSiblingWitnessInfo::AccessPair &Pair : Pairs) {
    Instruction *Output = Pair.first;
    Instruction *Input = Pair.second;
    MDNode *OutScope = scopeInDomain(Output, Domain);
    MDNode *InScope = scopeInDomain(Input, Domain);
    if ((OutScope && hasNoAliasScope(Input, OutScope)) ||
        (InScope && hasNoAliasScope(Output, InScope))) {
      ++NumSiblingWitnessPairsAlreadyEncoded;
      continue;
    }
    if (!OutScope) {
      OutScope = MDB.createAnonymousAliasScope(
          Domain, ("drfaa_sibling_" + Twine(ScopeID++)).str());
      Metadata *ScopeMD[] = {OutScope};
      appendScopedMetadata(*Output, LLVMContext::MD_alias_scope, ScopeMD);
    }
    Metadata *NoAliasMD[] = {OutScope};
    appendScopedMetadata(*Input, LLVMContext::MD_noalias, NoAliasMD);
    ++NumSiblingWitnessPairsMaterialized;
    Changed = true;
  }
  return Changed;
}

bool DRFScopedNoAliasImpl::run() {
  // This pass appears at multiple optimization stages.  Rebuilding from the
  // current IR avoids both duplicate scope lists and stale pair proofs after a
  // transform clones, deletes, or changes memory accesses.
  bool Changed = removeGeneratedMetadata();
  GeneratedDomains.clear();
  if (EnableDRFAA) {
    Changed |= populateTaskScopeNoAlias();
    Changed |= populateProvenPairNoAlias();
    Changed |= populateSiblingWitnessNoAlias();
  }
  Changed |= recordGeneratedDomains();
  return Changed;
}

bool DRFScopedNoAliasWrapperPass::runOnFunction(Function &F) {
  if (skipFunction(F))
    return false;

  TaskInfo &TI = getAnalysis<TaskInfoWrapperPass>().getTaskInfo();
  LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
  ScalarEvolution &SE = getAnalysis<ScalarEvolutionWrapperPass>().getSE();
  return DRFScopedNoAliasImpl(F, TI, &LI, SE).run();
}

// createDRFScopedNoAliasPass - Provide an entry point to create this pass.
//
namespace llvm {
FunctionPass *createDRFScopedNoAliasWrapperPass() {
  return new DRFScopedNoAliasWrapperPass();
}
} // end namespace llvm

PreservedAnalyses DRFScopedNoAliasPass::run(Function &F,
                                            FunctionAnalysisManager &AM) {
  TaskInfo &TI = AM.getResult<TaskAnalysis>(F);
  LoopInfo &LI = AM.getResult<LoopAnalysis>(F);
  ScalarEvolution &SE = AM.getResult<ScalarEvolutionAnalysis>(F);

  DRFScopedNoAliasImpl(F, TI, &LI, SE).run();

  PreservedAnalyses PA;
  PA.preserve<LoopAnalysis>();
  PA.preserve<ScalarEvolutionAnalysis>();
  PA.preserve<TaskAnalysis>();
  PA.preserve<DominatorTreeAnalysis>();
  return PA;
}
