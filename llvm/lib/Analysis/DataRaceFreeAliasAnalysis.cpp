//===- DataRaceFreeAliasAnalysis.cpp - DRF-based Alias Analysis -----------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file defines the DataRaceFreeAliasAnalysis pass, which implements alias
// analysis based on the assumption that a Tapir program is data-race free.
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/DataRaceFreeAliasAnalysis.h"
#include "mlir/Analysis/Presburger/IntegerRelation.h"
#include "mlir/Analysis/Presburger/PresburgerRelation.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/Hashing.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/BasicAliasAnalysis.h"
#include "llvm/Analysis/ConstraintSystem.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/MemoryLocation.h"
#include "llvm/Analysis/MustExecute.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionAliasAnalysis.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/Analysis/TapirTaskInfo.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/ValueHandle.h"
#include "llvm/InitializePasses.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/MathExtras.h"
#include "llvm/Support/raw_ostream.h"
#include <functional>
#include <limits>
#include <memory>
#include <numeric>
#include <optional>
#include <string>

using namespace llvm;

#define DEBUG_TYPE "drf-aa-result"

STATISTIC(NumDeltaSetCacheLookups,
          "Number of DRF-AA delta-set proof-cache lookups");
STATISTIC(NumDeltaSetCacheHits, "Number of DRF-AA delta-set proof-cache hits");
STATISTIC(NumDeltaSetCacheMisses,
          "Number of DRF-AA delta-set proof-cache misses");
STATISTIC(NumDeltaSetCacheInsertions,
          "Number of DRF-AA delta-set proof results cached");
STATISTIC(NumDeltaSetCacheCapacityDrops,
          "Number of DRF-AA delta-set proof results not cached at capacity");
STATISTIC(NumNestedAsymmetricAxisProofs,
          "Number of DRF-AA asymmetric proofs using a replicated inner-loop "
          "schedule");
STATISTIC(NumEnclosingParallelAxisProofs,
          "Number of loop-scoped DRF-AA proofs using an enclosing parallel "
          "axis");
STATISTIC(NumSiblingWitnessCacheRebuilds,
          "Number of DRF sibling-witness snapshot rebuilds");
STATISTIC(NumSiblingWitnessPhases,
          "Number of accepted bounded DRF sibling-witness phases");
STATISTIC(NumSiblingWitnessPairs,
          "Number of DRF sibling-witness access pairs proved");
STATISTIC(NumSiblingWitnessAnswers,
          "Number of direct DRF sibling-witness NoAlias answers");

cl::opt<bool> llvm::EnableDRFAA(
    "enable-drf-aa", cl::init(false), cl::Hidden,
    cl::desc("Enable AA based on the data-race-free assumption "
             "(default = off)"));
cl::opt<bool> llvm::EnableDRFLoopOptimizations(
    "enable-drf-loop-optimizations", cl::init(false), cl::Hidden,
    cl::desc("Enable experimental loop optimizations that consume the "
             "data-race-free contract (default = off)"));
static cl::opt<bool> EnableDRFAACtxI(
    "enable-drf-aa-ctxi", cl::init(true), cl::Hidden,
    cl::desc("Enable use of alias query context instructions to recover "
             "DRF-AA access sites for non-instruction pointers "
             "(default = on)"));
static cl::opt<bool> EnableDRFAASiblingWitness(
    "enable-drf-aa-sibling-witness", cl::init(false), cl::Hidden,
    cl::desc("Enable bounded intraprocedural DRF sibling-read witness proofs "
             "(default = off)"));

bool llvm::isDRFAASiblingWitnessEnabled() {
  return EnableDRFAA && EnableDRFAASiblingWitness;
}
static cl::opt<bool> DRFAASiblingWitnessTrace(
    "drf-aa-sibling-witness-trace", cl::init(false), cl::Hidden,
    cl::desc("Print why sibling-witness fork phases are accepted or rejected"));

static cl::opt<unsigned> DRFAASiblingWitnessTraceQueries(
    "drf-aa-sibling-witness-trace-queries", cl::init(0), cl::Hidden,
    cl::desc("Print up to N sibling-witness queries that found facts but "
             "were not answered, with the reason"));

static cl::opt<unsigned> DRFAASiblingWitnessNegativeRefresh(
    "drf-aa-sibling-witness-negative-refresh", cl::init(64), cl::Hidden,
    cl::desc("Rescan the function for sibling-witness facts only after this "
             "many consecutive queries without a candidate fact (1 = always)"));

static cl::opt<bool> EnableDRFAADeltaSetProof(
    "enable-drf-aa-delta-set-proof", cl::init(false), cl::Hidden,
    cl::desc("Enable experimental DRF-AA delta-set inclusion proofs "
             "(default = off)"));
static cl::opt<bool> EnableDRFAAHyperView(
    "enable-drf-aa-hyper-view", cl::init(false), cl::Hidden,
    cl::desc("Reason about hyperobject view accesses in DRF-AA race "
             "proofs by substituting the hyperobject's leftmost storage "
             "for the view (default = off)"));
static cl::opt<bool> EnableDRFAAPresburgerDeltaSetProof(
    "enable-drf-aa-presburger-delta-set-proof", cl::init(false), cl::Hidden,
    cl::desc("Enable the experimental Presburger-backed DRF-AA delta-set "
             "proof. This is off by default because exact set subtraction can "
             "be expensive in AA queries (default = off)"));
static cl::opt<unsigned> DRFAAAssumedMinTripCount(
    "drf-aa-assumed-min-trip-count", cl::init(3), cl::Hidden,
    cl::desc("Assumed minimum trip count for experimental symbolic DRF-AA "
             "domain proofs. Values 0 and 1 disable the extra assumption "
             "(default = 3)"));
static cl::opt<unsigned> DRFAAMaxPresburgerDeltaSetLoopVars(
    "drf-aa-presburger-delta-set-max-loop-vars", cl::init(2), cl::Hidden,
    cl::desc("Maximum common loop-instance dimensions for the experimental "
             "Presburger-backed DRF-AA delta-set proof (default = 2)"));
static cl::opt<unsigned> DRFAAMaxExhaustiveDeltaSetLoopVars(
    "drf-aa-delta-set-max-exhaustive-loop-vars", cl::init(2), cl::Hidden,
    cl::desc("Maximum common loop-instance dimensions for the expensive "
             "symbolic/exhaustive DRF-AA delta-set fallback proofs after the "
             "cheap interval proof fails (default = 2)"));
static cl::opt<bool> DRFAADumpQueryReasons(
    "drf-aa-dump-query-reasons", cl::init(false), cl::Hidden,
    cl::desc("Dump filtered DRF-AA query/proof rejection reasons "
             "(default = off)"));
static cl::opt<std::string> DRFAADumpQueryFilter(
    "drf-aa-dump-query-filter", cl::init(""), cl::Hidden,
    cl::desc("Only dump DRF-AA query reasons for functions or blocks whose "
             "names contain this substring (default = no filter)"));
static cl::opt<unsigned> DRFAADumpQueryLimit(
    "drf-aa-dump-query-limit", cl::init(200), cl::Hidden,
    cl::desc("Maximum number of DRF-AA query reason records to dump. 0 means "
             "unlimited (default = 200)"));

static unsigned DRFAADumpedQueryReasons = 0;

namespace llvm {

struct DRFAADeltaSetProofCache {
  // Access-specific eligibility is checked before lookup.  The proof itself
  // depends only on these SCEVs and their loop domain.
  struct Key {
    const SCEV *AS = nullptr;
    const SCEV *BS = nullptr;
    SmallVector<const Loop *, 4> InstanceLoops;
    SmallVector<unsigned, 4> ParallelLoopIndices;

    bool operator==(const Key &Other) const {
      return AS == Other.AS && BS == Other.BS &&
             InstanceLoops == Other.InstanceLoops &&
             ParallelLoopIndices == Other.ParallelLoopIndices;
    }
  };

  struct Entry {
    Key K;
    bool Result = false;
  };

  static constexpr unsigned MaxEntries = 4096;

  DenseMap<size_t, SmallVector<Entry, 1>> Buckets;
  unsigned NumEntries = 0;

  static size_t hashKey(const Key &K) {
    auto PtrBits = [](const void *Ptr) {
      return reinterpret_cast<uintptr_t>(Ptr);
    };

    hash_code H = hash_combine(PtrBits(K.AS), PtrBits(K.BS));
    for (const Loop *L : K.InstanceLoops)
      H = hash_combine(H, PtrBits(L));
    H = hash_combine(H, K.InstanceLoops.size());
    for (unsigned I : K.ParallelLoopIndices)
      H = hash_combine(H, I);
    H = hash_combine(H, K.ParallelLoopIndices.size());
    return static_cast<size_t>(H);
  }

  std::optional<bool> lookup(const Key &K) const {
    ++NumDeltaSetCacheLookups;
    auto It = Buckets.find(hashKey(K));
    if (It == Buckets.end()) {
      ++NumDeltaSetCacheMisses;
      return std::nullopt;
    }

    for (const Entry &E : It->second) {
      if (E.K == K) {
        ++NumDeltaSetCacheHits;
        return E.Result;
      }
    }

    ++NumDeltaSetCacheMisses;
    return std::nullopt;
  }

  void insert(Key K, bool Result) {
    if (NumEntries >= MaxEntries) {
      ++NumDeltaSetCacheCapacityDrops;
      return;
    }

    auto &Bucket = Buckets[hashKey(K)];
    for (Entry &E : Bucket) {
      if (E.K == K) {
        E.Result = Result;
        return;
      }
    }

    Bucket.push_back({std::move(K), Result});
    ++NumEntries;
    ++NumDeltaSetCacheInsertions;
  }
};

struct DRFLoopDependenceInfo::Cache {
  using AccessPair = std::pair<const Instruction *, const Instruction *>;
  DenseMap<const Loop *, DenseMap<AccessPair, DRFLoopDependenceKind>> Results;
  static constexpr unsigned MaxEntries = 4096;
  unsigned NumEntries = 0;
};

} // namespace llvm

DRFLoopDependenceInfo::DRFLoopDependenceInfo(TaskInfo *TI)
    : TI(TI), CachedResults(std::make_unique<Cache>()) {}
DRFLoopDependenceInfo::DRFLoopDependenceInfo(const DRFLoopDependenceInfo &Other)
    : TI(Other.TI),
      CachedResults(std::make_unique<Cache>(*Other.CachedResults)) {}

DRFLoopDependenceInfo &
DRFLoopDependenceInfo::operator=(const DRFLoopDependenceInfo &Other) {
  if (this == &Other)
    return *this;
  TI = Other.TI;
  CachedResults = std::make_unique<Cache>(*Other.CachedResults);
  return *this;
}

DRFLoopDependenceInfo::DRFLoopDependenceInfo(DRFLoopDependenceInfo &&) =
    default;

DRFLoopDependenceInfo &
DRFLoopDependenceInfo::operator=(DRFLoopDependenceInfo &&) = default;

DRFLoopDependenceInfo::~DRFLoopDependenceInfo() = default;

void DRFLoopDependenceInfo::clear() {
  CachedResults->Results.clear();
  CachedResults->NumEntries = 0;
}

bool DRFLoopDependenceInfo::isLogicallyParallel(const Loop *L) const {
  return isDRFLogicallyParallelLoop(L, TI);
}

DRFAAResult::DRFAAResult(TaskInfo &TI, BasicAAResult &BasicAA,
                         ScalarEvolution &SE, const TargetLibraryInfo &TLI)
    : AAResultBase(), TI(TI), BAA(BasicAA), SE(SE), TLI(TLI),
      DeltaSetProofCache(createDRFAADeltaSetProofCache()) {}

DRFAAResult::DRFAAResult(DRFAAResult &&Arg)
    : AAResultBase(std::move(Arg)), TI(Arg.TI), BAA(Arg.BAA), SE(Arg.SE),
      TLI(Arg.TLI), DeltaSetProofCache(std::move(Arg.DeltaSetProofCache)),
      SiblingWitnessInfo(std::move(Arg.SiblingWitnessInfo)) {
  if (!DeltaSetProofCache)
    DeltaSetProofCache.reset(createDRFAADeltaSetProofCache());
}

DRFAAResult::~DRFAAResult() = default;

DRFAADeltaSetProofCache *llvm::createDRFAADeltaSetProofCache() {
  return new DRFAADeltaSetProofCache();
}

void llvm::destroyDRFAADeltaSetProofCache(DRFAADeltaSetProofCache *Cache) {
  delete Cache;
}

bool DRFAAResult::invalidate(Function &Fn, const PreservedAnalyses &PA,
                             FunctionAnalysisManager::Invalidator &Inv) {
  // The delta-set proof cache is derived from the analyses below.  It remains
  // valid exactly when those dependencies remain valid.
  if (Inv.invalidate<TaskAnalysis>(Fn, PA) || Inv.invalidate<BasicAA>(Fn, PA) ||
      Inv.invalidate<ScalarEvolutionAnalysis>(Fn, PA) ||
      Inv.invalidate<TargetLibraryAnalysis>(Fn, PA))
    return true;

  // Otherwise this analysis result remains valid.
  return false;
}

#ifndef NDEBUG
static const Function *getParent(const Value *V) {
  if (const Instruction *inst = dyn_cast<Instruction>(V)) {
    if (!inst->getParent())
      return nullptr;
    return inst->getParent()->getParent();
  }

  if (const Argument *arg = dyn_cast<Argument>(V))
    return arg->getParent();

  return nullptr;
}

static bool notDifferentParent(const Value *O1, const Value *O2) {

  const Function *F1 = getParent(O1);
  const Function *F2 = getParent(O2);

  return !F1 || !F2 || F1 == F2;
}
#endif

static bool drfaaMatchesDumpFilter(const Instruction *I) {
  if (DRFAADumpQueryFilter.getValue().empty())
    return true;
  if (!I)
    return false;

  StringRef Filter = DRFAADumpQueryFilter.getValue();
  if (const Function *F = I->getFunction())
    if (F->getName().contains(Filter))
      return true;
  if (const BasicBlock *BB = I->getParent())
    if (BB->getName().contains(Filter))
      return true;
  return false;
}

static bool drfaaShouldDumpQueryReason(const Instruction *AccessA,
                                       const Instruction *AccessB) {
  if (!DRFAADumpQueryReasons)
    return false;
  if (DRFAADumpQueryLimit != 0 &&
      DRFAADumpedQueryReasons >= DRFAADumpQueryLimit)
    return false;
  if (!DRFAADumpQueryFilter.getValue().empty() &&
      !drfaaMatchesDumpFilter(AccessA) && !drfaaMatchesDumpFilter(AccessB))
    return false;
  ++DRFAADumpedQueryReasons;
  return true;
}

static void drfaaDumpInstLine(StringRef Label, const Instruction *I) {
  errs() << "    " << Label << ": ";
  if (!I) {
    errs() << "<none>\n";
    return;
  }

  if (const Function *F = I->getFunction())
    errs() << F->getName() << ": ";
  if (DebugLoc DL = I->getDebugLoc()) {
    DL.print(errs());
    errs() << ": ";
  }
  errs() << *I << "\n";
}

static void drfaaDumpQueryReason(StringRef Reason, const MemoryLocation &LocA,
                                 const MemoryLocation &LocB,
                                 const Instruction *AccessA,
                                 const Instruction *AccessB,
                                 const SCEV *AS = nullptr,
                                 const SCEV *BS = nullptr) {
  if (!drfaaShouldDumpQueryReason(AccessA, AccessB))
    return;

  errs() << "DRFAA-TRACE #" << DRFAADumpedQueryReasons << " reason=" << Reason
         << "\n";
  drfaaDumpInstLine("AccessA", AccessA);
  drfaaDumpInstLine("AccessB", AccessB);
  errs() << "    LocA.Ptr: " << *LocA.Ptr << "\n";
  errs() << "    LocB.Ptr: " << *LocB.Ptr << "\n";
  if (AS)
    errs() << "    SCEV A: " << *AS << "\n";
  if (BS)
    errs() << "    SCEV B: " << *BS << "\n";
}

/// Return the hyperobject operand if \p Ptr is directly the result of a
/// hyperobject view lookup (e.g. llvm.hyper.lookup), and nullptr otherwise.
/// Pointers merely derived from a view (casts, GEPs) are deliberately not
/// traced: the substitution below replaces the whole location with the
/// hyperobject handle, which is only exact for direct view accesses.
static const Value *getHyperViewHyperobject(const Value *Ptr) {
  const auto *CB = dyn_cast<CallBase>(Ptr);
  if (!CB || !CB->hasFnAttr(Attribute::HyperView) || CB->arg_empty())
    return nullptr;
  return CB->getArgOperand(0);
}

bool llvm::isDRFLogicallyParallelLoop(const Loop *L, const TaskInfo *TI) {
  return L &&
         (L->wasDerivedFromTapirLoop() ||
          (TI && getTaskIfTapirLoopStructure(L, const_cast<TaskInfo *>(TI))));
}

bool llvm::isOrdinaryDRFMemoryAccess(const Instruction *I) {
  const Value *Ptr = nullptr;
  if (const auto *LI = dyn_cast_or_null<LoadInst>(I)) {
    if (!LI->isSimple())
      return false;
    Ptr = LI->getPointerOperand();
  } else if (const auto *SI = dyn_cast_or_null<StoreInst>(I)) {
    if (!SI->isSimple())
      return false;
    Ptr = SI->getPointerOperand();
  } else {
    return false;
  }

  SmallVector<const Value *, 4> Objects;
  getUnderlyingObjects(Ptr, Objects);
  return none_of(Objects, [](const Value *Object) {
    const auto *CB = dyn_cast<CallBase>(Object);
    return CB && CB->hasFnAttr(Attribute::HyperView);
  });
}

bool llvm::drfInvariantLoadClobberWouldRace(const Loop *L, const TaskInfo &TI,
                                            const Instruction *Load,
                                            const Instruction *Clobber,
                                            ScalarEvolution *SE,
                                            bool AllowLoopInvariantGuards) {
  const auto *LI = dyn_cast_or_null<LoadInst>(Load);
  const auto *SI = dyn_cast_or_null<StoreInst>(Clobber);
  if (!L || !LI || !SI || !isDRFLogicallyParallelLoop(L, &TI) ||
      !L->contains(LI->getParent()) || !L->contains(SI->getParent()) ||
      !isOrdinaryDRFMemoryAccess(LI) || !isOrdinaryDRFMemoryAccess(SI) ||
      !L->isLoopInvariant(LI->getPointerOperand()))
    return false;

  // Loop spawning can rebind an alloca that was private to each source-level
  // Tapir iteration to one stack slot reused by a serialized chunk loop.  The
  // pointer then appears invariant in the derived loop, but it does not name a
  // shared source-level object and therefore cannot supply a race witness.
  // Preserve the ordinary rule for structurally intact Tapir loops, where an
  // alloca outside the loop really is shared by its detached iterations.
  if (L->wasDerivedFromTapirLoop() &&
      !getTaskIfTapirLoopStructure(L, const_cast<TaskInfo *>(&TI))) {
    SmallVector<const Value *, 4> Objects;
    getUnderlyingObjects(LI->getPointerOperand(), Objects);
    if (any_of(Objects,
               [](const Value *Object) { return isa<AllocaInst>(Object); }))
      return false;
  }

  // The race witness needs a different iteration from the one executing the
  // store.  Unknown trip counts use the explicit DRF-AA domain assumption, but
  // do not contradict a statically known single-iteration loop.
  if (DRFAAAssumedMinTripCount < 2)
    return false;
  if (SE) {
    unsigned MaxTripCount = SE->getSmallConstantMaxTripCount(L);
    if (MaxTripCount == 1)
      return false;
  }

  SimpleLoopSafetyInfo SafetyInfo;
  SafetyInfo.computeLoopSafetyInfo(L);
  if (SafetyInfo.isGuaranteedToExecute(*LI, &TI.getDominatorTree(),
                                       const_cast<TaskInfo *>(&TI), L))
    return true;
  if (!AllowLoopInvariantGuards)
    return false;

  // A load guarded only by loop-invariant branch decisions is uniform across
  // logical iterations: for a particular loop invocation it executes either in
  // every iteration or in none. In the former case an aliasing store still
  // conflicts with the load in another iteration; in the latter case there is
  // no dynamic load whose clobber query needs to be justified.
  //
  // Keep this proof deliberately structural. A unique predecessor chain avoids
  // reasoning about merged path predicates, and requiring every instruction
  // before the load to transfer execution rules out exceptions or non-returning
  // calls that could make the guard uniform while execution of the load is not.
  // Detaches, syncs, switches, and iteration-varying branches therefore remain
  // conservative.
  const BasicBlock *Header = L->getHeader();
  const BasicBlock *BB = LI->getParent();
  SmallPtrSet<const BasicBlock *, 8> Visited;

  if (!isGuaranteedToTransferExecutionToSuccessor(BB->begin(),
                                                  LI->getIterator()))
    return false;

  const Task *LoadTask = TI.getTaskFor(BB);
  while (BB != Header) {
    if (!Visited.insert(BB).second || pred_size(BB) != 1)
      return false;

    const BasicBlock *Pred = *pred_begin(BB);
    if (!L->contains(Pred) || TI.getTaskFor(Pred) != LoadTask ||
        !isGuaranteedToTransferExecutionToSuccessor(Pred))
      return false;

    const auto *BI = dyn_cast<BranchInst>(Pred->getTerminator());
    if (!BI || (BI->isConditional() && !L->isLoopInvariant(BI->getCondition())))
      return false;

    BB = Pred;
  }
  return true;
}

DRFLoopDependenceKind llvm::classifyDRFLoopDependence(const Loop *L,
                                                      TaskInfo *TI,
                                                      const Instruction *A,
                                                      const Instruction *B) {
  if (!L || !A || !B || !isDRFLogicallyParallelLoop(L, TI) ||
      !L->contains(A->getParent()) || !L->contains(B->getParent()) ||
      (!isa<StoreInst>(A) && !isa<StoreInst>(B)) ||
      !isOrdinaryDRFMemoryAccess(A) || !isOrdinaryDRFMemoryAccess(B))
    return DRFLoopDependenceKind::Unknown;

  return DRFLoopDependenceKind::NoCrossIteration;
}

DRFLoopDependenceKind DRFLoopDependenceInfo::get(const Loop *L,
                                                 const Instruction *A,
                                                 const Instruction *B) {
  // The classification is symmetric. Canonicalizing the access pair avoids
  // missing the cache when two clients ask the same question in reverse order.
  if (std::less<const Instruction *>()(B, A))
    std::swap(A, B);

  Cache::AccessPair Pair(A, B);
  auto LoopIt = CachedResults->Results.find(L);
  if (LoopIt != CachedResults->Results.end()) {
    auto It = LoopIt->second.find(Pair);
    if (It != LoopIt->second.end())
      return It->second;
  }

  DRFLoopDependenceKind Result = classifyDRFLoopDependence(L, TI, A, B);
  if (CachedResults->NumEntries < Cache::MaxEntries) {
    auto &LoopResults = CachedResults->Results[L];
    if (LoopResults.try_emplace(Pair, Result).second)
      ++CachedResults->NumEntries;
  }
  return Result;
}

static bool mayShareUnderlyingObject(const Value *A, const Value *B) {
  SmallVector<const Value *, 4> OA, OB;
  getUnderlyingObjects(A, OA);
  getUnderlyingObjects(B, OB);
  for (const Value *VA : OA)
    for (const Value *VB : OB)
      if (VA == VB)
        return true;
  return false;
}

static bool isLocallyPromotableAlloca(const AllocaInst *AI) {
  for (const User *U : AI->users()) {
    if (const auto *LI = dyn_cast<LoadInst>(U)) {
      if (LI->isVolatile() || LI->getType() != AI->getAllocatedType())
        return false;
    } else if (const auto *SI = dyn_cast<StoreInst>(U)) {
      if (SI->getValueOperand() == AI ||
          SI->getValueOperand()->getType() != AI->getAllocatedType() ||
          SI->isVolatile())
        return false;
    } else if (const auto *II = dyn_cast<IntrinsicInst>(U)) {
      if (!II->isLifetimeStartOrEnd() && !II->isDroppable() &&
          II->getIntrinsicID() != Intrinsic::fake_use)
        return false;
    } else if (const auto *BCI = dyn_cast<BitCastInst>(U)) {
      if (!onlyUsedByLifetimeMarkersOrDroppableInsts(BCI))
        return false;
    } else if (const auto *GEPI = dyn_cast<GetElementPtrInst>(U)) {
      if (!GEPI->hasAllZeroIndices() ||
          !onlyUsedByLifetimeMarkersOrDroppableInsts(GEPI))
        return false;
    } else if (const auto *ASCI = dyn_cast<AddrSpaceCastInst>(U)) {
      if (!onlyUsedByLifetimeMarkers(ASCI))
        return false;
    } else {
      return false;
    }
  }

  return true;
}

static bool isTaskPrivatePromotableAlloca(const Value *Ptr,
                                          const TaskInfo &TI) {
  const auto *AI = dyn_cast<AllocaInst>(getUnderlyingObject(Ptr));
  return AI && isLocallyPromotableAlloca(AI) &&
         TI.isAllocaParallelPromotable(AI);
}

static bool hasDRFParallelism(const TaskInfo &TI, const Instruction *A,
                              const Instruction *B) {
  bool DefinitelyParallel = TI.isDefinitelyLogicallyParallel(A, B);
  bool LoopCarriedParallel = TI.isLoopCarriedLogicallyParallel(A, B);

  LLVM_DEBUG(dbgs() << "DRFAA: hasDRFParallelism AddrA: " << *A
                    << " AddrB: " << *B << " definitely? " << DefinitelyParallel
                    << " loop-carried? " << LoopCarriedParallel << "\n");
  return DefinitelyParallel || LoopCarriedParallel;
}

static AliasResult
basicAAFallback(const MemoryLocation &LocA, const MemoryLocation &LocB,
                const Instruction *CtxI, const AAQueryInfo &AAQI,
                BasicAAResult &BasicAA, const TargetLibraryInfo &TLI) {
  AAResults AAR(TLI);
  AAR.addAAResult(BasicAA);
  SimpleAAQueryInfo BasicAAQI(AAR);
  BasicAAQI.MayBeCrossIteration = AAQI.MayBeCrossIteration;
  BasicAAQI.UseDominatorTree = AAQI.UseDominatorTree;
  BasicAAQI.AssumeSameSpindle = AAQI.AssumeSameSpindle;
  return BasicAA.alias(LocA, LocB, BasicAAQI, CtxI);
}

static bool ctxIMatchesLoc(const MemoryLocation &Loc, const Instruction *CtxI) {
  if (!CtxI)
    return false;

  std::optional<MemoryLocation> CtxLoc = MemoryLocation::getOrNone(CtxI);
  return CtxLoc && CtxLoc->Ptr == Loc.Ptr;
}

static const Instruction *getAccessInstForLoc(const MemoryLocation &Loc,
                                              const Instruction *CtxI) {
  if (EnableDRFAACtxI && ctxIMatchesLoc(Loc, CtxI))
    return CtxI;

  return dyn_cast<Instruction>(Loc.Ptr);
}

static bool canComputePointerDiff(ScalarEvolution &SE, const SCEV *A,
                                  const SCEV *B) {
  if (SE.getEffectiveSCEVType(A->getType()) !=
      SE.getEffectiveSCEVType(B->getType()))
    return false;

  return SE.instructionCouldExistWithOperands(A, B);
}

static bool getFixedLocationSize(const LocationSize &Size, uint64_t &Bytes) {
  if (!Size.hasValue() || Size.isScalable() || !Size.isPrecise())
    return false;

  Bytes = Size.getValue().getKnownMinValue();
  return Bytes != 0;
}

namespace {
using SiblingIntervals = SmallVector<std::pair<int64_t, int64_t>, 16>;

static void normalizeSiblingIntervals(SiblingIntervals &Intervals) {
  llvm::sort(Intervals);
  unsigned N = 0;
  for (auto I : Intervals) {
    if (N && I.first <= Intervals[N - 1].second)
      Intervals[N - 1].second = std::max(Intervals[N - 1].second, I.second);
    else
      Intervals[N++] = I;
  }
  Intervals.resize(N);
}

static bool siblingIntervalsCover(const SiblingIntervals &Cover,
                                  const SiblingIntervals &Covered) {
  unsigned J = 0;
  for (auto I : Covered) {
    while (J < Cover.size() && Cover[J].second <= I.first)
      ++J;
    if (J == Cover.size() || Cover[J].first > I.first ||
        Cover[J].second < I.second)
      return false;
  }
  return true;
}

// AA is queried while clients such as LICM edit instructions without
// invalidating the enclosing function analysis. A proof cache must detect
// those edits, not just FAM invalidation. This exact snapshot retains no IR
// uses and does not follow RAUW. It checks operands, CFG, instruction order,
// types, and the non-operand state on which the bounded matcher depends.
struct SiblingInstructionSnapshot {
  WeakVH Inst;
  Type *Ty;
  Type *GEPSourceTy = nullptr;
  unsigned Opcode;
  unsigned Flags;
  unsigned Extra = 0;
  AttributeList CallAttrs;
  AttributeList CalleeAttrs;
  SmallVector<WeakVH, 4> Operands;
  SmallVector<Type *, 4> OperandTypes;
  SmallVector<WeakVH, 2> IncomingBlocks;

  static unsigned extra(const Instruction &I) {
    if (const auto *C = dyn_cast<CmpInst>(&I))
      return C->getPredicate();
    if (const auto *L = dyn_cast<LoadInst>(&I))
      return unsigned(L->getOrdering()) * 2 + L->isVolatile();
    if (const auto *S = dyn_cast<StoreInst>(&I))
      return unsigned(S->getOrdering()) * 2 + S->isVolatile();
    return 0;
  }

  explicit SiblingInstructionSnapshot(Instruction &I)
      : Inst(&I), Ty(I.getType()), Opcode(I.getOpcode()),
        Flags(I.getRawSubclassOptionalData()), Extra(extra(I)) {
    if (const auto *G = dyn_cast<GetElementPtrInst>(&I))
      GEPSourceTy = G->getSourceElementType();
    if (const auto *CB = dyn_cast<CallBase>(&I)) {
      CallAttrs = CB->getAttributes();
      if (const Function *Callee = CB->getCalledFunction())
        CalleeAttrs = Callee->getAttributes();
    }
    for (Value *V : I.operands()) {
      Operands.emplace_back(V);
      OperandTypes.push_back(V->getType());
    }
    if (const auto *P = dyn_cast<PHINode>(&I))
      for (BasicBlock *BB : P->blocks())
        IncomingBlocks.emplace_back(BB);
  }

  bool matches(const Instruction &I) const {
    if (Inst != &I || Ty != I.getType() || Opcode != I.getOpcode() ||
        Flags != I.getRawSubclassOptionalData() || Extra != extra(I) ||
        Operands.size() != I.getNumOperands())
      return false;
    if (const auto *G = dyn_cast<GetElementPtrInst>(&I))
      if (GEPSourceTy != G->getSourceElementType())
        return false;
    if (const auto *CB = dyn_cast<CallBase>(&I)) {
      if (CallAttrs != CB->getAttributes())
        return false;
      if (const Function *Callee = CB->getCalledFunction())
        if (CalleeAttrs != Callee->getAttributes())
          return false;
    }
    for (unsigned J = 0; J < Operands.size(); ++J)
      if (Operands[J] != I.getOperand(J) ||
          OperandTypes[J] != I.getOperand(J)->getType())
        return false;
    if (const auto *P = dyn_cast<PHINode>(&I)) {
      if (IncomingBlocks.size() != P->getNumIncomingValues())
        return false;
      for (unsigned J = 0; J < IncomingBlocks.size(); ++J)
        if (IncomingBlocks[J] != P->getIncomingBlock(J))
          return false;
    }
    return true;
  }
};

struct SiblingAccess {
  Instruction *Inst;
  const Value *Ptr;
  const Value *Base;
  uint64_t Size;
  SiblingIntervals Bytes;
};

struct SiblingLeaf {
  BasicBlock *Entry = nullptr; // detached block, or the continuation block
  SmallPtrSet<BasicBlock *, 32> Blocks;
  SmallVector<Instruction *, 64> Memory;
  SmallVector<SiblingAccess, 64> Accesses;
};

// This deliberately recognizes a small structural language: unconditional
// blocks and rotated, finite constant-trip loops, then reattach or sync.
// In particular a load merely executing once somewhere in a loop is NOT
// sufficient. Every accepted body block executes on every loop iteration.
class SiblingPhaseBuilder {
  Function &F;
  TaskInfo &TI;
  LoopInfo &LI;
  const DominatorTree &DT;
  const DataLayout &DL;
  DetachInst *Start;
  Value *SyncRegion;
  unsigned BlockBudget = 512;
  DenseMap<const Loop *, unsigned> Trips;

  bool reject(const char *Why, const Value *V = nullptr) const {
    if (DRFAASiblingWitnessTrace) {
      errs() << "DRF-SIBLING-TRACE reject [" << F.getName() << "] " << Why;
      if (V) {
        errs() << ": ";
        if (const auto *BB = dyn_cast<BasicBlock>(V))
          errs() << "block %" << BB->getName();
        else
          V->print(errs(), /*IsForDebug=*/true);
      }
      errs() << "\n";
    }
    return false;
  }

  bool inspectBlock(BasicBlock *BB, SiblingLeaf &Leaf) {
    if (!BlockBudget-- || !DT.dominates(Start->getParent(), BB) ||
        !Leaf.Blocks.insert(BB).second)
      return reject("block budget/dominance/revisit", BB);
    for (Instruction &I : *BB) {
      if (I.isTerminator())
        continue;
      if (isa<LoadInst, StoreInst>(I)) {
        if (!isOrdinaryDRFMemoryAccess(&I))
          return reject("non-ordinary access", &I);
        Leaf.Memory.push_back(&I);
      } else if (auto *CB = dyn_cast<CallBase>(&I)) {
        const auto *II = dyn_cast<IntrinsicInst>(CB);
        if (!II || (II->getIntrinsicID() != Intrinsic::fmuladd &&
                    II->getIntrinsicID() != Intrinsic::fma &&
                    II->getIntrinsicID() != Intrinsic::smin &&
                    II->getIntrinsicID() != Intrinsic::smax &&
                    II->getIntrinsicID() != Intrinsic::umin &&
                    II->getIntrinsicID() != Intrinsic::umax &&
                    !isa<DbgInfoIntrinsic>(II)))
          return reject("unsupported call", &I);
      } else if (I.mayReadOrWriteMemory() || I.mayHaveSideEffects() ||
                 isa<AllocaInst>(I)) {
        return reject("side-effecting instruction", &I);
      }
    }
    if (Leaf.Memory.size() > 256)
      return reject("more than 256 memory instructions in leaf", BB);
    return true;
  }

  bool validLoop(Loop *L) {
    if (Trips.contains(L))
      return true;
    BasicBlock *Latch = L->getLoopLatch();
    BasicBlock *PH = L->getLoopPreheader();
    auto *BI = Latch ? dyn_cast<BranchInst>(Latch->getTerminator()) : nullptr;
    if (!PH || !BI || !BI->isConditional() || L->getExitingBlock() != Latch ||
        !L->getUniqueExitBlock() || PH->getSingleSuccessor() != L->getHeader())
      return reject("loop shape (needs preheader, latch==exiting, unique exit)",
                    L->getHeader());
    // Do not infer this domain from range metadata or assumptions. Require
    // a literal counted induction and simulate its latch for at most 64
    // iterations. This also makes metadata-only changes irrelevant to the
    // cached execution/coverage proof.
    auto *Cmp = dyn_cast<ICmpInst>(BI->getCondition());
    if (!Cmp)
      return reject("latch condition is not icmp", BI->getCondition());
    auto *Bound = dyn_cast<ConstantInt>(Cmp->getOperand(1));
    bool Swapped = false;
    Value *Compared = Cmp->getOperand(0);
    if (!Bound) {
      Bound = dyn_cast<ConstantInt>(Cmp->getOperand(0));
      Compared = Cmp->getOperand(1);
      Swapped = true;
    }
    if (!Bound || Bound->getBitWidth() > 64)
      return reject("latch bound not a constant", Cmp);
    // The latch may test the phi itself, its next value, or (after runtime
    // unrolling) a later value of the same literal recurrence.
    APInt ComparedOffset;
    PHINode *IV = dyn_cast<PHINode>(stripConstantOffset(Compared, ComparedOffset));
    if (!IV || IV->getParent() != L->getHeader() ||
        IV->getNumIncomingValues() != 2 || IV->getBasicBlockIndex(PH) < 0 ||
        IV->getBasicBlockIndex(Latch) < 0)
      return reject("latch compares a non-header-phi value", Cmp);
    auto *Initial = dyn_cast<ConstantInt>(IV->getIncomingValueForBlock(PH));
    if (auto *LatchConst =
            dyn_cast_or_null<ConstantInt>(IV->getIncomingValueForBlock(Latch))) {
      // InstCombine folds the increment of a two-trip loop into a literal
      // latch value: phi [Initial, PH], [LatchConst, Latch]. The IV takes
      // Initial on trip 1 and LatchConst on trip 2 and after, so the loop
      // must exit at trip 1 or 2.
      if (!Initial || Compared != IV)
        return reject("literal latch value with unsupported compare", IV);
      auto Exits = [&](const APInt &Tested) {
        bool Condition = Swapped ? ICmpInst::compare(Bound->getValue(), Tested,
                                                     Cmp->getPredicate())
                                 : ICmpInst::compare(Tested, Bound->getValue(),
                                                     Cmp->getPredicate());
        return BI->getSuccessor(Condition ? 0 : 1) != L->getHeader();
      };
      unsigned Count = Exits(Initial->getValue())        ? 1
                       : Exits(LatchConst->getValue()) ? 2
                                                       : 0;
      if (!Count)
        return reject("literal latch value loop never exits", IV);
      Trips[L] = Count;
      return true;
    }
    APInt Step;
    if (!Initial || !literalStep(IV, L, Step))
      return reject("IV initial/next not literal recurrence", IV);
    APInt Value = Initial->getValue();
    unsigned Count = 0;
    for (unsigned N = 1; N <= 64; ++N) {
      APInt Tested = Value + ComparedOffset;
      bool Condition = Swapped ? ICmpInst::compare(Bound->getValue(), Tested,
                                                   Cmp->getPredicate())
                               : ICmpInst::compare(Tested, Bound->getValue(),
                                                   Cmp->getPredicate());
      if (BI->getSuccessor(Condition ? 0 : 1) != L->getHeader()) {
        Count = N;
        break;
      }
      Value += Step;
    }
    if (!Count)
      return reject("literal trip count exceeds 64 or never exits", IV);
    Trips[L] = Count;
    return true;
  }

  // SimplifyCFG may merge the final syncs of several return paths into one
  // block that the phase does not dominate. Such a block holds only PHIs and
  // the sync, so it contributes no accesses and still ends every path of the
  // continuation leaf with a sync of this region.
  bool isTrailingSyncBlock(const BasicBlock *BB) const {
    const auto *Sync = dyn_cast<SyncInst>(BB->getTerminator());
    return Sync && Sync->getSyncRegion() == SyncRegion &&
           &*BB->getFirstNonPHIIt() == Sync;
  }

  bool walk(BasicBlock *&BB, SiblingLeaf &Leaf, Loop *Active = nullptr) {
    while (BB) {
      if (!Active && !DT.dominates(Start->getParent(), BB) &&
          isTrailingSyncBlock(BB))
        return true;
      Loop *L = LI.getLoopFor(BB);
      if (L != Active) {
        // At an outer loop header LI can point to that loop; a nested loop
        // must be entered through its header and unconditional preheader.
        if (!L || L->getParentLoop() != Active || L->getHeader() != BB)
          return reject("entered loop not nested directly/through header", BB);
        if (!validLoop(L))
          return false;
        if (!walk(BB, Leaf, L))
          return false;
        continue;
      }
      if (!inspectBlock(BB, Leaf))
        return false;
      Instruction *Term = BB->getTerminator();
      if (Active && BB == Active->getLoopLatch()) {
        auto *BI = dyn_cast<BranchInst>(Term);
        if (!BI || !BI->isConditional() ||
            (BI->getSuccessor(0) != Active->getHeader() &&
             BI->getSuccessor(1) != Active->getHeader()))
          return reject("latch terminator shape", BB);
        BB = Active->getUniqueExitBlock();
        return true;
      }
      if (auto *BI = dyn_cast<BranchInst>(Term)) {
        if (!BI->isUnconditional())
          return reject("conditional branch inside leaf", BB);
        BB = BI->getSuccessor(0);
        continue;
      }
      if (Active || !isa<ReattachInst, SyncInst>(Term))
        return reject("leaf terminator is not reattach/sync", BB);
      return true;
    }
    return reject("walk ran out of blocks");
  }

  bool evaluate(Value *V, const DenseMap<const Loop *, unsigned> &Point,
                APInt &Result, unsigned Depth = 0) {
    if (Depth > 20 || !V->getType()->isIntegerTy())
      return false;
    unsigned Bits = V->getType()->getIntegerBitWidth();
    if (!Bits || Bits > 64)
      return false;
    if (const auto *C = dyn_cast<ConstantInt>(V)) {
      Result = C->getValue();
      return true;
    }
    if (const auto *IV = dyn_cast<PHINode>(V)) {
      const Loop *L = LI.getLoopFor(IV->getParent());
      auto It = Point.find(L);
      if (!L || It == Point.end())
        return false;
      // literalIndex has already checked this exact recurrence. Evaluate the
      // IR itself: AA clients may mutate IR while ScalarEvolution's cached
      // exit counts/expressions are temporarily stale (notably in GVN).
      const auto *Initial = dyn_cast<ConstantInt>(
          IV->getIncomingValueForBlock(L->getLoopPreheader()));
      if (!Initial)
        return false;
      if (const auto *LatchConst = dyn_cast<ConstantInt>(
              IV->getIncomingValueForBlock(L->getLoopLatch()))) {
        // validLoop accepted a literal two-trip recurrence.
        Result = It->second == 0 ? Initial->getValue() : LatchConst->getValue();
        return true;
      }
      APInt Step;
      if (!literalStep(IV, L, Step))
        return false;
      Result = Initial->getValue() + Step * APInt(Bits, It->second);
      return true;
    }
    if (const auto *II = dyn_cast<IntrinsicInst>(V)) {
      APInt A(Bits, 0), B(Bits, 0);
      if (!evaluate(II->getArgOperand(0), Point, A, Depth + 1) ||
          !evaluate(II->getArgOperand(1), Point, B, Depth + 1))
        return false;
      switch (II->getIntrinsicID()) {
      case Intrinsic::smin:
        Result = APIntOps::smin(A, B);
        return true;
      case Intrinsic::smax:
        Result = APIntOps::smax(A, B);
        return true;
      case Intrinsic::umin:
        Result = APIntOps::umin(A, B);
        return true;
      case Intrinsic::umax:
        Result = APIntOps::umax(A, B);
        return true;
      default:
        return false;
      }
    }
    if (auto *Sel = dyn_cast<SelectInst>(V)) {
      const auto *Cmp = dyn_cast<ICmpInst>(Sel->getCondition());
      if (!Cmp || !Cmp->getOperand(0)->getType()->isIntegerTy() ||
          Cmp->getOperand(0)->getType()->getIntegerBitWidth() > 64)
        return false;
      unsigned CmpBits = Cmp->getOperand(0)->getType()->getIntegerBitWidth();
      APInt A(CmpBits, 0), B(CmpBits, 0), T(Bits, 0), F(Bits, 0);
      if (!evaluate(Cmp->getOperand(0), Point, A, Depth + 1) ||
          !evaluate(Cmp->getOperand(1), Point, B, Depth + 1) ||
          !evaluate(Sel->getTrueValue(), Point, T, Depth + 1) ||
          !evaluate(Sel->getFalseValue(), Point, F, Depth + 1))
        return false;
      Result = ICmpInst::compare(A, B, Cmp->getPredicate()) ? T : F;
      return true;
    }
    if (const auto *Cast = dyn_cast<CastInst>(V)) {
      APInt A(1, 0);
      if (!evaluate(Cast->getOperand(0), Point, A, Depth + 1))
        return false;
      if (Cast->getOpcode() == Instruction::SExt)
        Result = A.sext(Bits);
      else if (Cast->getOpcode() == Instruction::ZExt)
        Result = A.zext(Bits);
      else if (Cast->getOpcode() == Instruction::Trunc)
        Result = A.trunc(Bits);
      else
        return false;
      return true;
    }
    if (const auto *BO = dyn_cast<BinaryOperator>(V)) {
      APInt A(Bits, 0), B(Bits, 0);
      if (!evaluate(BO->getOperand(0), Point, A, Depth + 1) ||
          !evaluate(BO->getOperand(1), Point, B, Depth + 1))
        return false;
      switch (BO->getOpcode()) {
      case Instruction::Add:
        Result = A + B;
        return true;
      case Instruction::Sub:
        Result = A - B;
        return true;
      case Instruction::Mul:
        Result = A * B;
        return true;
      case Instruction::Shl:
        // Only a literal shift amount is accepted by literalIndex.
        if (B.uge(Bits))
          return false;
        Result = A.shl(B);
        return true;
      case Instruction::Or:
        // InstCombine rewrites an add of non-overlapping bit ranges as a
        // disjoint or (e.g. i + 1 when i is a multiple of 4); it is the add.
        if (!cast<PossiblyDisjointInst>(BO)->isDisjoint())
          return false;
        Result = A + B;
        return true;
      default:
        return false;
      }
    }
    return false;
  }

  // V = Base + Offset through a chain of adds/subs of literal constants.
  // Runtime unrolling leaves the latch comparing and the IV stepping through
  // such chains (iv.next.1 = (iv + 1) + 1); the bounded matcher treats the
  // chain as the single literal recurrence it denotes.
  static Value *stripConstantOffset(Value *V, APInt &Offset) {
    Offset = APInt(V->getType()->getIntegerBitWidth(), 0);
    for (unsigned Depth = 0; Depth < 8; ++Depth) {
      auto *BO = dyn_cast<BinaryOperator>(V);
      if (!BO)
        break;
      if (BO->getOpcode() == Instruction::Add) {
        if (auto *C = dyn_cast<ConstantInt>(BO->getOperand(1))) {
          Offset += C->getValue();
          V = BO->getOperand(0);
          continue;
        }
        if (auto *C = dyn_cast<ConstantInt>(BO->getOperand(0))) {
          Offset += C->getValue();
          V = BO->getOperand(1);
          continue;
        }
      } else if (BO->getOpcode() == Instruction::Sub) {
        if (auto *C = dyn_cast<ConstantInt>(BO->getOperand(1))) {
          Offset -= C->getValue();
          V = BO->getOperand(0);
          continue;
        }
      }
      break;
    }
    return V;
  }

  // The header phi's latch value must be the phi plus a nonzero literal.
  static bool literalStep(const PHINode *IV, const Loop *L, APInt &Step) {
    Value *LatchIn = IV->getIncomingValueForBlock(L->getLoopLatch());
    if (!LatchIn->getType()->isIntegerTy() ||
        LatchIn->getType()->getIntegerBitWidth() > 64)
      return false;
    return stripConstantOffset(LatchIn, Step) == IV && !Step.isZero();
  }

  bool literalIndex(Value *V, const SiblingLeaf &Leaf,
                    SmallPtrSetImpl<Value *> &Seen) {
    if (isa<ConstantInt>(V))
      return true;
    auto *I = dyn_cast<Instruction>(V);
    if (!I || !Leaf.Blocks.contains(I->getParent()) || Seen.size() >= 32)
      return false;
    if (!Seen.insert(V).second)
      return true;
    if (auto *IV = dyn_cast<PHINode>(I)) {
      Loop *L = LI.getLoopFor(IV->getParent());
      if (!L || L->getHeader() != IV->getParent() || !Trips.contains(L) ||
          IV->getNumIncomingValues() != 2 ||
          IV->getBasicBlockIndex(L->getLoopPreheader()) < 0 ||
          IV->getBasicBlockIndex(L->getLoopLatch()) < 0 ||
          !isa<ConstantInt>(
              IV->getIncomingValueForBlock(L->getLoopPreheader())))
        return false;
      // A fully simplified two-trip loop may carry a literal latch value.
      if (isa<ConstantInt>(IV->getIncomingValueForBlock(L->getLoopLatch())))
        return true;
      APInt Step;
      return literalStep(IV, L, Step);
    }
    // A clamp such as min(k, 2j - i + 1) is a pure function of the IVs and
    // is evaluated exactly at every enumerated instance, like an add.
    if (const auto *II = dyn_cast<IntrinsicInst>(I)) {
      switch (II->getIntrinsicID()) {
      case Intrinsic::smin:
      case Intrinsic::smax:
      case Intrinsic::umin:
      case Intrinsic::umax:
        return literalIndex(II->getArgOperand(0), Leaf, Seen) &&
               literalIndex(II->getArgOperand(1), Leaf, Seen);
      default:
        return false;
      }
    }
    if (auto *Sel = dyn_cast<SelectInst>(I)) {
      const auto *Cmp = dyn_cast<ICmpInst>(Sel->getCondition());
      return Cmp && literalIndex(Cmp->getOperand(0), Leaf, Seen) &&
             literalIndex(Cmp->getOperand(1), Leaf, Seen) &&
             literalIndex(Sel->getTrueValue(), Leaf, Seen) &&
             literalIndex(Sel->getFalseValue(), Leaf, Seen);
    }
    switch (I->getOpcode()) {
    case Instruction::Or:
      // InstCombine rewrites an add of non-overlapping bit ranges as a
      // disjoint or (e.g. i + 1 when i is a multiple of 4); evaluate treats
      // it as the add it stands for.
      if (!cast<PossiblyDisjointInst>(I)->isDisjoint())
        return false;
      return all_of(I->operands(), [&](Value *Operand) {
        return literalIndex(Operand, Leaf, Seen);
      });
    case Instruction::Shl:
      // Power-of-two strides: InstCombine rewrites mul-by-2^k as shl.
      if (!isa<ConstantInt>(I->getOperand(1)))
        return false;
      [[fallthrough]];
    case Instruction::Add:
    case Instruction::Sub:
    case Instruction::Mul:
    case Instruction::Trunc:
    case Instruction::SExt:
    case Instruction::ZExt:
      return all_of(I->operands(), [&](Value *Operand) {
        return literalIndex(Operand, Leaf, Seen);
      });
    default:
      return false;
    }
  }

  bool footprint(Instruction *I, SiblingLeaf &Leaf, SiblingAccess &A) {
    MemoryLocation Loc = MemoryLocation::get(I);
    uint64_t Size;
    if (!getFixedLocationSize(Loc.Size, Size) || Size > 256 ||
        Loc.Ptr->getType()->getPointerAddressSpace() != 0 ||
        DL.getIndexSizeInBits(0) != 64 ||
        DL.isNonIntegralPointerType(Loc.Ptr->getType()))
      return reject("access size/address space", I);
    const Value *Ptr = Loc.Ptr;
    APInt ConstantOffset(64, 0);
    SmallVector<std::pair<Value *, APInt>, 4> Terms;
    unsigned PointerDepth = 0;
    while (const auto *PI = dyn_cast<Instruction>(Ptr)) {
      // Preserve an exact shared pre-leaf SSA root, including symbolic
      // quadrant offsets. It is not necessary to strip to an allocation.
      // "Before the phase" is too strict: pointer arithmetic used only by a
      // later spawn is routinely sunk into the continuation between spawns,
      // where it still dominates the leaves that use it.
      if (!Leaf.Blocks.contains(PI->getParent()) &&
          DT.dominates(PI, Leaf.Entry))
        break;
      if (++PointerDepth > 16 || !Leaf.Blocks.contains(PI->getParent()))
        return reject("pointer chain too deep or leaves the leaf", PI);
      if (const auto *G = dyn_cast<GEPOperator>(Ptr)) {
        SmallMapVector<Value *, APInt, 4> Variables;
        APInt Constant(64, 0);
        if (!G->collectOffset(DL, 64, Variables, Constant))
          return reject("GEP collectOffset failed", PI);
        ConstantOffset += Constant;
        for (auto &V : Variables) {
          SmallPtrSet<Value *, 16> Seen;
          if (!literalIndex(V.first, Leaf, Seen))
            return reject("GEP index is not a literal IV expression", V.first);
          Terms.emplace_back(V.first, V.second);
        }
        Ptr = G->getPointerOperand();
      } else if (const auto *BC = dyn_cast<BitCastInst>(PI)) {
        Ptr = BC->getOperand(0);
      } else {
        return reject("pointer operand is not GEP/bitcast (phi/select?)", PI);
      }
    }
    if (!isa<Argument, GlobalValue, Instruction>(Ptr))
      return reject("pointer root kind", Ptr);
    SmallVector<const Loop *, 4> Loops;
    unsigned Instances = 1;
    for (const Loop *L = LI.getLoopFor(I->getParent()); L;
         L = L->getParentLoop()) {
      auto It = Trips.find(L);
      if (It == Trips.end())
        return reject("access inside a loop without a literal trip", I);
      if (Instances > 4096 / It->second)
        return reject("more than 4096 loop instances for access", I);
      Instances *= It->second;
      Loops.push_back(L);
    }
    A = {I, Loc.Ptr, Ptr, Size, {}};
    DenseMap<const Loop *, unsigned> Point;
    for (unsigned Instance = 0; Instance < Instances; ++Instance) {
      unsigned Remaining = Instance;
      for (const Loop *L : Loops) {
        Point[L] = Remaining % Trips.lookup(L);
        Remaining /= Trips.lookup(L);
      }
      APInt ByteOffset = ConstantOffset;
      for (const auto &Term : Terms) {
        APInt Index(1, 0);
        if (!evaluate(Term.first, Point, Index))
          return reject("index evaluation failed", Term.first);
        ByteOffset += Index.sextOrTrunc(64) * Term.second;
      }
      int64_t Begin = ByteOffset.getSExtValue();
      // Guard the interval arithmetic against wrapped offsets; whole-plane
      // strides of a few MB (an image plane, a matrix) are ordinary.
      if (Begin < -(int64_t(1) << 40) || Begin > (int64_t(1) << 40))
        return reject("byte offset outside +-1TB", I);
      A.Bytes.emplace_back(Begin, Begin + Size);
    }
    normalizeSiblingIntervals(A.Bytes);
    return true;
  }

public:
  SmallVector<SiblingLeaf, 4> Leaves;

  SiblingPhaseBuilder(Function &F, TaskInfo &TI, LoopInfo &LI,
                      DetachInst *Start)
      : F(F), TI(TI), LI(LI), DT(TI.getDominatorTree()), DL(F.getDataLayout()),
        Start(Start), SyncRegion(Start->getSyncRegion()) {}

  bool build() {
    // A repeated fork phase would need a separate proof about combinations
    // of phase instances. This first implementation deliberately declines it.
    if (LI.getLoopFor(Start->getParent()))
      return reject("fork phase inside a loop", Start->getParent());
    DetachInst *D = Start;
    BasicBlock *Continuation = nullptr;
    while (D) {
      if (D->hasUnwindDest() || D->getSyncRegion() != SyncRegion ||
          Leaves.size() >= 8)
        return reject("detach unwind/sync-region/too many leaves", D);
      Leaves.emplace_back();
      BasicBlock *BB = D->getDetached();
      Leaves.back().Entry = BB;
      if (!walk(BB, Leaves.back()))
        return reject("detached leaf walk failed", D->getDetached());
      auto *R = dyn_cast<ReattachInst>(BB->getTerminator());
      if (!R || R->getSyncRegion() != SyncRegion ||
          R->getSuccessor(0) != D->getContinue())
        return reject("reattach shape", BB);
      Continuation = D->getContinue();
      D = dyn_cast<DetachInst>(Continuation->getTerminator());
      if (D) {
        // No conditional or potentially exiting prefix between spawns.
        if (!DT.dominates(Start->getParent(), Continuation) ||
            LI.getLoopFor(Continuation))
          return reject("continuation between spawns not dominated/in loop",
                        Continuation);
        // Ordinary loads and stores here belong to no leaf (they are neither
        // outputs nor witnesses) and cannot prevent the later spawns from
        // executing, so they do not disturb the proof. Calls and anything
        // else that may exit or have side effects still end the phase.
        for (Instruction &I : *Continuation) {
          if (I.isTerminator())
            continue;
          if (isa<LoadInst, StoreInst>(I) && isOrdinaryDRFMemoryAccess(&I))
            continue;
          if (I.mayReadOrWriteMemory() || I.mayHaveSideEffects() ||
              isa<CallBase>(I))
            return reject("memory/side-effect between spawns", &I);
        }
      }
    }
    Leaves.emplace_back();
    Leaves.back().Entry = Continuation;
    if (!walk(Continuation, Leaves.back()))
      return reject("continuation leaf walk failed", Continuation);
    auto *Sync = dyn_cast<SyncInst>(Continuation->getTerminator());
    if (!Sync || Sync->getSyncRegion() != SyncRegion)
      return reject("continuation does not end in sync of this region",
                    Continuation);
    for (SiblingLeaf &Leaf : Leaves)
      for (Instruction *I : Leaf.Memory) {
        SiblingAccess A;
        if (!footprint(I, Leaf, A))
          return false;
        Leaf.Accesses.push_back(std::move(A));
      }
    if (DRFAASiblingWitnessTrace)
      errs() << "DRF-SIBLING-TRACE accepted [" << F.getName() << "] phase at %"
             << Start->getParent()->getName() << " with " << Leaves.size()
             << " leaves\n";
    return true;
  }
};
} // namespace

struct DRFSiblingWitnessInfo::Impl {
  Function &F;
  bool Built = false;
  SmallVector<WeakVH, 32> Blocks;
  SmallVector<SiblingInstructionSnapshot, 128> Snapshot;
  SmallVector<AccessPair, 128> Pairs;
  DenseSet<AccessPair> SeenPairs;
  struct DirectFact {
    const Value *A;
    const Value *B;
    uint64_t ASize;
    uint64_t BSize;
    SmallVector<BasicBlock *, 8> LeafBlocks;
  };
  SmallVector<DirectFact, 128> DirectFacts;
  using PointerPair = std::pair<const Value *, const Value *>;
  DenseMap<PointerPair, SmallVector<unsigned, 2>> DirectIndex;
  unsigned NegativeQueries = 0;

  static PointerPair pointerKey(const Value *A, const Value *B) {
    if (std::less<const Value *>()(B, A))
      std::swap(A, B);
    return {A, B};
  }

  ArrayRef<unsigned> candidates(const Value *A, const Value *B) const {
    auto It = DirectIndex.find(pointerKey(A, B));
    return It == DirectIndex.end() ? ArrayRef<unsigned>()
                                   : ArrayRef<unsigned>(It->second);
  }

  explicit Impl(Function &F) : F(F) {}

  bool unchanged() const {
    if (!Built || F.size() != Blocks.size())
      return false;
    unsigned B = 0, N = 0;
    for (const BasicBlock &BB : F) {
      if (Blocks[B++] != &BB)
        return false;
      for (const Instruction &I : BB)
        if (N == Snapshot.size() || !Snapshot[N++].matches(I))
          return false;
    }
    return N == Snapshot.size();
  }

  void addFact(const SiblingAccess &A, const SiblingAccess &B,
               const SiblingLeaf &Leaf) {
    if (A.Inst == B.Inst || A.Base == B.Base)
      return;
    AccessPair Pair(A.Inst, B.Inst);
    if (!SeenPairs.contains(Pair) &&
        !SeenPairs.contains(AccessPair(B.Inst, A.Inst))) {
      SeenPairs.insert(Pair);
      Pairs.push_back(Pair);
      ++NumSiblingWitnessPairs;
    }
    // A direct fact is keyed on the two pointer operands. At least one must
    // be defined inside the leaf: that value exists only when the phase
    // executes, so any query naming it is pinned to the phase even without a
    // context instruction. The other may be the access's root itself (an
    // argument, a global, or a pointer computed before the leaf), which is
    // how an unrolled offset-0 element is addressed. Two roots are never
    // paired: on a path that skips the phase those addresses may coincide.
    auto InLeaf = [&](const Value *V) {
      const auto *I = dyn_cast<Instruction>(V);
      return I && Leaf.Blocks.contains(I->getParent());
    };
    auto RootOfF = [&](const Value *V) {
      if (const auto *Arg = dyn_cast<Argument>(V))
        return Arg->getParent() == &F;
      if (const auto *I = dyn_cast<Instruction>(V))
        return I->getParent() && I->getFunction() == &F;
      return isa<GlobalValue>(V);
    };
    bool AInLeaf = InLeaf(A.Ptr), BInLeaf = InLeaf(B.Ptr);
    if ((!AInLeaf && !BInLeaf) || !(AInLeaf || RootOfF(A.Ptr)) ||
        !(BInLeaf || RootOfF(B.Ptr)))
      return;
    auto &Indices = DirectIndex[pointerKey(A.Ptr, B.Ptr)];
    for (unsigned Index : Indices) {
      const DirectFact &D = DirectFacts[Index];
      if (D.A == A.Ptr && D.B == B.Ptr && D.ASize == A.Size &&
          D.BSize == B.Size && D.LeafBlocks.size() == Leaf.Blocks.size() &&
          all_of(D.LeafBlocks,
                 [&](BasicBlock *BB) { return Leaf.Blocks.contains(BB); }))
        return;
    }
    DirectFact D{A.Ptr, B.Ptr, A.Size, B.Size, {}};
    D.LeafBlocks.append(Leaf.Blocks.begin(), Leaf.Blocks.end());
    Indices.push_back(DirectFacts.size());
    DirectFacts.push_back(std::move(D));
  }

  void analyzePhase(SiblingPhaseBuilder &Phase, TaskInfo &TI) {
    DenseMap<std::pair<const Instruction *, const Instruction *>, bool>
        ParallelCache;
    auto Parallel = [&](const Instruction *A, const Instruction *B) {
      if (std::less<const Instruction *>()(B, A))
        std::swap(A, B);
      auto Key = std::make_pair(A, B);
      auto It = ParallelCache.find(Key);
      if (It != ParallelCache.end())
        return It->second;
      bool Result = TI.isDefinitelyLogicallyParallel(A, B);
      ParallelCache[Key] = Result;
      return Result;
    };
    for (SiblingLeaf &Leaf : Phase.Leaves) {
      DenseMap<std::pair<Instruction *, const Value *>, SiblingIntervals>
          ReadCache;
      DenseMap<const Value *, SiblingIntervals> Writes;
      for (const SiblingAccess &A : Leaf.Accesses)
        if (isa<StoreInst>(A.Inst))
          Writes[A.Base].append(A.Bytes.begin(), A.Bytes.end());
      for (auto &W : Writes)
        normalizeSiblingIntervals(W.second);

      for (const SiblingAccess &Input : Leaf.Accesses) {
        if (!isa<LoadInst>(Input.Inst))
          continue;
        for (const SiblingAccess &Output : Leaf.Accesses) {
          if (Output.Base == Input.Base)
            continue;
          // A read/read answer needs a real guaranteed conflicting write.
          if (isa<LoadInst>(Output.Inst)) {
            auto W = Writes.find(Output.Base);
            if (W == Writes.end() ||
                !siblingIntervalsCover(W->second, Output.Bytes))
              continue;
          }
          auto Key = std::make_pair(Output.Inst, Input.Base);
          auto Cached = ReadCache.find(Key);
          if (Cached == ReadCache.end()) {
            SiblingIntervals Reads;
            for (const SiblingLeaf &Other : Phase.Leaves) {
              if (&Other == &Leaf)
                continue;
              for (const SiblingAccess &Witness : Other.Accesses) {
                if (!isa<LoadInst>(Witness.Inst) ||
                    Witness.Base != Input.Base ||
                    !Parallel(Output.Inst, Witness.Inst))
                  continue;
                if (isa<LoadInst>(Output.Inst) &&
                    any_of(Leaf.Accesses, [&](const SiblingAccess &W) {
                      return isa<StoreInst>(W.Inst) && W.Base == Output.Base &&
                             !Parallel(W.Inst, Witness.Inst);
                    }))
                  continue;
                Reads.append(Witness.Bytes.begin(), Witness.Bytes.end());
              }
            }
            normalizeSiblingIntervals(Reads);
            Cached = ReadCache.try_emplace(Key, std::move(Reads)).first;
          }
          if (siblingIntervalsCover(Cached->second, Input.Bytes))
            addFact(Output, Input, Leaf);
        }
      }
    }
    if (DRFAASiblingWitnessTrace)
      errs() << "DRF-SIBLING-TRACE [" << F.getName() << "] facts so far: "
             << DirectFacts.size() << " direct, " << Pairs.size() << " pairs\n";
  }

  void refresh() {
    if (unchanged())
      return;
    ++NumSiblingWitnessCacheRebuilds;
    Pairs.clear();
    SeenPairs.clear();
    DirectFacts.clear();
    DirectIndex.clear();
    Snapshot.clear();
    Blocks.clear();
    // The snapshot also bounds work in functions unrelated to this narrow
    // prototype. Unsupported phases produce no facts, never partial coverage.
    if (F.size() <= 1024 &&
        all_of(F,
               [](const BasicBlock &BB) {
                 return BB.getTerminator() != nullptr;
               }) &&
        any_of(F, [](const BasicBlock &BB) {
          return isa<DetachInst>(BB.getTerminator());
        })) {
      // AA clients may temporarily leave even TaskInfo or LoopInfo stale.
      // Build private structural analyses from the exact IR snapshot; this
      // proof neither consults nor invalidates the client's cached analyses.
      DominatorTree DT(F);
      LoopInfo LI(DT);
      TaskInfo TI;
      TI.recalculate(F, DT);
      unsigned PhaseBudget = 16;
      for (BasicBlock &BB : F) {
        auto *D = dyn_cast<DetachInst>(BB.getTerminator());
        if (!D || !PhaseBudget)
          continue;
        --PhaseBudget;
        SiblingPhaseBuilder Phase(F, TI, LI, D);
        if (Phase.build()) {
          ++NumSiblingWitnessPhases;
          analyzePhase(Phase, TI);
        }
      }
    }
    for (BasicBlock &BB : F) {
      Blocks.emplace_back(&BB);
      for (Instruction &I : BB)
        Snapshot.emplace_back(I);
    }
    Built = true;
  }
};

DRFSiblingWitnessInfo::DRFSiblingWitnessInfo(Function &F)
    : P(std::make_unique<Impl>(F)) {}
DRFSiblingWitnessInfo::~DRFSiblingWitnessInfo() = default;

ArrayRef<DRFSiblingWitnessInfo::AccessPair>
DRFSiblingWitnessInfo::getNoAliasPairs() {
  if (!isDRFAASiblingWitnessEnabled())
    return {};
  P->refresh();
  return P->Pairs;
}

AliasResult DRFSiblingWitnessInfo::alias(const MemoryLocation &A,
                                         const MemoryLocation &B,
                                         const Instruction *CtxI) {
  uint64_t ASize, BSize;
  if (!isDRFAASiblingWitnessEnabled() || A.Ptr == B.Ptr ||
      !getFixedLocationSize(A.Size, ASize) ||
      !getFixedLocationSize(B.Size, BSize))
    return AliasResult::MayAlias;
  // A missing candidate is only a conservative missed optimization, even if
  // IR has changed. Avoid rescanning a large function for negative traffic;
  // periodically refresh so newly exposed pointer pairs can become eligible.
  // A cached positive is ALWAYS checked against the exact current snapshot.
  if (P->Built && P->candidates(A.Ptr, B.Ptr).empty() &&
      ++P->NegativeQueries < DRFAASiblingWitnessNegativeRefresh)
    return AliasResult::MayAlias;
  P->NegativeQueries = 0;
  P->refresh();
  const char *Why = "no candidate fact for this pointer pair";
  for (unsigned Index : P->candidates(A.Ptr, B.Ptr)) {
    const Impl::DirectFact &D = P->DirectFacts[Index];
    bool Match =
        (D.A == A.Ptr && D.B == B.Ptr && D.ASize == ASize &&
         D.BSize == BSize) ||
        (D.A == B.Ptr && D.B == A.Ptr && D.ASize == BSize && D.BSize == ASize);
    if (Match && (!CtxI || is_contained(D.LeafBlocks, CtxI->getParent()))) {
      ++NumSiblingWitnessAnswers;
      return AliasResult::NoAlias;
    }
    Why = Match ? "context instruction outside the fact's leaf"
                : "candidate fact has different access sizes";
  }
  if (DRFAASiblingWitnessTraceQueries && !P->DirectFacts.empty()) {
    static unsigned Printed = 0;
    if (Printed < DRFAASiblingWitnessTraceQueries) {
      ++Printed;
      errs() << "DRF-SIBLING-QUERY [" << P->F.getName() << "] unanswered ("
             << Why << ") sizes " << ASize << "/" << BSize << "\n   A: ";
      A.Ptr->print(errs(), true);
      errs() << "\n   B: ";
      B.Ptr->print(errs(), true);
      if (CtxI) {
        errs() << "\n   ctx: ";
        CtxI->print(errs(), true);
      }
      errs() << "\n";
    }
  }
  return AliasResult::MayAlias;
}

static void collectAddRecs(const SCEV *S, Type *ExpectedTy, ScalarEvolution &SE,
                           SmallVectorImpl<const SCEVAddRecExpr *> &AddRecs) {
  if (const auto *AR = dyn_cast<SCEVAddRecExpr>(S)) {
    if (SE.getEffectiveSCEVType(AR->getType()) == ExpectedTy)
      AddRecs.push_back(AR);
  }

  // Don't recurse through pointer/integer casts: their operands have a
  // different effective type than the outer expression.
  if (isa<SCEVPtrToIntExpr>(S))
    return;

  for (const SCEV *Op : S->operands())
    collectAddRecs(Op, ExpectedTy, SE, AddRecs);
}

static bool residualFitsInSlice(ScalarEvolution &SE, const SCEV *Residual,
                                uint64_t MaxOffset) {
  const ConstantRange Range = SE.getUnsignedRange(Residual);
  APInt Max(Range.getBitWidth(), MaxOffset);
  return Range.getUnsignedMax().ule(Max);
}

static bool proveNoAliasViaParallelSlices(const MemoryLocation &LocA,
                                          const MemoryLocation &LocB,
                                          ScalarEvolution &SE) {
  uint64_t SizeA = 0;
  uint64_t SizeB = 0;
  if (!getFixedLocationSize(LocA.Size, SizeA) ||
      !getFixedLocationSize(LocB.Size, SizeB))
    return false;

  const Value *BaseA = getUnderlyingObject(LocA.Ptr);
  const Value *BaseB = getUnderlyingObject(LocB.Ptr);
  if (!BaseA || BaseA != BaseB)
    return false;

  const SCEV *AS = SE.getSCEV(const_cast<Value *>(LocA.Ptr));
  const SCEV *BS = SE.getSCEV(const_cast<Value *>(LocB.Ptr));
  const SCEV *BaseS = SE.getSCEV(const_cast<Value *>(BaseA));
  Type *IntTy = SE.getEffectiveSCEVType(AS->getType());

  const SCEV *AInt = SE.getPtrToIntExpr(AS, IntTy);
  const SCEV *BInt = SE.getPtrToIntExpr(BS, IntTy);
  const SCEV *BaseInt = SE.getPtrToIntExpr(BaseS, IntTy);
  if (isa<SCEVCouldNotCompute>(AInt) || isa<SCEVCouldNotCompute>(BInt) ||
      isa<SCEVCouldNotCompute>(BaseInt))
    return false;

  if (!canComputePointerDiff(SE, AInt, BaseInt) ||
      !canComputePointerDiff(SE, BInt, BaseInt))
    return false;

  const SCEV *OffsetA = SE.getMinusSCEV(AInt, BaseInt);
  const SCEV *OffsetB = SE.getMinusSCEV(BInt, BaseInt);
  if (isa<SCEVCouldNotCompute>(OffsetA) || isa<SCEVCouldNotCompute>(OffsetB))
    return false;

  SmallVector<const SCEVAddRecExpr *, 4> AddRecsA;
  SmallVector<const SCEVAddRecExpr *, 4> AddRecsB;
  collectAddRecs(OffsetA, IntTy, SE, AddRecsA);
  collectAddRecs(OffsetB, IntTy, SE, AddRecsB);

  uint64_t BestStride = 0;
  const SCEVAddRecExpr *BestARA = nullptr;
  const SCEVAddRecExpr *BestARB = nullptr;
  for (const auto *ARA : AddRecsA) {
    const auto *StepA = dyn_cast<SCEVConstant>(ARA->getStepRecurrence(SE));
    if (!StepA || StepA->getAPInt().isZero())
      continue;

    uint64_t StrideA = StepA->getAPInt().abs().getLimitedValue();
    for (const auto *ARB : AddRecsB) {
      if (ARA->getLoop() != ARB->getLoop())
        continue;

      const auto *StepB = dyn_cast<SCEVConstant>(ARB->getStepRecurrence(SE));
      if (!StepB || StepB->getAPInt().isZero())
        continue;

      uint64_t StrideB = StepB->getAPInt().abs().getLimitedValue();
      if (StrideA != StrideB)
        continue;

      if (StrideA > BestStride) {
        BestARA = ARA;
        BestARB = ARB;
        BestStride = StrideA;
      }
    }
  }

  if (!BestARA || !BestARB || BestStride < SizeA || BestStride < SizeB)
    return false;

  const SCEV *ResidualA = SE.getMinusSCEV(OffsetA, BestARA);
  const SCEV *ResidualB = SE.getMinusSCEV(OffsetB, BestARB);
  if (isa<SCEVCouldNotCompute>(ResidualA) ||
      isa<SCEVCouldNotCompute>(ResidualB))
    return false;

  return residualFitsInSlice(SE, ResidualA, BestStride - SizeA) &&
         residualFitsInSlice(SE, ResidualB, BestStride - SizeB);
}

static bool scevMayVaryAcrossLoopIterations(const SCEV *S, const Loop *L) {
  if (const auto *AR = dyn_cast<SCEVAddRecExpr>(S)) {
    if (AR->getLoop() == L)
      return true;

    // A recurrence in a loop nested inside L may vary within each iteration of
    // L but still repeat the same access schedule in every sibling iteration.
    // Only its operands can make it depend on L's iteration.
    for (const SCEV *Op : AR->operands())
      if (scevMayVaryAcrossLoopIterations(Op, L))
        return true;
    return false;
  }

  if (const auto *U = dyn_cast<SCEVUnknown>(S)) {
    if (const auto *I = dyn_cast<Instruction>(U->getValue()))
      return L->contains(I);
    return false;
  }

  for (const SCEV *Op : S->operands())
    if (scevMayVaryAcrossLoopIterations(Op, L))
      return true;
  return false;
}

static void collectLoopsFromSCEV(const SCEV *S,
                                 SmallVectorImpl<const Loop *> &Loops,
                                 SmallPtrSetImpl<const Loop *> &Seen) {
  if (const auto *AR = dyn_cast<SCEVAddRecExpr>(S))
    if (Seen.insert(AR->getLoop()).second)
      Loops.push_back(AR->getLoop());

  for (const SCEV *Op : S->operands())
    collectLoopsFromSCEV(Op, Loops, Seen);
}

static bool accessMayRace(const Instruction *I) {
  if (const auto *SI = dyn_cast<StoreInst>(I))
    return !SI->isAtomic();
  if (isa<VAArgInst>(I))
    return true;
  return false;
}

static bool memoryInstUsesLocation(const Instruction *I,
                                   const MemoryLocation &Loc) {
  if (!I)
    return false;

  std::optional<MemoryLocation> ILoc = MemoryLocation::getOrNone(I);
  return ILoc && ILoc->Ptr == Loc.Ptr;
}

static const Instruction *findRepresentativeAccess(const MemoryLocation &Loc,
                                                   const Instruction *Addr) {
  if (memoryInstUsesLocation(Addr, Loc))
    return Addr;

  const Instruction *ReadAccess = nullptr;
  // ConstantData values (for example, a null pointer passed to a memory
  // intrinsic) deliberately have no use-list.  The explicit context above is
  // the only representative access available for such a location.
  if (!Loc.Ptr->hasUseList())
    return nullptr;
  for (const User *U : Loc.Ptr->users()) {
    const auto *UI = dyn_cast<Instruction>(U);
    if (!UI || !memoryInstUsesLocation(UI, Loc))
      continue;

    if (accessMayRace(UI))
      return UI;
    if (!ReadAccess)
      ReadAccess = UI;
  }
  return ReadAccess;
}

static void
collectRepresentativeAccesses(const MemoryLocation &Loc,
                              const Instruction *Addr,
                              SmallVectorImpl<const Instruction *> &Accesses) {
  constexpr unsigned MaxRepresentativeAccesses = 16;
  auto AddAccess = [&](const Instruction *I) {
    if (!I || !memoryInstUsesLocation(I, Loc))
      return;
    if (is_contained(Accesses, I))
      return;
    if (Accesses.size() < MaxRepresentativeAccesses)
      Accesses.push_back(I);
  };

  AddAccess(Addr);
  // ConstantData values have no use-list.  AddAccess already considered the
  // concrete query context, so there is nothing else to discover here.
  if (!Loc.Ptr->hasUseList())
    return;

  for (const User *U : Loc.Ptr->users())
    AddAccess(dyn_cast<Instruction>(U));
}

static bool isGuaranteedInEveryIteration(const Instruction *I, const Loop *L,
                                         const TaskInfo &TI) {
  if (!I || !L || !L->contains(I->getParent()))
    return false;

  const DominatorTree &DT = TI.getDominatorTree();
  SimpleLoopSafetyInfo LSafety;
  LSafety.computeLoopSafetyInfo(L);
  if (LSafety.isGuaranteedToExecute(*I, &DT, &TI, L))
    return true;

  // I is not directly guaranteed in L, typically because it is nested in inner
  // loop(s) that might run zero times.  Look through inner loops between I's
  // innermost loop and L, requiring each is *unconditionally entered* on every
  // iteration of its parent (so its execution does not depend on L's induction
  // variable -- this still rejects guards such as "if (i==0)").
  //
  // FIXME: For now we ASSUME each such inner loop runs at least twice, instead
  // of proving its trip count is invariant w.r.t. L and >= 2.  This is NOT
  // sound for an inner loop that may run zero/one times, or whose bound depends
  // on L's induction variable (e.g. a triangular "for (k = 0; k < i; ++k)"):
  // there I executes non-uniformly across L's iterations and the cross-
  // iteration race witness can be missing.  Revisit with an L-invariant-trip-
  // count (and >= 2) check before relying on this.
  const Loop *IL = L;
  for (bool Descended = true; Descended;) {
    Descended = false;
    for (const Loop *Sub : IL->getSubLoops())
      if (Sub->contains(I->getParent())) {
        IL = Sub;
        Descended = true;
        break;
      }
  }
  if (IL == L)
    return false; // Directly in L but conditional: cannot relax.

  for (const Loop *M = IL; M != L; M = M->getParentLoop()) {
    const Loop *P = M->getParentLoop();
    BasicBlock *PH = M->getLoopPreheader();
    if (!P || !PH)
      return false;
    SimpleLoopSafetyInfo PSafety;
    PSafety.computeLoopSafetyInfo(P);
    if (!PSafety.isGuaranteedToExecute(*PH->getTerminator(), &DT, &TI, P))
      return false;
  }

  SimpleLoopSafetyInfo ILSafety;
  ILSafety.computeLoopSafetyInfo(IL);
  return ILSafety.isGuaranteedToExecute(*I, &DT, &TI, IL);
}

/// Return true when entering Inner is an unconditional part of each logical
/// iteration of Parent. MustExecute deliberately treats a detached task body
/// as not executing on the continuation strand, so recognize the canonical
/// Tapir detach edge explicitly while rejecting ordinary conditional edges.
static bool isUnconditionallyEnteredFromParentIteration(const Loop *Inner,
                                                        const Loop *Parent) {
  const BasicBlock *Preheader = Inner->getLoopPreheader();
  if (!Preheader || !Parent->contains(Preheader) ||
      Preheader->getSingleSuccessor() != Inner->getHeader())
    return false;

  auto PrefixTransfersExecution = [](const BasicBlock *BB) {
    return isGuaranteedToTransferExecutionToSuccessor(
        BB->begin(), BB->getTerminator()->getIterator());
  };

  const BasicBlock *BB = Preheader;
  SmallPtrSet<const BasicBlock *, 8> Visited;
  while (BB != Parent->getHeader()) {
    if (!Visited.insert(BB).second || !Parent->contains(BB) ||
        !PrefixTransfersExecution(BB) || pred_size(BB) != 1)
      return false;

    const BasicBlock *Pred = *pred_begin(BB);
    if (!Parent->contains(Pred) || !PrefixTransfersExecution(Pred))
      return false;

    const Instruction *Term = Pred->getTerminator();
    if (const auto *BI = dyn_cast<BranchInst>(Term)) {
      if (!BI->isUnconditional() || BI->getSuccessor(0) != BB)
        return false;
    } else if (const auto *DI = dyn_cast<DetachInst>(Term)) {
      // A detach starts its detached successor on every execution even though
      // that successor is not on the continuation strand.
      if (DI->getDetached() != BB)
        return false;
    } else {
      return false;
    }
    BB = Pred;
  }

  return PrefixTransfersExecution(BB);
}

/// Return true when Access executes on every taken iteration of L. The usual
/// MustExecute query also considers the loop's zero-trip header exit, which is
/// deliberately covered here by the explicit minimum-trip assumption.
static bool executesOnEveryTakenLoopIteration(const Instruction *Access,
                                              const Loop *L,
                                              const TaskInfo &TI) {
  const DominatorTree &DT = TI.getDominatorTree();
  SimpleLoopSafetyInfo Safety;
  Safety.computeLoopSafetyInfo(L);
  if (Safety.isGuaranteedToExecute(*Access, &DT, &TI, L))
    return true;

  if (Safety.anyBlockMayThrow() ||
      !isGuaranteedToTransferExecutionToSuccessor(
          Access->getParent()->begin(), Access->getIterator()))
    return false;

  const BasicBlock *Latch = L->getLoopLatch();
  if (!Latch || !DT.dominates(Access, Latch->getTerminator()))
    return false;

  SmallVector<BasicBlock *, 4> ExitingBlocks;
  L->getExitingBlocks(ExitingBlocks);
  for (const BasicBlock *Exiting : ExitingBlocks) {
    // A canonical pretest header exits only after all taken iterations have
    // executed. Other exits must be reached after this concrete access.
    if (Exiting != L->getHeader() &&
        !DT.dominates(Access, Exiting->getTerminator()))
      return false;
  }
  return true;
}

/// Prove that Access supplies the same-address witness at matching inner-loop
/// coordinates in sibling iterations of ParallelLoop. Merely proving that an
/// instruction executes somewhere in every outer iteration is insufficient:
/// a triangular inner domain can contain a coordinate in only one sibling.
static bool hasReplicatedInnerSchedule(const Instruction *Access,
                                       const Loop *ParallelLoop,
                                       const TaskInfo &TI,
                                       ScalarEvolution &SE,
                                       bool &UsedNestedSchedule) {
  UsedNestedSchedule = false;
  if (!Access || !ParallelLoop ||
      !ParallelLoop->contains(Access->getParent()) ||
      DRFAAAssumedMinTripCount < 2 ||
      SE.getSmallConstantMaxTripCount(ParallelLoop) == 1)
    return false;

  const Loop *Innermost = ParallelLoop;
  for (bool Descended = true; Descended;) {
    Descended = false;
    for (const Loop *Sub : Innermost->getSubLoops())
      if (Sub->contains(Access->getParent())) {
        Innermost = Sub;
        Descended = true;
        break;
      }
  }

  const DominatorTree &DT = TI.getDominatorTree();
  if (Innermost == ParallelLoop) {
    SimpleLoopSafetyInfo Safety;
    Safety.computeLoopSafetyInfo(ParallelLoop);
    return Safety.isGuaranteedToExecute(*Access, &DT, &TI, ParallelLoop);
  }

  // Each intervening serial loop must be entered on every parent iteration
  // and must expose the same iteration domain in all sibling Tapir tasks. The
  // explicit minimum-trip assumption supplies non-emptiness; a statically
  // known one-trip loop still contradicts the race-witness requirement.
  for (const Loop *L = Innermost; L != ParallelLoop;
       L = L->getParentLoop()) {
    const Loop *Parent = L->getParentLoop();
    if (!Parent || !isUnconditionallyEnteredFromParentIteration(L, Parent) ||
        SE.getSmallConstantMaxTripCount(L) == 1)
      return false;

    const SCEV *BackedgeCount = SE.getBackedgeTakenCount(L);
    if (isa<SCEVCouldNotCompute>(BackedgeCount) ||
        !SE.isLoopInvariant(BackedgeCount, ParallelLoop))
      return false;
  }

  if (!executesOnEveryTakenLoopIteration(Access, Innermost, TI))
    return false;

  UsedNestedSchedule = true;
  return true;
}

static bool mayUseReboundTaskPrivateStorage(const MemoryLocation &Loc,
                                            const Loop *ParallelLoop,
                                            const TaskInfo &TI) {
  if (!ParallelLoop->wasDerivedFromTapirLoop() ||
      getTaskIfTapirLoopStructure(ParallelLoop,
                                  const_cast<TaskInfo *>(&TI)))
    return false;

  SmallVector<const Value *, 4> Objects;
  getUnderlyingObjects(Loc.Ptr, Objects);
  return any_of(Objects,
                [](const Value *Object) { return isa<AllocaInst>(Object); });
}

static bool addSignedConstantStep(const SCEVConstant *StepC, int64_t &Accum) {
  const APInt &Step = StepC->getAPInt();
  if (!Step.isSignedIntN(63))
    return false;

  int64_t StepValue = Step.getSExtValue();
  if ((StepValue > 0 &&
       Accum > std::numeric_limits<int64_t>::max() - StepValue) ||
      (StepValue < 0 &&
       Accum < std::numeric_limits<int64_t>::min() - StepValue))
    return false;

  Accum += StepValue;
  return true;
}

static bool collectConstantAddRecSteps(const SCEV *S, ScalarEvolution &SE,
                                       DenseMap<const Loop *, int64_t> &Steps,
                                       SmallPtrSetImpl<const SCEV *> &Seen) {
  if (!Seen.insert(S).second)
    return true;

  if (const auto *AR = dyn_cast<SCEVAddRecExpr>(S)) {
    const auto *StepC = dyn_cast<SCEVConstant>(AR->getStepRecurrence(SE));
    if (!StepC)
      return false;

    if (!addSignedConstantStep(StepC, Steps[AR->getLoop()]))
      return false;
  }

  for (const SCEV *Op : S->operands())
    if (!collectConstantAddRecSteps(Op, SE, Steps, Seen))
      return false;

  return true;
}

static bool containsUnknownDefinedInLoop(const SCEV *S, const Loop *L,
                                         SmallPtrSetImpl<const SCEV *> &Seen) {
  if (!Seen.insert(S).second)
    return false;

  if (const auto *U = dyn_cast<SCEVUnknown>(S))
    if (const auto *I = dyn_cast<Instruction>(U->getValue()))
      return L->contains(I->getParent());

  for (const SCEV *Op : S->operands())
    if (containsUnknownDefinedInLoop(Op, L, Seen))
      return true;

  return false;
}

static bool getParallelGradient(const SCEV *S, ScalarEvolution &SE,
                                ArrayRef<const Loop *> ParallelLoops,
                                SmallVectorImpl<int64_t> &Gradient) {
  DenseMap<const Loop *, int64_t> Steps;
  SmallPtrSet<const SCEV *, 16> Seen;
  if (!collectConstantAddRecSteps(S, SE, Steps, Seen))
    return false;

  Gradient.clear();
  for (const Loop *L : ParallelLoops) {
    // Treat addrecs in non-parallel child loops as parameters, but do not let
    // an opaque value computed inside the parallel loop masquerade as a
    // loop-invariant zero step.  For example, b[idx[j]] has no addrec in the
    // Tapir loop, but the loaded idx[j] is still lane-varying.
    SmallPtrSet<const SCEV *, 16> UnknownSeen;
    if (containsUnknownDefinedInLoop(S, L, UnknownSeen))
      return false;

    Gradient.push_back(Steps.lookup(L));
  }
  return true;
}

static void
collectSmallNonZeroNullDirections(ArrayRef<int64_t> Gradient,
                                  SmallVectorImpl<SmallVector<int, 4>> &Dirs) {
  if (Gradient.empty() || Gradient.size() > 4)
    return;

  // Search only the cheap adjacent directions. This captures replicated
  // diagonal accesses such as covariance's data[k][j] over (i, j - i) without
  // turning every alias query into a general integer-nullspace problem.
  SmallVector<int, 4> Dir(Gradient.size(), 0);
  std::function<void(unsigned, bool, int64_t)> Search = [&](unsigned I,
                                                            bool AnyNonZero,
                                                            int64_t Dot) {
    if (I == Gradient.size()) {
      if (AnyNonZero && Dot == 0)
        Dirs.push_back(Dir);
      return;
    }

    for (int Step : {-1, 0, 1}) {
      int64_t Product = 0;
      if (Step != 0) {
        if (Gradient[I] == std::numeric_limits<int64_t>::min())
          continue;
        Product = Step * Gradient[I];
      }

      if ((Product > 0 &&
           Dot > std::numeric_limits<int64_t>::max() - Product) ||
          (Product < 0 && Dot < std::numeric_limits<int64_t>::min() - Product))
        continue;

      Dir[I] = Step;
      Search(I + 1, AnyNonZero || Step != 0, Dot + Product);
    }
    Dir[I] = 0;
  };

  Search(0, false, 0);
}

static bool
hasEnoughIterationsForFiberDirection(ArrayRef<const Loop *> ParallelLoops,
                                     ArrayRef<int> Direction) {
  if (ParallelLoops.empty() || ParallelLoops.size() != Direction.size())
    return false;

  // FIXME: This proof still assumes the symbolic Tapir-loop trip counts are
  // large enough whenever ScalarEvolution cannot prove a constant count. The
  // fiber-coverage logic below proves the address-domain shape; replace this
  // fallback with a real >=2 trip-count/domain proof before using it for
  // arbitrary inputs.
  return true;
}

static const SCEVAddRecExpr *findAddRecForLoop(const SCEV *S, const Loop *L) {
  if (const auto *AR = dyn_cast<SCEVAddRecExpr>(S))
    if (AR->getLoop() == L)
      return AR;

  for (const SCEV *Op : S->operands())
    if (const SCEVAddRecExpr *Found = findAddRecForLoop(Op, L))
      return Found;

  return nullptr;
}

class SCEVLoopStartRewriter : public SCEVRewriteVisitor<SCEVLoopStartRewriter> {
public:
  static const SCEV *rewrite(const SCEV *S, const Loop *L,
                             ScalarEvolution &SE) {
    SCEVLoopStartRewriter Rewriter(SE, L);
    return Rewriter.visit(S);
  }

  const SCEV *visitAddRecExpr(const SCEVAddRecExpr *Expr) {
    if (Expr->getLoop() == L)
      return visit(Expr->getStart());

    return SCEVRewriteVisitor<SCEVLoopStartRewriter>::visitAddRecExpr(Expr);
  }

private:
  SCEVLoopStartRewriter(ScalarEvolution &SE, const Loop *L)
      : SCEVRewriteVisitor(SE), L(L) {}

  const Loop *L;
};

class SCEVLoopShiftRewriter : public SCEVRewriteVisitor<SCEVLoopShiftRewriter> {
public:
  static const SCEV *rewrite(const SCEV *S, const Loop *L, int64_t Shift,
                             ScalarEvolution &SE) {
    SCEVLoopShiftRewriter Rewriter(SE, L, Shift);
    const SCEV *Result = Rewriter.visit(S);
    return Rewriter.Valid ? Result : SE.getCouldNotCompute();
  }

  const SCEV *visitAddRecExpr(const SCEVAddRecExpr *Expr) {
    SmallVector<const SCEV *, 2> Operands;
    for (const SCEV *Op : Expr->operands()) {
      const SCEV *Visited = visit(Op);
      if (isa<SCEVCouldNotCompute>(Visited)) {
        Valid = false;
        return SE.getCouldNotCompute();
      }
      Operands.push_back(Visited);
    }

    if (Expr->getLoop() != L)
      return SE.getAddRecExpr(Operands, Expr->getLoop(),
                              Expr->getNoWrapFlags());

    if (Operands.size() != 2) {
      Valid = false;
      return SE.getCouldNotCompute();
    }

    Type *StepTy = SE.getEffectiveSCEVType(Operands[1]->getType());
    const SCEV *ShiftS = SE.getConstant(StepTy, Shift, true);
    const SCEV *Delta = SE.getMulExpr(Operands[1], ShiftS);
    const SCEV *ShiftedStart = SE.getAddExpr(Operands[0], Delta);
    return SE.getAddRecExpr(ShiftedStart, Operands[1], Expr->getLoop(),
                            SCEV::FlagAnyWrap);
  }

private:
  SCEVLoopShiftRewriter(ScalarEvolution &SE, const Loop *L, int64_t Shift)
      : SCEVRewriteVisitor(SE), L(L), Shift(Shift) {}

  const Loop *L;
  int64_t Shift;
  bool Valid = true;
};

class SCEVLoopSymbolicShiftRewriter
    : public SCEVRewriteVisitor<SCEVLoopSymbolicShiftRewriter> {
public:
  static const SCEV *rewrite(const SCEV *S, const Loop *L, const SCEV *Shift,
                             ScalarEvolution &SE) {
    SCEVLoopSymbolicShiftRewriter Rewriter(SE, L, Shift);
    const SCEV *Result = Rewriter.visit(S);
    return Rewriter.Valid ? Result : SE.getCouldNotCompute();
  }

  const SCEV *visitAddRecExpr(const SCEVAddRecExpr *Expr) {
    SmallVector<const SCEV *, 2> Operands;
    for (const SCEV *Op : Expr->operands()) {
      const SCEV *Visited = visit(Op);
      if (isa<SCEVCouldNotCompute>(Visited)) {
        Valid = false;
        return SE.getCouldNotCompute();
      }
      Operands.push_back(Visited);
    }

    if (Expr->getLoop() != L)
      return SE.getAddRecExpr(Operands, Expr->getLoop(),
                              Expr->getNoWrapFlags());

    if (Operands.size() != 2) {
      Valid = false;
      return SE.getCouldNotCompute();
    }

    // Trip counts are deliberately widened before adding one.  A symbolic
    // upper-bound coordinate can therefore be wider than the address addrec's
    // step even though the coordinate itself is representable in the loop-IV
    // type.  Normalize it before forming the product required by SCEV.
    Type *StepTy = SE.getEffectiveSCEVType(Operands[1]->getType());
    const SCEV *TypedShift = SE.getTruncateOrZeroExtend(Shift, StepTy);
    const SCEV *Delta = SE.getMulExpr(Operands[1], TypedShift);
    const SCEV *ShiftedStart = SE.getAddExpr(Operands[0], Delta);
    return SE.getAddRecExpr(ShiftedStart, Operands[1], Expr->getLoop(),
                            SCEV::FlagAnyWrap);
  }

private:
  SCEVLoopSymbolicShiftRewriter(ScalarEvolution &SE, const Loop *L,
                                const SCEV *Shift)
      : SCEVRewriteVisitor(SE), L(L), Shift(Shift) {}

  const Loop *L;
  const SCEV *Shift;
  bool Valid = true;
};

static bool scevExpressionsEqual(ScalarEvolution &SE, const SCEV *A,
                                 const SCEV *B) {
  if (A == B)
    return true;

  Type *ATy = SE.getEffectiveSCEVType(A->getType());
  Type *BTy = SE.getEffectiveSCEVType(B->getType());
  if (ATy != BTy)
    return false;

  if (A->getType()->isPointerTy())
    A = SE.getPtrToIntExpr(A, ATy);
  if (B->getType()->isPointerTy())
    B = SE.getPtrToIntExpr(B, BTy);
  if (isa<SCEVCouldNotCompute>(A) || isa<SCEVCouldNotCompute>(B))
    return false;

  return SE.isKnownPredicate(CmpInst::ICMP_EQ, A, B);
}

static bool hasAxisReplication(const Instruction *Access, const SCEV *AddrS,
                               const TaskInfo &TI, ScalarEvolution &SE,
                               ArrayRef<const Loop *> ParallelLoops) {
  SmallVector<int64_t, 4> Gradient;
  if (!getParallelGradient(AddrS, SE, ParallelLoops, Gradient))
    return false;

  for (auto [Idx, Step] : enumerate(Gradient)) {
    if (Step != 0)
      continue;

    const Loop *L = ParallelLoops[Idx];
    bool UsedNestedSchedule = false;
    if (!hasReplicatedInnerSchedule(Access, L, TI, SE, UsedNestedSchedule))
      continue;

    SmallVector<int, 4> Direction(Gradient.size(), 0);
    Direction[Idx] = 1;
    if (hasEnoughIterationsForFiberDirection(ParallelLoops, Direction))
      return true;
  }

  return false;
}

static bool parallelPointDiffers(ArrayRef<int64_t> A, ArrayRef<int64_t> B) {
  if (A.size() != B.size())
    return false;

  for (auto [X, Y] : zip(A, B))
    if (X != Y)
      return true;
  return false;
}

static bool parallelLoopComesBefore(const Loop *A, const Loop *B) {
  if (A == B)
    return false;
  if (A->contains(B->getHeader()))
    return true;
  if (B->contains(A->getHeader()))
    return false;
  return A->getLoopDepth() < B->getLoopDepth();
}

static void sortLoopsOuterToInner(SmallVectorImpl<const Loop *> &Loops) {
  for (unsigned I = 1; I < Loops.size(); ++I) {
    const Loop *L = Loops[I];
    unsigned J = I;
    while (J > 0 && parallelLoopComesBefore(L, Loops[J - 1])) {
      Loops[J] = Loops[J - 1];
      --J;
    }
    Loops[J] = L;
  }
}

static const SCEV *evaluateSCEVAtAssignedParallelPoint(
    const SCEV *S, ArrayRef<const Loop *> ParallelLoops,
    ArrayRef<int64_t> Point, unsigned NumAssigned, ScalarEvolution &SE) {
  const SCEV *Result = S;
  for (unsigned I = 0; I < NumAssigned; ++I) {
    if (Point[I] == 0)
      continue;

    Result =
        SCEVLoopShiftRewriter::rewrite(Result, ParallelLoops[I], Point[I], SE);
    if (isa<SCEVCouldNotCompute>(Result))
      return Result;
  }

  for (unsigned I = 0; I < NumAssigned; ++I) {
    Result = SCEVLoopStartRewriter::rewrite(Result, ParallelLoops[I], SE);
    if (isa<SCEVCouldNotCompute>(Result))
      return Result;
  }

  return Result;
}

static const SCEV *
evaluateSCEVAtParallelPoint(const SCEV *S, ArrayRef<const Loop *> ParallelLoops,
                            ArrayRef<int64_t> Point, ScalarEvolution &SE) {
  return evaluateSCEVAtAssignedParallelPoint(S, ParallelLoops, Point,
                                             ParallelLoops.size(), SE);
}

static bool getTripCountAtParallelPoint(ArrayRef<const Loop *> ParallelLoops,
                                        ArrayRef<int64_t> Point,
                                        unsigned LoopIdx, ScalarEvolution &SE,
                                        int64_t &TripCount) {
  const SCEV *BTC = SE.getBackedgeTakenCount(ParallelLoops[LoopIdx]);
  if (isa<SCEVCouldNotCompute>(BTC))
    return false;

  const SCEV *TripS = SE.getAddExpr(BTC, SE.getConstant(BTC->getType(), 1));
  TripS = evaluateSCEVAtAssignedParallelPoint(TripS, ParallelLoops, Point,
                                              LoopIdx, SE);
  const auto *TripC = dyn_cast<SCEVConstant>(TripS);
  if (!TripC || !TripC->getAPInt().isSignedIntN(31))
    return false;

  TripCount = TripC->getAPInt().getSExtValue();
  return TripCount > 0;
}

static bool enumerateParallelDomainPoints(
    ArrayRef<const Loop *> ParallelLoops, ScalarEvolution &SE,
    const std::function<bool(ArrayRef<int64_t>)> &Visit) {
  if (ParallelLoops.empty() || ParallelLoops.size() > 4)
    return false;

  constexpr uint64_t MaxEnumeratedPoints = 8192;
  uint64_t NumPoints = 0;
  SmallVector<int64_t, 4> Point(ParallelLoops.size(), 0);
  std::function<bool(unsigned)> Enumerate = [&](unsigned LoopIdx) {
    if (LoopIdx == ParallelLoops.size()) {
      if (++NumPoints > MaxEnumeratedPoints)
        return false;
      return Visit(Point);
    }

    int64_t TripCount = 0;
    if (!getTripCountAtParallelPoint(ParallelLoops, Point, LoopIdx, SE,
                                     TripCount))
      return false;

    for (int64_t I = 0; I < TripCount; ++I) {
      Point[LoopIdx] = I;
      if (!Enumerate(LoopIdx + 1))
        return false;
    }
    Point[LoopIdx] = 0;
    return true;
  };

  return Enumerate(0);
}

static bool accessCanWitnessRaceWithWrite(const Instruction *I) {
  if (const auto *LI = dyn_cast<LoadInst>(I))
    return !LI->isAtomic() && !LI->isVolatile();
  if (const auto *SI = dyn_cast<StoreInst>(I))
    return !SI->isAtomic() && !SI->isVolatile();
  return isa<VAArgInst>(I);
}

static bool
isGuaranteedInEveryParallelIteration(const Instruction *I, const TaskInfo &TI,
                                     ArrayRef<const Loop *> ParallelLoops) {
  for (const Loop *L : ParallelLoops)
    if (!isGuaranteedInEveryIteration(I, L, TI))
      return false;
  return true;
}

struct ParallelAddressTouch {
  const SCEV *Addr = nullptr;
  SmallVector<int64_t, 4> Point;
};

static bool
appendParallelAddressTouches(const Instruction *Access, ScalarEvolution &SE,
                             ArrayRef<const Loop *> ParallelLoops,
                             SmallVectorImpl<ParallelAddressTouch> &Touches) {
  std::optional<MemoryLocation> Loc = MemoryLocation::getOrNone(Access);
  if (!Loc)
    return false;

  const SCEV *AddrS = SE.getSCEV(const_cast<Value *>(Loc->Ptr));
  if (isa<SCEVCouldNotCompute>(AddrS))
    return false;

  SmallVector<int64_t, 4> Gradient;
  if (!getParallelGradient(AddrS, SE, ParallelLoops, Gradient))
    return false;

  constexpr unsigned MaxAddressTouches = 65536;
  return enumerateParallelDomainPoints(
      ParallelLoops, SE, [&](ArrayRef<int64_t> Point) {
        const SCEV *AddrAtPoint =
            evaluateSCEVAtParallelPoint(AddrS, ParallelLoops, Point, SE);
        if (isa<SCEVCouldNotCompute>(AddrAtPoint) ||
            Touches.size() >= MaxAddressTouches)
          return false;

        ParallelAddressTouch Touch;
        Touch.Addr = AddrAtPoint;
        Touch.Point.append(Point.begin(), Point.end());
        Touches.push_back(std::move(Touch));
        return true;
      });
}

static bool collectParallelWitnessAccesses(
    const Instruction *Access, const Instruction *OtherAccess,
    const TaskInfo &TI, ScalarEvolution &SE,
    ArrayRef<const Loop *> ParallelLoops,
    SmallVectorImpl<const Instruction *> &Witnesses) {
  if (!accessMayRace(OtherAccess))
    return false;

  Witnesses.push_back(Access);
  const BasicBlock *BB = Access->getParent();
  for (const Instruction &I : *BB) {
    if (&I == Access || !accessCanWitnessRaceWithWrite(&I))
      continue;

    std::optional<MemoryLocation> Loc = MemoryLocation::getOrNone(&I);
    if (!Loc)
      continue;

    // A hyperobject view access cannot serve as an ordinary race witness:
    // view accesses of one hyperobject in parallel strands are runtime-
    // mediated and may legally touch the same storage.
    if (EnableDRFAAHyperView && getHyperViewHyperobject(Loc->Ptr))
      continue;

    if (!isGuaranteedInEveryParallelIteration(&I, TI, ParallelLoops))
      continue;

    const SCEV *IS = SE.getSCEV(const_cast<Value *>(Loc->Ptr));
    if (isa<SCEVCouldNotCompute>(IS))
      continue;

    SmallVector<int64_t, 4> Gradient;
    if (!getParallelGradient(IS, SE, ParallelLoops, Gradient))
      continue;

    Witnesses.push_back(&I);
  }

  return true;
}

static const SCEV *getLoopTripCountSCEV(const Loop *L, ScalarEvolution &SE) {
  const SCEV *BTC = SE.getBackedgeTakenCount(L);
  if (isa<SCEVCouldNotCompute>(BTC))
    return SE.getCouldNotCompute();

  // Adding one in the backedge count's type can wrap for narrow counters.  In
  // particular, a one-iteration generated loop has an i1 backedge count of
  // false; false + 1 is i1 true, which the signed affine linearizer reads as
  // -1.  Evaluate narrow counts in i64 before the addition, while preserving
  // the type of wider symbolic counts used by existing affine proofs.
  unsigned CountWidth = BTC->getType()->getIntegerBitWidth();
  Type *EvalTy =
      Type::getIntNTy(BTC->getType()->getContext(), std::max(CountWidth, 64U));
  return SE.getTripCountFromExitCount(BTC, EvalTy, L);
}

static const SCEV *addSignedConstantToSCEV(const SCEV *S, int64_t C,
                                           ScalarEvolution &SE) {
  Type *Ty = SE.getEffectiveSCEVType(S->getType());
  return SE.getAddExpr(S, SE.getConstant(Ty, C, true));
}

enum class SymbolicBoundaryKind { Lower, Upper };

struct SymbolicBoundary {
  SymbolicBoundaryKind Kind = SymbolicBoundaryKind::Lower;
  unsigned LoopIdx = 0;
  SmallVector<int, 4> TripShift;
  int64_t CoordOffset = 0;
};

// A face is a symbolic over-approximation of singleton-fiber points.  Covering
// every returned face by a companion access is sufficient, even when only a
// corner of that face is actually deficient.
struct SymbolicDeficientFace {
  SmallVector<SymbolicBoundary, 4> Boundaries;
};

static SymbolicBoundary makeLowerBoundary(unsigned LoopIdx) {
  return {SymbolicBoundaryKind::Lower, LoopIdx, {}, 0};
}

static SymbolicBoundary makeUpperBoundary(unsigned LoopIdx,
                                          ArrayRef<int> TripShift,
                                          int64_t CoordOffset) {
  SymbolicBoundary Boundary;
  Boundary.Kind = SymbolicBoundaryKind::Upper;
  Boundary.LoopIdx = LoopIdx;
  Boundary.TripShift.append(TripShift.begin(), TripShift.end());
  Boundary.CoordOffset = CoordOffset;
  return Boundary;
}

struct SymbolicLinearContext {
  ArrayRef<const Loop *> ParallelLoops;
  DenseMap<const Loop *, unsigned> LoopIndices;
  DenseMap<const SCEV *, unsigned> SymbolIndices;

  SymbolicLinearContext(ArrayRef<const Loop *> ParallelLoops)
      : ParallelLoops(ParallelLoops) {
    for (auto [Idx, L] : enumerate(ParallelLoops))
      LoopIndices[L] = Idx;
  }

  unsigned getNumVars() const {
    return ParallelLoops.size() + SymbolIndices.size();
  }

  std::optional<unsigned> getLoopVar(const Loop *L) const {
    auto It = LoopIndices.find(L);
    if (It == LoopIndices.end())
      return std::nullopt;
    return It->second;
  }

  unsigned getOrCreateSymbol(const SCEV *S) {
    auto Insert = SymbolIndices.try_emplace(S, getNumVars());
    return Insert.first->second;
  }
};

struct SymbolicLinearExpr {
  int64_t Constant = 0;
  SmallVector<int64_t, 8> Coeffs;

  void ensureVar(unsigned Var) {
    if (Coeffs.size() <= Var)
      Coeffs.resize(Var + 1, 0);
  }

  bool addConstant(int64_t C) { return !AddOverflow(Constant, C, Constant); }

  bool addCoeff(unsigned Var, int64_t C) {
    ensureVar(Var);
    return !AddOverflow(Coeffs[Var], C, Coeffs[Var]);
  }

  bool addScaled(const SymbolicLinearExpr &Other, int64_t Scale = 1) {
    int64_t ScaledConstant = 0;
    if (MulOverflow(Other.Constant, Scale, ScaledConstant) ||
        AddOverflow(Constant, ScaledConstant, Constant))
      return false;

    if (Coeffs.size() < Other.Coeffs.size())
      Coeffs.resize(Other.Coeffs.size(), 0);
    for (auto [Idx, C] : enumerate(Other.Coeffs)) {
      int64_t ScaledCoeff = 0;
      if (MulOverflow(C, Scale, ScaledCoeff) ||
          AddOverflow(Coeffs[Idx], ScaledCoeff, Coeffs[Idx]))
        return false;
    }
    return true;
  }
};

static bool getSignedConstantValue(const SCEV *S, int64_t &Value) {
  const auto *C = dyn_cast<SCEVConstant>(S);
  if (!C || !C->getAPInt().isSignedIntN(63))
    return false;
  Value = C->getAPInt().getSExtValue();
  return true;
}

static bool linearizeSCEV(const SCEV *S, SymbolicLinearContext &Ctx,
                          ScalarEvolution &SE, SymbolicLinearExpr &Result);

static bool linearizeAddRec(const SCEVAddRecExpr *AR,
                            SymbolicLinearContext &Ctx, ScalarEvolution &SE,
                            SymbolicLinearExpr &Result) {
  if (AR->getNumOperands() != 2)
    return false;

  SymbolicLinearExpr Start;
  if (!linearizeSCEV(AR->getStart(), Ctx, SE, Start) ||
      !Result.addScaled(Start))
    return false;

  int64_t Step = 0;
  if (!getSignedConstantValue(AR->getStepRecurrence(SE), Step))
    return false;

  std::optional<unsigned> LoopVar = Ctx.getLoopVar(AR->getLoop());
  if (!LoopVar)
    return false;

  return Result.addCoeff(*LoopVar, Step);
}

static bool linearizeMulExpr(const SCEVMulExpr *Mul, SymbolicLinearContext &Ctx,
                             ScalarEvolution &SE, SymbolicLinearExpr &Result) {
  int64_t Scale = 1;
  const SCEV *NonConstantOp = nullptr;
  for (const SCEV *Op : Mul->operands()) {
    int64_t C = 0;
    if (getSignedConstantValue(Op, C)) {
      if (MulOverflow(Scale, C, Scale))
        return false;
      continue;
    }

    if (NonConstantOp)
      return false;
    NonConstantOp = Op;
  }

  if (!NonConstantOp)
    return Result.addConstant(Scale);

  SymbolicLinearExpr OpResult;
  if (!linearizeSCEV(NonConstantOp, Ctx, SE, OpResult))
    return false;
  return Result.addScaled(OpResult, Scale);
}

static bool linearizeSCEV(const SCEV *S, SymbolicLinearContext &Ctx,
                          ScalarEvolution &SE, SymbolicLinearExpr &Result) {
  if (const auto *P2I = dyn_cast<SCEVPtrToIntExpr>(S))
    return linearizeSCEV(P2I->getOperand(), Ctx, SE, Result);

  if (const auto *C = dyn_cast<SCEVConstant>(S)) {
    if (!C->getAPInt().isSignedIntN(63))
      return false;
    return Result.addConstant(C->getAPInt().getSExtValue());
  }

  if (const auto *Add = dyn_cast<SCEVAddExpr>(S)) {
    for (const SCEV *Op : Add->operands()) {
      SymbolicLinearExpr OpResult;
      if (!linearizeSCEV(Op, Ctx, SE, OpResult) || !Result.addScaled(OpResult))
        return false;
    }
    return true;
  }

  if (const auto *Mul = dyn_cast<SCEVMulExpr>(S))
    return linearizeMulExpr(Mul, Ctx, SE, Result);

  if (const auto *AR = dyn_cast<SCEVAddRecExpr>(S))
    return linearizeAddRec(AR, Ctx, SE, Result);

  if (isa<SCEVUnknown>(S))
    return Result.addCoeff(Ctx.getOrCreateSymbol(S), 1);

  return false;
}

struct SymbolicConstraintSet {
  SymbolicLinearContext &Ctx;
  SmallVector<SmallVector<int64_t, 8>, 16> Rows;
  bool IsUnsat = false;

  SymbolicConstraintSet(SymbolicLinearContext &Ctx) : Ctx(Ctx) {}

  bool addAffineLEZero(const SymbolicLinearExpr &Expr) {
    if (IsUnsat)
      return true;

    bool HasVariable = false;
    for (int64_t C : Expr.Coeffs)
      HasVariable |= C != 0;

    if (!HasVariable) {
      if (Expr.Constant > 0)
        IsUnsat = true;
      return true;
    }

    SmallVector<int64_t, 8> Row(Ctx.getNumVars() + 1, 0);
    if (SubOverflow(int64_t(0), Expr.Constant, Row[0]))
      return false;
    for (auto [Idx, C] : enumerate(Expr.Coeffs)) {
      if (C == 0)
        continue;
      if (Row.size() <= Idx + 1)
        Row.resize(Idx + 2, 0);
      Row[Idx + 1] = C;
    }
    Rows.push_back(std::move(Row));
    return true;
  }

  bool mayHaveSolution() const {
    if (IsUnsat)
      return false;

    ConstraintSystem CS;
    unsigned RowSize = Ctx.getNumVars() + 1;
    for (SmallVector<int64_t, 8> Row : Rows) {
      Row.resize(RowSize, 0);
      CS.addVariableRow(Row);
    }
    return CS.mayHaveSolution();
  }
};

static SymbolicLinearExpr makeLoopVarExpr(unsigned LoopIdx) {
  SymbolicLinearExpr Expr;
  Expr.addCoeff(LoopIdx, 1);
  return Expr;
}

static bool subtractExpr(SymbolicLinearExpr &LHS,
                         const SymbolicLinearExpr &RHS) {
  return LHS.addScaled(RHS, -1);
}

static bool isZeroExpr(const SymbolicLinearExpr &Expr) {
  if (Expr.Constant != 0)
    return false;
  for (int64_t C : Expr.Coeffs)
    if (C != 0)
      return false;
  return true;
}

static bool negateLEZeroForIntegerDomain(const SymbolicLinearExpr &Expr,
                                         SymbolicLinearExpr &Negated) {
  // Negate "Expr <= 0" over integer variables:
  //   !(Expr <= 0)  <=>  Expr >= 1  <=>  1 - Expr <= 0.
  return Negated.addConstant(1) && Negated.addScaled(Expr, -1);
}

static const SCEV *getShiftedTripCountSCEV(unsigned LoopIdx,
                                           ArrayRef<const Loop *> ParallelLoops,
                                           ArrayRef<int> Shift,
                                           ScalarEvolution &SE) {
  const SCEV *Trip = getLoopTripCountSCEV(ParallelLoops[LoopIdx], SE);
  if (isa<SCEVCouldNotCompute>(Trip))
    return Trip;

  for (unsigned I = 0; I < LoopIdx && I < Shift.size(); ++I) {
    if (Shift[I] == 0)
      continue;
    Trip = SCEVLoopShiftRewriter::rewrite(Trip, ParallelLoops[I], Shift[I], SE);
    if (isa<SCEVCouldNotCompute>(Trip))
      return Trip;
  }
  return Trip;
}

static bool linearizeTripCount(unsigned LoopIdx,
                               ArrayRef<const Loop *> ParallelLoops,
                               ArrayRef<int> Shift, ScalarEvolution &SE,
                               SymbolicLinearContext &Ctx,
                               SymbolicLinearExpr &Trip) {
  const SCEV *TripS =
      getShiftedTripCountSCEV(LoopIdx, ParallelLoops, Shift, SE);
  if (isa<SCEVCouldNotCompute>(TripS))
    return false;

  if (DRFAAAssumedMinTripCount > 1) {
    // The assumed minimum supplies cross-iteration witnesses; it must never
    // erase an exact transformed-loop domain.  Strip-mining, for example, can
    // create a one-iteration outer loop from a large source loop.  If SCEV
    // proves that this modeled loop cannot meet the minimum, abstain from the
    // proof instead of adding contradictory constraints and proving inclusion
    // vacuously.  Unknown/symbolic counts continue to use the explicit user
    // assumption in the domain builders below.
    uint64_t MaxTrip =
        SE.getUnsignedRange(TripS).getUnsignedMax().getLimitedValue();
    if (MaxTrip < DRFAAAssumedMinTripCount)
      return false;
  }

  return linearizeSCEV(TripS, Ctx, SE, Trip);
}

static bool addDomainConstraints(ArrayRef<const Loop *> ParallelLoops,
                                 ScalarEvolution &SE,
                                 SymbolicLinearContext &Ctx,
                                 SymbolicConstraintSet &Constraints) {
  SmallVector<int, 4> ZeroShift(ParallelLoops.size(), 0);
  for (unsigned I = 0; I < ParallelLoops.size(); ++I) {
    // 0 <= x_i  ==>  -x_i <= 0.
    SymbolicLinearExpr Lower;
    if (!Lower.addCoeff(I, -1) || !Constraints.addAffineLEZero(Lower))
      return false;

    // x_i < Trip_i  ==>  x_i - Trip_i + 1 <= 0.
    SymbolicLinearExpr Trip;
    if (!linearizeTripCount(I, ParallelLoops, ZeroShift, SE, Ctx, Trip))
      return false;

    SymbolicLinearExpr Upper = makeLoopVarExpr(I);
    if (!subtractExpr(Upper, Trip) || !Upper.addConstant(1) ||
        !Constraints.addAffineLEZero(Upper))
      return false;

    if (DRFAAAssumedMinTripCount > 1) {
      // See the Presburger domain builder: this is an explicit experimental
      // assumption that each modeled loop has enough iterations.
      SymbolicLinearExpr MinTrip;
      if (!MinTrip.addConstant(
              static_cast<int64_t>(DRFAAAssumedMinTripCount)) ||
          !subtractExpr(MinTrip, Trip) || !Constraints.addAffineLEZero(MinTrip))
        return false;
    }
  }
  return true;
}

static bool
collectDomainConstraintExprs(ArrayRef<const Loop *> Loops, ArrayRef<int> Shift,
                             ScalarEvolution &SE, SymbolicLinearContext &Ctx,
                             SmallVectorImpl<SymbolicLinearExpr> &Constraints) {
  if (Loops.size() != Shift.size())
    return false;

  for (unsigned I = 0; I < Loops.size(); ++I) {
    // 0 <= x_i + Shift_i  ==>  -x_i - Shift_i <= 0.
    SymbolicLinearExpr Lower;
    if (!Lower.addCoeff(I, -1) || !Lower.addConstant(-Shift[I]))
      return false;
    Constraints.push_back(std::move(Lower));

    // x_i + Shift_i < Trip_i(x_prev + Shift_prev)
    //   ==> x_i + Shift_i - Trip_i(...) + 1 <= 0.
    SymbolicLinearExpr Trip;
    if (!linearizeTripCount(I, Loops, Shift, SE, Ctx, Trip))
      return false;

    SymbolicLinearExpr Upper = makeLoopVarExpr(I);
    if (!Upper.addConstant(Shift[I]) || !subtractExpr(Upper, Trip) ||
        !Upper.addConstant(1))
      return false;
    Constraints.push_back(std::move(Upper));

    if (DRFAAAssumedMinTripCount > 1) {
      SymbolicLinearExpr MinTrip;
      if (!MinTrip.addConstant(
              static_cast<int64_t>(DRFAAAssumedMinTripCount)) ||
          !subtractExpr(MinTrip, Trip))
        return false;
      Constraints.push_back(std::move(MinTrip));
    }
  }
  return true;
}

struct SymbolicNeighborFailReason {
  SymbolicBoundary Boundary;
  SymbolicLinearExpr Constraint;
};

static bool isSatisfiableWithDomain(ArrayRef<const Loop *> ParallelLoops,
                                    ScalarEvolution &SE,
                                    SymbolicLinearContext &Ctx,
                                    const SymbolicLinearExpr &Extra) {
  SymbolicConstraintSet Constraints(Ctx);
  if (!addDomainConstraints(ParallelLoops, SE, Ctx, Constraints) ||
      !Constraints.addAffineLEZero(Extra))
    return true;
  return Constraints.mayHaveSolution();
}

static bool isUpperFailPinnedToBoundary(ArrayRef<const Loop *> ParallelLoops,
                                        ScalarEvolution &SE,
                                        SymbolicLinearContext &Ctx,
                                        const SymbolicLinearExpr &Fail,
                                        const SymbolicLinearExpr &Above) {
  SymbolicConstraintSet Constraints(Ctx);
  if (!addDomainConstraints(ParallelLoops, SE, Ctx, Constraints) ||
      !Constraints.addAffineLEZero(Fail) || !Constraints.addAffineLEZero(Above))
    return false;
  return !Constraints.mayHaveSolution();
}

static bool collectNeighborFailReasons(
    ArrayRef<const Loop *> ParallelLoops, ArrayRef<int> Shift,
    ScalarEvolution &SE, SymbolicLinearContext &Ctx,
    SmallVectorImpl<SymbolicNeighborFailReason> &Reasons) {
  assert(ParallelLoops.size() == Shift.size() && "bad neighbor direction");

  for (unsigned I = 0; I < Shift.size(); ++I) {
    if (Shift[I] < 0) {
      // x_i + Shift_i < 0.  With unit directions and x_i >= 0, this pins x_i
      // to the lower boundary.
      if (Shift[I] != -1)
        return false;

      SymbolicLinearExpr Fail = makeLoopVarExpr(I);
      if (!Fail.addConstant(Shift[I] + 1))
        return false;
      if (!isSatisfiableWithDomain(ParallelLoops, SE, Ctx, Fail))
        continue;

      Reasons.push_back({makeLowerBoundary(I), std::move(Fail)});
    }

    if (Shift[I] > 0) {
      if (Shift[I] != 1)
        return false;

      // x_i + Shift_i >= Trip_i(x_prev + Shift_prev)
      //   ==> Trip_i(x_prev + Shift_prev) - Shift_i - x_i <= 0.
      SymbolicLinearExpr Trip;
      if (!linearizeTripCount(I, ParallelLoops, Shift, SE, Ctx, Trip))
        return false;

      SymbolicLinearExpr Fail = Trip;
      if (!Fail.addConstant(-Shift[I]) || !Fail.addCoeff(I, -1))
        return false;
      if (!isSatisfiableWithDomain(ParallelLoops, SE, Ctx, Fail))
        continue;

      // The symbolic face machinery represents boundary equalities.  If this
      // upper-neighbor failure can cover a thicker band than one boundary cell,
      // bail rather than under-cover the deficient set.
      SymbolicLinearExpr Above = Trip;
      if (!Above.addConstant(-Shift[I] + 1) || !Above.addCoeff(I, -1))
        return false;
      if (!isUpperFailPinnedToBoundary(ParallelLoops, SE, Ctx, Fail, Above))
        return false;

      Reasons.push_back(
          {makeUpperBoundary(I, Shift, -Shift[I]), std::move(Fail)});
    }
  }

  return true;
}

static bool addReasonConstraint(SymbolicConstraintSet &Constraints,
                                const SymbolicNeighborFailReason &Reason) {
  return Constraints.addAffineLEZero(Reason.Constraint);
}

static bool isDeficientFaceSatisfiable(ArrayRef<const Loop *> ParallelLoops,
                                       ScalarEvolution &SE,
                                       SymbolicLinearContext &Ctx,
                                       const SymbolicNeighborFailReason &A,
                                       const SymbolicNeighborFailReason &B) {
  SymbolicConstraintSet Constraints(Ctx);
  if (!addDomainConstraints(ParallelLoops, SE, Ctx, Constraints) ||
      !addReasonConstraint(Constraints, A) ||
      !addReasonConstraint(Constraints, B))
    return true;
  return Constraints.mayHaveSolution();
}

static bool sameSymbolicBoundary(const SymbolicBoundary &A,
                                 const SymbolicBoundary &B) {
  return A.Kind == B.Kind && A.LoopIdx == B.LoopIdx &&
         A.CoordOffset == B.CoordOffset && A.TripShift == B.TripShift;
}

static bool hasConflictingLoopBoundaries(const SymbolicDeficientFace &Face) {
  for (unsigned I = 0; I < Face.Boundaries.size(); ++I)
    for (unsigned J = I + 1; J < Face.Boundaries.size(); ++J)
      if (Face.Boundaries[I].LoopIdx == Face.Boundaries[J].LoopIdx &&
          Face.Boundaries[I].Kind != Face.Boundaries[J].Kind)
        return true;
  return false;
}

static SymbolicDeficientFace
makeFaceFromReasons(const SymbolicNeighborFailReason &A,
                    const SymbolicNeighborFailReason &B) {
  SymbolicDeficientFace Face;
  Face.Boundaries.push_back(A.Boundary);
  if (!sameSymbolicBoundary(A.Boundary, B.Boundary))
    Face.Boundaries.push_back(B.Boundary);
  return Face;
}

static bool
computeSymbolicDeficientFaces(ArrayRef<const Loop *> ParallelLoops,
                              ArrayRef<int> Direction, ScalarEvolution &SE,
                              SmallVectorImpl<SymbolicDeficientFace> &Faces) {
  Faces.clear();
  if (ParallelLoops.empty() || ParallelLoops.size() != Direction.size() ||
      ParallelLoops.size() > 4)
    return false;

  SymbolicLinearContext Ctx(ParallelLoops);
  SmallVector<SymbolicNeighborFailReason, 8> PlusReasons;
  SmallVector<SymbolicNeighborFailReason, 8> MinusReasons;
  SmallVector<int, 4> MinusDirection;
  for (int Component : Direction)
    MinusDirection.push_back(-Component);

  if (!collectNeighborFailReasons(ParallelLoops, Direction, SE, Ctx,
                                  PlusReasons) ||
      !collectNeighborFailReasons(ParallelLoops, MinusDirection, SE, Ctx,
                                  MinusReasons))
    return false;

  if (PlusReasons.empty() || MinusReasons.empty())
    return false;

  for (const SymbolicNeighborFailReason &Plus : PlusReasons) {
    for (const SymbolicNeighborFailReason &Minus : MinusReasons) {
      if (!isDeficientFaceSatisfiable(ParallelLoops, SE, Ctx, Plus, Minus))
        continue;

      SymbolicDeficientFace Face = makeFaceFromReasons(Plus, Minus);
      // Under the temporary >=2 assumption, a lower and upper boundary of the
      // same loop are distinct.  Treat such n==1-only cells as impossible until
      // the real multiplicity proof is wired.
      if (hasConflictingLoopBoundaries(Face))
        continue;

      Faces.push_back(std::move(Face));
    }
  }

  // If every pair of +v/-v failure reasons is impossible, every point has at
  // least one sibling along the null direction, so there is no companion face
  // to prove.
  return true;
}

static const SCEV *applySymbolicBoundary(const SCEV *S,
                                         const SymbolicBoundary &Boundary,
                                         ArrayRef<const Loop *> ParallelLoops,
                                         ScalarEvolution &SE) {
  assert(Boundary.LoopIdx < ParallelLoops.size() && "invalid boundary loop");

  const Loop *L = ParallelLoops[Boundary.LoopIdx];
  switch (Boundary.Kind) {
  case SymbolicBoundaryKind::Lower:
    return SCEVLoopStartRewriter::rewrite(S, L, SE);
  case SymbolicBoundaryKind::Upper: {
    const SCEV *Trip = getShiftedTripCountSCEV(Boundary.LoopIdx, ParallelLoops,
                                               Boundary.TripShift, SE);
    if (isa<SCEVCouldNotCompute>(Trip))
      return SE.getCouldNotCompute();

    const SCEV *Coord = addSignedConstantToSCEV(Trip, Boundary.CoordOffset, SE);
    const SCEV *Shifted =
        SCEVLoopSymbolicShiftRewriter::rewrite(S, L, Coord, SE);
    if (isa<SCEVCouldNotCompute>(Shifted))
      return Shifted;
    return SCEVLoopStartRewriter::rewrite(Shifted, L, SE);
  }
  }

  llvm_unreachable("unknown symbolic boundary kind");
}

static bool boundaryLoopComesBefore(const SymbolicBoundary &A,
                                    const SymbolicBoundary &B,
                                    ArrayRef<const Loop *> ParallelLoops) {
  const Loop *LA = ParallelLoops[A.LoopIdx];
  const Loop *LB = ParallelLoops[B.LoopIdx];
  if (LA == LB)
    return false;
  // Apply inner boundaries first so that trip-count expressions introduced for
  // inner upper bounds still see later substitutions for outer coordinates.
  return parallelLoopComesBefore(LB, LA);
}

static const SCEV *
applyFaceBoundariesToSCEV(const SCEV *S, const SymbolicDeficientFace &Face,
                          ArrayRef<const Loop *> ParallelLoops,
                          ScalarEvolution &SE) {
  SmallVector<SymbolicBoundary, 4> Boundaries(Face.Boundaries.begin(),
                                              Face.Boundaries.end());
  for (unsigned I = 1; I < Boundaries.size(); ++I) {
    SymbolicBoundary B = Boundaries[I];
    unsigned J = I;
    while (J > 0 &&
           boundaryLoopComesBefore(B, Boundaries[J - 1], ParallelLoops)) {
      Boundaries[J] = Boundaries[J - 1];
      --J;
    }
    Boundaries[J] = B;
  }

  const SCEV *Result = S;
  for (const SymbolicBoundary &Boundary : Boundaries) {
    Result = applySymbolicBoundary(Result, Boundary, ParallelLoops, SE);
    if (isa<SCEVCouldNotCompute>(Result))
      return Result;
  }
  return Result;
}

static int getInwardShiftSign(SymbolicBoundaryKind Kind) {
  switch (Kind) {
  case SymbolicBoundaryKind::Lower:
    return 1;
  case SymbolicBoundaryKind::Upper:
    return -1;
  }

  llvm_unreachable("unknown symbolic boundary kind");
}

static bool companionMatchesBoundarySCEV(const SCEV *CandidateS,
                                         const SCEV *BoundaryS,
                                         const SymbolicDeficientFace &Face,
                                         ArrayRef<const Loop *> ParallelLoops,
                                         ScalarEvolution &SE) {
  auto MatchesAfterFaceSubstitution = [&](const SCEV *S) {
    const SCEV *FaceS = applyFaceBoundariesToSCEV(S, Face, ParallelLoops, SE);
    return !isa<SCEVCouldNotCompute>(FaceS) &&
           scevExpressionsEqual(SE, FaceS, BoundaryS);
  };

  if (MatchesAfterFaceSubstitution(CandidateS))
    return true;

  constexpr unsigned MaxSymbolicCompanionShift = 8;
  for (const SymbolicBoundary &Boundary : Face.Boundaries) {
    const Loop *ShiftLoop = ParallelLoops[Boundary.LoopIdx];
    int ShiftSign = getInwardShiftSign(Boundary.Kind);
    for (unsigned Shift = 1; Shift <= MaxSymbolicCompanionShift; ++Shift) {
      const SCEV *Shifted = SCEVLoopShiftRewriter::rewrite(
          CandidateS, ShiftLoop, ShiftSign * static_cast<int64_t>(Shift), SE);
      if (!isa<SCEVCouldNotCompute>(Shifted) &&
          MatchesAfterFaceSubstitution(Shifted))
        return true;
    }
  }

  return false;
}

static const SCEV *getBoundarySCEVForDeficientFace(
    const SCEV *AddrS, const SymbolicDeficientFace &Face,
    ArrayRef<const Loop *> ParallelLoops, ScalarEvolution &SE) {
  return applyFaceBoundariesToSCEV(AddrS, Face, ParallelLoops, SE);
}

static bool hasSymbolicFaceCompanion(const Instruction *Access,
                                     const SCEV *AddrS,
                                     const Instruction *OtherAccess,
                                     const TaskInfo &TI, ScalarEvolution &SE,
                                     ArrayRef<const Loop *> ParallelLoops,
                                     const SymbolicDeficientFace &Face) {
  const SCEV *BoundaryS =
      getBoundarySCEVForDeficientFace(AddrS, Face, ParallelLoops, SE);
  if (isa<SCEVCouldNotCompute>(BoundaryS))
    return false;

  SmallVector<const Instruction *, 8> Witnesses;
  if (!collectParallelWitnessAccesses(Access, OtherAccess, TI, SE,
                                      ParallelLoops, Witnesses))
    return false;

  for (const Instruction *Witness : Witnesses) {
    if (Witness == Access)
      continue;

    std::optional<MemoryLocation> Loc = MemoryLocation::getOrNone(Witness);
    if (!Loc)
      continue;

    const SCEV *WitnessS = SE.getSCEV(const_cast<Value *>(Loc->Ptr));
    if (isa<SCEVCouldNotCompute>(WitnessS) ||
        !hasAxisReplication(Witness, WitnessS, TI, SE, ParallelLoops))
      continue;

    if (companionMatchesBoundarySCEV(WitnessS, BoundaryS, Face, ParallelLoops,
                                     SE))
      return true;
  }

  return false;
}

static bool proveParallelFiberCoverageSymbolically(
    const Instruction *Access, const SCEV *AddrS,
    const Instruction *OtherAccess, const TaskInfo &TI, ScalarEvolution &SE,
    ArrayRef<const Loop *> ParallelLoops,
    ArrayRef<SmallVector<int, 4>> Directions) {
  // First symbolic slice: two-dimensional triangular domains and primitive
  // diagonal direction (outer + 1, inner - 1).  The proof is factored like a
  // small Presburger query: derive deficient faces from D and v, then prove
  // each face has a same-address companion at a distinct parallel point.  The
  // companion's explicit >=2 multiplicity obligation is deliberately left for a
  // follow-up.
  for (ArrayRef<int> Direction : Directions) {
    SmallVector<SymbolicDeficientFace, 4> DeficientFaces;
    if (!computeSymbolicDeficientFaces(ParallelLoops, Direction, SE,
                                       DeficientFaces))
      continue;

    bool AllFacesCovered = true;
    for (const SymbolicDeficientFace &Face : DeficientFaces) {
      if (!hasSymbolicFaceCompanion(Access, AddrS, OtherAccess, TI, SE,
                                    ParallelLoops, Face)) {
        AllFacesCovered = false;
        break;
      }
    }

    if (AllFacesCovered) {
      LLVM_DEBUG(dbgs() << "DRFAA: symbolic replicated-fiber face proof\n");
      return true;
    }
  }

  return false;
}

static bool
proveParallelFiberCoverageByDomain(const Instruction *Access, const SCEV *AddrS,
                                   const Instruction *OtherAccess,
                                   const TaskInfo &TI, ScalarEvolution &SE,
                                   ArrayRef<const Loop *> ParallelLoops) {
  // This is a bounded affine-domain proof, not a shape-specific boundary
  // heuristic.  It enumerates the SCEV-proven parallel iteration domain,
  // records every address touched by the replicated access and by same-block
  // witness accesses, and requires every access address to have a matching
  // address at a distinct parallel point.  If any bound/address is not affine
  // enough for this local proof, we conservatively return MayAlias.
  SmallVector<const Instruction *, 8> Witnesses;
  if (!collectParallelWitnessAccesses(Access, OtherAccess, TI, SE,
                                      ParallelLoops, Witnesses))
    return false;

  SmallVector<ParallelAddressTouch, 128> TargetTouches;
  if (!appendParallelAddressTouches(Access, SE, ParallelLoops, TargetTouches))
    return false;

  SmallVector<ParallelAddressTouch, 256> WitnessTouches;
  for (const Instruction *Witness : Witnesses)
    if (!appendParallelAddressTouches(Witness, SE, ParallelLoops,
                                      WitnessTouches))
      return false;

  for (const ParallelAddressTouch &Target : TargetTouches) {
    bool Covered = false;
    for (const ParallelAddressTouch &Witness : WitnessTouches) {
      if (!parallelPointDiffers(Target.Point, Witness.Point))
        continue;
      if (scevExpressionsEqual(SE, Target.Addr, Witness.Addr)) {
        Covered = true;
        break;
      }
    }

    if (!Covered)
      return false;
  }

  return true;
}

static bool proveParallelFiberCoverage(const Instruction *Access,
                                       const SCEV *AddrS,
                                       const Instruction *OtherAccess,
                                       const TaskInfo &TI, ScalarEvolution &SE,
                                       ArrayRef<const Loop *> ParallelLoops,
                                       ArrayRef<int64_t> Gradient) {
  if (hasAxisReplication(Access, AddrS, TI, SE, ParallelLoops))
    return true;

  SmallVector<SmallVector<int, 4>, 8> Directions;
  collectSmallNonZeroNullDirections(Gradient, Directions);
  if (Directions.empty())
    return false;

  if (proveParallelFiberCoverageSymbolically(Access, AddrS, OtherAccess, TI, SE,
                                             ParallelLoops, Directions))
    return true;

  return proveParallelFiberCoverageByDomain(Access, AddrS, OtherAccess, TI, SE,
                                            ParallelLoops);
}

static void
collectParallelWitnessLoops(const Instruction *AccessA,
                            const Instruction *AccessB, const SCEV *AS,
                            const SCEV *BS, const TaskInfo &TI,
                            SmallVectorImpl<const Loop *> &ParallelLoops) {
  SmallVector<const Loop *, 4> CandidateLoops;
  SmallPtrSet<const Loop *, 4> SeenLoops;
  collectLoopsFromSCEV(AS, CandidateLoops, SeenLoops);
  collectLoopsFromSCEV(BS, CandidateLoops, SeenLoops);

  for (const Loop *L : CandidateLoops)
    if (L->contains(AccessA->getParent()) &&
        L->contains(AccessB->getParent()) && isDRFLogicallyParallelLoop(L, &TI))
      ParallelLoops.push_back(L);

  sortLoopsOuterToInner(ParallelLoops);
}

static bool accessHasStartAlignmentAtLeast(const Instruction *I,
                                           uint64_t Size) {
  if (!isPowerOf2_64(Size))
    return false;

  if (const auto *LI = dyn_cast<LoadInst>(I))
    return LI->getAlign().value() >= Size;
  if (const auto *SI = dyn_cast<StoreInst>(I))
    return SI->getAlign().value() >= Size;
  return false;
}

static const SCEV *getAddressComparableSCEV(const SCEV *S,
                                            ScalarEvolution &SE) {
  Type *Ty = SE.getEffectiveSCEVType(S->getType());
  if (S->getType()->isPointerTy())
    return SE.getPtrToIntExpr(S, Ty);
  return S;
}

static const SCEV *getAddressDeltaSCEV(const SCEV *A, const SCEV *B,
                                       ScalarEvolution &SE) {
  A = getAddressComparableSCEV(A, SE);
  B = getAddressComparableSCEV(B, SE);
  if (isa<SCEVCouldNotCompute>(A) || isa<SCEVCouldNotCompute>(B))
    return SE.getCouldNotCompute();

  if (SE.getEffectiveSCEVType(A->getType()) !=
      SE.getEffectiveSCEVType(B->getType()))
    return SE.getCouldNotCompute();

  if (!canComputePointerDiff(SE, A, B))
    return SE.getCouldNotCompute();

  return SE.getMinusSCEV(A, B);
}

static void collectCommonInstanceLoops(const Instruction *AccessA,
                                       const Instruction *AccessB,
                                       const SCEV *AS, const SCEV *BS,
                                       SmallVectorImpl<const Loop *> &Loops) {
  SmallVector<const Loop *, 8> CandidateLoops;
  SmallPtrSet<const Loop *, 8> SeenLoops;
  collectLoopsFromSCEV(AS, CandidateLoops, SeenLoops);
  collectLoopsFromSCEV(BS, CandidateLoops, SeenLoops);

  for (const Loop *L : CandidateLoops)
    if (L->contains(AccessA->getParent()) && L->contains(AccessB->getParent()))
      Loops.push_back(L);

  sortLoopsOuterToInner(Loops);
}

static bool getParallelLoopIndices(ArrayRef<const Loop *> InstanceLoops,
                                   ArrayRef<const Loop *> ParallelLoops,
                                   SmallVectorImpl<unsigned> &Indices) {
  for (const Loop *PL : ParallelLoops) {
    bool Found = false;
    for (auto [Idx, IL] : enumerate(InstanceLoops)) {
      if (IL != PL)
        continue;
      Indices.push_back(Idx);
      Found = true;
      break;
    }
    if (!Found)
      return false;
  }
  return true;
}

/// Keep the coordinates that decide whether two points of the instance nest
/// are logically parallel: every loop up to and including the innermost
/// parallel loop.  Serial loops nested inside all parallel loops never
/// separate two strands, so their coordinates are dropped.
static void projectParallelPoint(ArrayRef<int64_t> Point,
                                 ArrayRef<unsigned> ParallelLoopIndices,
                                 SmallVectorImpl<int64_t> &TaskPoint) {
  TaskPoint.clear();
  if (ParallelLoopIndices.empty())
    return;
  size_t Keep = std::min<size_t>(
      static_cast<size_t>(*llvm::max_element(ParallelLoopIndices)) + 1,
      Point.size());
  TaskPoint.append(Point.begin(), Point.begin() + Keep);
}

struct DeltaSetTouch {
  const SCEV *Addr = nullptr;
  SmallVector<int64_t, 4> TaskPoint;
};

static bool sameTaskPoint(ArrayRef<int64_t> A, ArrayRef<int64_t> B) {
  if (A.size() != B.size())
    return false;
  for (auto [X, Y] : zip(A, B))
    if (X != Y)
      return false;
  return true;
}

static bool addUniqueDeltaSetTouch(
    const SCEV *Addr, ArrayRef<int64_t> TaskPoint,
    DenseMap<const SCEV *, SmallVector<SmallVector<int64_t, 4>, 2>> &Seen,
    SmallVectorImpl<DeltaSetTouch> &Touches) {
  SmallVector<SmallVector<int64_t, 4>, 2> &Points = Seen[Addr];
  for (ArrayRef<int64_t> Existing : Points)
    if (sameTaskPoint(Existing, TaskPoint))
      return true;

  SmallVector<int64_t, 4> StoredPoint(TaskPoint.begin(), TaskPoint.end());
  Points.push_back(StoredPoint);

  DeltaSetTouch Touch;
  Touch.Addr = Addr;
  Touch.TaskPoint = std::move(StoredPoint);
  Touches.push_back(std::move(Touch));
  return true;
}

static bool collectDeltaSetTouches(const SCEV *AddrS, ScalarEvolution &SE,
                                   ArrayRef<const Loop *> InstanceLoops,
                                   ArrayRef<unsigned> ParallelLoopIndices,
                                   SmallVectorImpl<DeltaSetTouch> &Touches) {
  constexpr unsigned MaxDeltaSetTouches = 65536;
  DenseMap<const SCEV *, SmallVector<SmallVector<int64_t, 4>, 2>> Seen;

  return enumerateParallelDomainPoints(
      InstanceLoops, SE, [&](ArrayRef<int64_t> Point) {
        const SCEV *AddrAtPoint =
            evaluateSCEVAtParallelPoint(AddrS, InstanceLoops, Point, SE);
        if (isa<SCEVCouldNotCompute>(AddrAtPoint))
          return false;

        SmallVector<int64_t, 4> TaskPoint;
        projectParallelPoint(Point, ParallelLoopIndices, TaskPoint);
        if (!addUniqueDeltaSetTouch(AddrAtPoint, TaskPoint, Seen, Touches))
          return false;
        return Touches.size() <= MaxDeltaSetTouches;
      });
}

static bool collectSameInstanceDeltas(const SCEV *AS, const SCEV *BS,
                                      ScalarEvolution &SE,
                                      ArrayRef<const Loop *> InstanceLoops,
                                      DenseSet<const SCEV *> &Deltas) {
  constexpr unsigned MaxDeltaSetQueryDeltas = 65536;
  return enumerateParallelDomainPoints(
      InstanceLoops, SE, [&](ArrayRef<int64_t> Point) {
        const SCEV *AAtPoint =
            evaluateSCEVAtParallelPoint(AS, InstanceLoops, Point, SE);
        const SCEV *BAtPoint =
            evaluateSCEVAtParallelPoint(BS, InstanceLoops, Point, SE);
        if (isa<SCEVCouldNotCompute>(AAtPoint) ||
            isa<SCEVCouldNotCompute>(BAtPoint))
          return false;

        const SCEV *Delta = getAddressDeltaSCEV(AAtPoint, BAtPoint, SE);
        if (isa<SCEVCouldNotCompute>(Delta))
          return false;

        Deltas.insert(Delta);
        return Deltas.size() <= MaxDeltaSetQueryDeltas;
      });
}

struct SymbolicDeltaWitness {
  SmallVector<int, 4> ShiftA;
  SmallVector<int, 4> ShiftB;
  SmallVector<SymbolicLinearExpr, 16> ValidityConstraints;
};

static const SCEV *applyConstantLoopShifts(const SCEV *S,
                                           ArrayRef<const Loop *> Loops,
                                           ArrayRef<int> Shift,
                                           ScalarEvolution &SE) {
  assert(Loops.size() == Shift.size() && "bad symbolic shift");
  const SCEV *Result = S;
  for (auto [Idx, L] : enumerate(Loops)) {
    if (Shift[Idx] == 0)
      continue;
    Result = SCEVLoopShiftRewriter::rewrite(Result, L, Shift[Idx], SE);
    if (isa<SCEVCouldNotCompute>(Result))
      return Result;
  }
  return Result;
}

static bool linearizedSCEVsEqual(const SCEV *A, const SCEV *B,
                                 ArrayRef<const Loop *> Loops,
                                 ScalarEvolution &SE) {
  SymbolicLinearContext Ctx(Loops);
  SymbolicLinearExpr LA;
  SymbolicLinearExpr LB;
  if (!linearizeSCEV(A, Ctx, SE, LA) || !linearizeSCEV(B, Ctx, SE, LB))
    return false;
  if (!subtractExpr(LA, LB))
    return false;
  return isZeroExpr(LA);
}

static bool shiftedDeltaMatchesSameInstanceDelta(
    const SCEV *AS, const SCEV *BS, ArrayRef<const Loop *> InstanceLoops,
    ArrayRef<int> ShiftA, ArrayRef<int> ShiftB, ScalarEvolution &SE) {
  const SCEV *ShiftedAS =
      applyConstantLoopShifts(AS, InstanceLoops, ShiftA, SE);
  const SCEV *ShiftedBS =
      applyConstantLoopShifts(BS, InstanceLoops, ShiftB, SE);
  if (isa<SCEVCouldNotCompute>(ShiftedAS) ||
      isa<SCEVCouldNotCompute>(ShiftedBS))
    return false;

  const SCEV *SameDelta = getAddressDeltaSCEV(AS, BS, SE);
  const SCEV *CrossDelta = getAddressDeltaSCEV(ShiftedAS, ShiftedBS, SE);
  if (isa<SCEVCouldNotCompute>(SameDelta) ||
      isa<SCEVCouldNotCompute>(CrossDelta))
    return false;

  return scevExpressionsEqual(SE, CrossDelta, SameDelta) ||
         linearizedSCEVsEqual(CrossDelta, SameDelta, InstanceLoops, SE);
}

/// Two iteration points of the instance nest execute in logically parallel
/// strands iff the outermost coordinate in which they differ belongs to a
/// parallel loop.  Points that first differ in a serial loop are ordered by
/// the sync that terminates every parallel loop nested inside it, even when
/// they also differ in some inner parallel coordinate.  The coordinates may be
/// absolute points or constant shifts of one common point.
template <typename T>
static bool
firstDifferingCoordinateIsParallel(ArrayRef<T> A, ArrayRef<T> B,
                                   ArrayRef<unsigned> ParallelLoopIndices) {
  if (A.size() != B.size())
    return false;
  for (unsigned Idx = 0; Idx < A.size(); ++Idx)
    if (A[Idx] != B[Idx])
      return is_contained(ParallelLoopIndices, Idx);
  return false;
}

static bool shiftsAreLogicallyParallel(ArrayRef<int> ShiftA,
                                       ArrayRef<int> ShiftB,
                                       ArrayRef<unsigned> ParallelLoopIndices) {
  return firstDifferingCoordinateIsParallel(ShiftA, ShiftB,
                                            ParallelLoopIndices);
}

static bool
taskPointsAreLogicallyParallel(ArrayRef<int64_t> A, ArrayRef<int64_t> B,
                               ArrayRef<unsigned> ParallelLoopIndices) {
  return firstDifferingCoordinateIsParallel(A, B, ParallelLoopIndices);
}

static bool buildSymbolicDeltaWitness(const SCEV *AS, const SCEV *BS,
                                      ArrayRef<const Loop *> InstanceLoops,
                                      ArrayRef<unsigned> ParallelLoopIndices,
                                      ArrayRef<int> ShiftA,
                                      ArrayRef<int> ShiftB, ScalarEvolution &SE,
                                      SymbolicLinearContext &Ctx,
                                      SymbolicDeltaWitness &Witness) {
  if (!shiftsAreLogicallyParallel(ShiftA, ShiftB, ParallelLoopIndices))
    return false;

  if (!shiftedDeltaMatchesSameInstanceDelta(AS, BS, InstanceLoops, ShiftA,
                                            ShiftB, SE))
    return false;

  Witness.ShiftA.assign(ShiftA.begin(), ShiftA.end());
  Witness.ShiftB.assign(ShiftB.begin(), ShiftB.end());
  if (!collectDomainConstraintExprs(InstanceLoops, ShiftA, SE, Ctx,
                                    Witness.ValidityConstraints) ||
      !collectDomainConstraintExprs(InstanceLoops, ShiftB, SE, Ctx,
                                    Witness.ValidityConstraints))
    return false;
  return true;
}

static bool
constraintsMayHaveSolution(SymbolicLinearContext &Ctx,
                           ArrayRef<SymbolicLinearExpr> Constraints) {
  SymbolicConstraintSet CS(Ctx);
  for (const SymbolicLinearExpr &Constraint : Constraints)
    if (!CS.addAffineLEZero(Constraint))
      return true;
  return CS.mayHaveSolution();
}

static bool proveDomainCoveredBySymbolicDeltaWitnesses(
    ArrayRef<const Loop *> InstanceLoops, ScalarEvolution &SE,
    SymbolicLinearContext &Ctx, ArrayRef<SymbolicDeltaWitness> Witnesses) {
  SmallVector<int, 4> ZeroShift(InstanceLoops.size(), 0);
  SmallVector<SymbolicLinearExpr, 16> DomainConstraints;
  if (!collectDomainConstraintExprs(InstanceLoops, ZeroShift, SE, Ctx,
                                    DomainConstraints))
    return false;

  if (!constraintsMayHaveSolution(Ctx, DomainConstraints))
    return true;

  SmallVector<SmallVector<SymbolicLinearExpr, 16>, 8> WitnessFailures;
  uint64_t NumCases = 1;
  constexpr uint64_t MaxSymbolicDeltaCoverageCases = 4096;

  for (const SymbolicDeltaWitness &Witness : Witnesses) {
    SmallVector<SymbolicLinearExpr, 16> Failures;
    for (const SymbolicLinearExpr &Constraint : Witness.ValidityConstraints) {
      SymbolicLinearExpr Failure;
      if (!negateLEZeroForIntegerDomain(Constraint, Failure))
        return false;

      SmallVector<SymbolicLinearExpr, 32> TestConstraints;
      TestConstraints.append(DomainConstraints.begin(),
                             DomainConstraints.end());
      TestConstraints.push_back(Failure);
      if (constraintsMayHaveSolution(Ctx, TestConstraints))
        Failures.push_back(std::move(Failure));
    }

    // This witness is valid for the whole original domain.
    if (Failures.empty())
      return true;

    if (Failures.size() != 0 &&
        NumCases > MaxSymbolicDeltaCoverageCases / Failures.size())
      return false;
    NumCases *= Failures.size();
    WitnessFailures.push_back(std::move(Failures));
  }

  SmallVector<SymbolicLinearExpr, 16> ChosenFailures;
  std::function<bool(unsigned)> ProveAllFailureCombinationsUnsat =
      [&](unsigned WitnessIdx) {
        if (WitnessIdx == WitnessFailures.size()) {
          SmallVector<SymbolicLinearExpr, 32> Constraints;
          Constraints.append(DomainConstraints.begin(),
                             DomainConstraints.end());
          Constraints.append(ChosenFailures.begin(), ChosenFailures.end());
          return !constraintsMayHaveSolution(Ctx, Constraints);
        }

        for (const SymbolicLinearExpr &Failure : WitnessFailures[WitnessIdx]) {
          ChosenFailures.push_back(Failure);
          if (!ProveAllFailureCombinationsUnsat(WitnessIdx + 1))
            return false;
          ChosenFailures.pop_back();
        }
        return true;
      };

  return ProveAllFailureCombinationsUnsat(0);
}

static bool hasUnknownDefinedInAnyLoop(const SCEV *S,
                                       ArrayRef<const Loop *> Loops) {
  for (const Loop *L : Loops) {
    SmallPtrSet<const SCEV *, 16> Seen;
    if (containsUnknownDefinedInLoop(S, L, Seen))
      return true;
  }
  return false;
}

static SmallVector<int64_t, 8> makePresburgerRow(unsigned NumSetDims,
                                                 unsigned NumSymbols) {
  return SmallVector<int64_t, 8>(NumSetDims + NumSymbols + 1, 0);
}

static bool addScaledPresburgerCoeff(SmallVectorImpl<int64_t> &Row,
                                     unsigned Col, int64_t Coeff,
                                     int64_t Scale) {
  int64_t Scaled = 0;
  return !MulOverflow(Coeff, Scale, Scaled) &&
         !AddOverflow(Row[Col], Scaled, Row[Col]);
}

static bool appendExprToPresburgerRow(SmallVectorImpl<int64_t> &Row,
                                      const SymbolicLinearExpr &Expr,
                                      unsigned NumLoopVars, unsigned NumSetDims,
                                      unsigned LoopDimOffset,
                                      ArrayRef<int> SymbolMap, int64_t Scale) {
  if (Row.size() < NumSetDims + 1)
    return false;
  unsigned NumSymbols = Row.size() - NumSetDims - 1;

  for (auto [Var, Coeff] : enumerate(Expr.Coeffs)) {
    if (Coeff == 0)
      continue;

    unsigned Col = 0;
    if (Var < NumLoopVars) {
      Col = LoopDimOffset + Var;
      if (Col >= NumSetDims)
        return false;
    } else {
      unsigned SymbolIdx = Var - NumLoopVars;
      if (SymbolIdx >= SymbolMap.size() || SymbolMap[SymbolIdx] < 0)
        return false;
      if (static_cast<unsigned>(SymbolMap[SymbolIdx]) >= NumSymbols)
        return false;
      Col = NumSetDims + static_cast<unsigned>(SymbolMap[SymbolIdx]);
    }

    if (!addScaledPresburgerCoeff(Row, Col, Coeff, Scale))
      return false;
  }

  return addScaledPresburgerCoeff(Row, Row.size() - 1, Expr.Constant, Scale);
}

static bool appendExprLoopCoeffsToPresburgerRow(SmallVectorImpl<int64_t> &Row,
                                                const SymbolicLinearExpr &Expr,
                                                unsigned NumLoopVars,
                                                unsigned NumSetDims,
                                                unsigned LoopDimOffset,
                                                int64_t Scale) {
  if (Row.size() < NumSetDims + 1)
    return false;

  for (auto [Var, Coeff] : enumerate(Expr.Coeffs)) {
    if (Coeff == 0)
      continue;
    if (Var >= NumLoopVars)
      continue;

    unsigned Col = LoopDimOffset + Var;
    if (Col >= NumSetDims)
      return false;
    if (!addScaledPresburgerCoeff(Row, Col, Coeff, Scale))
      return false;
  }

  // Loop-invariant constants and symbols contribute the same offset to the
  // same-instance and cross-task delta sets.  The inclusion check is therefore
  // performed on the normalized loop-varying delta only.
  return true;
}

static void collectPresburgerTripSymbols(ArrayRef<SymbolicLinearExpr> TripExprs,
                                         unsigned NumLoopVars,
                                         unsigned NumOriginalSymbols,
                                         SmallVectorImpl<int> &SymbolMap) {
  SymbolMap.assign(NumOriginalSymbols, -1);
  unsigned NextSymbol = 0;
  for (const SymbolicLinearExpr &Expr : TripExprs) {
    for (auto [Var, Coeff] : enumerate(Expr.Coeffs)) {
      if (Coeff == 0 || Var < NumLoopVars)
        continue;
      unsigned SymbolIdx = Var - NumLoopVars;
      if (SymbolIdx >= NumOriginalSymbols || SymbolMap[SymbolIdx] >= 0)
        continue;
      SymbolMap[SymbolIdx] = NextSymbol++;
    }
  }
}

static unsigned countPresburgerSymbols(ArrayRef<int> SymbolMap) {
  unsigned Count = 0;
  for (int Mapped : SymbolMap)
    if (Mapped >= 0)
      ++Count;
  return Count;
}

static bool addTupleDomainConstraints(mlir::presburger::IntegerPolyhedron &Poly,
                                      ArrayRef<SymbolicLinearExpr> TripExprs,
                                      unsigned NumLoopVars, unsigned NumSetDims,
                                      unsigned NumSymbols,
                                      unsigned LoopDimOffset,
                                      ArrayRef<int> SymbolMap) {
  if (TripExprs.size() != NumLoopVars ||
      LoopDimOffset + NumLoopVars > NumSetDims)
    return false;

  for (unsigned I = 0; I < NumLoopVars; ++I) {
    // 0 <= x_i.
    SmallVector<int64_t, 8> Lower = makePresburgerRow(NumSetDims, NumSymbols);
    Lower[LoopDimOffset + I] = 1;
    Poly.addInequality(Lower);

    // x_i < Trip_i  ==>  Trip_i - x_i - 1 >= 0.
    SmallVector<int64_t, 8> Upper = makePresburgerRow(NumSetDims, NumSymbols);
    if (!appendExprToPresburgerRow(Upper, TripExprs[I], NumLoopVars, NumSetDims,
                                   LoopDimOffset, SymbolMap, 1))
      return false;
    if (!addScaledPresburgerCoeff(Upper, LoopDimOffset + I, -1, 1) ||
        !addScaledPresburgerCoeff(Upper, Upper.size() - 1, -1, 1))
      return false;
    Poly.addInequality(Upper);

    if (DRFAAAssumedMinTripCount > 1) {
      // Experimental DRF-AA proofs currently assume loop domains are large
      // enough to supply cross-task witnesses; encode that assumption directly
      // so symbolic trip counts do not admit zero/one-iteration edge cases.
      SmallVector<int64_t, 8> MinTrip =
          makePresburgerRow(NumSetDims, NumSymbols);
      if (!appendExprToPresburgerRow(MinTrip, TripExprs[I], NumLoopVars,
                                     NumSetDims, LoopDimOffset, SymbolMap, 1))
        return false;
      if (!addScaledPresburgerCoeff(
              MinTrip, MinTrip.size() - 1,
              -static_cast<int64_t>(DRFAAAssumedMinTripCount), 1))
        return false;
      Poly.addInequality(MinTrip);
    }
  }
  return true;
}

static bool addDeltaEquality(mlir::presburger::IntegerPolyhedron &Poly,
                             const SymbolicLinearExpr &ASExpr,
                             const SymbolicLinearExpr &BSExpr,
                             unsigned NumLoopVars, unsigned NumSetDims,
                             unsigned NumSymbols, unsigned ALoopDimOffset,
                             unsigned BLoopDimOffset, unsigned DeltaDim) {
  if (DeltaDim >= NumSetDims)
    return false;

  SmallVector<int64_t, 8> Eq = makePresburgerRow(NumSetDims, NumSymbols);
  if (!appendExprLoopCoeffsToPresburgerRow(Eq, ASExpr, NumLoopVars, NumSetDims,
                                           ALoopDimOffset, 1) ||
      !appendExprLoopCoeffsToPresburgerRow(Eq, BSExpr, NumLoopVars, NumSetDims,
                                           BLoopDimOffset, -1) ||
      !addScaledPresburgerCoeff(Eq, DeltaDim, -1, 1))
    return false;

  Poly.addEquality(Eq);
  return true;
}

static std::optional<mlir::presburger::PresburgerSet> buildSameInstanceDeltaSet(
    const SymbolicLinearExpr &ASExpr, const SymbolicLinearExpr &BSExpr,
    ArrayRef<SymbolicLinearExpr> TripExprs, unsigned NumLoopVars,
    unsigned NumSymbols, ArrayRef<int> SymbolMap) {
  unsigned NumSetDims = NumLoopVars + 1;
  unsigned DeltaDim = NumLoopVars;
  mlir::presburger::IntegerPolyhedron Poly(
      mlir::presburger::PresburgerSpace::getSetSpace(NumSetDims + NumSymbols,
                                                     0));

  if (!addTupleDomainConstraints(Poly, TripExprs, NumLoopVars, NumSetDims,
                                 NumSymbols, /*LoopDimOffset=*/0, SymbolMap) ||
      !addDeltaEquality(Poly, ASExpr, BSExpr, NumLoopVars, NumSetDims,
                        NumSymbols, /*ALoopDimOffset=*/0,
                        /*BLoopDimOffset=*/0, DeltaDim))
    return std::nullopt;

  if (NumLoopVars)
    Poly.convertToLocal(mlir::presburger::VarKind::SetDim, /*varStart=*/0,
                        /*varLimit=*/NumLoopVars);
  return mlir::presburger::PresburgerSet(Poly);
}

static std::optional<mlir::presburger::PresburgerSet> buildCrossTaskDeltaSet(
    const SymbolicLinearExpr &ASExpr, const SymbolicLinearExpr &BSExpr,
    ArrayRef<SymbolicLinearExpr> TripExprs, unsigned NumLoopVars,
    unsigned NumSymbols, ArrayRef<int> SymbolMap,
    ArrayRef<unsigned> ParallelLoopIndices) {
  mlir::presburger::PresburgerSpace ProjectedSpace =
      mlir::presburger::PresburgerSpace::getSetSpace(/*numDims=*/1 + NumSymbols,
                                                     /*numSymbols=*/0);
  mlir::presburger::PresburgerSet Cross =
      mlir::presburger::PresburgerSet::getEmpty(ProjectedSpace);

  unsigned NumSetDims = 2 * NumLoopVars + 1;
  unsigned AOffset = 0;
  unsigned BOffset = NumLoopVars;
  unsigned DeltaDim = 2 * NumLoopVars;

  for (unsigned ParallelIdx : ParallelLoopIndices) {
    if (ParallelIdx >= NumLoopVars)
      return std::nullopt;

    for (bool AAfterB : {false, true}) {
      mlir::presburger::IntegerPolyhedron Poly(
          mlir::presburger::PresburgerSpace::getSetSpace(
              NumSetDims + NumSymbols, 0));

      if (!addTupleDomainConstraints(Poly, TripExprs, NumLoopVars, NumSetDims,
                                     NumSymbols, AOffset, SymbolMap) ||
          !addTupleDomainConstraints(Poly, TripExprs, NumLoopVars, NumSetDims,
                                     NumSymbols, BOffset, SymbolMap) ||
          !addDeltaEquality(Poly, ASExpr, BSExpr, NumLoopVars, NumSetDims,
                            NumSymbols, AOffset, BOffset, DeltaDim))
        return std::nullopt;

      // Distinct logical parallel tasks: the witness points first differ in
      // this parallel loop, so they agree on every enclosing coordinate.  A
      // pair that first differs in an enclosing serial loop is ordered by the
      // sync that terminates this loop and cannot race.  The disjunction over
      // parallel loops and both signs is represented as a union.
      for (unsigned Outer = 0; Outer < ParallelIdx; ++Outer) {
        SmallVector<int64_t, 8> Eq = makePresburgerRow(NumSetDims, NumSymbols);
        Eq[AOffset + Outer] = 1;
        Eq[BOffset + Outer] = -1;
        Poly.addEquality(Eq);
      }
      SmallVector<int64_t, 8> Diff = makePresburgerRow(NumSetDims, NumSymbols);
      unsigned ACol = AOffset + ParallelIdx;
      unsigned BCol = BOffset + ParallelIdx;
      Diff[AAfterB ? ACol : BCol] = 1;
      Diff[AAfterB ? BCol : ACol] = -1;
      Diff.back() = -1;
      Poly.addInequality(Diff);

      if (NumLoopVars)
        Poly.convertToLocal(mlir::presburger::VarKind::SetDim,
                            /*varStart=*/0,
                            /*varLimit=*/2 * NumLoopVars);
      Cross = Cross.unionSet(mlir::presburger::PresburgerSet(Poly));
    }
  }

  return Cross;
}

struct AffineDeltaInterval {
  int64_t Low = 0;
  int64_t High = 0;
  // Zero means a singleton interval.  Otherwise the interval contains exactly
  // the values congruent to Low modulo Stride in [Low, High].
  int64_t Stride = 0;
};

static bool checkedAddTo(int64_t &LHS, int64_t RHS) {
  return !AddOverflow(LHS, RHS, LHS);
}

static bool checkedMulTo(int64_t LHS, int64_t RHS, int64_t &Result) {
  return !MulOverflow(LHS, RHS, Result);
}

static bool hasOnlyConstantPart(const SymbolicLinearExpr &Expr) {
  for (int64_t C : Expr.Coeffs)
    if (C != 0)
      return false;
  return true;
}

static bool
getConstantRectangularTripCounts(ArrayRef<const Loop *> InstanceLoops,
                                 ScalarEvolution &SE,
                                 SmallVectorImpl<int64_t> &TripCounts) {
  SymbolicLinearContext Ctx(InstanceLoops);
  SmallVector<int, 4> ZeroShift(InstanceLoops.size(), 0);
  TripCounts.clear();

  for (unsigned I = 0; I < InstanceLoops.size(); ++I) {
    SymbolicLinearExpr Trip;
    if (!linearizeTripCount(I, InstanceLoops, ZeroShift, SE, Ctx, Trip) ||
        !hasOnlyConstantPart(Trip) || Trip.Constant <= 0)
      return false;
    TripCounts.push_back(Trip.Constant);
  }
  return true;
}

static bool computeShiftedBoxBounds(ArrayRef<int64_t> TripCounts,
                                    ArrayRef<int> ShiftA, ArrayRef<int> ShiftB,
                                    SmallVectorImpl<int64_t> &Lows,
                                    SmallVectorImpl<int64_t> &Highs) {
  if (TripCounts.size() != ShiftA.size() || TripCounts.size() != ShiftB.size())
    return false;

  Lows.clear();
  Highs.clear();
  for (unsigned I = 0; I < TripCounts.size(); ++I) {
    int64_t Low = std::max<int64_t>(-ShiftA[I], -ShiftB[I]);
    int64_t High = std::min<int64_t>(TripCounts[I] - 1 - ShiftA[I],
                                     TripCounts[I] - 1 - ShiftB[I]);
    if (Low > High)
      return false;
    Lows.push_back(Low);
    Highs.push_back(High);
  }
  return true;
}

static bool getNormalizedShiftedDeltaExpr(
    const SCEV *AS, const SCEV *BS, ArrayRef<const Loop *> InstanceLoops,
    ArrayRef<int> ShiftA, ArrayRef<int> ShiftB, ScalarEvolution &SE,
    SymbolicLinearContext &Ctx, SymbolicLinearExpr &DeltaExpr) {
  const SCEV *ShiftedAS =
      applyConstantLoopShifts(AS, InstanceLoops, ShiftA, SE);
  const SCEV *ShiftedBS =
      applyConstantLoopShifts(BS, InstanceLoops, ShiftB, SE);
  if (isa<SCEVCouldNotCompute>(ShiftedAS) ||
      isa<SCEVCouldNotCompute>(ShiftedBS))
    return false;

  const SCEV *Delta = getAddressDeltaSCEV(ShiftedAS, ShiftedBS, SE);
  if (isa<SCEVCouldNotCompute>(Delta) ||
      !linearizeSCEV(Delta, Ctx, SE, DeltaExpr))
    return false;

  // Keep only the loop-varying coefficients plus the concrete constant.
  // Loop-invariant SCEVUnknowns contribute common address-base parameters to
  // both same-instance and cross-task delta images; dropping those parameter
  // coefficients preserves inclusion while avoiding parameterized base dims.
  if (DeltaExpr.Coeffs.size() > InstanceLoops.size())
    DeltaExpr.Coeffs.resize(InstanceLoops.size());
  return true;
}

static int64_t positiveMod(int64_t V, int64_t M) {
  assert(M > 0 && "expected positive modulus");
  int64_t R = V % M;
  return R < 0 ? R + M : R;
}

static bool computeContiguousImageInterval(const SymbolicLinearExpr &Expr,
                                           ArrayRef<int64_t> Lows,
                                           ArrayRef<int64_t> Highs,
                                           unsigned NumLoopVars,
                                           AffineDeltaInterval &Interval) {
  if (Lows.size() != NumLoopVars || Highs.size() != NumLoopVars)
    return false;

  int64_t Low = Expr.Constant;
  int64_t High = Expr.Constant;
  SmallVector<std::pair<int64_t, int64_t>, 4> StepsAndCounts;
  int64_t LatticeStride = 0;

  for (unsigned I = 0; I < NumLoopVars; ++I) {
    int64_t Coeff = I < Expr.Coeffs.size() ? Expr.Coeffs[I] : 0;
    if (Coeff == 0)
      continue;
    if (Lows[I] > Highs[I])
      return false;

    int64_t LowProduct = 0;
    int64_t HighProduct = 0;
    if (!checkedMulTo(Coeff, Lows[I], LowProduct) ||
        !checkedMulTo(Coeff, Highs[I], HighProduct))
      return false;
    if (LowProduct > HighProduct)
      std::swap(LowProduct, HighProduct);
    if (!checkedAddTo(Low, LowProduct) || !checkedAddTo(High, HighProduct))
      return false;

    int64_t Count = Highs[I] - Lows[I] + 1;
    if (Count <= 1)
      continue;
    if (Coeff == std::numeric_limits<int64_t>::min())
      return false;

    int64_t AbsCoeff = std::abs(Coeff);
    LatticeStride =
        LatticeStride == 0 ? AbsCoeff : std::gcd(LatticeStride, AbsCoeff);
    StepsAndCounts.push_back({AbsCoeff, Count});
  }

  if (LatticeStride == 0) {
    Interval.Low = Low;
    Interval.High = High;
    Interval.Stride = 0;
    return Low == High;
  }

  llvm::sort(StepsAndCounts,
             [](const auto &A, const auto &B) { return A.first < B.first; });

  int64_t CoveredWidth = 0;
  for (auto [RawStep, Count] : StepsAndCounts) {
    if (RawStep == 0 || Count <= 1)
      continue;
    int64_t Step = RawStep / LatticeStride;
    if (Step > CoveredWidth + 1)
      return false;

    int64_t Extra = 0;
    if (!checkedMulTo(Step, Count - 1, Extra) ||
        !checkedAddTo(CoveredWidth, Extra))
      return false;
  }

  Interval.Low = Low;
  Interval.High = High;
  Interval.Stride = LatticeStride;
  int64_t Span = 0;
  return !SubOverflow(High, Low, Span) && positiveMod(Span, LatticeStride) == 0;
}

static bool computeShiftedDeltaInterval(
    const SCEV *AS, const SCEV *BS, ArrayRef<const Loop *> InstanceLoops,
    ArrayRef<int64_t> TripCounts, ArrayRef<int> ShiftA, ArrayRef<int> ShiftB,
    ScalarEvolution &SE, SymbolicLinearContext &Ctx,
    AffineDeltaInterval &Interval) {
  SmallVector<int64_t, 4> Lows;
  SmallVector<int64_t, 4> Highs;
  if (!computeShiftedBoxBounds(TripCounts, ShiftA, ShiftB, Lows, Highs))
    return false;

  SymbolicLinearExpr DeltaExpr;
  if (!getNormalizedShiftedDeltaExpr(AS, BS, InstanceLoops, ShiftA, ShiftB, SE,
                                     Ctx, DeltaExpr))
    return false;

  return computeContiguousImageInterval(DeltaExpr, Lows, Highs,
                                        InstanceLoops.size(), Interval);
}

static bool checkedSub(int64_t LHS, int64_t RHS, int64_t &Result) {
  return !SubOverflow(LHS, RHS, Result);
}

static int64_t floorDiv(int64_t N, int64_t D) {
  assert(D > 0 && "expected positive divisor");
  int64_t Q = N / D;
  int64_t R = N % D;
  if (R != 0 && N < 0)
    --Q;
  return Q;
}

static int64_t ceilDiv(int64_t N, int64_t D) {
  assert(D > 0 && "expected positive divisor");
  int64_t Q = N / D;
  int64_t R = N % D;
  if (R != 0 && N > 0)
    ++Q;
  return Q;
}

static bool intervalContainsValue(const AffineDeltaInterval &I, int64_t V) {
  if (V < I.Low || V > I.High)
    return false;
  if (I.Stride == 0)
    return V == I.Low;
  int64_t Diff = 0;
  return checkedSub(V, I.Low, Diff) && positiveMod(Diff, I.Stride) == 0;
}

static bool intervalsCover(AffineDeltaInterval Target,
                           SmallVectorImpl<AffineDeltaInterval> &Intervals) {
  if (Target.Stride == 0) {
    for (const AffineDeltaInterval &I : Intervals)
      if (intervalContainsValue(I, Target.Low))
        return true;
    return false;
  }

  int64_t TargetSpan = 0;
  if (!checkedSub(Target.High, Target.Low, TargetSpan) || TargetSpan < 0 ||
      positiveMod(TargetSpan, Target.Stride) != 0)
    return false;
  int64_t LastTargetIdx = TargetSpan / Target.Stride;

  SmallVector<std::pair<int64_t, int64_t>, 16> Covered;
  for (const AffineDeltaInterval &I : Intervals) {
    if (I.High < Target.Low || I.Low > Target.High)
      continue;

    if (I.Stride == 0) {
      int64_t Diff = 0;
      if (!checkedSub(I.Low, Target.Low, Diff) ||
          positiveMod(Diff, Target.Stride) != 0)
        continue;
      int64_t K = Diff / Target.Stride;
      if (K >= 0 && K <= LastTargetIdx)
        Covered.push_back({K, K});
      continue;
    }

    if (Target.Stride % I.Stride != 0)
      continue;
    int64_t ResidueDiff = 0;
    if (!checkedSub(Target.Low, I.Low, ResidueDiff) ||
        positiveMod(ResidueDiff, I.Stride) != 0)
      continue;

    int64_t LowDiff = 0;
    int64_t HighDiff = 0;
    if (!checkedSub(I.Low, Target.Low, LowDiff) ||
        !checkedSub(I.High, Target.Low, HighDiff))
      return false;
    int64_t FirstK = std::max<int64_t>(0, ceilDiv(LowDiff, Target.Stride));
    int64_t LastK =
        std::min<int64_t>(LastTargetIdx, floorDiv(HighDiff, Target.Stride));
    if (FirstK <= LastK)
      Covered.push_back({FirstK, LastK});
  }

  llvm::sort(Covered, [](const auto &A, const auto &B) {
    if (A.first != B.first)
      return A.first < B.first;
    return A.second < B.second;
  });

  int64_t Next = 0;
  for (auto [Low, High] : Covered) {
    if (High < Next)
      continue;
    if (Low > Next)
      return false;
    if (High >= LastTargetIdx)
      return true;
    Next = High + 1;
  }
  return false;
}

static bool proveAffineDeltaSetInclusionByIntervalCover(
    const SCEV *AS, const SCEV *BS, ScalarEvolution &SE,
    ArrayRef<const Loop *> InstanceLoops,
    ArrayRef<unsigned> ParallelLoopIndices) {
  if (InstanceLoops.empty() || InstanceLoops.size() > 3 ||
      ParallelLoopIndices.empty())
    return false;

  // This proof is deliberately narrower than the Presburger formulation: it
  // handles constant rectangular loop domains only.  It is exact for that
  // slice, and it avoids running a potentially expensive quantified set
  // subtraction in the middle of alias analysis.
  SmallVector<int64_t, 4> TripCounts;
  if (!getConstantRectangularTripCounts(InstanceLoops, SE, TripCounts))
    return false;

  SymbolicLinearContext Ctx(InstanceLoops);
  SmallVector<int, 4> ZeroShift(InstanceLoops.size(), 0);
  AffineDeltaInterval SameInterval;
  if (!computeShiftedDeltaInterval(AS, BS, InstanceLoops, TripCounts, ZeroShift,
                                   ZeroShift, SE, Ctx, SameInterval))
    return false;

  SmallVector<AffineDeltaInterval, 32> CrossIntervals;
  SmallVector<int, 4> ShiftA(InstanceLoops.size(), 0);
  SmallVector<int, 4> ShiftB(InstanceLoops.size(), 0);
  constexpr unsigned MaxAffineIntervalCrossIntervals = 64;

  std::function<void(unsigned)> Enumerate = [&](unsigned Component) {
    if (CrossIntervals.size() >= MaxAffineIntervalCrossIntervals)
      return;

    if (Component == 2 * InstanceLoops.size()) {
      if (!shiftsAreLogicallyParallel(ShiftA, ShiftB, ParallelLoopIndices))
        return;
      AffineDeltaInterval CrossInterval;
      if (computeShiftedDeltaInterval(AS, BS, InstanceLoops, TripCounts, ShiftA,
                                      ShiftB, SE, Ctx, CrossInterval))
        CrossIntervals.push_back(CrossInterval);
      return;
    }

    SmallVectorImpl<int> &Shift =
        Component < InstanceLoops.size() ? ShiftA : ShiftB;
    unsigned ShiftIdx = Component % InstanceLoops.size();
    for (int Step : {-1, 0, 1}) {
      Shift[ShiftIdx] = Step;
      Enumerate(Component + 1);
      if (CrossIntervals.size() >= MaxAffineIntervalCrossIntervals)
        break;
    }
    Shift[ShiftIdx] = 0;
  };
  Enumerate(0);

  if (CrossIntervals.empty() || !intervalsCover(SameInterval, CrossIntervals))
    return false;

  LLVM_DEBUG(dbgs() << "DRFAA: alias-implies-race via affine interval "
                       "delta-set inclusion proof\n");
  return true;
}

static bool
proveAffineDeltaSetInclusion(const SCEV *AS, const SCEV *BS,
                             ScalarEvolution &SE,
                             ArrayRef<const Loop *> InstanceLoops,
                             ArrayRef<unsigned> ParallelLoopIndices) {
  if (InstanceLoops.empty() || InstanceLoops.size() > 4 ||
      ParallelLoopIndices.empty())
    return false;

  // Treating a loop-defined SCEVUnknown as an unconstrained parameter would
  // let non-affine indexed accesses fabricate cross-task witnesses.
  if (hasUnknownDefinedInAnyLoop(AS, InstanceLoops) ||
      hasUnknownDefinedInAnyLoop(BS, InstanceLoops))
    return false;

  if (proveAffineDeltaSetInclusionByIntervalCover(AS, BS, SE, InstanceLoops,
                                                  ParallelLoopIndices))
    return true;

  // The general Presburger relation below is opt-in: exact subset checking
  // with existential loop locals is too expensive to run from AA queries
  // without a cost model.  Dense 3D stencils generate many failed queries, so
  // keep this path to low-dimensional loop domains unless explicitly raised.
  if (!EnableDRFAAPresburgerDeltaSetProof ||
      InstanceLoops.size() > DRFAAMaxPresburgerDeltaSetLoopVars)
    return false;

  SymbolicLinearContext Ctx(InstanceLoops);
  SymbolicLinearExpr ASExpr;
  SymbolicLinearExpr BSExpr;
  if (!linearizeSCEV(AS, Ctx, SE, ASExpr) ||
      !linearizeSCEV(BS, Ctx, SE, BSExpr))
    return false;

  SmallVector<int, 4> ZeroShift(InstanceLoops.size(), 0);
  SmallVector<SymbolicLinearExpr, 4> TripExprs;
  for (unsigned I = 0; I < InstanceLoops.size(); ++I) {
    SymbolicLinearExpr Trip;
    if (!linearizeTripCount(I, InstanceLoops, ZeroShift, SE, Ctx, Trip))
      return false;
    TripExprs.push_back(std::move(Trip));
  }

  unsigned NumLoopVars = InstanceLoops.size();
  SmallVector<int, 8> SymbolMap;
  collectPresburgerTripSymbols(TripExprs, NumLoopVars, Ctx.SymbolIndices.size(),
                               SymbolMap);
  unsigned NumSymbols = countPresburgerSymbols(SymbolMap);
  constexpr unsigned MaxAffineDeltaSymbols = 8;
  if (NumSymbols > MaxAffineDeltaSymbols)
    return false;

  std::optional<mlir::presburger::PresburgerSet> Same =
      buildSameInstanceDeltaSet(ASExpr, BSExpr, TripExprs, NumLoopVars,
                                NumSymbols, SymbolMap);
  // Set inclusion is vacuously true for an empty left-hand side.  Such an
  // answer cannot establish that a real same-instance alias has a cross-task
  // race witness, so keep this check as a final defense against malformed or
  // contradictory domain models.
  if (!Same || Same->isIntegerEmpty())
    return false;

  std::optional<mlir::presburger::PresburgerSet> Cross =
      buildCrossTaskDeltaSet(ASExpr, BSExpr, TripExprs, NumLoopVars, NumSymbols,
                             SymbolMap, ParallelLoopIndices);
  if (!Cross)
    return false;

  if (Same->subtract(*Cross).isIntegerEmpty()) {
    LLVM_DEBUG(dbgs() << "DRFAA: alias-implies-race via affine delta-set "
                         "inclusion proof\n");
    return true;
  }

  return false;
}

// Symbolic affine slice of the delta-set proof.  Instead of enumerating every
// concrete loop point, enumerate small constant witness shifts (A at x+dA,
// B at x+dB), keep the shifts whose address delta is algebraically identical
// to the same-instance A(x)-B(x) delta, and use affine domain constraints to
// prove every original point is covered by at least one valid shifted witness.
// This is intentionally not a full Presburger solver: if coverage needs a
// witness whose coordinates are symbolic affine functions of x rather than
// small constant shifts, this proof bails and the bounded enumerator below gets
// the next chance.
static bool aliasWouldImplyParallelRaceViaSymbolicDeltaSetInclusion(
    const SCEV *AS, const SCEV *BS, ScalarEvolution &SE,
    ArrayRef<const Loop *> InstanceLoops,
    ArrayRef<unsigned> ParallelLoopIndices) {
  if (InstanceLoops.empty() || InstanceLoops.size() > 4)
    return false;

  // Treating a loop-defined SCEVUnknown as an unconstrained symbol would make
  // an indirect access such as a[idx[i]] look invariant.  Require affine
  // addrecs over the instance loops instead.
  if (hasUnknownDefinedInAnyLoop(AS, InstanceLoops) ||
      hasUnknownDefinedInAnyLoop(BS, InstanceLoops))
    return false;

  SymbolicLinearContext Ctx(InstanceLoops);
  SmallVector<SymbolicDeltaWitness, 8> Witnesses;
  constexpr unsigned MaxSymbolicDeltaWitnesses = 8;

  SmallVector<int, 4> ShiftA(InstanceLoops.size(), 0);
  SmallVector<int, 4> ShiftB(InstanceLoops.size(), 0);
  std::function<void(unsigned)> Enumerate = [&](unsigned Component) {
    if (Witnesses.size() >= MaxSymbolicDeltaWitnesses)
      return;

    if (Component == 2 * InstanceLoops.size()) {
      SymbolicDeltaWitness Witness;
      if (buildSymbolicDeltaWitness(AS, BS, InstanceLoops, ParallelLoopIndices,
                                    ShiftA, ShiftB, SE, Ctx, Witness))
        Witnesses.push_back(std::move(Witness));
      return;
    }

    SmallVectorImpl<int> &Shift =
        Component < InstanceLoops.size() ? ShiftA : ShiftB;
    unsigned ShiftIdx = Component % InstanceLoops.size();
    for (int Step : {-1, 0, 1}) {
      Shift[ShiftIdx] = Step;
      Enumerate(Component + 1);
      if (Witnesses.size() >= MaxSymbolicDeltaWitnesses)
        break;
    }
    Shift[ShiftIdx] = 0;
  };
  Enumerate(0);

  if (Witnesses.empty())
    return false;

  if (!proveDomainCoveredBySymbolicDeltaWitnesses(InstanceLoops, SE, Ctx,
                                                  Witnesses))
    return false;

  LLVM_DEBUG(dbgs() << "DRFAA: alias-implies-race via symbolic affine "
                       "delta-set inclusion proof\n");
  return true;
}

static bool aliasWouldImplyParallelRaceViaDeltaSetInclusion(
    const TaskInfo &TI, const MemoryLocation &LocA, const MemoryLocation &LocB,
    const Instruction *AccessA, const Instruction *AccessB, const SCEV *AS,
    const SCEV *BS, ScalarEvolution &SE,
    DRFAADeltaSetProofCache *DeltaSetCache) {
  if (!EnableDRFAADeltaSetProof)
    return false;

  if (mayShareUnderlyingObject(LocA.Ptr, LocB.Ptr))
    return false;

  uint64_t SizeA = 0;
  uint64_t SizeB = 0;
  if (!getFixedLocationSize(LocA.Size, SizeA) ||
      !getFixedLocationSize(LocB.Size, SizeB) || SizeA != SizeB)
    return false;

  // This first slice reasons about equality of access start addresses.  Require
  // element-sized alignment so any byte-overlap between equal-sized accesses is
  // also a start-address equality; otherwise a partial overlap could escape the
  // delta set.
  if (!accessHasStartAlignmentAtLeast(AccessA, SizeA) ||
      !accessHasStartAlignmentAtLeast(AccessB, SizeB))
    return false;

  SmallVector<const Loop *, 4> ParallelLoops;
  collectParallelWitnessLoops(AccessA, AccessB, AS, BS, TI, ParallelLoops);
  if (ParallelLoops.empty())
    return false;

  SmallVector<const Loop *, 8> InstanceLoops;
  collectCommonInstanceLoops(AccessA, AccessB, AS, BS, InstanceLoops);
  if (InstanceLoops.empty())
    return false;

  SmallVector<unsigned, 4> ParallelLoopIndices;
  if (!getParallelLoopIndices(InstanceLoops, ParallelLoops,
                              ParallelLoopIndices))
    return false;

  for (const Loop *L : InstanceLoops)
    if (!isGuaranteedInEveryIteration(AccessA, L, TI) ||
        !isGuaranteedInEveryIteration(AccessB, L, TI))
      return false;

  // Make both the proof algorithm and its cache key independent of operand
  // order.  This avoids caching a heuristic failure from one ordering while
  // computing the reverse ordering separately.
  const SCEV *ProofAS = AS;
  const SCEV *ProofBS = BS;
  if (std::less<const SCEV *>()(ProofBS, ProofAS))
    std::swap(ProofAS, ProofBS);

  auto ComputeProof = [&]() {
    if (proveAffineDeltaSetInclusion(ProofAS, ProofBS, SE, InstanceLoops,
                                     ParallelLoopIndices))
      return true;

    if (InstanceLoops.size() > DRFAAMaxExhaustiveDeltaSetLoopVars)
      return false;

    if (aliasWouldImplyParallelRaceViaSymbolicDeltaSetInclusion(
            ProofAS, ProofBS, SE, InstanceLoops, ParallelLoopIndices))
      return true;

    DenseSet<const SCEV *> QueryDeltas;
    if (!collectSameInstanceDeltas(ProofAS, ProofBS, SE, InstanceLoops,
                                   QueryDeltas) ||
        QueryDeltas.empty())
      return false;

    SmallVector<DeltaSetTouch, 128> TouchesA;
    SmallVector<DeltaSetTouch, 128> TouchesB;
    if (!collectDeltaSetTouches(ProofAS, SE, InstanceLoops, ParallelLoopIndices,
                                TouchesA) ||
        !collectDeltaSetTouches(ProofBS, SE, InstanceLoops, ParallelLoopIndices,
                                TouchesB))
      return false;

    constexpr uint64_t MaxDeltaSetRacePairs = 4 * 1024 * 1024;
    if (TouchesA.empty() || TouchesB.empty() ||
        static_cast<uint64_t>(TouchesA.size()) * TouchesB.size() >
            MaxDeltaSetRacePairs)
      return false;

    for (const DeltaSetTouch &A : TouchesA) {
      for (const DeltaSetTouch &B : TouchesB) {
        if (!taskPointsAreLogicallyParallel(A.TaskPoint, B.TaskPoint,
                                            ParallelLoopIndices))
          continue;

        const SCEV *Delta = getAddressDeltaSCEV(A.Addr, B.Addr, SE);
        if (isa<SCEVCouldNotCompute>(Delta))
          return false;

        auto It = QueryDeltas.find(Delta);
        if (It == QueryDeltas.end())
          continue;

        QueryDeltas.erase(It);
        if (QueryDeltas.empty()) {
          LLVM_DEBUG(dbgs() << "DRFAA: alias-implies-race via delta-set "
                               "inclusion proof\n");
          return true;
        }
      }
    }

    return false;
  };

  if (!DeltaSetCache)
    return ComputeProof();

  DRFAADeltaSetProofCache::Key Key;
  Key.AS = ProofAS;
  Key.BS = ProofBS;
  Key.InstanceLoops.assign(InstanceLoops.begin(), InstanceLoops.end());
  Key.ParallelLoopIndices.assign(ParallelLoopIndices.begin(),
                                 ParallelLoopIndices.end());

  if (std::optional<bool> Cached = DeltaSetCache->lookup(Key)) {
    LLVM_DEBUG(dbgs() << "DRFAA: delta-set proof cache hit: " << *Cached
                      << "\n");
    return *Cached;
  }

  bool Result = ComputeProof();
  DeltaSetCache->insert(std::move(Key), Result);
  return Result;
}

/// Return true when every loop coordinate omitted from ParallelLoops repeats
/// the same execution schedule across the modeled parallel domain. The fiber
/// proof can reason directly about varying bounds of loops in ParallelLoops,
/// but a varying serial child loop would otherwise be an invisible dimension.
static bool hasNoUnmodeledVaryingSchedule(
    const Instruction *Access, const TaskInfo &TI, ScalarEvolution &SE,
    ArrayRef<const Loop *> ParallelLoops) {
  if (!Access || ParallelLoops.empty() || DRFAAAssumedMinTripCount < 2)
    return false;

  SmallPtrSet<const Loop *, 4> ModeledLoops;
  for (const Loop *L : ParallelLoops)
    ModeledLoops.insert(L);

  const Loop *Outermost = ParallelLoops.front();
  if (!Outermost->contains(Access->getParent()))
    return false;

  const Loop *Innermost = Outermost;
  for (bool Descended = true; Descended;) {
    Descended = false;
    for (const Loop *Sub : Innermost->getSubLoops())
      if (Sub->contains(Access->getParent())) {
        Innermost = Sub;
        Descended = true;
        break;
      }
  }

  if (!executesOnEveryTakenLoopIteration(Access, Innermost, TI))
    return false;

  for (const Loop *L = Innermost; L != Outermost;
       L = L->getParentLoop()) {
    const Loop *Parent = L->getParentLoop();
    if (!Parent || !isUnconditionallyEnteredFromParentIteration(L, Parent))
      return false;

    if (ModeledLoops.contains(L))
      continue;

    if (SE.getSmallConstantMaxTripCount(L) == 1)
      return false;
    const SCEV *BackedgeCount = SE.getBackedgeTakenCount(L);
    if (isa<SCEVCouldNotCompute>(BackedgeCount))
      return false;

    for (const Loop *ParallelLoop : ParallelLoops)
      if (ParallelLoop->contains(L->getHeader()) &&
          !SE.isLoopInvariant(BackedgeCount, ParallelLoop))
        return false;
  }

  return true;
}

static bool accessAddressReplicatedAcrossParallelTasks(
    const Instruction *Access, const SCEV *AddrS,
    const Instruction *OtherAccess, const TaskInfo &TI, ScalarEvolution &SE,
    ArrayRef<const Loop *> ParallelLoops) {
  SmallVector<int64_t, 4> Gradient;
  if (!getParallelGradient(AddrS, SE, ParallelLoops, Gradient))
    return false;

  // Reject serial inner dimensions that are invisible to the fiber-domain
  // proof unless their schedule repeats across every modeled parallel axis.
  if (!hasNoUnmodeledVaryingSchedule(Access, TI, SE, ParallelLoops))
    return false;

  if (!proveParallelFiberCoverage(Access, AddrS, OtherAccess, TI, SE,
                                  ParallelLoops, Gradient))
    return false;

  // Access is the replicated-address witness. OtherAccess is the concrete
  // queried access: if it executes and aliases Access, a matching execution of
  // Access in another logical iteration creates the race, so OtherAccess need
  // not be must-execute in every sibling.
  LLVM_DEBUG({
    dbgs() << "DRFAA: replicated parallel-address witness for " << *Access
           << " with gradient [";
    for (unsigned I = 0; I < Gradient.size(); ++I) {
      if (I)
        dbgs() << ", ";
      dbgs() << Gradient[I];
    }
    dbgs() << "]\n";
  });
  return true;
}

static bool aliasWouldImplyParallelRaceViaReplicatedAccess(
    const TaskInfo &TI, const MemoryLocation &LocA, const MemoryLocation &LocB,
    const Instruction *AccessA, const Instruction *AccessB, const SCEV *AS,
    const SCEV *BS, ScalarEvolution &SE) {
  // This witness reasons about distinct logical objects.  Same-object
  // cross-iteration questions are handled by parallel-slice reasoning; for a
  // same-object ordinary query, a same-strand overlap can be legal and must not
  // be ruled out through this path.
  if (mayShareUnderlyingObject(LocA.Ptr, LocB.Ptr))
    return false;

  SmallVector<const Loop *, 4> ParallelLoops;
  collectParallelWitnessLoops(AccessA, AccessB, AS, BS, TI, ParallelLoops);
  if (ParallelLoops.empty())
    return false;

  if (accessAddressReplicatedAcrossParallelTasks(AccessA, AS, AccessB, TI, SE,
                                                 ParallelLoops) ||
      accessAddressReplicatedAcrossParallelTasks(AccessB, BS, AccessA, TI, SE,
                                                 ParallelLoops)) {
    LLVM_DEBUG(dbgs() << "DRFAA: alias-implies-race via replicated "
                         "parallel-address witness\n");
    return true;
  }

  return false;
}

static bool aliasWouldImplyParallelRaceViaAsymmetricAxis(
    const TaskInfo &TI, const MemoryLocation &LocA, const MemoryLocation &LocB,
    const Instruction *AccessA, const Instruction *AccessB, const SCEV *AS,
    const SCEV *BS, ScalarEvolution &SE, const Loop *Scope = nullptr) {
  SmallVector<const Loop *, 4> CandidateLoops;
  SmallPtrSet<const Loop *, 4> SeenLoops;
  collectLoopsFromSCEV(AS, CandidateLoops, SeenLoops);
  collectLoopsFromSCEV(BS, CandidateLoops, SeenLoops);

  // A pointer-table lookup such as Rows[i] is opaque to SCEV. For a scoped
  // LAA query it is nevertheless safe to ask whether it varies across an
  // enclosing Tapir axis: the SCEVUnknown is defined inside that axis. Do not
  // infer that table entries are affine or distinct, and do not expose this as
  // a context-free AA result.
  for (const Loop *L = Scope; L; L = L->getParentLoop())
    if (SeenLoops.insert(L).second)
      CandidateLoops.push_back(L);

  bool SawCommonLoop = false;
  bool SawLoopCarriedLoop = false;
  bool SawAsymmetricLoop = false;
  bool SawGuaranteedAsymmetricWitness = false;
  for (const Loop *L : CandidateLoops) {
    if (!L->contains(AccessA->getParent()) ||
        !L->contains(AccessB->getParent()))
      continue;
    SawCommonLoop = true;
    if (!isDRFLogicallyParallelLoop(L, &TI))
      continue;
    SawLoopCarriedLoop = true;

    const bool AVaries = scevMayVaryAcrossLoopIterations(AS, L);
    const bool BVaries = scevMayVaryAcrossLoopIterations(BS, L);
    if (AVaries == BVaries)
      continue;
    SawAsymmetricLoop = true;

    // A serialized Tapir-derived chunk may reuse one alloca that represented
    // distinct task-private objects in the source. Such storage cannot be a
    // cross-task race witness even if its lowered pointer now looks invariant.
    if (mayUseReboundTaskPrivateStorage(LocA, L, TI) ||
        mayUseReboundTaskPrivateStorage(LocB, L, TI))
      continue;

    // Only the loop-invariant access is the replicated sibling witness. The
    // varying access may be guarded: whenever that concrete access executes
    // and aliases the invariant address, a matching execution of the witness
    // in another logical iteration establishes the forbidden race.
    const Instruction *WitnessAccess = AVaries ? AccessB : AccessA;
    bool UsedNestedSchedule = false;
    if (!hasReplicatedInnerSchedule(WitnessAccess, L, TI, SE,
                                    UsedNestedSchedule))
      continue;
    SawGuaranteedAsymmetricWitness = true;
    if (UsedNestedSchedule)
      ++NumNestedAsymmetricAxisProofs;

    LLVM_DEBUG(dbgs() << "DRFAA: alias-implies-race via asymmetric Tapir axis "
                      << L->getHeader()->getName() << "\n");
    return true;
  }

  if (!SawCommonLoop)
    drfaaDumpQueryReason("axis-no-common-loop", LocA, LocB, AccessA, AccessB,
                         AS, BS);
  else if (!SawLoopCarriedLoop)
    drfaaDumpQueryReason("axis-no-loop-carried-parallel-loop", LocA, LocB,
                         AccessA, AccessB, AS, BS);
  else if (!SawAsymmetricLoop)
    drfaaDumpQueryReason("axis-not-asymmetric", LocA, LocB, AccessA, AccessB,
                         AS, BS);
  else if (!SawGuaranteedAsymmetricWitness)
    drfaaDumpQueryReason("axis-witness-schedule-not-replicated", LocA, LocB,
                         AccessA, AccessB, AS, BS);
  return false;
}

static bool aliasWouldImplyParallelRace(
    const TaskInfo &TI, const MemoryLocation &LocA, const MemoryLocation &LocB,
    const Instruction *AddrA, const Instruction *AddrB, ScalarEvolution &SE,
    DRFAADeltaSetProofCache *DeltaSetCache = nullptr) {
  const Instruction *AccessA = findRepresentativeAccess(LocA, AddrA);
  const Instruction *AccessB = findRepresentativeAccess(LocB, AddrB);
  if (!AccessA || !AccessB ||
      AccessA->getFunction() != AccessB->getFunction()) {
    drfaaDumpQueryReason("no-representative-access", LocA, LocB, AddrA, AddrB);
    return false;
  }

  // A read/read overlap is race-free, so DRF cannot rule it out.
  if (!accessMayRace(AccessA) && !accessMayRace(AccessB)) {
    drfaaDumpQueryReason("read-read", LocA, LocB, AccessA, AccessB);
    return false;
  }

  // Hyperobject view accesses are mediated by the runtime, so two parallel
  // view accesses of one hyperobject may legally alias: they can never form a
  // race witness against each other, and the proofs below must not run on a
  // view-vs-view pair.  Against an *ordinary* access the serial-projection
  // race model maps every view access of hyperobject h onto h's leftmost
  // storage (runtime-allocated views are runtime-private and unreachable from
  // ordinary pointers), so a view/ordinary overlap implies a cross-strand race
  // on that storage, which DRF forbids.  Encode both facts by substituting the
  // hyperobject handle for the view on exactly one side, and refusing to
  // reason when both sides are views.
  MemoryLocation EffLocA = LocA;
  MemoryLocation EffLocB = LocB;
  if (EnableDRFAAHyperView) {
    const Value *HyperA = getHyperViewHyperobject(LocA.Ptr);
    const Value *HyperB = getHyperViewHyperobject(LocB.Ptr);
    if (HyperA && HyperB) {
      drfaaDumpQueryReason("hyper-view-both-sides", LocA, LocB, AccessA,
                           AccessB);
      return false;
    }
    if (HyperA)
      EffLocA = MemoryLocation(HyperA, LocA.Size, LocA.AATags);
    if (HyperB)
      EffLocB = MemoryLocation(HyperB, LocB.Size, LocB.AATags);
  }

  const SCEV *AS = SE.getSCEV(const_cast<Value *>(EffLocA.Ptr));
  const SCEV *BS = SE.getSCEV(const_cast<Value *>(EffLocB.Ptr));
  if (isa<SCEVCouldNotCompute>(AS) || isa<SCEVCouldNotCompute>(BS)) {
    drfaaDumpQueryReason("scev-could-not-compute", LocA, LocB, AccessA, AccessB,
                         AS, BS);
    return false;
  }

  if (aliasWouldImplyParallelRaceViaAsymmetricAxis(
          TI, EffLocA, EffLocB, AccessA, AccessB, AS, BS, SE))
    return true;

  if (EnableDRFAADeltaSetProof) {
    SmallVector<const Instruction *, 8> AccessesA;
    SmallVector<const Instruction *, 8> AccessesB;
    collectRepresentativeAccesses(LocA, AddrA, AccessesA);
    collectRepresentativeAccesses(LocB, AddrB, AccessesB);

    bool SawDeltaCandidate = false;
    for (const Instruction *CandidateA : AccessesA) {
      for (const Instruction *CandidateB : AccessesB) {
        if (!CandidateA || !CandidateB ||
            CandidateA->getFunction() != CandidateB->getFunction())
          continue;
        if (!accessMayRace(CandidateA) && !accessMayRace(CandidateB))
          continue;
        SawDeltaCandidate = true;
        if (aliasWouldImplyParallelRaceViaDeltaSetInclusion(
                TI, EffLocA, EffLocB, CandidateA, CandidateB, AS, BS, SE,
                DeltaSetCache))
          return true;
      }
    }
    if (!SawDeltaCandidate)
      drfaaDumpQueryReason("delta-no-candidate-access-pair", LocA, LocB,
                           AccessA, AccessB, AS, BS);
    else
      drfaaDumpQueryReason("delta-no-proof", LocA, LocB, AccessA, AccessB, AS,
                           BS);
  } else {
    drfaaDumpQueryReason("delta-disabled", LocA, LocB, AccessA, AccessB, AS,
                         BS);
  }

  bool ReplicatedProof = aliasWouldImplyParallelRaceViaReplicatedAccess(
      TI, EffLocA, EffLocB, AccessA, AccessB, AS, BS, SE);
  if (!ReplicatedProof)
    drfaaDumpQueryReason("all-race-proofs-failed", LocA, LocB, AccessA, AccessB,
                         AS, BS);
  return ReplicatedProof;
}

DRFProofKind llvm::classifyDRFAliasProof(
    const TaskInfo &TI, const MemoryLocation &LocA, const MemoryLocation &LocB,
    const Instruction *AddrA, const Instruction *AddrB, ScalarEvolution &SE,
    DRFAADeltaSetProofCache *DeltaSetCache) {
  if (!EnableDRFAA)
    return DRFProofKind::Unknown;
  return aliasWouldImplyParallelRace(TI, LocA, LocB, AddrA, AddrB, SE,
                                     DeltaSetCache)
             ? DRFProofKind::NoAlias
             : DRFProofKind::Unknown;
}

DRFProofKind llvm::classifyDRFAliasProof(
    const TaskInfo &TI, const MemoryLocation &LocA, const MemoryLocation &LocB,
    const Instruction *AddrA, const Instruction *AddrB, ScalarEvolution &SE) {
  return classifyDRFAliasProof(TI, LocA, LocB, AddrA, AddrB, SE, nullptr);
}

bool llvm::drfAliasWouldImplyParallelRace(
    const TaskInfo &TI, const MemoryLocation &LocA, const MemoryLocation &LocB,
    const Instruction *AddrA, const Instruction *AddrB, ScalarEvolution &SE,
    DRFAADeltaSetProofCache *DeltaSetCache) {
  return classifyDRFAliasProof(TI, LocA, LocB, AddrA, AddrB, SE,
                               DeltaSetCache) == DRFProofKind::NoAlias;
}

bool llvm::drfAliasWouldImplyParallelRace(
    const TaskInfo &TI, const MemoryLocation &LocA, const MemoryLocation &LocB,
    const Instruction *AddrA, const Instruction *AddrB, ScalarEvolution &SE) {
  return classifyDRFAliasProof(TI, LocA, LocB, AddrA, AddrB, SE) ==
         DRFProofKind::NoAlias;
}

bool llvm::drfAliasWouldImplyRaceViaEnclosingParallelLoop(
    const Loop *InnerLoop, const TaskInfo &TI, const MemoryLocation &LocA,
    const MemoryLocation &LocB, const Instruction *AccessA,
    const Instruction *AccessB, ScalarEvolution &SE) {
  if (!EnableDRFAA || !InnerLoop || !AccessA || !AccessB ||
      AccessA->getFunction() != AccessB->getFunction() ||
      !memoryInstUsesLocation(AccessA, LocA) ||
      !memoryInstUsesLocation(AccessB, LocB) ||
      !isOrdinaryDRFMemoryAccess(AccessA) ||
      !isOrdinaryDRFMemoryAccess(AccessB) ||
      (!accessMayRace(AccessA) && !accessMayRace(AccessB)))
    return false;

  const SCEV *AS = SE.getSCEV(const_cast<Value *>(LocA.Ptr));
  const SCEV *BS = SE.getSCEV(const_cast<Value *>(LocB.Ptr));
  if (isa<SCEVCouldNotCompute>(AS) || isa<SCEVCouldNotCompute>(BS))
    return false;

  if (!aliasWouldImplyParallelRaceViaAsymmetricAxis(
          TI, LocA, LocB, AccessA, AccessB, AS, BS, SE, InnerLoop))
    return false;

  ++NumEnclosingParallelAxisProofs;
  return true;
}

AliasResult DRFAAResult::alias(const MemoryLocation &LocA,
                               const MemoryLocation &LocB, AAQueryInfo &AAQI,
                               const Instruction *CtxI) {
  if (!EnableDRFAA)
    return AAResultBase::alias(LocA, LocB, AAQI, CtxI);

  LLVM_DEBUG(dbgs() << "DRFAA:\n\tLocA.Ptr = " << *LocA.Ptr
                    << "\n\tLocB.Ptr = " << *LocB.Ptr << "\n");
  assert(notDifferentParent(LocA.Ptr, LocB.Ptr) &&
         "DRFAliasAnalysis doesn't support interprocedural queries.");

  // The ordinary two-access rule below deliberately abstains on a same-task
  // pair. A guaranteed sibling read can provide the third-access race witness
  // for that pair. Its finite footprints cover all serial iteration choices,
  // so this is also valid when AAQI.MayBeCrossIteration is set. Do not consult
  // dominance-derived facts while a caller is lazily updating the DT.
  // One pointer defined in the function pins the query to that function's
  // phase; the other may be a root (argument, global, pre-phase value) of the
  // same function, which is how an unrolled offset-0 element is addressed.
  const Function *WitnessF = nullptr;
  for (const Value *V : {LocA.Ptr, LocB.Ptr})
    if (const auto *I = dyn_cast<Instruction>(V))
      if (I->getParent()) {
        WitnessF = I->getFunction();
        break;
      }
  auto InWitnessF = [&](const Value *V) {
    if (const auto *I = dyn_cast<Instruction>(V))
      return I->getParent() && I->getFunction() == WitnessF;
    if (const auto *Arg = dyn_cast<Argument>(V))
      return Arg->getParent() == WitnessF;
    return isa<GlobalValue>(V);
  };
  if (isDRFAASiblingWitnessEnabled() && AAQI.UseDominatorTree && WitnessF &&
      InWitnessF(LocA.Ptr) && InWitnessF(LocB.Ptr)) {
    if (!SiblingWitnessInfo)
      SiblingWitnessInfo = std::make_unique<DRFSiblingWitnessInfo>(
          *const_cast<Function *>(WitnessF));
    if (SiblingWitnessInfo->alias(LocA, LocB, CtxI) == AliasResult::NoAlias)
      return AliasResult::NoAlias;
  }

  // Two hyperobject view pointers may legally alias even across parallel
  // strands (the runtime mediates view access), so the DRF assumption yields
  // no information for a view-vs-view query.  In particular the definite-
  // parallel distinct-objects conclusion below would be wrong: two lookups of
  // the same hyperobject are distinct "objects" to getUnderlyingObjects, yet
  // they denote the same storage in the serial projection.  Abstain entirely.
  if (EnableDRFAAHyperView && getHyperViewHyperobject(LocA.Ptr) &&
      getHyperViewHyperobject(LocB.Ptr)) {
    drfaaDumpQueryReason("alias-hyper-view-both-sides", LocA, LocB,
                         dyn_cast<Instruction>(LocA.Ptr),
                         dyn_cast<Instruction>(LocB.Ptr));
    return AAResultBase::alias(LocA, LocB, AAQI, CtxI);
  }

  const Instruction *AddrA = getAccessInstForLoc(LocA, CtxI);
  const Instruction *AddrB = getAccessInstForLoc(LocB, CtxI);
  if (!AddrA || !AddrB) {
    drfaaDumpQueryReason("alias-no-access-inst", LocA, LocB, AddrA, AddrB);
    return AAResultBase::alias(LocA, LocB, AAQI, CtxI);
  }

  // Distinguish the two kinds of evidence.  Definite parallelism means the
  // accesses are in distinct parallel tasks for *every* dynamic instance,
  // so the data-race-free assumption forbids aliasing outright.  Loop-
  // carried parallelism only means the accesses are in distinct
  // *iterations* of the same Tapir-loop body; for a given iteration they
  // execute in one serial strand, where aliasing is race-free and legal. So
  // loop-carried evidence must never license an unconditional no-alias
  // answer.
  bool DefinitelyParallel = TI.isDefinitelyLogicallyParallel(AddrA, AddrB);
  bool LoopCarriedParallel =
      !DefinitelyParallel && TI.isLoopCarriedLogicallyParallel(AddrA, AddrB);

  LLVM_DEBUG(dbgs() << "DRFAA: alias definitely? " << DefinitelyParallel
                    << " loop-carried? " << LoopCarriedParallel << "\n");

  if (!DefinitelyParallel && !LoopCarriedParallel) {
    drfaaDumpQueryReason("alias-not-logically-parallel", LocA, LocB, AddrA,
                         AddrB);
    return AAResultBase::alias(LocA, LocB, AAQI, CtxI);
  }

  AliasResult BasicAR = basicAAFallback(LocA, LocB, CtxI, AAQI, BAA, TLI);
  if (BasicAR != AliasResult::MayAlias)
    return BasicAR;

  if (LoopCarriedParallel) {
    const bool ShareObject = mayShareUnderlyingObject(LocA.Ptr, LocB.Ptr);

    // Cross-iteration parallelism is only sound evidence for no-alias on
    // the *same* allocation when the query is explicitly about distinct
    // iterations and the per-iteration address slices are provably
    // disjoint.  In particular it is *not* a license to treat two same-
    // iteration accesses to the same object as non-aliasing: they may be
    // the same address accessed in one serial strand.
    if (AAQI.MayBeCrossIteration && ShareObject &&
        proveNoAliasViaParallelSlices(LocA, LocB, SE))
      return AliasResult::NoAlias;

    // The asymmetric "alias would imply a parallel race" argument applies
    // to distinct allocations: in an every-iteration access pair where
    // exactly one operand is loop-invariant, the invariant operand is
    // touched at the same address in every sibling iteration while the
    // varying operand sweeps a different address each iteration.  If the
    // two could ever overlap, the overlapping address would be written in
    // one iteration and accessed in the others, a cross-iteration
    // write/read race that the data-race-free assumption forbids -- so
    // they never overlap.  This is sound for an ordinary same-body query,
    // and also for a cross-iteration query: such a query concerns pairs
    // of accesses in distinct iterations, which exist only when the loop
    // runs at least twice, exactly the regime in which the race witness
    // is available.  (We only take this path for distinct allocations;
    // same-allocation cross-iteration queries are handled by the slice
    // reasoning above, and the both-vary same-iteration case is excluded
    // inside aliasWouldImplyParallelRace via its asymmetry requirement.)
    if ((!AAQI.MayBeCrossIteration || !ShareObject) &&
        aliasWouldImplyParallelRace(TI, LocA, LocB, AddrA, AddrB, SE,
                                    DeltaSetProofCache.get()))
      return AliasResult::NoAlias;

    drfaaDumpQueryReason(ShareObject ? "loopcarried-same-object-mayalias"
                                     : "loopcarried-race-proof-failed",
                         LocA, LocB, AddrA, AddrB);
    return AAResultBase::alias(LocA, LocB, AAQI, CtxI);
  }

  if (mayShareUnderlyingObject(LocA.Ptr, LocB.Ptr)) {
    if (AAQI.MayBeCrossIteration) {
      // Parallel loop iterations frequently access the same allocation
      // through identical addrecs evaluated at different dynamic
      // iterations. Recover the no-alias answer by proving each access
      // stays within one stride-sized slice of the common object.
      if (proveNoAliasViaParallelSlices(LocA, LocB, SE))
        return AliasResult::NoAlias;
    } else {
      AliasResult SCEVAR = aliasBasedOnScalarEvolution(SE, LocA, LocB);
      if (SCEVAR != AliasResult::MayAlias)
        return SCEVAR;
    }
    drfaaDumpQueryReason("definite-same-object-mayalias", LocA, LocB, AddrA,
                         AddrB);
    return AAResultBase::alias(LocA, LocB, AAQI, CtxI);
  }

  return AliasResult::NoAlias;
}

ModRefInfo DRFAAResult::getModRefInfo(const CallBase *Call,
                                      const MemoryLocation &Loc,
                                      AAQueryInfo &AAQI) {
  if (!EnableDRFAA)
    return AAResultBase::getModRefInfo(Call, Loc, AAQI);

  LLVM_DEBUG(dbgs() << "DRFAA:getModRefInfo(Call, Loc)\n");
  assert(notDifferentParent(Call, Loc.Ptr) &&
         "DRFAliasAnalysis doesn't support interprocedural queries.");

  if (const Instruction *Addr = dyn_cast<Instruction>(Loc.Ptr)) {
    const Task *CallTask = TI.getTaskFor(Call->getParent());
    const Task *AddrTask = TI.getTaskFor(Addr->getParent());
    if (hasDRFParallelism(TI, Call, Addr) &&
        (CallTask != AddrTask || isTaskPrivatePromotableAlloca(Loc.Ptr, TI)))
      return ModRefInfo::NoModRef;
  }

  return AAResultBase::getModRefInfo(Call, Loc, AAQI);
}

ModRefInfo DRFAAResult::getModRefInfo(const CallBase *Call1,
                                      const CallBase *Call2,
                                      AAQueryInfo &AAQI) {
  if (!EnableDRFAA)
    return AAResultBase::getModRefInfo(Call1, Call2, AAQI);

  LLVM_DEBUG(dbgs() << "DRFAA:getModRefInfo(Call1, Call2)\n");

  if ((TI.getTaskFor(Call1->getParent()) !=
       TI.getTaskFor(Call2->getParent())) &&
      hasDRFParallelism(TI, Call1, Call2))
    return ModRefInfo::NoModRef;

  return AAResultBase::getModRefInfo(Call1, Call2, AAQI);
}

AnalysisKey DRFAA::Key;

DRFAAResult DRFAA::run(Function &F, FunctionAnalysisManager &AM) {
  return DRFAAResult(AM.getResult<TaskAnalysis>(F), AM.getResult<BasicAA>(F),
                     AM.getResult<ScalarEvolutionAnalysis>(F),
                     AM.getResult<TargetLibraryAnalysis>(F));
}

char DRFAAWrapperPass::ID = 0;
INITIALIZE_PASS_BEGIN(DRFAAWrapperPass, "drf-aa", "DRF-based Alias Analysis",
                      false, true)
INITIALIZE_PASS_DEPENDENCY(BasicAAWrapperPass)
INITIALIZE_PASS_DEPENDENCY(ScalarEvolutionWrapperPass)
INITIALIZE_PASS_DEPENDENCY(TaskInfoWrapperPass)
INITIALIZE_PASS_DEPENDENCY(TargetLibraryInfoWrapperPass)
INITIALIZE_PASS_END(DRFAAWrapperPass, "drf-aa", "DRF-based Alias Analysis",
                    false, true)

FunctionPass *llvm::createDRFAAWrapperPass() { return new DRFAAWrapperPass(); }

DRFAAWrapperPass::DRFAAWrapperPass() : FunctionPass(ID) {
  initializeDRFAAWrapperPassPass(*PassRegistry::getPassRegistry());
}

bool DRFAAWrapperPass::runOnFunction(Function &F) {
  Result.reset(
      new DRFAAResult(getAnalysis<TaskInfoWrapperPass>().getTaskInfo(),
                      getAnalysis<BasicAAWrapperPass>().getResult(),
                      getAnalysis<ScalarEvolutionWrapperPass>().getSE(),
                      getAnalysis<TargetLibraryInfoWrapperPass>().getTLI(F)));
  return false;
}

void DRFAAWrapperPass::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequired<BasicAAWrapperPass>();
  AU.addRequired<ScalarEvolutionWrapperPass>();
  AU.addRequired<TaskInfoWrapperPass>();
  AU.addRequired<TargetLibraryInfoWrapperPass>();
}
