//===- DataRaceFreeAliasAnalysis.h - DRF-based AA ---------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file
/// This is the interface for an alias analysis based on the assumption that
/// a Tapir program is data-race free.
///
//===----------------------------------------------------------------------===//

#ifndef LLVM_ANALYSIS_DATARACEFREEALIASANALYSIS_H
#define LLVM_ANALYSIS_DATARACEFREEALIASANALYSIS_H

#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/Pass.h"
#include "llvm/Support/CommandLine.h"
#include <cstdint>
#include <memory>

namespace llvm {

class BasicAAResult;
class Instruction;
class Loop;
class TaskInfo;
class MemoryLocation;
class ScalarEvolution;
class TargetLibraryInfo;
struct DRFAADeltaSetProofCache;

extern cl::opt<bool> EnableDRFAA;

/// Enable the experimental loop transforms that consume the DRF contract.
/// This option is deliberately separate from EnableDRFAA: alias-analysis
/// clients should not unexpectedly opt into loop restructuring.
extern cl::opt<bool> EnableDRFLoopOptimizations;

/// Experimental, bounded sibling-read proofs for ordinary accesses in a
/// straight fork/sync phase containing finite, unconditional serial loops.
bool isDRFAASiblingWitnessEnabled();

class DRFSiblingWitnessInfo {
public:
  using AccessPair = std::pair<Instruction *, Instruction *>;
  explicit DRFSiblingWitnessInfo(Function &F);
  ~DRFSiblingWitnessInfo();
  DRFSiblingWitnessInfo(const DRFSiblingWitnessInfo &) = delete;
  DRFSiblingWitnessInfo &operator=(const DRFSiblingWitnessInfo &) = delete;

  /// These pairs refer to the current IR and are intended for immediate
  /// materialization. Do not retain them across IR changes.
  ArrayRef<AccessPair> getNoAliasPairs();
  /// Only precise, phase-local pointer definitions are eligible. A fact about
  /// the guarded parallel phase is never an unconditional argument attribute.
  AliasResult alias(const MemoryLocation &A, const MemoryLocation &B,
                    const Instruction *CtxI = nullptr);

private:
  struct Impl;
  std::unique_ptr<Impl> P;
};

/// The strength of a fact licensed by the DRF contract.
///
/// NoCrossIteration is a loop-level dependence fact: the accesses may still
/// alias in the same iteration.  NoAlias is a location-level fact strong
/// enough to materialize as alias-analysis metadata.  Keeping the strengths
/// explicit prevents a loop-carried fact from accidentally becoming a
/// whole-function no-alias assertion.
enum class DRFProofKind : uint8_t {
  Unknown,
  NoCrossIteration,
  NoAlias,
};

using DRFLoopDependenceKind = DRFProofKind;

/// Return true only for ordinary, non-atomic, non-volatile loads and stores
/// whose pointer is not based on a hyperobject view.
bool isOrdinaryDRFMemoryAccess(const Instruction *I);

/// Return true when \p L is either a Tapir loop or a serial loop carrying the
/// provenance of a Tapir loop.  The latter case is important after
/// strip-mining or deliberate serialization for SIMD optimization.
bool isDRFLogicallyParallelLoop(const Loop *L, const TaskInfo *TI = nullptr);

/// Return true when a possibly-aliasing store can be ignored for a
/// loop-invariant load under the DRF contract.
///
/// This is deliberately a loop-scoped fact.  It requires a logically parallel
/// loop with at least two logical iterations, an ordinary store in the loop,
/// and an ordinary invariant-address load that executes on every iteration.
/// When \p AllowLoopInvariantGuards is true, a structurally proven
/// loop-invariant control path is also accepted. If the store aliases a
/// dynamically executed load, the store conflicts with the load in another
/// iteration and the source program has a race. Callers must only use this
/// result to resolve an uncertain (MayAlias) clobber; a proven overlap remains
/// a clobber.
///
/// In provenance-only serialized loops, alloca-rooted invariant addresses are
/// rejected because loop spawning may have rebound per-iteration task storage.
bool drfInvariantLoadClobberWouldRace(const Loop *L, const TaskInfo &TI,
                                      const Instruction *Load,
                                      const Instruction *Clobber,
                                      ScalarEvolution *SE = nullptr,
                                      bool AllowLoopInvariantGuards = false);

/// Classify a pair of accesses at one loop level under the DRF contract.
/// Calls, atomics, volatile accesses, read/read pairs, and hyperobject views
/// return Unknown.  NoCrossIteration says only that a conflicting dependence
/// cannot be carried by \p L; it says nothing about same-iteration aliasing.
DRFLoopDependenceKind classifyDRFLoopDependence(const Loop *L, TaskInfo *TI,
                                                const Instruction *A,
                                                const Instruction *B);

/// Per-function cache for the shared loop-level DRF classification.  LAA and
/// loop-nest transforms issue the same pair queries repeatedly; caching here
/// keeps the semantic test centralized and makes those repeated queries cheap.
class DRFLoopDependenceInfo {
public:
  explicit DRFLoopDependenceInfo(TaskInfo *TI = nullptr);
  DRFLoopDependenceInfo(DRFLoopDependenceInfo &&);
  DRFLoopDependenceInfo &operator=(DRFLoopDependenceInfo &&);
  ~DRFLoopDependenceInfo();

  DRFLoopDependenceInfo(const DRFLoopDependenceInfo &);
  DRFLoopDependenceInfo &operator=(const DRFLoopDependenceInfo &);

  DRFLoopDependenceKind get(const Loop *L, const Instruction *A,
                            const Instruction *B);
  bool isLogicallyParallel(const Loop *L) const;
  void clear();

private:
  struct Cache;
  TaskInfo *TI;
  std::unique_ptr<Cache> CachedResults;
};

/// Return true if aliasing between the two locations would imply a parallel
/// race under the DRF assumption. This exposes the same proof used by DRFAA's
/// AliasResult path so transforms can materialize the fact before Tapir
/// lowering loses the original access provenance.
DRFAADeltaSetProofCache *createDRFAADeltaSetProofCache();
void destroyDRFAADeltaSetProofCache(DRFAADeltaSetProofCache *Cache);

/// Classify the location-level DRF proof for an access pair.  This interface
/// returns only Unknown or NoAlias; a NoCrossIteration fact requires a
/// particular loop and is exposed by classifyDRFLoopDependence instead.
DRFProofKind
classifyDRFAliasProof(const TaskInfo &TI, const MemoryLocation &LocA,
                      const MemoryLocation &LocB, const Instruction *AddrA,
                      const Instruction *AddrB, ScalarEvolution &SE,
                      DRFAADeltaSetProofCache *DeltaSetCache);

DRFProofKind
classifyDRFAliasProof(const TaskInfo &TI, const MemoryLocation &LocA,
                      const MemoryLocation &LocB, const Instruction *AddrA,
                      const Instruction *AddrB, ScalarEvolution &SE);

bool drfAliasWouldImplyParallelRace(
    const TaskInfo &TI, const MemoryLocation &LocA, const MemoryLocation &LocB,
    const Instruction *AddrA, const Instruction *AddrB, ScalarEvolution &SE,
    DRFAADeltaSetProofCache *DeltaSetCache);

bool drfAliasWouldImplyParallelRace(
    const TaskInfo &TI, const MemoryLocation &LocA, const MemoryLocation &LocB,
    const Instruction *AddrA, const Instruction *AddrB, ScalarEvolution &SE);

/// Return true when this exact access pair can use an enclosing logically
/// parallel loop as an asymmetric race witness. Unlike the location-level AA
/// interface above, this query is scoped to \p InnerLoop: an address computed
/// opaquely inside an enclosing Tapir iteration may count as varying across
/// that iteration, while the other access must have a replicated execution
/// schedule at matching inner-loop coordinates.
///
/// This is a loop-local NoCrossIteration/no-check fact. It must not be cached
/// as a context-free NoAlias result or materialized as noalias metadata.
bool drfAliasWouldImplyRaceViaEnclosingParallelLoop(
    const Loop *InnerLoop, const TaskInfo &TI, const MemoryLocation &LocA,
    const MemoryLocation &LocB, const Instruction *AccessA,
    const Instruction *AccessB, ScalarEvolution &SE);

/// A simple alias analysis implementation that implements the assumption that
/// the Tapir program is data-race free.  This analysis uses TaskInfo to
/// determine which may-aliasing instructions may happen in parallel.  If two
/// that may alias instructions may happen in parallel and the instructions are
/// not otherwise marked atomic, then the data-race-free assumption asserts that
/// they do not alias.  To avoid turning conditional parallelism into an
/// unconditional no-alias fact, this analysis applies that rule to access
/// pairs that TaskInfo proves are definitely logically parallel. It also has an
/// experimental path for Tapir loop-carried parallelism.
class DRFAAResult : public AAResultBase {
  TaskInfo &TI;
  BasicAAResult &BAA;
  ScalarEvolution &SE;
  const TargetLibraryInfo &TLI;
  std::unique_ptr<DRFAADeltaSetProofCache> DeltaSetProofCache;
  std::unique_ptr<DRFSiblingWitnessInfo> SiblingWitnessInfo;

public:
  explicit DRFAAResult(TaskInfo &TI, BasicAAResult &BasicAA,
                       ScalarEvolution &SE, const TargetLibraryInfo &TLI);
  DRFAAResult(DRFAAResult &&Arg);
  ~DRFAAResult();

  /// Handle invalidation events in the new pass manager.
  bool invalidate(Function &Fn, const PreservedAnalyses &PA,
                  FunctionAnalysisManager::Invalidator &Inv);

  AliasResult alias(const MemoryLocation &LocA, const MemoryLocation &LocB,
                    AAQueryInfo &AAQI, const Instruction *CtxI);
  ModRefInfo getModRefInfo(const CallBase *Call, const MemoryLocation &Loc,
                           AAQueryInfo &AAQI);
  ModRefInfo getModRefInfo(const CallBase *Call1, const CallBase *Call2,
                           AAQueryInfo &AAQI);
};

/// Analysis pass providing a never-invalidated alias analysis result.
class DRFAA : public AnalysisInfoMixin<DRFAA> {
  friend AnalysisInfoMixin<DRFAA>;
  static AnalysisKey Key;

public:
  using Result = DRFAAResult;

  DRFAAResult run(Function &F, FunctionAnalysisManager &AM);
};

/// Legacy wrapper pass to provide the DRFAAResult object.
class DRFAAWrapperPass : public FunctionPass {
  std::unique_ptr<DRFAAResult> Result;

public:
  static char ID;

  DRFAAWrapperPass();

  DRFAAResult &getResult() { return *Result; }
  const DRFAAResult &getResult() const { return *Result; }

  bool runOnFunction(Function &F) override;
  void getAnalysisUsage(AnalysisUsage &AU) const override;
};

/// Creates an instance of \c DRFAAWrapperPass.
FunctionPass *createDRFAAWrapperPass();

} // end namespace llvm

#endif // LLVM_ANALYSIS_DATARACEFREEALIASANALYSIS_H
