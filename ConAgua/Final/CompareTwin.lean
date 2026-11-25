module

public import ConRon.Bridge.Compare.Stages
public import ConRon.Arena.Justify
public import ConRon.Arena.Pooled
public import ConRon.Arena.Frontend.Prelude
public import ConRon.Arena.Checker

@[expose] public section

/-!
# The twin's compared run accepting, from the start state

con-ron's `--compare -- C S` on two lean4export files (its `driver/compare_json.rs`, its capstones
`model_exists_compare` and `no_False_compare`) at the twin's level, as `Final/Twin.lean` states the
flat run. The x64 checker freezes ONE store image for both check phases: the solution's jobs and
the challenge's jobs both start from the state after the challenge's stream index (`sI`), the
solution's with its index `IS`, the challenge's with `IC` and the solution `solutionOf IS recsC`.

* `CmpStages bC bS pins ipins dsS recsC IS IC sI`: the stages from the twin's start state up to the
  challenge's index: the reserved pins, the prelude, both parses into the one store, the
  solution's preparation, the pins, its index, the challenge's preparation from that state, its
  side records (each hole the axiom of its statement), its index ending in `sI`.
* `TwinComparesAccepts bC bS` (the sequential run): after the stages, one worker runs the
  solution's jobs in order from `sI.worker`, then the challenge's with the solution, continuing.
* `PoolJobs`, `PoolJobs2`, `TwinComparesAcceptsPooled bC bS` (`--jobs`): workers each run some of
  the solution's jobs from `sI.worker` and then, continuing, some of the challenge's.
* The model and no-`False` theorems: `Final/CompareTwinSeq.lean`, `Final/CompareTwinThr.lean`.
-/

namespace ConAgua.Final

open ConLeche ConRon.Arena ConRon.Arena.Frontend
open ConRon.Bridge ConRon.Bridge.Frontend

/-- **A pool of jobs from one state**: job lists covering every record position, each
increasing, each accepted from `s.worker` (con-ron's `PooledAccepts` after its index build). -/
def PoolJobs (mode : CheckMode) (pins : List INatOpPinSet) (J : Option ISolution)
    (I : IStreamIndex) (ds : Array IDeclaration) (s : AState) : Prop :=
  ∃ (parts : List (List Nat)),
    (∀ t < ds.size, ∃ w ∈ parts, t ∈ w) ∧ (∀ w ∈ parts, ∀ t ∈ w, t < ds.size) ∧
    (∀ w ∈ parts, w.Pairwise (· < ·)) ∧
    (∀ w ∈ parts, ∃ s'', checkJobList mode pins J I ds w s.worker = .ok (.ok (), s''))

/-- One worker in order is a pool. -/
theorem PoolJobs.of_seq {mode : CheckMode} {pins : List INatOpPinSet} {J : Option ISolution}
    {I : IStreamIndex} {ds : Array IDeclaration} {s s'' : AState}
    (h : checkJobList mode pins J I ds (List.range ds.size) s.worker = .ok (.ok (), s'')) :
    PoolJobs mode pins J I ds s := by
  refine ⟨[List.range ds.size], fun t ht => ⟨_, List.mem_singleton_self _, List.mem_range.mpr ht⟩,
    fun w hw t ht => ?_, fun w hw => ?_, fun w hw => ?_⟩
  · rw [List.mem_singleton] at hw; subst hw; exact List.mem_range.mp ht
  · rw [List.mem_singleton] at hw; subst hw; exact List.pairwise_lt_range
  · rw [List.mem_singleton] at hw; subst hw; exact ⟨s'', h⟩

/-- **The stages of the compared run up to the challenge's index**, at a pin list: what both
phases' jobs start from (`sI`, with the solution's index `IS`, its records `dsS`, the challenge's
index `IC` and records `recsC`). -/
def CmpStages (bC bS : ByteArray) (pins : List NatOpPinSet) (ipins : List INatOpPinSet)
    (dsS : Array IDeclaration) (recsC : List IDeclaration) (IS IC : IStreamIndex) (sI : AState) :
    Prop :=
  ∃ (sA sB sC sC' sD sE sF sG sH : AState) (pre : PreludeIx) (rC rS : ParseResultD)
    (dsC : Array IDeclaration),
    internReservedPins (AState.init EStore.empty) = .ok ((), sA) ∧
    builtinPreludeE sA = .ok (.ok pre, sB) ∧
    parseChunks [bC] sB = .ok (.ok rC, sC) ∧
    parseChunks [bS] sC = .ok (.ok rS, sC') ∧
    preparePrelude pre rS.decls sC' = .ok (dsS, sD) ∧
    internAllPins pins maxNatSizeDefault sD = .ok (ipins, sE) ∧
    buildIndex dsS sE = .ok (.ok IS, sF) ∧
    preparePrelude pre rC.decls sF = .ok (dsC, sG) ∧
    sideRecordsGo [] dsC.toList sG = .ok (recsC, sH) ∧
    buildIndex recsC.toArray sH = .ok (.ok IC, sI)

/-- **The twin accepts the comparison as the sequential x64 run does**: the stages up to the
challenge's index (ending in `sI`), then one worker running the solution's jobs in order from
`sI.worker` (ending in `sJ`), then the challenge's jobs in order with the solution, continuing on
that worker (from `sJ`). -/
def TwinComparesAccepts (bC bS : ByteArray) : Prop :=
  ∃ (pins : List NatOpPinSet) (ipins : List INatOpPinSet) (dsS : Array IDeclaration)
    (recsC : List IDeclaration) (IS IC : IStreamIndex) (sI sJ sK : AState),
    CmpStages bC bS pins ipins dsS recsC IS IC sI ∧
    checkJobList .verified ipins none IS dsS (List.range dsS.size) sI.worker = .ok (.ok (), sJ) ∧
    checkJobList .verified ipins (some (solutionOf IS recsC)) IC recsC.toArray
      (List.range recsC.toArray.size) sJ = .ok (.ok (), sK)

/-- **Both phases' pools, each worker continuing** (`--jobs`): job-list pairs, one per worker:
the first lists cover the solution's positions, the second the challenge's, each list increasing,
and each worker runs its solution list from `s.worker` (no solution) and then, from the state that
left, its challenge list with the solution `J`. -/
def PoolJobs2 (pins : List INatOpPinSet) (J : ISolution) (IS IC : IStreamIndex)
    (dsS dsC : Array IDeclaration) (s : AState) : Prop :=
  ∃ (parts : List (List Nat × List Nat)),
    (∀ t < dsS.size, ∃ q ∈ parts, t ∈ q.1) ∧ (∀ t < dsC.size, ∃ q ∈ parts, t ∈ q.2) ∧
    (∀ q ∈ parts, (∀ t ∈ q.1, t < dsS.size) ∧ (∀ t ∈ q.2, t < dsC.size)) ∧
    (∀ q ∈ parts, q.1.Pairwise (· < ·) ∧ q.2.Pairwise (· < ·)) ∧
    (∀ q ∈ parts, ∃ w w', checkJobList .verified pins none IS dsS q.1 s.worker = .ok (.ok (), w) ∧
      checkJobList .verified pins (some J) IC dsC q.2 w = .ok (.ok (), w'))

/-- **The twin accepts the comparison as the threaded x64 run does**: the stages up to the
challenge's index (ending in `sI`), then workers each running some of the solution's jobs from
`sI.worker` and then, continuing, some of the challenge's with the solution (`PoolJobs2`). -/
def TwinComparesAcceptsPooled (bC bS : ByteArray) : Prop :=
  ∃ (pins : List NatOpPinSet) (ipins : List INatOpPinSet) (dsS : Array IDeclaration)
    (recsC : List IDeclaration) (IS IC : IStreamIndex) (sI : AState),
    CmpStages bC bS pins ipins dsS recsC IS IC sI ∧
    PoolJobs2 ipins (solutionOf IS recsC) IS IC dsS recsC.toArray sI

/-- The sequential run is the threaded one with one worker. -/
theorem TwinComparesAccepts.pooled {bC bS : ByteArray} (h : TwinComparesAccepts bC bS) :
    TwinComparesAcceptsPooled bC bS := by
  obtain ⟨pins, ipins, dsS, recsC, IS, IC, sI, sJ, sK, hS, hJS, hJC⟩ := h
  refine ⟨pins, ipins, dsS, recsC, IS, IC, sI, hS, [(List.range dsS.size, List.range recsC.toArray.size)],
    fun t ht => ⟨_, List.mem_singleton_self _, List.mem_range.mpr ht⟩,
    fun t ht => ⟨_, List.mem_singleton_self _, List.mem_range.mpr ht⟩, fun q hq => ?_, fun q hq => ?_,
    fun q hq => ?_⟩
  all_goals rw [List.mem_singleton] at hq; subst hq
  · exact ⟨fun t ht => List.mem_range.mp ht, fun t ht => List.mem_range.mp ht⟩
  · exact ⟨List.pairwise_lt_range, List.pairwise_lt_range⟩
  · exact ⟨sJ, sK, hJS, hJC⟩

end ConAgua.Final
