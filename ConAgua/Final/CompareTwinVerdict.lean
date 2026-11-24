module

public import ConAgua.Final.TwinVerdict
public import ConAgua.Final.CompareTwin
public import ConRon.Arena.Main

@[expose] public section

/-!
# The twin's compared run failing: what a reject or a decline of `--compare` claims

`twinCompareRun` is the compared run's stages (`CmpStages`, `Final/CompareTwin.lean`) as one twin
computation that ends in a verdict, in the order of con-ron's `compare_json` (`compareJsonTail`,
`ConRon/Arena/Main.lean`) with both check phases' jobs taken out: the reserved-name pins, the
built-in prelude, the challenge's parse, the solution's, the solution's preparation, the pins, the
solution's stream index, the challenge's preparation, its side records, its stream index.

* `TwinCompareStagesFail bC bS c`: at some pin list, `twinCompareRun` fails with an error of class
  `c` (`twinCls`: `1` reject, `2` decline): a stage fails.
* `TwinCompareVerdict bC bS c` (the sequential run): a stage fails, or after every stage the
  solution's jobs in order fail from `sI.worker`, or they accept and the challenge's jobs in order
  fail with the solution, continuing on that worker.
* `TwinCompareVerdictPooled bC bS c` (`--jobs`): a stage fails, or some worker's list of the
  solution's jobs fails from `sI.worker`, or the solution's jobs are accepted by workers covering
  them and some worker fails on its list of the challenge's jobs after its solution list.

The constructors `TwinCompareStagesFail.prelude`, `.frontC`, `.frontS` build a stage failure from
the stage that failed and the stages before it, which ran ok.
-/

namespace ConAgua.Final

open ConLeche ConRon.Arena ConRon.Arena.Frontend L.Arena

/-- **The twin's compared run's stages as one computation** (con-ron's `compare_json` after its
argument checks, `compareJsonTail`, without the jobs): the stages `CmpStages` lists. -/
def twinCompareRun (pins : List NatOpPinSet) (bC bS : ByteArray) :
    AM (Except (ConRon.Arena.CheckError × Nat) Unit) :=
  internReservedPins >>= fun _ =>
  thenV builtinPreludeE fun pre =>
  thenV (parseChunks [bC]) fun rC =>
  thenV (parseChunks [bS]) fun rS =>
  preparePrelude pre rS.decls >>= fun dsS =>
  internAllPins pins maxNatSizeDefault >>= fun _ =>
  thenV (buildIndex dsS) fun _ =>
  preparePrelude pre rC.decls >>= fun dsC =>
  sideRecordsGo [] dsC.toList >>= fun recsC =>
  thenV (buildIndex recsC.toArray) fun _ =>
  pure (.ok ())

/-- **A stage of the twin's comparison of the challenge `bC` with the solution `bS` fails** with
an error of class `c` (`1` reject, `2` decline): at some pin list, its stages from the start state
fail. -/
def TwinCompareStagesFail (bC bS : ByteArray) (c : L.Word) : Prop :=
  ∃ pins, TwinFailsV (twinCompareRun pins bC bS) (AState.init EStore.empty) c

/-- **The sequential run rejects or declines**: a stage fails (`TwinCompareStagesFail`), or after
every stage the solution's jobs in order fail from `sI.worker`, or they accept (ending in `sJ`)
and the challenge's jobs in order fail from `sJ` with the solution, with an error of class `c`. -/
def TwinCompareVerdict (bC bS : ByteArray) (c : L.Word) : Prop :=
  TwinCompareStagesFail bC bS c ∨
  (∃ (pins : List NatOpPinSet) (ipins : List INatOpPinSet) (dsS : Array IDeclaration)
    (recsC : List IDeclaration) (IS IC : IStreamIndex) (sI : AState),
    CmpStages bC bS pins ipins dsS recsC IS IC sI ∧
    TwinFailsV (checkJobList .verified ipins none IS dsS (List.range dsS.size)) sI.worker c) ∨
  (∃ (pins : List NatOpPinSet) (ipins : List INatOpPinSet) (dsS : Array IDeclaration)
    (recsC : List IDeclaration) (IS IC : IStreamIndex) (sI sJ : AState),
    CmpStages bC bS pins ipins dsS recsC IS IC sI ∧
    checkJobList .verified ipins none IS dsS (List.range dsS.size) sI.worker = .ok (.ok (), sJ) ∧
    TwinFailsV (checkJobList .verified ipins (some (solutionOf IS recsC)) IC recsC.toArray
      (List.range recsC.toArray.size)) sJ c)

/-- **The threaded run rejects or declines**: a stage fails (`TwinCompareStagesFail`), or after
every stage some worker's list of the solution's jobs fails from `sI.worker`, or the solution's
jobs are accepted by workers covering them and some worker, after its solution list (accepted from
`sI.worker`, ending in `w`), fails on its list of the challenge's jobs from `w` with the solution,
with an error of class `c`. -/
def TwinCompareVerdictPooled (bC bS : ByteArray) (c : L.Word) : Prop :=
  TwinCompareStagesFail bC bS c ∨
  (∃ (pins : List NatOpPinSet) (ipins : List INatOpPinSet) (dsS : Array IDeclaration)
    (recsC : List IDeclaration) (IS IC : IStreamIndex) (sI : AState) (l : List Nat),
    CmpStages bC bS pins ipins dsS recsC IS IC sI ∧ (∀ t ∈ l, t < dsS.size) ∧
    TwinFailsV (checkJobList .verified ipins none IS dsS l) sI.worker c) ∨
  (∃ (pins : List NatOpPinSet) (ipins : List INatOpPinSet) (dsS : Array IDeclaration)
    (recsC : List IDeclaration) (IS IC : IStreamIndex) (sI w : AState) (lS lC : List Nat),
    CmpStages bC bS pins ipins dsS recsC IS IC sI ∧ PoolJobs .verified ipins none IS dsS sI ∧
    (∀ t ∈ lS, t < dsS.size) ∧ (∀ t ∈ lC, t < recsC.length) ∧
    checkJobList .verified ipins none IS dsS lS sI.worker = .ok (.ok (), w) ∧
    TwinFailsV (checkJobList .verified ipins (some (solutionOf IS recsC)) IC recsC.toArray lC)
      w c)

/-- The sequential run's verdict is the threaded one's with one worker. -/
theorem TwinCompareVerdict.pooled {bC bS : ByteArray} {c : L.Word}
    (h : TwinCompareVerdict bC bS c) : TwinCompareVerdictPooled bC bS c := by
  rcases h with h | ⟨pins, ipins, dsS, recsC, IS, IC, sI, hS, hF⟩ |
    ⟨pins, ipins, dsS, recsC, IS, IC, sI, sJ, hS, hJ, hF⟩
  · exact .inl h
  · exact .inr (.inl ⟨pins, ipins, dsS, recsC, IS, IC, sI, _, hS, fun t ht => List.mem_range.mp ht, hF⟩)
  · exact .inr (.inr ⟨pins, ipins, dsS, recsC, IS, IC, sI, sJ, _, _, hS, PoolJobs.of_seq hJ,
      fun t ht => List.mem_range.mp ht, fun t ht => by simpa using List.mem_range.mp ht, hJ, hF⟩)

/-! ## From the stage that failed -/

section stages
variable {bC bS : ByteArray} {c : L.Word}

/-- **The built-in prelude failed.** -/
theorem TwinCompareStagesFail.prelude {sA : AState}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (h : TwinFailsV builtinPreludeE sA c) : TwinCompareStagesFail bC bS c :=
  ⟨[], TwinFailsV.bind_ok (v := ()) hA (TwinFailsV.of_thenV h)⟩

/-- **The challenge's parse failed.** -/
theorem TwinCompareStagesFail.frontC {sA sB : AState} {pre : PreludeIx}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE sA = .ok (.ok pre, sB))
    (h : TwinFailsV (parseChunks [bC]) sB c) : TwinCompareStagesFail bC bS c :=
  ⟨[], TwinFailsV.bind_ok (v := ()) hA (TwinFailsV.of_thenV_ok hB (TwinFailsV.of_thenV h))⟩

/-- **The solution's parse failed**, after the challenge's. -/
theorem TwinCompareStagesFail.frontS {sA sB sC : AState} {pre : PreludeIx} {rC : ParseResultD}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE sA = .ok (.ok pre, sB))
    (hC : parseChunks [bC] sB = .ok (.ok rC, sC))
    (h : TwinFailsV (parseChunks [bS]) sC c) : TwinCompareStagesFail bC bS c :=
  ⟨[], TwinFailsV.bind_ok (v := ()) hA (TwinFailsV.of_thenV_ok hB (TwinFailsV.of_thenV_ok hC
    (TwinFailsV.of_thenV h)))⟩

end stages

end ConAgua.Final
