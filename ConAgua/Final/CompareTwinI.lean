module

public import ConAgua.Final.CompareTwin
public import ConAgua.Final.CompareTwinVerdict
import ConRon.Bridge.Specs
import ConRon.Bridge.Inductives.Decl
import ConLeche.Model.OfEnvModelM
import ConLeche.Verify.Cached.PureRun
import ConRon.Bridge.Checker.Install
import ConRon.Bridge.Checker.Index
import ConRon.Bridge.Checker.Pool
import ConRon.Bridge.Checker.Pooled
import ConLeche.Verify.Driver.Reach
import ConLeche.Verify.Frontend.FileFalse
import ConLeche.Verify.Frontend.Prepare

@[expose] public section

/-!
# The twin's compared run with both check phases from one state (lane compare2, design (i))

The x64 checker freezes ONE store image for both check phases: the solution's jobs and the
challenge's jobs both start from the state after the challenge's stream index (`sI`), the
solution's with its index `IS`, the challenge's with `IC` and the solution `solutionOf IS recsC`.

* `PoolJobs mode pins J I ds s`: con-ron's pool (`PooledAccepts`) without the index build: a family
  of job lists covering every record position, each increasing, each accepted from `s.worker`.
* `TwinComparesAcceptsI bC bS`: the stages, both indices, then both phases' jobs in order on
  `sI.worker` (one worker each). `TwinComparesAcceptsPooledI`: the same with `PoolJobs`.
* `twinComparesAcceptsPooledI_model`, `_no_False`: con-ron's `stagesC_model` re-proved with the
  solution's fold at `sI` (`pooled_fold_records` is generic in the jobs' start state; its
  hypotheses at `sI` come by `Ext`/`PExt` monotonicity from the solution's index state).
-/

namespace ConAgua.Final

open ConLeche ConRon.Arena ConRon.Arena.Frontend
open ConRon.Bridge ConRon.Bridge.Frontend

universe w

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

/-- **The twin accepts the comparison, both check phases from the challenge's index state**: the
stages (reserved pins, prelude, both parses, the solution's preparation, the pins, its index, the
challenge's preparation from that state, its side records, its index ending in `sI`), then the
solution's jobs (no solution) and the challenge's (with the solution) in order on `sI.worker`. -/
def TwinComparesAcceptsI (bC bS : ByteArray) : Prop :=
  ∃ (pins : List NatOpPinSet) (sA sB sC sC' sD sE sF sG sH sI sJ sK : AState) (pre : PreludeIx)
    (rC rS : ParseResultD) (dsS dsC : Array IDeclaration) (recsC : List IDeclaration)
    (ipins : List INatOpPinSet) (IS IC : IStreamIndex),
    internReservedPins (AState.init EStore.empty) = .ok ((), sA) ∧
    builtinPreludeE sA = .ok (.ok pre, sB) ∧
    parseChunks [bC] sB = .ok (.ok rC, sC) ∧
    parseChunks [bS] sC = .ok (.ok rS, sC') ∧
    preparePrelude pre rS.decls sC' = .ok (dsS, sD) ∧
    internAllPins pins maxNatSizeDefault sD = .ok (ipins, sE) ∧
    buildIndex dsS sE = .ok (.ok IS, sF) ∧
    preparePrelude pre rC.decls sF = .ok (dsC, sG) ∧
    sideRecordsGo [] dsC.toList sG = .ok (recsC, sH) ∧
    buildIndex recsC.toArray sH = .ok (.ok IC, sI) ∧
    checkJobList .verified ipins none IS dsS (List.range dsS.size) sI.worker = .ok (.ok (), sJ) ∧
    checkJobList .verified ipins (some (solutionOf IS recsC)) IC recsC.toArray
      (List.range recsC.toArray.size) sI.worker = .ok (.ok (), sK)

/-- **The twin accepts the comparison with both check phases as pools from the challenge's index
state** (`--jobs`). -/
def TwinComparesAcceptsPooledI (bC bS : ByteArray) : Prop :=
  ∃ (pins : List NatOpPinSet) (sA sB sC sC' sD sE sF sG sH sI : AState) (pre : PreludeIx)
    (rC rS : ParseResultD) (dsS dsC : Array IDeclaration) (recsC : List IDeclaration)
    (ipins : List INatOpPinSet) (IS IC : IStreamIndex),
    internReservedPins (AState.init EStore.empty) = .ok ((), sA) ∧
    builtinPreludeE sA = .ok (.ok pre, sB) ∧
    parseChunks [bC] sB = .ok (.ok rC, sC) ∧
    parseChunks [bS] sC = .ok (.ok rS, sC') ∧
    preparePrelude pre rS.decls sC' = .ok (dsS, sD) ∧
    internAllPins pins maxNatSizeDefault sD = .ok (ipins, sE) ∧
    buildIndex dsS sE = .ok (.ok IS, sF) ∧
    preparePrelude pre rC.decls sF = .ok (dsC, sG) ∧
    sideRecordsGo [] dsC.toList sG = .ok (recsC, sH) ∧
    buildIndex recsC.toArray sH = .ok (.ok IC, sI) ∧
    PoolJobs .verified ipins none IS dsS sI ∧
    PoolJobs .verified ipins (some (solutionOf IS recsC)) IC recsC.toArray sI

theorem TwinComparesAcceptsI.pooled {bC bS : ByteArray} (h : TwinComparesAcceptsI bC bS) :
    TwinComparesAcceptsPooledI bC bS := by
  obtain ⟨pins, sA, sB, sC, sC', sD, sE, sF, sG, sH, sI, sJ, sK, pre, rC, rS, dsS, dsC, recsC, ipins,
    IS, IC, hA, hB, hC, hCS, hDS, hE, hIS, hDC, hside, hIC, hJS, hJC⟩ := h
  exact ⟨pins, sA, sB, sC, sC', sD, sE, sF, sG, sH, sI, pre, rC, rS, dsS, dsC, recsC, ipins, IS, IC,
    hA, hB, hC, hCS, hDS, hE, hIS, hDC, hside, hIC, PoolJobs.of_seq hJS, PoolJobs.of_seq hJC⟩

/-- con-ron: proof/ConRon/Bridge/Compare/Stages.lean stagesC_model, with the solution's fold at the
challenge's index state — **the challenge of a comparison accepted from one state has a model**. -/
theorem stagesCI_model (V : Type w) [ConLeche.SetTheory V]
    (hk : CoreSpec ConRon.Arena.checkFuel) (hind : IndSpec)
    {bC bS : ByteArray} (h : TwinComparesAcceptsPooledI bC bS) :
    ∃ rcC preC dsP, ConLeche.Frontend.parseChunks [bC] = .ok rcC ∧
      dsP = (ConLeche.Frontend.preparePrelude preC rcC.decls).toList.map
        ConLeche.Cached.sideRecord ∧
      Nonempty (ConLeche.Model.EnvModelM V (ConLeche.streamEnv dsP)) := by
  obtain ⟨pins, sA, sB, sC, sC', sD, sE, sF, sG, sH, sI, pre, rC, rS, dsS, dsC, recsC, ipins, IS, IC,
    hA, hB, hC, hCS, hDS, hE, hidxS, hDC, hside, hidxC, ⟨partsS, hcovS, -, hincS, haccS⟩, hFC⟩ := h
  obtain ⟨hoff, hst, hpp, hipins, hpps, hpd, hpersPre, hpersRC, rcC, rcS, preC, hclC, -,
    hrelPre, hrelC, hdenS⟩ := stagesC_frame hA hB hC hCS hDS hE
  obtain ⟨hstF, hxF, hpF, hoffF, hIS, hpIS⟩ :=
    buildIndex_run constsSpec tablesSpec hst hpp hoff hpd hdenS hidxS
  -- the challenge's preparation and its records
  obtain ⟨hstepG, hpersC, hclPrepC⟩ :=
    preparePrelude_run (preC := preC) hstF.state hoffF (hstF.pins)
      (denoteDeclArray_ext hxF hrelPre) hpersPre (denoteDeclArray_ext hxF hrelC) hpersRC hDC
  have hdenC : denoteDecls sG.store dsC.toList =
      some (ConLeche.Frontend.preparePrelude preC rcC.decls).toList :=
    denoteDeclArray_iff.mp hclPrepC
  obtain ⟨rfl, hdenR, hpersR⟩ := sideRecordsGo_run hstepG.ok (hstF.pins.mono hstepG.ext hstepG.pins)
    dsC.toList [] recsC _ [] rfl hdenC hside
  simp only [List.nil_append] at hdenR
  have hpR : ∀ x ∈ recsC, PersDecl x :=
    hpersR (fun _ h => nomatch h) (fun x hx => hpersC x (by simpa using hx))
  have hstG : DriverOK sG := DriverOK.of_check
    (hstF.monoF hstepG.ok hstepG.ext hstepG.cframe hstepG.pins) hstepG.pins
  have hxEG : Ext sE.store sG.store := hxF.trans hstepG.ext
  have hoffG : sG.store.scratchOn = false := by rw [hstepG.scratch]; exact hoffF
  have hppG : PersPins sG := hpp.mono (by rw [hstepG.pins, hpF])
  -- the challenge's index: the state both phases' jobs start from
  obtain ⟨hstI, hxI, hpI, -, -, -⟩ :=
    buildIndex_run constsSpec tablesSpec hstG hppG hoffG (by simpa using hpR) (by simpa using hdenR)
      hidxC
  have hxEI : Ext sE.store sI.store := hxEG.trans hxI
  -- the solution: the pure fold accepts it, from `sI`
  obtain ⟨hlen, hget⟩ := denoteDecls_getElem hdenS
  obtain ⟨F, hpure⟩ := pooled_fold_records (recordSpec hk hind) (kernelPushes pins) hpps hstI.state
    (hstI.pins) (hppG.mono hpI) (PinsDenote.mono hxEI ipins pins hipins) hpd (by simpa using hlen)
    (fun i hi => by
      obtain ⟨hi', h⟩ := hget i (by simpa using hi)
      exact ⟨hi', Frontend.denoteDecl_ext (hxF.trans (hstepG.ext.trans hxI)) (by simpa using h)⟩)
    (hIS.pmono hpIS (PExt.of_ext (hstepG.ext.trans hxI))) hpIS partsS hcovS hincS haccS
  -- the challenge's check phase
  obtain ⟨partsC, hcovC, hbndC, hincC, haccC⟩ := hFC
  have hrun := Arena.pooledAcceptsJ_bridge (pinsP := pins) (dsS :=
      (ConLeche.Frontend.preparePrelude preC rcS.decls).toList)
    (matesU := ConLeche.Cached.recordMates
      ((ConLeche.Frontend.preparePrelude preC rcC.decls).toList.map
        ConLeche.Cached.sideRecord).toArray)
    hk hind hstG hoffG hppG hpps (PinsDenote.mono hxEG ipins pins hipins)
    (by simpa using hpR) (by simpa using hdenR)
    (hIS.pmono hpIS (PExt.of_ext hstepG.ext)) hpIS (pure_nodup hpure)
    (solutionOf_mates hstepG.ok.wf hdenR hpR) ⟨partsC, hidxC, hcovC, hbndC, hincC, haccC⟩
  exact ⟨rcC, preC, _, hclC, rfl, Compare.mixed_model (pinsP := pins) V hpure hrun⟩

/-- **The challenge of a comparison accepted from one state has a model**: con-leche's parser
reads the challenge, and its prepared records, each hole the axiom of its statement, have a model
in every set theory. Nothing is concluded about the solution. -/
theorem twinComparesAcceptsPooledI_model (V : Type w) [SetTheory V] {bC bS : ByteArray}
    (h : TwinComparesAcceptsPooledI bC bS) :
    ∃ (rcC : ConLeche.Frontend.ParseResultD) (preC : ConLeche.Frontend.PreludeIx),
      ConLeche.Frontend.parseChunks [bC] = .ok rcC ∧
      Nonempty (Model V (ConLeche.streamEnv
        ((ConLeche.Frontend.preparePrelude preC rcC.decls).toList.map ConLeche.Cached.sideRecord))) := by
  obtain ⟨rcC, preC, dsP, hclC, rfl, ⟨hmod⟩⟩ :=
    stagesCI_model V CoreSpec.of_core ConRon.Bridge.Inductives.indSpec_of_bridge h
  exact ⟨rcC, preC, hclC, ⟨ConLeche.Model.Model.ofEnvModelM hmod⟩⟩

/-- **No `False` in the challenge of a comparison accepted from one state**: a challenge file that
declares a theorem of type `False` is not accepted, whatever the solution. -/
theorem twinComparesAcceptsPooledI_no_False (V : Type w) [SetTheory V] {bC bS : ByteArray}
    (hfalse : jsonWithTheoremFalse [bC]) (h : TwinComparesAcceptsPooledI bC bS) : False := by
  obtain ⟨rcC, preC, dsP, hclC, rfl, ⟨mp⟩⟩ :=
    stagesCI_model V CoreSpec.of_core ConRon.Bridge.Inductives.indSpec_of_bridge h
  obtain ⟨cv, vl, hty, hmem⟩ := ConLeche.Frontend.parseChunks_jsonWithTheoremFalse hfalse hclC
  have hmem' : Declaration.thmDecl cv vl ∈
      (ConLeche.Frontend.preparePrelude preC rcC.decls).toList := by
    simpa using ConLeche.Frontend.mem_preparePrelude (pre := preC) hmem
  -- the checked record installs a constant of the theorem's type (as con-ron's stagesC_no_False)
  have hc : ∃ c ∈ ConLeche.declConstants (ConLeche.Cached.sideRecord (.thmDecl cv vl)),
      c.toConstantVal.type = .const falseName [] := by
    simp only [ConLeche.Cached.sideRecord]
    split
    · next hb =>
      have hbi : ConLeche.Cached.builtinAxiomName cv.name = false := by
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hb; exact hb.1
      have hq : cv.name ≠ quotSoundName := fun h => by
        simp [ConLeche.Cached.builtinAxiomName, h] at hbi
      have hs : cv.name ≠ sorryAxName := fun h => by
        simp [ConLeche.Cached.builtinAxiomName, h] at hbi
      exact ⟨.axiomInfo cv, by simp [ConLeche.declConstants, hq, hs], hty⟩
    · exact ⟨.thmInfo cv, by simp [ConLeche.declConstants], hty⟩
  obtain ⟨c, hcd, hcty⟩ := hc
  have hcs : c ∈ (ConLeche.streamEnv ((ConLeche.Frontend.preparePrelude preC
      rcC.decls).toList.map ConLeche.Cached.sideRecord)).consts :=
    (ConLeche.Driver.mem_streamEnv_consts _ _).2
      (.inl ⟨_, List.mem_map_of_mem hmem', hcd⟩)
  exact ConLeche.Model.no_constant_of_False mp c hcs hcty

/-- info: 'ConAgua.Final.twinComparesAcceptsPooledI_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms twinComparesAcceptsPooledI_model

/-- info: 'ConAgua.Final.twinComparesAcceptsPooledI_no_False' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms twinComparesAcceptsPooledI_no_False

/-! ## Failing from one state -/

/-- **The stages of `TwinComparesAcceptsI` up to the challenge's index**, at a pin list: what both
phases' jobs start from (`sI`, with the solution's index `IS`, its records `dsS`, the challenge's
index `IC` and records `recsC`). -/
def CmpStagesI (bC bS : ByteArray) (pins : List NatOpPinSet) (ipins : List INatOpPinSet)
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

/-- **The twin rejects or declines the comparison, both phases' jobs from one state**: a stage
fails (`TwinCompareVerdict`, unchanged), or after every stage the solution's jobs in order fail
from `sI.worker`, or the solution's jobs accept there and the challenge's jobs in order fail from
`sI.worker` with the solution, with an error of class `c`. -/
def TwinCompareVerdictI (bC bS : ByteArray) (c : L.Word) : Prop :=
  TwinCompareVerdict bC bS c ∨
  (∃ (pins : List NatOpPinSet) (ipins : List INatOpPinSet) (dsS : Array IDeclaration) (recsC : List IDeclaration) (IS IC : IStreamIndex) (sI : AState), CmpStagesI bC bS pins ipins dsS recsC IS IC sI ∧
    L.Arena.TwinFailsV (checkJobList .verified ipins none IS dsS (List.range dsS.size)) sI.worker c) ∨
  (∃ (pins : List NatOpPinSet) (ipins : List INatOpPinSet) (dsS : Array IDeclaration) (recsC : List IDeclaration) (IS IC : IStreamIndex) (sI : AState) (sJ : AState), CmpStagesI bC bS pins ipins dsS recsC IS IC sI ∧
    checkJobList .verified ipins none IS dsS (List.range dsS.size) sI.worker = .ok (.ok (), sJ) ∧
    L.Arena.TwinFailsV (checkJobList .verified ipins (some (solutionOf IS recsC)) IC recsC.toArray
      (List.range recsC.toArray.size)) sI.worker c)

/-- **The pooled comparison rejects or declines, both phases' jobs from one state**: a stage fails
(`TwinCompareVerdict`), or after every stage some worker's list of the solution's jobs fails from
`sI.worker`, or the solution's pool accepts from `sI` and some worker's list of the challenge's
jobs fails from `sI.worker` with the solution, with an error of class `c`. -/
def TwinCompareVerdictPooledI (bC bS : ByteArray) (c : L.Word) : Prop :=
  TwinCompareVerdict bC bS c ∨
  (∃ (pins : List NatOpPinSet) (ipins : List INatOpPinSet) (dsS : Array IDeclaration) (recsC : List IDeclaration) (IS IC : IStreamIndex) (sI : AState) (w : List Nat), CmpStagesI bC bS pins ipins dsS recsC IS IC sI ∧
    (∀ t ∈ w, t < dsS.size) ∧
    L.Arena.TwinFailsV (checkJobList .verified ipins none IS dsS w) sI.worker c) ∨
  (∃ (pins : List NatOpPinSet) (ipins : List INatOpPinSet) (dsS : Array IDeclaration) (recsC : List IDeclaration) (IS IC : IStreamIndex) (sI : AState) (w : List Nat), CmpStagesI bC bS pins ipins dsS recsC IS IC sI ∧
    PoolJobs .verified ipins none IS dsS sI ∧ (∀ t ∈ w, t < recsC.length) ∧
    L.Arena.TwinFailsV (checkJobList .verified ipins (some (solutionOf IS recsC)) IC recsC.toArray w)
      sI.worker c)

theorem TwinCompareVerdictI.pooled {bC bS : ByteArray} {c : L.Word}
    (h : TwinCompareVerdictI bC bS c) : TwinCompareVerdictPooledI bC bS c := by
  rcases h with h | ⟨pins, ipins, dsS, recsC, IS, IC, sI, hS, hF⟩ |
    ⟨pins, ipins, dsS, recsC, IS, IC, sI, sJ, hS, hJ, hF⟩
  · exact .inl h
  · exact .inr (.inl ⟨pins, ipins, dsS, recsC, IS, IC, sI, _, hS,
      fun t ht => List.mem_range.mp ht, hF⟩)
  · exact .inr (.inr ⟨pins, ipins, dsS, recsC, IS, IC, sI, _, hS, PoolJobs.of_seq hJ,
      fun t ht => by simpa using List.mem_range.mp ht, hF⟩)

/-! ## The sequential run: the challenge's jobs continue on the solution's worker -/

/-- **The twin accepts the comparison as the sequential x64 run does**: the stages up to the
challenge's index (ending in `sI`), then one worker running the solution's jobs in order from
`sI.worker` (ending in `sJ`), then the challenge's jobs in order with the solution, continuing on
that worker (from `sJ`). -/
def TwinComparesAcceptsSeqI (bC bS : ByteArray) : Prop :=
  ∃ (pins : List NatOpPinSet) (ipins : List INatOpPinSet) (dsS : Array IDeclaration)
    (recsC : List IDeclaration) (IS IC : IStreamIndex) (sI sJ sK : AState),
    CmpStagesI bC bS pins ipins dsS recsC IS IC sI ∧
    checkJobList .verified ipins none IS dsS (List.range dsS.size) sI.worker = .ok (.ok (), sJ) ∧
    checkJobList .verified ipins (some (solutionOf IS recsC)) IC recsC.toArray
      (List.range recsC.toArray.size) sJ = .ok (.ok (), sK)

/-- **The sequential run rejects or declines**: a stage fails (`TwinCompareVerdict`), or after
every stage the solution's jobs in order fail from `sI.worker`, or they accept (ending in `sJ`)
and the challenge's jobs in order fail from `sJ` with the solution, with an error of class `c`. -/
def TwinCompareVerdictSeqI (bC bS : ByteArray) (c : L.Word) : Prop :=
  TwinCompareVerdict bC bS c ∨
  (∃ (pins : List NatOpPinSet) (ipins : List INatOpPinSet) (dsS : Array IDeclaration)
    (recsC : List IDeclaration) (IS IC : IStreamIndex) (sI : AState),
    CmpStagesI bC bS pins ipins dsS recsC IS IC sI ∧
    L.Arena.TwinFailsV (checkJobList .verified ipins none IS dsS (List.range dsS.size)) sI.worker c) ∨
  (∃ (pins : List NatOpPinSet) (ipins : List INatOpPinSet) (dsS : Array IDeclaration)
    (recsC : List IDeclaration) (IS IC : IStreamIndex) (sI sJ : AState),
    CmpStagesI bC bS pins ipins dsS recsC IS IC sI ∧
    checkJobList .verified ipins none IS dsS (List.range dsS.size) sI.worker = .ok (.ok (), sJ) ∧
    L.Arena.TwinFailsV (checkJobList .verified ipins (some (solutionOf IS recsC)) IC recsC.toArray
      (List.range recsC.toArray.size)) sJ c)

end ConAgua.Final
