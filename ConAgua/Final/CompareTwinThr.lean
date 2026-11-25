module

public import ConAgua.Final.CompareTwin
import ConRon.Bridge.Specs
import ConRon.Bridge.Inductives.Decl
import ConLeche.Model.OfEnvModelM
import ConLeche.Verify.Cached.PureRun
import ConRon.Bridge.Checker.Install
import ConRon.Bridge.Checker.Index
import ConRon.Bridge.Checker.Pool
import ConRon.Bridge.Checker.Pooled
import ConRon.Bridge.Compare.Pooled
import ConLeche.Verify.Driver.Reach
import ConLeche.Verify.Frontend.FileFalse
import ConLeche.Verify.Frontend.Prepare


@[expose] public section

/-!
# The threaded compared run's twin: each worker's challenge jobs from its solution jobs (lane compare2)

`TwinComparesAcceptsPooled` (`Final/CompareTwin.lean`): after the stages up to the challenge's index
build (`sI`), workers each run some of the solution's jobs from `sI.worker` and then, continuing,
some of the challenge's with the solution (`PoolJobs2`).

* `stagesCPooled_model`: con-ron's `stagesC_model` with the solution's fold by `pooled_foldP` over the
  workers' solution lists (every prefix accepted, so each worker's solution list ends in a worker's
  state of `sI`: `job_spec` along the list), and the challenge's (`pooledAcceptsJ_bridge`'s body)
  over the workers' challenge lists, each from the state its solution list ended in.
* `twinComparesAcceptsPooled_model`, `_no_False`: the challenge has a model; no `False` in it.
  The sequential ones (`Final/CompareTwinSeq.lean`) follow by `TwinComparesAccepts.pooled`.
-/

namespace ConAgua.Final

open ConLeche ConRon.Arena ConRon.Arena.Frontend
open ConRon.Bridge ConRon.Bridge.Frontend

universe w

/-- A list of jobs accepted, at its head: the head's job and the rest from its state. -/
theorem checkJobList_cons_inv {mode : CheckMode} {pins : List INatOpPinSet} {J : Option ISolution}
    {I : IStreamIndex} {ds : Array IDeclaration} {t : Nat} {rest : List Nat} {w w'' : AState}
    (h : checkJobList mode pins J I ds (t :: rest) w = .ok (.ok (), w'')) :
    ∃ (ht : t < ds.size) (w₁ : AState), recordJob mode pins J I t ds[t] w = .ok ((), w₁) ∧
      checkJobList mode pins J I ds rest w₁ = .ok (.ok (), w'') := by
  simp only [checkJobList] at h
  cases hr : runJob mode pins J I ds t w with
  | error e => rw [hr] at h; exact nomatch h
  | ok r =>
    obtain ⟨res, w₁⟩ := r
    rw [hr] at h
    cases res with
    | error e => simp at h
    | ok u =>
      simp only at h
      unfold runJob at hr
      cases hdt : ds[t]? with
      | none => rw [hdt] at hr; simp at hr
      | some dt =>
        rw [hdt] at hr
        simp only at hr
        cases hj : recordJob mode pins J I t dt w with
        | error e => rw [hj] at hr; simp at hr
        | ok q =>
          obtain ⟨u', w₁'⟩ := q
          rw [hj] at hr
          simp only [Except.ok.injEq, Prod.mk.injEq] at hr
          obtain ⟨-, rfl⟩ := hr
          obtain ⟨ht, rfl⟩ := Array.getElem?_eq_some_iff.mp hdt
          exact ⟨ht, _, by cases u'; exact hj, h⟩

/-- con-ron: proof/ConRon/Bridge/Compare/Stages.lean stagesC_model, with each worker's solution
jobs from the challenge's index state and its challenge jobs from the state they end in — **the
challenge of a comparison the twin accepts as the threads run it has a model**. -/
theorem stagesCPooled_model (V : Type w) [ConLeche.SetTheory V]
    (hk : CoreSpec ConRon.Arena.checkFuel) (hind : IndSpec)
    {bC bS : ByteArray} (h : TwinComparesAcceptsPooled bC bS) :
    ∃ rcC preC dsP, ConLeche.Frontend.parseChunks [bC] = .ok rcC ∧
      dsP = (ConLeche.Frontend.preparePrelude preC rcC.decls).toList.map
        ConLeche.Cached.sideRecord ∧
      Nonempty (ConLeche.Model.EnvModelM V (ConLeche.streamEnv dsP)) := by
  obtain ⟨pins, ipins, dsS, recsC, IS, IC, sI, hSt, parts, hcovS, hcovC, hrng, hinc, hacc⟩ := h
  obtain ⟨sA, sB, sC, sC', sD, sE, sF, sG, sH, pre, rC, rS, dsC, hA, hB, hC, hCS, hDS, hE, hidxS,
    hDC, hside, hidxC⟩ := hSt
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
  obtain ⟨hstI, hxI, hpI, -, hICd, hpIC⟩ :=
    buildIndex_run constsSpec tablesSpec hstG hppG hoffG (by simpa using hpR) (by simpa using hdenR)
      hidxC
  have hxEI : Ext sE.store sI.store := hxEG.trans hxI
  have hpinsOK : PinsOK sI := hstI.pins
  have hppI : PersPins sI := hppG.mono hpI
  have hPD : PinsDenote sI.store ipins pins := PinsDenote.mono hxEI ipins pins hipins
  -- the solution: every prefix of its records is accepted by the pure fold with distinct names
  -- (con-ron's `pooled_foldP` over the workers' solution lists), so each worker's solution list
  -- ends in a worker's state of `sI`
  obtain ⟨hlen, hget⟩ := denoteDecls_getElem hdenS
  let dsPS := (ConLeche.Frontend.preparePrelude preC rcS.decls).toList
  have hdenS' : ∀ (i : Nat) (hi : i < dsS.size), ∃ hi' : i < dsPS.length,
      Frontend.denoteDecl sI.store dsS[i] = some dsPS[i] := fun i hi => by
    obtain ⟨hi', h⟩ := hget i (by simpa using hi)
    exact ⟨by simpa [dsPS] using hi', Frontend.denoteDecl_ext hxEI (by simpa [dsPS] using h)⟩
  have hlenS : dsPS.length = dsS.size := by simpa [dsPS] using hlen
  have hISI := hIS.pmono hpIS (PExt.of_ext (hstepG.ext.trans hxI))
  have hrecS : RecordSpec ipins pins := recordSpec hk hind
  let PS : Nat → Prop := fun t => PrefixOK pins dsPS t ∧
    ((ConLeche.Cached.recsConsts (dsPS.take t)).map (·.name)).Nodup
  have hP0 : PS 0 := by
    have h0 : (ConLeche.Cached.recsConsts ([] : List Declaration)).length = 0 := by
      have := (ConLeche.Cached.buildIndex_spec (#[] : Array Declaration)).next
      simpa [ConLeche.Cached.buildIndex] using this.symm
    exact ⟨⟨0, fun _ _ => rfl⟩, by rw [List.take_zero, List.eq_nil_of_length_eq_zero h0]; exact List.nodup_nil⟩
  have hallS := pooled_foldP (Inv := WorkerOK sI) (Run := RecordRun ipins IS dsS) (N := dsS.size)
    (P := fun k => ∀ t ≤ k, PS t) (fun t ht => (Nat.le_zero.mp ht) ▸ hP0)
    (fun {k w w'} hkN hw hP hr => by
      obtain ⟨hk, hj⟩ := hr
      obtain ⟨hk', hdk⟩ := hdenS' k hk
      obtain ⟨hw', env', F, hF⟩ := job_spec hrecS hpps hpinsOK hppI hPD hpd hISI hpIS hw hk hk' hdk
        (hP k (Nat.le_refl _)).1.envWF (hP k (Nat.le_refl _)).2 hj
      refine ⟨hw', fun t ht => ?_⟩
      rcases Nat.lt_or_ge t (k + 1) with h | h
      · exact hP t (by omega)
      · obtain rfl : t = k + 1 := by omega
        exact PrefixOK.step (kernelPushes pins) hk' (hP k (Nat.le_refl _)).1 hF (hP k (Nat.le_refl _)).2)
    (fun {t w w'} hr => by obtain ⟨hk, -⟩ := hr; exact hk) (parts.map (·.1))
    (fun t ht => by obtain ⟨q, hq, ht'⟩ := hcovS t ht; exact ⟨q.1, List.mem_map_of_mem hq, ht'⟩)
    (fun w hw => by obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hw; exact (hinc q hq).1)
    (fun w hw => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hw
      obtain ⟨w₁, -, h1, -⟩ := hacc q hq
      exact ⟨sI.worker, WorkerOK.start hstI.state, checkJobList_chain _ _ _ h1⟩)
  obtain ⟨⟨F, hF⟩, hndS⟩ := hallS dsS.size (Nat.le_refl _)
  rw [← hlenS, List.take_of_length_le (Nat.le_refl _)] at hF hndS
  have hpure : ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified F) pins dsPS =
      .ok (ConLeche.streamEnv dsPS) := hF F (Nat.le_refl _)
  -- each worker's solution list ends in a worker's state of `sI`
  have hwalk : ∀ (l : List Nat) (w w'' : AState), WorkerOK sI w → (∀ x ∈ l, x < dsS.size) →
      checkJobList .verified ipins none IS dsS l w = .ok (.ok (), w'') → WorkerOK sI w'' := by
    intro l
    induction l with
    | nil =>
      intro w w'' hw _ h
      simp only [checkJobList] at h
      obtain ⟨-, rfl⟩ := AM.pure_ok h
      exact hw
    | cons x rest ih =>
      intro w w'' hw hl h
      obtain ⟨hx, w₁, hj, hrest⟩ := checkJobList_cons_inv h
      obtain ⟨hx', hdx⟩ := hdenS' x hx
      have hPx := hallS x (by omega)
      obtain ⟨hw₁, -⟩ := job_spec hrecS hpps hpinsOK hppI hPD hpd hISI hpIS hw hx hx' hdx hPx.1.envWF hPx.2 hj
      exact ih w₁ w'' hw₁ (fun y hy => hl y (List.mem_cons_of_mem _ hy)) hrest
  -- the challenge's jobs, with the solution, each worker from where its solution jobs ended
  let dsPC := (ConLeche.Frontend.preparePrelude preC rcC.decls).toList.map ConLeche.Cached.sideRecord
  let matesU := ConLeche.Cached.recordMates dsPC.toArray
  let J := solutionOf IS recsC
  obtain ⟨hlenC, hgetC⟩ := denoteDecls_getElem hdenR
  have hdenC' : ∀ (i : Nat) (hi : i < recsC.toArray.size), ∃ hi' : i < dsPC.length,
      Frontend.denoteDecl sI.store recsC.toArray[i] = some dsPC[i] := fun i hi => by
    obtain ⟨hi', h⟩ := hgetC i (by simpa using hi)
    exact ⟨by simpa [dsPC] using hi', Frontend.denoteDecl_ext hxI (by simpa [dsPC] using h)⟩
  have hlenC' : dsPC.length = recsC.toArray.size := by simpa [dsPC] using hlenC
  have hrec : RecordSpecC ipins pins J (ConLeche.streamEnv
      (ConLeche.Frontend.preparePrelude preC rcS.decls).toList) matesU := recordSpecC hk hind
  have hIS' := hIS.pmono hpIS (PExt.of_ext (hstepG.ext.trans hxI))
  have hmates : MatesRel sI.store J.mates matesU :=
    (solutionOf_mates hstepG.ok.wf hdenR hpR).mono hxI
  have hfin := pooled_foldP (Inv := WorkerOK sI) (Run := RecordRunJ ipins (some J) IC recsC.toArray)
    (N := dsPC.length) (P := MixedPrefix pins ⟨mkFEnv (ConLeche.streamEnv dsPS), matesU⟩ dsPC)
    (MixedPrefix.zero _ _ _)
    (fun {k w w'} _ hw hP hr => by
      obtain ⟨hk, hj⟩ := hr
      obtain ⟨hk', hdk⟩ := hdenC' k hk
      obtain ⟨hw', env', hstep⟩ := job_specC hrec hpps hpinsOK hppI hPD (by simpa using hpR) hICd hpIC
        hIS' hpIS (pure_nodup hpure) hmates hw hk hk' hdk hP hj
      exact ⟨hw', MixedPrefix.step hk' hP hstep⟩)
    (fun {t w w'} hr => by obtain ⟨hk, -⟩ := hr; omega) (parts.map (·.2))
    (fun t ht => by obtain ⟨q, hq, ht'⟩ := hcovC t (by omega); exact ⟨q.2, List.mem_map_of_mem hq, ht'⟩)
    (fun w hw => by obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hw; exact (hinc q hq).2)
    (fun w hw => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hw
      obtain ⟨w₁, w₂, h1, h2⟩ := hacc q hq
      exact ⟨w₁, hwalk q.1 sI.worker w₁ (WorkerOK.start hstI.state) (hrng q hq).1 h1,
        checkJobList_chainJ _ _ _ h2⟩)
  obtain ⟨hrunF, -⟩ := hfin
  rw [List.take_of_length_le (Nat.le_refl _)] at hrunF
  exact ⟨rcC, preC, _, hclC, rfl, Compare.mixed_model (pinsP := pins) V hpure hrunF⟩

/-- **The challenge of a comparison the twin accepts as the threads run it has a model**: con-leche's parser reads the
challenge, and its prepared records, each hole the axiom of its statement, have a model in every
set theory. Nothing is concluded about the solution. -/
theorem twinComparesAcceptsPooled_model (V : Type w) [SetTheory V] {bC bS : ByteArray}
    (h : TwinComparesAcceptsPooled bC bS) :
    ∃ (rcC : ConLeche.Frontend.ParseResultD) (preC : ConLeche.Frontend.PreludeIx),
      ConLeche.Frontend.parseChunks [bC] = .ok rcC ∧
      Nonempty (Model V (ConLeche.streamEnv
        ((ConLeche.Frontend.preparePrelude preC rcC.decls).toList.map ConLeche.Cached.sideRecord))) := by
  obtain ⟨rcC, preC, dsP, hclC, rfl, ⟨hmod⟩⟩ :=
    stagesCPooled_model V CoreSpec.of_core ConRon.Bridge.Inductives.indSpec_of_bridge h
  exact ⟨rcC, preC, hclC, ⟨ConLeche.Model.Model.ofEnvModelM hmod⟩⟩

/-- **No `False` in the challenge of a comparison the twin accepts as the threads run it**: a challenge file that declares
a theorem of type `False` is not accepted, whatever the solution. -/
theorem twinComparesAcceptsPooled_no_False (V : Type w) [SetTheory V] {bC bS : ByteArray}
    (hfalse : jsonWithTheoremFalse [bC]) (h : TwinComparesAcceptsPooled bC bS) : False := by
  obtain ⟨rcC, preC, dsP, hclC, rfl, ⟨mp⟩⟩ :=
    stagesCPooled_model V CoreSpec.of_core ConRon.Bridge.Inductives.indSpec_of_bridge h
  obtain ⟨cv, vl, hty, hmem⟩ := ConLeche.Frontend.parseChunks_jsonWithTheoremFalse hfalse hclC
  have hmem' : Declaration.thmDecl cv vl ∈
      (ConLeche.Frontend.preparePrelude preC rcC.decls).toList := by
    simpa using ConLeche.Frontend.mem_preparePrelude (pre := preC) hmem
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

/-- info: 'ConAgua.Final.twinComparesAcceptsPooled_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms twinComparesAcceptsPooled_model

/-- info: 'ConAgua.Final.twinComparesAcceptsPooled_no_False' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms twinComparesAcceptsPooled_no_False

end ConAgua.Final
