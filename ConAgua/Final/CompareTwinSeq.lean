module

public import ConAgua.Final.CompareTwinI
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
# The sequential compared run's twin: the challenge's jobs from the solution's (lane compare2)

`TwinComparesAcceptsSeqI` (`Final/CompareTwinI.lean`): after the stages up to the challenge's
index build (`sI`), the solution's jobs run in order from `sI.worker` and end in `sJ`, and the
challenge's jobs (with the solution) run in order from `sJ`.

* `seqS_walk`: a list of jobs run in order from a worker's state of `s₁`, from an accepted prefix,
  ends in a worker's state of `s₁` with the prefix extended (`job_spec`, `PrefixOK.step`): so `sJ`
  is a worker's state of `sI`, and the solution's pure fold accepts.
* `stagesCSeqI_model`: con-ron's `stagesC_model` with the solution's fold by `seqS_walk` and the
  challenge's (`pooledAcceptsJ_bridge`'s body) from `sJ`, a worker's state of `sI`.
* `twinComparesAcceptsSeqI_model`, `_no_False`: the conclusions of the pooled ones.
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

/-- **A worker's list run in order, from an accepted prefix** (con-ron's `pooled_fold_records`'
step, along one list): jobs `k‥k+n-1` accepted in order from a worker's state `w` of `s₁`, the
prefix of length `k` accepted by the pure fold with distinct names, end in a worker's state of
`s₁`, the prefix of length `k + n` accepted with distinct names. -/
theorem seqS_walk {pins : List INatOpPinSet} {pinsP : List NatOpPinSet}
    {ds : Array IDeclaration} {dsP : List Declaration} {I : IStreamIndex} {s₁ : AState}
    (hrec : RecordSpec pins pinsP) (hpush : KernelPushes pinsP) (hpp : PersPinSets pins)
    (hpinsOK : PinsOK s₁) (hpersPins : PersPins s₁) (hpins : PinsDenote s₁.store pins pinsP)
    (hpd : ∀ x ∈ ds.toList, PersDecl x)
    (hden : ∀ (i : Nat) (hi : i < ds.size), ∃ hi' : i < dsP.length,
      Frontend.denoteDecl s₁.store ds[i] = some dsP[i])
    (hI : IndexDenotes s₁.store I (ConLeche.Cached.buildIndex dsP.toArray))
    (hpI : PersIFBase I.base) :
    ∀ (n k : Nat) (w w'' : AState), WorkerOK s₁ w →
      PrefixOK pinsP dsP k ∧ ((ConLeche.Cached.recsConsts (dsP.take k)).map (·.name)).Nodup →
      checkJobList .verified pins none I ds (List.range' k n) w = .ok (.ok (), w'') →
      WorkerOK s₁ w'' ∧ PrefixOK pinsP dsP (k + n) ∧
        ((ConLeche.Cached.recsConsts (dsP.take (k + n))).map (·.name)).Nodup := by
  intro n
  induction n with
  | zero =>
    intro k w w'' hw hP h
    simp only [List.range'_zero, checkJobList] at h
    obtain ⟨-, rfl⟩ := AM.pure_ok h
    exact ⟨hw, hP⟩
  | succ n ih =>
    intro k w w'' hw hP h
    rw [List.range'_succ] at h
    obtain ⟨hk, w₁, hj, hrest⟩ := checkJobList_cons_inv h
    obtain ⟨hk', hdk⟩ := hden k hk
    obtain ⟨hw₁, env', F, hF⟩ :=
      job_spec hrec hpp hpinsOK hpersPins hpins hpd hI hpI hw hk hk' hdk hP.1.envWF hP.2 hj
    have hP' := PrefixOK.step hpush hk' hP.1 hF hP.2
    obtain ⟨hw'', hP''⟩ := ih (k + 1) w₁ w'' hw₁ hP' hrest
    rw [show k + 1 + n = k + (n + 1) by omega] at hP''
    exact ⟨hw'', hP''⟩

/-- con-ron: proof/ConRon/Bridge/Compare/Stages.lean stagesC_model, with the solution's jobs in
order from the challenge's index state and the challenge's from the state they end in — **the
challenge of a sequentially compared run has a model**. -/
theorem stagesCSeqI_model (V : Type w) [ConLeche.SetTheory V]
    (hk : CoreSpec ConRon.Arena.checkFuel) (hind : IndSpec)
    {bC bS : ByteArray} (h : TwinComparesAcceptsSeqI bC bS) :
    ∃ rcC preC dsP, ConLeche.Frontend.parseChunks [bC] = .ok rcC ∧
      dsP = (ConLeche.Frontend.preparePrelude preC rcC.decls).toList.map
        ConLeche.Cached.sideRecord ∧
      Nonempty (ConLeche.Model.EnvModelM V (ConLeche.streamEnv dsP)) := by
  obtain ⟨pins, ipins, dsS, recsC, IS, IC, sI, sJ, sK, hSt, hJS, hJC⟩ := h
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
  -- the solution: its jobs in order from `sI.worker` end in a worker's state `sJ`, and its pure
  -- fold accepts
  obtain ⟨hlen, hget⟩ := denoteDecls_getElem hdenS
  have hW := seqS_walk (recordSpec hk hind) (kernelPushes pins) hpps hpinsOK hppI hPD hpd
    (dsP := (ConLeche.Frontend.preparePrelude preC rcS.decls).toList)
    (fun i hi => by
      obtain ⟨hi', h⟩ := hget i (by simpa using hi)
      exact ⟨hi', Frontend.denoteDecl_ext hxEI (by simpa using h)⟩)
    (hIS.pmono hpIS (PExt.of_ext (hstepG.ext.trans hxI))) hpIS dsS.size 0 sI.worker sJ
    (WorkerOK.start hstI.state) ⟨⟨0, fun _ _ => rfl⟩, by
      have h0 : (ConLeche.Cached.recsConsts ([] : List Declaration)).length = 0 := by
        have := (ConLeche.Cached.buildIndex_spec (#[] : Array Declaration)).next
        simpa [ConLeche.Cached.buildIndex] using this.symm
      rw [List.take_zero, List.eq_nil_of_length_eq_zero h0]; exact List.nodup_nil⟩
    (by rw [← List.range_eq_range']; exact hJS)
  obtain ⟨hWJ, ⟨F, hF⟩, hndS⟩ := hW
  have hlenS : (ConLeche.Frontend.preparePrelude preC rcS.decls).toList.length = dsS.size := by
    simpa using hlen
  rw [Nat.zero_add, List.take_of_length_le (by omega)] at hF hndS
  have hpure : ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified F) pins
      (ConLeche.Frontend.preparePrelude preC rcS.decls).toList =
      .ok (ConLeche.streamEnv (ConLeche.Frontend.preparePrelude preC rcS.decls).toList) :=
    hF F (Nat.le_refl _)
  -- the challenge's jobs, with the solution, in order from `sJ`
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
    (N := dsPC.length) (P := MixedPrefix pins ⟨mkFEnv (ConLeche.streamEnv
      (ConLeche.Frontend.preparePrelude preC rcS.decls).toList), matesU⟩ dsPC)
    (MixedPrefix.zero _ _ _)
    (fun {k w w'} _ hw hP hr => by
      obtain ⟨hk, hj⟩ := hr
      obtain ⟨hk', hdk⟩ := hdenC' k hk
      obtain ⟨hw', env', hstep⟩ := job_specC hrec hpps hpinsOK hppI hPD (by simpa using hpR) hICd hpIC
        hIS' hpIS (pure_nodup hpure) hmates hw hk hk' hdk hP hj
      exact ⟨hw', MixedPrefix.step hk' hP hstep⟩)
    (fun {t w w'} hr => by obtain ⟨hk, -⟩ := hr; omega) [List.range recsC.toArray.size]
    (fun t ht => ⟨_, List.mem_singleton_self _, List.mem_range.mpr (by omega)⟩)
    (fun w hw => by rw [List.mem_singleton] at hw; subst hw; exact List.pairwise_lt_range)
    (fun w hw => by
      rw [List.mem_singleton] at hw; subst hw
      exact ⟨sJ, hWJ, checkJobList_chainJ _ _ _ hJC⟩)
  obtain ⟨hrunF, -⟩ := hfin
  rw [List.take_of_length_le (Nat.le_refl _)] at hrunF
  exact ⟨rcC, preC, _, hclC, rfl, Compare.mixed_model (pinsP := pins) V hpure hrunF⟩

/-- **The challenge of a sequentially compared run has a model**: con-leche's parser reads the
challenge, and its prepared records, each hole the axiom of its statement, have a model in every
set theory. Nothing is concluded about the solution. -/
theorem twinComparesAcceptsSeqI_model (V : Type w) [SetTheory V] {bC bS : ByteArray}
    (h : TwinComparesAcceptsSeqI bC bS) :
    ∃ (rcC : ConLeche.Frontend.ParseResultD) (preC : ConLeche.Frontend.PreludeIx),
      ConLeche.Frontend.parseChunks [bC] = .ok rcC ∧
      Nonempty (Model V (ConLeche.streamEnv
        ((ConLeche.Frontend.preparePrelude preC rcC.decls).toList.map ConLeche.Cached.sideRecord))) := by
  obtain ⟨rcC, preC, dsP, hclC, rfl, ⟨hmod⟩⟩ :=
    stagesCSeqI_model V CoreSpec.of_core ConRon.Bridge.Inductives.indSpec_of_bridge h
  exact ⟨rcC, preC, hclC, ⟨ConLeche.Model.Model.ofEnvModelM hmod⟩⟩

/-- **No `False` in the challenge of a sequentially compared run**: a challenge file that declares
a theorem of type `False` is not accepted, whatever the solution. -/
theorem twinComparesAcceptsSeqI_no_False (V : Type w) [SetTheory V] {bC bS : ByteArray}
    (hfalse : jsonWithTheoremFalse [bC]) (h : TwinComparesAcceptsSeqI bC bS) : False := by
  obtain ⟨rcC, preC, dsP, hclC, rfl, ⟨mp⟩⟩ :=
    stagesCSeqI_model V CoreSpec.of_core ConRon.Bridge.Inductives.indSpec_of_bridge h
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

/-- info: 'ConAgua.Final.twinComparesAcceptsSeqI_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms twinComparesAcceptsSeqI_model

/-- info: 'ConAgua.Final.twinComparesAcceptsSeqI_no_False' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms twinComparesAcceptsSeqI_no_False

end ConAgua.Final
