module

public import ConAgua.Verdict.ThreadsE
public import ConAgua.Verdict.CmpVModes
import ConAgua.Verdict.IndArmTopE
import ConAgua.Checker.CmpSJobs
import ConAgua.Checker.ParThreadCall
import ConAgua.Checker.ParDriverTwin
import ConAgua.Checker.ParDriverL
import ConAgua.Checker.CmpHdrKeep
import ConAgua.Checker.CheckARun
import ConAgua.Checker.AsmFinal
import ConAgua.Arena.FreezeFresh
import ConAgua.Arena.FreezeTrunc
import ConAgua.Arena.IWFrame
import ConAgua.Checker.JobsStart
import ConAgua.Final.CmpChain
import ConAgua.Checker.RomProgInit
import ConAgua.Verdict.DeclTopE
import ConAgua.Arena.IndT.CheckIndDecl
import ConAgua.Checker.IndArm
import ConAgua.Checker.IotaArm
import ConAgua.Checker.ArmsT
import ConAgua.Checker.LoopProg
import ConAgua.Verdict.KnotAllE
import ConAgua.Checker.DefnArmT
import ConAgua.Checker.BlockRefsProg

@[expose] public section

/-!
# The solution's jobs of the compared run fail only where the twin's do (lane compare2, helper
compare2-verdict)

The error half of `sjobs_chainO` (`Checker/CmpSJobs.lean`): the solution's jobs run one after the
other on one worker region, each on the buffer as the job before left it; when job `j` fails with
a class other than `0` after the jobs below it accepted, the twin's job list over every solution
record fails with that class from the index state's worker (`sjobs_failO`, the walk of
`threads_twinVerdictPooled` over the changing buffers). `cmpV_sjob`: the same from the driver's
runs (`CmpErr`'s third arm), as `TwinCompareVerdict.jobsS`.
-/

open ConRon.Arena ConAgua.Final

namespace L.Checker

open L L.Arena L.Rom L.Compiler ConRon.Bridge

local notation "VM" => ConLeche.CheckMode.verified

/-- **The jobs' error claims at the checker for any record decoder** that is injective and gives
`Quot`'s universe name a handle (`jobG_checker` without the stages). -/
theorem jobG_ofDn {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration}
    {ipins : List INatOpPinSet} (hinj : L.Ind.DnInj dn) (hq : L.Ind.QuotDn dn) (pb : ByteArray)
    (hpb : pb.size < 2 ^ 63) (hpre : PbPre pb) :
    JobG ipins dn ds (Prog.subPB pb.data.toList checkerProg) := by
  have hr : RomOK pb.data.toList := by simpa [RomOK] using hpb
  have H := indArmProgs_checker _ hr hpre
  have hnv := checkerProg_nvPB pb.data.toList
  have hU : UceProg (Prog.subPB pb.data.toList checkerProg) :=
    ⟨checkerProg_uceLookupsPB _⟩
  have hG : VerdictCtxU (Prog.subPB pb.data.toList checkerProg) :=
    ⟨⟨hnv, checkerProg_coreStubsEPB _⟩, hU⟩
  exact jobG_of _ _ _ _
    (armsE_of _ _ _ _ (checkerProg_axArmPB _ hr hpre) (checkerProg_defnArmPB _ hr hpre)
      (checkerProg_thmArmPB _ hr hpre) (checkerProg_opqArmPB _ hr hpre) (checkerProg_quotArmPB _)
      (checkerProg_knotStagePB _) (checkerProg_leafClosedPB _) (checkerProg_apdPB _)
      (checkerProg_crKeepPB _) (checkerProg_crfPB _) (checkerProg_ccvSimsPB _ _)
      (checkerProg_quotSimsPB _ hr hpre hq) hinj hG)
    (indArmSpecE_checker _ hr hpre (cbRefs_checker _ hr hpre (snoSim_checker _)) _ hinj) hnv

/-- **The jobs' error claims at the checker for any twin prefix** (`jobG_checker` at `StagesOut`). -/
theorem jobG_ofOut {sE : AState} {ds : Array IDeclaration} {ipins : List INatOpPinSet}
    {pins : List ConLeche.NatOpPinSet} (ho : StagesOut sE ds ipins pins) (pb : ByteArray)
    (hpb : pb.size < 2 ^ 63) (hpre : PbPre pb) :
    JobG ipins (dnOf sE.store) ds (Prog.subPB pb.data.toList checkerProg) :=
  jobG_ofDn ho.dnInj ho.quotDn pb hpb hpre

/-- A job list failing on a prefix fails with the rest after it. -/
theorem twinFailsV_checkJobList_append {mode : ConLeche.CheckMode} {pins : List INatOpPinSet}
    {J : Option ISolution} {I : IStreamIndex} {ds : Array IDeclaration} {c : Word} :
    ∀ (w rest : List Nat) (a : AState), TwinFailsV (checkJobList mode pins J I ds w) a c →
      TwinFailsV (checkJobList mode pins J I ds (w ++ rest)) a c
  | [], _, a, h => by
    rcases h with ⟨ce, hce, -⟩ | ⟨ce, i, a', hce, -⟩ <;> cases hce
  | t :: w, rest, a, h => by
    have e : ∀ l, (checkJobList mode pins J I ds (t :: l)).run a =
        match runJob mode pins J I ds t a with
        | .ok (.ok (), s') => checkJobList mode pins J I ds l s'
        | .ok (.error e, s') => .ok (.error e, s')
        | .error e => .error e := fun _ => rfl
    have ih := twinFailsV_checkJobList_append (mode := mode) (pins := pins) (J := J) (I := I)
      (ds := ds) (c := c) w rest
    cases hr : runJob mode pins J I ds t a with
    | error ce =>
      rcases h with ⟨ce', hce, hc⟩ | ⟨ce', i, a', hce, hc⟩
      · exact .inl ⟨ce', by rw [List.cons_append, e, hr]; rw [e, hr] at hce; exact hce, hc⟩
      · rw [e, hr] at hce; cases hce
    | ok v =>
      obtain ⟨r, s'⟩ := v
      cases r with
      | error ce =>
        rcases h with ⟨ce', hce, hc⟩ | ⟨ce', i, a', hce, hc⟩
        · rw [e, hr] at hce; cases hce
        · exact .inr ⟨ce', i, a', by rw [List.cons_append, e, hr]; rw [e, hr] at hce; exact hce, hc⟩
      | ok u =>
        cases u
        have h' : TwinFailsV (checkJobList mode pins J I ds w) s' c := by
          rcases h with ⟨ce', hce, hc⟩ | ⟨ce', i, a', hce, hc⟩
          · exact .inl ⟨ce', by rw [e, hr] at hce; exact hce, hc⟩
          · exact .inr ⟨ce', i, a', by rw [e, hr] at hce; exact hce, hc⟩
        rcases ih s' h' with ⟨ce', hce, hc⟩ | ⟨ce', i, a', hce, hc⟩
        · exact .inl ⟨ce', by rw [List.cons_append, e, hr]; exact hce, hc⟩
        · exact .inr ⟨ce', i, a', by rw [List.cons_append, e, hr]; exact hce, hc⟩

/-- **The solution's jobs, chained on one region, job `j` failing ⇒ the twin's job list fails.**
As `sjobs_chainO`: the buffers `Bs` (`Bs 0` the frozen buffer) and the region memories `rm`
(`rm 0` fresh), the jobs below `j` returning calls whose frozen arrays are the next buffer's
images; job `j`'s call fails with `e` of class other than `0`. -/
theorem sjobs_failO {b pb : ByteArray} {sz : TieredArray → Nat} {ds : Array IDeclaration}
    {ipins : List INatOpPinSet} {pins : List ConLeche.NatOpPinSet} {sE : AState} {I : IStreamIndex}
    {sF : AState} {m₇ m : Mem}
    (ho : StagesOut sE ds ipins pins) (hidx : buildIndex ds sE = .ok (.ok I, sF))
    (hF : FoldOn b pb sz ds ipins sE I sF m₇ m)
    (hJP : JobProg ipins (dnOf sE.store) ds (Prog.subPB pb.data.toList checkerProg))
    (hJG : JobG ipins (dnOf sE.store) ds (Prog.subPB pb.data.toList checkerProg))
    (hok : parCompactOK m 1 = true) (hlt : (m.arr64 OUT).size < 2 ^ 64)
    (Bs : Nat → Array Word) (hB0 : Bs 0 = bufOf m) (rm : Nat → Mem)
    (hz : ∀ b ∈ parOwnedL, (rm 0).arr64 b = zeros (m.arr64 b).size) (hI0 : (rm 0).glob INIT = 0)
    (j : Nat) (hj : j < ds.size)
    (hrun : ∀ i < j, ∃ n rs, n ≤ 2 ^ 62 ∧
      L.run checkerProg n "check" [] (bufMem (Bs i) (rm i) (UInt64.ofNat i)) = .ok (rs, rm (i + 1)) ∧
      BufKept (Bs (i + 1)) (rm (i + 1)))
    (n : Nat) (hn : n ≤ 2 ^ 62) (e : Err)
    (hfail : L.run checkerProg n "check" [] (bufMem (Bs j) (rm j) (UInt64.ofNat j)) = .error e)
    (hk0 : e.cls ≠ 0) :
    TwinFailsV (checkJobList VM ipins none I ds (List.range ds.size)) sF.worker e.cls := by
  let bs := pb.data.toList
  let p := Prog.subPB bs checkerProg
  have hsz : ds.size < 2 ^ 63 := by
    have := hF.build.decls.room; have := hF.build.decls.dsize; omega
  have hx := (ho.built hidx).1
  let a₀ : AState := { sF with caches := Caches.empty }
  let Rel : Nat × Mem → AState → Prop := fun r a =>
    ∀ j, ThrAt ipins (dnOf sE.store) ds I a₀ bs (seedMem (bufMem (Bs r.1) r.2 j)) a
  let Call : Nat → Nat × Mem → Nat × Mem → Prop := fun k r r' => r.1 = k ∧ r'.1 = k + 1 ∧ ∃ n rs,
    n ≤ 2 ^ 62 ∧ L.run checkerProg n "check" [] (bufMem (Bs k) r.2 (UInt64.ofNat k)) = .ok (rs, r'.2) ∧
    BufKept (Bs (k + 1)) r'.2
  obtain ⟨pinsP, dsP, hst, hrec, hpp, hden, hPD, hH⟩ := poolHyps_of_out ho hidx Rel Call
  have hFD : FrontDecls ds := ho.front
  have hLD : DeclsLpsDn (dnOf sE.store) ds := declsLpsDn_dnOf ho.pd ho.den
  have hdn : DnPers (dnOf sE.store) := fun k x hk => by
    simp only [dnOf] at hk; split at hk
    · assumption
    · cases hk
  have hRS : RecStep ipins (dnOf sE.store) ds I a₀ p :=
    recCall_stepE (J := none) hJP hFD hLD hdn hpp (by omega) hden hPD hrec (fun h => absurd h (by simp))
  have hCE : CjStepE ipins (dnOf sE.store) ds I a₀ p :=
    cjStepE_of hJP hFD hLD hdn hrec hpp hsz hden hPD hJG
  have hstep : ∀ (k : Nat) (r r' : Nat × Mem) (a : AState) (hk : k < ds.size), Rel r a → Call k r r' →
      (∃ env, FoldOK env (I.view k) (AM.st enterScratch a)) →
      ∃ a', recordJob .verified ipins none I k ds[k] a = .ok ((), a') ∧ Rel r' a' := by
    intro k r r' a hk hR ⟨e1, e2, n, rs, hn, hrun, hkept⟩ hfo
    have hk' : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
    have hR' := hR (UInt64.ofNat k)
    rw [e1] at hR'
    obtain ⟨⟨a', hrj, X, hJ, hPB, hX⟩, hI⟩ := runThr hJP.check_jobs hRS hsz n hn a (UInt64.ofNat k)
      (by rw [hk']; exact hk) (by rw [hk']; exact hfo) _ rfl hR' rfl rfl hrun
    refine ⟨a', ?_, fun j => ⟨X, hJ, hPB, fun t ht => ?_⟩⟩
    · have e : ds[(UInt64.ofNat k).toNat]'(by rw [hk']; exact hk) = ds[k] := by simp only [hk']
      rw [← e]; simp only [hk'] at hrj ⊢; exact hrj
    · rw [e2]; exact (thr_next (Bs (k + 1)) j hI hkept t ht).trans (hX t ht)
  have H := hH hstep
  have hstart : Rel (0, rm 0) sF.worker := by
    intro j
    have hoff := hF.build.off
    have hw := hF.build.drv.state.wf
    have hKI := indexKeysIn_of (hF.jobM hx).arena.base H.hI H.hpI
    have hJR := JobM.fresh ((hF.jobM hx).trunc hoff hKI) hw hoff
    refine ⟨freshMem m, ⟨_, ⟨hJR, PExt.of_ext (Ext.refl _), rfl⟩, ?_⟩, ?_, ?_⟩
    · exact ⟨by simp [AState.worker, enableScratch_dropScratch], rfl, rfl⟩
    · rw [freshMem_arr8]
      show m.bytes L.Rom.PB = _
      rw [hF.bytes, ← Mem.arr8, hF.r7.since.keep.arr8]; exact loadMem_pb b pb sz
    · show ∀ t, thrS t = true → (seedMem (bufMem (Bs 0) (rm 0) j)).arr64 t = _
      rw [hB0]
      exact thr_first hok hlt (rm 0) j hz hI0
  -- the jobs below `j`: one thread's chain, every record below `j` run
  have hchain : ∀ i ≤ j, JobChain Call (i, rm i) (List.range' i (j - i)) := by
    intro i hi
    induction h : j - i generalizing i with
    | zero => exact .nil _
    | succ c ih =>
      rw [List.range'_succ]
      obtain ⟨n, rs, hn, hr, hk⟩ := hrun i (by omega)
      have hcall : Call i (i, rm i) (i + 1, rm (i + 1)) := ⟨rfl, rfl, n, rs, hn, hr, hk⟩
      exact .cons (w' := (i + 1, rm (i + 1))) hcall (ih (i + 1) (by omega) (by omega))
  have hc0 := hchain 0 (Nat.zero_le _)
  rw [Nat.sub_zero, ← List.range_eq_range'] at hc0
  have hpre := pool_prefix H hst [((0, rm 0), List.range j)] (by simpa using hstart)
    (by simpa using hc0) (by simpa using List.pairwise_lt_range) j (by omega)
    (fun k hk => ⟨_, List.mem_singleton_self _, List.mem_range.mpr hk⟩)
  have hfold : ∀ x a, x < ds.size → x ≤ j → WorkerOK sF a →
      ∃ env, FoldOK env (I.view x) (AM.st enterScratch a) := fun x a hx hxj hw => by
    obtain ⟨hP, hnd⟩ := hpre x hxj
    obtain ⟨hx', -⟩ := H.hden x hx
    exact worker_foldOK H.hpinsOK H.hpersPins H.hI H.hpI hx' hP hnd hw
  -- the walk: job `i`, …, job `j`, the last failing
  have walk : ∀ (c i : Nat) (a : AState), i + c = j → Rel (i, rm i) a → WorkerOK sF a →
      ErrClaimV (checkJobList VM ipins none I ds (List.range' i (c + 1))) a e := by
    intro c
    induction c with
    | zero =>
      intro i a hic hR hw
      simp only [Nat.add_zero] at hic
      subst hic
      have hj64 : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
      have := runThrE hCE n hn a (UInt64.ofNat i) (by rw [hj64]; exact hj)
        (by rw [hj64]; exact hfold _ a hj (Nat.le_refl _) hw) _ rfl (hR _) rfl rfl hfail
      rw [hj64] at this
      exact this
    | succ c ih =>
      intro i a hic hR hw
      have hi : i < ds.size := by omega
      obtain ⟨n', rs, hn', hr, hkept⟩ := hrun i (by omega)
      have hi64 : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
      obtain ⟨⟨a', hrj, X, hJ, hPB, hX⟩, hI'⟩ := runThr hJP.check_jobs hRS hsz n' hn' a (UInt64.ofNat i)
        (by rw [hi64]; exact hi) (by rw [hi64]; exact hfold _ a hi (by omega) hw) _ rfl (hR _) rfl rfl hr
      have hR' : Rel (i + 1, rm (i + 1)) a' :=
        fun j => ⟨X, hJ, hPB, fun t ht => (thr_next (Bs (i + 1)) j hI' hkept t ht).trans (hX t ht)⟩
      have hrj' : recordJob VM ipins none I i ds[i] a = .ok ((), a') := by
        have e : ds[(UInt64.ofNat i).toNat]'(by rw [hi64]; exact hi) = ds[i] := by simp only [hi64]
        rw [← e]; simp only [hi64] at hrj ⊢; exact hrj
      obtain ⟨hP, hnd⟩ := hpre i (by omega)
      obtain ⟨hx', hdk⟩ := H.hden _ hi
      obtain ⟨hw', -⟩ := job_spec H.hrec H.hpp H.hpinsOK H.hpersPins H.hpins H.hpd H.hI
        H.hpI hw hi hx' hdk hP.envWF hnd hrj'
      rw [List.range'_succ]
      exact ErrClaimV.cons_ok hi hrj' (ih (i + 1) a' (by omega) hR' hw')
  have hW := walk j 0 sF.worker (by omega) hstart (WorkerOK.start hst) hk0
  have hsplit : List.range ds.size = List.range' 0 (j + 1) ++ List.range' (j + 1) (ds.size - (j + 1)) := by
    obtain ⟨r, hr⟩ : ∃ r, ds.size = j + 1 + r := ⟨ds.size - (j + 1), by omega⟩
    rw [hr, List.range_eq_range', ← List.range'_append]
    simp
  rw [hsplit]
  exact twinFailsV_checkJobList_append _ _ _ hW

/-- **A solution job of the compared run failing is the twin's** (`CmpErr`'s third arm): after
modes `4` and `5` returned, the jobs below `j` accepted on the buffer as the jobs before left it
(`CmpJobs`), job `j < k` failing with a class other than `0`, `k` the solution's record count. -/
theorem cmpV_sjob (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (hbC : bC.size < 2 ^ 63) (hbS : bS.size < 2 ^ 63) (hpb : pb.size < 2 ^ 63)
    {rs4 : List Word} {m4 : Mem} {rs5 : List Word} {m5 : Mem}
    (h4 : cmpRun checkerProg (cmpM4 checkerTab MODE bC pb) = .ok (rs4, m4))
    (hge4 : 2 ^ 63 ≤ (rs4.getD 0 0).toNat)
    (h5 : cmpRun checkerProg (cmpM5 MODE m4 bS) = .ok (rs5, m5))
    (hge5 : 2 ^ 63 ≤ (rs5.getD 0 0).toNat) {rm : Nat → Mem} (h0 : rm 0 = zeroMem checkerTab)
    {j : Nat} (hj : j < (rs5.getD 0 0 - 9223372036854775808).toNat)
    (hjobs : CmpJobs checkerProg MODE PLO PHI frozenIdsL parOwnedL (cmpBuf OUT m5) rm j) {e : Err}
    (hfail : cmpRun checkerProg (bufMemG frozenIdsL parOwnedL PLO PHI MODE
      (bufSeq frozenIdsL (cmpBuf OUT m5) rm j) (rm j) (UInt64.ofNat j)) = .error e)
    (hk : e.cls ≠ 0) : TwinCompareVerdict bC bS e.cls := by
  obtain ⟨-, PS, m₇, m, hF, -, -, hok, hm5, hres⟩ := checker_modes45 bC bS pb h64 hbC hbS hpb h4 hge4 h5 hge5
  subst hm5
  have ho := StagesOut.cmp PS.pfx PS.pinsR
  have hJP := jobProg_of_out checkerCdG_proved ho (ds := PS.dsS) hpb hF.r7.since.pbpre
  have hJG := jobG_ofOut ho pb hpb hF.r7.since.pbpre
  have hsz : ∀ t, (m.arr64 t).size = abiSz checkerTab t := fun t => by
    rw [hF.frame.size, hF.r7.since.frame.size]; simp [loadMem, Mem.arr64]
  have hlt : (m.arr64 OUT).size < 2 ^ 64 := by
    rw [hsz]; have := abiSz_le checkerTab_abiOk OUT; simp only [abiWords] at this; omega
  have hB := (pc1_cmpBufOk m hok hlt).2
  have hB0 : cmpBuf OUT (parCompactMem m 1) = bufOf m := by
    simp only [cmpBuf]; rw [bufOf, (parCompactMem_hdr hok).2.1]
  have hBs := bufSeq_ok hB checker_cmpHdrKeep _ hjobs
  have hN : abiFuel ≤ 2 ^ 62 := by simp [abiFuel]
  have hds : PS.dsS.size < 2 ^ 63 := by
    have := hF.build.decls.room; have := hF.build.decls.dsize; omega
  have hkS : (rs5.getD 0 0 - 9223372036854775808).toNat = PS.dsS.size := by
    rw [L.getD_zero, hres]
    have e : (9223372036854775808 : Word) + UInt64.ofNat PS.dsS.size - 9223372036854775808 =
        UInt64.ofNat PS.dsS.size := by rw [UInt64.add_comm, UInt64.add_sub_cancel]
    rw [e, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
  rw [hkS] at hj
  have hTF := sjobs_failO ho PS.idx hF hJP hJG hok hlt
    (bufSeq frozenIdsL (cmpBuf OUT (parCompactMem m 1)) rm) hB0 rm
    (fun b hb => by rw [h0, hsz]; simp [ConAgua.Final.zeroMem, Mem.arr64, zeros]) (by rw [h0]; rfl) j hj
    (fun i hi => by
      obtain ⟨rs, hr, -⟩ := hjobs i hi
      have hr' : L.run checkerProg abiFuel "check" []
          (bufMem (bufSeq frozenIdsL (cmpBuf OUT (parCompactMem m 1)) rm i) (rm i) (UInt64.ofNat i)) =
          .ok (rs, rm (i + 1)) := by rw [bufMem_eq]; exact hr
      refine ⟨abiFuel, rs, hN, hr', fun k' hk' h1 => ?_⟩
      have hBj := hBs i (by omega)
      have hL : frozenIdsL.length = frozen.length + 1 := by rw [frozenIdsL_eq]; simp
      have hi' : k' + 1 < frozenIdsL.length := by omega
      have hent := hBj.ent (k' + 1) hi'
      have he := bufNext_entry hBj (checker_cmpHdrKeep _ _ _ _ _ hr) hi'
      have hs : ((rm (i + 1)).arr64 frozenIdsL[k' + 1]).size =
          (bufEntry (bufSeq frozenIdsL (cmpBuf OUT (parCompactMem m 1)) rm i) (k' + 1)).2 := by
        rw [run_check_size hr', frozenIdsL_get hk', bufMem_frozen _ _ _ hk' h1]
        simp only [bufImg, Array.size_extract]; omega
      have := bufNext_img hBj hi' he hs
      rw [frozenIdsL_get hk'] at this
      exact this.symm)
    abiFuel hN e (by rw [bufMem_eq]; exact hfail) hk
  obtain ⟨⟨hA, hB', hC⟩, hCS, hDS⟩ := PS.pfx
  exact TwinCompareVerdict.jobsS hA hB' hC hCS hDS PS.pinsR PS.idx hTF

end L.Checker
