module

public import ConAgua.Verdict.CmpVSJobs
public import ConAgua.Verdict.ThreadsE
public import ConAgua.Final.CompareTwinVerdict
import ConAgua.Checker.ParThreadTwin
import ConAgua.Checker.ParDriverTwin
import ConAgua.Checker.ParDriverL
import ConAgua.Checker.CheckARun
import ConAgua.Checker.AsmFinal
import ConAgua.Checker.JobsStart
import ConAgua.Checker.RomProgInit
import ConAgua.Arena.FreezeFresh
import ConAgua.Arena.FreezeTrunc
import ConAgua.Arena.IWFrame
import ConAgua.Final.CmpChain

@[expose] public section

/-!
# The threaded solution's jobs of the compared run fail only where the twin's pool does (lane
compare2, helper compare2-verdict)

`cmpV_threadsFailO`: `threads_twinVerdictPooled`'s walk after an index build (`FoldOn`, the
stages' twin facts `StagesOut`, as `threads_pooledO`): a thread over the frozen buffer whose calls
ran and whose next call failed with a class other than `0`, the jobs below it run by the threads,
is a worker's job list failing with that class. `cmpV_tjobS`: the same for the solution's pool of
the threaded compared run, after modes `4` and `5` (`TwinCompareVerdictPooled`'s second
disjunct).
-/

open ConRon.Arena ConAgua.Final

namespace L.Checker

open L L.Arena L.Rom L.Compiler ConRon.Bridge

local notation "VM" => ConLeche.CheckMode.verified

/-- **A thread's failing call after an index build is a worker's job list failing**
(`threads_twinVerdictPooled` at `FoldOn` and `StagesOut`): the thread with the fresh region `r₀`
ran its calls `cs` (each below `j`), its call on `j < khi` failed with `e` of class other than `0`;
the threads `ths` (fresh regions, claims below `khi`, increasing) ran every index below `j`. -/
theorem cmpV_threadsFailO {b pb : ByteArray} {sz : TieredArray → Nat} {ds : Array IDeclaration}
    {ipins : List INatOpPinSet} {pins : List ConLeche.NatOpPinSet} {sE : AState} {I : IStreamIndex}
    {sF : AState} {m₇ m : Mem}
    (ho : StagesOut sE ds ipins pins) (hidx : buildIndex ds sE = .ok (.ok I, sF))
    (hF : FoldOn b pb sz ds ipins sE I sF m₇ m)
    (hJP : JobProg ipins (dnOf sE.store) ds (Prog.subPB pb.data.toList checkerProg))
    (hJG : JobG ipins (dnOf sE.store) ds (Prog.subPB pb.data.toList checkerProg))
    (hok : parCompactOK m 1 = true) (hlt : (m.arr64 OUT).size < 2 ^ 64)
    (B : Array Word) (hBm : B = bufOf m) (khi : Word) (hk : khi.toNat = ds.size)
    (r₀ : Mem) (hz : ∀ b ∈ parOwnedL, r₀.arr64 b = zeros (m.arr64 b).size)
    (hI : r₀.glob INIT = 0) (j : Word) (cs : List (Word × Nat × Mem)) (n : Nat) (e : Err)
    (hruns : ThreadFails B j n e r₀ cs) (hcs : ∀ c ∈ cs, c.1 < j)
    (hj : j < khi) (hk0 : e.cls ≠ 0)
    (ths : List (Mem × List (Word × Nat × Mem)))
    (hth : ∀ t ∈ ths, (∀ b ∈ parOwnedL, t.1.arr64 b = zeros (m.arr64 b).size) ∧
      t.1.glob INIT = 0 ∧ ThreadRuns B t.1 t.2 ∧ ∀ c ∈ t.2, c.1 < khi)
    (hinc : ∀ t ∈ ths, (t.2.map (·.1)).Pairwise (· < ·))
    (hbelow : ∀ i : Word, i < j → ∃ t ∈ ths, ∃ c ∈ t.2, c.1 = i) :
    ∃ w : List Nat, (∀ t ∈ w, t < ds.size) ∧
      TwinFailsV (checkJobList VM ipins none I ds w) sF.worker e.cls := by
  let bs := pb.data.toList
  let p := Prog.subPB bs checkerProg
  have hsz : ds.size < 2 ^ 63 := by
    have := hF.build.decls.room; have := hF.build.decls.dsize; omega
  have hx := (ho.built hidx).1
  have hjN : j.toNat < ds.size := by rw [← hk]; exact UInt64.lt_iff_toNat_lt.mp hj
  have hcN : ∀ c ∈ cs, c.1.toNat < ds.size := fun c hc => by
    have := UInt64.lt_iff_toNat_lt.mp (hcs c hc); omega
  -- the twin's side
  let a₀ : AState := { sF with caches := Caches.empty }
  let Rel : Mem → AState → Prop := fun r a =>
    ∀ j, ThrAt ipins (dnOf sE.store) ds I a₀ bs (seedMem (bufMem B r j)) a
  let Call : Nat → Mem → Mem → Prop := fun k r r' => ∃ n rs, n ≤ 2 ^ 62 ∧
    L.run checkerProg n "check" [] (bufMem B r (UInt64.ofNat k)) = .ok (rs, r') ∧ BufKept B r'
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
  have hstep : ∀ (k : Nat) (r r' : Mem) (a : AState) (hk : k < ds.size), Rel r a → Call k r r' →
      (∃ env, FoldOK env (I.view k) (AM.st enterScratch a)) →
      ∃ a', recordJob .verified ipins none I k ds[k] a = .ok ((), a') ∧ Rel r' a' := by
    intro k r r' a hk hR ⟨n, rs, hn, hrun, hkept⟩ hfo
    have hk' : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
    obtain ⟨⟨a', hrj, X, hJ, hPB, hX⟩, hI⟩ := runThr hJP.check_jobs hRS hsz n hn a (UInt64.ofNat k)
      (by rw [hk']; exact hk) (by rw [hk']; exact hfo) _ rfl (hR _) rfl rfl hrun
    refine ⟨a', ?_, fun j => ⟨X, hJ, hPB, fun t ht => (thr_next B j hI hkept (thr_ctl_next hrun) t ht).trans (hX t ht)⟩⟩
    have e : ds[(UInt64.ofNat k).toNat]'(by rw [hk']; exact hk) = ds[k] := by simp only [hk']
    rw [← e]; simp only [hk'] at hrj ⊢; exact hrj
  have H := hH hstep
  -- a fresh region starts in the relation
  have hstart : ∀ r : Mem, (∀ b ∈ parOwnedL, r.arr64 b = zeros (m.arr64 b).size) → r.glob INIT = 0 →
      Rel r sF.worker := by
    intro r hz hI j
    have hoff := hF.build.off
    have hw := hF.build.drv.state.wf
    have hKI := indexKeysIn_of (hF.jobM hx).arena.base H.hI H.hpI
    have hJR := JobM.fresh ((hF.jobM hx).trunc hoff hKI) hw hoff
    refine ⟨freshMem m, ⟨_, ⟨hJR, PExt.of_ext (Ext.refl _), rfl⟩, ?_⟩, ?_, ?_⟩
    · exact ⟨by simp [AState.worker, enableScratch_dropScratch], rfl, rfl⟩
    · rw [freshMem_arr8]
      show m.bytes L.Rom.PB = _
      rw [hF.bytes, ← Mem.arr8, hF.r7.since.keep.arr8]; exact loadMem_pb b pb sz
    · rw [hBm]
      exact thr_first hok hlt r j (fun b hb => by rw [hz b hb]) hI
  -- the threads' runs below `j`: the fold's prefixes up to `j`
  let ths' : List (Mem × List Nat) := ths.map fun t => (t.1, t.2.map (·.1.toNat))
  have hinc' : ∀ t ∈ ths', t.2.Pairwise (· < ·) := by
    intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
    have := hinc t₀ ht₀
    rw [List.pairwise_map] at this ⊢
    exact this.imp fun h => UInt64.lt_iff_toNat_lt.mp h
  have hpre := pool_prefix H hst ths'
    (fun t ht => by
      obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
      exact hstart t₀.1 (hth t₀ ht₀).1 (hth t₀ ht₀).2.1)
    (fun t ht => by
      obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
      exact threadRuns_chain B _ _ (hth t₀ ht₀).2.2.1)
    hinc' j.toNat (by omega) (fun i hi => by
      have hi64 : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
      obtain ⟨t, ht, c, hc, hci⟩ := hbelow (UInt64.ofNat i) (by rw [UInt64.lt_iff_toNat_lt, hi64]; exact hi)
      exact ⟨_, List.mem_map_of_mem ht, List.mem_map.mpr ⟨c, hc, by rw [hci, hi64]⟩⟩)
  have hfold : ∀ x a, x < ds.size → x ≤ j.toNat → WorkerOK sF a →
      ∃ env, FoldOK env (I.view x) (AM.st enterScratch a) := fun x a hx hxj hw => by
    obtain ⟨hP, hnd⟩ := hpre x hxj
    obtain ⟨hx', -⟩ := H.hden x hx
    exact worker_foldOK H.hpinsOK H.hpersPins H.hI H.hpI hx' hP hnd hw
  -- the thread's walk
  have walk : ∀ (cs : List (Word × Nat × Mem)) (r : Mem) (a : AState), Rel r a → WorkerOK sF a →
      ThreadFails B j n e r cs →
      (∀ c ∈ cs, c.1 < j) →
      ErrClaimV (checkJobList VM ipins none I ds (cs.map (·.1.toNat) ++ [j.toNat])) a e := by
    intro cs
    induction cs with
    | nil =>
      intro r a hR hw ⟨hn, hrun⟩ _
      exact runThrE hCE n hn a j hjN (hfold _ a hjN (Nat.le_refl _) hw) _ rfl (hR j) rfl rfl hrun
    | cons c cs ih =>
      intro r a hR hw h hc
      obtain ⟨j', n', r'⟩ := c
      obtain ⟨hn', ⟨rs, hrun⟩, hkept, hrest⟩ := h
      have hjj : j'.toNat < j.toNat := UInt64.lt_iff_toNat_lt.mp (hc _ List.mem_cons_self)
      have hj' : j'.toNat < ds.size := by omega
      obtain ⟨⟨a', hrj, X, hJ, hPB, hX⟩, hI'⟩ := runThr hJP.check_jobs hRS hsz n' hn' a j' hj'
        (hfold _ a hj' (by omega) hw) _ rfl (hR _) rfl rfl hrun
      have hR' : Rel r' a' := fun j => ⟨X, hJ, hPB, fun t ht => (thr_next B j hI' hkept (thr_ctl_next hrun) t ht).trans (hX t ht)⟩
      obtain ⟨hP, hnd⟩ := hpre j'.toNat (by omega)
      obtain ⟨hx', hdk⟩ := H.hden _ hj'
      obtain ⟨hw', -⟩ := job_spec H.hrec H.hpp H.hpinsOK H.hpersPins H.hpins H.hpd H.hI
        H.hpI hw hj' hx' hdk hP.envWF hnd hrj
      exact ErrClaimV.cons_ok hj' hrj
        (ih r' a' hR' hw' hrest fun c hc' => hc c (List.mem_cons_of_mem _ hc'))
  have hW := walk cs r₀ sF.worker (hstart r₀ hz hI) (WorkerOK.start hst) hruns hcs
  refine ⟨cs.map (·.1.toNat) ++ [j.toNat], fun t ht => ?_, hW hk0⟩
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
    exact hcN c hc
  · rw [List.mem_singleton.mp ht]; exact hjN

/-- **A solution job on a thread of the threaded compared run failing is the twin pool's**: after
modes `4` and `5` returned (`m5`, `rs5`), a thread over the frozen buffer `cmpBuf OUT m5` with a
fresh region `r₀` ran its calls `cs` (each below `j`) and its call on `j < k` (`k` the solution's
record count) failed with `e` of class other than `0`; the threads `ths` (fresh regions, claims
below `k`, increasing) ran every index below `j`. -/
theorem cmpV_tjobS (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (hbC : bC.size < 2 ^ 63) (hbS : bS.size < 2 ^ 63) (hpb : pb.size < 2 ^ 63)
    {rs4 : List Word} {m4 : Mem} {rs5 : List Word} {m5 : Mem}
    (h4 : cmpRun checkerProg (cmpM4 checkerTab MODE bC pb) = .ok (rs4, m4))
    (hge4 : 2 ^ 63 ≤ (rs4.getD 0 0).toNat)
    (h5 : cmpRun checkerProg (cmpM5 MODE m4 bS) = .ok (rs5, m5))
    (hge5 : 2 ^ 63 ≤ (rs5.getD 0 0).toNat)
    (r₀ : Mem) (hz : ∀ b ∈ parOwnedL, r₀.arr64 b = zeros (m5.arr64 b).size)
    (hI : r₀.glob INIT = 0) (j : Word) (cs : List (Word × Nat × Mem)) (n : Nat) (e : Err)
    (hruns : ThreadFails (cmpBuf OUT m5) j n e r₀ cs) (hcs : ∀ c ∈ cs, c.1 < j)
    (hj : j < rs5.getD 0 0 - 9223372036854775808) (hk0 : e.cls ≠ 0)
    (ths : List (Mem × List (Word × Nat × Mem)))
    (hth : ∀ t ∈ ths, (∀ b ∈ parOwnedL, t.1.arr64 b = zeros (m5.arr64 b).size) ∧
      t.1.glob INIT = 0 ∧ ThreadRuns (cmpBuf OUT m5) t.1 t.2 ∧
      ∀ c ∈ t.2, c.1 < rs5.getD 0 0 - 9223372036854775808)
    (hinc : ∀ t ∈ ths, (t.2.map (·.1)).Pairwise (· < ·))
    (hbelow : ∀ i : Word, i < j → ∃ t ∈ ths, ∃ c ∈ t.2, c.1 = i) :
    TwinCompareVerdictPooled bC bS e.cls := by
  obtain ⟨-, PS, m₇, m, hF, -, -, hok, hm5, hres⟩ := checker_modes45 bC bS pb h64 hbC hbS hpb h4 hge4 h5 hge5
  subst hm5
  have ho := StagesOut.cmp PS.pfx PS.pinsR
  have hJP := jobProg_of_out checkerCdG_proved ho (ds := PS.dsS) hpb hF.r7.since.pbpre
  have hJG := jobG_ofOut ho pb hpb hF.r7.since.pbpre
  have hsz : ∀ t, (m.arr64 t).size = abiSz checkerTab t := fun t => by
    rw [hF.frame.size, hF.r7.since.frame.size]; simp [loadMem, Mem.arr64]
  have hlt : (m.arr64 OUT).size < 2 ^ 64 := by
    rw [hsz]; have := abiSz_le checkerTab_abiOk OUT; simp only [abiWords] at this; omega
  have hB0 : cmpBuf OUT (parCompactMem m 1) = bufOf m := by
    simp only [cmpBuf]; rw [bufOf, (parCompactMem_hdr hok).2.1]
  have hO := parCompactMem_out m 1
  have hds : PS.dsS.size < 2 ^ 63 := by
    have := hF.build.decls.room; have := hF.build.decls.dsize; omega
  have hkS : (rs5.getD 0 0 - 9223372036854775808).toNat = PS.dsS.size := by
    rw [L.getD_zero, hres]
    have e : (9223372036854775808 : Word) + UInt64.ofNat PS.dsS.size - 9223372036854775808 =
        UInt64.ofNat PS.dsS.size := by rw [UInt64.add_comm, UInt64.add_sub_cancel]
    rw [e, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
  obtain ⟨w, hw, hTF⟩ := cmpV_threadsFailO ho PS.idx hF hJP hJG hok hlt _ hB0 _ hkS r₀
    (fun b hb => by rw [hz b hb, hO.size]) hI j cs n e hruns hcs hj hk0 ths
    (fun t ht => by
      obtain ⟨h1, h2, h3, h4⟩ := hth t ht
      exact ⟨fun b hb => by rw [h1 b hb, hO.size], h2, h3, h4⟩) hinc hbelow
  obtain ⟨⟨hA, hB', hC⟩, hCS, hDS⟩ := PS.pfx
  exact .inr (.inl ⟨PS.pins, PS.sA, PS.sB, PS.sC, PS.sC', PS.sD, PS.sE, PS.sF, PS.pre, PS.rC, PS.rS,
    PS.dsS, PS.ipins, PS.IS, w, hA, hB', hC, hCS, hDS, PS.pinsR, PS.idx, hw, hTF⟩)

-- TEMP (compare2-freeze): `sorryAx` from the stand-ins (bufSeq_seed_standin, checker_modes45, checkC3_of_stages)
/-- info: 'L.Checker.cmpV_tjobS' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cmpV_tjobS

end L.Checker
