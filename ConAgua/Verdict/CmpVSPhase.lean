module

import ConAgua.Checker.CompareTwinC
public import ConAgua.Verdict.CmpVSJobs
public import ConAgua.Verdict.ThreadsE
public import ConAgua.Checker.CmpSPhaseThr
public import ConAgua.Final.CompareTwinVerdict
import ConAgua.Verdict.CmpVTJobsC
import ConAgua.Checker.CmpThreadsPool
import ConAgua.Checker.CmpVerdictNv
import ConAgua.Checker.CrsProgPB
import ConAgua.Checker.RomProgInit
import ConAgua.Checker.JobsProg
import ConAgua.Checker.CheckARun
import ConAgua.Checker.AsmFinal
import ConAgua.Arena.FreezeFresh
import ConAgua.Arena.FreezeTrunc
import ConAgua.Arena.JobStart
import ConAgua.Arena.LoopStart
import ConAgua.Arena.PoolJobsJ

@[expose] public section

/-!
# Both phases' threads fail only where the twin's pools from one state do (lane compare2,
design (i))

A thread over header S's view whose calls ran and whose next call failed with a class other than
`0`, the jobs below it run by the threads, is a worker's list of the solution's jobs failing from
`sI.worker`: `TwinCompareVerdictPooled`'s second disjunct.
-/

open ConRon.Arena ConAgua.Final

namespace L.Checker

open L L.Arena L.Rom L.Compiler ConRon.Bridge

local notation "VM" => ConLeche.CheckMode.verified

/-- **A solution job on a thread failing, from the challenge's index state, is the twin pool's**
a thread over header S's view (`CsViewS`, a buffer `B`
whose first call is `mS`'s fresh memory) with a fresh region `r₀` ran its calls `cs` (each below
`j`) and its call on `j < khi` (`khi` the solution's record count) failed with `e` of class other
than `0`; the threads `ths` ran every index below `j`: `TwinCompareVerdictPooled`'s second
disjunct. -/
theorem cmpV_tjobSI {bC bS pb : ByteArray} (hpb : pb.size < 2 ^ 63) (PS : PhaseS bC bS) {m₇ m : Mem}
    (hF : FoldOn bS pb (abiSz checkerTab) PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m)
    {c : Word} {m9 mS : Mem} (h6 : F6 PS m c m9) (hb9 : m9.bytes = m.bytes)
    {m2 m3 m4 : Mem} {dsC : Array IDeclaration} {sG : AState} {res : List IDeclaration}
    {I : IStreamIndex} {a' : AState}
    (h : Side6 PS m c m2 m3 dsC sG res m4) (hI : buildIndex res.toArray sG = .ok (.ok I, a'))
    (hV : CsViewS m m9 mS)
    (B : Array Word) (hB : CsFirst B mS) (khi : Word) (hk : khi.toNat = PS.dsS.size)
    (r₀ : Mem) (hz : ∀ b ∈ parOwnedL, r₀.arr64 b = zeros (mS.arr64 b).size)
    (hI0 : r₀.glob INIT = 0) (j : Word) (cs : List (Word × Nat × Mem)) (n : Nat) (e : Err)
    (hruns : ThreadFails B j n e r₀ cs) (hcs : ∀ c' ∈ cs, c'.1 < j)
    (hj : j < khi) (hk0 : e.cls ≠ 0)
    (ths : List (Mem × List (Word × Nat × Mem)))
    (hth : ∀ t ∈ ths, (∀ b ∈ parOwnedL, t.1.arr64 b = zeros (mS.arr64 b).size) ∧ t.1.glob INIT = 0 ∧
      ThreadRuns B t.1 t.2 ∧ ∀ c' ∈ t.2, c'.1 < khi)
    (hinc : ∀ t ∈ ths, (t.2.map (·.1)).Pairwise (· < ·))
    (hbelow : ∀ i : Word, i < j → ∃ t ∈ ths, ∃ c' ∈ t.2, c'.1 = i) :
    TwinCompareVerdictPooled bC bS e.cls := by
  obtain ⟨hJM9, hwf, hoff, -⟩ := F6.jobMAt hF h6 h hI
  have hJM : JobM PS.ipins (dnOf sG.store) PS.dsS none PS.IS mS a' :=
    hJM9.csViewS (J := solutionOf PS.IS res) hV hF.build.idx hF.frozen hF.build.decls hF.fsize
  obtain ⟨-, -, -, -, ho⟩ := h.phase.out
  -- the solution's records at `sG`
  have hoS := StagesOut.cmp PS.pfx PS.pinsR
  obtain ⟨dsSP, hdenS⟩ := hoS.den
  obtain ⟨-, hxF, -, -, -, -⟩ :=
    buildIndex_run constsSpec tablesSpec hoS.drv hoS.pp hoS.off hoS.pd hdenS PS.idx
  obtain ⟨-, hxFG, -, -, -⟩ := h.phase.out
  have hxEG : Ext PS.sE.store sG.store := hxF.trans hxFG
  -- the program facts
  have hr : RomOK pb.data.toList := by simpa [RomOK] using hpb
  have hpre := hF.r7.since.pbpre
  have hinj : L.Ind.DnInj (dnOf sG.store) := dnOf_inj ho.drv.state.wf
  have hq : L.Ind.QuotDn (dnOf sG.store) := by
    obtain ⟨k, hk, hd⟩ := ho.quot
    exact ⟨k, by simp only [dnOf, hk]; exact hd⟩
  obtain ⟨hdf, hind⟩ := checkerCdG_proved pb PS.ipins (dnOf sG.store) PS.dsS hpb hpre hinj
  have hcd := checkerProg_cdProgPB pb.data.toList hr hpre hinj hq hdf hind
  have hJP := checkerProg_jobProgPB pb.data.toList hr hpre hcd (checkerProg_canonPB _)
  let p := Prog.subPB pb.data.toList checkerProg
  have hds : PS.dsS.size < 2 ^ 63 := by
    have := hF.build.decls.room; have := hF.build.decls.dsize; omega
  have hjN : j.toNat < PS.dsS.size := by rw [← hk]; exact UInt64.lt_iff_toNat_lt.mp hj
  have hcN : ∀ c' ∈ cs, c'.1.toNat < PS.dsS.size := fun c' hc => by
    have := UInt64.lt_iff_toNat_lt.mp (hcs c' hc); omega
  -- the twin's side
  let a₀ : AState := { a' with caches := Caches.empty }
  let Rel : Mem → AState → Prop := fun r a =>
    ∀ j, ThrAt PS.ipins (dnOf sG.store) PS.dsS PS.IS a₀ pb.data.toList (seedMem (bufMem B r j)) a
  let Call : Nat → Mem → Mem → Prop := fun k r r' => ∃ n rs, n ≤ 2 ^ 62 ∧
    L.run checkerProg n "check" [] (bufMem B r (UInt64.ofNat k)) = .ok (rs, r') ∧ BufKept B r'
  obtain ⟨pinsP, dsP, hst, hrec, hpp, hden, hPD, -, -, -, hH⟩ := poolHypsS_I h.phase hI Rel Call
  have hdn : DnPers (dnOf sG.store) := fun k x hk => by
    simp only [dnOf] at hk; split at hk
    · assumption
    · cases hk
  have hLD : DeclsLpsDn (dnOf sG.store) PS.dsS :=
    declsLpsDn_dnOf hoS.pd ⟨_, ConRon.Bridge.Frontend.denoteDecls_ext hxEG _ _ hdenS⟩
  have hRS : RecStep PS.ipins (dnOf sG.store) PS.dsS PS.IS a₀ p :=
    recCall_stepE (J := none) hJP hoS.front hLD hdn hpp (by omega) hden hPD hrec
      (fun h => absurd h (by simp))
  have hCE : CjStepE PS.ipins (dnOf sG.store) PS.dsS PS.IS a₀ p :=
    cjStepE_of hJP hoS.front hLD hdn hrec hpp hds hden hPD (jobG_ofDn hinj hq pb hpb hpre)
  have hstep : ∀ (k : Nat) (r r' : Mem) (a : AState) (hk : k < PS.dsS.size), Rel r a → Call k r r' →
      (∃ env, FoldOK env (PS.IS.view k) (AM.st enterScratch a)) →
      ∃ a', recordJob VM PS.ipins none PS.IS k PS.dsS[k] a = .ok ((), a') ∧ Rel r' a' := by
    intro k r r' a hk hR ⟨n, rs, hn, hrun, hkept⟩ hfo
    have hk' : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
    obtain ⟨⟨a', hrj, X, hJ, hPB, hX⟩, hI'⟩ := runThr hJP.check_jobs hRS hds n hn a (UInt64.ofNat k)
      (by rw [hk']; exact hk) (by rw [hk']; exact hfo) _ rfl (hR _) rfl rfl hrun
    refine ⟨a', ?_, fun j => ⟨X, hJ, hPB, fun t ht => (thr_next _ j hI' hkept (thr_ctl_next hrun) t ht).trans (hX t ht)⟩⟩
    have e : PS.dsS[(UInt64.ofNat k).toNat]'(by rw [hk']; exact hk) = PS.dsS[k] := by simp only [hk']
    rw [← e]; simp only [hk'] at hrj ⊢; exact hrj
  have H := hH hstep
  -- a fresh region starts in the relation
  have hstart : ∀ r : Mem, (∀ b ∈ parOwnedL, r.arr64 b = zeros (mS.arr64 b).size) →
      r.glob INIT = 0 → Rel r a'.worker := by
    intro r hz hI0 j
    have hKI := indexKeysIn_of hJM.arena.base H.hI H.hpI
    have hJR := JobM.fresh (hJM.trunc hoff hKI) hwf hoff
    refine ⟨freshMem mS, ⟨_, ⟨hJR, PExt.of_ext (Ext.refl _), rfl⟩, ?_⟩, ?_, ?_⟩
    · exact ⟨by simp [AState.worker, estore_dropScratch_self hwf hoff], rfl, rfl⟩
    · rw [freshMem_arr8]
      show mS.bytes L.Rom.PB = _
      rw [hV.bytes, hb9, hF.bytes, ← Mem.arr8, hF.r7.since.keep.arr8]; exact loadMem_pb bS pb _
    · exact hB r j hz hI0
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
    hinc' j.toNat (Nat.le_of_lt hjN) (fun i hi => by
      have hi64 : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
      obtain ⟨t, ht, c', hc, hci⟩ := hbelow (UInt64.ofNat i) (by rw [UInt64.lt_iff_toNat_lt, hi64]; exact hi)
      exact ⟨_, List.mem_map_of_mem ht, List.mem_map.mpr ⟨c', hc, by rw [hci, hi64]⟩⟩)
  have hfold : ∀ x a, x < PS.dsS.size → x ≤ j.toNat → WorkerOK a' a →
      ∃ env, FoldOK env (PS.IS.view x) (AM.st enterScratch a) := fun x a hx hxj hw => by
    obtain ⟨hP, hnd⟩ := hpre x hxj
    obtain ⟨hx', -⟩ := H.hden x hx
    exact worker_foldOK H.hpinsOK H.hpersPins H.hI H.hpI hx' hP hnd hw
  -- the thread's walk
  have walk : ∀ (cs : List (Word × Nat × Mem)) (r : Mem) (a : AState), Rel r a → WorkerOK a' a →
      ThreadFails B j n e r cs → (∀ c' ∈ cs, c'.1 < j) →
      ErrClaimV (checkJobList VM PS.ipins none PS.IS PS.dsS (cs.map (·.1.toNat) ++ [j.toNat])) a e := by
    intro cs
    induction cs with
    | nil =>
      intro r a hR hw ⟨hn, hrun⟩ _
      exact runThrE hCE n hn a j hjN (hfold _ a hjN (Nat.le_refl _) hw) _ rfl (hR j) rfl rfl hrun
    | cons c' cs ih =>
      intro r a hR hw h hc
      obtain ⟨j', n', r'⟩ := c'
      obtain ⟨hn', ⟨rs, hrun⟩, hkept, hrest⟩ := h
      have hjj : j'.toNat < j.toNat := UInt64.lt_iff_toNat_lt.mp (hc _ List.mem_cons_self)
      have hj' : j'.toNat < PS.dsS.size := by omega
      obtain ⟨⟨a₁, hrj, X, hJ, hPB, hX⟩, hI'⟩ := runThr hJP.check_jobs hRS hds n' hn' a j' hj'
        (hfold _ a hj' (by omega) hw) _ rfl (hR _) rfl rfl hrun
      have hR' : Rel r' a₁ := fun j => ⟨X, hJ, hPB, fun t ht => (thr_next _ j hI' hkept (thr_ctl_next hrun) t ht).trans (hX t ht)⟩
      obtain ⟨hP, hnd⟩ := hpre j'.toNat (by omega)
      obtain ⟨hx', hdk⟩ := H.hden _ hj'
      obtain ⟨hw', -⟩ := job_spec H.hrec H.hpp H.hpinsOK H.hpersPins H.hpins H.hpd H.hI
        H.hpI hw hj' hx' hdk hP.envWF hnd hrj
      exact ErrClaimV.cons_ok hj' hrj
        (ih r' a₁ hR' hw' hrest fun c hc' => hc c (List.mem_cons_of_mem _ hc'))
  have hW := walk cs r₀ a'.worker (hstart r₀ hz hI0) (WorkerOK.start hst) hruns hcs
  refine .inr (.inl ⟨PS.pins, PS.ipins, PS.dsS, res, PS.IS, I, a', cs.map (·.1.toNat) ++ [j.toNat],
    h.stagesI hI, fun t ht => ?_, hW hk0⟩)
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨c', hc, rfl⟩ := List.mem_map.mp ht
    exact hcN c' hc
  · rw [List.mem_singleton.mp ht]; exact hjN

/-- info: 'L.Checker.cmpV_tjobSI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cmpV_tjobSI

end L.Checker
