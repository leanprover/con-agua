module

public import ConAgua.Final.C1Threads
public import ConAgua.Verdict.ThreadsE
import ConAgua.Verdict.CmpVSJobs
import ConAgua.Verdict.CmpVTJobsC
import ConAgua.Checker.CmpThreadsC
import ConAgua.Checker.CmpVerdictNv
import ConAgua.Checker.CmpSPhaseT
import ConAgua.Checker.CrsProgPB
import ConAgua.Checker.RomProgInit
import ConAgua.Checker.JobsProg
import ConAgua.Arena.FreezeFresh
import ConRon.Bridge.Compare.Mates
import ConAgua.Checker.C1Back
import ConAgua.Checker.C1Hdr
public import ConAgua.Final.CpThreads
public import ConAgua.Checker.CmpSPhase
import ConAgua.Checker.CompareChain6J
public import ConAgua.Arena.FreezeView
import ConAgua.Final.CmpChain
public import ConAgua.Final.CompareTwinVerdict
import ConRon.Bridge.Checker.Install
import ConAgua.Checker.ArmsT
import ConAgua.Checker.LoopProg
import ConAgua.Arena.IWFrame

@[expose] public section

/-!
# A challenge job failing on a thread of the compared run, both phases on one region (lane compare2, H7)

`c1Thr_failC`: a thread ran its solution calls over header S and then, on the region as they left
it, its challenge calls over header C, the last failing with an error of class other than `0`; the
other threads claimed every solution job and every challenge job below the failing one: the
twin's threaded comparison fails with that class (`TwinCompareVerdictPooled`'s third disjunct). The
solution's phase as in `c1Thr_accepts` (with the failing thread's solution calls as one more
worker), the switch (`c1_thrBack`), then the failing thread's walk (from its own start).
-/

open ConRon.Arena ConRon.Bridge

namespace ConAgua.Final

open L L.Compiler L.Checker L.Arena L.Rom

local notation "VM" => ConLeche.CheckMode.verified

/-- **A thread's challenge job failing after its solution calls is the twin's threaded failure.** -/
theorem c1Thr_failC {bC bS pb : ByteArray} (hpb : pb.size < 2 ^ 63) (PS : PhaseS bC bS)
    {m₇ m : Mem} (hF : FoldOn bS pb (abiSz checkerTab) PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m)
    {c : Word} {m9 mS : Mem} (h6 : F6 PS m c m9) (hb9 : m9.bytes = m.bytes) (hV : CsViewS m m9 mS)
    (B : Array Word) (hBS : HdrView B mS) (khi : Word) (hk : khi.toNat = PS.dsS.size)
    (BC : Array Word) (hBC : HdrView BC m9)
    (hext : ∀ i < frozen.length, fzExt mS (fzAt i) = fzExt m9 (fzAt i))
    (r₀ : Mem) (hz : ∀ b ∈ parOwnedL, r₀.arr64 b = zeros (mS.arr64 b).size) (hI0 : r₀.glob INIT = 0)
    (csS : List (Word × Nat × Mem)) (hS : ThreadRuns B r₀ csS) (hcsS : ∀ c' ∈ csS, c'.1 < khi)
    (hincS1 : (csS.map (·.1)).Pairwise (· < ·))
    (j : Word) (csC : List (Word × Nat × Mem)) (n : Nat) (e : Err)
    (hruns : ThreadFails BC j n e (runsEnd r₀ csS) csC) (hcs : ∀ c' ∈ csC, c'.1 < j)
    (hj : j < c) (hk0 : e.cls ≠ 0)
    (ths : List (Mem × List (Word × Nat × Mem) × List (Word × Nat × Mem)))
    (hth : ∀ t ∈ ths, (∀ b ∈ parOwnedL, t.1.arr64 b = zeros (mS.arr64 b).size) ∧ t.1.glob INIT = 0 ∧
      ThreadRuns B t.1 t.2.1 ∧ (∀ c' ∈ t.2.1, c'.1 < khi) ∧
      ThreadRuns BC (runsEnd t.1 t.2.1) t.2.2 ∧ ∀ c' ∈ t.2.2, c'.1 < c)
    (hcovS : ∀ j' : Word, j' < khi → ∃ t ∈ ths, ∃ c' ∈ t.2.1, c'.1 = j')
    (hcovC : ∀ j' : Word, j' < j → ∃ t ∈ ths, ∃ c' ∈ t.2.2, c'.1 = j')
    (hincS : ∀ t ∈ ths, (t.2.1.map (·.1)).Pairwise (· < ·))
    (hincC : ∀ t ∈ ths, (t.2.2.map (·.1)).Pairwise (· < ·)) :
    TwinCompareVerdictPooled bC bS e.cls := by
  obtain ⟨m2, m3, dsC, sG, res, m4, I, a', h, hI, -⟩ := F6.jobM hF h6
  obtain ⟨hJM9, hwf, hoff, -⟩ := F6.jobMAt hF h6 h hI
  have hJM : JobM PS.ipins (dnOf sG.store) PS.dsS none PS.IS mS a' :=
    hJM9.csViewS (J := solutionOf PS.IS res) hV hF.build.idx hF.frozen hF.build.decls hF.fsize
  obtain ⟨-, -, -, -, ho⟩ := h.phase.out
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
  have hds : PS.dsS.size < 2 ^ 63 := by
    have := hF.build.decls.room; have := hF.build.decls.dsize; omega
  -- the solution's phase
  let a₀ : AState := { a' with caches := Caches.empty }
  let X₀ : Mem := freshMem mS
  let RelS : Mem → AState → Prop := fun r a =>
    ∀ j, ThrAtQ (c1Q X₀) PS.ipins (dnOf sG.store) PS.dsS PS.IS a₀ pb.data.toList
      (L.Checker.seedMem (bufMem B r j)) a
  let CallS : Nat → Mem → Mem → Prop := fun k r r' => ∃ n rs, n ≤ 2 ^ 62 ∧
    L.run checkerProg n "check" [] (bufMem B r (UInt64.ofNat k)) = .ok (rs, r') ∧ BufKept B r'
  obtain ⟨pinsP, dsP, hst, hrec, hpp, hden, hPD, -, -, -, hH⟩ := poolHypsS_I h.phase hI RelS CallS
  have hdn : DnPers (dnOf sG.store) := fun k x hk => by
    simp only [dnOf] at hk; split at hk
    · assumption
    · cases hk
  have hLD : DeclsLpsDn (dnOf sG.store) PS.dsS :=
    declsLpsDn_dnOf hoS.pd ⟨_, ConRon.Bridge.Frontend.denoteDecls_ext hxEG _ _ hdenS⟩
  have h224 : rdW (X₀.arr64 CTL) 224 = 0 := by rw [c1_rdW_fresh mS (by decide)]; exact hV.c224
  have hRS : RecStepQ (c1Q X₀) PS.ipins (dnOf sG.store) PS.dsS PS.IS a₀ (Prog.subPB pb.data.toList checkerProg) :=
    c1_recStepQ (closedW_subPB _ checkerProg_cqF0W) hJP.record_job X₀ h224
      (recCall_stepX (J := none) hJP hoS.front hLD hdn hpp (by omega) hden hPD hrec
        (fun h => absurd h (by simp)) X₀)
  have hstepS : ∀ (k : Nat) (r r' : Mem) (a : AState) (hk : k < PS.dsS.size), RelS r a → CallS k r r' →
      (∃ env, FoldOK env (PS.IS.view k) (AM.st enterScratch a)) →
      ∃ a', recordJob VM PS.ipins none PS.IS k PS.dsS[k] a = .ok ((), a') ∧ RelS r' a' := by
    intro k r r' a hk hR ⟨n, rs, hn, hrun, hkept⟩ hfo
    have hk' : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
    obtain ⟨⟨a', hrj, X, hJ, hQ, hPB, hX⟩, hI'⟩ := runThrQ hJP.check_jobs hRS (fun X g hQ _ => c1Q_flush g hQ)
      hds n hn a (UInt64.ofNat k) (by rw [hk']; exact hk) (by rw [hk']; exact hfo) _ rfl (hR _) rfl rfl hrun
    refine ⟨a', ?_, fun j => ⟨X, hJ, hQ, hPB, fun t ht =>
      (thr_next _ j hI' hkept (thr_ctl_next hrun) t ht).trans (hX t ht)⟩⟩
    have e : PS.dsS[(UInt64.ofNat k).toNat]'(by rw [hk']; exact hk) = PS.dsS[k] := by simp only [hk']
    rw [← e]; simp only [hk'] at hrj ⊢; exact hrj
  have H := hH hstepS
  -- the threads' starts
  have hKI := indexKeysIn_of hJM.arena.base H.hI H.hpI
  have hJR0 := JobM.fresh (hJM.trunc hoff hKI (.inr (F6.extOKS hF h6 hV))) hwf hoff
  have hPB0 : X₀.arr8 L.Rom.PB = pb.data.toList.toArray := by
    rw [freshMem_arr8]
    show mS.bytes L.Rom.PB = _
    rw [hV.bytes, hb9, hF.bytes, ← Mem.arr8, hF.r7.since.keep.arr8]; exact loadMem_pb bS pb _
  have hstart0 : ∀ r : Mem, (∀ b ∈ parOwnedL, r.arr64 b = zeros (mS.arr64 b).size) → r.glob INIT = 0 →
      RelS r a'.worker := by
    intro r hz hI0 j
    refine ⟨X₀, ⟨_, ⟨hJR0, PExt.of_ext (Ext.refl _), rfl⟩, ?_⟩, ⟨MemFrame.refl _ _ _, fun _ _ h => h⟩, hPB0,
      csFirst_hdrView hBS r j hz hI0⟩
    exact ⟨by simp [AState.worker, estore_dropScratch_self hwf hoff], rfl, rfl⟩

  -- the solution's phase: the failing thread's solution calls and the other threads'
  let thsE : List (Mem × List Nat × Mem) := (r₀, csS.map (·.1.toNat), runsEnd r₀ csS) ::
    ths.map fun t => (t.1, t.2.1.map (·.1.toNat), runsEnd t.1 t.2.1)
  have hincL : ∀ l : List (Word × Nat × Mem), (l.map (·.1)).Pairwise (· < ·) →
      (l.map (·.1.toNat)).Pairwise (· < ·) := fun l hl => by
    rw [List.pairwise_map] at hl ⊢
    exact hl.imp fun h => UInt64.lt_iff_toNat_lt.mp h
  have hrangeL : ∀ l : List (Word × Nat × Mem), (∀ c' ∈ l, c'.1 < khi) →
      ∀ k ∈ l.map (·.1.toNat), k < PS.dsS.size := fun l hl k hk' => by
    obtain ⟨c', hc, rfl⟩ := List.mem_map.mp hk'
    have := hl c' hc
    rw [UInt64.lt_iff_toNat_lt, hk] at this
    exact this
  have hinc' : ∀ t ∈ thsE, t.2.1.Pairwise (· < ·) := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact hincL _ hincS1
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
    exact hincL _ (hincS t₀ ht₀)
  have hrange : ∀ t ∈ thsE, ∀ k ∈ t.2.1, k < PS.dsS.size := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact hrangeL _ hcsS
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
    exact hrangeL _ (hth t₀ ht₀).2.2.2.1
  have hcov' : ∀ k < PS.dsS.size, ∃ t ∈ thsE, k ∈ t.2.1 := by
    intro k hk'
    have hk64 : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
    obtain ⟨t, ht, c', hc, hcj⟩ := hcovS (UInt64.ofNat k) (by rw [UInt64.lt_iff_toNat_lt, hk, hk64]; exact hk')
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_map_of_mem ht), List.mem_map.mpr ⟨c', hc, by rw [hcj, hk64]⟩⟩
  have hE := pool_twinE H hst thsE
    (fun t ht => by
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hstart0 _ hz hI0
      obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
      exact hstart0 _ (hth t₀ ht₀).1 (hth t₀ ht₀).2.1)
    (fun t ht => by
      rcases List.mem_cons.mp ht with rfl | ht
      · exact threadRuns_chainE B _ _ hS
      obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
      exact threadRuns_chainE B _ _ (hth t₀ ht₀).2.2.1) hinc' hrange hcov'
  have hPS : PoolJobs VM PS.ipins none PS.IS PS.dsS a' :=
    ⟨thsE.map (·.2.1),
      fun k hk' => by obtain ⟨t, ht, hkt⟩ := hcov' k hk'; exact ⟨t.2.1, List.mem_map_of_mem ht, hkt⟩,
      fun w hw k hkw => by obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hw; exact hrange t ht k hkw,
      fun w hw => by obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hw; exact hinc' t ht,
      fun w hw => by
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hw
        obtain ⟨a'', hl, -⟩ := hE t ht
        exact ⟨a'', hl⟩⟩
  -- the challenge's phase
  let J := solutionOf PS.IS res
  obtain ⟨hdfC, hindC⟩ := checkerCdG_proved pb PS.ipins (dnOf sG.store) res.toArray hpb hpre hinj
  have hcdC := checkerProg_cdProgPB pb.data.toList hr hpre hinj hq hdfC hindC
  have hJPC := checkerProg_jobProgPB pb.data.toList hr hpre hcdC (checkerProg_canonPB _)
  have hcnt : c.toNat = res.toArray.size := by simpa using h.count.1
  have hdsC : res.toArray.size < 2 ^ 63 := by
    have := h.decls.room; have := h.decls.dsize; simp only [List.size_toArray] at *; omega
  let RelC : Mem → AState → Prop := fun r a =>
    ∀ j, ThrAt PS.ipins (dnOf sG.store) res.toArray I a₀ pb.data.toList (L.Checker.seedMem (bufMem BC r j)) a (some J)
  let CallC : Nat → Mem → Mem → Prop := fun k r r' => ∃ n rs, n ≤ 2 ^ 62 ∧
    L.run checkerProg n "check" [] (bufMem BC r (UInt64.ofNat k)) = .ok (rs, r') ∧ BufKept BC r'
  obtain ⟨pinsPC, dsPC, dsSPC, matesU, hstC, hspec, hppC, hdenC, hPDC, hHC⟩ :=
    poolHypsJ_ofPI h.phase hI hPS RelC CallC
  have hRSC : RecStep PS.ipins (dnOf sG.store) res.toArray I a₀ (Prog.subPB pb.data.toList checkerProg) (some J) :=
    recCall_stepE (J := some J) hJPC ho.front (declsLpsDn_dnOf ho.pd ho.den) hdn hppC (by omega) hdenC hPDC
      hspec (fun _ => checkerProg_crsSpecPB pb.data.toList hr hpre hcdC)
  have hstepC : ∀ (k : Nat) (r r' : Mem) (a : AState) (hk : k < res.toArray.size), RelC r a → CallC k r r' →
      (∃ env, FoldOK env (I.view k) (AM.st enterScratch a)) →
      ∃ a', recordJob VM PS.ipins (some J) I k res.toArray[k] a = .ok ((), a') ∧ RelC r' a' := by
    intro k r r' a hk hR ⟨n, rs, hn, hrun, hkept⟩ hfo
    have hk' : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
    obtain ⟨⟨a', hrj, X, hJ, hPB, hX⟩, hI'⟩ := runThr hJPC.check_jobs hRSC hdsC n hn a (UInt64.ofNat k)
      (by rw [hk']; exact hk) (by rw [hk']; exact hfo) _ rfl (hR _) rfl rfl hrun
    refine ⟨a', ?_, fun j => ⟨X, hJ, hPB, fun t ht => (thr_next _ j hI' hkept (thr_ctl_next hrun) t ht).trans (hX t ht)⟩⟩
    have e : res.toArray[(UInt64.ofNat k).toNat]'(by rw [hk']; exact hk) = res.toArray[k] := by simp only [hk']
    rw [← e]; simp only [hk'] at hrj ⊢; exact hrj
  have HC := hHC hstepC
  have hKIC := indexKeysIn_of hJM9.arena.base HC.hI HC.hpI
  have hSK : SolKeysIn m9 J := solKeysIn_of hJM9.arena.base HC.hIS HC.hpIS HC.hmates
  have hJRC := JobM.fresh (hJM9.truncJ hoff hKIC (.inr (F6.extOK hF h6)) (fun J' e => by cases e; exact ⟨hSK, (F6.ext hF h6).1⟩)) hwf hoff

  have hcrs : CrsFor PS.ipins (dnOf sG.store) res.toArray (Prog.subPB pb.data.toList checkerProg) (some J) :=
    fun _ => checkerProg_crsSpecPB pb.data.toList hr hpre hcdC
  have hCE : CjStepE PS.ipins (dnOf sG.store) res.toArray I a₀ (Prog.subPB pb.data.toList checkerProg) (some J) :=
    cjStepE_ofJ hJPC ho.front (declsLpsDn_dnOf ho.pd ho.den) hdn hppC hdsC hdenC hPDC hspec hcrs
      ⟨jobG_ofDn hinj hq pb hpb hpre, crsG_checker _⟩
  -- each thread's worker state after its solution calls
  obtain ⟨wf, hlf, hRf, hwf0⟩ := hE _ List.mem_cons_self
  have hW : ∀ t : Mem × List (Word × Nat × Mem) × List (Word × Nat × Mem), ∃ w : AState, t ∈ ths →
      RelS (runsEnd t.1 t.2.1) w ∧ WorkerOK a' w := fun t => by
    by_cases ht : t ∈ ths
    · obtain ⟨w, -, hw⟩ := hE _ (List.mem_cons_of_mem _ (List.mem_map_of_mem ht))
      exact ⟨w, fun _ => hw⟩
    · exact ⟨a', fun h => absurd h ht⟩
  obtain ⟨W, hWf⟩ := Classical.axiomOfChoice hW
  let thsC : List (Mem × AState × List Nat) := ths.map fun t => (runsEnd t.1 t.2.1, W t, t.2.2.map (·.1.toNat))
  have hincC' : ∀ t ∈ thsC, t.2.2.Pairwise (· < ·) := by
    intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
    exact hincL _ (hincC t₀ ht₀)
  have hjN : j.toNat < res.toArray.size := by rw [← hcnt]; exact UInt64.lt_iff_toNat_lt.mp hj
  have hcN : ∀ c' ∈ csC, c'.1.toNat < res.toArray.size := fun c' hc => by
    have := UInt64.lt_iff_toNat_lt.mp (hcs c' hc); omega
  have hpreM := pool_prefixJW HC thsC
    (fun t ht => by
      obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
      exact ⟨fun j => c1_thrBack hV.frame hext hBS hBC hJRC.toJobM j ((hWf t₀ ht₀).1 j), (hWf t₀ ht₀).2⟩)
    (fun t ht => by
      obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
      exact threadRuns_chain BC _ _ (hth t₀ ht₀).2.2.2.2.1) hincC' j.toNat (Nat.le_of_lt hjN)
    (fun i hi => by
      have hi64 : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
      obtain ⟨t, ht, c', hc, hci⟩ := hcovC (UInt64.ofNat i) (by rw [UInt64.lt_iff_toNat_lt, hi64]; exact hi)
      exact ⟨_, List.mem_map_of_mem ht, List.mem_map.mpr ⟨c', hc, by rw [hci, hi64]⟩⟩)
  have hfold : ∀ x a, x < res.toArray.size → x ≤ j.toNat → WorkerOK a' a →
      ∃ env, FoldOK env (I.view x) (AM.st enterScratch a) := fun x a hx hxj hw => by
    obtain ⟨hx', -⟩ := HC.hden x hx
    exact worker_foldOKJ HC.hpinsOK HC.hpersPins HC.hI HC.hpI hx' (hpreM x hxj) hw
  -- the failing thread's challenge calls
  have walk : ∀ (cs : List (Word × Nat × Mem)) (r : Mem) (a : AState), RelC r a → WorkerOK a' a →
      ThreadFails BC j n e r cs → (∀ c' ∈ cs, c'.1 < j) →
      ErrClaimV (checkJobList VM PS.ipins (some J) I res.toArray (cs.map (·.1.toNat) ++ [j.toNat])) a e := by
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
      have hj' : j'.toNat < res.toArray.size := by omega
      obtain ⟨⟨a₁, hrj, X, hJ, hPB, hX⟩, hI'⟩ := runThr hJPC.check_jobs hRSC hdsC n' hn' a j' hj'
        (hfold _ a hj' (by omega) hw) _ rfl (hR _) rfl rfl hrun
      have hR' : RelC r' a₁ := fun j =>
        ⟨X, hJ, hPB, fun t ht => (thr_next _ j hI' hkept (thr_ctl_next hrun) t ht).trans (hX t ht)⟩
      obtain ⟨hx', hdk⟩ := HC.hden _ hj'
      obtain ⟨hw', -⟩ := job_specC HC.hrec HC.hpp HC.hpinsOK HC.hpersPins HC.hpins HC.hpd HC.hI
        HC.hpI HC.hIS HC.hpIS HC.hndS HC.hmates hw hj' hx' hdk (hpreM j'.toNat (by omega)) hrj
      exact ErrClaimV.cons_ok hj' hrj
        (ih r' a₁ hR' hw' hrest fun c hc' => hc c (List.mem_cons_of_mem _ hc'))
  have hWk := walk csC (runsEnd r₀ csS) wf (fun j => c1_thrBack hV.frame hext hBS hBC hJRC.toJobM j (hRf j)) hwf0
    hruns hcs
  refine .inr (.inr ⟨PS.pins, PS.ipins, PS.dsS, res, PS.IS, I, a', wf, csS.map (·.1.toNat),
    csC.map (·.1.toNat) ++ [j.toNat], h.stagesI hI, hPS, hrangeL _ hcsS, fun t ht => ?_, hlf, hWk hk0⟩)
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨c', hc, rfl⟩ := List.mem_map.mp ht
    simpa using hcN c' hc
  · rw [List.mem_singleton.mp ht]; simpa using hjN

end ConAgua.Final
