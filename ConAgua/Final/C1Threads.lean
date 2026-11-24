module

public import ConAgua.Checker.C1Back
public import ConAgua.Arena.C1Pool
public import ConAgua.Final.CpThreads
import ConAgua.Checker.CmpThreadsC
import ConAgua.Checker.CmpSPhaseT
import ConAgua.Checker.CrsProgPB
import ConAgua.Checker.RomProgInit
import ConAgua.Checker.JobsProg
import ConAgua.Arena.FreezeFresh
import ConRon.Bridge.Compare.Mates
import ConAgua.Checker.C1Hdr
public import ConAgua.Checker.CmpSPhase
import ConAgua.Checker.CompareChain6J
public import ConAgua.Arena.FreezeView
import ConAgua.Final.CmpChain
public import ConAgua.Final.CompareTwin
import ConRon.Bridge.Checker.Install
import ConAgua.Checker.ArmsT
import ConAgua.Checker.LoopProg

@[expose] public section

/-!
# The threaded compared run's threads, both phases on one region (lane compare2, H7)

Each thread runs its solution calls over header S from a fresh region, then its challenge calls
over header C on the region as they left it.

* `c1_solPhase`: the solution's phase per thread (`pool_twinE`): each thread's list accepted from
  `sI.worker`, ending in a worker state where the thread's region is the solution's jobs' relation
  with `c1Q` (what the solution's jobs keep), and the twin's pool of the solution's jobs.
* `c1Thr_accepts`: then the switch (`c1_thrBack`) and the challenge's phase from each thread's end
  (`pool_twinJW`): `TwinComparesAcceptsPooled`.
-/

open ConRon.Arena ConRon.Bridge

namespace ConAgua.Final

open L L.Compiler L.Checker L.Arena L.Rom

local notation "VM" => ConLeche.CheckMode.verified

/-- A thread's calls as a chain with its end (`runsEnd`). -/
theorem threadRuns_chainE (B : Array Word) :
    ∀ (cs : List (Word × Nat × Mem)) (r : Mem), ThreadRuns B r cs →
      JobChainE (fun k r r' => ∃ n rs, n ≤ 2 ^ 62 ∧
        L.run checkerProg n "check" [] (bufMem B r (UInt64.ofNat k)) = .ok (rs, r') ∧ BufKept B r')
        r (cs.map (·.1.toNat)) (runsEnd r cs)
  | [], r, _ => .nil r
  | (j, n, r') :: cs, r, ⟨hn, ⟨rs, hrun⟩, hkept, hrest⟩ =>
    .cons ⟨n, rs, hn, by rw [UInt64.ofNat_toNat]; exact hrun, hkept⟩ (threadRuns_chainE B cs r' hrest)

theorem c1_rdW_fresh (m : Mem) {x : Word} (hx : x.toNat < 256) :
    rdW ((freshMem m).arr64 CTL) x = rdW (m.arr64 CTL) x := by
  rw [c1_rdW, c1_rdW, freshMem_arr, ite_eq_left rfl, truncFrozen_ctl, getD_freshCtl, ite_eq_left hx]

/-- **Both phases' threads on one region accept ⇒ the twin's threaded comparison accepts.** -/
theorem c1Thr_accepts {bC bS pb : ByteArray} (hpb : pb.size < 2 ^ 63) (PS : PhaseS bC bS)
    {m₇ m : Mem} (hF : FoldOn bS pb (abiSz checkerTab) PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m)
    {c : Word} {m9 mS : Mem} (h6 : F6 PS m c m9) (hb9 : m9.bytes = m.bytes) (hV : CsViewS m m9 mS)
    (B : Array Word) (hBS : HdrView B mS) (khi : Word) (hk : khi.toNat = PS.dsS.size)
    (BC : Array Word) (hBC : HdrView BC m9)
    (hext : ∀ i < frozen.length, fzExt mS (fzAt i) = fzExt m9 (fzAt i))
    (ths : List (Mem × List (Word × Nat × Mem) × List (Word × Nat × Mem)))
    (hth : ∀ t ∈ ths, (∀ b ∈ parOwnedL, t.1.arr64 b = zeros (mS.arr64 b).size) ∧ t.1.glob INIT = 0 ∧
      ThreadRuns B t.1 t.2.1 ∧ (∀ c' ∈ t.2.1, c'.1 < khi) ∧
      ThreadRuns BC (runsEnd t.1 t.2.1) t.2.2 ∧ ∀ c' ∈ t.2.2, c'.1 < c)
    (hcovS : ∀ j : Word, j < khi → ∃ t ∈ ths, ∃ c' ∈ t.2.1, c'.1 = j)
    (hcovC : ∀ j : Word, j < c → ∃ t ∈ ths, ∃ c' ∈ t.2.2, c'.1 = j)
    (hincS : ∀ t ∈ ths, (t.2.1.map (·.1)).Pairwise (· < ·))
    (hincC : ∀ t ∈ ths, (t.2.2.map (·.1)).Pairwise (· < ·)) :
    TwinComparesAcceptsPooled bC bS := by
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
  let thsE : List (Mem × List Nat × Mem) := ths.map fun t => (t.1, t.2.1.map (·.1.toNat), runsEnd t.1 t.2.1)
  have hinc' : ∀ t ∈ thsE, t.2.1.Pairwise (· < ·) := by
    intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
    have := hincS t₀ ht₀
    rw [List.pairwise_map] at this ⊢
    exact this.imp fun h => UInt64.lt_iff_toNat_lt.mp h
  have hrange : ∀ t ∈ thsE, ∀ k ∈ t.2.1, k < PS.dsS.size := by
    intro t ht k hk'
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
    obtain ⟨c', hc, rfl⟩ := List.mem_map.mp hk'
    have := (hth t₀ ht₀).2.2.2.1 c' hc
    rw [UInt64.lt_iff_toNat_lt, hk] at this
    exact this
  have hcov' : ∀ k < PS.dsS.size, ∃ t ∈ thsE, k ∈ t.2.1 := by
    intro k hk'
    have hk64 : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
    obtain ⟨t, ht, c', hc, hcj⟩ := hcovS (UInt64.ofNat k) (by rw [UInt64.lt_iff_toNat_lt, hk, hk64]; exact hk')
    exact ⟨_, List.mem_map_of_mem ht, List.mem_map.mpr ⟨c', hc, by rw [hcj, hk64]⟩⟩
  have hE := pool_twinE H hst thsE
    (fun t ht => by
      obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
      exact hstart0 _ (hth t₀ ht₀).1 (hth t₀ ht₀).2.1)
    (fun t ht => by
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
  -- each thread's worker state after its solution calls
  have hW : ∀ t : Mem × List (Word × Nat × Mem) × List (Word × Nat × Mem), ∃ w : AState, t ∈ ths →
      checkJobList VM PS.ipins none PS.IS PS.dsS (t.2.1.map (·.1.toNat)) a'.worker = .ok (.ok (), w) ∧
        RelS (runsEnd t.1 t.2.1) w ∧ WorkerOK a' w := fun t => by
    by_cases ht : t ∈ ths
    · obtain ⟨w, hw⟩ := hE _ (List.mem_map_of_mem ht)
      exact ⟨w, fun _ => hw⟩
    · exact ⟨a', fun h => absurd h ht⟩
  obtain ⟨W, hWf⟩ := Classical.axiomOfChoice hW
  let thsC : List (Mem × AState × List Nat) := ths.map fun t => (runsEnd t.1 t.2.1, W t, t.2.2.map (·.1.toNat))
  have hincC' : ∀ t ∈ thsC, t.2.2.Pairwise (· < ·) := by
    intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
    have := hincC t₀ ht₀
    rw [List.pairwise_map] at this ⊢
    exact this.imp fun h => UInt64.lt_iff_toNat_lt.mp h
  have hrangeC : ∀ t ∈ thsC, ∀ k ∈ t.2.2, k < res.toArray.size := by
    intro t ht k hk'
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
    obtain ⟨c', hc, rfl⟩ := List.mem_map.mp hk'
    have := (hth t₀ ht₀).2.2.2.2.2 c' hc
    rw [UInt64.lt_iff_toNat_lt, hcnt] at this
    exact this
  have hcovC' : ∀ k < res.toArray.size, ∃ t ∈ thsC, k ∈ t.2.2 := by
    intro k hk'
    have hk64 : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
    obtain ⟨t, ht, c', hc, hcj⟩ := hcovC (UInt64.ofNat k) (by rw [UInt64.lt_iff_toNat_lt, hcnt, hk64]; exact hk')
    exact ⟨_, List.mem_map_of_mem ht, List.mem_map.mpr ⟨c', hc, by rw [hcj, hk64]⟩⟩
  have hacc := pool_twinJW HC thsC
    (fun t ht => by
      obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
      exact ⟨fun j => c1_thrBack hV.frame hext hBS hBC hJRC.toJobM j ((hWf t₀ ht₀).2.1 j), (hWf t₀ ht₀).2.2⟩)
    (fun t ht => by
      obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
      exact threadRuns_chain BC _ _ (hth t₀ ht₀).2.2.2.2.1) hincC' hrangeC hcovC'
  refine ⟨PS.pins, PS.ipins, PS.dsS, res, PS.IS, I, a', h.stagesI hI,
    ths.map fun t => (t.2.1.map (·.1.toNat), t.2.2.map (·.1.toNat)), fun k hk' => ?_, fun k hk' => ?_,
    fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · obtain ⟨t, ht, hkt⟩ := hcov' k hk'
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
    exact ⟨_, List.mem_map_of_mem ht₀, hkt⟩
  · obtain ⟨t, ht, hkt⟩ := hcovC' k hk'
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
    exact ⟨_, List.mem_map_of_mem ht₀, hkt⟩
  · obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp hq
    exact ⟨hrange _ (List.mem_map_of_mem ht₀), hrangeC _ (List.mem_map_of_mem ht₀)⟩
  · obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp hq
    exact ⟨hinc' _ (List.mem_map_of_mem ht₀), hincC' _ (List.mem_map_of_mem ht₀)⟩
  · obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp hq
    obtain ⟨w', hw'⟩ := hacc _ (List.mem_map_of_mem ht₀)
    exact ⟨W t₀, w', ((hWf t₀ ht₀).1), hw'⟩

end ConAgua.Final
