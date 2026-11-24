module

public import ConAgua.Final.CmpChainC
public import ConAgua.Checker.ParThreadTwin
public import ConAgua.Checker.CmpSPhase
public import ConAgua.Checker.CmpSPhaseT
import ConAgua.Checker.CmpThreadsC
import ConAgua.Checker.CmpThreadsPool
import ConAgua.Checker.CrsProgPB
import ConAgua.Checker.RomProgInit
import ConAgua.Checker.JobsProg
import ConAgua.Checker.CheckARun
import ConAgua.Checker.AsmFinal
import ConAgua.Arena.FreezeFresh
import ConAgua.Arena.FreezeTrunc
import ConAgua.Arena.JobStart
import ConAgua.Arena.LoopStart
import ConRon.Bridge.Compare.Mates

@[expose] public section

/-!
# Both phases' threads from the challenge's index state (lane compare2, design (i))

The compared run's one frozen image after mode `6`'s steps (`F6`, memory `m9`), read through two
headers: header C's view is `m9`, header S's view is `CsViewS m m9 mS`. A buffer `B` whose first
call agrees with a memory's fresh worker memory (`CsFirst B mS`, what a header's view gives)
starts every thread in the jobs' relation.

* `Side6.uniq`, `F6.jobMAt`: the challenge's job memory half at any witnesses of the steps.
* `cmpThreadsS_poolI`: threads over header S's view whose calls claim every solution record give
  the twin's pool of the solution's jobs from `sI` (`PoolJobs … none IS dsS sI`).
* `cmpThreadsC_poolI`: threads over header C's view, given the solution's pool from `sI`, give
  the twin's pool of the challenge's jobs from `sI` at the solution.
-/

open ConRon.Arena ConRon.Bridge

namespace ConAgua.Final

open L L.Compiler L.Checker L.Arena L.Rom

local notation "VM" => ConLeche.CheckMode.verified

/-- **A buffer's first call starts at a memory's fresh worker memory**: from a fresh region (`INIT
= 0`, every owned array zero at its size in `m`), the memory after `check_b`'s seed copy on
`bufMem B r j` agrees with `freshMem m` on `thrS` (`thr_first` for `bufOf m`). -/
def CsFirst (B : Array Word) (m : Mem) : Prop :=
  ∀ (r : Mem) (j : Word), (∀ b ∈ parOwnedL, r.arr64 b = zeros (m.arr64 b).size) → r.glob INIT = 0 →
    ∀ t, thrS t = true → (seedMem (bufMem B r j)).arr64 t = (freshMem m).arr64 t

theorem csFirst_bufOf {m : Mem} (hok : parCompactOK m 1 = true) (hlt : (m.arr64 OUT).size < 2 ^ 64) :
    CsFirst (bufOf m) m := fun r j hz hI => thr_first hok hlt r j hz hI

section
variable {bC bS : ByteArray} {PS : PhaseS bC bS} {m : Mem} {c : Word}

/-- **Mode `6`'s steps are deterministic on the twin's side**: the preparation's records and state
and the side records. -/
theorem _root_.L.Checker.Side6.uniq {m2 m3 m2' m3' m4 m4' : Mem} {dsC dsC' : Array IDeclaration} {sG sG' : AState}
    {res res' : List IDeclaration} (h : Side6 PS m c m2 m3 dsC sG res m4)
    (h' : Side6 PS m c m2' m3' dsC' sG' res' m4') : dsC' = dsC ∧ sG' = sG ∧ res' = res := by
  have e := h.prep.run.symm.trans h'.prep.run
  simp only [Except.ok.injEq, Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  have e2 := h.run.symm.trans h'.run
  simp only [Except.ok.injEq, Prod.mk.injEq] at e2
  exact ⟨rfl, rfl, e2.1.symm⟩

/-- **The challenge's job memory half at given witnesses of mode `6`'s steps** (`F6.jobM`). -/
theorem _root_.L.Checker.F6.jobMAt {pb : ByteArray} {sz : TieredArray → Nat} {m₇ : Mem}
    (hF : FoldOn bS pb sz PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m) {m9 : Mem} (h6 : F6 PS m c m9)
    {m2 m3 m4 : Mem} {dsC : Array IDeclaration} {sG : AState} {res : List IDeclaration}
    {I : IStreamIndex} {a' : AState}
    (h : Side6 PS m c m2 m3 dsC sG res m4) (hI : buildIndex res.toArray sG = .ok (.ok I, a')) :
    JobM PS.ipins (dnOf sG.store) res.toArray (some (solutionOf PS.IS res)) I m9 a' ∧
      StoreWF a'.store ∧ a'.store.scratchOn = false ∧ ∀ t, (m9.arr64 t).size = (m.arr64 t).size := by
  obtain ⟨m2', m3', dsC', sG', res', m4', I', a'', h', hI', hJM, hwf, hoff, hsz⟩ := F6.jobM hF h6
  obtain ⟨-, rfl, rfl⟩ := h.uniq h'
  rw [hI] at hI'
  simp only [Except.ok.injEq, Prod.mk.injEq] at hI'
  obtain ⟨rfl, rfl⟩ := hI'
  exact ⟨hJM, hwf, hoff, hsz⟩

end

/-- **The solution's threads at the challenge's index state accept ⇒ the twin's pool of the
solution's jobs from `sI` accepts.** After the solution's index build (`FoldOn`) and mode `6`'s
steps (`F6`: the frozen memory `m9`, the challenge's index build ending in `a'`), header S's view
`mS` of `m9` (`CsViewS`), a buffer `B` whose first
call is `mS`'s fresh memory, threads on `B`, each a fresh region running its calls, every job index
below `khi` (the solution's record count) claimed, each thread's claims increasing. -/
theorem cmpThreadsS_poolI {bC bS pb : ByteArray} (hpb : pb.size < 2 ^ 63) (PS : PhaseS bC bS) {m₇ m : Mem}
    (hF : FoldOn bS pb (abiSz checkerTab) PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m)
    {c : Word} {m9 mS : Mem} (h6 : F6 PS m c m9) (hb9 : m9.bytes = m.bytes)
    {m2 m3 m4 : Mem} {dsC : Array IDeclaration} {sG : AState} {res : List IDeclaration}
    {I : IStreamIndex} {a' : AState}
    (h : Side6 PS m c m2 m3 dsC sG res m4) (hI : buildIndex res.toArray sG = .ok (.ok I, a'))
    (hV : CsViewS m m9 mS)
    (B : Array Word) (hB : CsFirst B mS) (khi : Word) (hk : khi.toNat = PS.dsS.size)
    (ths : List (Mem × List (Word × Nat × Mem)))
    (hth : ∀ t ∈ ths, (∀ b ∈ parOwnedL, t.1.arr64 b = zeros (mS.arr64 b).size) ∧ t.1.glob INIT = 0 ∧
      ThreadRuns B t.1 t.2 ∧ ∀ c' ∈ t.2, c'.1 < khi)
    (hcov : ∀ j : Word, j < khi → ∃ t ∈ ths, ∃ c' ∈ t.2, c'.1 = j)
    (hinc : ∀ t ∈ ths, (t.2.map (·.1)).Pairwise (· < ·)) :
    PoolJobs VM PS.ipins none PS.IS PS.dsS a' := by
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
  have hds : PS.dsS.size < 2 ^ 63 := by
    have := hF.build.decls.room; have := hF.build.decls.dsize; omega
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
  have hRS : RecStep PS.ipins (dnOf sG.store) PS.dsS PS.IS a₀ (Prog.subPB pb.data.toList checkerProg) :=
    recCall_stepE (J := none) hJP hoS.front hLD hdn hpp (by omega) hden hPD hrec
      (fun h => absurd h (by simp))
  have hstep : ∀ (k : Nat) (r r' : Mem) (a : AState) (hk : k < PS.dsS.size), Rel r a → Call k r r' →
      (∃ env, FoldOK env (PS.IS.view k) (AM.st enterScratch a)) →
      ∃ a', recordJob VM PS.ipins none PS.IS k PS.dsS[k] a = .ok ((), a') ∧ Rel r' a' := by
    intro k r r' a hk hR ⟨n, rs, hn, hrun, hkept⟩ hfo
    have hk' : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
    obtain ⟨⟨a', hrj, X, hJ, hPB, hX⟩, hI'⟩ := runThr hJP.check_jobs hRS hds n hn a (UInt64.ofNat k)
      (by rw [hk']; exact hk) (by rw [hk']; exact hfo) _ rfl (hR _) rfl rfl hrun
    refine ⟨a', ?_, fun j => ⟨X, hJ, hPB, fun t ht => (thr_next _ j hI' hkept t ht).trans (hX t ht)⟩⟩
    have e : PS.dsS[(UInt64.ofNat k).toNat]'(by rw [hk']; exact hk) = PS.dsS[k] := by simp only [hk']
    rw [← e]; simp only [hk'] at hrj ⊢; exact hrj
  have H := hH hstep
  -- the threads' starts
  let ths' : List (Mem × List Nat) := ths.map fun t => (t.1, t.2.map (·.1.toNat))
  have hstart : ∀ t ∈ ths', Rel t.1 a'.worker := by
    intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
    obtain ⟨hz, hI0, -, -⟩ := hth t₀ ht₀
    intro j
    have hKI := indexKeysIn_of hJM.arena.base H.hI H.hpI
    have hJR := JobM.fresh (hJM.trunc hoff hKI) hwf hoff
    refine ⟨freshMem mS, ⟨_, ⟨hJR, PExt.of_ext (Ext.refl _), rfl⟩, ?_⟩, ?_, ?_⟩
    · exact ⟨by simp [AState.worker, estore_dropScratch_self hwf hoff], rfl, rfl⟩
    · rw [freshMem_arr8]
      show mS.bytes L.Rom.PB = _
      rw [hV.bytes, hb9, hF.bytes, ← Mem.arr8, hF.r7.since.keep.arr8]; exact loadMem_pb bS pb _
    · exact hB t₀.1 j hz hI0
  have hchain : ∀ t ∈ ths', JobChain Call t.1 t.2 := by
    intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
    exact threadRuns_chain B _ _ (hth t₀ ht₀).2.2.1
  have hinc' : ∀ t ∈ ths', t.2.Pairwise (· < ·) := by
    intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
    have := hinc t₀ ht₀
    rw [List.pairwise_map] at this ⊢
    exact this.imp fun h => UInt64.lt_iff_toNat_lt.mp h
  have hrange : ∀ t ∈ ths', ∀ k ∈ t.2, k < PS.dsS.size := by
    intro t ht k hk'
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
    obtain ⟨c', hc, rfl⟩ := List.mem_map.mp hk'
    have := (hth t₀ ht₀).2.2.2 c' hc
    rw [UInt64.lt_iff_toNat_lt, hk] at this
    exact this
  have hcov' : ∀ k < PS.dsS.size, ∃ t ∈ ths', k ∈ t.2 := by
    intro k hk'
    have hk64 : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
    obtain ⟨t, ht, c', hc, hcj⟩ := hcov (UInt64.ofNat k) (by rw [UInt64.lt_iff_toNat_lt, hk, hk64]; exact hk')
    exact ⟨_, List.mem_map_of_mem ht, List.mem_map.mpr ⟨c', hc, by rw [hcj, hk64]⟩⟩
  obtain ⟨-, hacc⟩ := pool_twin H hst ths' hstart hchain hinc' hrange hcov'
  exact ⟨ths'.map (·.2),
    fun k hk' => by obtain ⟨t, ht, hkt⟩ := hcov' k hk'; exact ⟨t.2, List.mem_map_of_mem ht, hkt⟩,
    fun w hw k hkw => by obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hw; exact hrange t ht k hkw,
    fun w hw => by obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hw; exact hinc' t ht,
    fun w hw => by obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hw; exact hacc t ht⟩

/-- **The challenge's threads at the challenge's index state accept, after the solution's pool
from there ⇒ the twin's pool of the challenge's jobs from `sI` at the solution accepts.** After
the solution's index build (`FoldOn`) and mode `6`'s steps (`F6`: the frozen memory `m9`, header
C's view, the challenge's index build ending in `a'`), the solution's pool from `a'`, a buffer `B`
whose first call is `m9`'s fresh memory, threads on `B`, each a fresh region running its calls,
every job index below `c` (the challenge's record count) claimed, each thread's claims increasing. -/
theorem cmpThreadsC_poolI {bC bS pb : ByteArray} (hpb : pb.size < 2 ^ 63) (PS : PhaseS bC bS) {m₇ m : Mem}
    (hF : FoldOn bS pb (abiSz checkerTab) PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m)
    {c : Word} {m9 : Mem} (h6 : F6 PS m c m9) (hb9 : m9.bytes = m.bytes)
    {m2 m3 m4 : Mem} {dsC : Array IDeclaration} {sG : AState} {res : List IDeclaration}
    {I : IStreamIndex} {a' : AState}
    (h : Side6 PS m c m2 m3 dsC sG res m4) (hI : buildIndex res.toArray sG = .ok (.ok I, a'))
    (hPS : PoolJobs VM PS.ipins none PS.IS PS.dsS a')
    (B : Array Word) (hB : CsFirst B m9)
    (ths : List (Mem × List (Word × Nat × Mem)))
    (hth : ∀ t ∈ ths, (∀ b ∈ parOwnedL, t.1.arr64 b = zeros (m9.arr64 b).size) ∧ t.1.glob INIT = 0 ∧
      ThreadRuns B t.1 t.2 ∧ ∀ c' ∈ t.2, c'.1 < c)
    (hcov : ∀ j : Word, j < c → ∃ t ∈ ths, ∃ c' ∈ t.2, c'.1 = j)
    (hinc : ∀ t ∈ ths, (t.2.map (·.1)).Pairwise (· < ·)) :
    PoolJobs VM PS.ipins (some (solutionOf PS.IS res)) I res.toArray a' := by
  obtain ⟨hJM, hwf, hoff, -⟩ := F6.jobMAt hF h6 h hI
  obtain ⟨-, -, -, -, ho⟩ := h.phase.out
  let J := solutionOf PS.IS res
  -- the program facts
  have hr : RomOK pb.data.toList := by simpa [RomOK] using hpb
  have hpre := hF.r7.since.pbpre
  have hinj : L.Ind.DnInj (dnOf sG.store) := dnOf_inj ho.drv.state.wf
  have hq : L.Ind.QuotDn (dnOf sG.store) := by
    obtain ⟨k, hk, hd⟩ := ho.quot
    exact ⟨k, by simp only [dnOf, hk]; exact hd⟩
  obtain ⟨hdf, hind⟩ := checkerCdG_proved pb PS.ipins (dnOf sG.store) res.toArray hpb hpre hinj
  have hcd := checkerProg_cdProgPB pb.data.toList hr hpre hinj hq hdf hind
  have hJP := checkerProg_jobProgPB pb.data.toList hr hpre hcd (checkerProg_canonPB _)
  have hcnt : c.toNat = res.toArray.size := by simpa using h.count.1
  have hds : res.toArray.size < 2 ^ 63 := by
    have := h.decls.room; have := h.decls.dsize; simp only [List.size_toArray] at *; omega
  -- the twin's side
  let a₀ : AState := { a' with caches := Caches.empty }
  let Rel : Mem → AState → Prop := fun r a =>
    ∀ j, ThrAt PS.ipins (dnOf sG.store) res.toArray I a₀ pb.data.toList (seedMem (bufMem B r j)) a (some J)
  let Call : Nat → Mem → Mem → Prop := fun k r r' => ∃ n rs, n ≤ 2 ^ 62 ∧
    L.run checkerProg n "check" [] (bufMem B r (UInt64.ofNat k)) = .ok (rs, r') ∧ BufKept B r'
  obtain ⟨pinsP, dsP, dsSP, matesU, hst, hspec, hpp, hden, hPD, hH⟩ :=
    poolHypsJ_ofPI h.phase hI hPS Rel Call
  have hdn : DnPers (dnOf sG.store) := fun k x hk => by
    simp only [dnOf] at hk; split at hk
    · assumption
    · cases hk
  have hRS : RecStep PS.ipins (dnOf sG.store) res.toArray I a₀ (Prog.subPB pb.data.toList checkerProg) (some J) :=
    recCall_stepE (J := some J) hJP ho.front (declsLpsDn_dnOf ho.pd ho.den) hdn hpp (by omega) hden hPD
      hspec (fun _ => checkerProg_crsSpecPB pb.data.toList hr hpre hcd)
  have hstep : ∀ (k : Nat) (r r' : Mem) (a : AState) (hk : k < res.toArray.size), Rel r a → Call k r r' →
      (∃ env, FoldOK env (I.view k) (AM.st enterScratch a)) →
      ∃ a', recordJob VM PS.ipins (some J) I k res.toArray[k] a = .ok ((), a') ∧ Rel r' a' := by
    intro k r r' a hk hR ⟨n, rs, hn, hrun, hkept⟩ hfo
    have hk' : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
    obtain ⟨⟨a', hrj, X, hJ, hPB, hX⟩, hI'⟩ := runThr hJP.check_jobs hRS hds n hn a (UInt64.ofNat k)
      (by rw [hk']; exact hk) (by rw [hk']; exact hfo) _ rfl (hR _) rfl rfl hrun
    refine ⟨a', ?_, fun j => ⟨X, hJ, hPB, fun t ht => (thr_next _ j hI' hkept t ht).trans (hX t ht)⟩⟩
    have e : res.toArray[(UInt64.ofNat k).toNat]'(by rw [hk']; exact hk) = res.toArray[k] := by simp only [hk']
    rw [← e]; simp only [hk'] at hrj ⊢; exact hrj
  have H := hH hstep
  -- the threads' starts
  let ths' : List (Mem × List Nat) := ths.map fun t => (t.1, t.2.map (·.1.toNat))
  have hstart : ∀ t ∈ ths', Rel t.1 a'.worker := by
    intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
    obtain ⟨hz, hI0, -, -⟩ := hth t₀ ht₀
    intro j
    have hKI := indexKeysIn_of hJM.arena.base H.hI H.hpI
    have hSK : SolKeysIn m9 J := solKeysIn_of hJM.arena.base H.hIS H.hpIS H.hmates
    have hJR := JobM.fresh (hJM.truncJ hoff hKI (fun J' e => by cases e; exact hSK)) hwf hoff
    refine ⟨freshMem m9, ⟨_, ⟨hJR, PExt.of_ext (Ext.refl _), rfl⟩, ?_⟩, ?_, ?_⟩
    · exact ⟨by simp [AState.worker, estore_dropScratch_self hwf hoff], rfl, rfl⟩
    · rw [freshMem_arr8]
      show m9.bytes L.Rom.PB = _
      rw [hb9, hF.bytes, ← Mem.arr8, hF.r7.since.keep.arr8]; exact loadMem_pb bS pb _
    · exact hB t₀.1 j hz hI0
  have hchain : ∀ t ∈ ths', JobChain Call t.1 t.2 := by
    intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
    exact threadRuns_chain B _ _ (hth t₀ ht₀).2.2.1
  have hinc' : ∀ t ∈ ths', t.2.Pairwise (· < ·) := by
    intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
    have := hinc t₀ ht₀
    rw [List.pairwise_map] at this ⊢
    exact this.imp fun h => UInt64.lt_iff_toNat_lt.mp h
  have hrange : ∀ t ∈ ths', ∀ k ∈ t.2, k < res.toArray.size := by
    intro t ht k hk'
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
    obtain ⟨c', hc, rfl⟩ := List.mem_map.mp hk'
    have := (hth t₀ ht₀).2.2.2 c' hc
    rw [UInt64.lt_iff_toNat_lt, hcnt] at this
    exact this
  have hcov' : ∀ k < res.toArray.size, ∃ t ∈ ths', k ∈ t.2 := by
    intro k hk'
    have hk64 : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
    obtain ⟨t, ht, c', hc, hcj⟩ := hcov (UInt64.ofNat k) (by rw [UInt64.lt_iff_toNat_lt, hcnt, hk64]; exact hk')
    exact ⟨_, List.mem_map_of_mem ht, List.mem_map.mpr ⟨c', hc, by rw [hcj, hk64]⟩⟩
  have hacc := pool_twinJT H hst ths' hstart hchain hinc' hrange hcov'
  exact ⟨ths'.map (·.2),
    fun k hk' => by obtain ⟨t, ht, hkt⟩ := hcov' k hk'; exact ⟨t.2, List.mem_map_of_mem ht, hkt⟩,
    fun w hw k hkw => by obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hw; exact hrange t ht k hkw,
    fun w hw => by obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hw; exact hinc' t ht,
    fun w hw => by obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hw; exact hacc t ht⟩

/-- **The stages of the compared run up to the challenge's index build**, from mode `6`'s steps. -/
theorem _root_.L.Checker.Side6.stagesI {bC bS : ByteArray} {PS : PhaseS bC bS} {m : Mem} {c : Word}
    {m2 m3 m4 : Mem} {dsC : Array IDeclaration} {sG : AState} {res : List IDeclaration}
    {I : IStreamIndex} {a' : AState}
    (h : Side6 PS m c m2 m3 dsC sG res m4) (hI : buildIndex res.toArray sG = .ok (.ok I, a')) :
    CmpStagesI bC bS PS.pins PS.ipins PS.dsS res PS.IS I a' := by
  obtain ⟨⟨hA, hB, hC'⟩, hCS, hDS⟩ := PS.pfx
  exact ⟨PS.sA, PS.sB, PS.sC, PS.sC', PS.sD, PS.sE, PS.sF, sG, sG, PS.pre, PS.rC, PS.rS, dsC,
    hA, hB, hC', hCS, hDS, PS.pinsR, PS.idx, h.prep.run, h.run, hI⟩

/-- **Both phases' threads accept ⇒ the twin's pooled comparison from one state accepts**
(`cmpThreadsS_poolI`, then `cmpThreadsC_poolI`). -/
theorem cmpThreads_twinPooledI {bC bS pb : ByteArray} (hpb : pb.size < 2 ^ 63) (PS : PhaseS bC bS)
    {m₇ m : Mem} (hF : FoldOn bS pb (abiSz checkerTab) PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m)
    {c : Word} {m9 mS : Mem} (h6 : F6 PS m c m9) (hb9 : m9.bytes = m.bytes)
    (hV : CsViewS m m9 mS)
    (BS : Array Word) (hBS : CsFirst BS mS) (khi : Word) (hk : khi.toNat = PS.dsS.size)
    (thsS : List (Mem × List (Word × Nat × Mem)))
    (hthS : ∀ t ∈ thsS, (∀ b ∈ parOwnedL, t.1.arr64 b = zeros (mS.arr64 b).size) ∧ t.1.glob INIT = 0 ∧
      ThreadRuns BS t.1 t.2 ∧ ∀ c' ∈ t.2, c'.1 < khi)
    (hcovS : ∀ j : Word, j < khi → ∃ t ∈ thsS, ∃ c' ∈ t.2, c'.1 = j)
    (hincS : ∀ t ∈ thsS, (t.2.map (·.1)).Pairwise (· < ·))
    (BC : Array Word) (hBC : CsFirst BC m9)
    (thsC : List (Mem × List (Word × Nat × Mem)))
    (hthC : ∀ t ∈ thsC, (∀ b ∈ parOwnedL, t.1.arr64 b = zeros (m9.arr64 b).size) ∧ t.1.glob INIT = 0 ∧
      ThreadRuns BC t.1 t.2 ∧ ∀ c' ∈ t.2, c'.1 < c)
    (hcovC : ∀ j : Word, j < c → ∃ t ∈ thsC, ∃ c' ∈ t.2, c'.1 = j)
    (hincC : ∀ t ∈ thsC, (t.2.map (·.1)).Pairwise (· < ·)) :
    TwinComparesAcceptsPooledI bC bS := by
  obtain ⟨m2, m3, dsC, sG, res, m4, I, a', h, hI, -⟩ := F6.jobM hF h6
  have hPS := cmpThreadsS_poolI hpb PS hF h6 hb9 h hI hV BS hBS khi hk thsS hthS hcovS hincS
  have hPC := cmpThreadsC_poolI hpb PS hF h6 hb9 h hI hPS BC hBC thsC hthC hcovC hincC
  obtain ⟨sA, sB, sC, sC', sD, sE, sF, sG', sH, pre, rC, rS, dsC', hA, hB, hC', hCS, hDS, hE, hIS,
    hDC, hside, hIC⟩ := h.stagesI hI
  exact ⟨PS.pins, sA, sB, sC, sC', sD, sE, sF, sG', sH, a', pre, rC, rS, PS.dsS, dsC', res, PS.ipins,
    PS.IS, I, hA, hB, hC', hCS, hDS, hE, hIS, hDC, hside, hIC, hPS, hPC⟩

end ConAgua.Final
