module

public import ConAgua.Final.CmpChainC
public import ConAgua.Checker.ParThreadTwin
import ConAgua.Checker.CmpThreadsPool
import ConAgua.Checker.CrsProgPB
import ConAgua.Checker.RomProgInit
import ConAgua.Checker.JobsProg
import ConAgua.Checker.CheckARun
import ConAgua.Checker.AsmFinal
import ConAgua.Arena.FreezeFresh
import ConAgua.Arena.FreezeTrunc
import ConAgua.Arena.JobStart
import ConRon.Bridge.Compare.Mates

@[expose] public section

/-!
# The challenge's threads (lane compare2)

The threaded compared run's challenge phase at the L level: after mode `7` (`F6`, then
`par_compact(1)`: the challenge's frozen buffer, with the solution's rows), threads whose calls of
entry 2 claim every challenge record give the twin's pool with the solution (`PooledAcceptsJ`), as
`threads_pooledO` (`Checker/ParThreadTwin.lean`) does for the flat run:

* `solKeysIn_of`: the solution's keys (its index's and its mates') are tier-0 names below the
  name counts, from the twin's facts (`indexKeysIn_of`, `MatesRel`).
* `cmpThreadsC_pooledJ`: each thread starts at the fresh memory (`JobM.truncJ`, `JobM.fresh` at
  the solution), its calls are the pool's steps (`runThr` at the solution), and the pool with a
  solution (`pool_twinJT`) gives every thread's claims accepted.
-/

open ConRon.Arena ConRon.Bridge

namespace L.Arena

/-- **The solution's keys in the store** (`SolKeysIn`), from its index denoting persistently and its
mates related (`MatesRel`: every key persistent and denoting). -/
theorem solKeysIn_of {m : Mem} {a : AState} {J : ISolution} {dsS : List ConLeche.Declaration}
    {matesU : Std.HashMap ConLeche.Name (Array ConLeche.Name)} (hR : ArenaR m a)
    (hIS : IndexDenotes a.store J.idx (ConLeche.Cached.buildIndex dsS.toArray))
    (hpIS : PersIFBase J.idx.base) (hmt : MatesRel a.store J.mates matesU) : SolKeysIn m J :=
  ⟨indexKeysIn_of hR hIS hpIS, fun n l e hn => by
    obtain ⟨nm, hdn, -⟩ := hmt.cover n l e
    exact nameIn_of hR (hmt.pers n l e).1 hdn hn⟩

end L.Arena

namespace ConAgua.Final

open L L.Compiler L.Checker L.Arena L.Rom

local notation "VM" => ConLeche.CheckMode.verified

/-- **The challenge's threads accept ⇒ the twin's pool with the solution accepts the challenge's
phase**. After the solution's index build (`FoldOn`) and its pooled accept, mode `7` (`F6`, then
`par_compact(1)`: `m7`), threads on mode `7`'s buffer, each a fresh region running its calls,
every job index below `c` claimed, each thread's claims increasing: the challenge's preparation
and side records (`Side6`) and its pooled check with the solution `solutionOf PS.IS res`
(`PooledAcceptsJ`, from `sG`, the side records' state). -/
theorem cmpThreadsC_pooledJ {bC bS pb : ByteArray} (hpb : pb.size < 2 ^ 63) (PS : PhaseS bC bS) {m₇ m : Mem}
    (hF : FoldOn bS pb (abiSz checkerTab) PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m)
    (hPS : PooledAccepts .verified PS.ipins PS.dsS PS.sE PS.IS PS.sF)
    {c : Word} {m9 m7 : Mem} (h6 : F6 PS m c m9) (hb9 : m9.bytes = m.bytes)
    (hok : parCompactOK m9 1 = true) (hm7 : m7 = parCompactMem m9 1)
    (ths : List (Mem × List (Word × Nat × Mem)))
    (hth : ∀ t ∈ ths, (∀ b ∈ parOwnedL, t.1.arr64 b = zeros (m7.arr64 b).size) ∧ t.1.glob INIT = 0 ∧
      ThreadRuns (cmpBuf OUT m7) t.1 t.2 ∧ ∀ c' ∈ t.2, c'.1 < c)
    (hcov : ∀ j : Word, j < c → ∃ t ∈ ths, ∃ c' ∈ t.2, c'.1 = j)
    (hinc : ∀ t ∈ ths, (t.2.map (·.1)).Pairwise (· < ·)) :
    ∃ (m2 m3 : Mem) (dsC : Array IDeclaration) (sG : AState) (res : List IDeclaration) (m4 : Mem)
      (I : IStreamIndex) (a' : AState),
      Side6 PS m c m2 m3 dsC sG res m4 ∧
      PooledAcceptsJ .verified PS.ipins (some (solutionOf PS.IS res)) res.toArray sG I a' := by
  subst hm7
  obtain ⟨m2, m3, dsC, sG, res, m4, I, a', h, hI, hJM, hwf, hoff, hsz9⟩ := F6.jobM hF h6
  refine ⟨m2, m3, dsC, sG, res, m4, I, a', h, ?_⟩
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
  -- the buffer
  have hlt : (m9.arr64 OUT).size < 2 ^ 64 := by
    rw [hsz9, hF.sizeAt]; have := abiSz_le checkerTab_abiOk OUT; simp only [abiWords] at this; omega
  have hB : cmpBuf OUT (parCompactMem m9 1) = bufOf m9 := by
    simp only [cmpBuf]; rw [bufOf, (parCompactMem_hdr hok).2.1]
  have hO := parCompactMem_out m9 1
  have hcnt : c.toNat = res.toArray.size := by simpa using h.count.1
  have hds : res.toArray.size < 2 ^ 63 := by
    have := h.decls.room; have := h.decls.dsize; simp only [List.size_toArray] at *; omega
  -- the twin's side
  let a₀ : AState := { a' with caches := Caches.empty }
  let Rel : Mem → AState → Prop := fun r a =>
    ∀ j, ThrAt PS.ipins (dnOf sG.store) res.toArray I a₀ pb.data.toList (seedMem (bufMem (bufOf m9) r j)) a (some J)
  let Call : Nat → Mem → Mem → Prop := fun k r r' => ∃ n rs, n ≤ 2 ^ 62 ∧
    L.run checkerProg n "check" [] (bufMem (bufOf m9) r (UInt64.ofNat k)) = .ok (rs, r') ∧
      BufKept (bufOf m9) r'
  obtain ⟨pinsP, dsP, dsSP, matesU, hst, hspec, hpp, hden, hPD, hH⟩ :=
    poolHypsJ_ofP h.phase hPS hI Rel Call
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
    refine ⟨a', ?_, fun j => ⟨X, hJ, hPB, fun t ht => (thr_next _ j hI' hkept (thr_ctl_next hrun) t ht).trans (hX t ht)⟩⟩
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
    have hJR := JobM.fresh (hJM.truncJ hoff hKI (.inr (F6.extOK hF h6)) (fun J' e => by cases e; exact ⟨hSK, (F6.ext hF h6).1⟩)) hwf hoff
    refine ⟨freshMem m9, ⟨_, ⟨hJR, PExt.of_ext (Ext.refl _), rfl⟩, ?_⟩, ?_, ?_⟩
    · exact ⟨by simp [AState.worker, estore_dropScratch_self hwf hoff], rfl, rfl⟩
    · rw [freshMem_arr8]
      show m9.bytes L.Rom.PB = _
      rw [hb9, hF.bytes, ← Mem.arr8, hF.r7.since.keep.arr8]; exact loadMem_pb bS pb _
    · exact thr_first hok hlt t₀.1 j (fun b hb => by rw [hz b hb, hO.size]) hI0
  have hchain : ∀ t ∈ ths', JobChain Call t.1 t.2 := by
    intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
    have := threadRuns_chain (bufOf m9) _ _ (by rw [← hB]; exact (hth t₀ ht₀).2.2.1)
    exact this
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
  exact ⟨ths'.map (·.2), hI,
    fun k hk' => by obtain ⟨t, ht, hkt⟩ := hcov' k hk'; exact ⟨t.2, List.mem_map_of_mem ht, hkt⟩,
    fun w hw k hkw => by obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hw; exact hrange t ht k hkw,
    fun w hw => by obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hw; exact hinc' t ht,
    fun w hw => by obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hw; exact hacc t ht⟩

end ConAgua.Final
