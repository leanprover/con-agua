module

public import ConAgua.Final.CmpChain
public import ConAgua.Final.CmpThreadsL
import ConAgua.Final.CmpChainC
public import ConAgua.Checker.ParThreadTwin
import ConAgua.Checker.AsmFinal

@[expose] public section

/-!
# The threaded compared run's solution phase at the L level (lane compare2)

`cmpThreadsS_pooled`: after modes `4` and `5` (`checker_modes45`: the solution's index build,
`FoldOn`, then `par_compact(1)`: `m5`), threads on mode `5`'s buffer, each a fresh region running
its calls (`ThreadRuns`), every job index below `k` claimed, each thread's claims increasing: the
solution's check phase is con-ron's pool without a solution (`PooledAccepts`, `J = none`). The
flat threaded mode's `threads_pooledO` at the compared run's stages (`StagesOut.cmp`); the
sequential analogue is `cmpSJobs_twin`.
-/

namespace ConAgua.Final

open L L.Compiler L.Checker L.Arena ConRon.Arena

/-- **The solution's threads accept ⇒ the twin's pool accepts the solution's phase**, from the
solution's index build (`FoldOn`) and mode `5`'s memory `m5 = parCompactMem m 1`. -/
theorem cmpSThreads_pooled {bC bS pb : ByteArray} (hpb : pb.size < 2 ^ 63) (PS : PhaseS bC bS) {m₇ m m5 : Mem}
    (hF : FoldOn bS pb (abiSz checkerTab) PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m)
    (hok : parCompactOK m 1 = true) (hm5 : m5 = parCompactMem m 1) (khi : Word) (hk : khi.toNat = PS.dsS.size)
    (ths : List (Mem × List (Word × Nat × Mem)))
    (hth : ∀ t ∈ ths, (∀ b ∈ parOwnedL, t.1.arr64 b = zeros (m5.arr64 b).size) ∧ t.1.glob INIT = 0 ∧
      ThreadRuns (cmpBuf OUT m5) t.1 t.2 ∧ ∀ c ∈ t.2, c.1 < khi)
    (hcov : ∀ j : Word, j < khi → ∃ t ∈ ths, ∃ c ∈ t.2, c.1 = j)
    (hinc : ∀ t ∈ ths, (t.2.map (·.1)).Pairwise (· < ·)) :
    PooledAccepts .verified PS.ipins PS.dsS PS.sE PS.IS PS.sF := by
  subst hm5
  have ho := StagesOut.cmp PS.pfx PS.pinsR
  have hJP := jobProg_of_out checkerCdG_proved ho (ds := PS.dsS) hpb hF.r7.since.pbpre
  have hsz : ∀ t, (m.arr64 t).size = abiSz checkerTab t := fun t => by
    rw [hF.frame.size, hF.r7.since.frame.size]; simp [loadMem, Mem.arr64]
  have hlt : (m.arr64 OUT).size < 2 ^ 64 := by
    rw [hsz]; have := abiSz_le checkerTab_abiOk OUT; simp only [abiWords] at this; omega
  have hB0 : cmpBuf OUT (parCompactMem m 1) = bufOf m := by
    simp only [cmpBuf]; rw [bufOf, (parCompactMem_hdr hok).2.1]
  have hO := parCompactMem_out m 1
  obtain ⟨parts, h1, h2, h3, h4⟩ := threads_pooledO ho PS.idx hF hJP hok hlt _ hB0 khi hk ths
    (fun t ht => by
      obtain ⟨hz, hI, hR, hc⟩ := hth t ht
      exact ⟨fun b hb => by rw [hz b hb, hO.size], hI, hR, hc⟩) hcov hinc
  exact ⟨parts, PS.idx, h1, h2, h3, h4⟩

/-- **The solution's phase of the threaded compared run**, from the runs of modes `4` and `5`
(each returning `2^63` or more) and the solution's threads (`CmpTPoolS`'s facts): the twin's
phase `PS`, its index build, mode `5`'s memory, and the pool's accept. -/
theorem cmpThreadsS_phase (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (hbC : bC.size < 2 ^ 63) (hbS : bS.size < 2 ^ 63) (hpb : pb.size < 2 ^ 63)
    {rs4 : List Word} {m4 : Mem} {rs5 : List Word} {m5 : Mem}
    (h4 : cmpRun checkerProg (cmpM4 checkerTab MODE bC pb) = .ok (rs4, m4))
    (hge4 : 2 ^ 63 ≤ (rs4.getD 0 0).toNat)
    (h5 : cmpRun checkerProg (cmpM5 MODE m4 bS) = .ok (rs5, m5))
    (hge5 : 2 ^ 63 ≤ (rs5.getD 0 0).toNat)
    (ths : List (Mem × List (Word × Nat × Mem)))
    (hth : ∀ t ∈ ths, (∀ b ∈ parOwnedL, t.1.arr64 b = zeros (m5.arr64 b).size) ∧ t.1.glob INIT = 0 ∧
      ThreadRuns (cmpBuf OUT m5) t.1 t.2 ∧ ∀ c ∈ t.2, c.1 < rs5.getD 0 0 - 9223372036854775808)
    (hcov : ∀ j : Word, j < rs5.getD 0 0 - 9223372036854775808 → ∃ t ∈ ths, ∃ c ∈ t.2, c.1 = j)
    (hinc : ∀ t ∈ ths, (t.2.map (·.1)).Pairwise (· < ·)) :
    CmpAt4 bC bS pb (abiSz checkerTab) m4 ∧
    ∃ (PS : PhaseS bC bS) (m₇ m : Mem),
      FoldOn bS pb (abiSz checkerTab) PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m ∧
      Stash m PS.pre PS.rC ∧ Keep6 m PS.pre ∧ parCompactOK m 1 = true ∧ m5 = parCompactMem m 1 ∧
      rs5.headD 0 = 9223372036854775808 + UInt64.ofNat PS.dsS.size ∧
      PooledAccepts .verified PS.ipins PS.dsS PS.sE PS.IS PS.sF := by
  obtain ⟨hA4, PS, m₇, m, hF, hst, hk6, hok, hm5, hres5⟩ :=
    checker_modes45 bC bS pb h64 hbC hbS hpb h4 hge4 h5 hge5
  have hn : PS.dsS.size < 2 ^ 63 := by
    have := hF.build.decls.room; have := hF.build.decls.dsize; omega
  have hk : (rs5.getD 0 0 - 9223372036854775808).toNat = PS.dsS.size := by
    have e : (9223372036854775808 : Word) + UInt64.ofNat PS.dsS.size - 9223372036854775808 =
        UInt64.ofNat PS.dsS.size := by rw [UInt64.add_comm, UInt64.add_sub_cancel]
    rw [L.getD_zero, hres5, e, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
  exact ⟨hA4, PS, m₇, m, hF, hst, hk6, hok, hm5, hres5,
    cmpSThreads_pooled hpb PS hF hok hm5 _ hk ths hth hcov hinc⟩

/-! ## Mode `7` -/

/-- Mode `7`'s memory is mode `5`'s with the mode word `7` (the input already the solution's). -/
theorem cmpM7_eq {m4 : Mem} {bS : ByteArray} {rs5 : List Word} {m5 : Mem}
    (h5 : cmpRun checkerProg (cmpM5 MODE m4 bS) = .ok (rs5, m5)) : cmpM7 MODE m5 bS = m5.setG MODE 7 := by
  have hb := run_check_bytes h5
  have hin : m5.arr8 IN = bS.data := by
    show m5.bytes IN = _
    rw [hb]; simp [cmpM5, cmpIn, Mem.setG]
  have e : bS = ⟨m5.arr8 IN⟩ := by rw [hin]
  rw [cmpM7, e, cmpIn_self]

/-- **Mode `7` of the checker**: after modes `4` and `5` (`cmpThreadsS_phase`'s `PS`, `m`), mode
`7`'s run ends in the frozen buffer's memory (`par_compact(1)`) of a memory `F6 c` with the bytes
of `m`, and returns `2^63 + c`. -/
theorem checker_mode7 {bC bS pb : ByteArray} (hpb : pb.size < 2 ^ 63) (PS : PhaseS bC bS) {m₇ m : Mem}
    (hF : FoldOn bS pb (abiSz checkerTab) PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m)
    (hst : Stash m PS.pre PS.rC) (hk6 : Keep6 m PS.pre) {m4 : Mem} {rs5 : List Word} {m5 : Mem}
    (h5 : cmpRun checkerProg (cmpM5 MODE m4 bS) = .ok (rs5, m5)) (hm5 : m5 = parCompactMem m 1)
    {rs7 : List Word} {m7 : Mem} (h7 : cmpRun checkerProg (cmpM7 MODE m5 bS) = .ok (rs7, m7)) :
    ∃ c m9, F6 PS m c m9 ∧ parCompactOK m9 1 = true ∧ m7 = parCompactMem m9 1 ∧ m9.bytes = m.bytes ∧
      rs7.headD 0 = (9223372036854775808 : Word) + c := by
  have hsz : ∀ s, abiSz checkerTab s < 2 ^ 64 := fun s => by
    have := abiSz_le checkerTab_abiOk s; simp only [abiWords] at this; omega
  have hN : abiFuel < 2 ^ 62 := by simp [abiFuel]
  have hsz6 : ∀ g ≤ 2, abiSz checkerTab (sixArr g) = abiSz checkerTab (eixArr g) ∧
      abiSz checkerTab (stxArr g) = abiSz checkerTab (tixArr g) := by
    intro g hg
    rcases (show g = 0 ∨ g = 1 ∨ g = 2 by omega) with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
  rw [cmpM7_eq h5] at h7
  have hO5 : OutEq m m5 := hm5 ▸ OutEq.of_out (parCompactMem_out m 1)
  obtain ⟨c, ⟨m9, hF6, hok9, rfl⟩, hres⟩ := checkC3_run_g PS hF hst hk6 hsz hpb hsz6 (hO5.setG MODE 7) 7 1
    (.inr ⟨rfl, rfl⟩) (by simp [Mem.setG]) abiFuel hN rs7 _ h7
  have hO9 : OutEq m9 (parCompactMem m9 1) := OutEq.of_out (parCompactMem_out m9 1)
  have hb9 : m9.bytes = m.bytes := by
    rw [← hO9.bytes, run_check_bytes h7]
    exact hO5.bytes
  exact ⟨c, m9, hF6, hok9, rfl, hb9, hres⟩

/-- **The buffer's geometry after mode `7`** (as `checker_cmpBufOk` after mode `5`). -/
theorem checker_cmp7BufOk (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (hbC : bC.size < 2 ^ 63) (hbS : bS.size < 2 ^ 63) (hpb : pb.size < 2 ^ 63)
    {rs4 : List Word} {m4 : Mem} {rs5 : List Word} {m5 : Mem} {rs7 : List Word} {m7 : Mem}
    (h4 : cmpRun checkerProg (cmpM4 checkerTab MODE bC pb) = .ok (rs4, m4))
    (hge4 : 2 ^ 63 ≤ (rs4.getD 0 0).toNat)
    (h5 : cmpRun checkerProg (cmpM5 MODE m4 bS) = .ok (rs5, m5))
    (hge5 : 2 ^ 63 ≤ (rs5.getD 0 0).toNat)
    (h7 : cmpRun checkerProg (cmpM7 MODE m5 bS) = .ok (rs7, m7))
    (_hge7 : 2 ^ 63 ≤ (rs7.getD 0 0).toNat) :
    CmpBufOk frozenIdsL OUT m7 := by
  obtain ⟨-, PS, m₇, m, hF, hst, hk6, -, hm5, -⟩ := checker_modes45 bC bS pb h64 hbC hbS hpb h4 hge4 h5 hge5
  obtain ⟨c, m9, -, hok9, rfl, -, -⟩ := checker_mode7 hpb PS hF hst hk6 h5 hm5 h7
  have hlt : (m9.arr64 OUT).size < 2 ^ 64 := by
    have e7 := run_check_size h7 OUT
    have e5 := run_check_size h5 OUT
    have e4 := run_check_size h4 OUT
    rw [← (parCompactMem_out m9 1).size OUT, e7, cmpM7_eq h5]
    have e : ((m5.setG MODE 7).arr64 OUT).size = (m5.arr64 OUT).size := rfl
    rw [e, e5]
    simp only [cmpM5, cmpIn, Mem.setG, Mem.arr64] at e4 ⊢
    rw [e4]
    simp only [cmpM4, loadMem, Mem.setG, Array.size_replicate]
    have := abiSz_le checkerTab_abiOk OUT; simp only [abiWords] at this; omega
  exact pc1_cmpBufOk m9 hok9 hlt

/-! ## The composition -/

/-- **The threaded compared run's L runs accept ⇒ the twin's pooled comparison accepts.** -/
theorem cmpThreads_twinPooled (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (hbC : bC.size < 2 ^ 63) (hbS : bS.size < 2 ^ 63) (hpb : pb.size < 2 ^ 63)
    (rs4 : List Word) (m4 : Mem) (h4 : cmpRun checkerProg (cmpM4 checkerTab MODE bC pb) = .ok (rs4, m4))
    (hge4 : 2 ^ 63 ≤ (rs4.getD 0 0).toNat)
    (rs5 : List Word) (m5 : Mem) (h5 : cmpRun checkerProg (cmpM5 MODE m4 bS) = .ok (rs5, m5))
    (hge5 : 2 ^ 63 ≤ (rs5.getD 0 0).toNat)
    (thsS : List (Mem × List (Word × Nat × Mem)))
    (hthS : ∀ t ∈ thsS, (∀ b ∈ parOwnedL, t.1.arr64 b = zeros (m5.arr64 b).size) ∧ t.1.glob INIT = 0 ∧
      ThreadRuns (cmpBuf OUT m5) t.1 t.2 ∧ ∀ c ∈ t.2, c.1 < rs5.getD 0 0 - 9223372036854775808)
    (hcovS : ∀ j : Word, j < rs5.getD 0 0 - 9223372036854775808 → ∃ t ∈ thsS, ∃ c ∈ t.2, c.1 = j)
    (hincS : ∀ t ∈ thsS, (t.2.map (·.1)).Pairwise (· < ·))
    (rs7 : List Word) (m7 : Mem) (h7 : cmpRun checkerProg (cmpM7 MODE m5 bS) = .ok (rs7, m7))
    (_hge7 : 2 ^ 63 ≤ (rs7.getD 0 0).toNat)
    (thsC : List (Mem × List (Word × Nat × Mem)))
    (hthC : ∀ t ∈ thsC, (∀ b ∈ parOwnedL, t.1.arr64 b = zeros (m7.arr64 b).size) ∧ t.1.glob INIT = 0 ∧
      ThreadRuns (cmpBuf OUT m7) t.1 t.2 ∧ ∀ c ∈ t.2, c.1 < rs7.getD 0 0 - 9223372036854775808)
    (hcovC : ∀ j : Word, j < rs7.getD 0 0 - 9223372036854775808 → ∃ t ∈ thsC, ∃ c ∈ t.2, c.1 = j)
    (hincC : ∀ t ∈ thsC, (t.2.map (·.1)).Pairwise (· < ·)) :
    TwinComparesAcceptsPooled bC bS := by
  obtain ⟨-, PS, m₇, m, hF, hst, hk6, -, hm5, -, hPS⟩ :=
    cmpThreadsS_phase bC bS pb h64 hbC hbS hpb h4 hge4 h5 hge5 thsS hthS hcovS hincS
  obtain ⟨c, m9, hF6, hok9, hm7, hb9, hres7⟩ := checker_mode7 hpb PS hF hst hk6 h5 hm5 h7
  have hhi : rs7.getD 0 0 - 9223372036854775808 = c := by
    rw [L.getD_zero, hres7, UInt64.add_comm, UInt64.add_sub_cancel]
  rw [hhi] at hthC hcovC
  obtain ⟨m2, m3, dsC, sG, res, m4', I, a', hS6, hC⟩ :=
    cmpThreadsC_pooledJ hpb PS hF hPS hF6 hb9 hok9 hm7 thsC hthC hcovC hincC
  obtain ⟨⟨hA, hB, hC'⟩, hCS, hDS⟩ := PS.pfx
  exact ⟨PS.pins, PS.sA, PS.sB, PS.sC, PS.sC', PS.sD, PS.sE, PS.sF, sG, sG, a', PS.pre, PS.rC, PS.rS,
    PS.dsS, dsC, res, PS.ipins, PS.IS, I, hA, hB, hC', hCS, hDS, PS.pinsR, hPS, hS6.prep.run, hS6.run, hC⟩

end ConAgua.Final
