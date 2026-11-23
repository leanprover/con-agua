module

public import ConAgua.Final.CmpAbi
public import ConAgua.Final.ThreadsFinal
public import ConAgua.Checker.CompareChain5
import ConAgua.Front.Preserve
import ConAgua.Checker.CheckARun
import ConAgua.Checker.AsmFinal
import all ConAgua.Checker.Entry

@[expose] public section

/-!
# The compared run's L-level chain, for the checker (lane compare)

`checker_cmpBufOk`: after modes `4` and `5` of `checkerProg` (`checkC1_run`, `checkC2_run`), the
frozen buffer mode `5` leaves in `OUT` has the geometry `ca_compare` relies on (`CmpBufOk`), as
entry 1's does (`entry1_buf`).
-/

namespace ConAgua.Final

open L L.Compiler L.Checker L.Arena

/-- A run of `check` keeps every word array's size. -/
theorem run_check_size {N : Nat} {m : Mem} {rs : List Word} {m' : Mem}
    (h : L.run checkerProg N "check" [] m = .ok (rs, m')) (a : TieredArray) :
    (m'.arr64 a).size = (m.arr64 a).size := by
  have t := Triple.keep checkerProg_noSt8 (n := N) (f := "check") (vs := [])
    (s₀ := ⟨m, Locals.init []⟩) (Q := fun _ _ => True)
    (M.triple_of_run fun _ _ _ _ _ => trivial)
  have hk := run_post (Q := fun _ m'' => L.Keep m m'') h (by
    apply M.triple_of_run
    intro s r s' hs' hrun
    exact (M.of_run (P := fun x => x = _) hs' hrun t).2.1)
  exact hk.2 a

/-- **The frozen buffer's geometry** after `par_compact(1)` (`entry1_buf`'s argument at any
memory): its length word inside `OUT`, at least the header long, the entries inside it and in
increasing order. -/
theorem pc1_buf (m : Mem) (hok : parCompactOK m 1 = true) (hlt : (m.arr64 OUT).size < 2 ^ 64)
    (B : Array Word) (hB : B = ((parCompactMem m 1).arr64 OUT).extract 0
      (((parCompactMem m 1).arr64 OUT).getD 1 0).toNat) :
    (((parCompactMem m 1).arr64 OUT).getD 1 0).toNat ≤ ((parCompactMem m 1).arr64 OUT).size ∧
      hdrW ≤ (((parCompactMem m 1).arr64 OUT).getD 1 0).toNat ∧ bufEntry B 0 = (0, hdrW) ∧
      (∀ i < frozenIdsL.length, (bufEntry B i).1 + (bufEntry B i).2 ≤ B.size) ∧
      (∀ i < frozenIdsL.length, ∀ i' < frozenIdsL.length, i < i' →
        (bufEntry B i).1 + (bufEntry B i).2 ≤ (bufEntry B i').1) := by
  have hF := parCompactMem_out m 1
  have hlen : (((parCompactMem m 1).arr64 OUT).getD 1 0).toNat = (fzOff m frozen.length).toNat := by
    rw [(parCompactMem_hdr hok).2.1]
  have hBm : B = bufOf m := by rw [hB, bufOf, (parCompactMem_hdr hok).2.1]
  have hs := bufOf_size hok hlt
  have hoffs := buf_offs hok hlt
  have hFl : frozen.length = 63 := frozen_length
  have hL : frozenIdsL.length = frozen.length + 1 := by rw [frozenIdsL_eq]; simp
  refine ⟨by rw [hlen, hF.size, hs.2]; exact hoffs.2, by rw [hlen, hs.2]; omega,
    by rw [hBm]; exact bufEntry_zero hok hlt, fun i hi => hBm ▸ buf_entries_inside hok hlt hi, fun i hi i' hi' hii => ?_⟩
  rw [hBm]
  obtain ⟨c, rfl⟩ : ∃ c, i' = c + 1 := ⟨i' - 1, by omega⟩
  obtain ⟨he', ho'⟩ := bufEntry_succ hok hlt (i := c) (by omega)
  rw [he', ho']
  rcases i with _ | a
  · rw [bufEntry_zero hok hlt]; simp only; omega
  · obtain ⟨he, ho⟩ := bufEntry_succ hok hlt (i := a) (by omega)
    rw [he, ho]
    have := fzSum_mono m (j := a + 1) (n := c) (by omega)
    rw [fzSum_succ, ← fzExt_eq] at this
    simp only; omega

theorem cmpM4_eq (bC pb : ByteArray) :
    cmpM4 checkerTab MODE bC pb = loadMemM bC pb (abiSz checkerTab) 4 := rfl

/-- **Modes `4` and `5` of the checker**: from the runs `CmpGuard` names (mode `4` returning
`2^63` or more, mode `5` `2^63` or more), mode `4`'s end and mode `5`'s (`checkC2_run`). -/
theorem checker_modes45 (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (hbC : bC.size < 2 ^ 63) (hbS : bS.size < 2 ^ 63) (hpb : pb.size < 2 ^ 63)
    {rs4 : List Word} {m4 : Mem} {rs5 : List Word} {m5 : Mem}
    (h4 : cmpRun checkerProg (cmpM4 checkerTab MODE bC pb) = .ok (rs4, m4))
    (hge4 : 2 ^ 63 ≤ (rs4.getD 0 0).toNat)
    (h5 : cmpRun checkerProg (cmpM5 MODE m4 bS) = .ok (rs5, m5))
    (hge5 : 2 ^ 63 ≤ (rs5.getD 0 0).toNat) :
    CmpAt4 bC bS pb (abiSz checkerTab) m4 ∧
    ∃ (PS : PhaseS bC bS) (m₇ m : Mem),
      FoldOn bS pb (abiSz checkerTab) PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m ∧
      Stash m PS.pre PS.rC ∧ Keep6 m PS.pre ∧ parCompactOK m 1 = true ∧ m5 = parCompactMem m 1 ∧
      rs5.headD 0 = 9223372036854775808 + UInt64.ofNat PS.dsS.size := by
  have hsz : ∀ s, abiSz checkerTab s < 2 ^ 64 := fun s => by
    have := abiSz_le checkerTab_abiOk s; simp only [abiWords] at this; omega
  have hN : abiFuel < 2 ^ 62 := by simp [abiFuel]
  have hr4 : rs4.headD 0 ≠ 1 := fun e => by rw [L.getD_zero, e] at hge4; simp at hge4
  have hr5 : rs5.headD 0 ≠ 1 := fun e => by rw [L.getD_zero, e] at hge5; simp at hge5
  obtain ⟨-, hA4⟩ := checkC1_run bC bS pb _ ⟨h64, hbC, hpb, hsz⟩ abiFuel hN rs4 m4 h4 hr4
  exact ⟨hA4, checkC2_run bC bS pb _ ⟨h64, hbS, hpb, hsz⟩ abiFuel hN m4 hA4 rs5 m5 h5 hr5⟩

/-- **The buffer's geometry after mode `5`** (`CmpGuard`'s first half, for the checker). -/
theorem checker_cmpBufOk (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (hbC : bC.size < 2 ^ 63) (hbS : bS.size < 2 ^ 63) (hpb : pb.size < 2 ^ 63)
    {rs4 : List Word} {m4 : Mem} {rs5 : List Word} {m5 : Mem}
    (h4 : cmpRun checkerProg (cmpM4 checkerTab MODE bC pb) = .ok (rs4, m4))
    (hge4 : 2 ^ 63 ≤ (rs4.getD 0 0).toNat)
    (h5 : cmpRun checkerProg (cmpM5 MODE m4 bS) = .ok (rs5, m5))
    (hge5 : 2 ^ 63 ≤ (rs5.getD 0 0).toNat) :
    CmpBufOk frozenIdsL OUT m5 := by
  obtain ⟨-, PS, m₇, m, -, -, -, hok, rfl, -⟩ := checker_modes45 bC bS pb h64 hbC hbS hpb h4 hge4 h5 hge5
  have hlt : (m.arr64 OUT).size < 2 ^ 64 := by
    have e5 := run_check_size h5 OUT
    have e4 := run_check_size h4 OUT
    rw [← (parCompactMem_out m 1).size OUT, e5]
    simp only [cmpM5, cmpIn, Mem.setG, Mem.arr64] at e4 ⊢
    rw [e4]
    simp only [cmpM4, loadMem, Mem.setG, Array.size_replicate]
    have := abiSz_le checkerTab_abiOk OUT; simp only [abiWords] at this; omega
  obtain ⟨hlen, hhdr, he0, hin, hord⟩ := pc1_buf m hok hlt (cmpBuf OUT (parCompactMem m 1)) rfl
  have hsize : (cmpBuf OUT (parCompactMem m 1)).size = (((parCompactMem m 1).arr64 OUT).getD 1 0).toNat := by
    simp only [cmpBuf, Array.size_extract]; omega
  have hL : frozenIdsL.length = 64 := by rw [frozenIdsL_eq]; simp [frozen_length]
  have hH : hdrW = 136 := by decide
  refine ⟨hlen, by rw [he0], fun i hi => by rw [he0]; simp only; omega, hin, fun i hi i' hi' hne => ?_⟩
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact .inl (hord i hi i' hi' h)
  · exact .inr (.inl (hord i' hi' i hi h))

end ConAgua.Final
