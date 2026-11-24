module

public import ConAgua.Final.CmpAbi
public import ConAgua.Checker.CompareChain5
import ConAgua.Checker.CmpSJobs
import ConAgua.Checker.CmpHdrKeep
import ConAgua.Checker.CheckARun
import ConAgua.Checker.AsmFinal
import all ConAgua.Checker.Entry
import ConAgua.Checker.BlockRefsProg
import ConAgua.Checker.DefnArmT
import ConAgua.Checker.IndArm
import ConAgua.Checker.StreamRecsProg
public import ConAgua.Checker.ParDriverTwin
public import ConAgua.Checker.ProgTab
import ConAgua.Checker.RomProg0
import ConAgua.L.WordOff

@[expose] public section

/-!
# The compared run's L-level chain, for the checker (lane compare)

`checker_cmpBufOk`: after modes `4` and `5` of `checkerProg` (`checkC1_run`, `checkC2_run`), the
frozen buffer mode `5` leaves in `OUT` has the geometry `ca_compare` relies on (`CmpBufOk`), as
entry 1's does (`entry1_buf`).
-/

namespace ConAgua.Final

open L L.Compiler L.Checker L.Arena

/-- **`check_decl`'s program facts at every injective record decoder** (`CheckerCdG`; the
flat run's `checkerCd_proved` at any decoder). -/
theorem checkerCdG_proved : L.Checker.CheckerCdG := fun pb _ dn _ hpb hpre hdn =>
  have hr : L.Rom.RomOK pb.data.toList := by simpa [L.Rom.RomOK] using hpb
  ⟨L.Checker.checkerProg_defnLoopPB _ hr hpre,
    L.Checker.indArmSpec_checker _ hr hpre
      (L.Checker.cbRefs_checker _ hr hpre (L.Checker.snoSim_checker _)) dn hdn⟩

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

/-- **TEMP stand-in** (compare2-freeze; the old in-place sequential solution phase over the buffer
sequence `bufSeq`, removed with it before landing): the seed's image is the same along the jobs. -/
theorem bufSeq_seed_standin (B : Array Word) (rm : Nat → Mem) :
    ∀ k, bufImg (bufSeq frozenIdsL B rm (k + 1)) 1 = bufImg (bufSeq frozenIdsL B rm k) 1 := by
  sorry

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
  have hFl := frozen_length
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

/-- **The buffer's geometry after `par_compact(1)`** (`CmpBufOk`). -/
theorem pc1_cmpBufOk (m : Mem) (hok : parCompactOK m 1 = true) (hlt : (m.arr64 OUT).size < 2 ^ 64) :
    CmpBufOk frozenIdsL OUT (parCompactMem m 1) := by
  obtain ⟨hlen, hhdr, he0, hin, hord⟩ := pc1_buf m hok hlt (cmpBuf OUT (parCompactMem m 1)) rfl
  have hL := frozenIdsL_length
  have hH := hdrW_eq
  refine ⟨hlen, by rw [he0], fun i hi => by rw [he0]; simp only; omega, hin, fun i hi i' hi' hne => ?_⟩
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact .inl (hord i hi i' hi' h)
  · exact .inr (.inl (hord i' hi' i hi h))

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
  exact pc1_cmpBufOk m hok hlt

/-- **A job keeps the header** (`CmpGuard`'s second half, for the checker): `check` with the mode
word `2` stores into neither the header nor the seed (`check_mode2_hk`). -/
theorem checker_cmpHdrKeep : CmpHdrKeep checkerProg MODE PLO PHI frozenIdsL parOwnedL := by
  intro B r j rs r' h _
  have h' : L.run checkerProg abiFuel "check" [] (bufMem B r j) = .ok (rs, r') := by rw [bufMem_eq]; exact h
  have hk := run_post (Q := fun _ m'' => (bufMem B r j).glob MODE = 2 → HkFr (bufMem B r j) m'')
    h' (check_mode2_hk abiFuel _) rfl
  have e : frozenIdsL[0] = (HDRF : TieredArray) := rfl
  rw [e, hk.1, bufMem_hdr]

/-- **The solution's jobs of the compared run accept ⇒ the twin's job list accepts** (one worker,
`J = none`). After mode `5` (the solution's index build, `FoldOn`, then `par_compact(1)`: `m5`),
the jobs `j < k` on the buffer as the jobs before left it, from the zero region (`CmpJobs`), with
`k` the number of the solution's records. -/
theorem cmpSJobs_twin {bC bS pb : ByteArray} (hpb : pb.size < 2 ^ 63) (PS : PhaseS bC bS) {m₇ m m5 : Mem}
    (hF : FoldOn bS pb (abiSz checkerTab) PS.dsS PS.ipins PS.sE PS.IS PS.sF m₇ m)
    (hok : parCompactOK m 1 = true) (hm5 : m5 = parCompactMem m 1) {rm : Nat → Mem} {k : Nat}
    (hj : CmpJobs checkerProg MODE PLO PHI frozenIdsL parOwnedL (cmpBuf OUT m5) rm k)
    (h0 : rm 0 = zeroMem checkerTab) (hk : k = PS.dsS.size) :
    ∃ s'', ConRon.Arena.checkJobList .verified PS.ipins none PS.IS PS.dsS (List.range k) PS.sF.worker =
      .ok (.ok (), s'') := by
  subst hm5 hk
  have ho := StagesOut.cmp PS.pfx PS.pinsR
  have hJP := jobProg_of_out checkerCdG_proved ho (ds := PS.dsS) hpb hF.r7.since.pbpre
  have hsz : ∀ t, (m.arr64 t).size = abiSz checkerTab t := fun t => by
    rw [hF.frame.size, hF.r7.since.frame.size]; simp [loadMem, Mem.arr64]
  have hlt : (m.arr64 OUT).size < 2 ^ 64 := by
    rw [hsz]; have := abiSz_le checkerTab_abiOk OUT; simp only [abiWords] at this; omega
  have hB := (pc1_cmpBufOk m hok hlt).2
  have hB0 : cmpBuf OUT (parCompactMem m 1) = bufOf m := by
    simp only [cmpBuf]; rw [bufOf, (parCompactMem_hdr hok).2.1]
  have hBs := bufSeq_ok hB checker_cmpHdrKeep _ hj
  have hN : abiFuel ≤ 2 ^ 62 := by simp [abiFuel]
  refine sjobs_chainO ho PS.idx hF hJP hok hlt (bufSeq frozenIdsL (cmpBuf OUT (parCompactMem m 1)) rm) hB0
    (bufSeq_seed_standin _ rm) rm
    (fun b hb => by rw [h0, hsz]; simp [zeroMem, Mem.arr64, zeros]) (by rw [h0]; rfl) fun j hjk => ?_
  obtain ⟨rs, hr, -⟩ := hj j hjk
  have hr' : L.run checkerProg abiFuel "check" []
      (bufMem (bufSeq frozenIdsL (cmpBuf OUT (parCompactMem m 1)) rm j) (rm j) (UInt64.ofNat j)) =
      .ok (rs, rm (j + 1)) := by rw [bufMem_eq]; exact hr
  refine ⟨abiFuel, rs, hN, hr', fun k' hk' h1 => ?_⟩
  have hBj := hBs j (by omega)
  have hL : frozenIdsL.length = frozen.length + 1 := by rw [frozenIdsL_eq]; simp
  have hi : k' + 1 < frozenIdsL.length := by omega
  have hent := hBj.ent (k' + 1) hi
  have he := bufNext_entry hBj (checker_cmpHdrKeep _ _ _ _ _ hr) hi
  have hs : ((rm (j + 1)).arr64 frozenIdsL[k' + 1]).size =
      (bufEntry (bufSeq frozenIdsL (cmpBuf OUT (parCompactMem m 1)) rm j) (k' + 1)).2 := by
    rw [run_check_size hr', frozenIdsL_get hk', bufMem_frozen _ _ _ hk' h1]
    simp only [bufImg, Array.size_extract]; omega
  have := bufNext_img hBj hi he hs
  rw [frozenIdsL_get hk'] at this
  exact this.symm

/-- info: 'ConAgua.Final.cmpSJobs_twin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cmpSJobs_twin

end ConAgua.Final
