import ConAgua.Final.DrvAbi
import ConAgua.Checker.ParDriverTwin
import ConAgua.Checker.AsmFinal

/-!
# The final theorem for the sequential driver of the committed file (lane parmode)

`checkerFile_drv_accepts_regs`: the harness calls the driver `ca_start` of `checker.s` as
`AbiCall` says. The machine returns to the caller with the
callee-saved registers restored, and if it reports `rdx = 0` with `rax = ACCEPT`, the twin's
pipeline accepts `[b]`. From the machine-level driver (`drv_outcome`: entry 1's run, then entry 2's
run in place) and the L-level composition (`drv_twinAccepts`).
-/

namespace ConAgua.Final

open L L.Compiler L.Checker L.Arena ConRon.Arena

universe w

/-- The file's code as the driver sees it: the parallel mode's entries, the stub, the compiler's
output. -/
theorem code_of_checkerFile_par [Host] {k0 : Nat} (hcode : Code checkerFile k0) :
    Code (parStub checkerTab MODE PLO PHI OUT HDRF CTLF 132 frozenIdsL parOwnedL ++
      (abiStub checkerTab ++ compileProg checkerTab checkerProg "check")) k0 := by
  rw [checkerFile_eq, checkerStub_eq, List.append_assoc] at hcode
  exact hcode

theorem checker_seqParamsOk : seqParamsOk checkerTab OUT HDRF CTLF 132 = true := by decide

/-- `getD 0 0` is the head. -/
theorem getD_zero_headD (rs : List Word) : rs.getD 0 0 = rs.headD 0 := by cases rs <;> rfl

/-- `seqMem`'s word arrays (the globals' writes keep them). -/
theorem seqMem_arr64 (m : Mem) (lo hi : Word) (hsz : 242 < m.words.size) (a : Nat) :
    (seqMem m MODE PLO PHI OUT HDRF CTLF 132 lo hi).arr64 a =
      if a = OUT ∨ a = CTLF then #[] else if a = HDRF then (m.arr64 OUT).extract 0 132 else m.arr64 a := by
  show (seqMem0 m OUT HDRF CTLF 132).arr64 a = _
  by_cases ha : a < m.words.size
  · exact seqMem0_arr64 m OUT HDRF CTLF 132 ha
  · have h1 : (seqMem0 m OUT HDRF CTLF 132).arr64 a = #[] := by
      simp only [seqMem0, seqWords, Mem.arr64, Array.getD_eq_getD_getElem?, Array.getElem?_mapIdx,
        Array.getElem?_eq_none (Nat.le_of_not_lt ha), Option.map_none, Option.getD_none]
    have h2 : m.arr64 a = #[] := by
      simp only [Mem.arr64, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt ha),
        Option.getD_none]
    have h3 : ¬ (a = OUT ∨ a = CTLF) ∧ a ≠ HDRF := by
      simp only [OUT, CTLF, HDRF]; omega
    rw [h1, if_neg h3.1, if_neg h3.2, h2]

/-- **The driver's accept is the twin's**: `DrvAccepts` at the checker's program gives
`TwinAccepts [b]`. -/
theorem drvAccepts_twin (b pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (h : DrvAccepts checkerProg checkerTab MODE PLO PHI OUT HDRF CTLF 132 b pb) :
    TwinAccepts [b] := by
  obtain ⟨hb, hpb, h⟩ := h
  have hin : InputsOK b pb (List.replicate checkerTab.nw abiWords) :=
    ⟨h64, hb, hpb, fun n hn => by simp [List.mem_replicate] at hn; rw [hn.2]; simp [abiWords]⟩
  obtain ⟨rs₁, m₁, h₁, hnw, hcase⟩ := h
  have hsz : 242 < m₁.words.size := by rw [hnw]; decide
  have hN : abiFuel < 2 ^ 62 := by simp [abiFuel]
  rcases hcase with hacc | ⟨hge, rs₂, m₂, h₂, hacc₂⟩
  · -- entry 1 never returns `ACCEPT`: its result is `2^63 + |pend|`
    rw [getD_zero_headD] at hacc
    have hr : rs₁.headD 0 ≠ 1 := by rw [hacc]; decide
    obtain ⟨PA, m, v, hS, -, -, -, -, hres⟩ :=
      checkA_run b pb [] _ hin 3 (Or.inr rfl) abiFuel hN rs₁ m₁ h₁ hr
    have hn : PA.pend.size ≤ 2 ^ 62 := hS.loop.pend.count ▸ hS.loop.pend.bound
    have e2 : (9223372036854775808 + UInt64.ofNat PA.pend.size : Word).toNat = 2 ^ 63 + PA.pend.size := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
      simp only [UInt64.reduceToNat]; omega
    rw [hacc] at hres
    have e := congrArg UInt64.toNat hres
    rw [e2] at e
    simp only [ACCEPT, UInt64.reduceToNat] at e
    omega
  · rw [getD_zero_headD] at hge h₂ hacc₂
    refine drv_twinAccepts b pb [] _ hin abiFuel hN rs₁ m₁ h₁ hge abiFuel (by simp [abiFuel])
      (seqMem m₁ MODE PLO PHI OUT HDRF CTLF 132 0 (rs₁.headD 0 - 9223372036854775808)) rs₂ m₂
      ?_ ?_ ?_ ?_ ?_ ?_ h₂ hacc₂
    · intro a ha
      rw [seqMem_arr64 _ _ _ hsz]
      have h1 : ¬ (a = OUT ∨ a = CTLF) := by
        rintro (rfl | rfl) <;> revert ha <;> decide
      have h2 : a ≠ HDRF := by rintro rfl; revert ha; decide
      simp only [h1, h2, if_false]
    · rfl
    · rfl
    · rfl
    · rw [seqMem_arr64 _ _ _ hsz]; simp
    · simp only [rd64, seqMem_arr64 _ _ _ hsz]
      simp only [show ¬ (HDRF = OUT ∨ HDRF = CTLF) by decide, if_false, if_true]
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_extract]
      by_cases h3 : 3 < (m₁.arr64 OUT).size
      · have h4 : 3 < min 132 (m₁.arr64 OUT).size := by omega
        simp [h4]
      · have h4 : ¬ 3 < min 132 (m₁.arr64 OUT).size := by omega
        simp [h4, Array.getElem?_eq_none (Nat.le_of_not_lt h3)]

/-- **The final theorem for the driver of `checker.s`.** -/
theorem checkerFile_drv_accepts_regs [Host]
    (k0 : Nat) (hcode : Code checkerFile k0)
    (b pb : ByteArray) (h64 : System.Platform.numBits = 64) (dm : MachineData) (ra : Word)
    (hc : AbiCall b pb dm ra) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ RegsRestored dm.regs st.data.regs ∧
        (st.data.regs.rdx = 0 → st.data.regs.rax = ACCEPT → TwinAccepts [b]))
      dm (label abiStartL) :=
  eventually_weaken _ _ _ _ (fun _ ⟨hpc, hr, h, _⟩ => ⟨hpc, hr, fun h0 h1 => drvAccepts_twin b pb h64 (h h0 h1)⟩)
    (drv_outcome checkerProg checkerTab checkerTab_abiOk checkerProg_wf (by decide) MODE PLO PHI OUT
      HDRF CTLF 132 frozenIdsL parOwnedL (by decide) (by decide) (by decide) checker_seqParamsOk k0
      (code_of_checkerFile_par hcode) L.Checker.checkL checkerProg_lookup_check (by decide) b pb dm ra hc)

/-- info: 'ConAgua.Final.checkerFile_drv_accepts_regs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerFile_drv_accepts_regs

end ConAgua.Final
