module

public import ConAgua.Final.DrvAbi
public import ConAgua.Checker.ParDriverTwin
import ConAgua.Checker.BlockRefsProg
import ConAgua.Checker.AsmFinal
import ConAgua.Checker.AsmStubEq
import ConAgua.Checker.AsmFileEq
import ConAgua.Checker.AsmTailEq
import ConAgua.Checker.ProgIRef
import ConAgua.Checker.AsmXOk
public import ConAgua.Checker.AsmX
import ConAgua.Checker.ProgWf
import ConAgua.Checker.CheckARun
public import ConAgua.Checker.ProgI
public import ConAguaAsm.Checker
import all ConAgua.Checker.Entry
import ConAgua.Checker.DefnArmT
import ConAgua.Checker.IndArm
import ConAgua.L.WordOff

@[expose] public section

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
    Code (parStub checkerTab MODE PLO PHI OUT HDRF CTLF 138 frozenIdsL parOwnedL ++
      (abiStub checkerTab ++ compileProgX checkerX checkerTab checkerProgI "check")) k0 := by
  rw [checkerFile_eq, checkerStub_eq, List.append_assoc, ← List.append_assoc (abiStub checkerTab),
    ← List.append_assoc] at hcode
  exact hcode.left

/-- The file's code as the compared run's driver sees it: as `code_of_checkerFile_par`, then the
compared run's entries and driver (`cmpStub`, the file's tail). -/
theorem code_of_checkerFile_cmp [Host] {k0 : Nat} (hcode : Code checkerFile k0) :
    Code (parStub checkerTab MODE PLO PHI OUT HDRF CTLF 138 frozenIdsL parOwnedL ++
      (abiStub checkerTab ++ (compileProgX checkerX checkerTab checkerProgI "check" ++
        cmpStub checkerTab MODE OUT parOwnedL))) k0 := by
  rw [checkerFile_eq, checkerStub_eq, checkerTail_eq, List.append_assoc] at hcode
  exact hcode

theorem checker_seqParamsOk : seqParamsOk checkerTab OUT HDRF CTLF 138 = true := by decide +kernel

/-- `seqMem`'s word arrays (the globals' writes keep them). -/
theorem seqMem_arr64 (m : Mem) (lo hi : Word) (s : TieredArray) :
    (seqMem m MODE PLO PHI OUT HDRF CTLF 138 lo hi).arr64 s =
      if s = ↑OUT ∨ s = ↑CTLF then #[] else if s = ↑HDRF then (m.arr64 OUT).extract 0 138 else m.arr64 s :=
  seqMem0_arr64 m OUT HDRF CTLF 138 s

/-- **`check_decl`'s program facts at every run of entry 1's stages** (`CheckerCd`, at every
`PhaseA`: the stages and the stream index): the definition arm's
(`checkerProg_defnLoopPB`) and the inductive arm's (`indArmSpec_checker`). -/
theorem checkerCd_proved : L.Checker.CheckerCd := fun _ pb PA hpb hpre =>
  have hr : L.Rom.RomOK pb.data.toList := by simpa [L.Rom.RomOK] using hpb
  ⟨L.Checker.checkerProg_defnLoopPB _ hr hpre,
    L.Checker.indArmSpec_checker _ hr hpre
      (L.Checker.cbRefs_checker _ hr hpre (L.Checker.snoSim_checker _)) _ PA.dnInj⟩

/-- **The driver's accept is the twin's**: `DrvAccepts` at the checker's program gives
`TwinAccepts [b]`. -/
theorem drvAccepts_twin (b pb : ByteArray)
    (h64 : System.Platform.numBits = 64)
    (h : DrvAccepts checkerTab checkerProg MODE PLO PHI OUT HDRF CTLF 138 b pb) :
    TwinAccepts [b] := by
  obtain ⟨hb, hpb, h⟩ := h
  have hin : InputsOK b pb (abiSz checkerTab) := ⟨h64, hb, hpb, fun s => by
    have := abiSz_le checkerTab_abiOk s; simp only [abiWords] at this; omega⟩
  obtain ⟨rs₁, m₁, h₁, hcase⟩ := h
  have hN : abiFuel < 2 ^ 62 := by simp [abiFuel]
  rcases hcase with hacc | ⟨hge, rs₂, m₂, h₂, hacc₂⟩
  · -- entry 1 never returns `ACCEPT`: its result is `2^63 + |ds|`
    rw [L.getD_zero] at hacc
    have hr : rs₁.headD 0 ≠ 1 := by rw [hacc]; decide
    obtain ⟨PA, m₇, m, hF, -, -, hres⟩ :=
      checkA_run b pb _ hin 3 (Or.inr rfl) abiFuel hN rs₁ m₁ h₁ hr
    have hn : PA.ds.size < 2 ^ 63 := by
      have := hF.build.decls.room; have := hF.build.decls.dsize; omega
    have e2 : (9223372036854775808 + UInt64.ofNat PA.ds.size : Word).toNat = 2 ^ 63 + PA.ds.size := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
      simp only [UInt64.reduceToNat]; omega
    rw [hacc] at hres
    have e := congrArg UInt64.toNat hres
    rw [e2] at e
    simp only [ACCEPT, UInt64.reduceToNat] at e
    omega
  · rw [L.getD_zero] at hge h₂ hacc₂
    refine drv_twinAccepts checkerCd_proved b pb _ hin abiFuel hN rs₁ m₁ h₁ hge abiFuel (by simp [abiFuel])
      (seqMem m₁ MODE PLO PHI OUT HDRF CTLF 138 0 (rs₁.headD 0 - 9223372036854775808)) rs₂ m₂
      ?_ rfl rfl rfl ?_ h₂ hacc₂
    · intro a ha
      rw [seqMem_arr64]
      have h1 : ¬ (a = ↑OUT ∨ a = ↑CTLF) := by
        rintro (rfl | rfl) <;> revert ha <;> decide
      have h2 : a ≠ ↑HDRF := by rintro rfl; revert ha; decide
      simp only [h1, h2, ite_false]
    · rw [seqMem_arr64]; simp

/-- **The final theorem for the driver of `checker.s`**. -/
theorem checkerFile_drv_accepts_regs [Host]
    (k0 : Nat) (hcode : Code checkerFile k0)
    (b pb : ByteArray) (h64 : System.Platform.numBits = 64) (dm : MachineData) (ra : Word)
    (hc : AbiCall b pb dm ra) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ RegsRestored dm.regs st.data.regs ∧
        (st.data.regs.rdx = 0 → st.data.regs.rax = ACCEPT → TwinAccepts [b]))
      dm (label abiStartL) :=
  eventually_weaken _ _ _ _ (fun _ ⟨hpc, hr, h, _⟩ => ⟨hpc, hr, fun h0 h1 => drvAccepts_twin b pb h64 (h h0 h1)⟩)
    (drv_outcome checkerProgI checkerProg checkerProgI_refines checkerTab checkerTab_abiOk checkerX_ok checkerTab_abiIO checkerProgI_wf (by decide) MODE PLO PHI OUT
      HDRF CTLF 138 frozenIdsL parOwnedL (by decide) (by decide) (by decide) checker_seqParamsOk k0
      (code_of_checkerFile_par hcode) L.Checker.checkL checkerProg_lookup_check (by decide) b pb dm ra hc)

/-- info: 'ConAgua.Final.checkerFile_drv_accepts_regs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerFile_drv_accepts_regs

end ConAgua.Final
