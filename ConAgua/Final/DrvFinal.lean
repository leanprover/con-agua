module

public import ConAgua.Final.DrvAbi
import ConAgua.Checker.ParDriverTwin
import ConAgua.Checker.AsmFinal
import ConAgua.Checker.AsmStubEq
import ConAgua.Checker.AsmFileEq
import ConAgua.Checker.ProgIRef
import ConAgua.Checker.ProgWf
import ConAgua.Checker.CheckARun
public import ConAgua.Checker.ProgI
public import ConAgua.Checker.ProgTab
public import ConAgua.Final.Twin
public import ConAguaAsm.Checker
import all ConAgua.Checker.Entry

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
    Code (parStub checkerTab MODE PLO PHI OUT HDRF CTLF 136 frozenIdsL parOwnedL ++
      (abiStub checkerTab ++ compileProg checkerTab checkerProgI "check")) k0 := by
  rw [checkerFile_eq, checkerStub_eq, List.append_assoc] at hcode
  exact hcode

theorem checker_seqParamsOk : seqParamsOk checkerTab OUT HDRF CTLF 136 = true := by decide +kernel

/-- `getD 0 0` is the head. -/
theorem getD_zero_headD (rs : List Word) : rs.getD 0 0 = rs.headD 0 := by cases rs <;> rfl

/-- `seqMem`'s word arrays (the globals' writes keep them). -/
theorem seqMem_arr64 (m : Mem) (lo hi : Word) (s : TieredArray) :
    (seqMem m MODE PLO PHI OUT HDRF CTLF 136 lo hi).arr64 s =
      if s = ↑OUT ∨ s = ↑CTLF then #[] else if s = ↑HDRF then (m.arr64 OUT).extract 0 132 else m.arr64 s := by
  sorry

/-- **The driver's accept is the twin's**: `DrvAccepts` at the checker's program gives
`TwinAccepts [b]`. -/
theorem drvAccepts_twin (b pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (h : DrvAccepts checkerTab checkerProg MODE PLO PHI OUT HDRF CTLF 136 b pb) :
    TwinAccepts [b] := by
  sorry

/-- **The final theorem for the driver of `checker.s`.** -/
theorem checkerFile_drv_accepts_regs [Host]
    (k0 : Nat) (hcode : Code checkerFile k0)
    (b pb : ByteArray) (h64 : System.Platform.numBits = 64) (dm : MachineData) (ra : Word)
    (hc : AbiCall b pb dm ra) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ RegsRestored dm.regs st.data.regs ∧
        (st.data.regs.rdx = 0 → st.data.regs.rax = ACCEPT → TwinAccepts [b]))
      dm (label abiStartL) := by
  sorry

/-- info: 'ConAgua.Final.checkerFile_drv_accepts_regs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
-- ronsync2 stage 2: #guard_msgs in #print axioms checkerFile_drv_accepts_regs

end ConAgua.Final
