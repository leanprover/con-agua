import ConAgua.Checker.AsmFinal
import ConAgua.Checker.LoopStage

/-!
# The end-to-end theorem so far, from exactly what it still assumes (lane `loopt3`)

`checkerFile_accepts` (`Checker/AsmFinal.lean`) assumes `PipelineRefines checkerProg`; lane
`pipeline`'s `pipelineRefines_checker` reduces that to `LoopStage checkerProg checkerRels`, and
`loopStage_of` (`Checker/LoopStage.lean`) reduces that to the named hypotheses below. Each later
landing discharges one of them; `#print axioms` lists the `sorry`s the proved parts still rest on
(the stub contracts the census lists).
-/

namespace ConAgua.Final

open L L.Compiler L.Checker L.Arena ConRon.Arena

/-- **The final theorem for the committed file `asm/checker.s`** (called through the entry stub
`ca_start`, `AbiCall`), from the one named hypothesis still open: the inductive arm's contract
`IndArmSpec` (lane `indproofs4`) at the checker's program with the ROM substituted. -/
theorem checkerFile_accepts_remaining [Host]
    (hIA : ∀ bs dn, L.Ind.DnInj dn → IndArmSpec (checkerProg.subPB bs) dn)
    (k0 : Nat) (hcode : Code checkerFile k0)
    (b pb : ByteArray) (h64 : System.Platform.numBits = 64) (hb : b.size < 2 ^ 63)
    (hpb : pb.size < 2 ^ 63) (dm : MachineData) (ra : Word) (hc : AbiCall b pb dm ra) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧
        (st.data.regs.rdx = 0 → st.data.regs.rax = ACCEPT → TwinAccepts [b]))
      dm (label abiStartL) :=
  checkerFile_accepts (pipelineRefines_checker (loopStage_of hIA)) k0 hcode b pb h64 hb hpb dm ra hc

#print axioms checkerFile_accepts_remaining

end ConAgua.Final
