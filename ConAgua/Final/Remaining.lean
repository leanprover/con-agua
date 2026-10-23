import ConAgua.Checker.AsmFinal
import ConAgua.Checker.LoopStage

/-!
# The end-to-end theorem so far, from exactly what it still assumes (lane `loopt3`)

`checkerAsm_accepts` (`Checker/AsmFinal.lean`) assumes `PipelineRefines checkerProg`; lane
`pipeline`'s `pipelineRefines_checker` reduces that to `LoopStage checkerProg checkerRels`, and
`loopStage_of` (`Checker/LoopStage.lean`) reduces that to the named hypotheses below. Each later
landing discharges one of them; `#print axioms` lists the `sorry`s the proved parts still rest on
(the stub contracts the census lists).
-/

namespace ConAgua.Final

open L L.Compiler L.Checker L.Arena ConRon.Arena

/-- **`checker_x64_accepts` for the checker's code**, from the hypotheses still open:
the declaration loop's program hypotheses at `checkerProg` with the ROM substituted
(`LoopCallees`, which contains the inductive arm's contract `IndArmSpec`, and `LoopTopProg`). -/
theorem checkerAsm_accepts_remaining [Host]
    (hLC : ∀ bs dn, L.Ind.DnInj dn → QuotDn dn → LoopCallees dn (checkerProg.subPB bs))
    (hTop : ∀ bs, LoopTopProg (checkerProg.subPB bs))
    (G : L.Compiler.Layout) (hG : G.Ok) (htab : G.tab = checkerTab)
    (k0 : Nat) (hcode : Code checkerAsm k0) (hnargs : G.nargs = 0)
    (b pb : ByteArray) (h64 : System.Platform.numBits = 64) (hb : b.size < 2 ^ 63)
    (hpb : pb.size < 2 ^ 63)
    (s8 s64 : List Nat) (N : Nat) (hN62 : N < 2 ^ 62) (dm : MachineData) (ra : Word)
    (hmem : MemRel G (loadMem b pb s8 s64) dm.dmem) (hc : HarnessCall G N dm ra) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧
        (st.data.regs.rdx = 0 → st.data.regs.rax = ACCEPT → TwinAccepts [b]))
      dm (label enterL) :=
  checkerAsm_accepts (pipelineRefines_checker (loopStage_of hLC hTop)) G hG htab k0
    hcode hnargs b pb h64 hb hpb s8 s64 N hN62 dm ra hmem hc

#print axioms checkerAsm_accepts_remaining

end ConAgua.Final
