module

public import ConAgua.Final.CmpMain
public import ConAgua.Final.CmpChain
import ConAgua.Checker.AsmFinal
import ConAgua.Checker.ProgIRef
import ConAgua.Checker.AsmXOk
import ConAgua.Checker.ProgWf
import ConAgua.Final.DrvFinal
import all ConAgua.Checker.Entry

@[expose] public section

/-!
# The compared run's end-to-end theorems (lane compare)

What is proved about the committed assembly file `checker.s` when it is called at the compared
run's driver `ca_compare` (`CmpCall`: the challenge's and the solution's bytes, the pins, a zero
region, the machine stack; and `numBits = 64`).

* `checkerFile_compare_runs_regs`: the machine returns to the return address `ra` with the
  caller's callee-saved registers intact; `rdx = 0`, `rax = ACCEPT` means the L runs of the
  compared mode accepted (`CmpAccepts`), `rdx = 2` that one failed with the code in `rax`
  (`CmpErr`).
-/

namespace ConAgua.Final

open L L.Compiler L.Checker L.Arena

/-- **The compared run's driver of `checker.s` on the machine, at the L level.** From
`ca_compare`, called as `CmpCall` says, the machine returns to `ra` with the callee-saved
registers restored, and its verdict is the L runs' (`CmpAccepts`, `CmpErr`). -/
theorem checkerFile_compare_runs_regs [Host] (k0 : Nat) (hcode : Code checkerFile k0)
    (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (sa : Word) (dm : MachineData) (ra : Word) (hc : CmpCall bC bS pb sa dm ra) :
    Ev (CmpPost dm ra
        (CmpAccepts checkerTab checkerProg MODE PLO PHI OUT HDRF CTLF 138 frozenIdsL parOwnedL bC bS pb)
        (CmpErr checkerTab checkerProg MODE PLO PHI OUT HDRF CTLF 138 frozenIdsL parOwnedL bC bS pb))
      dm (label abiCompareL) :=
  cmp_outcome_regs checkerProgI checkerProg checkerProgI_refines checkerTab checkerTab_abiOk checkerX_ok
    checkerTab_abiIO checkerProgI_wf (by decide) MODE PLO PHI OUT HDRF CTLF 138 frozenIdsL parOwnedL
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    checker_seqParamsOk checker_bufMinOk parOwnedL_not_frozen (by decide +kernel)
    (fun a ha => List.all_eq_true.mp frozenIdsL_dom a ha) (by decide +kernel) k0
    (code_of_checkerFile_cmp hcode) L.Checker.checkL checkerProg_lookup_check (by decide)
    bC bS pb sa dm ra hc (checker_cmpGuard bC bS pb h64)

/-- info: 'ConAgua.Final.checkerFile_compare_runs_regs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerFile_compare_runs_regs

end ConAgua.Final
