module

public import ConAguaAsm.Checker
import ConAgua.AsmFile.Eq
meta import ConAguaAsm.Checker
meta import ConAgua.AsmFile.Eq

@[expose] public section

/-!
# The committed file's tail

`checkerTail`: the code of `checker.s` after the compiled checker, from the label `ca_start_a4`
on (`asm_tail`, `ConAgua/AsmFile/Eq.lean`): the compared run's entries and driver (`cmpStub`,
`ConAgua/Compiler/AbiCmp.lean`). Apart from `AsmFileEq.lean`, as `AsmStub.lean`, so that
`checkerTail_eq` (`ConAgua/Checker/AsmTailEq.lean`) does not wait for the compiled checker.
-/

namespace L.Checker

open L.Compiler

/-- **The file's code after the compiled checker** (the compared run's driver). -/
asm_tail checkerTail : checkerFile from "ca_start_a4"

end L.Checker
