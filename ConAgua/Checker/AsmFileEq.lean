import ConAgua.Checker.Asm
import ConAguaAsm.Checker
import ConAgua.AsmFile.Eq

/-!
# The committed file is the compiler's output

`checkerFile_eq : checkerFile = checkerStub ++ compileProg checkerTab checkerProg "check"`: the code
of `checker.s` (`checkerFile`, read by the trusted parser, `ConAguaAsm/Checker.lean`) is the
entry stub `checkerStub` (lane `abi`'s `abiStub checkerTab`: `checkerStub_eq`,
`ConAgua/Checker/AsmStubEq.lean`)
followed by the compiled checker. Kernel-checked (`asm_file_eq`, `ConAgua/AsmFile/Eq.lean`):
structurally against `checkerAsm`, whose equation with the compiler's output the kernel checked
function by function (`ConAgua/Checker/Asm.lean`). A file that is not the compiler's output
(stale, or printed wrongly) fails here, naming the first function that differs; regenerate it with
`scripts/asm_file.py`.
-/

namespace L.Checker

open L.Compiler

/-- **The committed file is the compiler's output**, after the entry stub `checkerStub`. -/
asm_file_eq checkerFile_eq : checkerFile = checkerStub ++ checkerAsm via checkerAsm_eq

end L.Checker
