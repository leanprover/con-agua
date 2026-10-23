import ConAgua.AsmFile.Eq
import ConAgua.Checker.Asm
import ConAgua.Compiler.Abi
import ConAguaAsm.Checker

/-!
# The committed file is the compiler's output

`checkerFile_eq : checkerFile = abiStub checkerTab ++ compileProg checkerTab checkerProg "check"`:
the code of `asm/checker.s` (`checkerFile`, read by the trusted parser, `ConAguaAsm/Checker.lean`)
is the entry stub followed by the compiled checker. Kernel-checked (`asm_file_eq`,
`ConAgua/AsmFile/Eq.lean`): the stub by evaluation, the rest structurally against `checkerAsm`,
whose equation with the compiler's output the kernel checked function by function
(`ConAgua/Checker/Asm.lean`). A file that is not the compiler's output (stale, or printed wrongly)
fails here, naming the first function that differs; regenerate it with `scripts/asm_file.py`.
-/

namespace L.Checker

open L.Compiler

set_option profiler true in
asm_file_eq checkerFile_eq : checkerFile = (abiStub checkerTab) ++ checkerAsm via checkerAsm_eq

end L.Checker
