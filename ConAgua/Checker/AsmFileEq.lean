module

public import ConAgua.Checker.Asm
public import ConAgua.Checker.AsmStub
public import ConAgua.Checker.AsmTail
import ConAgua.AsmFile.Eq
meta import ConAgua.Checker.Asm
meta import ConAgua.Checker.AsmStub
meta import ConAgua.Checker.AsmTail
meta import ConAgua.AsmFile.Eq

@[expose] public section

/-!
# The committed file is the compiler's output

`checkerFile_eq : checkerFile = checkerStub ++ (compileProgX checkerX checkerTab checkerProgI "check" ++ checkerTail)`: the code
of `checker.s` (`checkerFile`, read by the trusted parser, `ConAguaAsm/Checker.lean`) is the
entry stub `checkerStub` (`ConAgua/Checker/AsmStub.lean`; lane `abi`'s `abiStub checkerTab`:
`checkerStub_eq`, `ConAgua/Checker/AsmStubEq.lean`) followed by the compiled checker and the tail
`checkerTail` (`ConAgua/Checker/AsmTail.lean`; lane compare's `cmpStub`: `checkerTail_eq`,
`ConAgua/Checker/AsmTailEq.lean`).
Kernel-checked (`asm_file_eq`, `ConAgua/AsmFile/Eq.lean`): structurally against `checkerAsm`, whose equation with the compiler's output the kernel checked
function by function (`ConAgua/Checker/Asm.lean`). A file that is not the compiler's output
(stale, or printed wrongly) fails here, naming the first function that differs; regenerate it with
`scripts/asm_file.py`.
-/

namespace L.Checker

open L.Compiler

/-- **The committed file is the compiler's output**, after the entry stub `checkerStub` and before
the tail `checkerTail`. -/
asm_file_eq checkerFile_eq : checkerFile = checkerStub ++ checkerAsm ++ checkerTail via checkerAsm_eq

end L.Checker
