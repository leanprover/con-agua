import ConAguaAsm.Checker
import ConAgua.AsmFile.Eq

/-!
# The committed file's stub

`checkerStub`: the code of `checker.s` before the trampoline (`asm_stub`,
`ConAgua/AsmFile/Eq.lean`), apart from `AsmFileEq.lean` so that `checkerStub_eq`
(`ConAgua/Checker/AsmStubEq.lean`) does not wait for the compiled checker (`checkerAsm`).
-/

namespace L.Checker

open L.Compiler

/-- **The file's code before the trampoline** (the entry stub). -/
asm_stub checkerStub : checkerFile

end L.Checker
