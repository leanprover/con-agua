import ConAgua.AsmFile.Include

/-!
# The checker's code: the file `checker.s`

`checkerFile` is the code of the committed assembler file `checker.s` (the entry stub, the
trampoline and the checker's functions: the exact file `main.c` is assembled with), read
by the trusted parser when this module is elaborated (`include_asm`,
`ConAgua/AsmFile/Include.lean`). The final theorems are stated about it
(`ConAgua/Checker/AsmFinal.lean`); `checkerFile_eq` (`ConAgua/Checker/AsmFileEq.lean`) relates it
to the compiler's output. This module is in the library `ConAguaAsm`, which `needs` the file
(`lakefile.toml`), so Lake rebuilds it when the file changes.
-/

namespace L.Checker

/-- **The checker's code**: the `.text` section of `checker.s`. -/
noncomputable def checkerFile : Program := include_asm "../checker.s"

end L.Checker
