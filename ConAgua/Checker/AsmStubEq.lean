import ConAgua.Checker.AsmFileEq
import ConAgua.Compiler.Abi
import ConAgua.AsmFile.ListEq
import ConAgua.Arena.Freeze

/-!
# The committed file's stub is the entry stub

`checkerStub_eq : checkerStub = parStub … ++ abiStub checkerTab`: the code of `checker.s`
before the trampoline (`checkerStub`, `ConAgua/Checker/AsmFileEq.lean`) is lane parmode's three
parallel-mode entries and lane `abi`'s entry stub for the checker's table
(`ConAgua/Compiler/Abi.lean`). Kernel-checked in pieces (`list_eq`,
`ConAgua/AsmFile/ListEq.lean`; 10 383 directives, ~10 s): the stub's words, ROM included, are
structural `Nat` arithmetic (`romVals`, `romWord`), cheap for the kernel.
-/

namespace L.Checker

open L.Compiler

/-- **The file's stub is the parallel mode's entries, then `abiStub checkerTab`.** -/
list_eq checkerStub_eq : checkerStub = parStub checkerTab L.Arena.MODE L.Arena.PLO L.Arena.PHI L.Arena.OUT L.Arena.HDRF L.Arena.CTLF 132 L.Arena.frozenIdsL L.Arena.parOwnedL ++ abiStub checkerTab

end L.Checker
