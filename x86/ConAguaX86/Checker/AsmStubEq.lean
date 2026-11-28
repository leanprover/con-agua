module

public import ConAguaX86.Checker.AsmStub
public import ConAgua.Checker.ProgTab
public import ConAguaX86.Compiler.Abi
import ConAguaX86.AsmFile.ListEq
meta import ConAguaX86.Checker.AsmStub
meta import ConAgua.Checker.ProgTab
meta import ConAguaX86.Compiler.Abi
meta import ConAguaX86.AsmFile.ListEq

@[expose] public section

/-!
# The committed file's stub is the entry stub

`checkerStub_eq : checkerStub = parStub … ++ abiStub checkerTab`: the code of `checker.s`
before the trampoline (`checkerStub`, `ConAgua/Checker/AsmStub.lean`) is lane parmode's three
parallel-mode entries and lane `abi`'s entry stub for the checker's table
(`ConAgua/Compiler/Abi.lean`). Kernel-checked in pieces (`list_eq`,
`ConAgua/AsmFile/ListEq.lean`; 10 383 directives, ~10 s): the stub's words, ROM included, are
structural `Nat` arithmetic (`romVals`, `romWord`), cheap for the kernel.
-/

namespace L.Checker

open L.Compiler

set_option maxRecDepth 100000 in
/-- **The file's stub is the parallel mode's entries, then `abiStub checkerTab`.** -/
list_eq checkerStub_eq : checkerStub = parStub checkerTab L.Arena.MODE L.Arena.PLO L.Arena.PHI L.Arena.OUT L.Arena.HDRF L.Arena.CTLF L.Arena.hdrHw L.Arena.frozenIdsL L.Arena.parOwnedL ++ abiStub checkerTab

end L.Checker
