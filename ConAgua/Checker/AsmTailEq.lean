module

public import ConAgua.Checker.AsmTail
public import ConAgua.Checker.ProgTab
public import ConAgua.Compiler.AbiCmp
import ConAgua.AsmFile.ListEq
meta import ConAgua.Checker.AsmTail
meta import ConAgua.Checker.ProgTab
meta import ConAgua.Compiler.AbiCmp
meta import ConAgua.AsmFile.ListEq

@[expose] public section

/-!
# The committed file's tail is the compared run's driver

`checkerTail_eq : checkerTail = cmpStub checkerTab MODE OUT parOwnedL ++ ctaStub checkerTab MODE`: the code of `checker.s`
after the compiled checker (`checkerTail`, `ConAgua/Checker/AsmTail.lean`) is lane compare's
entries of modes 4–6 and the driver `ca_compare`, then lane compare2's entry of mode 7 (`ctaStub`;
`ConAgua/Compiler/AbiCmp.lean`).
Kernel-checked by `list_eq` (`ConAgua/AsmFile/ListEq.lean`).
-/

namespace L.Checker

open L.Compiler

set_option maxRecDepth 100000 in
/-- **The file's tail is `cmpStub checkerTab ++ ctaStub checkerTab`.** -/
list_eq checkerTail_eq : checkerTail = cmpStub checkerTab L.Arena.MODE L.Arena.OUT L.Arena.parOwnedL ++
  ctaStub checkerTab L.Arena.MODE

end L.Checker
