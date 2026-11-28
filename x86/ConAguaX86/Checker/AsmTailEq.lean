module

public import ConAguaX86.Checker.AsmTail
public import ConAgua.Checker.ProgTab
public import ConAguaX86.Compiler.AbiCmp
import ConAguaX86.AsmFile.ListEq
meta import ConAguaX86.Checker.AsmTail
meta import ConAgua.Checker.ProgTab
meta import ConAguaX86.Compiler.AbiCmp
meta import ConAguaX86.AsmFile.ListEq

@[expose] public section

/-!
# The committed file's tail is the compared run's driver

`checkerTail_eq : checkerTail = cmpStub checkerTab MODE`: the code of `checker.s`
after the compiled checker (`checkerTail`, `ConAgua/Checker/AsmTail.lean`) is the compared run's
entries (modes 4 to 7; `ca_start_c`, `ca_start_ac`; `ConAgua/Compiler/AbiCmp.lean`).
Kernel-checked by `list_eq` (`ConAgua/AsmFile/ListEq.lean`).
-/

namespace L.Checker

open L.Compiler

set_option maxRecDepth 100000 in
/-- **The file's tail is `cmpStub checkerTab`.** -/
list_eq checkerTail_eq : checkerTail = cmpStub checkerTab L.Arena.MODE

end L.Checker
