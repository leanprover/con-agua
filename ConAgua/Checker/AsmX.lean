module

public import ConAgua.AsmEsc.SubRowAsm
public import ConAgua.Checker.ProgTab

@[expose] public section

/-!
# The checker's hand-written function bodies

`checkerX`: the bodies that replace the compiled code of some functions of the checker
(`compileProgX`, `ConAgua/Compiler/Compile.lean`), keyed by the function name's code (`nameCode`).
Each keeps its L function (every L-level proof is about that) and is proved against the compiler
proof's per-function contract (`checkerX_ok`, `AsmXOk.lean`).

* `mul_row` (`L.Arena.mulRow`, the bignum multiply-accumulate row): `mulRowAsm`,
  `ConAgua/AsmEsc/MulRowAsm.lean`.
* `sub_row` (`L.Arena.subRow`, the in-place subtraction of Karatsuba's middle term): `subRowAsm`,
  `ConAgua/AsmEsc/SubRowAsm.lean`.
-/

namespace L.Checker

open L L.Compiler L.AsmEsc

/-- `nameCode "mul_row"`, as a literal (`nameCode_mul_row`). -/
abbrev mulRowCode : Nat := 34702489570787084

/-- `nameCode "sub_row"`, as a literal (`nameCode_sub_row`). -/
abbrev subRowCode : Nat := 34702489570126600

/-- **The hand-written bodies of the checker.** -/
def checkerX : AsmTab := [(mulRowCode, mulRowAsm checkerTab), (subRowCode, subRowAsm checkerTab)]

end L.Checker
