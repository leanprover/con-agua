module

public import ConAguaX86.AsmEsc.SubRowAsm
public import ConAguaX86.AsmEsc.DivSubmulAsm
public import ConAguaX86.AsmEsc.Chain1
public import ConAguaX86.AsmEsc.NatMadAsm
public import ConAguaX86.AsmEsc.NatCmpAsm
public import ConAguaX86.AsmEsc.BitAsm
public import ConAguaX86.AsmEsc.ShiftAsm
public import ConAguaX86.AsmEsc.LitHashAsm
public import ConAgua.Checker.ProgTab
public import ConAgua.Checker.AsmKeys

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
* `div_submul` (`L.Arena.divSubmul`, long division's multiply-subtract step): `divSubmulAsm`,
  `ConAgua/AsmEsc/DivSubmulAsm.lean`.
* `add_n`, `sub_n`, `add_1`, `sub_1` (`L.Arena.addN` …, the bignum's carry chains): the templates
  `chain2Asm` (`ConAgua/AsmEsc/Chain2.lean`) and `chain1Asm` (`Chain1.lean`).
* `nat_mad` (`L.Front.natMad`, the decimal reader's multiply-add): `natMadAsm`,
  `ConAgua/AsmEsc/NatMadAsm.lean`.
* `nat_cmp` (`L.Arena.natCmp`, the comparison of two numbers): `natCmpAsm`,
  `ConAgua/AsmEsc/NatCmpAsm.lean`.
* `and_n`, `or_n`, `xor_n`, `copy_n` (linleaf's bitwise and copy leaves): the templates `bitAsm`
  and `copyAsm`, `ConAgua/AsmEsc/BitAsm.lean` (proofs in `BitAsmSim.lean`).
* `lit_hash` (`L.Arena.litHash`, the hash of a literal's limbs): `litHashAsm`,
  `ConAgua/AsmEsc/LitHashAsm.lean`.
* `shl_n`, `shr_n`, `zero_n` (linleaf's shift and zeroing leaves): `shlAsm` (`shld`), `shrAsm`
  (`shrd`), `zeroAsm`, `ConAgua/AsmEsc/ShiftAsm.lean` (proofs in `ShiftAsmSim.lean`).
-/

namespace L.Checker

open L L.Compiler L.AsmEsc

/-- **The hand-written bodies of the checker.** -/
def checkerX : AsmTab :=
  [(mulRowCode, mulRowAsm checkerTab), (subRowCode, subRowAsm checkerTab),
   (divSubmulCode, divSubmulAsm checkerTab),
   (addNCode, chain2Asm checkerTab "add_n" false), (add1Code, chain1Asm checkerTab "add_1" false),
   (subNCode, chain2Asm checkerTab "sub_n" true), (sub1Code, chain1Asm checkerTab "sub_1" true),
   (natMadCode, natMadAsm checkerTab), (natCmpCode, natCmpAsm checkerTab),
   (andNCode, bitAsm checkerTab "and_n" .and), (orNCode, bitAsm checkerTab "or_n" .or),
   (xorNCode, bitAsm checkerTab "xor_n" .xor), (copyNCode, copyAsm checkerTab "copy_n"),
   (litHashCode, litHashAsm checkerTab),
   (shlNCode, shlAsm checkerTab), (shrNCode, shrAsm checkerTab), (zeroNCode, zeroAsm checkerTab)]

/-- The inliner's exclusion list is `checkerX`'s keys. -/
theorem checkerX_keys : checkerX.map (·.1) = checkerXKeys := rfl

end L.Checker
