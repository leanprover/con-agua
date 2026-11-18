module

@[expose] public section

/-!
# The names of the checker's hand-written functions

`checkerXKeys`: the name codes (`nameCode`) of the functions that have a hand-written body
(`checkerX`, `ConAgua/Checker/AsmX.lean`; `checkerX_keys`). The inliner leaves their calls as calls
(`envOf`'s exclusion list, `ConAgua/Checker/ProgI.lean`), so the hand-written code is what runs. A
module of its own, without the bodies and their proofs, so that the inlined program does not
depend on them.
-/

namespace L.Checker

/-- `nameCode "mul_row"`, as a literal (`nameCode_mul_row`). -/
abbrev mulRowCode : Nat := 34702489570787084

/-- `nameCode "sub_row"`, as a literal (`nameCode_sub_row`). -/
abbrev subRowCode : Nat := 34702489570126600

/-- `nameCode "div_submul"`, as a literal (`nameCode_div_submul`). -/
abbrev divSubmulCode : Nat := 535373398662674939474756

/-- `nameCode "add_n"`, as a literal (`nameCode_add_n`). -/
abbrev addNCode : Nat := 485870472443

/-- `nameCode "add_1"`, as a literal (`nameCode_add_1`). -/
abbrev add1Code : Nat := 219759777982

/-- `nameCode "sub_n"`, as a literal (`nameCode_sub_n`). -/
abbrev subNCode : Nat := 485870344732

/-- `nameCode "sub_1"`, as a literal (`nameCode_sub_1`). -/
abbrev sub1Code : Nat := 219759650271

/-- `nameCode "nat_mad"`, as a literal (`nameCode_nat_mad`). -/
abbrev natMadCode : Nat := 29212172247658203

/-- `nameCode "nat_cmp"`, as a literal (`nameCode_nat_cmp`). -/
abbrev natCmpCode : Nat := 32683224171858665

/-- `nameCode "and_n"`, as a literal (`nameCode_and_n`). -/
abbrev andNCode : Nat := 485870475013

/-- `nameCode "or_n"`, as a literal (`nameCode_or_n`). -/
abbrev orNCode : Nat := 1890550194

/-- `nameCode "xor_n"`, as a literal (`nameCode_xor_n`). -/
abbrev xorNCode : Nat := 485871399979

/-- `nameCode "copy_n"`, as a literal (`nameCode_copy_n`). -/
abbrev copyNCode : Nat := 124869068680590

/-- **The name codes of the hand-written functions.** -/
def checkerXKeys : List Nat :=
  [mulRowCode, subRowCode, divSubmulCode, addNCode, add1Code, subNCode, sub1Code, natMadCode, natCmpCode, andNCode, orNCode, xorNCode,
   copyNCode]

end L.Checker
