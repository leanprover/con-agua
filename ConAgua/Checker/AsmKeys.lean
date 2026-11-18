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

/-- **The name codes of the hand-written functions.** -/
def checkerXKeys : List Nat := [mulRowCode, subRowCode]

end L.Checker
