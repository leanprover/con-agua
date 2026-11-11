module

import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
public import ConAgua.Arena.DeclCanonView2
import all ConAgua.Arena.DeclArms
public import ConAgua.Front.StateDR

@[expose] public section

/-!
# The quotient arm's helpers (lane `decls3`)

The pool's size bound canon's comparisons take (`poolSmall_of_stage`) and the slot word
`check_decl_quot` computes from a record's kind word (`slotOfW`, `slotOfW_eq`). The arm itself is
`cdq_ref` (`DeclAxQuotT.lean`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Ind

/-! ## The quotient arm `check_decl_quot(i, vis)` -/

open L.Front (DECL DLP DeclsF DeclAt CVAt dw quotW)

/-- The slot word `check_decl_quot` computes from the record's kind word. -/
def slotOfW (kw : Word) : Word := if kw = 1 then 0 else if kw = 2 then 1 else if kw = 3 then 2 else 3

theorem slotOfW_eq (kw : Word) : slotOfW kw = UInt64.ofNat (quotW kw).slot := by
  unfold slotOfW quotW
  by_cases h1 : kw = 1 <;> by_cases h2 : kw = 2 <;> by_cases h3 : kw = 3 <;> simp_all <;> rfl

end L.Arena
