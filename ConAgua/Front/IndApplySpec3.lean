import ConAgua.Front.IndApply
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# The apply step of an `inductive` line, III: the entries' lookups

`apply_ind(v)` runs `ind_fields`, `validate_ind_d`, `install_ind_d` in sequence (its unified model
`applyIndE` and its refinement `applyInd_ref`, `FrontPreOK2.lean`); `apply_ind_line(j)` applies the
line's one member (`next_member`, key `23`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order
open L.Arena
open L.Scan.Member

namespace L.Front.Ind

/-- The two entries, at their names in `p`. -/
structure IndLineLookups (p : Prog) : Prop where
  apply_ind : p.lookup "apply_ind" = some applyInd
  apply_ind_line : p.lookup "apply_ind_line" = some applyIndLine

end L.Front.Ind
