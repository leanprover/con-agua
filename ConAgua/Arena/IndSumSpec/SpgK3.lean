import ConAgua.Arena.IndSim
import ConAgua.Arena.IndSumSpec.ColW

/-!
# SpgK3

`spgK3`, `spgK2`, `spgK2_some`, `spgK3_some`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The word model -/

/-- After the row. -/
def spgK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, r.tail.headD 0], m)
/-- After `struct_used_later_list`: the rows. -/
def spgK2 (n : Nat) (so sl z nF : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (u, m) => spgK3 (rowW n m (u.headD 0) (u.tail.headD 0) so sl z 0 nF)
section arms
variable (n : Nat) (m m1 : Mem) (cty nP nF so sl z : Word) (r u : List Word)
theorem spgK2_some : spgK2 n so sl z nF (some (u, m1)) =
    spgK3 (rowW n m1 (u.headD 0) (u.tail.headD 0) so sl z 0 nF) := rfl
theorem spgK3_some : spgK3 (some (r, m1)) = some ([r.headD 0, r.tail.headD 0], m1) := rfl
end arms
attribute [ind_grind] spgK2_some spgK3_some

end L.Ind

end
