import ConAgua.Arena.IndInstallSpec.GrcProg

/-!
# DecISS

`decISS`.
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- A member's fields' sorts: a pointer to `[off, len]` of `[off, len]` level-handle slices. -/
def decISS (m : Mem) (q : Nat) : Option (List (List LIdx)) := decAt m (fun o l => decPL m (decIS m) o l) q

end L.Ind

end
