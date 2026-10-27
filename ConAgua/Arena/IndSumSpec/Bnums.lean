import ConRon.Arena.Handle
import Std.WP.Assertion
import ConAgua.Arena.Reasons

/-!
# Bnums

`bnums`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `struct_used_later_list`: the relation to the twin -/

/-- The numbers a list of answers is stored as. -/
def bnums (bs : List Bool) : List Nat := bs.map (fun b => if b then 1 else 0)

end L.Ind
end
