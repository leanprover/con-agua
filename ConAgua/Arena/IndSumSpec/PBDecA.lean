import ConAgua.Arena.IndRealIlpP

/-!
# PBDecA

`PBDecA`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- What `struct_proj_bodies` returns: `(0, _, _)` for `none`, `(1, off, len)` for the array. -/
def PBDecA (m : Mem) (r : List Word) : Option (Array EIdx) → Prop
  | none => r.headD 0 = 0
  | some l => r.headD 0 = 1 ∧ decHL m (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat = some l.toList ∧
      (r.tail.headD 0).toNat + (r.tail.tail.headD 0).toNat ≤ iwTop m

end L.Ind

end
