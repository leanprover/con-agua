import ConAgua.Arena.IndRealAbsPos

/-!
# RootOutsB

`pos2FuelF`, `RootOutsB`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- The twin's fold of the seed's fuel. -/
def pos2FuelF (acc : Nat) (d : EIdx) : AM Nat := do
  let w ← ConRon.Arena.whnfWalkFuel d
  pure (max acc w)

/-! ## The root frame -/

/-- The root frame's outputs: a slice of `(off, len)` records of `(kinds, closed)` slices. -/
def RootOutsB (m : Mem) (o l : Nat) (outss : List (List (List NestFieldKind × EIdx))) : Prop :=
  DecB (fun m => decPL m (decAt m (fun o l => decPL m (decKE m) o l)) o l) m outss

end L.Ind

end
