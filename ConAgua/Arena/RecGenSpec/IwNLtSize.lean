module

public import ConAgua.Arena.WhnfBase

@[expose] public section

/-!
# IwNLtSize

`cfaFv` (`class_fields_agree`'s datum variable).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## The model -/

section model
variable (p : Prog) (k : Nat)

/-- The datum variable `i` (in range), else the interned `.bvar 0`. -/
def cfaFv (m : Mem) (fvo fvl i : Word) : Option (List Word × Mem) :=
  if i < fvl then some ([rdW (m.arr64 IW) (fvo + i)], m) else callW p k "intern_bvar" [0] m

end model

/-! ## Reading the fields' records -/

end L.Ind

end
