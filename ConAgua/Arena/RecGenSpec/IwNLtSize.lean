module

public import ConAgua.Arena.IndIface
public import ConAgua.Arena.WhnfBase

@[expose] public section

/-!
# IwNLtSize

`cfaFv` (`class_fields_agree`'s datum variable), `iwN_lt_size`.
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

/-- An ordinary field's record: tag `0`. A recursive field's: tag `1`, its class and telescope
length. -/
theorem iwN_lt_size {m : Mem} {i v : Nat} (h : iwN m i = some v) : i < (m.arr64 IW).size := by
  simp only [iwN, nat?, iwA, aread_apply, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, -⟩ := h
  exact (Array.getElem?_eq_some_iff.mp hx).1

end L.Ind

end
