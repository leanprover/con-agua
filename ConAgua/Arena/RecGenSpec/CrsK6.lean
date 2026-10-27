import ConAgua.Arena.IndCopy

/-!
# CrsK6

`crsK6`, `crsK5`, `cr1K`.
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

def crsK6 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r6, m6) => some ([r6.headD 0, r6.tail.headD 0], m6)

def crsK5 (n : Nat) (y : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) => crsK6 (consW n m5 y (r5.headD 0) (r5.tail.headD 0))

def cr1K : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m') => some ([r.headD 0], m')

/-! ## The `abstract1` memo across a rule's check -/

end L.Ind

end
