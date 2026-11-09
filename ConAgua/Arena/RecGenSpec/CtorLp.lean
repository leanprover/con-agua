module

public import ConAgua.Arena.IndIface

@[expose] public section

/-!
# CtorLp

`cxoK9`.
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
variable (p : Prog) (n : Nat)

/-- After `rec6`: the record. -/
def cxoK9 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

end model

end L.Ind

end
