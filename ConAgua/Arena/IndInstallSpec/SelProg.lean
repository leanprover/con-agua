import ConAgua.Arena.DeclNatSub
import ConAgua.Arena.RecGenSpec.ClassFeR

/-!
# SelProg

`SelProg`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `block_large_elim_allowed`: a stub contract -/

/-! ## `struct_elim_level` under the stage relation -/

/-- The lookups of `struct_elim_level`. -/
structure SelProg (p : Prog) : Prop where
  pf1 : p.lookup "param_find" = some paramFind
  pp1 : p.lookup "param_push" = some paramPush
  ip : p.lookup "intern_param" = some internParam
  pf2 : p.lookup "zero_find" = some zeroFind
  pp2 : p.lookup "zero_push" = some zeroPush
  iz : p.lookup "intern_zero" = some internZero
  sel : p.lookup "struct_elim_level" = some structElimLevelL

end L.Ind
