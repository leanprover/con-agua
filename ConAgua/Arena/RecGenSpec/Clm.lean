import ConAgua.Arena.RecGen
import ConAgua.Arena.WhnfBase
import ConAgua.Scan.Common

/-!
# Clm

`clm_spec`, `clmW`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## Frames -/

/-! ## `class_majors` -/

l_model clm_spec (p : Prog) (hp : p.lookup "class_majors" = some classMajorsL)
  fns [hp ↦ clmW]
  specs [callW_spec p n "intern_const", callW_spec p n "mk_app_n_f", callW_spec p n "target_major_of",
    callW_spec p n "target_major_pins", callW_spec p n "sl_cons"]
  grind [arena_grind] finish [rdW_eq] gen 40 instances 20000

end L.Ind
