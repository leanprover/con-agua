import ConAgua.Arena.RecGenSpec18
import ConAgua.Arena.RecGenSpec14

/-!
# `classMajors` (lane `indproofs3`, helper `indproofs3-pos-cls`)

Every class key checked as a major: the key's application (`intern_const`, the `mk_app_n` stub),
`target_major_of`, `target_major_pins`; a recursion consing each major onto the rest's slice (D18).
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

/-- The lookups of `class_majors`. -/
structure ClmProg (p : Prog) : Prop where
  tmf : TmfProg p
  tmp : TmpProg p
  keys : KeysProg p
  cm : p.lookup "class_majors" = some classMajorsL

end L.Ind
