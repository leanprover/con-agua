import ConAgua.Arena.IndInstallSpec21

/-!
# Refinements of `IndInstall`, part 22 (lane `indproofs2`, helper `install`): `checkBlockCtors`,
the word models

Per member: `check_sum_ctors` (`IndSumSpec13`'s refinement, `installSimSumCtors` below), the
two results wrapped (`rec2`), recursion as the twin's with both pointers consed (D18).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `check_sum_ctors` as a callee (lane `indproofs2`'s `IndSumSpec13`) -/

/-! ## `check_block_ctors_one` -/

/-- **`check_block_ctors_one` is its model `icboW`** (generated). -/
l_model icbo_spec (p : Prog) (hp : p.lookup "check_block_ctors_one" = some checkBlockCtorsOne)
  fns [hp ↦ icboW]
  specs [callW_spec p n "check_sum_ctors", callW_spec p n "rec2"]
  grind [ind_grind] finish [rdW_eq] gen 40 heartbeats 1600000 instances 20000

/-! ## `check_block_ctors_go` -/

/-- **`check_block_ctors_go` is its model `icbgW`** (generated). -/
l_model icbg_spec (p : Prog) (hp : p.lookup "check_block_ctors_go" = some checkBlockCtorsGo)
  fns [hp ↦ icbgW]
  specs [callW_spec p n "check_block_ctors_one", callW_spec p n "sl_cons"]
  grind [ind_grind] finish [rdW_eq] gen 40 heartbeats 1600000 instances 20000

/-! ## `check_block_ctors` -/

/-- **`check_block_ctors` is its model `ictW`** (generated). -/
l_model ict_spec (p : Prog) (hp : p.lookup "check_block_ctors" = some checkBlockCtors)
  fns [hp ↦ ictW]
  specs [callW_spec p n "block_shape_lps", callW_spec p n "check_block_ctors_go"]
  grind [ind_grind] finish [] gen 40 heartbeats 1600000 instances 20000

end L.Ind
