import ConAgua.Arena.IndInstall
import ConAgua.Arena.WhnfBase
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Icbo

`ict_spec`, `ictW`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `check_block_ctors` -/

/-- **`check_block_ctors` is its model `ictW`** (generated). -/
l_model ict_spec (p : Prog) (hp : p.lookup "check_block_ctors" = some checkBlockCtors)
  fns [hp ↦ ictW]
  specs [callW_spec p n "block_shape_lps", callW_spec p n "check_block_ctors_go"]
  grind [ind_grind] finish [] gen 40 heartbeats 1600000 instances 20000

end L.Ind

end
