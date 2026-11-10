module

public import ConAgua.Arena.IndInstall
public import ConAgua.Arena.WhnfBase
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
public import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.IndInstall

@[expose] public section

/-!
# Icp

`icprW`, `icpr_spec`: `check_block_pass_rec`'s generated model (the pass's record).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `check_block_pass_rec` -/

/-- **`check_block_pass_rec(…)` is its model `icprW`** (generated; body fuel `n`): the
allocation, then the record's eleven writes. -/
l_model icpr_spec (p : Prog) (hp : p.lookup "check_block_pass_rec" = some checkBlockPassRec)
  fns [hp ↦ icprW list]
  specs [callW_spec p n "iw_alloc"]
  grind [arena_grind, ind_grind] pfuel

end L.Ind
