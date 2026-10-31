import ConAgua.Arena.Verdict
import ConAgua.Arena.Infer
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The generated models of `InferProj.lean`

Generated `unified` models only, apart from their refinements (`InferProj.lean`): they need
the code and their callees' runs, not the refinements before it, so they build beside that chain.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- **`infer_proj_at`'s unified model**: every callee (outside the verdict closure) lifted. -/
l_model ipaE_spec (p : Prog) (hf : p.lookup "infer_proj_at" = some inferProjAtL)
  fns [hf ↦ ipaE list]
  specs [callW_spec p n "get_app_args", callW_spec p n "ls_node", callW_spec p n "pin_word",
    callW_spec p n "lvl_eq_c", callW_spec p n "field_sort_zero", callW_spec p n "proj_type_at"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

end L.Arena
