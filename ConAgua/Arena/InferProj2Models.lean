module

public import ConAgua.Arena.InferProjModels
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.Verdict
import ConAgua.Checker.NoVerdictTree
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import all ConAgua.Arena.Infer

@[expose] public section

/-!
# The generated models of `InferProj2.lean`

Generated `unified` models only, apart from their refinements (`InferProj2.lean`): they need
the code and their callees' runs, not the refinements before it, so they build beside that chain.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- **`infer_proj`'s unified model**: the knot's slots (`infer`, `infer_io`, `whnf`) through their
runs, `infer_proj_at` by its unified model, the other callees (outside the verdict closure)
lifted. -/
l_model ipE_spec (p : Prog) (hf : p.lookup "infer_proj" = some inferProjL)
    (hipa : p.lookup "infer_proj_at" = some inferProjAtL)
    (hcp : p.lookup "check_proj_guard" = some checkProjGuardL)
    (hs : p.lookup "former_sort_loop" = some formerSortLoopL)
    (hg : p.lookup "proj_guard_sort" = some projGuardSortL)
    (hc : p.lookup "check_guard_rows" = some checkGuardRowsL)
  fns [hf ↦ ipE list]
  specs [callE_spec p n "infer", callE_spec p n "infer_io", callE_spec p n "whnf", callW_spec p n "get_app_fn", callW_spec p n "find_proj", callW_spec p n "find_table",
    callW_spec p n "get_app_args", callW_spec p n "env_find", ipaE_spec p hipa hcp hs hg hc n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] heartbeats 2000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem] cut 1

end L.Arena
