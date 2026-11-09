module

import ConAgua.Arena.Verdict
public import ConAgua.Arena.ProjGuardRef
public import ConAgua.Arena.Infer
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
public import ConAgua.Checker.NoVerdictFns
public import ConAgua.L.ErrSpec
import all ConAgua.Arena.Infer

@[expose] public section

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

/-- **`proj_type_at`'s model**: `inst_lp` and `inst_list` lifted. -/
l_model ptaW_spec (p : Prog) (hf : p.lookup "proj_type_at" = some projTypeAtL)
  fns [hf ↦ ptaW]
  specs [callW_spec p n "inst_lp", callW_spec p n "inst_list"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

/-- **`infer_proj_at`'s unified model**: `check_proj_guard` through its unified model, the other
callees lifted. -/
l_model ipaE_spec (p : Prog) (hf : p.lookup "infer_proj_at" = some inferProjAtL)
  (hcp : p.lookup "check_proj_guard" = some checkProjGuardL)
  (hs : p.lookup "former_sort_loop" = some formerSortLoopL)
  (hg : p.lookup "proj_guard_sort" = some projGuardSortL)
  (hc : p.lookup "check_guard_rows" = some checkGuardRowsL)
  fns [hf ↦ ipaE list]
  specs [callW_spec p n "get_app_args", callW_spec p n "ls_node", cpgE_spec p hcp hs hg hc n,
    callW_spec p n "proj_type_at"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

end L.Arena
