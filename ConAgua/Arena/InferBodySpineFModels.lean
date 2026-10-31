module

public import ConAgua.Arena.Verdict
public import ConAgua.Arena.Infer
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
public import ConAgua.L.ModelGen
public import ConAgua.Checker.NoVerdictTree
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-!
# The generated models of `InferBodySpineF.lean`

Generated `unified` models only, apart from their refinements (`InferBodySpineF.lean`): they need
the code and their callees' runs, not the refinements before it, so they build beside that chain.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- **`infer_spine_arg`'s unified model**: the `infer` slot and `defeq_arg` through their runs. -/
l_model isaE_spec (p : Prog) (hf : p.lookup "infer_spine_arg" = some inferSpineArgL)
  fns [hf ↦ isaE list] grind [arena_grind] unified

/-- `infer_spine`'s unified model: the `whnf` slot and `infer_spine_arg` through their runs,
`inst_list` lifted. -/
l_model ispE_spec (p : Prog) (hf : p.lookup "infer_spine" = some inferSpineL)
  fns [hf ↦ ispE list]
  specs [callW_spec p n "inst_list"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  finish [tierW, idxW] heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- `infer_app`'s unified model: the `infer` slot and `infer_spine` through their runs,
`head_and_args` lifted. -/
l_model aE_spec (p : Prog) (hf : p.lookup "infer_app" = some inferAppL)
  fns [hf ↦ aE list]
  specs [callW_spec p n "head_and_args"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

end L.Arena
