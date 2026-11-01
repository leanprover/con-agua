module

public import ConAgua.Arena.Verdict
public import ConAgua.Arena.Infer
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
public import ConAgua.Checker.NoVerdictFns

@[expose] public section

/-!
# The generated models of `InferBodyDisp.lean`

Generated `unified` models only, apart from their refinements (`InferBodyDisp.lean`): they need
the code and their callees' runs, not the refinements before it, so they build beside that chain.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- `infer_body`'s unified model: `e_view` and the interning lifted, each arm through its run. -/
l_model ibE_spec (p : Prog) (hf : p.lookup "infer_body" = some inferBodyL)
  fns [hf ↦ ibE list]
  specs [callW_spec p n "e_view", callW_spec p n "intern_succ", callW_spec p n "intern_sort"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- `infer_body_io`'s unified model. -/
l_model iboE_spec (p : Prog) (hf : p.lookup "infer_body_io" = some inferBodyIOL)
  fns [hf ↦ iboE list]
  specs [callW_spec p n "e_view", callW_spec p n "intern_succ", callW_spec p n "intern_sort",
    callW_spec p n "inst1"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

end L.Arena
