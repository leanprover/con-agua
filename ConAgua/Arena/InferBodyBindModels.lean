module

import ConAgua.Arena.Verdict
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
# The generated models of `InferBodyBind.lean`

Generated `unified` models only, apart from their refinements (`InferBodyBind.lean`): they need
the code and their callees' runs, not the refinements before it, so they build beside that chain.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- `infer_lams_leaf`'s unified model: the `infer` slot through its run, the opening and the
outward rebuild (`inst_list`, `ar_entry`, `mk_forall`) lifted. -/
l_model ilfE_spec (p : Prog) (hf : p.lookup "infer_lams_leaf" = some inferLamsLeafL)
  fns [hf ↦ ilfE list]
  specs [callW_spec p n "inst_list", callW_spec p n "ar_entry", callW_spec p n "mk_forall"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  finish [tierW, idxW] heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- `infer_lams`' unified model: the slots and the leaf through their runs, the opening and the
binder's free variable (`inst_list`, `intern_fvar`) lifted. -/
l_model ilsE_spec (p : Prog) (hf : p.lookup "infer_lams" = some inferLamsL)
  fns [hf ↦ ilsE list]
  specs [callW_spec p n "inst_list", callW_spec p n "intern_fvar"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- `infer_lam`'s unified model: the slots and `infer_lams` through their runs, the binder's free
variable lifted. -/
l_model ilmE_spec (p : Prog) (hf : p.lookup "infer_lam" = some inferLamL)
  fns [hf ↦ ilmE list]
  specs [callW_spec p n "intern_fvar"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

end L.Arena
