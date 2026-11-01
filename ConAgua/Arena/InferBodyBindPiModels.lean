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

@[expose] public section

/-!
# The generated models of `InferBodyBindPi.lean`

Generated `unified` models only, apart from their refinements (`InferBodyBindPi.lean`): they need
the code and their callees' runs, not the refinements before it, so they build beside that chain.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- `infer_pis_leaf`'s unified model: the `infer` slot and `ensure_sort` through their runs, the
opening, the outward fold and the sort (`inst_list`, `intern_imax`, `intern_sort`) lifted. -/
l_model iplE_spec (p : Prog) (hf : p.lookup "infer_pis_leaf" = some inferPisLeafL)
  fns [hf ↦ iplE list]
  specs [callW_spec p n "inst_list", callW_spec p n "intern_imax", callW_spec p n "intern_sort"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  finish [tierW, idxW] heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- `infer_pis`' unified model: the slots and the leaf through their runs, the opening and the
binder's free variable (`inst_list`, `intern_fvar`) lifted. -/
l_model ipsE_spec (p : Prog) (hf : p.lookup "infer_pis" = some inferPisL)
  fns [hf ↦ ipsE list]
  specs [callW_spec p n "inst_list", callW_spec p n "intern_fvar"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- `infer_forall`'s unified model: the slots and `infer_pis` through their runs, the binder's free
variable lifted. -/
l_model ifrE_spec (p : Prog) (hf : p.lookup "infer_forall" = some inferForallL)
  fns [hf ↦ ifrE list]
  specs [callW_spec p n "intern_fvar"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

end L.Arena
