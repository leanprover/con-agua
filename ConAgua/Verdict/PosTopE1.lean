module

import ConAgua.Arena.Verdict
import ConAgua.Arena.IndPosSpec.NuW
import ConAgua.Checker.NoVerdictTree
public import Std.Tactic.BVDecide.Normalize.Prop
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
public import ConAgua.Arena.IndPosSpec.RsLook
public import ConAgua.Arena.IndPosSpec.UnW
public import ConAgua.Checker.NoVerdictFns
public import ConAgua.L.ErrSpec

@[expose] public section

/-!
# The positivity pass's entry points: unified models (lane `verdicts-b`, helper `ia2`, fork `top`)

The models of `check_abs_ctor_sorts_one`, `check_abs_ctor_sorts`, `check_abs_ctor_sorts_all`,
`nest_uniform`, `nest_root` (`unified`; `check_block_positivity`'s is in `IndT/Positivity`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

noncomputable section

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

l_model iaoE_spec (p : Prog) (hf : p.lookup "check_abs_ctor_sorts_one" = some checkAbsCtorSortsOne)
  fns [hf ↦ iaoE list] specs [callW_spec p n "open_pis_at_fvars_f"] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model iacE_spec (p : Prog) (h1 : p.lookup "check_abs_ctor_sorts_one" = some checkAbsCtorSortsOne)
  (hf : p.lookup "check_abs_ctor_sorts" = some checkAbsCtorSorts)
  fns [hf ↦ iacE list]
  specs [callW_spec p n "all_level_params_defined", callW_spec p n "nest_ctx_hi_at", iaoE_spec p h1 n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model iaaE_spec (p : Prog) (h1 : p.lookup "check_abs_ctor_sorts_one" = some checkAbsCtorSortsOne)
  (h2 : p.lookup "check_abs_ctor_sorts" = some checkAbsCtorSorts)
  (hf : p.lookup "check_abs_ctor_sorts_all" = some checkAbsCtorSortsAll)
  fns [hf ↦ iaaE list] specs [iacE_spec p h1 h2 n] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model nuE_spec (p : Prog) (hL : NuLook p) (hc : p.lookup "nest_uniform_cs" = some nestUniformCsL)
  (hf : p.lookup "nest_uniform" = some nestUniformL)
  fns [hf ↦ nuE list] specs [nestUniformCs_spec p hL hc (realCall p) (realCall_spec p) n] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model nrtE_spec (p : Prog) (hL : RsLook p)
  fns [hL.proot ↦ nrtE list]
  specs [nestCtxHiAt_specE p hL.nb.ct.cr.rx.hi n, posRec2_specW p hL.nb.ct.cr.rx.ha hL.nb.ct.cr.rx.h2 n,
    slSnoc_specW p hL.nb.ct.cr.rx.ha hL.nb.nit.hc2 hL.nb.nag.hsn n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

end L.Ind

end
