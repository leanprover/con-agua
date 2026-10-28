import ConAgua.Arena.Verdict
import ConAgua.Arena.IndPosSpec.NuW
import ConAgua.Checker.NoVerdictTree
import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndPosSpec.RsLook

/-!
# The positivity pass's entry points: error models (lane `verdicts-b`, helper `ia2`, fork `top`)

The models of `check_abs_ctor_sorts_one`, `check_abs_ctor_sorts`, `nest_uniform`, `nest_root`
(`unified`), `check_abs_ctor_sorts_all`, `check_block_positivity` (`errors`).
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
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model iacE_spec (p : Prog) (h1 : p.lookup "check_abs_ctor_sorts_one" = some checkAbsCtorSortsOne)
  (hf : p.lookup "check_abs_ctor_sorts" = some checkAbsCtorSorts)
  fns [hf ↦ iacE list]
  specs [callW_spec p n "all_level_params_defined", callW_spec p n "nest_ctx_hi_at", iaoE_spec p h1 n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model iaaE_spec (p : Prog) (hf : p.lookup "check_abs_ctor_sorts_all" = some checkAbsCtorSortsAll)
  fns [hf ↦ iaaE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

l_model nuE_spec (p : Prog) (hL : NuLook p) (hc : p.lookup "nest_uniform_cs" = some nestUniformCsL)
  (hf : p.lookup "nest_uniform" = some nestUniformL)
  fns [hf ↦ nuE list] specs [nestUniformCs_spec p hL hc (realCall p) (realCall_spec p) n] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model nrtE_spec (p : Prog) (hL : RsLook p)
  fns [hL.proot ↦ nrtE list]
  specs [nestCtxHiAt_specE p hL.nb.ct.cr.rx.hi n, posRec2_specW p hL.nb.ct.cr.rx.ha hL.nb.ct.cr.rx.h2 n,
    slSnoc_specW p hL.nb.ct.cr.rx.ha hL.nb.nit.hc2 hL.nb.nag.hsn n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model cbpE_spec (p : Prog) (hf : p.lookup "check_block_positivity" = some checkBlockPositivity)
  fns [hf ↦ cbpE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

end L.Ind

end
