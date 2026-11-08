module

import ConAgua.Arena.IndPosSpec.NestContParamsClosed
import ConAgua.Arena.IndPosSpec.GgW2
public import ConAgua.Verdict.LefRef
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
public import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Arena.IndPartsSpec.BlockCounts
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.IndPosSpec.CfW
public import ConAgua.Arena.IndPosSpec.NbLook
import all ConAgua.Arena.IndPos2

@[expose] public section

/-!
# Error models of `nest_pos`, `nest_pos_bind`, `nest_pos_app`, `nest_cont`, their leaves
(lane `verdicts-b`, helper `ia2`, fork `kn1`)
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

l_model npE_spec (p : Prog) (hf : p.lookup "nest_pos" = some nestPosL)
  fns [hf ↦ npE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified

l_model npbE_spec (p : Prog) (hf : p.lookup "nest_pos_bind" = some nestPosBindL)
  fns [hf ↦ npbE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified

l_model npaE_spec (p : Prog) (hf : p.lookup "nest_pos_app" = some nestPosAppL)
  fns [hf ↦ npaE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified

l_model ncE_spec (p : Prog) (hf : p.lookup "nest_cont" = some nestContL)
  fns [hf ↦ ncE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified

/- ronsync2 stage 2: commented out (statement at the old twin/L)
l_model pfvE_spec (p : Prog) (hL : PfLook p)
  fns [hL.hp ↦ pfvE]
  specs [nestHoleAt_spec' p hL n, nestOccAny_spec p hL.no hL.hoa n, nestArity_spec' p hL.na n,
    nestPosHoleKind_spec p hL.hh hL.hk n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]
-/

l_model nccE_spec (p : Prog) (hL : NbLook p)
  fns [hL.hcc ↦ nccE]
  specs [nestOccAny_spec p hL.nit.no hL.nit.hoa n, pos2Pin_spec p hL.hpa n,
    nestContParamsClosed_spec p hL.usl.hbp hL.dc.hf hL.hpc n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

noncomputable section

/- ronsync2 stage 2: commented out (statement at the old twin/L)
l_model ntyE_spec (p : Prog) (hL : NtyLook p)
  fns [hL.hp ↦ ntyE]
  specs [callW_spec p n "env_find", callW_spec p n "view_ls_len", stripPis_specF p hL.hst n,
    cvLps_spec p hL.ha hL.hc hL.he hL.hcv n, callW_spec p n "inst_lp_fast",
    instPisWith_spec p hL.hv hL.hip hL.hi1 n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
l_model nitE_spec (p : Prog) (hL : NitLook p)
  fns [hL.hp ↦ nitE]
  specs [ntyE_spec p hL.ty n, piBinders_spec p hL.ty.ha hL.hc2 hL.ty.hv hL.hs hL.hpb n, eView_spec p hL.ty.hv n,
    nestOccAny_spec p hL.no hL.hoa n, lefE_spec p hL.hlf n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]
-/

end

end L.Ind

end
