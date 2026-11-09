module

public import ConAgua.Arena.IndT.PassCS
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
public import ConAgua.Arena.IndInstallSpec.Pos3Init
public import ConAgua.Arena.IndInstallSpec.NhW
public import ConAgua.Arena.IndRealOpf
import ConAgua.Arena.IndRealOpf3
import ConAgua.Arena.IndInstallSpec.NestCtx
import ConAgua.Arena.IndPosSpec.NestHoles
import ConAgua.Arena.IndInstallSpec.PartsShapeFacts
import ConAgua.Arena.IndT.BncAfr
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
import all ConAgua.Arena.IndInstall

@[expose] public section

/-!
# `block_nest_ctx`' contract (lane `ronsync2`, stage 3)

`block_nest_ctx(p)` (`IndInstall.lean`): the formers' slice (`block_shape_formers`), the first
former's telescope opened (`open_pis_at_fvars_f`), the context record (`block_shape_nest_ctx`), the
members' holes (`nest_holes`). Its unified model `bncE`, the refinement `bnc_ref` against con-ron's
`blockNestCtx`, the contract `bncRefS_of`.
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

set_option experimental.vcgen true in
/-- **`block_nest_ctx`'s unified model**: every callee lifted. -/
l_model bncE_spec (p : Prog) (hP : PosBlkProg p)
  fns [hP.bnc ↦ bncE list]
  specs [callW_spec p n "block_shape_formers", callW_spec p n "open_pis_at_fvars_f",
    callW_spec p n "block_shape_nest_ctx", callW_spec p n "nest_holes"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]


end L.Ind

end
