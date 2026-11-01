module

public import ConAgua.Verdict.IndBTmm
public import ConAgua.Verdict.IndBTmo
public import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
import all ConAgua.Arena.RecCheck

@[expose] public section
/-!
# `target_major_of_const`: the model for both outcomes

`tmcE` (`l_model … unified`): `block_shape_member_names` and `sl_find` lifted (through their runs,
`callW`), the member branch through `tmmE`, the outside branch through `tmoE`. Its refinement is
`tmc_ref` (`IndT/RecGenTmf`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model tmcE_spec (p : Prog) (P : TmfProg p)
  fns [P.tmc ↦ tmcE]
  specs [tmmE_spec p P.tmm n, tmoE_spec p P.tmo n, callW_spec p n "block_shape_member_names",
    callW_spec p n "sl_find"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

end L.Ind

end
