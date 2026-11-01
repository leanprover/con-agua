module

public import ConAgua.Verdict.IndBTmc
public import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
import all ConAgua.Arena.RecCheck

@[expose] public section
/-!
# `target_major_of`: the model for both outcomes

`tmfE` (`l_model … unified`): `get_app_args_f`, `get_app_fn_f` and `e_view` lifted (through their
runs, `callW`), `target_major_of_const` through `tmcE`. Its refinement is `tmf_ref`
(`IndT/RecGenTmf`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model tmfE_spec (p : Prog) (P : TmfProg p)
  fns [P.tmf ↦ tmfE]
  specs [tmcE_spec p P n, callW_spec p n "get_app_args_f", callW_spec p n "get_app_fn_f",
    callW_spec p n "e_view"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

end L.Ind

end
