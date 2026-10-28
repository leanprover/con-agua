import ConAgua.Arena.IndRealLvlC
import ConAgua.Arena.IndSim
import ConAgua.Arena.IndSumSpec.CheckStructFieldSortsISucc
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

/-!
# `nest_cont_key`'s unified model

`nest_cont_key`'s refinement is `keyRef_step` (`Arena/IndT/PosKey.lean`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

l_model nckE_spec (p : Prog) (hf : p.lookup "nest_cont_key" = some nestContKeyL)
  fns [hf ↦ nckE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified

open ConRon.Bridge.Inductives (dCtx dProg dState dCtx_ext dProg_ext dState_ext)

local notation "V" => ConLeche.CheckMode.verified

end L.Ind
