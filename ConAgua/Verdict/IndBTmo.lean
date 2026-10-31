import ConAgua.Verdict.IndBTmt
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
/-!
# `target_major_of_outside`: the model for both outcomes

`tmoE` (`l_model … unified`): `pin_at`, `target_ctors_of`, the closedness and occurrence tests
lifted (through their runs, `callW`), the tail through `tmtE`. Its refinement is `tmo_ref`
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

l_model tmoE_spec (p : Prog) (P : TmoOProg p)
  fns [P.out ↦ tmoE]
  specs [tmtE_spec p P.tmt n, callW_spec p n "pin_at", callW_spec p n "target_ctors_of",
    callW_spec p n "target_major_of_outside_closed", callW_spec p n "target_major_of_outside_occ"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

end L.Ind

end
