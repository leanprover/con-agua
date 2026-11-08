module

public import ConAgua.Verdict.IndBToi
public import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.RecGenSpec.OcW
import all ConAgua.Arena.RecCheck

@[expose] public section
/-!
# `target_major_of_outside_tail`: the model for both outcomes

`tmtE` (`l_model … unified`): `target_outside_inst` through `toiE`, `lvl_eq_c` and
`mk_target_major` lifted (through their runs, `callW`). Its refinement is `tmt_ref`
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

/- ronsync2 stage 2: commented out (statement at the old twin/L)
l_model tmtE_spec (p : Prog) (P : TmtProg p)
  fns [P.tail ↦ tmtE]
  specs [toiE_spec p P.toi n, callW_spec p n "lvl_eq_c", callW_spec p n "mk_target_major"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]
-/

end L.Ind

end
