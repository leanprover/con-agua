module

public import ConAgua.Arena.IndPos2
import ConAgua.Arena.Verdict
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.WP.Triple.SpecLemmas
public import ConAgua.L.ErrSpec
import all ConAgua.Arena.IndPos2

@[expose] public section

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
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified

end L.Ind
