module

public import ConAgua.Arena.IndPos2
public import ConAgua.Arena.Verdict
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
public import ConAgua.L.ModelGen

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
