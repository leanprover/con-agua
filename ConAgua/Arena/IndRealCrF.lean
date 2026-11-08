module

public import ConAgua.Arena.ConstsResolveF
import ConAgua.Arena.StageInst1
public import ConAgua.Arena.WhnfIota
public import ConAgua.Arena.CallF
public import ConAgua.L.ProgHas
import all ConAgua.Arena.ConstsResolveF
import all ConAgua.Arena.Env
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.MemoLib
import all ConAgua.Arena.Pins
import all ConAgua.Arena.WhnfIota

@[expose] public section

/-!
# `consts_resolve_ffast`'s model (lane `indproofs4`, helper `memo`)

The program- and fuel-free model `crfF := callF crfP "consts_resolve_ffast"` (the recipe of
`IndReal.lean`) over the walk's program `crfP` (lane `tails`' `crfProg` with the environment and
pin reads it calls); it writes only its memo table `CRM` (155) and the memo's epoch and count
(`CTL[158]`, `CTL[159]`). Kept low (below `IndSumSpec/StructProjArgP`, whose models call it); the refinement
`crfF_ok` is in `IndRealMemoCr.lean`, above lane `tails`' `ConstsResolveFRefine2`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The functions `consts_resolve_ffast` reaches. -/
def crfPFns : List FnName :=
  ["consts_resolve_ffast", "crf_go", "cr_leaf", "cr_lit_pins", "pin_found", "crm_find", "crm_put",
    "crm_clear", "e_view", "is_str_lit", "env_find", "env_row_get", "env_ix", "pin_at"]

end L.Ind
