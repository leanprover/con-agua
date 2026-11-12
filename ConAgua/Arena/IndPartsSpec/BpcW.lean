module

public import ConAgua.Arena.DeclHeader
public import ConAgua.Arena.IndPartsSpec.EqW
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.ModelGen
import all ConAgua.Arena.IndParts

@[expose] public section

/-!
# BpcW

The generated models and specs of `readBlock`'s three universe and parameter tests (each a cited
`all`): `floW` (`formers_lps_ok`), `cpoW` (`ctors_params_ok`), `cloW` (`ctors_lps_ok`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **`formers_lps_ok` is its model `floW`.** -/
l_model flo_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hec : p.lookup "er_copy" = some erCopy) (het : p.lookup "er_to_iw" = some erToIw)
    (hseq : p.lookup "sl_eq" = some slEq) (hp : p.lookup "formers_lps_ok" = some formersLpsOk)
  fns [hp ↦ floW list]
  specs [erToIw_specW p ha hec het n, slEq_spec p hseq n]
  grind [arena_grind, ind_grind] finish [rdW_eq, erRd]

/-- **`ctors_params_ok` is its model `cpoW`.** -/
l_model cpo_spec (p : Prog) (hp : p.lookup "ctors_params_ok" = some ctorsParamsOk)
  fns [hp ↦ cpoW list]
  grind [arena_grind, ind_grind] finish [rdW_eq]

/-- **`ctors_lps_ok` is its model `cloW`.** -/
l_model clo_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hec : p.lookup "er_copy" = some erCopy) (het : p.lookup "er_to_iw" = some erToIw)
    (hseq : p.lookup "sl_eq" = some slEq) (hp : p.lookup "ctors_lps_ok" = some ctorsLpsOk)
  fns [hp ↦ cloW list]
  specs [erToIw_specW p ha hec het n, slEq_spec p hseq n]
  grind [arena_grind, ind_grind] finish [rdW_eq, erRd]

end L.Ind

end
