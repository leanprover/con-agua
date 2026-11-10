module

public import ConAgua.Arena.DeclHeader
public import ConAgua.Arena.IndPartsSpec.EqW
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.ModelGen
import all ConAgua.Arena.IndParts

@[expose] public section

/-!
# BpcW

The generated models and specs of the four pins passes: `bpfW`, `bprW`, `bpcW`, `bpoW`.
-/


/-!
# Refinements of `IndParts`, part 13 (lane `indproofs2`, helper `parts`): `blockShape?`'s pins

The reserved-name and level-parameter pins (`block_shape_pins_formers`/`_recs`/`_ctors`/`_ok`,
pure in the twin: one `Bool`), and the eliminator (`block_shape_large`). Shared pieces: a constant's
level parameters copied by `er_to_iw` (`partsLpsCopy`), `reserved_contains` against the twin's
`reservedBasisNames` (`partsResCont`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The pins: models (generated) -/

/-- **`block_shape_pins_formers` is its model `bpfW`.** -/
l_model bpf_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hrf : p.lookup "reserved_from" = some reservedFrom)
    (hrc : p.lookup "reserved_contains" = some reservedContains) (hec : p.lookup "er_copy" = some erCopy)
    (het : p.lookup "er_to_iw" = some erToIw) (hseq : p.lookup "sl_eq" = some slEq)
    (hp : p.lookup "block_shape_pins_formers" = some blockShapePinsFormers)
  fns [hp ↦ bpfW list]
  specs [resCont_spec p hrf hrc n, erToIw_specW p ha hec het n, slEq_spec p hseq n]
  grind [arena_grind, ind_grind] finish [rdW_eq, erRd]

/-- **`block_shape_pins_recs` is its model `bprW`.** -/
l_model bpr_spec (p : Prog) (hrf : p.lookup "reserved_from" = some reservedFrom)
    (hrc : p.lookup "reserved_contains" = some reservedContains)
    (hp : p.lookup "block_shape_pins_recs" = some blockShapePinsRecs)
  fns [hp ↦ bprW list]
  specs [resCont_spec p hrf hrc n]
  grind [arena_grind, ind_grind] finish [rdW_eq, erRd]

/-- **`block_shape_pins_ctors` is its model `bpcW`.** -/
l_model bpc_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hrf : p.lookup "reserved_from" = some reservedFrom)
    (hrc : p.lookup "reserved_contains" = some reservedContains) (hec : p.lookup "er_copy" = some erCopy)
    (het : p.lookup "er_to_iw" = some erToIw) (hseq : p.lookup "sl_eq" = some slEq)
    (hp : p.lookup "block_shape_pins_ctors" = some blockShapePinsCtors)
  fns [hp ↦ bpcW list]
  specs [resCont_spec p hrf hrc n, erToIw_specW p ha hec het n, slEq_spec p hseq n]
  grind [arena_grind, ind_grind] finish [rdW_eq, erRd]

/-! ## `block_shape_pins_ok` -/

/-- **`block_shape_pins_ok` is its model `bpoW`** (at exec fuel `n + 1`). -/
l_model bpo_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hrf : p.lookup "reserved_from" = some reservedFrom)
    (hrc : p.lookup "reserved_contains" = some reservedContains) (hec : p.lookup "er_copy" = some erCopy)
    (het : p.lookup "er_to_iw" = some erToIw) (hseq : p.lookup "sl_eq" = some slEq)
    (hf : p.lookup "block_shape_pins_formers" = some blockShapePinsFormers)
    (hr : p.lookup "block_shape_pins_recs" = some blockShapePinsRecs)
    (hc : p.lookup "block_shape_pins_ctors" = some blockShapePinsCtors)
    (hp : p.lookup "block_shape_pins_ok" = some blockShapePinsOk)
  fns [hp ↦ bpoW list]
  specs [bpf_spec p ha hrf hrc hec het hseq hf n, bpr_spec p hrf hrc hr n,
    bpc_spec p ha hrf hrc hec het hseq hc n]
  grind [arena_grind, ind_grind] pfuel

end L.Ind

end
