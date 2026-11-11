module

public import ConAgua.Arena.IndPartsSpec.EqW
public import ConAgua.Arena.RecCheckSpec.EraseFVarTys
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.Arena.RecCheckSpec.K53Look
import ConAgua.L.ModelGen
import all ConAgua.Arena.RecCheck

@[expose] public section

/-!
# EeW

`ee_spec`, `tte_spec`: `erase_each` and `target_k53_tele` generated (`eeW`, `tteW`).
-/

noncomputable section

/-!
# `RecCheck`: `targetK53`, the L side (lane `indproofs3`, helper `rec`)

K.53′ at one recorded field: `strip_pis` (stub), the telescope check (`target_k53_tele`: both sides
erased by `erase_each`, compared by `sl_eq`), the head check (`target_k53_heads`: `get_app_fn_f`,
`get_app_args_f` stubs, `e_view`), the argument check (`target_k53_args`: erased indices, the
leaf's class `intern_const` + `mk_app_n_f` (stub) + `nest_occ`, then `target_class_match`).
L: `erase_each` is the twin's `mapM` as a self-recursion consing each result (`sl_cons`, D18); a
handle guard after `intern_const` (`mk_app_n_f`'s contract takes a handle).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `erase_each`, `target_k53_tele` -/

/-- **`erase_each` is its model `eeW`** (generated). -/
l_model ee_spec (p : Prog) (L : K53Look p)
  fns [L.ee ↦ eeW list]
  specs [eftF_spec p L.tmn.tcm.tp.rc n, slCons_specW p L.tmn.tcm.ha L.tmn.tcm.ic L.tmn.tcm.sc n]
  grind [arena_grind]

/-- **`target_k53_tele` is its model `tteW`** (generated). -/
l_model tte_spec (p : Prog) (L : K53Look p)
  fns [L.tte ↦ tteW list]
  specs [ee_spec p L n, slEq_spec p L.eq n]
  grind [arena_grind]

end L.Ind

end
end
