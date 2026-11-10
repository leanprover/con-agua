module

public import ConAgua.Arena.IndPosSpec.MatesW
public import ConAgua.Arena.StripTeleSpec
import ConAgua.L.ModelGen
public import ConAgua.Arena.IndParts
import all ConAgua.Arena.IndParts

@[expose] public section

/-!
# BsoK2

The generated `bsoW` (`bso_spec`), `bsoTwin`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `block_shape_result_sort` -/

/-- **`block_shape_result_sort` is its model `bsoW`** (generated). -/
l_model bso_spec (p : Prog) (hv : p.lookup "e_view" = some eView) (hpw : p.lookup "pin_word" = some pinWordL)
    (hg : p.lookup "sl_getd" = some slGetD)
    (hp : p.lookup "block_shape_result_sort" = some blockShapeResultSort) (hst : StripProg p)
  fns [hp ↦ bsoW list]
  specs [slGetD_specW p hg n, stripPis_specF p hst n, eView_spec p hv n, pinWord_specV p hpw n]
  grind [arena_grind, ind_grind]

/-- The twin's result sort (`blockShape?`'s first `let s`). -/
def bsoTwin (nP : Nat) (nIdxs : List Nat) (ty : EIdx) : AM LIdx := do
  match ← stripPis (nP + nIdxs.headD 0) ty with
  | some q => do
    match ← view q.2 with
    | .sort s => pure s
    | _ => zeroLevel
  | none => zeroLevel

end L.Ind

end
