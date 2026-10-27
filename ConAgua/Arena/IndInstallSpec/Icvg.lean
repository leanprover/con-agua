import ConAgua.Arena.RecClassSpec.Classes
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

/-!
# Icvg

`icvg_spec`, `icvgW`, `RecsB`, `ShapeCV`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `check_block_inds_cv_tas` -/

/-- **`check_block_inds_cv_tas_go` is its model `icvgW`** (generated). -/
l_model icvg_spec (p : Prog) (hp : p.lookup "check_block_inds_cv_tas_go" = some checkBlockIndsCvTasGo)
  fns [hp ↦ icvgW]
  specs [callW_spec p n "sl_cons"]
  grind [ind_grind] finish [rdW_eq] gen 20

/-- The recursor shapes' slice of the shape at `pp` lies below the top. -/
def RecsB (m : Mem) (pp : Word) : Prop :=
  ∀ o l, iwN m (pp.toNat + 2) = some o → iwN m (pp.toNat + 3) = some l → o + l ≤ iwTop m

/-- Every member's former constant record lies below the tops (`CVExt`). -/
def ShapeCV (m : Mem) (q : Word) : Prop :=
  ∀ o l, iwN m q.toNat = some o → iwN m (q.toNat + 1) = some l → ∀ j < l, ∀ c,
    iwN m (o + j) = some c → ∀ d, iwN m c = some d → CVExt m d

end L.Ind

end
