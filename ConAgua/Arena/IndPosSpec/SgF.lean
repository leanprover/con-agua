import ConRon.Arena.Inductives.Positivity
import ConAgua.Arena.Reasons

/-!
# SgF

`sgF`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ### The relational side -/

/-- The twin's per-parameter step of `nestSeedOf`. -/
def sgF (c : NestCtx) (holes : List EIdx) (x : EIdx) : AM EIdx := do
  let y ← ConRon.Arena.replaceApps c.names c.lvls 0 c.nP x
  ConRon.Arena.replaceFVars (.keyMap c.params holes) y

end L.Ind

end
