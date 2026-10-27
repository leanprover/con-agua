import ConRon.Arena.Store
import Std.WP.Assertion
import ConAgua.Arena.Reasons

/-!
# NodeV

`NodeV`.
-/

set_option linter.unusedSectionVars false

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The non-leaf, non-`const` views: the ones whose walk goes through `mentions_any_node`. -/
def NodeV : ENodeView → Prop
  | .fvar .. | .app .. | .lam .. | .forallE .. | .letE .. | .proj .. => True
  | _ => False

end L.Ind

end
