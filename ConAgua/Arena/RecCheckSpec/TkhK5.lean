import ConAgua.L.Semantics
import ConRon.Arena.Handle
import Std.WP.Assertion
import ConAgua.Arena.Reasons

/-!
# TkhK5

`tkhK5`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `target_k53_heads` -/

def tkhK5 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

end L.Ind

end
