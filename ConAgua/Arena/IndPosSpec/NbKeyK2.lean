module

public import ConAgua.Arena.IndPosSpec.DepthGo

@[expose] public section

/-!
# NbKeyK2

`wfWf`: a callee's model at any exec fuel.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Callees at any exec fuel -/

/-- `whnf_walk_fuel` at any exec fuel. -/
def wfWf : Nat → Mem → Word → Option (List Word × Mem)
  | n + 2, m, e => match wfW n m e with
    | none => none
    | some (r, m1) => some ([r], m1)
  | _, _, _ => none

end L.Ind

end
