import ConAgua.Arena.IndPosSpec.GgW
import ConAgua.Arena.IndPosSpec.MW9
import ConAgua.Arena.IndPosSpec.NcnW
import ConAgua.Arena.IndPosSpec.P2ctK1
import ConAgua.Arena.IndPosSpec.FgW2

/-!
# NbKeyK2

`wfWf`, `ncnWf`: callees' models at any exec fuel.
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

/-- `nest_ctor_nf` at any exec fuel. -/
def ncnWf : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | k + 1, m, ctx, po, pl, us, dO, dL, cv, closed => match ncnW k m ctx po pl us dO dL cv closed with
    | none => none
    | some (r, m1) => some ([r], m1)
  | _, _, _, _, _, _, _, _, _, _ => none

end L.Ind

end
