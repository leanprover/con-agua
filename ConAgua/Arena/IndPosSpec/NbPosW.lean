import ConAgua.Arena.IndPosSpec.NbKeyK2
import ConAgua.Arena.IndRealNames
import ConAgua.Arena.IndGrindAttr
import ConAgua.Arena.IndPosSpec.NestGroupCtors

/-!
# NbPosW

`nwsWf`: `nest_walk_stack`'s model at any exec fuel.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- `nest_walk_stack` at any exec fuel. -/
def nwsWf : Nat → Mem → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | n + 1, m, ctx, off, l, po, pl => nwsW n m ctx off l po pl
  | _, _, _, _, _, _, _ => none

end L.Ind

end
