import ConAgua.Arena.IndPosSpec.RxMapW
import ConAgua.Arena.IndGrindAttr

/-!
# NcnW

`ncnK3`, `ncnK2`, `ncnK1`, `ncnW`, `ncnK3_some`, `ncnK2_some` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

def ncnK3 (us cv q l : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (ty, m3) => posRecW m3 [rdW (m3.arr64 EREC) cv, us, q, l, ty]
def ncnK2 (k : Nat) (f us cv closed : Word) : Option (Word × Word × Mem) → Option (Word × Mem)
  | none => none
  | some (q, l, m2) => ncnK3 us cv q l (rxW k m2 f closed)
def ncnK1 (k : Nat) (us dO dL cv closed : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (f, m1) => ncnK2 k f us cv closed (rxDsW k m1 f dO dL)
/-- The model of `nest_ctor_nf` at exec fuel `k + 1`. -/
def ncnW (k : Nat) (m : Mem) (ctx po pl us dO dL cv closed : Word) : Option (Word × Mem) :=
  ncnK1 k us dO dL cv closed (posRecW m [0, ctx, po, pl, pl])

section arms
variable (k : Nat) (m1 m2 m3 : Mem) (f us cv closed dO dL q l ty : Word)
theorem ncnK3_some : ncnK3 us cv q l (some (ty, m3)) = posRecW m3 [rdW (m3.arr64 EREC) cv, us, q, l, ty] := rfl
theorem ncnK2_some : ncnK2 k f us cv closed (some (q, l, m2)) = ncnK3 us cv q l (rxW k m2 f closed) := rfl
theorem ncnK1_some : ncnK1 k us dO dL cv closed (some (f, m1)) = ncnK2 k f us cv closed (rxDsW k m1 f dO dL) := rfl
end arms
attribute [ind_grind] ncnK3_some ncnK2_some ncnK1_some

end L.Ind

end
