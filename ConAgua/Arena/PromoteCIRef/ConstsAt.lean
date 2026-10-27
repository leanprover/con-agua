import ConAgua.Arena.EnvRec

/-!
# ConstsAt

`ConstsAt`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The constants at `ECON` positions `j, j - 1, …`, decoded in the pool `A`, are `cs`. -/
def ConstsAt (dn : NIdx → Option ConLeche.Name) (A E : Array Word) : Nat → List IConstantInfo → Prop
  | _, [] => True
  | j, ci :: cs => (∃ ptr : Word, E[j]? = some ptr ∧ decCI A dn ptr.toNat = some ci) ∧
      ConstsAt dn A E (j - 1) cs

end L.Arena
