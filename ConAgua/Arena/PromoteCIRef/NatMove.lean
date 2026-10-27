import ConAgua.Arena.EnvRec

/-!
# NatMove

`nat?_move`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

theorem nat?_move {a b : Array Word} {i j x : Nat} (hw : b[j]? = a[i]?) (h : nat? a i = some x) :
    nat? b j = some x := by
  simp only [L.Arena.nat?] at h ⊢; rw [hw]; exact h

end L.Arena
