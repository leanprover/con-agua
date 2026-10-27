import ConAgua.Arena.PromoteCIInfra

/-!
# PreESizeLe

`preE_size_le`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

theorem preE_size_le (m : Mem) (D : Nat) : (preE m D).size ≤ D := by
  simp [preE, Nat.min_le_left]

end L.Arena
