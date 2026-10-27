import ConAgua.Arena.PromoteCIInfra

/-!
# PreECongr

`preE_congr`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

theorem preE_congr {m m' : Mem} (h : m'.arr64 EREC = m.arr64 EREC) (T : Nat) :
    preE m' T = preE m T := by simp [preE, h]

end L.Arena
