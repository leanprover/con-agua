import ConAgua.Arena.IndIface

/-!
# Of

`ErecGrow.of_eq`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

theorem ErecGrow.of_eq {m m' : Mem} (hE : m'.arr64 EREC = m.arr64 EREC)
    (hT : erecTop m' = erecTop m) : ErecGrow m m' :=
  ⟨by omega, fun i _ => by rw [hE], by rw [hE]⟩

end L.Arena
