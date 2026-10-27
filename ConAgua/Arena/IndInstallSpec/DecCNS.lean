import ConAgua.Arena.IndIface

/-!
# DecCNS

`decCNS`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- A member's constructors: a pointer to `[off, len]` of `[cv, nF]` pointers. -/
def decCNS (m : Mem) (mp : Nat) : Option (List (IConstantVal × Nat)) := decAt m (decPL m (decCN m)) mp

end L.Ind

end
