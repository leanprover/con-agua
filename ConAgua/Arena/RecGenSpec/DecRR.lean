import ConAgua.Arena.IndIface

/-!
# DecRR

`decRR`, `crrXs`, `crrK5`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## The `rec4` records -/

/-- `IConstantVal × TargetMajor × List EIdx` at `p`: `[cv, M, rhss.off, rhss.len]`. -/
def decRR (m : Mem) (p : Nat) : Option (IConstantVal × TargetMajor × List EIdx) := do
  let cvp ← iwN m p
  let cv ← decCVp m cvp
  let mp ← iwN m (p + 1)
  let M ← decTM m mp
  let rhss ← decAt m (decHL m) (p + 2)
  pure (cv, M, rhss)

/-! ## The model -/

/-- The constructors of class `c` (`g.ctors.getD c []`) as a slice. -/
def crrXs (m : Mem) (g c : Word) : Word × Word :=
  if c < rdW (m.arr64 IW) (g + 10) then
    (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (g + 9) + c)),
     rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (g + 9) + c) + 1))
  else (0, 0)

def crrK5 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) => some ([r5.headD 0, r5.tail.headD 0], m5)

end L.Ind

end
