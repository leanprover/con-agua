import ConAgua.Arena.IndIface

/-!
# PcrK3

`pcrK3`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `nest_crest` refines `nestCrest` -/

def pcrK3 : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) => some ([1, r], m3)
end L.Ind

end
