import ConAgua.Arena.IndPosSpec.DepthGo

/-!
# PcrK1

`pcrK1`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

def pcrK1 (k : Nat) (dO dL hO hL : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => if r1.headD 0 = 0 then some ([0, 0], m1)
      else pcrK2 k (r1.tail.headD 0) (posRecW m1 [1, dO, dL, hO, hL])
end L.Ind

end
