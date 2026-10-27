import ConAgua.Arena.IndPosSpec.PcrK1

/-!
# PcrW

`pcrW`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The model of `nest_crest` at exec fuel `k + 3`. -/
def pcrW (k : Nat) (m : Mem) (no nl us dO dL hO hL cty : Word) : Option (List Word × Mem) :=
  pcrK1 k dO dL hO hL (pccW k m no nl us dL cty)

end L.Ind

end
