import ConAgua.Arena.IndPosSpec.BvbWMfr
import ConAgua.Arena.IndPosSpec.NbPosW
import ConAgua.Arena.IndPosSpec.PosBindT
import ConAgua.Arena.IndPosSpec.KlB
import ConAgua.Arena.IndPosSpec.WCtx

/-!
# WalkOK

`CtorsCtx`: the constructor walk's slices.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section stmts
variable (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)

/-- The facts every constructor walk of a frame shares. -/
structure CtorsCtx (m : Mem) (us dO dL no nl hO hL : Word) (ds : List EIdx) (names : List NIdx)
    (holes : List EIdx) : Prop where
  hus : H us
  hds : DecB (fun m => (decHL m dO.toNat dL.toNat : Option (List EIdx))) m ds
  hdsb : dO.toNat + dL.toNat ≤ iwTop m
  hnames : decHL m no.toNat nl.toNat = some names
  hnamesb : no.toNat + nl.toNat ≤ iwTop m
  hnn : dL.toNat + names.length < 2 ^ 64
  hholes : decHL m hO.toNat hL.toNat = some holes
  hholesb : hO.toNat + hL.toNat ≤ iwTop m

end stmts

end L.Ind

end
