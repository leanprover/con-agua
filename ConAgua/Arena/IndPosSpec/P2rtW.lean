module

import ConAgua.Arena.IndPosSpec.Nb
import ConAgua.L.ModelGen
public import ConAgua.Arena.IndPosSpec.RsLook
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.Arena.IndPosSpec.UnW
public import ConAgua.Arena.IndPosSpec.NbKeyK2
import all ConAgua.Arena.IndPos2

@[expose] public section

/-!
# P2rtW

`p2sfW`, `p2sfK`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Models -/

l_model nestSeedsFuel_spec (p : Prog) (hL : RsLook p)
  fns [hL.pfuel ↦ p2sfW list]
  specs [whnfWalkFuel_spec' p hL.nb n]
  grind [arena_grind] fold [tierW, idxW] finish [tierW, idxW]


end L.Ind

end
