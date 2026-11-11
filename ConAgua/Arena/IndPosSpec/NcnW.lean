module

import ConAgua.Arena.IndGrindAttr
public import ConAgua.Arena.IndPosSpec.Rx
import ConAgua.L.ModelGen
import all ConAgua.Arena.IndPos2

@[expose] public section

/-!
# NcnW

`nestCtorNf_spec`: the model `ncnW` of `nest_ctor_nf`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **`nest_ctor_nf` is its model `ncnW`** (generated, the fuel a parameter: the spec at exec fuel
`k + 1`). -/
l_model nestCtorNf_spec (p : Prog) (hL : RxLook p) (hp : p.lookup "nest_ctor_nf" = some nestCtorNfL)
  fns [hp ↦ ncnW]
  specs [posRec5_specW p hL.ha hL.h5 n, (rxSpec_all p hL n).2.2.2.1, (rxSpec_all p hL n).2.2.2.2.2.2.2]
  grind [arena_grind] fold [tierW, idxW] finish [tierW, idxW] pfuel

end L.Ind

end
