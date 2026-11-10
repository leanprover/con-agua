module

public import ConAgua.Arena.IndPosSpec.NoConstWf
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.WP.Tactic
import ConAgua.L.ModelGen
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.IndPos2

@[expose] public section

/-!
# NestOccAny

`noaW`, `noaK`, `noaW_nil`, `noaW_cons`, `noaK_hit`, `noaK_miss` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `nest_occ_any`: `xs.anyM (nestOcc names lo hi ·)` -/

l_model nestOccAny_spec (p : Prog) (hl : NoLook p) (hp : p.lookup "nest_occ_any" = some nestOccAnyL)
  fns [hp ↦ noaW list]
  specs [nestOcc_spec' p hl n]
  grind [arena_grind] fold [tierW, idxW] finish [tierW, idxW]

end L.Ind

end
