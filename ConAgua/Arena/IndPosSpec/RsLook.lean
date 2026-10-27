import ConAgua.Arena.IndPosSpec.NbLook

/-!
# RsLook

`RsLook`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## L ⊑ the models -/

/-- The root frame's and the seeds' lookups. -/
structure RsLook (p : Prog) : Prop where
  nb : NbLook p
  proot : p.lookup "nest_root" = some nestRootL
  pfuel : p.lookup "nest_seeds_fuel" = some nestSeedsFuelL
  pseeds : p.lookup "nest_seeds" = some nestSeedsL

end L.Ind

end
