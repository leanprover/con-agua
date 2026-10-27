import ConAgua.Arena.IndPos2SpecO

/-! # `IndPos2`, the `nestPos` block (lane `indproofs2`, helper `pos2`): the census theorems — each
function of the block, run by `exec` at any fuel `n`, refines its twin
(`nbSpec_all`: L ⊑ the word models; `nbOK_all`: the models ⊑ the twin). -/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section census
variable {p : Prog} (L : NbLook p) (n : Nat) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
include L

end census

end L.Ind
