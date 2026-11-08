module

import ConAgua.Arena.IndPosSpec.BvbWMfr
public import ConAgua.Arena.RecCheckSpec.TaCW

@[expose] public section

/-!
# BvbWStageC

`taF`, `bvbW_stageC`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

def taF : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, no, nl, lvls, ho, hl, e => taAW n m no nl lvls ho hl e

section rel
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

/-- **`bvar_b` under the stage relation at the twin's `coreWalkFuel`**, at any exec fuel (the L
fuel word `CWF` is `coreWalkFuel`: `bvbW_okF`'s first alternative). -/
theorem bvbW_stageC {m m' : Mem} {a : AState} (hS : StageR vis fe m a) (n : Nat)
    (h x : Word) (hh : H h) (hb : bvbW n m h CWF = some (x, m')) :
    ∃ a', (bvarB coreWalkFuel (decE h)).run a = .ok (x.toNat, a') ∧ StageR vis fe m' a' ∧ IWGrow m m' ∧
      MFr [] [] m m' := by
  sorry

end rel

end L.Ind

end
