import ConAgua.Arena.RecCheckSpec.ArfW
import ConAgua.Census.Attr

/-!
# AuxRuleFire: `ConRon.Arena.auxRuleFire`

The refinement theorems `auxRuleFire_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **`aux_rule_fire` refines `auxRuleFire`** (through `view_ls` and `abstract_prefix_list`'s stub):
the fire `.nested lvls pins` as `(1, lvls, pins)`, slices below the top. -/
@[refines ConRon.Arena.auxRuleFire]
theorem auxRuleFire_refines (p : Prog) (hp : ArfLook p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M rP : Word) (TM : TargetMajor)
    (hS : StageR dn vis fe s₀.mem a₀) (hM : DecB (fun m => decTM m M.toNat) s₀.mem TM)
    (hP : PoolSmall s₀.mem) (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "aux_rule_fire" [M, rP]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.auxRuleFire TM rP.toNat) a₀ ∧
      KP dn vis fe s₀.mem decFire (r, s'.mem) (AM.st (ConRon.Arena.auxRuleFire TM rP.toNat) a₀)
        (AM.res (ConRon.Arena.auxRuleFire TM rP.toNat) a₀) ∧ AbsOK s'.mem; ⊤⦄ :=
  triple_post (auxRuleFire_spec p hp n s₀ M rP) fun _ _ ⟨hl, hw⟩ =>
    let h := (arfW_sim dn vis fe n _ a₀ M rP TM hS hM hP hA).am hw
    ⟨hl, h.1, h.2.1, h.2.2⟩

end L.Ind

end
