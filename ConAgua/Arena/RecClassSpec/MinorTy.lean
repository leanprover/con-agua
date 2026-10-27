import ConAgua.Arena.RecClassSpec.MnW

/-!
# MinorTy: `ConRon.Arena.ClassGen.minorTy`

The refinement theorems `classGenMinorTy_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **`class_gen_minor_ty` refines `ClassGen.minorTy`** (through `open_pis_at_fvars_f`'s real refinement and its other callees:
`get_app_args`, `mk_app_n_f`, `fvar_type_ds`, `close_telescope`'s `abstract1_fast`, …; the generator
and the constructor record decoded below the tops). -/
@[refines ConRon.Arena.ClassGen.minorTy]
theorem classGenMinorTy_refines (p : Prog) (hp : MnProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (g c x d : Word) (G : ClassGen) (X : ClassCtor)
    (hS : StageR dn vis fe s₀.mem a₀) (hG : DecB (fun m => decCG m g.toNat) s₀.mem G)
    (hns : G.nP + G.slots.length < 2 ^ 64) (hX : DecB (fun m => decCC m x.toNat) s₀.mem X)
    (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_minor_ty" [g, c, x, d]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.ClassGen.minorTy G c.toNat X d.toNat) a₀ ∧
      KP dn vis fe s₀.mem decOE (r, s'.mem) (AM.st (ConRon.Arena.ClassGen.minorTy G c.toNat X d.toNat) a₀)
        (AM.res (ConRon.Arena.ClassGen.minorTy G c.toNat X d.toNat) a₀) ∧ AbsOK s'.mem; ⊤⦄ :=
  triple_post (classGenMinorTy_spec p hp n s₀ g c x d) fun _ _ ⟨hl, hw⟩ =>
    let h := (mnW_sim dn vis fe n _ a₀ g c x d G X hS hG hns hX hA).am hw
    ⟨hl, h.1, h.2.1, h.2.2⟩

end L.Ind

end
