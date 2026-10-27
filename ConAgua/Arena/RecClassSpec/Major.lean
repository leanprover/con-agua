import ConAgua.Arena.RecClassSpec.MjW
import ConAgua.Census.Attr

/-!
# Major: `ConRon.Arena.ClassGen.major`, `ConRon.Arena.ClassGen.motiveTy`

The refinement theorems `classGenMajor_refines`, `classGenMotiveTy_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **`class_gen_major` refines `ClassGen.major`** (through `open_pis_at_fvars_f`'s real
refinement, under the walk memos, kept after; the class generator decoded below the tops). -/
@[refines ConRon.Arena.ClassGen.major]
theorem classGenMajor_refines (p : Prog) (hp : MjProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (g c d : Word) (G : ClassGen)
    (hS : StageR dn vis fe s₀.mem a₀) (hG : DecB (fun m => decCG m g.toNat) s₀.mem G)
    (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_major" [g, c, d]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.ClassGen.major G c.toNat d.toNat) a₀ ∧
      KP dn vis fe s₀.mem decOLE (r, s'.mem) (AM.st (ConRon.Arena.ClassGen.major G c.toNat d.toNat) a₀)
        (AM.res (ConRon.Arena.ClassGen.major G c.toNat d.toNat) a₀) ∧ AbsOK s'.mem; ⊤⦄ :=
  triple_post (classGenMajor_spec p hp n s₀ g c d) fun _ _ ⟨hl, hw⟩ =>
    ⟨hl, (mjW_sim dn vis fe n _ a₀ g c d G hS hG hA).am hw⟩

/-- **`class_gen_motive_ty` refines `ClassGen.motiveTy`** (through the stubs of `class_gen_major`,
`fvar_type_ds` and `close_telescope`'s `abstract1_fast`). -/
@[refines ConRon.Arena.ClassGen.motiveTy]
theorem classGenMotiveTy_refines (p : Prog) (hp : MtProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (g c d : Word) (G : ClassGen)
    (hS : StageR dn vis fe s₀.mem a₀) (hG : DecB (fun m => decCG m g.toNat) s₀.mem G) (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_motive_ty" [g, c, d]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.ClassGen.motiveTy G c.toNat d.toNat) a₀ ∧
      KP dn vis fe s₀.mem decOE (r, s'.mem) (AM.st (ConRon.Arena.ClassGen.motiveTy G c.toNat d.toNat) a₀)
        (AM.res (ConRon.Arena.ClassGen.motiveTy G c.toNat d.toNat) a₀) ∧ AbsOK s'.mem; ⊤⦄ :=
  triple_post (classGenMotiveTy_spec p hp n s₀ g c d) fun _ _ ⟨hl, hw⟩ =>
    let h := (motW_sim dn vis fe n _ a₀ g c d G hS hG hA).am hw
    ⟨hl, h.1, h.2.1, h.2.2⟩

end L.Ind

end
