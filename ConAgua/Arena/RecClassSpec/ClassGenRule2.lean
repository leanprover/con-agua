import ConAgua.Arena.RecClassSpec.RuW
import ConAgua.Census.Attr

/-!
# ClassGenRule2: `ConRon.Arena.classGenRule`

The refinement theorems `classGenRule_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **`class_gen_rule` refines `classGenRule`** (through `open_pis_at_fvars_f`'s real refinement and the stubs of
`mk_app_n_f`, `fvar_type_ds`, `close_lams`'s `abstract1_fast`; the generator, the constructor record,
the classes of the recursors and the generated constants decoded below the tops). -/
@[refines ConRon.Arena.classGenRule]
theorem classGenRule_refines (p : Prog) (hp : RuProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (g rco rcl cgo cgl rlvls c x : Word) (G : ClassGen)
    (X : ClassCtor) (recCls : List Nat) (cvGs : List IConstantVal) (hS : StageR dn vis fe s₀.mem a₀)
    (hG : DecB (fun m => decCG m g.toNat) s₀.mem G) (hns : G.nP + G.slots.length < 2 ^ 64)
    (hX : DecB (fun m => decCC m x.toNat) s₀.mem X) (hrl : H rlvls)
    (hrc : DecB (fun m => decNL m rco.toNat rcl.toNat) s₀.mem recCls) (hrcb : rco.toNat + rcl.toNat < 2 ^ 64)
    (hcg : DecB (fun m => decPL m (decCVp m) cgo.toNat cgl.toNat) s₀.mem cvGs) (hcgb : cgo.toNat + cgl.toNat < 2 ^ 64)
    (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_rule" [g, rco, rcl, cgo, cgl, rlvls, c, x]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classGenRule G recCls cvGs (decI rlvls) c.toNat X) a₀ ∧
      KP dn vis fe s₀.mem decOE (r, s'.mem) (AM.st (ConRon.Arena.classGenRule G recCls cvGs (decI rlvls) c.toNat X) a₀)
        (AM.res (ConRon.Arena.classGenRule G recCls cvGs (decI rlvls) c.toNat X) a₀) ∧ AbsOK s'.mem; ⊤⦄ :=
  triple_post (classGenRule_spec p hp n s₀ g rco rcl cgo cgl rlvls c x) fun _ _ ⟨hl, hw⟩ =>
    let h := (ruW_sim dn vis fe n _ a₀ g rco rcl cgo cgl rlvls c x G X recCls cvGs hS hG hns hX hrl hrc hrcb hcg hcgb
      hA).am hw
    ⟨hl, h.1, h.2.1, h.2.2⟩

end L.Ind

end
