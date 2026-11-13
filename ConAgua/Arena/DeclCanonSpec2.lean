module

import ConRon.Bridge.Grind
public import ConAgua.Arena.DeclCanonSpec
import all ConAgua.Arena.DeclArmsCanon
import ConAgua.Arena.RecLayout.CIDec

@[expose] public section

/-!
# `ci_to_cv` in L (lane `decls3`, helper `decls3-canon`)

`ci_to_cv(p)` is `p + 1`, the inline constant value of the constant record at `p`; it refines the
twin's pure projection `IConstantInfo.toConstantVal` (`ciToCv_refines`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section specs
variable (p : Prog) (hp : CanonProg p)
include hp

theorem ciToCv_spec' (n : Nat) (s₀ : St) (x : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ci_to_cv" [x]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ r.headD 0 = x + 1; ⊤⦄ := by
  rw [invoke_eq _ (hp.get "ci_to_cv")]
  simp only [callFn, ciToCv]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs] <;>
      simp_all [LocEq, BinOp.eval, Sig.retVal, Sig.retOr, Locals.init]

end specs

/-! ## The relational lemma -/

section refs
variable (p : Prog) (hp : CanonProg p) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
include hp

/-- **`ci_to_cv` refines `IConstantInfo.toConstantVal`**: the result decodes in `erecP` of the
memory after (records below the pool's top). -/
@[refines ConRon.Arena.IConstantInfo.toConstantVal]
theorem ciToCv_refines (q : Word) (ci : IConstantInfo) :
    RefAM p "ci_to_cv" [q]
      (fun m a => StageR vis fe m a ∧ decCI (erecP m) q.toNat = some ci)
      (pure ci.toConstantVal)
      (KeepPost vis fe (fun m r (cv : IConstantVal) => decCV (erecP m) (r.headD 0).toNat = some cv)) := by
  intro n s₀ a₀ ⟨hS, hci⟩
  refine triple_post (ciToCv_spec' p hp n s₀ q) ?_
  rintro r s' ⟨hl, hm, hr⟩
  exact ⟨hl, trivial, by rw [hm]; exact hS, by rw [hm]; exact IWGrow.refl _,
    by rw [hm]; show decCV _ (r.headD 0).toNat = some ci.toConstantVal; rw [hr]; exact decCI_cv_rd (erRdOK _) hci⟩

end refs

end L.Ind
