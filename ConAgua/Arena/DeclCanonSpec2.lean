module

import ConAgua.Arena.DeclCanonEq
import ConAgua.Arena.DeclRec
import ConRon.Bridge.Grind
public import ConAgua.Arena.DeclCanonSpec
import all ConAgua.Arena.DeclArmsCanon

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

theorem hslice_agree {kk : IdxKind} {a b : Array Word} {t : Nat} (h : ∀ i < t, b[i]? = a[i]?)
    {o c : Nat} (hc : o + c ≤ t) : (hslice? (aread b) o c : Option (List (Idx kk))) = hslice? (aread a) o c := by
  sorry

/-- **A fresh constant value** `⟨nm, lps, ty⟩` written at `q‥q+3` decodes to itself. -/
theorem decCV_new {a a' : Array Word} {N q : Nat} {nm lo ll ty : Word} {lps : List NIdx}
    (hnm : nm.toNat < 2 ^ 32) (hty : ty.toNat < 2 ^ 32) (h0 : a'[q]? = some nm)
    (h1 : a'[q + 1]? = some lo) (h2 : a'[q + 2]? = some ll) (h3 : a'[q + 3]? = some ty)
    (hs : hslice? (aread a) lo.toNat ll.toNat = some lps) (hlow : ∀ i < N, a'[i]? = a[i]?)
    (hb : ll.toNat = 0 ∨ lo.toNat + ll.toNat ≤ N) :
    decCV (aread a') q = some ⟨decI nm, lps, decI ty⟩ := by
  sorry

theorem ctc_ok {vis : Word} {fe : IFEnv} {m : Mem} {a : AState}
    (hS : StageR vis fe m a) {x : Word} {ci : IConstantInfo}
    (hci : decCI (erecP m) x.toNat = some ci) :
    decCV (erecP m) (x + 1).toNat = some ci.toConstantVal := by
  have hcv := ciD_cv hci
  obtain ⟨w, hw, -⟩ := decCV_name hcv
  have hb := erecP_lt64 hw
  have e : (x + 1).toNat = x.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  rw [e]; exact hcv

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
    by rw [hm]; show decCV _ (r.headD 0).toNat = some ci.toConstantVal; rw [hr]; exact ctc_ok hS hci⟩

end refs

end L.Ind
