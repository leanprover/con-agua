import ConAgua.Arena.DeclCanonEq
import ConAgua.Arena.DeclRec

/-!
# `ci_to_cv` in L (lane `decls3`, helper `decls3-canon`)

`ci_to_cv(p)` is `p + 1`, the inline constant value of the constant record at `p`; it refines the
twin's pure projection `IConstantInfo.toConstantVal` (`ciToCv_refines`).
-/

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

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
    {o c : Nat} (hc : o + c ≤ t) : (hslice? b o c : Option (List (Idx kk))) = hslice? a o c := by
  simp only [hslice?]
  exact mapM_congr_of _ _ _ fun j hj => by
    simp only [List.mem_range] at hj
    simp only [hd?, h (o + j) (by omega)]

/-- **A fresh constant value** `⟨nm, lps, ty⟩` written at `q‥q+3` decodes to itself. -/
theorem decCV_new {a a' : Array Word} {N q : Nat} {nm lo ll ty : Word} {lps : List NIdx}
    (hnm : nm.toNat < 2 ^ 32) (hty : ty.toNat < 2 ^ 32) (h0 : a'[q]? = some nm)
    (h1 : a'[q + 1]? = some lo) (h2 : a'[q + 2]? = some ll) (h3 : a'[q + 3]? = some ty)
    (hs : hslice? a lo.toNat ll.toNat = some lps) (hlow : ∀ i < N, a'[i]? = a[i]?)
    (hb : ll.toNat = 0 ∨ lo.toNat + ll.toNat ≤ N) :
    decCV a' q = some ⟨decI nm, lps, decI ty⟩ := by
  have hsl : hslice? a' lo.toNat ll.toNat = some lps := by
    rcases hb with h | h
    · rw [h] at hs ⊢; simpa [hslice?] using hs
    · rw [hslice_agree hlow h]; exact hs
  simp only [decCV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def]
  refine ⟨decI nm, ?_, lps, ?_, decI ty, ?_, rfl⟩
  · simp [hd?, h0, hnm]
  · simp only [hlist?, nat?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.map_eq_some_iff]
    exact ⟨lo.toNat, ⟨lo, h1, rfl⟩, ll.toNat, ⟨ll, h2, rfl⟩, hsl⟩
  · simp [hd?, h3, hty]


theorem erecP_rd {m : Mem} {j : Nat} {w : Word} (h : (erecP m)[j]? = some w) :
    (m.arr64 EREC)[j]? = some w := by
  rw [← erecP_getE (erecP_lt h)]; exact h

theorem ctc_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem} {a : AState}
    (hS : StageR dn vis fe m a) {x : Word} {ci : IConstantInfo}
    (hci : decCI (erecP m) dn x.toNat = some ci) :
    decCV (erecP m) (x + 1).toNat = some ci.toConstantVal := by
  obtain ⟨wk, e, hk⟩ := ciD hci
  have hsz : (m.arr64 EREC).size < 2 ^ 64 := hS.2.2.2.2.1
  have hsz' : (erecP m).size < 2 ^ 64 := Nat.lt_of_le_of_lt (by simp [erecP]; exact Nat.min_le_right _ _) hsz
  have step : ∀ {cv : IConstantVal}, decCV (erecP m) (x.toNat + 1) = some cv →
      decCV (erecP m) (x + 1).toNat = some cv := by
    intro cv hcv
    obtain ⟨w, hw, -⟩ := decCV_name hcv
    have := toNat_add_of_get hsz' (k := 1) (kn := 1) rfl hw
    rw [this]; exact hcv
  rcases hk with ⟨k0, cv, hcv, rfl⟩ | ⟨k0, cv, v, hi, hcv, hv, hhi, rfl⟩ | ⟨k0, cv, hcv, rfl⟩ |
      ⟨k0, cv, caps, hcv, hcaps, rfl⟩ | ⟨k0, cv, np, nf, hcv, hnp, hnf, rfl⟩ |
      ⟨k0, cv, mi, rp, o, c, rules, hcv, hmi, hrp, ho, hc, hr, rfl⟩ <;>
    exact step hcv

section refs
variable (p : Prog) (hp : CanonProg p) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
include hp

/-- **`ci_to_cv` refines `IConstantInfo.toConstantVal`**: the result decodes in `erecP` of the
memory after (records below the pool's top). -/
@[refines ConRon.Arena.IConstantInfo.toConstantVal]
theorem ciToCv_refines (q : Word) (ci : IConstantInfo) :
    RefAM p "ci_to_cv" [q]
      (fun m a => StageR dn vis fe m a ∧ decCI (erecP m) dn q.toNat = some ci)
      (pure ci.toConstantVal)
      (KeepPost dn vis fe (fun m r (cv : IConstantVal) => decCV (erecP m) (r.headD 0).toNat = some cv)) := by
  intro n s₀ a₀ ⟨hS, hci⟩
  refine triple_post (ciToCv_spec' p hp n s₀ q) ?_
  rintro r s' ⟨hl, hm, hr⟩
  exact ⟨hl, trivial, by rw [hm]; exact hS, by rw [hm]; exact IWGrow.refl _,
    by rw [hm, hr]; exact ctc_ok hS hci⟩

end refs

end L.Ind
