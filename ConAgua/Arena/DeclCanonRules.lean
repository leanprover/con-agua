module

import ConAgua.Arena.DeclCanonEq
public import ConAgua.Arena.DeclCanonExpr2
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.DeclArmsCanon

@[expose] public section

/-!
# `canon_rules_eq` (lane `decls3`, helper `decls3-canon`)
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **The model of `canon_rules_eq`** (`cnCrW`). -/
l_model canonRulesEq_spec (p : Prog) (hp : CanonProg p)
  fns [hp.get "canon_rules_eq" ↦ cnCrW]
  specs [ruleEqButRhs_spec p hp n, canonExprEq_spec p hp n]
  grind [arena_grind]

theorem decRules_length {R : Nat → Option Word} {o l : Nat} {xs : List IRecRule}
    (h : decRules R o l = some xs) : xs.length = l := by
  have := mapM_opt_length _ _ _ h
  simpa using this

/-- The next rule's records, at the word address. -/
theorem decRules_shift {R : Nat → Option Word} {o : Word} {k : Nat} {rs : List IRecRule}
    (h : decRules R (o.toNat + 11) k = some rs) (hR : ∀ i v, R i = some v → i < 2 ^ 64) :
    decRules R (o + 11).toNat k = some rs := by
  cases k with
  | zero => simpa [decRules] using h
  | succ k =>
  have h' := h
  rw [decRules_succ] at h'
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h'
  obtain ⟨r0, hr0, -⟩ := h'
  obtain ⟨w, hw, -⟩ := hd?_some (decRule_ctor hr0)
  have := hR _ _ hw
  have e : (o + 11).toNat = o.toNat + 11 := by
    rw [UInt64.toNat_add]; simp only [show (11 : Word).toNat = 11 from rfl]; omega
  rw [e]; exact h

theorem cnCrW_ok {vis : Word} {fe : IFEnv} (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (po pl qo ql co cl fuel o1 l1 o2 l2 x : Word) (ps qs cs : List NIdx)
      (xs ys : List IRecRule),
    cnCrW k m po pl qo ql co cl fuel o1 l1 o2 l2 = some (x, m') → StageR vis fe m a →
    CtxR m po pl qo ql co cl ps qs cs → LitInj a → PoolSmall m →
    decRules (erecP m) o1.toNat l1.toNat = some xs → decRules (erecP m) o2.toNat l2.toNat = some ys →
    ∃ b, (ConRon.Arena.canonRulesEq ps qs cs fuel.toNat xs ys).run a = .ok (b, a) ∧
      x = (if b then 1 else 0) ∧ StageR vis fe m' a ∧ IWGrow m m' ∧ PoolSmall m' := by
  induction k with
  | zero => intro m m' a po pl qo ql co cl fuel o1 l1 o2 l2 x ps qs cs xs ys h; simp [cnCrW] at h
  | succ k ih =>
    intro m m' a po pl qo ql co cl fuel o1 l1 o2 l2 x ps qs cs xs ys h hS hC hL hP hxs hys
    rw [cnCrW] at h
    have lx := decRules_length hxs
    have ly := decRules_length hys
    by_cases h0 : l1 = 0 ∧ l2 = 0
    · rw [ite_eq_left h0] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have e1 : xs = [] := List.length_eq_zero_iff.mp (by rw [lx, h0.1]; rfl)
      have e2 : ys = [] := List.length_eq_zero_iff.mp (by rw [ly, h0.2]; rfl)
      subst e1 e2
      exact ⟨true, by simp [ConRon.Arena.canonRulesEq]; rfl, rfl, hS, IWGrow.refl _, hP⟩
    rw [ite_eq_right h0] at h
    by_cases h1 : l1 = 0 ∨ l2 = 0
    · rw [ite_eq_left h1] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      refine ⟨false, ?_, rfl, hS, IWGrow.refl _, hP⟩
      rcases xs with _ | ⟨x1, xs'⟩ <;> rcases ys with _ | ⟨y1, ys'⟩
      · exfalso; apply h0
        refine ⟨UInt64.toNat_inj.mp (by simpa using lx.symm), UInt64.toNat_inj.mp (by simpa using ly.symm)⟩
      · simp [ConRon.Arena.canonRulesEq]; rfl
      · simp [ConRon.Arena.canonRulesEq]; rfl
      · exfalso
        rcases h1 with h1 | h1 <;> (subst h1; simp at lx ly)
    rw [ite_eq_right h1] at h
    rw [not_or] at h1
    rcases xs with _ | ⟨x1, xs'⟩
    · exfalso; apply h1.1; exact UInt64.toNat_inj.mp (by simpa using lx.symm)
    rcases ys with _ | ⟨y1, ys'⟩
    · exfalso; apply h1.2; exact UInt64.toNat_inj.mp (by simpa using ly.symm)
    have l1e : l1.toNat = xs'.length + 1 := by simpa using lx.symm
    have l2e : l2.toNat = ys'.length + 1 := by simpa using ly.symm
    rw [l1e, decRules_succ] at hxs
    rw [l2e, decRules_succ] at hys
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hxs hys
    obtain ⟨x1', hx1e, xs'', hxs'e, hxeq⟩ := hxs
    obtain ⟨y1', hy1e, ys'', hys'e, hyeq⟩ := hys
    obtain ⟨rfl, rfl⟩ := List.cons.inj hxeq
    obtain ⟨rfl, rfl⟩ := List.cons.inj hyeq
    obtain ⟨w0, w1, w3, w8, e0, e1, e3, e8, h0', h8, c0, c1, c8, hf⟩ := ruleFields (erRdOK m) hx1e
    obtain ⟨v0, v1, v3, v8, f0, f1, f3, f8, g0', g8, d0, d1, d8, hg⟩ := ruleFields (erRdOK m) hy1e
    have hB := ruleEqButRhsB_ok (erRdOK m) hx1e hy1e
    have l1p : (l1 - 1).toNat = xs''.length := by rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp [l1e]
    have l2p : (l2 - 1).toNat = ys''.length := by rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp [l2e]
    rw [ConRon.Arena.canonRulesEq.eq_2]
    by_cases hbB : ruleEqButRhsB (erRd m) o1 o2 = true
    · have hd : ({ x1' with rhs := default } : IRecRule) = { y1' with rhs := default } :=
        of_decide_eq_true (hB ▸ hbB)
      have hcond : (({ x1' with rhs := default } : IRecRule) == { y1' with rhs := default }) = true :=
        beq_iff_eq.mpr hd
      simp (config := { decide := true }) only [hbB, ↓reduceIte] at h
      rw [erRd_foldN, erRd_foldN, e8, f8] at h
      cases hc : ceW k m po pl qo ql co cl fuel w8 v8 with
      | none => rw [hc] at h; simp [cnCrW.k_canon_expr_eq] at h
      | some xx =>
      obtain ⟨e1', m1⟩ := xx
      rw [hc, cnCrW.k_canon_expr_eq.eq_2] at h
      obtain ⟨b1, hb1, hr1, hS1, hg1, hP1⟩ := ceW_ok k m m1 a po pl qo ql co cl fuel w8 v8 e1' ps qs cs
        hc hS hC hL hP h8 g8
      rw [c8, d8] at *
      rw [ite_eq_left hcond]
      obtain ⟨b, hb, hr, q1, q2, q3⟩ := andThen_ok' (Q := StageR vis fe m' a ∧ IWGrow m m' ∧ PoolSmall m')
        hb1 hr1
        (fun hne2 => by
          rw [ite_eq_right hne2] at h
          have hx2 := decRules_shift (ArrExt.decRules (L.Ind.IWGrow.ext hg1) hxs'e) (erRdOK m1).lt
          have hy2 := decRules_shift (ArrExt.decRules (L.Ind.IWGrow.ext hg1) hys'e) (erRdOK m1).lt
          rw [← l1p, ← l2p] at *
          obtain ⟨b2, hb2, hr2, hS2, hg2, hP2⟩ := ih m1 m' a po pl qo ql co cl fuel (o1 + 11) (l1 - 1)
            (o2 + 11) (l2 - 1) x ps qs cs _ _ h hS1 (hC.grow hg1) hL hP1 hx2 hy2
          exact ⟨b2, hb2, hr2, hS2, hg1.trans hg2, hP2⟩)
        (fun h0 => by
          rw [ite_eq_left h0] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          exact ⟨rfl, hS1, hg1, hP1⟩)
      exact ⟨b, hb, hr, q1, q2, q3⟩
    · simp (config := { decide := true }) only [hbB, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hd : ¬ (({ x1' with rhs := default } : IRecRule) = { y1' with rhs := default }) := by
        intro e
        apply hbB
        rw [hB]; exact decide_eq_true e
      have hcond : (({ x1' with rhs := default } : IRecRule) == { y1' with rhs := default }) = false := by
        simpa using hd
      rw [hcond]
      exact ⟨false, rfl, rfl, hS, IWGrow.refl _, hP⟩

/-- **`canon_rules_eq` refines `canonRulesEq`.** -/
@[refines ConRon.Arena.canonRulesEq]
theorem canonRulesEq_refines (p : Prog) (hp : CanonProg p) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (po pl qo ql co cl fuel o1 l1 o2 l2 : Word) (ps qs cs : List NIdx)
    (xs ys : List IRecRule) :
    RefAM p "canon_rules_eq" [po, pl, qo, ql, co, cl, fuel, o1, l1, o2, l2]
      (fun m a => StageR vis fe m a ∧ CtxR m po pl qo ql co cl ps qs cs ∧ LitInj a ∧
        PoolSmall m ∧ decRules (erecP m) o1.toNat l1.toNat = some xs ∧
        decRules (erecP m) o2.toNat l2.toNat = some ys)
      (ConRon.Arena.canonRulesEq ps qs cs fuel.toNat xs ys) (CPostL dn vis fe decW0B) := by
  intro n s₀ a₀ ⟨hS, hC, hL, hP, hxs, hys⟩
  refine triple_post (canonRulesEq_spec p hp n s₀ po pl qo ql co cl fuel o1 l1 o2 l2) ?_
  rintro x s' ⟨hl, hx⟩
  obtain ⟨b, hb, hrb, hS', hg, hP'⟩ := cnCrW_ok n _ _ a₀ po pl qo ql co cl fuel o1 l1 o2 l2 _ ps qs cs xs ys
    hx hS hC hL hP hxs hys
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hb
  refine ⟨hl, hok, ?_⟩
  rw [hst, hres]
  exact ⟨⟨⟨hS', hg, decW0B_of' hrb⟩, hP'⟩, hL⟩

end L.Ind
