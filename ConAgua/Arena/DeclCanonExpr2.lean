import ConAgua.Arena.DeclCanonExpr
import ConAgua.Census.Attr

/-!
# The canonical expression comparison, relational lemma (lane `decls3`, helper `decls3-canon`)
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem cnGetD1' (r : List Word) : r.getD 1 0 = r.tail.headD 0 := by
  rcases r with _ | ⟨x, _ | ⟨y, z⟩⟩ <;> rfl
theorem getD2' (r : List Word) : r.getD 2 0 = r.tail.tail.headD 0 := by
  rcases r with _ | ⟨x, _ | ⟨y, _ | ⟨z, w⟩⟩⟩ <;> rfl
theorem getD3' (r : List Word) : r.getD 3 0 = r.tail.tail.tail.headD 0 := by
  rcases r with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, v⟩⟩⟩⟩ <;> rfl

theorem andThen_ok' {A B : AM Bool} {a : AState} {r r1 : Word} {b1 : Bool} {Q : Prop}
    (hA : A.run a = .ok (b1, a)) (hr1 : r1 = if b1 then 1 else 0)
    (hB : r1 ≠ 0 → ∃ b2, B.run a = .ok (b2, a) ∧ r = (if b2 then 1 else 0) ∧ Q)
    (h0 : r1 = 0 → r = 0 ∧ Q) :
    ∃ b, (do let x ← A; if x = true then B else pure false : AM Bool).run a = .ok (b, a) ∧
      r = (if b then 1 else 0) ∧ Q := by
  cases b1
  · obtain ⟨hr, hQ⟩ := h0 (by simpa using hr1)
    refine ⟨false, ?_, by simp [hr], hQ⟩
    simp [StateT.run_bind, hA, exc_ok_bind']; rfl
  · obtain ⟨b2, hb2, hr, hQ⟩ := hB (by simp [hr1])
    refine ⟨b2, ?_, hr, hQ⟩
    simp [StateT.run_bind, hA, exc_ok_bind', hb2]

/-- Literals are hash-consed: two handles viewing the same literal are the same handle. -/
def LitInj (a : AState) : Prop :=
  ∀ (x y : EIdx) (l : ConLeche.Literal), a.store.view x = some (.lit l) →
    a.store.view y = some (.lit l) → x = y

theorem ceW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (po pl qo ql co cl fuel x y r : Word) (ps qs cs : List NIdx),
    ceW n m po pl qo ql co cl fuel x y = some (r, m') → StageR dn vis fe m a →
    CtxR m po pl qo ql co cl ps qs cs → LitInj a → PoolSmall m → x.toNat < 2 ^ 32 →
    y.toNat < 2 ^ 32 →
    ∃ b, (ConRon.Arena.canonExprEq ps qs cs fuel.toNat (decE x) (decE y)).run a = .ok (b, a) ∧
      r = (if b then 1 else 0) ∧ StageR dn vis fe m' a ∧ IWGrow m m' ∧ PoolSmall m' := by
  induction n with
  | zero => intro m m' a po pl qo ql co cl fuel x y r ps qs cs h; simp [ceW] at h
  | succ n ih =>
    intro m m' a po pl qo ql co cl fuel x y r ps qs cs h hS hC hL hP hx hy
    rw [ceW_succ] at h
    have hf : ¬ fuel = 0 := fun hf => by rw [ite_eq_left hf] at h; simp at h
    rw [ite_eq_right hf, ceK0_def] at h
    by_cases hne : eViewW m x = [] ∨ eViewW m y = []
    · rw [ite_eq_left hne] at h; simp at h
    rw [ite_eq_right hne] at h
    rw [not_or] at hne
    obtain ⟨vx, hvx, hrx⟩ := eViewW_ok m a hS.1.arena.1 x hne.1
    obtain ⟨vy, hvy, hry⟩ := eViewW_ok m a hS.1.arena.1 y hne.2
    have hfuel : fuel.toNat = (fuel - 1).toNat + 1 := toNat_pred hf
    rw [hfuel, ConRon.Arena.canonExprEq.eq_2, StateT.run_bind, view_run _ _ _ hvx, exc_ok_bind',
      StateT.run_bind, view_run _ _ _ hvy, exc_ok_bind']
    generalize eViewW m x = ru at *
    generalize eViewW m y = rv at *
    cases vx <;> cases vy <;> simp only [ViewR, cnGetD1', getD2', getD3'] at hrx hry
    all_goals first
      | simp only [hrx.1, hry.1] at h
      | simp only [hrx.1, hry] at h
      | simp only [hrx, hry.1] at h
      | simp only [hrx, hry] at h
    all_goals first
      | (simp at h
         obtain ⟨hr, rfl⟩ := h
         exact ⟨false, rfl, hr.symm, hS, IWGrow.refl _, hP⟩)
      | skip
    case neg.bvar.bvar =>
      rename_i i j
      dsimp only
      have hh := h
      simp (config := { decide := true }) only [↓reduceIte,
        Option.some.injEq, Prod.mk.injEq] at hh
      obtain ⟨hr, rfl⟩ := hh
      refine ⟨i == j, rfl, ?_, hS, IWGrow.refl _, hP⟩
      rw [← hr]
      by_cases e : ru.tail.headD 0 = rv.tail.headD 0
      · have : i = j := by rw [← hrx.2, ← hry.2, e]
        rw [ite_eq_left e]; simp [this]
      · have : i ≠ j := fun e' => e (UInt64.toNat_inj.mp (by rw [hrx.2, hry.2, e']))
        rw [ite_eq_right e]; simp [this]
    case neg.fvar.fvar =>
      rename_i i1 t1 i2 t2
      dsimp only
      obtain ⟨e0, hi1, hl1, ht1⟩ := hrx
      obtain ⟨f0, hi2, hl2, ht2⟩ := hry
      simp (config := { decide := true }) only [ne_eq, ↓reduceIte] at h
      by_cases e : ru.tail.headD 0 = rv.tail.headD 0
      · rw [ite_eq_right (fun h => h e)] at h
        obtain ⟨b, hb, hr, hS', hg, hP'⟩ := ih m m' a po pl qo ql co cl (fuel - 1) _ _ r ps qs cs h
          hS hC hL hP hl1 hl2
        rw [ht1, ht2] at hb
        have hii : i1 = i2 := by rw [← hi1, ← hi2, e]
        refine ⟨b, ?_, hr, hS', hg, hP'⟩
        simp only [hii, beq_self_eq_true, ite_true]
        exact hb
      · rw [ite_eq_left e] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        have hii : (i1 == i2) = false := by
          have : i1 ≠ i2 := fun e' => e (UInt64.toNat_inj.mp (by rw [hi1, hi2, e']))
          simpa using this
        simp only [hii]
        exact ⟨false, rfl, rfl, hS, IWGrow.refl _, hP⟩
    case neg.sort.sort =>
      rename_i u1 u2
      dsimp only
      obtain ⟨e0, hl1, hu1⟩ := hrx
      obtain ⟨f0, hl2, hu2⟩ := hry
      cases hc : cnClW n m po pl qo ql co cl (fuel - 1) (ru.tail.headD 0) (rv.tail.headD 0) with
      | none => rw [hc] at h; simp [ceKL] at h
      | some r1 =>
      rw [hc, ceKL_some] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨b, hb, hrb⟩ := clW_ok n m a po pl qo ql co cl (fuel - 1) _ _ r1 ps qs cs hc
        hS.1.arena.1 hC hl1 hl2
      rw [hu1, hu2] at hb
      exact ⟨b, hb, hrb, hS, IWGrow.refl _, hP⟩
    case neg.const.const =>
      rename_i n1 us1 n2 us2
      dsimp only
      obtain ⟨e0, hw1, hn1, hl1, hus1⟩ := hrx
      obtain ⟨f0, hw2, hn2, hl2, hus2⟩ := hry
      simp (config := { decide := true }) only [ne_eq, ↓reduceIte] at h
      by_cases e : ru.tail.headD 0 = rv.tail.headD 0
      · rw [ite_eq_right (fun h => h e)] at h
        cases hc : lsEqW n m po pl qo ql co cl (fuel - 1) (ru.tail.tail.headD 0)
            (rv.tail.tail.headD 0) with
        | none => rw [hc] at h; simp [ceKS] at h
        | some x1 =>
        obtain ⟨r1, m1⟩ := x1
        rw [hc, ceKS_some] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        obtain ⟨b, hb, hrb, hS', hg, hP'⟩ := lsEqW_ok n hc hS hC hl1 hl2 hP
        rw [hus1, hus2] at hb
        have hnn : (n1 == n2) = true := by rw [← hn1, ← hn2, e]; exact beq_self_eq_true _
        refine ⟨b, ?_, hrb, hS', hg, hP'⟩
        simp only [hnn, ite_true]
        exact hb
      · rw [ite_eq_left e] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        have hnn : (n1 == n2) = false := by
          rw [← hn1, ← hn2, decI_beq _ _ hw1 hw2]
          exact decide_eq_false e
        simp only [hnn]
        exact ⟨false, rfl, rfl, hS, IWGrow.refl _, hP⟩
    case neg.app.app | neg.lam.lam | neg.forallE.forallE =>
      rename_i f1 x1 f2 x2
      dsimp only
      obtain ⟨e0, hw1, hf1, hw1', hx1⟩ := hrx
      obtain ⟨f0, hw2, hf2, hw2', hx2⟩ := hry
      simp (config := { decide := true }) only [↓reduceIte] at h
      cases hc : ceW n m po pl qo ql co cl (fuel - 1) (ru.tail.headD 0) (rv.tail.headD 0) with
      | none => rw [hc] at h; simp [ceK1] at h
      | some xx =>
      obtain ⟨r1, m1⟩ := xx
      rw [hc, ceK1_some] at h
      obtain ⟨b1, hb1, hr1, hS1, hg1, hP1⟩ := ih m m1 a po pl qo ql co cl (fuel - 1) _ _ r1 ps qs cs hc
        hS hC hL hP hw1 hw2
      rw [hf1, hf2] at hb1
      obtain ⟨b, hb, hr, hq1, hq2, hq3⟩ := andThen_ok' (Q := StageR dn vis fe m' a ∧ IWGrow m m' ∧ PoolSmall m')
        hb1 hr1
        (fun hne => by
          rw [ite_eq_right hne] at h
          obtain ⟨b2, hb2, hr2, hS2, hg2, hP2⟩ := ih m1 m' a po pl qo ql co cl (fuel - 1) _ _ r ps qs cs h
            hS1 (hC.grow hg1) hL hP1 hw1' hw2'
          rw [hx1, hx2] at hb2
          exact ⟨b2, hb2, hr2, hS2, hg1.trans hg2, hP2⟩)
        (fun h0 => by
          rw [ite_eq_left h0] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          exact ⟨rfl, hS1, hg1, hP1⟩)
      exact ⟨b, hb, hr, hq1, hq2, hq3⟩
    case neg.letE.letE =>
      rename_i t1 v1 b1 t2 v2 b2
      dsimp only
      obtain ⟨e0, hw1, ht1, hw1', hv1, hw1'', hb1⟩ := hrx
      obtain ⟨f0, hw2, ht2, hw2', hv2, hw2'', hb2⟩ := hry
      simp (config := { decide := true }) only [↓reduceIte] at h
      cases hc : ceW n m po pl qo ql co cl (fuel - 1) (ru.tail.headD 0) (rv.tail.headD 0) with
      | none => rw [hc] at h; simp [ceK2] at h
      | some xx =>
      obtain ⟨r1, m1⟩ := xx
      rw [hc, ceK2_some] at h
      obtain ⟨c1, hc1, hr1, hS1, hg1, hP1⟩ := ih m m1 a po pl qo ql co cl (fuel - 1) _ _ r1 ps qs cs hc
        hS hC hL hP hw1 hw2
      rw [ht1, ht2] at hc1
      obtain ⟨b, hb, hr, hq1, hq2, hq3⟩ := andThen_ok' (Q := StageR dn vis fe m' a ∧ IWGrow m m' ∧ PoolSmall m')
        hc1 hr1
        (fun hne => by
          rw [ite_eq_right hne] at h
          cases hd : ceW n m1 po pl qo ql co cl (fuel - 1) (ru.tail.tail.headD 0)
              (rv.tail.tail.headD 0) with
          | none => rw [hd] at h; simp [ceK3] at h
          | some yy =>
          obtain ⟨r2, m2⟩ := yy
          rw [hd, ceK3_some] at h
          obtain ⟨c2, hc2, hr2, hS2, hg2, hP2⟩ := ih m1 m2 a po pl qo ql co cl (fuel - 1) _ _ r2 ps qs cs hd
            hS1 (hC.grow hg1) hL hP1 hw1' hw2'
          rw [hv1, hv2] at hc2
          obtain ⟨b3, hb3, hr3, q1, q2, q3⟩ := andThen_ok' (Q := StageR dn vis fe m' a ∧ IWGrow m m' ∧ PoolSmall m')
            hc2 hr2
            (fun hne2 => by
              rw [ite_eq_right hne2] at h
              obtain ⟨c3, hc3, hr3, hS3, hg3, hP3⟩ := ih m2 m' a po pl qo ql co cl (fuel - 1) _ _ r ps qs cs h
                hS2 ((hC.grow hg1).grow hg2) hL hP2 hw1'' hw2''
              rw [hb1, hb2] at hc3
              exact ⟨c3, hc3, hr3, hS3, (hg1.trans hg2).trans hg3, hP3⟩)
            (fun h0 => by
              rw [ite_eq_left h0] at h
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
              exact ⟨rfl, hS2, hg1.trans hg2, hP2⟩)
          exact ⟨b3, hb3, hr3, q1, q2, q3⟩)
        (fun h0 => by
          rw [ite_eq_left h0] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          exact ⟨rfl, hS1, hg1, hP1⟩)
      exact ⟨b, hb, hr, hq1, hq2, hq3⟩
    case neg.lit.lit =>
      rename_i l1 l2
      dsimp only
      simp (config := { decide := true }) only [↓reduceIte] at h
      obtain ⟨hh, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      refine ⟨l1 == l2, rfl, ?_, hS, IWGrow.refl _, hP⟩
      rw [← hh]
      by_cases e : x = y
      · subst e
        have : l1 = l2 := by
          rw [hvx] at hvy; exact ENodeView.lit.inj (Option.some.inj hvy)
        simp [this]
      · have : l1 ≠ l2 := fun e' => e (decI_inj hx hy (by
          have := hL _ _ l1 hvx (by rw [e']; exact hvy)
          exact this))
        simp [e, this]
    case neg.proj.proj =>
      rename_i s1 i1 e1 s2 i2 e2
      dsimp only
      obtain ⟨e0, hw1, hs1, hi1, hw1', he1⟩ := hrx
      obtain ⟨f0, hw2, hs2, hi2, hw2', he2⟩ := hry
      simp (config := { decide := true }) only [ne_eq, ↓reduceIte] at h
      by_cases e : ru.tail.headD 0 ≠ rv.tail.headD 0 ∨ ru.tail.tail.headD 0 ≠ rv.tail.tail.headD 0
      · rw [ite_eq_left e] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        have hnn : (s1 == s2 && i1 == i2) = false := by
          rcases e with e | e
          · have : (s1 == s2) = false := by
              rw [← hs1, ← hs2, decI_beq _ _ hw1 hw2]; exact decide_eq_false (fun h' => e h')
            simp [this]
          · have : (i1 == i2) = false := by
              have : i1 ≠ i2 := fun e' => e (UInt64.toNat_inj.mp (by rw [hi1, hi2, e']))
              simpa using this
            simp [this]
        simp only [hnn]
        exact ⟨false, rfl, rfl, hS, IWGrow.refl _, hP⟩
      · rw [ite_eq_right e] at h
        rw [not_or] at e
        have e : ru.tail.headD 0 = rv.tail.headD 0 ∧ ru.tail.tail.headD 0 = rv.tail.tail.headD 0 :=
          ⟨Classical.byContradiction e.1, Classical.byContradiction e.2⟩
        obtain ⟨b, hb, hr, hS', hg, hP'⟩ := ih m m' a po pl qo ql co cl (fuel - 1) _ _ r ps qs cs h
          hS hC hL hP hw1' hw2'
        rw [he1, he2] at hb
        have hnn : (s1 == s2 && i1 == i2) = true := by
          have h1 : s1 = s2 := by rw [← hs1, ← hs2, e.1]
          have h2 : i1 = i2 := by rw [← hi1, ← hi2, e.2]
          simp [h1, h2]
        refine ⟨b, ?_, hr, hS', hg, hP'⟩
        simp only [hnn, ite_true]
        exact hb

/-- The post of a comparison that leaves the twin state alone but may grow the pool, with the
literal hash-consing carried along. -/
def CPostL {α : Type} (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (dec : Mem → List Word → α → Prop) (m m' : Mem) (a : AState) (r : List Word) (x : α) : Prop :=
  CPost dn vis fe dec m m' a r x ∧ LitInj a

/-- **`canon_expr_eq` refines `canonExprEq`** (literals compared by handle, `LitInj`). -/
@[refines ConRon.Arena.canonExprEq]
theorem canonExprEq_refines (p : Prog) (hp : CanonProg p) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (po pl qo ql co cl fuel x y : Word) (ps qs cs : List NIdx) :
    RefAM p "canon_expr_eq" [po, pl, qo, ql, co, cl, fuel, x, y]
      (fun m a => StageR dn vis fe m a ∧ CtxR m po pl qo ql co cl ps qs cs ∧ LitInj a ∧
        PoolSmall m ∧ x.toNat < 2 ^ 32 ∧ y.toNat < 2 ^ 32)
      (ConRon.Arena.canonExprEq ps qs cs fuel.toNat (decE x) (decE y))
      (CPostL dn vis fe decW0B) := by
  intro n s₀ a₀ ⟨hS, hC, hL, hP, hx, hy⟩
  refine triple_post (canonExprEq_spec p hp n s₀ po pl qo ql co cl fuel x y) ?_
  rintro r s' ⟨hl, hr⟩
  obtain ⟨b, hb, hrb, hS', hg, hP'⟩ := ceW_ok n _ _ a₀ po pl qo ql co cl fuel x y _ ps qs cs hr hS hC hL hP hx hy
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hb
  refine ⟨hl, hok, ?_⟩
  rw [hst, hres]
  exact ⟨⟨⟨hS', hg, decW0B_of' hrb⟩, hP'⟩, hL⟩

end L.Ind
