import ConAgua.Arena.DeclCanonConst

/-!
# `canon_rules_eq` (lane `decls3`, helper `decls3-canon`)
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

mutual
/-- **The model of `canon_rules_eq`**. -/
def cnCrW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | k + 1, m, po, pl, qo, ql, co, cl, fuel, o1, l1, o2, l2 =>
    if l1 = 0 ∧ l2 = 0 then some (1, m)
    else if l1 = 0 ∨ l2 = 0 then some (0, m)
    else crK0 k m po pl qo ql co cl fuel o1 l1 o2 l2
      (if ruleEqButRhsB (m.arr64 EREC) o1 o2 then 1 else 0)

/-- After `rule_eq_but_rhs`. -/
def crK0 (k : Nat) (m : Mem) (po pl qo ql co cl fuel o1 l1 o2 l2 e : Word) : Option (Word × Mem) :=
  if e = 0 then some (0, m)
  else cnCrK1 k po pl qo ql co cl fuel o1 l1 o2 l2
    (ceW k m po pl qo ql co cl fuel (rdW (m.arr64 EREC) (o1 + 8)) (rdW (m.arr64 EREC) (o2 + 8)))

/-- After `canon_expr_eq`. -/
def cnCrK1 (k : Nat) (po pl qo ql co cl fuel o1 l1 o2 l2 : Word) : Option (Word × Mem) →
    Option (Word × Mem)
  | none => none
  | some (e, m1) =>
    if e = 0 then some (0, m1)
    else cnCrW k m1 po pl qo ql co cl fuel (o1 + 11) (l1 - 1) (o2 + 11) (l2 - 1)
end

section arms
variable (k : Nat) (m m1 : Mem) (po pl qo ql co cl fuel o1 l1 o2 l2 e : Word)
theorem crW_succ : cnCrW (k + 1) m po pl qo ql co cl fuel o1 l1 o2 l2 =
    (if l1 = 0 ∧ l2 = 0 then some (1, m)
    else if l1 = 0 ∨ l2 = 0 then some (0, m)
    else crK0 k m po pl qo ql co cl fuel o1 l1 o2 l2
      (if ruleEqButRhsB (m.arr64 EREC) o1 o2 then 1 else 0)) := by rw [cnCrW]
theorem crK0_def : crK0 k m po pl qo ql co cl fuel o1 l1 o2 l2 e =
    (if e = 0 then some (0, m)
    else cnCrK1 k po pl qo ql co cl fuel o1 l1 o2 l2
      (ceW k m po pl qo ql co cl fuel (rdW (m.arr64 EREC) (o1 + 8)) (rdW (m.arr64 EREC) (o2 + 8)))) :=
  by rw [crK0]
theorem crK1_some : cnCrK1 k po pl qo ql co cl fuel o1 l1 o2 l2 (some (e, m1)) =
    (if e = 0 then some (0, m1)
    else cnCrW k m1 po pl qo ql co cl fuel (o1 + 11) (l1 - 1) (o2 + 11) (l2 - 1)) := by rw [cnCrK1]
end arms

grind_pattern [ind_grind] crW_succ => cnCrW (k + 1) m po pl qo ql co cl fuel o1 l1 o2 l2
grind_pattern [ind_grind] crK0_def => crK0 k m po pl qo ql co cl fuel o1 l1 o2 l2 e
grind_pattern [ind_grind] crK1_some => cnCrK1 k po pl qo ql co cl fuel o1 l1 o2 l2 (some (e, m1))

section specs6
variable (p : Prog) (hp : CanonProg p)
include hp

set_option maxHeartbeats 4000000 in
theorem canonRulesEq_spec (n : Nat) : ∀ (s₀ : St) (po pl qo ql co cl fuel o1 l1 o2 l2 : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "canon_rules_eq"
      [po, pl, qo, ql, co, cl, fuel, o1, l1, o2, l2]
    ⦃fun x s' => LocEq s' s₀ ∧ cnCrW n s₀.mem po pl qo ql co cl fuel o1 l1 o2 l2 = some (x.headD 0, s'.mem);
      ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ po pl qo ql co cl fuel o1 l1 o2 l2
    rw [invoke_eq _ (hp.get "canon_rules_eq")]; simp only [callFn, canonRulesEq]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ po pl qo ql co cl fuel o1 l1 o2 l2
    rw [invoke_eq _ (hp.get "canon_rules_eq")]
    simp only [callFn, canonRulesEq]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        ruleEqButRhs_spec p hp n, canonExprEq_spec p hp n, ih] <;>
      finish (gen := 20) [rdW_eq, init11_0, init11_1, init11_2, init11_3, init11_4, init11_5,
        init11_6, init11_7, init11_8, init11_9, init11_10]

end specs6


theorem decRules_length {a : Array Word} {o l : Nat} {xs : List IRecRule}
    (h : decRules a o l = some xs) : xs.length = l := by
  have := mapM_opt_length _ _ _ h
  simpa using this

theorem cnCrW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (po pl qo ql co cl fuel o1 l1 o2 l2 x : Word) (ps qs cs : List NIdx)
      (xs ys : List IRecRule),
    cnCrW k m po pl qo ql co cl fuel o1 l1 o2 l2 = some (x, m') → StageR dn vis fe m a →
    CtxR m po pl qo ql co cl ps qs cs → LitInj a → PoolSmall m →
    decRules (erecP m) o1.toNat l1.toNat = some xs → decRules (erecP m) o2.toNat l2.toNat = some ys →
    ∃ b, (ConRon.Arena.canonRulesEq ps qs cs fuel.toNat xs ys).run a = .ok (b, a) ∧
      x = (if b then 1 else 0) ∧ StageR dn vis fe m' a ∧ IWGrow m m' ∧ PoolSmall m' := by
  induction k with
  | zero => intro m m' a po pl qo ql co cl fuel o1 l1 o2 l2 x ps qs cs xs ys h; simp [cnCrW] at h
  | succ k ih =>
    intro m m' a po pl qo ql co cl fuel o1 l1 o2 l2 x ps qs cs xs ys h hS hC hL hP hxs hys
    rw [crW_succ] at h
    have lx := decRules_length hxs
    have ly := decRules_length hys
    by_cases h0 : l1 = 0 ∧ l2 = 0
    · rw [if_pos h0] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have e1 : xs = [] := List.length_eq_zero_iff.mp (by rw [lx, h0.1]; rfl)
      have e2 : ys = [] := List.length_eq_zero_iff.mp (by rw [ly, h0.2]; rfl)
      subst e1 e2
      exact ⟨true, by simp [ConRon.Arena.canonRulesEq]; rfl, rfl, hS, IWGrow.refl _, hP⟩
    rw [if_neg h0] at h
    by_cases h1 : l1 = 0 ∨ l2 = 0
    · rw [if_pos h1] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      refine ⟨false, ?_, rfl, hS, IWGrow.refl _, hP⟩
      rcases xs with _ | ⟨x1, xs'⟩ <;> rcases ys with _ | ⟨y1, ys'⟩
      · exfalso; apply h0
        refine ⟨UInt64.toNat_inj.mp (by simpa using lx.symm), UInt64.toNat_inj.mp (by simpa using ly.symm)⟩
      · simp [ConRon.Arena.canonRulesEq]; rfl
      · simp [ConRon.Arena.canonRulesEq]; rfl
      · exfalso
        rcases h1 with h1 | h1 <;> (subst h1; simp at lx ly)
    rw [if_neg h1] at h
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
    have hsz : (m.arr64 EREC).size < 2 ^ 64 := hS.2.2.2.2.1
    have hx1 := ArrExt.decRule (erecP_ext m) hx1e
    have hy1 := ArrExt.decRule (erecP_ext m) hy1e
    obtain ⟨w0, w1, w2, w3, w8, w9, w10, e0, e1, e2, e3, e8, e9, e10, h0', h8, c0, c1, c2, c8, c9, c10, hf, hb⟩ :=
      ruleFields (a := erA m) (q := o1) hsz hx1
    obtain ⟨v0, v1, v2, v3, v8, v9, v10, f0, f1, f2, f3, f8, f9, f10, g0', g8, d0, d1, d2, d8, d9, d10, hg, hb'⟩ :=
      ruleFields (a := erA m) (q := o2) hsz hy1
    have hB := ruleEqButRhsB_ok hsz hx1 hy1
    have o1e : (o1 + 11).toNat = o1.toNat + 11 := by rw [UInt64.toNat_add]; simp; omega
    have o2e : (o2 + 11).toNat = o2.toNat + 11 := by rw [UInt64.toNat_add]; simp; omega
    have l1p : (l1 - 1).toNat = xs''.length := by rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp [l1e]
    have l2p : (l2 - 1).toNat = ys''.length := by rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp [l2e]
    rw [crK0_def] at h
    rw [ConRon.Arena.canonRulesEq.eq_2]
    by_cases hbB : ruleEqButRhsB (m.arr64 EREC) o1 o2 = true
    · have hd : ({ x1' with rhs := default } : IRecRule) = { y1' with rhs := default } :=
        of_decide_eq_true (hB ▸ hbB)
      have hcond : (({ x1' with rhs := default } : IRecRule) == { y1' with rhs := default }) = true :=
        beq_iff_eq.mpr hd
      have hne : (if ruleEqButRhsB (m.arr64 EREC) o1 o2 = true then (1 : Word) else 0) ≠ 0 := by
        simp [hbB]
      rw [if_neg hne] at h
      simp only [erA] at e8 f8
      rw [e8, f8] at h
      cases hc : ceW k m po pl qo ql co cl fuel w8 v8 with
      | none => rw [hc] at h; simp [cnCrK1] at h
      | some xx =>
      obtain ⟨e1', m1⟩ := xx
      rw [hc, crK1_some] at h
      obtain ⟨b1, hb1, hr1, hS1, hg1, hP1⟩ := ceW_ok k m m1 a po pl qo ql co cl fuel w8 v8 e1' ps qs cs
        hc hS hC hL hP h8 g8
      rw [c8, d8] at *
      rw [if_pos hcond]
      obtain ⟨b, hb, hr, q1, q2, q3⟩ := andThen_ok' (Q := StageR dn vis fe m' a ∧ IWGrow m m' ∧ PoolSmall m')
        hb1 hr1
        (fun hne2 => by
          rw [if_neg hne2] at h
          have hx2 := ArrExt.decRules (IWGrow.erecPExtR hg1) hxs'e
          have hy2 := ArrExt.decRules (IWGrow.erecPExtR hg1) hys'e
          rw [← o1e, ← o2e, ← l1p, ← l2p] at *
          obtain ⟨b2, hb2, hr2, hS2, hg2, hP2⟩ := ih m1 m' a po pl qo ql co cl fuel (o1 + 11) (l1 - 1)
            (o2 + 11) (l2 - 1) x ps qs cs _ _ h hS1 (hC.grow hg1) hL hP1 hx2 hy2
          exact ⟨b2, hb2, hr2, hS2, hg1.trans hg2, hP2⟩)
        (fun h0 => by
          rw [if_pos h0] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
          exact ⟨rfl, hS1, hg1, hP1⟩)
      exact ⟨b, hb, hr, q1, q2, q3⟩
    · have hB0 : (if ruleEqButRhsB (m.arr64 EREC) o1 o2 = true then (1 : Word) else 0) = 0 := by
        simp [hbB]
      rw [if_pos hB0] at h
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
      (fun m a => StageR dn vis fe m a ∧ CtxR m po pl qo ql co cl ps qs cs ∧ LitInj a ∧
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
