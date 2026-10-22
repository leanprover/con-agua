import ConAgua.Arena.DeclNatTy

/-!
# The structural-`Nat` gate: the recurrence equations (lane `decls3`, helper `decls3-nat`)

`nat_ap1`, `nat_ap2`, the equation lists and `nat_op_equations`. A `List (EIdx × EIdx)` is an `IW`
slice of pointers to two-word records `[lhs, rhs]` (`EqL`).
-/

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The two-word record at `p` holds `a`, `b`, below the pool's top. -/
def RecAt (m : Mem) (p a b : Word) : Prop :=
  p.toNat + 2 ≤ iwTop m ∧ (iwA m)[p.toNat]? = some a ∧ (iwA m)[p.toNat + 1]? = some b

theorem RecAt.grow {m m' : Mem} {p a b : Word} (h : RecAt m p a b) (hg : IWGrow m m') :
    RecAt m' p a b := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Nat.le_trans h1 hg.1, ?_, ?_⟩
  · simp only [iwA] at h2 ⊢; rw [hg.2.2.1 _ (by omega)]; exact h2
  · simp only [iwA] at h3 ⊢; rw [hg.2.2.1 _ (by omega)]; exact h3

/-- `List (EIdx × EIdx)` as the slice `(o, l)` of pointers to equation records. -/
def EqL (m : Mem) (o l : Nat) (ps : List (EIdx × EIdx)) : Prop :=
  o + l ≤ iwTop m ∧ l = ps.length ∧ ∀ (j : Nat) (hj : j < ps.length), ∃ p a b : Word,
    (iwA m)[o + j]? = some p ∧ RecAt m p a b ∧ a.toNat < 2 ^ 32 ∧ b.toNat < 2 ^ 32 ∧
      ps[j] = (decE a, decE b)

theorem EqL.grow {m m' : Mem} {o l : Nat} {ps : List (EIdx × EIdx)} (h : EqL m o l ps)
    (hg : IWGrow m m') : EqL m' o l ps := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Nat.le_trans h1 hg.1, h2, fun j hj => ?_⟩
  obtain ⟨p, a, b, hp, hr, ha, hb, he⟩ := h3 j hj
  refine ⟨p, a, b, ?_, hr.grow hg, ha, hb, he⟩
  simp only [iwA] at hp ⊢; rw [hg.2.2.1 _ (by omega)]; exact hp

/-- The post of a function returning an equation list `(o, l)`. -/
def decEqRL (m : Mem) (r : List Word) (ps : List (EIdx × EIdx)) : Prop :=
  EqL m (r.getD 0 0).toNat (r.getD 1 0).toNat ps

section eq
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

structure NatEqProg (p : Prog) : Prop extends NatTyProg p where
  lNatAp1 : p.lookup "nat_ap1" = some natAp1L
  lNatAp2 : p.lookup "nat_ap2" = some natAp2L
  lNatEqList2 : p.lookup "nat_eq_list2" = some natEqList2
  lNatEqList3 : p.lookup "nat_eq_list3" = some natEqList3
  lNatEqList4 : p.lookup "nat_eq_list4" = some natEqList4
  lNatEqPr : p.lookup "nat_eq_pr" = some natEqPr
  lNatEqUn : p.lookup "nat_eq_un" = some natEqUn
  lNatEqMu : p.lookup "nat_eq_mu" = some natEqMu
  lNatEqPo : p.lookup "nat_eq_po" = some natEqPo
  lNatEqBe : p.lookup "nat_eq_be" = some natEqBe
  lNatEqBl : p.lookup "nat_eq_bl" = some natEqBl
  lNatOpEquations : p.lookup "nat_op_equations" = some natOpEquationsL

/-! ### `nat_ap1`, `nat_ap2` -/

def natAp1W (p : Prog) (n : Nat) (m : Mem) (nm a : Word) : Option (List Word × Mem) :=
  bW (callW p n "const_e" [nm] m) fun r1 m1 =>
  bW (callW p n "mk_app" [r1.headD 0, a] m1) fun r2 m2 => some ([r2.headD 0], m2)

theorem natAp1_specW (p : Prog) (hp : p.lookup "nat_ap1" = some natAp1L) (n : Nat) (s₀ : St)
    (nm a : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nat_ap1" [nm, a]
    ⦃fun r s' => LocEq s' s₀ ∧ natAp1W p n s₀.mem nm a = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, natAp1L]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "const_e", callW_spec p n "mk_app"] <;>
    finish (gen := 20) [natAp1W, bW]

theorem natAp1_ref (hN : NatEqProg p) (nm a : Word) :
    CallRef p "nat_ap1" [nm, a] (fun m s => StageR dn vis fe m s ∧ H nm ∧ H a)
      (natAp1 (decI nm) (decE a)) (KeepPost dn vis fe decW0E) := by
  refine CallRef.of_succ fun k m s r m' ⟨hS, hn, ha⟩ hc => ?_
  have hw := callW_model (M := fun mm => natAp1W p k mm nm a) (natAp1_specW p hN.lNatAp1 k · nm a) hc
  unfold natAp1W at hw
  cases h1 : callW p k "const_e" [nm] m with
  | none => rw [h1] at hw; simp at hw
  | some q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, bW_some] at hw
  obtain ⟨x1, a1, hrun1, hS1, hg1, hx1l, hx1⟩ := constE_ref (dn := dn) (vis := vis) (fe := fe)
    hN.toMasterProg nm k m s r1 m1 ⟨hS, hn⟩ h1
  cases h2 : callW p k "mk_app" [r1.headD 0, a] m1 with
  | none => rw [h2] at hw; simp at hw
  | some q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, bW_some] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2l, hx2⟩ := mkApp_ref (dn := dn) (vis := vis) (fe := fe)
    hN.toMasterProg (r1.headD 0) a k m1 a1 r2 m2 hS1 h2
  refine ⟨x2, a2, ?_, hS2, hg1.trans hg2, hx2l, hx2⟩
  simp only [natAp1, StateT.run_bind, hrun1, exc_ok_bind', ← hx1]
  exact hrun2

def natAp2W (p : Prog) (n : Nat) (m : Mem) (nm a b : Word) : Option (List Word × Mem) :=
  bW (callW p n "nat_ap1" [nm, a] m) fun r1 m1 =>
  bW (callW p n "mk_app" [r1.headD 0, b] m1) fun r2 m2 => some ([r2.headD 0], m2)

theorem natAp2_specW (p : Prog) (hp : p.lookup "nat_ap2" = some natAp2L) (n : Nat) (s₀ : St)
    (nm a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nat_ap2" [nm, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ natAp2W p n s₀.mem nm a b = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, natAp2L]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "nat_ap1", callW_spec p n "mk_app"] <;>
    finish (gen := 20) [natAp2W, bW]

theorem natAp2_ref (hN : NatEqProg p) (nm a b : Word) :
    CallRef p "nat_ap2" [nm, a, b] (fun m s => StageR dn vis fe m s ∧ H nm ∧ H a ∧ H b)
      (natAp2 (decI nm) (decE a) (decE b)) (KeepPost dn vis fe decW0E) := by
  refine CallRef.of_succ fun k m s r m' ⟨hS, hn, ha, hb⟩ hc => ?_
  have hw := callW_model (M := fun mm => natAp2W p k mm nm a b) (natAp2_specW p hN.lNatAp2 k · nm a b) hc
  unfold natAp2W at hw
  cases h1 : callW p k "nat_ap1" [nm, a] m with
  | none => rw [h1] at hw; simp at hw
  | some q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, bW_some] at hw
  obtain ⟨x1, a1, hrun1, hS1, hg1, hx1l, hx1⟩ := natAp1_ref (dn := dn) (vis := vis) (fe := fe) hN nm a
    k m s r1 m1 ⟨hS, hn, ha⟩ h1
  cases h2 : callW p k "mk_app" [r1.headD 0, b] m1 with
  | none => rw [h2] at hw; simp at hw
  | some q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, bW_some] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2l, hx2⟩ := mkApp_ref (dn := dn) (vis := vis) (fe := fe)
    hN.toMasterProg (r1.headD 0) b k m1 a1 r2 m2 hS1 h2
  refine ⟨x2, a2, ?_, hS2, hg1.trans hg2, hx2l, hx2⟩
  simp only [natAp2, StateT.run_bind, hrun1, exc_ok_bind', ← hx1]
  exact hrun2

@[refines ConRon.Arena.natAp1]
theorem natAp1_refines (hN : NatEqProg p) (nm a : Word) :
    RefAM p "nat_ap1" [nm, a] (fun m s => StageR dn vis fe m s ∧ H nm ∧ H a)
      (natAp1 (decI nm) (decE a)) (KeepPost dn vis fe decW0E) :=
  (natAp1_ref hN nm a).refAM

@[refines ConRon.Arena.natAp2]
theorem natAp2_refines (hN : NatEqProg p) (nm a b : Word) :
    RefAM p "nat_ap2" [nm, a, b] (fun m s => StageR dn vis fe m s ∧ H nm ∧ H a ∧ H b)
      (natAp2 (decI nm) (decE a) (decE b)) (KeepPost dn vis fe decW0E) :=
  (natAp2_ref hN nm a b).refAM

/-- Emitting an equation list: `ws` the record pointers, written into a fresh slice. -/
theorem emit_eqL {p : Prog} (hal : p.lookup "iw_alloc" = some iwAlloc) {k : Nat} {m mq m' : Mem}
    {a : AState} {rq r : List Word} {N : Word} {ws : List Word} {ps : List (EIdx × EIdx)}
    (hS : StageR dn vis fe m a) (hN : N.toNat = ws.length) (hlen : ps.length = ws.length)
    (hrec : ∀ (j : Nat) (hj : j < ws.length), ∃ x y : Word, RecAt m ws[j] x y ∧ x.toNat < 2 ^ 32 ∧
      y.toNat < 2 ^ 32 ∧ ps[j]'(by omega) = (decE x, decE y))
    (hq : callW p k "iw_alloc" [N] m = some (rq, mq)) (hr : r = [rq.headD 0, N])
    (hm : m' = wrIW mq (rq.headD 0) ws) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ decEqRL m' r ps := by
  obtain ⟨hq0, hmq, hKeep, hroom, htop⟩ := iwAlloc_fref p hal N k m rq mq hS.2 hq
  have hrec' := recPost_wr m ws N hN hS.2 (by simpa [iwTop, hN] using hroom)
  subst hmq; subst hr; rw [hq0]; rw [hq0] at hm; subst hm
  obtain ⟨hqq, hKp, hroom', htop', hget⟩ := hrec'
  have hq' : (rdW (m.arr64 CTL) 200).toNat = iwTop m := rfl
  refine ⟨hKp.stage hS, hKp.1, ?_⟩
  simp only [decEqRL, EqL, List.getD_cons_zero, List.getD_cons_succ, hq', hN]
  refine ⟨by omega, hlen.symm, fun j hj => ?_⟩
  obtain ⟨x, y, hr', hx, hy, he⟩ := hrec j (by omega)
  refine ⟨ws[j]'(by omega), x, y, ?_, hr'.grow hKp.1, hx, hy, he⟩
  simp only [iwA]
  rw [hget j (by omega)]
  simp [List.getElem?_eq_getElem (show j < ws.length by omega)]

end eq

end L.Ind
