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

theorem recAt_of_post {m m1 : Mem} {r : List Word} {a b : Word} (h : RecPost m m1 r [a, b])
    (hI : IWOK m) : RecAt m1 (r.headD 0) a b := by
  obtain ⟨hq, hK, hroom, htop, hget⟩ := h
  have hq' : (r.headD 0).toNat = iwTop m := by rw [hq]; rfl
  refine ⟨by rw [hq']; simp at htop; omega, ?_, ?_⟩
  · have := hget 0 (by simp); simp only [iwA, hq']; simpa using this
  · have := hget 1 (by simp); simp only [iwA, hq']; simpa using this

def natEqList2W (p : Prog) (n : Nat) (m : Mem) (a1 b1 a2 b2 : Word) : Option (List Word × Mem) :=
  bW (callW p n "rec2" [a1, b1] m) fun r1 m1 =>
  bW (callW p n "rec2" [a2, b2] m1) fun r2 m2 =>
  bW (callW p n "iw_alloc" [2] m2) fun rq mq =>
  some ([rq.headD 0, 2], ((mq.set64 IW (rq.headD 0) (r1.headD 0)).set64 IW (rq.headD 0 + 1) (r2.headD 0)))

theorem natEqList2_specW (p : Prog) (hp : p.lookup "nat_eq_list2" = some natEqList2) (n : Nat) (s₀ : St)
    (a1 b1 a2 b2 : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nat_eq_list2" [a1, b1, a2, b2]
    ⦃fun r s' => LocEq s' s₀ ∧ natEqList2W p n s₀.mem a1 b1 a2 b2 = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, natEqList2]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "rec2", callW_spec p n "iw_alloc"] <;>
    finish (gen := 20) [natEqList2W, bW]

theorem natEqList2_ref (hN : NatEqProg p) (a1 b1 a2 b2 : Word) :
    CallRef p "nat_eq_list2" [a1, b1, a2, b2] (fun m s => StageR dn vis fe m s ∧ H a1 ∧ H b1 ∧ H a2 ∧ H b2)
      (pure [(decE a1, decE b1), (decE a2, decE b2)] : AM (List (EIdx × EIdx))) (KeepPost dn vis fe decEqRL) := by
  refine CallRef.of_succ fun k m s r m' ⟨hS, ha1, hb1, ha2, hb2⟩ hc => ?_
  have hw := callW_model (M := fun mm => natEqList2W p k mm a1 b1 a2 b2) (natEqList2_specW p hN.lNatEqList2 k · a1 b1 a2 b2) hc
  unfold natEqList2W at hw
  cases h1 : callW p k "rec2" [a1, b1] m with
  | none => rw [h1] at hw; simp at hw
  | some q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, bW_some] at hw
  have hR1 := rec2_fref p hN.lIwAlloc hN.lRec2 a1 b1 k m r1 m1 hS.2 h1
  have hK1 := hR1.2.1
  have hS1 := hK1.stage hS
  have rec1 : RecAt m1 (r1.headD 0) a1 b1 := recAt_of_post hR1 hS.2
  cases h2 : callW p k "rec2" [a2, b2] m1 with
  | none => rw [h2] at hw; simp at hw
  | some q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, bW_some] at hw
  have hR2 := rec2_fref p hN.lIwAlloc hN.lRec2 a2 b2 k m1 r2 m2 hS1.2 h2
  have hK2 := hR2.2.1
  have hS2 := hK2.stage hS1
  have rec2 : RecAt m2 (r2.headD 0) a2 b2 := recAt_of_post hR2 hS1.2
  cases hq : callW p k "iw_alloc" [2] m2 with
  | none => rw [hq] at hw; simp at hw
  | some qq =>
  obtain ⟨rq, mq⟩ := qq
  rw [hq, bW_some] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨hr, hm⟩ := hw
  have hrec : ∀ (j : Nat) (hj : j < [r1.headD 0, r2.headD 0].length), ∃ x y : Word, RecAt m2 ([r1.headD 0, r2.headD 0][j]) x y ∧ x.toNat < 2 ^ 32 ∧ y.toNat < 2 ^ 32 ∧ [(decE a1, decE b1), (decE a2, decE b2)][j]'(by simpa using hj) = (decE x, decE y) := by
    intro j hj
    simp only [List.length_cons, List.length_nil] at hj
    match j, hj with
    | 0, _ => exact ⟨a1, b1, (rec1.grow (hK2.1)), ha1, hb1, rfl⟩
    | 1, _ => exact ⟨a2, b2, rec2, ha2, hb2, rfl⟩
  have hall := emit_eqL (dn := dn) (vis := vis) (fe := fe) hN.lIwAlloc (k := k) (m' := m') (r := r) (ws := [r1.headD 0, r2.headD 0]) (ps := [(decE a1, decE b1), (decE a2, decE b2)]) hS2 rfl rfl hrec hq hr.symm (by rw [← hm]; simp [wrIW, UInt64.add_assoc])
  exact ⟨_, s, rfl, hall.1, ((hK1.1).trans hK2.1).trans hall.2.1, hall.2.2⟩

def natEqList3W (p : Prog) (n : Nat) (m : Mem) (a1 b1 a2 b2 a3 b3 : Word) : Option (List Word × Mem) :=
  bW (callW p n "rec2" [a1, b1] m) fun r1 m1 =>
  bW (callW p n "rec2" [a2, b2] m1) fun r2 m2 =>
  bW (callW p n "rec2" [a3, b3] m2) fun r3 m3 =>
  bW (callW p n "iw_alloc" [3] m3) fun rq mq =>
  some ([rq.headD 0, 3], (((mq.set64 IW (rq.headD 0) (r1.headD 0)).set64 IW (rq.headD 0 + 1) (r2.headD 0)).set64 IW (rq.headD 0 + 2) (r3.headD 0)))

theorem natEqList3_specW (p : Prog) (hp : p.lookup "nat_eq_list3" = some natEqList3) (n : Nat) (s₀ : St)
    (a1 b1 a2 b2 a3 b3 : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nat_eq_list3" [a1, b1, a2, b2, a3, b3]
    ⦃fun r s' => LocEq s' s₀ ∧ natEqList3W p n s₀.mem a1 b1 a2 b2 a3 b3 = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, natEqList3]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "rec2", callW_spec p n "iw_alloc"] <;>
    finish (gen := 20) [natEqList3W, bW]

theorem natEqList3_ref (hN : NatEqProg p) (a1 b1 a2 b2 a3 b3 : Word) :
    CallRef p "nat_eq_list3" [a1, b1, a2, b2, a3, b3] (fun m s => StageR dn vis fe m s ∧ H a1 ∧ H b1 ∧ H a2 ∧ H b2 ∧ H a3 ∧ H b3)
      (pure [(decE a1, decE b1), (decE a2, decE b2), (decE a3, decE b3)] : AM (List (EIdx × EIdx))) (KeepPost dn vis fe decEqRL) := by
  refine CallRef.of_succ fun k m s r m' ⟨hS, ha1, hb1, ha2, hb2, ha3, hb3⟩ hc => ?_
  have hw := callW_model (M := fun mm => natEqList3W p k mm a1 b1 a2 b2 a3 b3) (natEqList3_specW p hN.lNatEqList3 k · a1 b1 a2 b2 a3 b3) hc
  unfold natEqList3W at hw
  cases h1 : callW p k "rec2" [a1, b1] m with
  | none => rw [h1] at hw; simp at hw
  | some q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, bW_some] at hw
  have hR1 := rec2_fref p hN.lIwAlloc hN.lRec2 a1 b1 k m r1 m1 hS.2 h1
  have hK1 := hR1.2.1
  have hS1 := hK1.stage hS
  have rec1 : RecAt m1 (r1.headD 0) a1 b1 := recAt_of_post hR1 hS.2
  cases h2 : callW p k "rec2" [a2, b2] m1 with
  | none => rw [h2] at hw; simp at hw
  | some q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, bW_some] at hw
  have hR2 := rec2_fref p hN.lIwAlloc hN.lRec2 a2 b2 k m1 r2 m2 hS1.2 h2
  have hK2 := hR2.2.1
  have hS2 := hK2.stage hS1
  have rec2 : RecAt m2 (r2.headD 0) a2 b2 := recAt_of_post hR2 hS1.2
  cases h3 : callW p k "rec2" [a3, b3] m2 with
  | none => rw [h3] at hw; simp at hw
  | some q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, bW_some] at hw
  have hR3 := rec2_fref p hN.lIwAlloc hN.lRec2 a3 b3 k m2 r3 m3 hS2.2 h3
  have hK3 := hR3.2.1
  have hS3 := hK3.stage hS2
  have rec3 : RecAt m3 (r3.headD 0) a3 b3 := recAt_of_post hR3 hS2.2
  cases hq : callW p k "iw_alloc" [3] m3 with
  | none => rw [hq] at hw; simp at hw
  | some qq =>
  obtain ⟨rq, mq⟩ := qq
  rw [hq, bW_some] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨hr, hm⟩ := hw
  have hrec : ∀ (j : Nat) (hj : j < [r1.headD 0, r2.headD 0, r3.headD 0].length), ∃ x y : Word, RecAt m3 ([r1.headD 0, r2.headD 0, r3.headD 0][j]) x y ∧ x.toNat < 2 ^ 32 ∧ y.toNat < 2 ^ 32 ∧ [(decE a1, decE b1), (decE a2, decE b2), (decE a3, decE b3)][j]'(by simpa using hj) = (decE x, decE y) := by
    intro j hj
    simp only [List.length_cons, List.length_nil] at hj
    match j, hj with
    | 0, _ => exact ⟨a1, b1, (rec1.grow ((hK2.1).trans hK3.1)), ha1, hb1, rfl⟩
    | 1, _ => exact ⟨a2, b2, (rec2.grow (hK3.1)), ha2, hb2, rfl⟩
    | 2, _ => exact ⟨a3, b3, rec3, ha3, hb3, rfl⟩
  have hall := emit_eqL (dn := dn) (vis := vis) (fe := fe) hN.lIwAlloc (k := k) (m' := m') (r := r) (ws := [r1.headD 0, r2.headD 0, r3.headD 0]) (ps := [(decE a1, decE b1), (decE a2, decE b2), (decE a3, decE b3)]) hS3 rfl rfl hrec hq hr.symm (by rw [← hm]; simp [wrIW, UInt64.add_assoc])
  exact ⟨_, s, rfl, hall.1, (((hK1.1).trans hK2.1).trans hK3.1).trans hall.2.1, hall.2.2⟩

def natEqList4W (p : Prog) (n : Nat) (m : Mem) (a1 b1 a2 b2 a3 b3 a4 b4 : Word) : Option (List Word × Mem) :=
  bW (callW p n "rec2" [a1, b1] m) fun r1 m1 =>
  bW (callW p n "rec2" [a2, b2] m1) fun r2 m2 =>
  bW (callW p n "rec2" [a3, b3] m2) fun r3 m3 =>
  bW (callW p n "rec2" [a4, b4] m3) fun r4 m4 =>
  bW (callW p n "iw_alloc" [4] m4) fun rq mq =>
  some ([rq.headD 0, 4], ((((mq.set64 IW (rq.headD 0) (r1.headD 0)).set64 IW (rq.headD 0 + 1) (r2.headD 0)).set64 IW (rq.headD 0 + 2) (r3.headD 0)).set64 IW (rq.headD 0 + 3) (r4.headD 0)))

theorem natEqList4_specW (p : Prog) (hp : p.lookup "nat_eq_list4" = some natEqList4) (n : Nat) (s₀ : St)
    (a1 b1 a2 b2 a3 b3 a4 b4 : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nat_eq_list4" [a1, b1, a2, b2, a3, b3, a4, b4]
    ⦃fun r s' => LocEq s' s₀ ∧ natEqList4W p n s₀.mem a1 b1 a2 b2 a3 b3 a4 b4 = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, natEqList4]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "rec2", callW_spec p n "iw_alloc"] <;>
    finish (gen := 20) [natEqList4W, bW]

theorem natEqList4_ref (hN : NatEqProg p) (a1 b1 a2 b2 a3 b3 a4 b4 : Word) :
    CallRef p "nat_eq_list4" [a1, b1, a2, b2, a3, b3, a4, b4] (fun m s => StageR dn vis fe m s ∧ H a1 ∧ H b1 ∧ H a2 ∧ H b2 ∧ H a3 ∧ H b3 ∧ H a4 ∧ H b4)
      (pure [(decE a1, decE b1), (decE a2, decE b2), (decE a3, decE b3), (decE a4, decE b4)] : AM (List (EIdx × EIdx))) (KeepPost dn vis fe decEqRL) := by
  refine CallRef.of_succ fun k m s r m' ⟨hS, ha1, hb1, ha2, hb2, ha3, hb3, ha4, hb4⟩ hc => ?_
  have hw := callW_model (M := fun mm => natEqList4W p k mm a1 b1 a2 b2 a3 b3 a4 b4) (natEqList4_specW p hN.lNatEqList4 k · a1 b1 a2 b2 a3 b3 a4 b4) hc
  unfold natEqList4W at hw
  cases h1 : callW p k "rec2" [a1, b1] m with
  | none => rw [h1] at hw; simp at hw
  | some q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, bW_some] at hw
  have hR1 := rec2_fref p hN.lIwAlloc hN.lRec2 a1 b1 k m r1 m1 hS.2 h1
  have hK1 := hR1.2.1
  have hS1 := hK1.stage hS
  have rec1 : RecAt m1 (r1.headD 0) a1 b1 := recAt_of_post hR1 hS.2
  cases h2 : callW p k "rec2" [a2, b2] m1 with
  | none => rw [h2] at hw; simp at hw
  | some q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, bW_some] at hw
  have hR2 := rec2_fref p hN.lIwAlloc hN.lRec2 a2 b2 k m1 r2 m2 hS1.2 h2
  have hK2 := hR2.2.1
  have hS2 := hK2.stage hS1
  have rec2 : RecAt m2 (r2.headD 0) a2 b2 := recAt_of_post hR2 hS1.2
  cases h3 : callW p k "rec2" [a3, b3] m2 with
  | none => rw [h3] at hw; simp at hw
  | some q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, bW_some] at hw
  have hR3 := rec2_fref p hN.lIwAlloc hN.lRec2 a3 b3 k m2 r3 m3 hS2.2 h3
  have hK3 := hR3.2.1
  have hS3 := hK3.stage hS2
  have rec3 : RecAt m3 (r3.headD 0) a3 b3 := recAt_of_post hR3 hS2.2
  cases h4 : callW p k "rec2" [a4, b4] m3 with
  | none => rw [h4] at hw; simp at hw
  | some q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [h4, bW_some] at hw
  have hR4 := rec2_fref p hN.lIwAlloc hN.lRec2 a4 b4 k m3 r4 m4 hS3.2 h4
  have hK4 := hR4.2.1
  have hS4 := hK4.stage hS3
  have rec4 : RecAt m4 (r4.headD 0) a4 b4 := recAt_of_post hR4 hS3.2
  cases hq : callW p k "iw_alloc" [4] m4 with
  | none => rw [hq] at hw; simp at hw
  | some qq =>
  obtain ⟨rq, mq⟩ := qq
  rw [hq, bW_some] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨hr, hm⟩ := hw
  have hrec : ∀ (j : Nat) (hj : j < [r1.headD 0, r2.headD 0, r3.headD 0, r4.headD 0].length), ∃ x y : Word, RecAt m4 ([r1.headD 0, r2.headD 0, r3.headD 0, r4.headD 0][j]) x y ∧ x.toNat < 2 ^ 32 ∧ y.toNat < 2 ^ 32 ∧ [(decE a1, decE b1), (decE a2, decE b2), (decE a3, decE b3), (decE a4, decE b4)][j]'(by simpa using hj) = (decE x, decE y) := by
    intro j hj
    simp only [List.length_cons, List.length_nil] at hj
    match j, hj with
    | 0, _ => exact ⟨a1, b1, (rec1.grow (((hK2.1).trans hK3.1).trans hK4.1)), ha1, hb1, rfl⟩
    | 1, _ => exact ⟨a2, b2, (rec2.grow ((hK3.1).trans hK4.1)), ha2, hb2, rfl⟩
    | 2, _ => exact ⟨a3, b3, (rec3.grow (hK4.1)), ha3, hb3, rfl⟩
    | 3, _ => exact ⟨a4, b4, rec4, ha4, hb4, rfl⟩
  have hall := emit_eqL (dn := dn) (vis := vis) (fe := fe) hN.lIwAlloc (k := k) (m' := m') (r := r) (ws := [r1.headD 0, r2.headD 0, r3.headD 0, r4.headD 0]) (ps := [(decE a1, decE b1), (decE a2, decE b2), (decE a3, decE b3), (decE a4, decE b4)]) hS4 rfl rfl hrec hq hr.symm (by rw [← hm]; simp [wrIW, UInt64.add_assoc])
  exact ⟨_, s, rfl, hall.1, ((((hK1.1).trans hK2.1).trans hK3.1).trans hK4.1).trans hall.2.1, hall.2.2⟩

end eq

end L.Ind
