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
  lNatCertify : p.lookup "certify_nat_eqs" = some certifyNatEqsL
  lNatOpEquations : p.lookup "nat_op_equations" = some natOpEquationsL

/-! ### `nat_ap1`, `nat_ap2` -/

def natAp1W (p : Prog) (n : Nat) (m : Mem) (nm a : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "const_e" [nm] m) fun r1 m1 =>
  ntBW (callW p n "mk_app" [r1.headD 0, a] m1) fun r2 m2 => some ([r2.headD 0], m2)

theorem natAp1_specW (p : Prog) (hp : p.lookup "nat_ap1" = some natAp1L) (n : Nat) (s₀ : St)
    (nm a : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nat_ap1" [nm, a]
    ⦃fun r s' => LocEq s' s₀ ∧ natAp1W p n s₀.mem nm a = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, natAp1L]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "const_e", callW_spec p n "mk_app"] <;>
    finish (gen := 20) [natAp1W, ntBW]

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
  ntBW (callW p n "nat_ap1" [nm, a] m) fun r1 m1 =>
  ntBW (callW p n "mk_app" [r1.headD 0, b] m1) fun r2 m2 => some ([r2.headD 0], m2)

theorem natAp2_specW (p : Prog) (hp : p.lookup "nat_ap2" = some natAp2L) (n : Nat) (s₀ : St)
    (nm a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nat_ap2" [nm, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ natAp2W p n s₀.mem nm a b = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, natAp2L]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "nat_ap1", callW_spec p n "mk_app"] <;>
    finish (gen := 20) [natAp2W, ntBW]

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
  ntBW (callW p n "rec2" [a1, b1] m) fun r1 m1 =>
  ntBW (callW p n "rec2" [a2, b2] m1) fun r2 m2 =>
  ntBW (callW p n "iw_alloc" [2] m2) fun rq mq =>
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
    finish (gen := 20) [natEqList2W, ntBW]

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
  ntBW (callW p n "rec2" [a1, b1] m) fun r1 m1 =>
  ntBW (callW p n "rec2" [a2, b2] m1) fun r2 m2 =>
  ntBW (callW p n "rec2" [a3, b3] m2) fun r3 m3 =>
  ntBW (callW p n "iw_alloc" [3] m3) fun rq mq =>
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
    finish (gen := 20) [natEqList3W, ntBW]

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
  ntBW (callW p n "rec2" [a1, b1] m) fun r1 m1 =>
  ntBW (callW p n "rec2" [a2, b2] m1) fun r2 m2 =>
  ntBW (callW p n "rec2" [a3, b3] m2) fun r3 m3 =>
  ntBW (callW p n "rec2" [a4, b4] m3) fun r4 m4 =>
  ntBW (callW p n "iw_alloc" [4] m4) fun rq mq =>
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
    finish (gen := 20) [natEqList4W, ntBW]

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

theorem eqL_retag {m : Mem} {rl : List Word} {xl : List (EIdx × EIdx)} {k : Nat}
    (h : decEqRL m rl xl) (hk : xl.length = k) :
    EqL m (rl.headD 0).toNat k xl := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [ntGetD0, ntGetD1] at h1 h2 h3
  exact ⟨by omega, hk.symm, h3⟩

def natEqPrT (c : NIdx) (z : EIdx) (x : EIdx) (sx : EIdx) : AM (List (EIdx × EIdx)) := do
  let l1 ← natAp1 c z
  let l2 ← natAp1 c sx
  pure [(l1, z), (l2, x)]

def natEqPrW (p : Prog) (n : Nat) (m : Mem) (c z x sx : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "nat_ap1" [c, z] m) fun r_l1 m_l1 =>
  ntBW (callW p n "nat_ap1" [c, sx] m_l1) fun r_l2 m_l2 =>
  ntBW (callW p n "nat_eq_list2" [r_l1.headD 0, z, r_l2.headD 0, x] m_l2) fun rl ml =>
  some ([rl.headD 0, 2], ml)

theorem natEqPr_specW (p : Prog) (hp : p.lookup "nat_eq_pr" = some natEqPr) (n : Nat) (s₀ : St)
    (c z x sx : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nat_eq_pr" [c, z, x, sx]
    ⦃fun r s' => LocEq s' s₀ ∧ natEqPrW p n s₀.mem c z x sx = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, natEqPr]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "nat_ap1", callW_spec p n "nat_ap2", callW_spec p n "nat_eq_list2"] <;>
    finish (gen := 20) (instances := 10000) [natEqPrW, ntBW]

theorem natEqPr_ref (hN : NatEqProg p) (c z x sx : Word) :
    CallRef p "nat_eq_pr" [c, z, x, sx] (fun m s => StageR dn vis fe m s ∧ H c ∧ H z ∧ H x ∧ H sx)
      (natEqPrT (decI c) (decE z) (decE x) (decE sx)) (KeepPost dn vis fe decEqRL) := by
  refine CallRef.of_succ fun k m s r m' ⟨hS, h_c, h_z, h_x, h_sx⟩ hc => ?_
  have hw := callW_model (M := fun mm => natEqPrW p k mm c z x sx) (natEqPr_specW p hN.lNatEqPr k · c z x sx) hc
  unfold natEqPrW at hw
  cases hc_l1 : callW p k "nat_ap1" [c, z] m with
  | none => rw [hc_l1] at hw; simp at hw
  | some q_l1 =>
  obtain ⟨r_l1, m_l1⟩ := q_l1
  rw [hc_l1, bW_some] at hw
  obtain ⟨x_l1, a_l1, hrun_l1, hS_l1, hg_l1, hl_l1, hx_l1⟩ := natAp1_ref (dn := dn) (vis := vis) (fe := fe) hN (c) (z) k m s r_l1 m_l1 ⟨hS, h_c, h_z⟩ hc_l1
  cases hc_l2 : callW p k "nat_ap1" [c, sx] m_l1 with
  | none => rw [hc_l2] at hw; simp at hw
  | some q_l2 =>
  obtain ⟨r_l2, m_l2⟩ := q_l2
  rw [hc_l2, bW_some] at hw
  obtain ⟨x_l2, a_l2, hrun_l2, hS_l2, hg_l2, hl_l2, hx_l2⟩ := natAp1_ref (dn := dn) (vis := vis) (fe := fe) hN (c) (sx) k m_l1 a_l1 r_l2 m_l2 ⟨hS_l1, h_c, h_sx⟩ hc_l2
  cases hcl : callW p k "nat_eq_list2" [r_l1.headD 0, z, r_l2.headD 0, x] m_l2 with
  | none => rw [hcl] at hw; simp at hw
  | some ql =>
  obtain ⟨rl, ml⟩ := ql
  rw [hcl, bW_some] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨hr, hm⟩ := hw
  obtain ⟨xl, al, hrunl, hSl, hgl, hdl⟩ := natEqList2_ref (dn := dn) (vis := vis) (fe := fe) hN (r_l1.headD 0) (z) (r_l2.headD 0) (x) k m_l2 a_l2 rl ml ⟨hS_l2, hl_l1, h_z, hl_l2, h_x⟩ hcl
  obtain ⟨hxl, hal⟩ := Prod.mk.inj (Except.ok.inj (show (Except.ok ([(decE (r_l1.headD 0), decE (z)), (decE (r_l2.headD 0), decE (x))], a_l2) : Except CheckError _) = Except.ok (xl, al) from hrunl))
  subst hal
  subst hr; subst hm
  try simp only [decE_eq] at hrun_l1
  try simp only [decE_eq] at hrun_l2
  try simp only [decE_eq, hx_l1] at hrun_l2
  simp only [decE_eq, hx_l1, hx_l2] at hxl
  refine ⟨xl, a_l2, ?_, hSl, ((hg_l1).trans hg_l2).trans hgl, eqL_retag hdl (by rw [← hxl]; rfl)⟩
  simp only [natEqPrT, decE_eq, StateT.run_bind, hrun_l1, hrun_l2, exc_ok_bind']
  rw [← hxl]
  rfl

def natEqUnT (c : NIdx) (x : EIdx) (y : EIdx) (z : EIdx) (sy : EIdx) (w : NIdx) : AM (List (EIdx × EIdx)) := do
  let l1 ← natAp2 c x z
  let l2 ← natAp2 c x sy
  let r3 ← natAp2 c x y
  let r2 ← natAp1 w r3
  pure [(l1, x), (l2, r2)]

def natEqUnW (p : Prog) (n : Nat) (m : Mem) (c x y z sy w : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "nat_ap2" [c, x, z] m) fun r_l1 m_l1 =>
  ntBW (callW p n "nat_ap2" [c, x, sy] m_l1) fun r_l2 m_l2 =>
  ntBW (callW p n "nat_ap2" [c, x, y] m_l2) fun r_r3 m_r3 =>
  ntBW (callW p n "nat_ap1" [w, r_r3.headD 0] m_r3) fun r_r2 m_r2 =>
  ntBW (callW p n "nat_eq_list2" [r_l1.headD 0, x, r_l2.headD 0, r_r2.headD 0] m_r2) fun rl ml =>
  some ([rl.headD 0, 2], ml)

theorem natEqUn_specW (p : Prog) (hp : p.lookup "nat_eq_un" = some natEqUn) (n : Nat) (s₀ : St)
    (c x y z sy w : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nat_eq_un" [c, x, y, z, sy, w]
    ⦃fun r s' => LocEq s' s₀ ∧ natEqUnW p n s₀.mem c x y z sy w = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, natEqUn]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "nat_ap1", callW_spec p n "nat_ap2", callW_spec p n "nat_eq_list2"] <;>
    finish (gen := 20) (instances := 10000) [natEqUnW, ntBW]

theorem natEqUn_ref (hN : NatEqProg p) (c x y z sy w : Word) :
    CallRef p "nat_eq_un" [c, x, y, z, sy, w] (fun m s => StageR dn vis fe m s ∧ H c ∧ H x ∧ H y ∧ H z ∧ H sy ∧ H w)
      (natEqUnT (decI c) (decE x) (decE y) (decE z) (decE sy) (decI w)) (KeepPost dn vis fe decEqRL) := by
  refine CallRef.of_succ fun k m s r m' ⟨hS, h_c, h_x, h_y, h_z, h_sy, h_w⟩ hc => ?_
  have hw := callW_model (M := fun mm => natEqUnW p k mm c x y z sy w) (natEqUn_specW p hN.lNatEqUn k · c x y z sy w) hc
  unfold natEqUnW at hw
  cases hc_l1 : callW p k "nat_ap2" [c, x, z] m with
  | none => rw [hc_l1] at hw; simp at hw
  | some q_l1 =>
  obtain ⟨r_l1, m_l1⟩ := q_l1
  rw [hc_l1, bW_some] at hw
  obtain ⟨x_l1, a_l1, hrun_l1, hS_l1, hg_l1, hl_l1, hx_l1⟩ := natAp2_ref (dn := dn) (vis := vis) (fe := fe) hN (c) (x) (z) k m s r_l1 m_l1 ⟨hS, h_c, h_x, h_z⟩ hc_l1
  cases hc_l2 : callW p k "nat_ap2" [c, x, sy] m_l1 with
  | none => rw [hc_l2] at hw; simp at hw
  | some q_l2 =>
  obtain ⟨r_l2, m_l2⟩ := q_l2
  rw [hc_l2, bW_some] at hw
  obtain ⟨x_l2, a_l2, hrun_l2, hS_l2, hg_l2, hl_l2, hx_l2⟩ := natAp2_ref (dn := dn) (vis := vis) (fe := fe) hN (c) (x) (sy) k m_l1 a_l1 r_l2 m_l2 ⟨hS_l1, h_c, h_x, h_sy⟩ hc_l2
  cases hc_r3 : callW p k "nat_ap2" [c, x, y] m_l2 with
  | none => rw [hc_r3] at hw; simp at hw
  | some q_r3 =>
  obtain ⟨r_r3, m_r3⟩ := q_r3
  rw [hc_r3, bW_some] at hw
  obtain ⟨x_r3, a_r3, hrun_r3, hS_r3, hg_r3, hl_r3, hx_r3⟩ := natAp2_ref (dn := dn) (vis := vis) (fe := fe) hN (c) (x) (y) k m_l2 a_l2 r_r3 m_r3 ⟨hS_l2, h_c, h_x, h_y⟩ hc_r3
  cases hc_r2 : callW p k "nat_ap1" [w, r_r3.headD 0] m_r3 with
  | none => rw [hc_r2] at hw; simp at hw
  | some q_r2 =>
  obtain ⟨r_r2, m_r2⟩ := q_r2
  rw [hc_r2, bW_some] at hw
  obtain ⟨x_r2, a_r2, hrun_r2, hS_r2, hg_r2, hl_r2, hx_r2⟩ := natAp1_ref (dn := dn) (vis := vis) (fe := fe) hN (w) (r_r3.headD 0) k m_r3 a_r3 r_r2 m_r2 ⟨hS_r3, h_w, hl_r3⟩ hc_r2
  cases hcl : callW p k "nat_eq_list2" [r_l1.headD 0, x, r_l2.headD 0, r_r2.headD 0] m_r2 with
  | none => rw [hcl] at hw; simp at hw
  | some ql =>
  obtain ⟨rl, ml⟩ := ql
  rw [hcl, bW_some] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨hr, hm⟩ := hw
  obtain ⟨xl, al, hrunl, hSl, hgl, hdl⟩ := natEqList2_ref (dn := dn) (vis := vis) (fe := fe) hN (r_l1.headD 0) (x) (r_l2.headD 0) (r_r2.headD 0) k m_r2 a_r2 rl ml ⟨hS_r2, hl_l1, h_x, hl_l2, hl_r2⟩ hcl
  obtain ⟨hxl, hal⟩ := Prod.mk.inj (Except.ok.inj (show (Except.ok ([(decE (r_l1.headD 0), decE (x)), (decE (r_l2.headD 0), decE (r_r2.headD 0))], a_r2) : Except CheckError _) = Except.ok (xl, al) from hrunl))
  subst hal
  subst hr; subst hm
  try simp only [decE_eq] at hrun_l1
  try simp only [decE_eq] at hrun_l2
  try simp only [decE_eq, hx_l1] at hrun_l2
  try simp only [decE_eq] at hrun_r3
  try simp only [decE_eq, hx_l1] at hrun_r3
  try simp only [decE_eq, hx_l2] at hrun_r3
  try simp only [decE_eq] at hrun_r2
  try simp only [decE_eq, hx_l1] at hrun_r2
  try simp only [decE_eq, hx_l2] at hrun_r2
  try simp only [decE_eq, hx_r3] at hrun_r2
  simp only [decE_eq, hx_l1, hx_l2, hx_r3, hx_r2] at hxl
  refine ⟨xl, a_r2, ?_, hSl, ((((hg_l1).trans hg_l2).trans hg_r3).trans hg_r2).trans hgl, eqL_retag hdl (by rw [← hxl]; rfl)⟩
  simp only [natEqUnT, decE_eq, StateT.run_bind, hrun_l1, hrun_l2, hrun_r3, hrun_r2, exc_ok_bind']
  rw [← hxl]
  rfl

def natEqMuT (c : NIdx) (x : EIdx) (y : EIdx) (z : EIdx) (sy : EIdx) (ad : NIdx) : AM (List (EIdx × EIdx)) := do
  let l1 ← natAp2 c x z
  let l2 ← natAp2 c x sy
  let r3 ← natAp2 c x y
  let r2 ← natAp2 ad r3 x
  pure [(l1, z), (l2, r2)]

def natEqMuW (p : Prog) (n : Nat) (m : Mem) (c x y z sy ad : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "nat_ap2" [c, x, z] m) fun r_l1 m_l1 =>
  ntBW (callW p n "nat_ap2" [c, x, sy] m_l1) fun r_l2 m_l2 =>
  ntBW (callW p n "nat_ap2" [c, x, y] m_l2) fun r_r3 m_r3 =>
  ntBW (callW p n "nat_ap2" [ad, r_r3.headD 0, x] m_r3) fun r_r2 m_r2 =>
  ntBW (callW p n "nat_eq_list2" [r_l1.headD 0, z, r_l2.headD 0, r_r2.headD 0] m_r2) fun rl ml =>
  some ([rl.headD 0, 2], ml)

theorem natEqMu_specW (p : Prog) (hp : p.lookup "nat_eq_mu" = some natEqMu) (n : Nat) (s₀ : St)
    (c x y z sy ad : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nat_eq_mu" [c, x, y, z, sy, ad]
    ⦃fun r s' => LocEq s' s₀ ∧ natEqMuW p n s₀.mem c x y z sy ad = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, natEqMu]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "nat_ap1", callW_spec p n "nat_ap2", callW_spec p n "nat_eq_list2"] <;>
    finish (gen := 20) (instances := 10000) [natEqMuW, ntBW]

theorem natEqMu_ref (hN : NatEqProg p) (c x y z sy ad : Word) :
    CallRef p "nat_eq_mu" [c, x, y, z, sy, ad] (fun m s => StageR dn vis fe m s ∧ H c ∧ H x ∧ H y ∧ H z ∧ H sy ∧ H ad)
      (natEqMuT (decI c) (decE x) (decE y) (decE z) (decE sy) (decI ad)) (KeepPost dn vis fe decEqRL) := by
  refine CallRef.of_succ fun k m s r m' ⟨hS, h_c, h_x, h_y, h_z, h_sy, h_ad⟩ hc => ?_
  have hw := callW_model (M := fun mm => natEqMuW p k mm c x y z sy ad) (natEqMu_specW p hN.lNatEqMu k · c x y z sy ad) hc
  unfold natEqMuW at hw
  cases hc_l1 : callW p k "nat_ap2" [c, x, z] m with
  | none => rw [hc_l1] at hw; simp at hw
  | some q_l1 =>
  obtain ⟨r_l1, m_l1⟩ := q_l1
  rw [hc_l1, bW_some] at hw
  obtain ⟨x_l1, a_l1, hrun_l1, hS_l1, hg_l1, hl_l1, hx_l1⟩ := natAp2_ref (dn := dn) (vis := vis) (fe := fe) hN (c) (x) (z) k m s r_l1 m_l1 ⟨hS, h_c, h_x, h_z⟩ hc_l1
  cases hc_l2 : callW p k "nat_ap2" [c, x, sy] m_l1 with
  | none => rw [hc_l2] at hw; simp at hw
  | some q_l2 =>
  obtain ⟨r_l2, m_l2⟩ := q_l2
  rw [hc_l2, bW_some] at hw
  obtain ⟨x_l2, a_l2, hrun_l2, hS_l2, hg_l2, hl_l2, hx_l2⟩ := natAp2_ref (dn := dn) (vis := vis) (fe := fe) hN (c) (x) (sy) k m_l1 a_l1 r_l2 m_l2 ⟨hS_l1, h_c, h_x, h_sy⟩ hc_l2
  cases hc_r3 : callW p k "nat_ap2" [c, x, y] m_l2 with
  | none => rw [hc_r3] at hw; simp at hw
  | some q_r3 =>
  obtain ⟨r_r3, m_r3⟩ := q_r3
  rw [hc_r3, bW_some] at hw
  obtain ⟨x_r3, a_r3, hrun_r3, hS_r3, hg_r3, hl_r3, hx_r3⟩ := natAp2_ref (dn := dn) (vis := vis) (fe := fe) hN (c) (x) (y) k m_l2 a_l2 r_r3 m_r3 ⟨hS_l2, h_c, h_x, h_y⟩ hc_r3
  cases hc_r2 : callW p k "nat_ap2" [ad, r_r3.headD 0, x] m_r3 with
  | none => rw [hc_r2] at hw; simp at hw
  | some q_r2 =>
  obtain ⟨r_r2, m_r2⟩ := q_r2
  rw [hc_r2, bW_some] at hw
  obtain ⟨x_r2, a_r2, hrun_r2, hS_r2, hg_r2, hl_r2, hx_r2⟩ := natAp2_ref (dn := dn) (vis := vis) (fe := fe) hN (ad) (r_r3.headD 0) (x) k m_r3 a_r3 r_r2 m_r2 ⟨hS_r3, h_ad, hl_r3, h_x⟩ hc_r2
  cases hcl : callW p k "nat_eq_list2" [r_l1.headD 0, z, r_l2.headD 0, r_r2.headD 0] m_r2 with
  | none => rw [hcl] at hw; simp at hw
  | some ql =>
  obtain ⟨rl, ml⟩ := ql
  rw [hcl, bW_some] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨hr, hm⟩ := hw
  obtain ⟨xl, al, hrunl, hSl, hgl, hdl⟩ := natEqList2_ref (dn := dn) (vis := vis) (fe := fe) hN (r_l1.headD 0) (z) (r_l2.headD 0) (r_r2.headD 0) k m_r2 a_r2 rl ml ⟨hS_r2, hl_l1, h_z, hl_l2, hl_r2⟩ hcl
  obtain ⟨hxl, hal⟩ := Prod.mk.inj (Except.ok.inj (show (Except.ok ([(decE (r_l1.headD 0), decE (z)), (decE (r_l2.headD 0), decE (r_r2.headD 0))], a_r2) : Except CheckError _) = Except.ok (xl, al) from hrunl))
  subst hal
  subst hr; subst hm
  try simp only [decE_eq] at hrun_l1
  try simp only [decE_eq] at hrun_l2
  try simp only [decE_eq, hx_l1] at hrun_l2
  try simp only [decE_eq] at hrun_r3
  try simp only [decE_eq, hx_l1] at hrun_r3
  try simp only [decE_eq, hx_l2] at hrun_r3
  try simp only [decE_eq] at hrun_r2
  try simp only [decE_eq, hx_l1] at hrun_r2
  try simp only [decE_eq, hx_l2] at hrun_r2
  try simp only [decE_eq, hx_r3] at hrun_r2
  simp only [decE_eq, hx_l1, hx_l2, hx_r3, hx_r2] at hxl
  refine ⟨xl, a_r2, ?_, hSl, ((((hg_l1).trans hg_l2).trans hg_r3).trans hg_r2).trans hgl, eqL_retag hdl (by rw [← hxl]; rfl)⟩
  simp only [natEqMuT, decE_eq, StateT.run_bind, hrun_l1, hrun_l2, hrun_r3, hrun_r2, exc_ok_bind']
  rw [← hxl]
  rfl

def natEqPoT (c : NIdx) (x : EIdx) (y : EIdx) (z : EIdx) (sy : EIdx) (sN : NIdx) (mu : NIdx) : AM (List (EIdx × EIdx)) := do
  let l1 ← natAp2 c x z
  let sz ← natAp1 sN z
  let l2 ← natAp2 c x sy
  let r3 ← natAp2 c x y
  let r2 ← natAp2 mu r3 x
  pure [(l1, sz), (l2, r2)]

def natEqPoW (p : Prog) (n : Nat) (m : Mem) (c x y z sy sN mu : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "nat_ap2" [c, x, z] m) fun r_l1 m_l1 =>
  ntBW (callW p n "nat_ap1" [sN, z] m_l1) fun r_sz m_sz =>
  ntBW (callW p n "nat_ap2" [c, x, sy] m_sz) fun r_l2 m_l2 =>
  ntBW (callW p n "nat_ap2" [c, x, y] m_l2) fun r_r3 m_r3 =>
  ntBW (callW p n "nat_ap2" [mu, r_r3.headD 0, x] m_r3) fun r_r2 m_r2 =>
  ntBW (callW p n "nat_eq_list2" [r_l1.headD 0, r_sz.headD 0, r_l2.headD 0, r_r2.headD 0] m_r2) fun rl ml =>
  some ([rl.headD 0, 2], ml)

theorem natEqPo_specW (p : Prog) (hp : p.lookup "nat_eq_po" = some natEqPo) (n : Nat) (s₀ : St)
    (c x y z sy sN mu : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nat_eq_po" [c, x, y, z, sy, sN, mu]
    ⦃fun r s' => LocEq s' s₀ ∧ natEqPoW p n s₀.mem c x y z sy sN mu = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, natEqPo]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "nat_ap1", callW_spec p n "nat_ap2", callW_spec p n "nat_eq_list2"] <;>
    finish (gen := 20) (instances := 10000) [natEqPoW, ntBW]

theorem natEqPo_ref (hN : NatEqProg p) (c x y z sy sN mu : Word) :
    CallRef p "nat_eq_po" [c, x, y, z, sy, sN, mu] (fun m s => StageR dn vis fe m s ∧ H c ∧ H x ∧ H y ∧ H z ∧ H sy ∧ H sN ∧ H mu)
      (natEqPoT (decI c) (decE x) (decE y) (decE z) (decE sy) (decI sN) (decI mu)) (KeepPost dn vis fe decEqRL) := by
  refine CallRef.of_succ fun k m s r m' ⟨hS, h_c, h_x, h_y, h_z, h_sy, h_sN, h_mu⟩ hc => ?_
  have hw := callW_model (M := fun mm => natEqPoW p k mm c x y z sy sN mu) (natEqPo_specW p hN.lNatEqPo k · c x y z sy sN mu) hc
  unfold natEqPoW at hw
  cases hc_l1 : callW p k "nat_ap2" [c, x, z] m with
  | none => rw [hc_l1] at hw; simp at hw
  | some q_l1 =>
  obtain ⟨r_l1, m_l1⟩ := q_l1
  rw [hc_l1, bW_some] at hw
  obtain ⟨x_l1, a_l1, hrun_l1, hS_l1, hg_l1, hl_l1, hx_l1⟩ := natAp2_ref (dn := dn) (vis := vis) (fe := fe) hN (c) (x) (z) k m s r_l1 m_l1 ⟨hS, h_c, h_x, h_z⟩ hc_l1
  cases hc_sz : callW p k "nat_ap1" [sN, z] m_l1 with
  | none => rw [hc_sz] at hw; simp at hw
  | some q_sz =>
  obtain ⟨r_sz, m_sz⟩ := q_sz
  rw [hc_sz, bW_some] at hw
  obtain ⟨x_sz, a_sz, hrun_sz, hS_sz, hg_sz, hl_sz, hx_sz⟩ := natAp1_ref (dn := dn) (vis := vis) (fe := fe) hN (sN) (z) k m_l1 a_l1 r_sz m_sz ⟨hS_l1, h_sN, h_z⟩ hc_sz
  cases hc_l2 : callW p k "nat_ap2" [c, x, sy] m_sz with
  | none => rw [hc_l2] at hw; simp at hw
  | some q_l2 =>
  obtain ⟨r_l2, m_l2⟩ := q_l2
  rw [hc_l2, bW_some] at hw
  obtain ⟨x_l2, a_l2, hrun_l2, hS_l2, hg_l2, hl_l2, hx_l2⟩ := natAp2_ref (dn := dn) (vis := vis) (fe := fe) hN (c) (x) (sy) k m_sz a_sz r_l2 m_l2 ⟨hS_sz, h_c, h_x, h_sy⟩ hc_l2
  cases hc_r3 : callW p k "nat_ap2" [c, x, y] m_l2 with
  | none => rw [hc_r3] at hw; simp at hw
  | some q_r3 =>
  obtain ⟨r_r3, m_r3⟩ := q_r3
  rw [hc_r3, bW_some] at hw
  obtain ⟨x_r3, a_r3, hrun_r3, hS_r3, hg_r3, hl_r3, hx_r3⟩ := natAp2_ref (dn := dn) (vis := vis) (fe := fe) hN (c) (x) (y) k m_l2 a_l2 r_r3 m_r3 ⟨hS_l2, h_c, h_x, h_y⟩ hc_r3
  cases hc_r2 : callW p k "nat_ap2" [mu, r_r3.headD 0, x] m_r3 with
  | none => rw [hc_r2] at hw; simp at hw
  | some q_r2 =>
  obtain ⟨r_r2, m_r2⟩ := q_r2
  rw [hc_r2, bW_some] at hw
  obtain ⟨x_r2, a_r2, hrun_r2, hS_r2, hg_r2, hl_r2, hx_r2⟩ := natAp2_ref (dn := dn) (vis := vis) (fe := fe) hN (mu) (r_r3.headD 0) (x) k m_r3 a_r3 r_r2 m_r2 ⟨hS_r3, h_mu, hl_r3, h_x⟩ hc_r2
  cases hcl : callW p k "nat_eq_list2" [r_l1.headD 0, r_sz.headD 0, r_l2.headD 0, r_r2.headD 0] m_r2 with
  | none => rw [hcl] at hw; simp at hw
  | some ql =>
  obtain ⟨rl, ml⟩ := ql
  rw [hcl, bW_some] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨hr, hm⟩ := hw
  obtain ⟨xl, al, hrunl, hSl, hgl, hdl⟩ := natEqList2_ref (dn := dn) (vis := vis) (fe := fe) hN (r_l1.headD 0) (r_sz.headD 0) (r_l2.headD 0) (r_r2.headD 0) k m_r2 a_r2 rl ml ⟨hS_r2, hl_l1, hl_sz, hl_l2, hl_r2⟩ hcl
  obtain ⟨hxl, hal⟩ := Prod.mk.inj (Except.ok.inj (show (Except.ok ([(decE (r_l1.headD 0), decE (r_sz.headD 0)), (decE (r_l2.headD 0), decE (r_r2.headD 0))], a_r2) : Except CheckError _) = Except.ok (xl, al) from hrunl))
  subst hal
  subst hr; subst hm
  try simp only [decE_eq] at hrun_l1
  try simp only [decE_eq] at hrun_sz
  try simp only [decE_eq, hx_l1] at hrun_sz
  try simp only [decE_eq] at hrun_l2
  try simp only [decE_eq, hx_l1] at hrun_l2
  try simp only [decE_eq, hx_sz] at hrun_l2
  try simp only [decE_eq] at hrun_r3
  try simp only [decE_eq, hx_l1] at hrun_r3
  try simp only [decE_eq, hx_sz] at hrun_r3
  try simp only [decE_eq, hx_l2] at hrun_r3
  try simp only [decE_eq] at hrun_r2
  try simp only [decE_eq, hx_l1] at hrun_r2
  try simp only [decE_eq, hx_sz] at hrun_r2
  try simp only [decE_eq, hx_l2] at hrun_r2
  try simp only [decE_eq, hx_r3] at hrun_r2
  simp only [decE_eq, hx_l1, hx_sz, hx_l2, hx_r3, hx_r2] at hxl
  refine ⟨xl, a_r2, ?_, hSl, (((((hg_l1).trans hg_sz).trans hg_l2).trans hg_r3).trans hg_r2).trans hgl, eqL_retag hdl (by rw [← hxl]; rfl)⟩
  simp only [natEqPoT, decE_eq, StateT.run_bind, hrun_l1, hrun_sz, hrun_l2, hrun_r3, hrun_r2, exc_ok_bind']
  rw [← hxl]
  rfl

def natEqBeT (c : NIdx) (x : EIdx) (y : EIdx) (z : EIdx) (sx : EIdx) (sy : EIdx) (bT : EIdx) (bF : EIdx) : AM (List (EIdx × EIdx)) := do
  let l1 ← natAp2 c z z
  let l2 ← natAp2 c z sy
  let l3 ← natAp2 c sx z
  let l4 ← natAp2 c sx sy
  let r4 ← natAp2 c x y
  pure [(l1, bT), (l2, bF), (l3, bF), (l4, r4)]

def natEqBeW (p : Prog) (n : Nat) (m : Mem) (c x y z sx sy bT bF : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "nat_ap2" [c, z, z] m) fun r_l1 m_l1 =>
  ntBW (callW p n "nat_ap2" [c, z, sy] m_l1) fun r_l2 m_l2 =>
  ntBW (callW p n "nat_ap2" [c, sx, z] m_l2) fun r_l3 m_l3 =>
  ntBW (callW p n "nat_ap2" [c, sx, sy] m_l3) fun r_l4 m_l4 =>
  ntBW (callW p n "nat_ap2" [c, x, y] m_l4) fun r_r4 m_r4 =>
  ntBW (callW p n "nat_eq_list4" [r_l1.headD 0, bT, r_l2.headD 0, bF, r_l3.headD 0, bF, r_l4.headD 0, r_r4.headD 0] m_r4) fun rl ml =>
  some ([rl.headD 0, 4], ml)

theorem natEqBe_specW (p : Prog) (hp : p.lookup "nat_eq_be" = some natEqBe) (n : Nat) (s₀ : St)
    (c x y z sx sy bT bF : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nat_eq_be" [c, x, y, z, sx, sy, bT, bF]
    ⦃fun r s' => LocEq s' s₀ ∧ natEqBeW p n s₀.mem c x y z sx sy bT bF = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, natEqBe]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "nat_ap1", callW_spec p n "nat_ap2", callW_spec p n "nat_eq_list4"] <;>
    finish (gen := 20) (instances := 10000) [natEqBeW, ntBW]

theorem natEqBe_ref (hN : NatEqProg p) (c x y z sx sy bT bF : Word) :
    CallRef p "nat_eq_be" [c, x, y, z, sx, sy, bT, bF] (fun m s => StageR dn vis fe m s ∧ H c ∧ H x ∧ H y ∧ H z ∧ H sx ∧ H sy ∧ H bT ∧ H bF)
      (natEqBeT (decI c) (decE x) (decE y) (decE z) (decE sx) (decE sy) (decE bT) (decE bF)) (KeepPost dn vis fe decEqRL) := by
  refine CallRef.of_succ fun k m s r m' ⟨hS, h_c, h_x, h_y, h_z, h_sx, h_sy, h_bT, h_bF⟩ hc => ?_
  have hw := callW_model (M := fun mm => natEqBeW p k mm c x y z sx sy bT bF) (natEqBe_specW p hN.lNatEqBe k · c x y z sx sy bT bF) hc
  unfold natEqBeW at hw
  cases hc_l1 : callW p k "nat_ap2" [c, z, z] m with
  | none => rw [hc_l1] at hw; simp at hw
  | some q_l1 =>
  obtain ⟨r_l1, m_l1⟩ := q_l1
  rw [hc_l1, bW_some] at hw
  obtain ⟨x_l1, a_l1, hrun_l1, hS_l1, hg_l1, hl_l1, hx_l1⟩ := natAp2_ref (dn := dn) (vis := vis) (fe := fe) hN (c) (z) (z) k m s r_l1 m_l1 ⟨hS, h_c, h_z, h_z⟩ hc_l1
  cases hc_l2 : callW p k "nat_ap2" [c, z, sy] m_l1 with
  | none => rw [hc_l2] at hw; simp at hw
  | some q_l2 =>
  obtain ⟨r_l2, m_l2⟩ := q_l2
  rw [hc_l2, bW_some] at hw
  obtain ⟨x_l2, a_l2, hrun_l2, hS_l2, hg_l2, hl_l2, hx_l2⟩ := natAp2_ref (dn := dn) (vis := vis) (fe := fe) hN (c) (z) (sy) k m_l1 a_l1 r_l2 m_l2 ⟨hS_l1, h_c, h_z, h_sy⟩ hc_l2
  cases hc_l3 : callW p k "nat_ap2" [c, sx, z] m_l2 with
  | none => rw [hc_l3] at hw; simp at hw
  | some q_l3 =>
  obtain ⟨r_l3, m_l3⟩ := q_l3
  rw [hc_l3, bW_some] at hw
  obtain ⟨x_l3, a_l3, hrun_l3, hS_l3, hg_l3, hl_l3, hx_l3⟩ := natAp2_ref (dn := dn) (vis := vis) (fe := fe) hN (c) (sx) (z) k m_l2 a_l2 r_l3 m_l3 ⟨hS_l2, h_c, h_sx, h_z⟩ hc_l3
  cases hc_l4 : callW p k "nat_ap2" [c, sx, sy] m_l3 with
  | none => rw [hc_l4] at hw; simp at hw
  | some q_l4 =>
  obtain ⟨r_l4, m_l4⟩ := q_l4
  rw [hc_l4, bW_some] at hw
  obtain ⟨x_l4, a_l4, hrun_l4, hS_l4, hg_l4, hl_l4, hx_l4⟩ := natAp2_ref (dn := dn) (vis := vis) (fe := fe) hN (c) (sx) (sy) k m_l3 a_l3 r_l4 m_l4 ⟨hS_l3, h_c, h_sx, h_sy⟩ hc_l4
  cases hc_r4 : callW p k "nat_ap2" [c, x, y] m_l4 with
  | none => rw [hc_r4] at hw; simp at hw
  | some q_r4 =>
  obtain ⟨r_r4, m_r4⟩ := q_r4
  rw [hc_r4, bW_some] at hw
  obtain ⟨x_r4, a_r4, hrun_r4, hS_r4, hg_r4, hl_r4, hx_r4⟩ := natAp2_ref (dn := dn) (vis := vis) (fe := fe) hN (c) (x) (y) k m_l4 a_l4 r_r4 m_r4 ⟨hS_l4, h_c, h_x, h_y⟩ hc_r4
  cases hcl : callW p k "nat_eq_list4" [r_l1.headD 0, bT, r_l2.headD 0, bF, r_l3.headD 0, bF, r_l4.headD 0, r_r4.headD 0] m_r4 with
  | none => rw [hcl] at hw; simp at hw
  | some ql =>
  obtain ⟨rl, ml⟩ := ql
  rw [hcl, bW_some] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨hr, hm⟩ := hw
  obtain ⟨xl, al, hrunl, hSl, hgl, hdl⟩ := natEqList4_ref (dn := dn) (vis := vis) (fe := fe) hN (r_l1.headD 0) (bT) (r_l2.headD 0) (bF) (r_l3.headD 0) (bF) (r_l4.headD 0) (r_r4.headD 0) k m_r4 a_r4 rl ml ⟨hS_r4, hl_l1, h_bT, hl_l2, h_bF, hl_l3, h_bF, hl_l4, hl_r4⟩ hcl
  obtain ⟨hxl, hal⟩ := Prod.mk.inj (Except.ok.inj (show (Except.ok ([(decE (r_l1.headD 0), decE (bT)), (decE (r_l2.headD 0), decE (bF)), (decE (r_l3.headD 0), decE (bF)), (decE (r_l4.headD 0), decE (r_r4.headD 0))], a_r4) : Except CheckError _) = Except.ok (xl, al) from hrunl))
  subst hal
  subst hr; subst hm
  try simp only [decE_eq] at hrun_l1
  try simp only [decE_eq] at hrun_l2
  try simp only [decE_eq, hx_l1] at hrun_l2
  try simp only [decE_eq] at hrun_l3
  try simp only [decE_eq, hx_l1] at hrun_l3
  try simp only [decE_eq, hx_l2] at hrun_l3
  try simp only [decE_eq] at hrun_l4
  try simp only [decE_eq, hx_l1] at hrun_l4
  try simp only [decE_eq, hx_l2] at hrun_l4
  try simp only [decE_eq, hx_l3] at hrun_l4
  try simp only [decE_eq] at hrun_r4
  try simp only [decE_eq, hx_l1] at hrun_r4
  try simp only [decE_eq, hx_l2] at hrun_r4
  try simp only [decE_eq, hx_l3] at hrun_r4
  try simp only [decE_eq, hx_l4] at hrun_r4
  simp only [decE_eq, hx_l1, hx_l2, hx_l3, hx_l4, hx_r4] at hxl
  refine ⟨xl, a_r4, ?_, hSl, (((((hg_l1).trans hg_l2).trans hg_l3).trans hg_l4).trans hg_r4).trans hgl, eqL_retag hdl (by rw [← hxl]; rfl)⟩
  simp only [natEqBeT, decE_eq, StateT.run_bind, hrun_l1, hrun_l2, hrun_l3, hrun_l4, hrun_r4, exc_ok_bind']
  rw [← hxl]
  rfl

def natEqBlT (c : NIdx) (x : EIdx) (y : EIdx) (z : EIdx) (sx : EIdx) (sy : EIdx) (bT : EIdx) (bF : EIdx) : AM (List (EIdx × EIdx)) := do
  let l1 ← natAp2 c z y
  let l2 ← natAp2 c sx z
  let l3 ← natAp2 c sx sy
  let r3 ← natAp2 c x y
  pure [(l1, bT), (l2, bF), (l3, r3)]

def natEqBlW (p : Prog) (n : Nat) (m : Mem) (c x y z sx sy bT bF : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "nat_ap2" [c, z, y] m) fun r_l1 m_l1 =>
  ntBW (callW p n "nat_ap2" [c, sx, z] m_l1) fun r_l2 m_l2 =>
  ntBW (callW p n "nat_ap2" [c, sx, sy] m_l2) fun r_l3 m_l3 =>
  ntBW (callW p n "nat_ap2" [c, x, y] m_l3) fun r_r3 m_r3 =>
  ntBW (callW p n "nat_eq_list3" [r_l1.headD 0, bT, r_l2.headD 0, bF, r_l3.headD 0, r_r3.headD 0] m_r3) fun rl ml =>
  some ([rl.headD 0, 3], ml)

theorem natEqBl_specW (p : Prog) (hp : p.lookup "nat_eq_bl" = some natEqBl) (n : Nat) (s₀ : St)
    (c x y z sx sy bT bF : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nat_eq_bl" [c, x, y, z, sx, sy, bT, bF]
    ⦃fun r s' => LocEq s' s₀ ∧ natEqBlW p n s₀.mem c x y z sx sy bT bF = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, natEqBl]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "nat_ap1", callW_spec p n "nat_ap2", callW_spec p n "nat_eq_list3"] <;>
    finish (gen := 20) (instances := 10000) [natEqBlW, ntBW]

theorem natEqBl_ref (hN : NatEqProg p) (c x y z sx sy bT bF : Word) :
    CallRef p "nat_eq_bl" [c, x, y, z, sx, sy, bT, bF] (fun m s => StageR dn vis fe m s ∧ H c ∧ H x ∧ H y ∧ H z ∧ H sx ∧ H sy ∧ H bT ∧ H bF)
      (natEqBlT (decI c) (decE x) (decE y) (decE z) (decE sx) (decE sy) (decE bT) (decE bF)) (KeepPost dn vis fe decEqRL) := by
  refine CallRef.of_succ fun k m s r m' ⟨hS, h_c, h_x, h_y, h_z, h_sx, h_sy, h_bT, h_bF⟩ hc => ?_
  have hw := callW_model (M := fun mm => natEqBlW p k mm c x y z sx sy bT bF) (natEqBl_specW p hN.lNatEqBl k · c x y z sx sy bT bF) hc
  unfold natEqBlW at hw
  cases hc_l1 : callW p k "nat_ap2" [c, z, y] m with
  | none => rw [hc_l1] at hw; simp at hw
  | some q_l1 =>
  obtain ⟨r_l1, m_l1⟩ := q_l1
  rw [hc_l1, bW_some] at hw
  obtain ⟨x_l1, a_l1, hrun_l1, hS_l1, hg_l1, hl_l1, hx_l1⟩ := natAp2_ref (dn := dn) (vis := vis) (fe := fe) hN (c) (z) (y) k m s r_l1 m_l1 ⟨hS, h_c, h_z, h_y⟩ hc_l1
  cases hc_l2 : callW p k "nat_ap2" [c, sx, z] m_l1 with
  | none => rw [hc_l2] at hw; simp at hw
  | some q_l2 =>
  obtain ⟨r_l2, m_l2⟩ := q_l2
  rw [hc_l2, bW_some] at hw
  obtain ⟨x_l2, a_l2, hrun_l2, hS_l2, hg_l2, hl_l2, hx_l2⟩ := natAp2_ref (dn := dn) (vis := vis) (fe := fe) hN (c) (sx) (z) k m_l1 a_l1 r_l2 m_l2 ⟨hS_l1, h_c, h_sx, h_z⟩ hc_l2
  cases hc_l3 : callW p k "nat_ap2" [c, sx, sy] m_l2 with
  | none => rw [hc_l3] at hw; simp at hw
  | some q_l3 =>
  obtain ⟨r_l3, m_l3⟩ := q_l3
  rw [hc_l3, bW_some] at hw
  obtain ⟨x_l3, a_l3, hrun_l3, hS_l3, hg_l3, hl_l3, hx_l3⟩ := natAp2_ref (dn := dn) (vis := vis) (fe := fe) hN (c) (sx) (sy) k m_l2 a_l2 r_l3 m_l3 ⟨hS_l2, h_c, h_sx, h_sy⟩ hc_l3
  cases hc_r3 : callW p k "nat_ap2" [c, x, y] m_l3 with
  | none => rw [hc_r3] at hw; simp at hw
  | some q_r3 =>
  obtain ⟨r_r3, m_r3⟩ := q_r3
  rw [hc_r3, bW_some] at hw
  obtain ⟨x_r3, a_r3, hrun_r3, hS_r3, hg_r3, hl_r3, hx_r3⟩ := natAp2_ref (dn := dn) (vis := vis) (fe := fe) hN (c) (x) (y) k m_l3 a_l3 r_r3 m_r3 ⟨hS_l3, h_c, h_x, h_y⟩ hc_r3
  cases hcl : callW p k "nat_eq_list3" [r_l1.headD 0, bT, r_l2.headD 0, bF, r_l3.headD 0, r_r3.headD 0] m_r3 with
  | none => rw [hcl] at hw; simp at hw
  | some ql =>
  obtain ⟨rl, ml⟩ := ql
  rw [hcl, bW_some] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨hr, hm⟩ := hw
  obtain ⟨xl, al, hrunl, hSl, hgl, hdl⟩ := natEqList3_ref (dn := dn) (vis := vis) (fe := fe) hN (r_l1.headD 0) (bT) (r_l2.headD 0) (bF) (r_l3.headD 0) (r_r3.headD 0) k m_r3 a_r3 rl ml ⟨hS_r3, hl_l1, h_bT, hl_l2, h_bF, hl_l3, hl_r3⟩ hcl
  obtain ⟨hxl, hal⟩ := Prod.mk.inj (Except.ok.inj (show (Except.ok ([(decE (r_l1.headD 0), decE (bT)), (decE (r_l2.headD 0), decE (bF)), (decE (r_l3.headD 0), decE (r_r3.headD 0))], a_r3) : Except CheckError _) = Except.ok (xl, al) from hrunl))
  subst hal
  subst hr; subst hm
  try simp only [decE_eq] at hrun_l1
  try simp only [decE_eq] at hrun_l2
  try simp only [decE_eq, hx_l1] at hrun_l2
  try simp only [decE_eq] at hrun_l3
  try simp only [decE_eq, hx_l1] at hrun_l3
  try simp only [decE_eq, hx_l2] at hrun_l3
  try simp only [decE_eq] at hrun_r3
  try simp only [decE_eq, hx_l1] at hrun_r3
  try simp only [decE_eq, hx_l2] at hrun_r3
  try simp only [decE_eq, hx_l3] at hrun_r3
  simp only [decE_eq, hx_l1, hx_l2, hx_l3, hx_r3] at hxl
  refine ⟨xl, a_r3, ?_, hSl, ((((hg_l1).trans hg_l2).trans hg_l3).trans hg_r3).trans hgl, eqL_retag hdl (by rw [← hxl]; rfl)⟩
  simp only [natEqBlT, decE_eq, StateT.run_bind, hrun_l1, hrun_l2, hrun_l3, hrun_r3, exc_ok_bind']
  rw [← hxl]
  rfl


/-! ### `certify_nat_eqs` -/

theorem EqL.cons {m : Mem} {o l : Nat} {e : EIdx × EIdx} {es : List (EIdx × EIdx)}
    (h : EqL m o l (e :: es)) :
    ∃ p a b : Word, l ≠ 0 ∧ (iwA m)[o]? = some p ∧ RecAt m p a b ∧ a.toNat < 2 ^ 32 ∧
      b.toNat < 2 ^ 32 ∧ e = (decE a, decE b) ∧ EqL m (o + 1) (l - 1) es := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨p, a, b, hp, hr, ha, hb, he⟩ := h3 0 (by simp)
  refine ⟨p, a, b, by simp at h2; omega, by simpa using hp, hr, ha, hb, by simpa using he, ?_, ?_, ?_⟩
  · simp at h2 ⊢; omega
  · simp at h2 ⊢; omega
  · intro j hj
    obtain ⟨p', a', b', hp', hr', ha', hb', he'⟩ := h3 (j + 1) (by simpa using hj)
    refine ⟨p', a', b', ?_, hr', ha', hb', by simpa using he'⟩
    simpa [Nat.add_assoc, Nat.add_comm 1 j] using hp'

def certW (p : Prog) (cl : CallM) (n : Nat) (m : Mem) (vis o l : Word) : Option (List Word × Mem) :=
  if l = 0 then some ([1], m) else
  ntBW (cl n "is_def_eq_core" [vis, 2, rdW (m.arr64 IW) (rdW (m.arr64 IW) o),
      rdW (m.arr64 IW) (rdW (m.arr64 IW) o + 1)] m) fun r1 m1 =>
  if r1.headD 0 = 0 then some ([0], m1)
  else ntBW (callW p n "certify_nat_eqs" [vis, o + 1, l - 1] m1) fun r2 m2 => some ([r2.headD 0], m2)

theorem certify_specW (p : Prog) (hp : p.lookup "certify_nat_eqs" = some certifyNatEqsL)
    (cl : CallM) (hc : CallSpec p cl) (n : Nat)
    (s₀ : St) (vis o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "certify_nat_eqs" [vis, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ certW p cl n s₀.mem vis o l = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, certifyNatEqsL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      hc n "is_def_eq_core", callW_spec p n "certify_nat_eqs"] <;>
    finish (gen := 20) [certW, ntBW]

local notation "V" => ConLeche.CheckMode.verified

theorem certify_ref (hN : NatEqProg p) (o l : Word) (ps : List (EIdx × EIdx)) :
    ∀ (k : Nat) (m : Mem) (a : AState) (r : List Word) (m' : Mem), StageR dn vis fe m a →
      EqL m o.toNat l.toNat ps → o.toNat + l.toNat < 2 ^ 64 →
      callW p k "certify_nat_eqs" [vis, o, l] m = some (r, m') →
      ∃ x a', (certifyNatEqs V fe ps).run a = .ok (x, a') ∧ KeepPost dn vis fe decW0B m m' a' r x := by
  induction ps generalizing o l with
  | nil =>
    intro k m a r m' hS hE hb hc
    have hl0 : l = 0 := UInt64.toNat_inj.mp (by have := hE.2.1; simpa using this)
    cases k with
    | zero => rw [callW_zero] at hc; cases hc
    | succ k =>
    have hw := callW_model (M := fun mm => certW p stubCall k mm vis o l) (certify_specW p hN.lNatCertify stubCall (stubCall_spec p) k · vis o l) hc
    simp only [certW, hl0, if_true, Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact ⟨true, a, rfl, hS, IWGrow.refl _, by simp [decW0B]⟩
  | cons e es ih =>
    intro k m a r m' hS hE hb hc
    cases k with
    | zero => rw [callW_zero] at hc; cases hc
    | succ k =>
    obtain ⟨pp, ea, eb, hl0, hpp, hrec, hea, heb, he, hrest⟩ := hE.cons
    have hw := callW_model (M := fun mm => certW p stubCall k mm vis o l) (certify_specW p hN.lNatCertify stubCall (stubCall_spec p) k · vis o l) hc
    unfold certW at hw
    rw [if_neg (fun h => hl0 (by simp [h]))] at hw
    have hpp' : rdW (m.arr64 IW) o = pp := by
      simp only [iwA] at hpp; simp [rdW, hpp]
    have hea' : rdW (m.arr64 IW) pp = ea := by
      obtain ⟨-, h2, -⟩ := hrec; simp only [iwA] at h2; simp [rdW, h2]
    have heb' : rdW (m.arr64 IW) (pp + 1) = eb := by
      obtain ⟨h1, -, h3⟩ := hrec
      have hpb : (pp + 1).toNat = pp.toNat + 1 := by
        have e1 := hS.2.1; have e2 := hS.2.2.2.1; have e3 : pp.toNat + 1 < 2 ^ 64 := by omega
        rw [UInt64.toNat_add]; simp only [UInt64.toNat_one]; exact Nat.mod_eq_of_lt e3
      simp only [iwA] at h3; simp [rdW, hpb, h3]
    rw [hpp', hea', heb'] at hw
    cases h1 : stubCall k "is_def_eq_core" [vis, 2, ea, eb] m with
    | none => rw [h1] at hw; simp at hw
    | some q1 =>
    obtain ⟨r1, m1⟩ := q1
    rw [h1, bW_some] at hw
    obtain ⟨x1, a1, hrun1, hS1, hg1, hx1⟩ := isDefEqCore_spec dn vis fe 2 ea eb hea heb m m1 a r1 h1 hS
    by_cases hz : r1.headD 0 = 0
    · rw [if_pos hz] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      have hx : x1 = false := by have := hx1.1; rw [hz] at this; simpa using this.symm
      refine ⟨false, a1, ?_, hS1, hg1, by simp [decW0B]⟩
      have hrun1' : (isDefEqCore V fe checkFuel 2 (decE ea) (decE eb)).run a = .ok (x1, a1) := hrun1
      subst he
      simp only [certifyNatEqs, StateT.run_bind, hrun1', exc_ok_bind', hx, Bool.false_eq_true, if_false]
      rfl
    · rw [if_neg hz] at hw
      have hx : x1 = true := by
        have := hx1.1; have hne : (r1.headD 0 != 0) = true := by simpa using hz
        rw [hne] at this; exact this.symm
      have hrun1' : (isDefEqCore V fe checkFuel 2 (decE ea) (decE eb)).run a = .ok (x1, a1) := hrun1
      cases h2 : callW p k "certify_nat_eqs" [vis, o + 1, l - 1] m1 with
      | none => rw [h2] at hw; simp at hw
      | some q2 =>
      obtain ⟨r2, m2⟩ := q2
      rw [h2, bW_some] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      have hrest1 : EqL m1 (o + 1).toNat (l - 1).toNat es := by
        have ho1 : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
        have hl1 : (l - 1).toNat = l.toNat - 1 := by
          have : 0 < l.toNat := Nat.pos_of_ne_zero hl0
          rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
        rw [ho1, hl1]; exact hrest.grow hg1
      have hb1 : (o + 1).toNat + (l - 1).toNat < 2 ^ 64 := by
        have ho1 : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
        have hl1 : (l - 1).toNat = l.toNat - 1 := by
          have : 0 < l.toNat := Nat.pos_of_ne_zero hl0
          rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
        omega
      obtain ⟨x, a2, hrun2, hK⟩ := ih (o + 1) (l - 1) k m1 a1 r2 m2 hS1 hrest1 hb1 h2
      refine ⟨x, a2, ?_, hK.1, hg1.trans hK.2.1, by simpa [decW0B] using hK.2.2⟩
      subst he
      simp only [certifyNatEqs, StateT.run_bind, hrun1', exc_ok_bind', hx, if_true]
      exact hrun2

/-- Under `StageR` (the core through its stub); the census link is `certW_okT`. -/
theorem certifyNatEqs_refines (hN : NatEqProg p) (o l : Word) (ps : List (EIdx × EIdx)) :
    RefAM p "certify_nat_eqs" [vis, o, l]
      (fun m a => StageR dn vis fe m a ∧ EqL m o.toNat l.toNat ps ∧ o.toNat + l.toNat < 2 ^ 64)
      (certifyNatEqs V fe ps) (KeepPost dn vis fe decW0B) :=
  CallRef.refAM (fun k m a r m' ⟨hS, hE, hb⟩ hc => certify_ref hN o l ps k m a r m' hS hE hb hc)

end eq

end L.Ind
