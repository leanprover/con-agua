import ConAgua.Arena.DeclCanonRules

/-!
# `ci_canon_defn`, `ci_canon_rec`, `ci_canon_eq`, `canon_eq_list` (lane `decls3`, helper `decls3-canon`)
-/

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- A twin conditional whose condition is an `AM Bool`, with the state changing along the way. -/
theorem andThen_st {A B : AM Bool} {a a1 : AState} {r r1 : Word} {b1 : Bool} {Q : AState → Prop}
    (hA : A.run a = .ok (b1, a1)) (hr1 : r1 = if b1 then 1 else 0)
    (hB : r1 ≠ 0 → ∃ b2 a2, B.run a1 = .ok (b2, a2) ∧ r = (if b2 then 1 else 0) ∧ Q a2)
    (h0 : r1 = 0 → r = 0 ∧ Q a1) :
    ∃ b a', (do let x ← A; if x = true then B else pure false : AM Bool).run a = .ok (b, a') ∧
      r = (if b then 1 else 0) ∧ Q a' := by
  cases b1
  · obtain ⟨hr, hQ⟩ := h0 (by simpa using hr1)
    refine ⟨false, a1, ?_, by simp [hr], hQ⟩
    simp [StateT.run_bind, hA, exc_ok_bind']; rfl
  · obtain ⟨b2, a2, hb2, hr, hQ⟩ := hB (by simp [hr1])
    refine ⟨b2, a2, ?_, hr, hQ⟩
    simp [StateT.run_bind, hA, exc_ok_bind', hb2]

/-- The state-and-pool facts every comparison carries. -/
def CQ (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m m' : Mem) (a' : AState) : Prop :=
  StageR dn vis fe m' a' ∧ IWGrow m m' ∧ PoolSmall m' ∧ LitInj a'


/-! ## `ci_canon_defn` -/

mutual
/-- **The model of `ci_canon_defn(p, q)`**. -/
def cdW : Nat → Mem → Word → Word → Option (Word × Mem)
  | 0, _, _, _ => none
  | k + 1, m, p, q => cdK0 k m p q (if hintEqB (m.arr64 EREC) (p + 6) (q + 6) then 1 else 0)

/-- After `hint_eq`. -/
def cdK0 (k : Nat) (m : Mem) (p q e : Word) : Option (Word × Mem) :=
  if e = 0 then some (0, m) else cdK1 k p q (cvceW k m (p + 1) (q + 1))

/-- After `cv_canon_eq`. -/
def cdK1 (k : Nat) (p q : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (e, m1) => if e = 0 then some (0, m1) else cdK2 k p q (ctxW k m1 (p + 1) (q + 1))

/-- After `canon_ctx`. -/
def cdK2 (k : Nat) (p q : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (rc, m2) =>
    ceW k m2 (rc.headD 0) (rc.tail.headD 0) (rc.tail.tail.headD 0) (rc.tail.tail.tail.headD 0)
      (rc.tail.tail.tail.tail.headD 0) (rc.tail.tail.tail.tail.tail.headD 0) 4000000000
      (rdW (m2.arr64 EREC) (p + 5)) (rdW (m2.arr64 EREC) (q + 5))
end

section arms
variable (k : Nat) (m m1 m2 : Mem) (p q e : Word) (rc : List Word)
theorem cdW_succ : cdW (k + 1) m p q =
    cdK0 k m p q (if hintEqB (m.arr64 EREC) (p + 6) (q + 6) then 1 else 0) := by rw [cdW]
theorem cdK0_def : cdK0 k m p q e =
    (if e = 0 then some (0, m) else cdK1 k p q (cvceW k m (p + 1) (q + 1))) := by rw [cdK0]
theorem cdK1_some : cdK1 k p q (some (e, m1)) =
    (if e = 0 then some (0, m1) else cdK2 k p q (ctxW k m1 (p + 1) (q + 1))) := by rw [cdK1]
theorem cdK2_some : cdK2 k p q (some (rc, m2)) =
    ceW k m2 (rc.headD 0) (rc.tail.headD 0) (rc.tail.tail.headD 0) (rc.tail.tail.tail.headD 0)
      (rc.tail.tail.tail.tail.headD 0) (rc.tail.tail.tail.tail.tail.headD 0) 4000000000
      (rdW (m2.arr64 EREC) (p + 5)) (rdW (m2.arr64 EREC) (q + 5)) := by rw [cdK2]
end arms

grind_pattern [ind_grind] cdW_succ => cdW (k + 1) m p q
grind_pattern [ind_grind] cdK0_def => cdK0 k m p q e
grind_pattern [ind_grind] cdK1_some => cdK1 k p q (some (e, m1))
grind_pattern [ind_grind] cdK2_some => cdK2 k p q (some (rc, m2))

theorem ciCanonDefn_spec (pr : Prog) (hp : CanonProg pr) (n : Nat) (s₀ : St) (p q : Word) :
    ⦃fun s => s = s₀⦄ invoke pr (exec pr n) "ci_canon_defn" [p, q]
    ⦃fun x s' => LocEq s' s₀ ∧ cdW n s₀.mem p q = some (x.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.ci_canon_defn]
  simp only [callFn, ciCanonDefn]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        hintEq_spec pr hp n, cvCanonEq_spec pr hp n, canonCtx_spec pr hp n,
        canonExprEq_spec pr hp n] <;>
      finish (gen := 20) [cdW]


theorem ciD_defn {a : Array Word} {dn : NIdx → Option ConLeche.Name} {p : Nat} {cv : IConstantVal}
    {v : EIdx} {hi : ConLeche.ReducibilityHint} (h : decCI a dn p = some (.defnInfo cv v hi)) :
    decCV a (p + 1) = some cv ∧ hd? a (p + 5) = some v ∧ decHint a (p + 6) = some hi := by
  obtain ⟨wk, e, hk⟩ := ciD h
  rcases hk with ⟨-, c, hc, hx⟩ | ⟨-, c, v', hi', hc, hv, hh, hx⟩ | ⟨-, c, hc, hx⟩ |
      ⟨-, c, caps, hc, hcaps, hx⟩ | ⟨-, c, np, nf, hc, hnp, hnf, hx⟩ |
      ⟨-, c, mi, rp, o, c', rules, hc, hmi, hrp, ho, hc', hr, hx⟩ | ⟨-, tbl, ht, hx⟩ <;>
    (cases hx <;> first | exact ⟨hc, hv, hh⟩ | skip)

theorem cdW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} (k : Nat)
    {m m' : Mem} {p q x : Word} {cv cv' : IConstantVal} {v v' : EIdx}
    {hi hi' : ConLeche.ReducibilityHint}
    (h : cdW k m p q = some (x, m')) (hS : StageR dn vis fe m a)
    (hp : decCI (erecP m) dn p.toNat = some (.defnInfo cv v hi))
    (hq : decCI (erecP m) dn q.toNat = some (.defnInfo cv' v' hi'))
    (hP : PoolSmall m) (hL : LitInj a) :
    ∃ (b : Bool) (a' : AState),
      (IConstantInfo.canonEq (.defnInfo cv v hi) (.defnInfo cv' v' hi')).run a = .ok (b, a') ∧
      x = (if b then 1 else 0) ∧ CQ dn vis fe m m' a' := by
  cases k with
  | zero => simp [cdW] at h
  | succ k =>
  rw [cdW_succ] at h
  obtain ⟨hcp, hvp, hhp⟩ := ciD_defn hp
  obtain ⟨hcq, hvq, hhq⟩ := ciD_defn hq
  have hsz : (m.arr64 EREC).size < 2 ^ 64 := hS.2.2.2.2.1
  have hsz' : (erecP m).size < 2 ^ 64 := Nat.lt_of_le_of_lt (by simp [erecP]; exact Nat.min_le_right _ _) hsz
  obtain ⟨w1, hw1, -⟩ := decCV_name hcp
  obtain ⟨u1, hu1, -⟩ := decCV_name hcq
  have p1 : (p + 1).toNat = p.toNat + 1 := toNat_add_of_get hsz' (k := 1) (kn := 1) rfl hw1
  have q1 : (q + 1).toNat = q.toNat + 1 := toNat_add_of_get hsz' (k := 1) (kn := 1) rfl hu1
  have hB := hintEqB_ok' (a := erA m) hsz (p := p) (q := q) (k := 6) (kn := 6) rfl
    (ArrExt.decHint (erecP_ext m) hhp) (ArrExt.decHint (erecP_ext m) hhq)
  simp only [erA] at hB
  simp only [IConstantInfo.canonEq]
  rw [cdK0_def] at h
  by_cases hbB : hintEqB (m.arr64 EREC) (p + 6) (q + 6) = true
  · have hd : hi = hi' := of_decide_eq_true (hB ▸ hbB)
    subst hd
    have hne : (if hintEqB (m.arr64 EREC) (p + 6) (q + 6) = true then (1 : Word) else 0) ≠ 0 := by
      simp [hbB]
    rw [if_neg hne] at h
    cases hc : cvceW k m (p + 1) (q + 1) with
    | none => rw [hc] at h; simp [cdK1] at h
    | some xx =>
    obtain ⟨e1, m1⟩ := xx
    rw [hc, cdK1_some] at h
    obtain ⟨b1, a1, hb1, hr1, hS1, hg1, hP1, hL1⟩ := cvceW_ok k hc hS (by rw [p1]; exact hcp)
      (by rw [q1]; exact hcq) hP hL
    simp only [beq_self_eq_true, if_true]
    obtain ⟨b, a', hb, hr, hq⟩ := andThen_st (Q := CQ dn vis fe m m') (A := cv.canonEq cv')
      (B := (do let cs ← ConRon.Arena.canonNames cv.levelParams.length
                ConRon.Arena.canonExprEq cv.levelParams cv'.levelParams cs coreWalkFuel v v' : AM Bool))
      hb1 hr1
      (fun hne1 => by
        rw [if_neg hne1] at h
        cases hx : ctxW k m1 (p + 1) (q + 1) with
        | none => rw [hx] at h; simp [cdK2] at h
        | some x2 =>
        obtain ⟨rc, m2⟩ := x2
        rw [hx, cdK2_some] at h
        have hcp1 : decCV (erecP m1) (p + 1).toNat = some cv :=
          ArrExt.decCV (IWGrow.erecPExtR hg1) (by rw [p1]; exact hcp)
        have hcq1 : decCV (erecP m1) (q + 1).toNat = some cv' :=
          ArrExt.decCV (IWGrow.erecPExtR hg1) (by rw [q1]; exact hcq)
        obtain ⟨cs, a2, po, pl, qo, ql, co, cl, hrc, hrun, hS2, hg2, hP2, hL2, hC2⟩ :=
          ctxW_ok k hx hS1 hcp1 hcq1 hP1 hL1
        subst hrc
        simp only [List.headD_cons, List.tail_cons] at h
        have hsz2 : (m2.arr64 EREC).size < 2 ^ 64 := hS2.2.2.2.2.1
        have hgg : IWGrow m m2 := hg1.trans hg2
        obtain ⟨wv, ev, hv32, hvd⟩ := hdW_ (a := erA m2) (q := p) (k := 5) (kn := 5) hsz2 rfl
          (ArrExt.hd? (IWGrow.erecExt hgg) hvp)
        obtain ⟨wv', ev', hv32', hvd'⟩ := hdW_ (a := erA m2) (q := q) (k := 5) (kn := 5) hsz2 rfl
          (ArrExt.hd? (IWGrow.erecExt hgg) hvq)
        simp only [erA] at ev ev'
        rw [ev, ev'] at h
        obtain ⟨b3, hb3, hr3, hS3, hg3, hP3⟩ := ceW_ok k m2 m' a2 po pl qo ql co cl 4000000000 wv wv' x
          cv.levelParams cv'.levelParams cs h hS2 hC2 hL2 hP2 hv32 hv32'
        refine ⟨b3, a2, ?_, hr3, hS3, hgg.trans hg3, hP3, hL2⟩
        rw [StateT.run_bind, hrun, exc_ok_bind']
        rw [fuelW] at hb3
        rw [hvd, hvd']
        exact hb3)
      (fun h0 => by
        rw [if_pos h0] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        exact ⟨rfl, hS1, hg1, hP1, hL1⟩)
    exact ⟨b, a', hb, hr, hq⟩
  · have hB0 : (if hintEqB (m.arr64 EREC) (p + 6) (q + 6) = true then (1 : Word) else 0) = 0 := by
      simp [hbB]
    rw [if_pos hB0] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hne : hi ≠ hi' := fun e => hbB (by rw [hB]; exact decide_eq_true e)
    have hcond : (hi == hi') = false := by simpa using hne
    rw [hcond]
    exact ⟨false, a, rfl, rfl, hS, IWGrow.refl _, hP, hL⟩

end L.Ind
