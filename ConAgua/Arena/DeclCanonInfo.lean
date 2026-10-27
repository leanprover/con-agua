import ConAgua.Arena.DeclCanonRules
import ConAgua.Arena.DeclCanonConst
import ConAgua.Arena.DeclCanonSpec2
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr

/-!
# `ci_canon_defn`, `ci_canon_rec`, `ci_canon_eq`, `canon_eq_list` (lane `decls3`, helper `decls3-canon`)
-/

set_option experimental.vcgen true

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
  rw [invoke_eq _ (hp.get "ci_canon_defn")]
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
      ⟨-, c, mi, rp, o, c', rules, hc, hmi, hrp, ho, hc', hr, hx⟩ <;>
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
    rw [ite_eq_right hne] at h
    cases hc : cvceW k m (p + 1) (q + 1) with
    | none => rw [hc] at h; simp [cdK1] at h
    | some xx =>
    obtain ⟨e1, m1⟩ := xx
    rw [hc, cdK1_some] at h
    obtain ⟨b1, a1, hb1, hr1, hS1, hg1, hP1, hL1⟩ := cvceW_ok k hc hS (by rw [p1]; exact hcp)
      (by rw [q1]; exact hcq) hP hL
    simp only [beq_self_eq_true, ite_true]
    obtain ⟨b, a', hb, hr, hq⟩ := andThen_st (Q := CQ dn vis fe m m') (A := cv.canonEq cv')
      (B := (do let cs ← ConRon.Arena.canonNames cv.levelParams.length
                ConRon.Arena.canonExprEq cv.levelParams cv'.levelParams cs coreWalkFuel v v' : AM Bool))
      hb1 hr1
      (fun hne1 => by
        rw [ite_eq_right hne1] at h
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
        rw [ite_eq_left h0] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        exact ⟨rfl, hS1, hg1, hP1, hL1⟩)
    exact ⟨b, a', hb, hr, hq⟩
  · have hB0 : (if hintEqB (m.arr64 EREC) (p + 6) (q + 6) = true then (1 : Word) else 0) = 0 := by
      simp [hbB]
    rw [ite_eq_left hB0] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hne : hi ≠ hi' := fun e => hbB (by rw [hB]; exact decide_eq_true e)
    have hcond : (hi == hi') = false := by simpa using hne
    rw [hcond]
    exact ⟨false, a, rfl, rfl, hS, IWGrow.refl _, hP, hL⟩


/-! ## `ci_canon_rec` -/

mutual
/-- **The model of `ci_canon_rec(p, q)`**. -/
def cwW : Nat → Mem → Word → Word → Option (Word × Mem)
  | 0, _, _, _ => none
  | k + 1, m, p, q =>
    if rdW (m.arr64 EREC) (p + 5) ≠ rdW (m.arr64 EREC) (q + 5) ∨
        rdW (m.arr64 EREC) (p + 6) ≠ rdW (m.arr64 EREC) (q + 6) then some (0, m)
    else cwK1 k p q (cvceW k m (p + 1) (q + 1))

/-- After `cv_canon_eq`. -/
def cwK1 (k : Nat) (p q : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (e, m1) => if e = 0 then some (0, m1) else cwK2 k p q (ctxW k m1 (p + 1) (q + 1))

/-- After `canon_ctx`. -/
def cwK2 (k : Nat) (p q : Word) : Option (List Word × Mem) → Option (Word × Mem)
  | none => none
  | some (rc, m2) =>
    cnCrW k m2 (rc.headD 0) (rc.tail.headD 0) (rc.tail.tail.headD 0) (rc.tail.tail.tail.headD 0)
      (rc.tail.tail.tail.tail.headD 0) (rc.tail.tail.tail.tail.tail.headD 0) 4000000000
      (rdW (m2.arr64 EREC) (p + 7)) (rdW (m2.arr64 EREC) (p + 8))
      (rdW (m2.arr64 EREC) (q + 7)) (rdW (m2.arr64 EREC) (q + 8))
end

section arms
variable (k : Nat) (m m1 m2 : Mem) (p q e : Word) (rc : List Word)
theorem cwW_succ : cwW (k + 1) m p q =
    (if rdW (m.arr64 EREC) (p + 5) ≠ rdW (m.arr64 EREC) (q + 5) ∨
        rdW (m.arr64 EREC) (p + 6) ≠ rdW (m.arr64 EREC) (q + 6) then some (0, m)
    else cwK1 k p q (cvceW k m (p + 1) (q + 1))) := by rw [cwW]
theorem cwK1_some : cwK1 k p q (some (e, m1)) =
    (if e = 0 then some (0, m1) else cwK2 k p q (ctxW k m1 (p + 1) (q + 1))) := by rw [cwK1]
theorem cwK2_some : cwK2 k p q (some (rc, m2)) =
    cnCrW k m2 (rc.headD 0) (rc.tail.headD 0) (rc.tail.tail.headD 0) (rc.tail.tail.tail.headD 0)
      (rc.tail.tail.tail.tail.headD 0) (rc.tail.tail.tail.tail.tail.headD 0) 4000000000
      (rdW (m2.arr64 EREC) (p + 7)) (rdW (m2.arr64 EREC) (p + 8))
      (rdW (m2.arr64 EREC) (q + 7)) (rdW (m2.arr64 EREC) (q + 8)) := by rw [cwK2]
end arms

grind_pattern [ind_grind] cwW_succ => cwW (k + 1) m p q
grind_pattern [ind_grind] cwK1_some => cwK1 k p q (some (e, m1))
grind_pattern [ind_grind] cwK2_some => cwK2 k p q (some (rc, m2))

theorem ciCanonRec_spec (pr : Prog) (hp : CanonProg pr) (n : Nat) (s₀ : St) (p q : Word) :
    ⦃fun s => s = s₀⦄ invoke pr (exec pr n) "ci_canon_rec" [p, q]
    ⦃fun x s' => LocEq s' s₀ ∧ cwW n s₀.mem p q = some (x.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "ci_canon_rec")]
  simp only [callFn, ciCanonRec]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        cvCanonEq_spec pr hp n, canonCtx_spec pr hp n, canonRulesEq_spec pr hp n] <;>
      finish (gen := 20) [cwW]


theorem ciD_rec {a : Array Word} {dn : NIdx → Option ConLeche.Name} {p : Nat} {cv : IConstantVal}
    {mi rp : Nat} {rules : List IRecRule} (h : decCI a dn p = some (.recInfo cv mi rp rules)) :
    decCV a (p + 1) = some cv ∧ nat? a (p + 5) = some mi ∧ nat? a (p + 6) = some rp ∧
    ∃ o c, nat? a (p + 7) = some o ∧ nat? a (p + 8) = some c ∧ decRules a o c = some rules := by
  obtain ⟨wk, e, hk⟩ := ciD h
  rcases hk with ⟨-, c, hc, hx⟩ | ⟨-, c, v', hi', hc, hv, hh, hx⟩ | ⟨-, c, hc, hx⟩ |
      ⟨-, c, caps, hc, hcaps, hx⟩ | ⟨-, c, np, nf, hc, hnp, hnf, hx⟩ |
      ⟨-, c, mi', rp', o, c', rules', hc, hmi, hrp, ho, hc', hr, hx⟩ <;>
    (cases hx <;> first | exact ⟨hc, hmi, hrp, o, c', ho, hc', hr⟩ | skip)

theorem cwW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} (k : Nat)
    {m m' : Mem} {p q x : Word} {cv cv' : IConstantVal} {mi mi' rp rp' : Nat}
    {rules rules' : List IRecRule}
    (h : cwW k m p q = some (x, m')) (hS : StageR dn vis fe m a)
    (hp : decCI (erecP m) dn p.toNat = some (.recInfo cv mi rp rules))
    (hq : decCI (erecP m) dn q.toNat = some (.recInfo cv' mi' rp' rules'))
    (hP : PoolSmall m) (hL : LitInj a) :
    ∃ (b : Bool) (a' : AState),
      (IConstantInfo.canonEq (.recInfo cv mi rp rules) (.recInfo cv' mi' rp' rules')).run a =
        .ok (b, a') ∧ x = (if b then 1 else 0) ∧ CQ dn vis fe m m' a' := by
  cases k with
  | zero => simp [cwW] at h
  | succ k =>
  rw [cwW_succ] at h
  obtain ⟨hcp, hmp, hrp, o1, l1, ho1, hl1, hrs⟩ := ciD_rec hp
  obtain ⟨hcq, hmq, hrq, o2, l2, ho2, hl2, hrs'⟩ := ciD_rec hq
  have hsz : (m.arr64 EREC).size < 2 ^ 64 := hS.2.2.2.2.1
  have hsz' : (erecP m).size < 2 ^ 64 := Nat.lt_of_le_of_lt (by simp [erecP]; exact Nat.min_le_right _ _) hsz
  obtain ⟨w1, hw1, -⟩ := decCV_name hcp
  obtain ⟨u1, hu1, -⟩ := decCV_name hcq
  have p1 : (p + 1).toNat = p.toNat + 1 := toNat_add_of_get hsz' (k := 1) (kn := 1) rfl hw1
  have q1 : (q + 1).toNat = q.toNat + 1 := toNat_add_of_get hsz' (k := 1) (kn := 1) rfl hu1
  obtain ⟨wm, em, rfl⟩ := natW_ (a := erA m) (q := p) (k := 5) (kn := 5) hsz rfl
    (ArrExt.nat? (erecP_ext m) hmp)
  obtain ⟨wm', em', rfl⟩ := natW_ (a := erA m) (q := q) (k := 5) (kn := 5) hsz rfl
    (ArrExt.nat? (erecP_ext m) hmq)
  obtain ⟨wr, er, rfl⟩ := natW_ (a := erA m) (q := p) (k := 6) (kn := 6) hsz rfl
    (ArrExt.nat? (erecP_ext m) hrp)
  obtain ⟨wr', er', rfl⟩ := natW_ (a := erA m) (q := q) (k := 6) (kn := 6) hsz rfl
    (ArrExt.nat? (erecP_ext m) hrq)
  simp only [erA] at em em' er er'
  simp only [IConstantInfo.canonEq]
  rw [em, em', er, er'] at h
  by_cases hc : wm ≠ wm' ∨ wr ≠ wr'
  · rw [ite_eq_left hc] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hb : (wm.toNat == wm'.toNat && wr.toNat == wr'.toNat) = false := by
      rcases hc with hc | hc
      · have : (wm.toNat == wm'.toNat) = false := by
          simpa using fun e => hc (UInt64.toNat_inj.mp e)
        simp [this]
      · have : (wr.toNat == wr'.toNat) = false := by
          simpa using fun e => hc (UInt64.toNat_inj.mp e)
        simp [this]
    rw [hb]
    exact ⟨false, a, rfl, rfl, hS, IWGrow.refl _, hP, hL⟩
  · rw [ite_eq_right hc] at h
    have hw : wm = wm' ∧ wr = wr' := by
      rw [not_or] at hc; exact ⟨Classical.byContradiction hc.1, Classical.byContradiction hc.2⟩
    obtain ⟨rfl, rfl⟩ := hw
    simp only [beq_self_eq_true, Bool.and_self, ite_true]
    cases hc1 : cvceW k m (p + 1) (q + 1) with
    | none => rw [hc1] at h; simp [cwK1] at h
    | some xx =>
    obtain ⟨e1, m1⟩ := xx
    rw [hc1, cwK1_some] at h
    obtain ⟨b1, a1, hb1, hr1, hS1, hg1, hP1, hL1⟩ := cvceW_ok k hc1 hS (by rw [p1]; exact hcp)
      (by rw [q1]; exact hcq) hP hL
    obtain ⟨b, a', hb, hr, hq⟩ := andThen_st (Q := CQ dn vis fe m m') (A := cv.canonEq cv')
      (B := (do let cs ← ConRon.Arena.canonNames cv.levelParams.length
                ConRon.Arena.canonRulesEq cv.levelParams cv'.levelParams cs coreWalkFuel rules rules' : AM Bool))
      hb1 hr1
      (fun hne1 => by
        rw [ite_eq_right hne1] at h
        cases hx : ctxW k m1 (p + 1) (q + 1) with
        | none => rw [hx] at h; simp [cwK2] at h
        | some x2 =>
        obtain ⟨rc, m2⟩ := x2
        rw [hx, cwK2_some] at h
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
        obtain ⟨wa, ea, rfl⟩ := natW_ (a := erA m2) (q := p) (k := 7) (kn := 7) hsz2 rfl
          (ArrExt.nat? (IWGrow.erecExt hgg) ho1)
        obtain ⟨wb, eb, rfl⟩ := natW_ (a := erA m2) (q := p) (k := 8) (kn := 8) hsz2 rfl
          (ArrExt.nat? (IWGrow.erecExt hgg) hl1)
        obtain ⟨wc, ec, rfl⟩ := natW_ (a := erA m2) (q := q) (k := 7) (kn := 7) hsz2 rfl
          (ArrExt.nat? (IWGrow.erecExt hgg) ho2)
        obtain ⟨wd, ed, rfl⟩ := natW_ (a := erA m2) (q := q) (k := 8) (kn := 8) hsz2 rfl
          (ArrExt.nat? (IWGrow.erecExt hgg) hl2)
        simp only [erA] at ea eb ec ed
        rw [ea, eb, ec, ed] at h
        obtain ⟨b3, hb3, hr3, hS3, hg3, hP3⟩ := cnCrW_ok k m2 m' a2 po pl qo ql co cl 4000000000 wa wb wc wd x
          cv.levelParams cv'.levelParams cs rules rules' h hS2 hC2 hL2 hP2
          (ArrExt.decRules (IWGrow.erecPExtR hgg) hrs) (ArrExt.decRules (IWGrow.erecPExtR hgg) hrs')
        refine ⟨b3, a2, ?_, hr3, hS3, hgg.trans hg3, hP3, hL2⟩
        rw [StateT.run_bind, hrun, exc_ok_bind']
        rw [fuelW] at hb3
        exact hb3)
      (fun h0 => by
        rw [ite_eq_left h0] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        exact ⟨rfl, hS1, hg1, hP1, hL1⟩)
    exact ⟨b, a', hb, hr, hq⟩


/-! ## `ci_canon_eq` -/

/-- **The model of `ci_canon_eq(p, q)`**. -/
def cieW : Nat → Mem → Word → Word → Option (Word × Mem)
  | 0, _, _, _ => none
  | k + 1, m, p, q =>
    if rdW (m.arr64 EREC) p ≠ rdW (m.arr64 EREC) q then some (0, m)
    else if 5 < rdW (m.arr64 EREC) p then none
    else if rdW (m.arr64 EREC) p = 1 then cdW k m p q
    else if rdW (m.arr64 EREC) p = 4 ∧ (rdW (m.arr64 EREC) (p + 5) ≠ rdW (m.arr64 EREC) (q + 5) ∨
        rdW (m.arr64 EREC) (p + 6) ≠ rdW (m.arr64 EREC) (q + 6)) then some (0, m)
    else if rdW (m.arr64 EREC) p = 5 then cwW k m p q
    else cvceW k m (p + 1) (q + 1)

theorem cieW_succ (k : Nat) (m : Mem) (p q : Word) : cieW (k + 1) m p q =
    (if rdW (m.arr64 EREC) p ≠ rdW (m.arr64 EREC) q then some (0, m)
    else if 5 < rdW (m.arr64 EREC) p then none
    else if rdW (m.arr64 EREC) p = 1 then cdW k m p q
    else if rdW (m.arr64 EREC) p = 4 ∧ (rdW (m.arr64 EREC) (p + 5) ≠ rdW (m.arr64 EREC) (q + 5) ∨
        rdW (m.arr64 EREC) (p + 6) ≠ rdW (m.arr64 EREC) (q + 6)) then some (0, m)
    else if rdW (m.arr64 EREC) p = 5 then cwW k m p q
    else cvceW k m (p + 1) (q + 1)) := rfl

grind_pattern [ind_grind] cieW_succ => cieW (k + 1) m p q

theorem ciCanonEq_spec (pr : Prog) (hp : CanonProg pr) (n : Nat) (s₀ : St) (p q : Word) :
    ⦃fun s => s = s₀⦄ invoke pr (exec pr n) "ci_canon_eq" [p, q]
    ⦃fun x s' => LocEq s' s₀ ∧ cieW n s₀.mem p q = some (x.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "ci_canon_eq")]
  simp only [callFn, ciCanonEq]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        ciCanonDefn_spec pr hp n, ciCanonRec_spec pr hp n,
        cvCanonEq_spec pr hp n] <;>
      finish (gen := 20)


theorem cieW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {a : AState} (k : Nat) {m m' : Mem} {p q x : Word} {c c' : IConstantInfo}
    (h : cieW k m p q = some (x, m')) (hS : StageR dn vis fe m a)
    (hp : decCI (erecP m) dn p.toNat = some c) (hq : decCI (erecP m) dn q.toNat = some c')
    (hP : PoolSmall m) (hL : LitInj a) :
    ∃ (b : Bool) (a' : AState), (c.canonEq c').run a = .ok (b, a') ∧ x = (if b then 1 else 0) ∧
      CQ dn vis fe m m' a' := by
  cases k with
  | zero => simp [cieW] at h
  | succ k =>
  rw [cieW_succ] at h
  have hsz : (m.arr64 EREC).size < 2 ^ 64 := hS.2.2.2.2.1
  have hsz' : (erecP m).size < 2 ^ 64 := Nat.lt_of_le_of_lt (by simp [erecP]; exact Nat.min_le_right _ _) hsz
  obtain ⟨wk, e, hx⟩ := ciD hp
  obtain ⟨wk', e', hy⟩ := ciD hq
  have r1 : rdW (m.arr64 EREC) p = wk := rdW_zero' (erecP_rd e)
  have r2 : rdW (m.arr64 EREC) q = wk' := rdW_zero' (erecP_rd e')
  rw [r1, r2] at h
  have wl : ∀ (w : Word) (n : Nat) (hn : n < 2 ^ 64), w.toNat = n → w = UInt64.ofNat n := fun w n hn h =>
    UInt64.toNat_inj.mp (by rw [h]; simp [UInt64.toNat_ofNat_of_lt' hn])
  rcases hx with ⟨k0, cv, hcv, rfl⟩ | ⟨k0, cv, v, hi, hcv, hv, hhi, rfl⟩ | ⟨k0, cv, hcv, rfl⟩ |
      ⟨k0, cv, caps, hcv, hcaps, rfl⟩ | ⟨k0, cv, np, nf, hcv, hnp, hnf, rfl⟩ |
      ⟨k0, cv, mi, rp, o, cc, rules, hcv, hmi, hrp, ho, hcc, hr, rfl⟩ <;>
  rcases hy with ⟨k1, cv', hcv', rfl⟩ | ⟨k1, cv', v', hi', hcv', hv', hhi', rfl⟩ | ⟨k1, cv', hcv', rfl⟩ |
      ⟨k1, cv', caps', hcv', hcaps', rfl⟩ | ⟨k1, cv', np', nf', hcv', hnp', hnf', rfl⟩ |
      ⟨k1, cv', mi', rp', o', cc', rules', hcv', hmi', hrp', ho', hcc', hr', rfl⟩
  all_goals first
    | (have hne : wk ≠ wk' := fun h => by have := congrArg UInt64.toNat h; omega
       rw [ite_eq_left hne] at h
       obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
       exact ⟨false, a, by simp [IConstantInfo.canonEq]; rfl, rfl, hS, IWGrow.refl _, hP, hL⟩)
    | skip
  · -- axiom
    have e0 := wl wk 0 (by decide) k0
    have e1 := wl wk' 0 (by decide) k1
    subst e0 e1
    simp (config := { decide := true }) only [ne_eq, ↓reduceIte, false_and] at h
    have p1 : (p + 1).toNat = p.toNat + 1 := by
      obtain ⟨w1, hw1, -⟩ := decCV_name hcv
      exact toNat_add_of_get hsz' (k := 1) (kn := 1) rfl hw1
    have q1 : (q + 1).toNat = q.toNat + 1 := by
      obtain ⟨w1, hw1, -⟩ := decCV_name hcv'
      exact toNat_add_of_get hsz' (k := 1) (kn := 1) rfl hw1
    obtain ⟨b, a', hb, hr, hq⟩ := cvceW_ok k h hS (by rw [p1]; exact hcv) (by rw [q1]; exact hcv') hP hL
    exact ⟨b, a', by simp only [IConstantInfo.canonEq]; exact hb, hr, hq⟩
  · -- defn
    have e0 := wl wk 1 (by decide) k0
    have e1 := wl wk' 1 (by decide) k1
    subst e0 e1
    simp (config := { decide := true }) only [↓reduceIte] at h
    obtain ⟨b, a', hb, hr, hq⟩ := cdW_ok k h hS hp hq hP hL
    exact ⟨b, a', hb, hr, hq⟩
  · -- thm
    have e0 := wl wk 2 (by decide) k0
    have e1 := wl wk' 2 (by decide) k1
    subst e0 e1
    simp (config := { decide := true }) only [ne_eq, ↓reduceIte, false_and] at h
    have p1 : (p + 1).toNat = p.toNat + 1 := by
      obtain ⟨w1, hw1, -⟩ := decCV_name hcv
      exact toNat_add_of_get hsz' (k := 1) (kn := 1) rfl hw1
    have q1 : (q + 1).toNat = q.toNat + 1 := by
      obtain ⟨w1, hw1, -⟩ := decCV_name hcv'
      exact toNat_add_of_get hsz' (k := 1) (kn := 1) rfl hw1
    obtain ⟨b, a', hb, hr, hq⟩ := cvceW_ok k h hS (by rw [p1]; exact hcv) (by rw [q1]; exact hcv') hP hL
    exact ⟨b, a', by simp only [IConstantInfo.canonEq]; exact hb, hr, hq⟩
  · -- ind
    have e0 := wl wk 3 (by decide) k0
    have e1 := wl wk' 3 (by decide) k1
    subst e0 e1
    simp (config := { decide := true }) only [ne_eq, ↓reduceIte, false_and] at h
    have p1 : (p + 1).toNat = p.toNat + 1 := by
      obtain ⟨w1, hw1, -⟩ := decCV_name hcv
      exact toNat_add_of_get hsz' (k := 1) (kn := 1) rfl hw1
    have q1 : (q + 1).toNat = q.toNat + 1 := by
      obtain ⟨w1, hw1, -⟩ := decCV_name hcv'
      exact toNat_add_of_get hsz' (k := 1) (kn := 1) rfl hw1
    obtain ⟨b, a', hb, hr, hq⟩ := cvceW_ok k h hS (by rw [p1]; exact hcv) (by rw [q1]; exact hcv') hP hL
    exact ⟨b, a', by simp only [IConstantInfo.canonEq]; exact hb, hr, hq⟩
  · -- ctor
    have e0 := wl wk 4 (by decide) k0
    have e1 := wl wk' 4 (by decide) k1
    subst e0 e1
    simp (config := { decide := true }) only [ne_eq, ↓reduceIte, true_and] at h
    have p1 : (p + 1).toNat = p.toNat + 1 := by
      obtain ⟨w1, hw1, -⟩ := decCV_name hcv
      exact toNat_add_of_get hsz' (k := 1) (kn := 1) rfl hw1
    have q1 : (q + 1).toNat = q.toNat + 1 := by
      obtain ⟨w1, hw1, -⟩ := decCV_name hcv'
      exact toNat_add_of_get hsz' (k := 1) (kn := 1) rfl hw1
    obtain ⟨wa, ea, rfl⟩ := natW_ (a := erA m) (q := p) (k := 5) (kn := 5) hsz rfl
      (ArrExt.nat? (erecP_ext m) hnp)
    obtain ⟨wb, eb, rfl⟩ := natW_ (a := erA m) (q := p) (k := 6) (kn := 6) hsz rfl
      (ArrExt.nat? (erecP_ext m) hnf)
    obtain ⟨wc, ec, rfl⟩ := natW_ (a := erA m) (q := q) (k := 5) (kn := 5) hsz rfl
      (ArrExt.nat? (erecP_ext m) hnp')
    obtain ⟨wd, ed, rfl⟩ := natW_ (a := erA m) (q := q) (k := 6) (kn := 6) hsz rfl
      (ArrExt.nat? (erecP_ext m) hnf')
    simp only [erA] at ea eb ec ed
    rw [ea, eb, ec, ed] at h
    by_cases hc : wa ≠ wc ∨ wb ≠ wd
    · rw [ite_eq_left hc] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hbb : (wa.toNat == wc.toNat && wb.toNat == wd.toNat) = false := by
        rcases hc with hc | hc
        · have : (wa.toNat == wc.toNat) = false := by
            simpa using fun e => hc (UInt64.toNat_inj.mp e)
          simp [this]
        · have : (wb.toNat == wd.toNat) = false := by
            simpa using fun e => hc (UInt64.toNat_inj.mp e)
          simp [this]
      refine ⟨false, a, ?_, rfl, hS, IWGrow.refl _, hP, hL⟩
      simp only [IConstantInfo.canonEq]
      rw [hbb]; rfl
    · rw [ite_eq_right hc] at h
      have hw : wa = wc ∧ wb = wd := by
        rw [not_or] at hc; exact ⟨Classical.byContradiction hc.1, Classical.byContradiction hc.2⟩
      obtain ⟨rfl, rfl⟩ := hw
      obtain ⟨b, a', hb, hr, hq⟩ := cvceW_ok k h hS (by rw [p1]; exact hcv) (by rw [q1]; exact hcv') hP hL
      refine ⟨b, a', ?_, hr, hq⟩
      simp only [IConstantInfo.canonEq, beq_self_eq_true, Bool.and_self, ite_true]
      exact hb
  · -- rec
    have e0 := wl wk 5 (by decide) k0
    have e1 := wl wk' 5 (by decide) k1
    subst e0 e1
    simp (config := { decide := true }) only [ne_eq, ↓reduceIte, false_and] at h
    obtain ⟨b, a', hb, hr, hq⟩ := cwW_ok k h hS hp hq hP hL
    exact ⟨b, a', hb, hr, hq⟩


/-- **`ci_canon_eq` refines `IConstantInfo.canonEq`.** -/
@[refines ConRon.Arena.IConstantInfo.canonEq]
theorem ciCanonEq_refines (pr : Prog) (hp : CanonProg pr) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (p q : Word) (c c' : IConstantInfo) :
    RefAM pr "ci_canon_eq" [p, q]
      (fun m a => StageR dn vis fe m a ∧ decCI (erecP m) dn p.toNat = some c ∧
        decCI (erecP m) dn q.toNat = some c' ∧ PoolSmall m ∧ LitInj a)
      (c.canonEq c') (CPostL dn vis fe decW0B) := by
  intro n s₀ a₀ ⟨hS, hc, hc', hP, hL⟩
  refine triple_post (ciCanonEq_spec pr hp n s₀ p q) ?_
  rintro x s' ⟨hl, hx⟩
  obtain ⟨b, a', hb, hrb, hS', hg, hP', hL'⟩ := cieW_ok n hx hS hc hc' hP hL
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hb
  refine ⟨hl, hok, ?_⟩
  rw [hst, hres]
  exact ⟨⟨⟨hS', hg, decW0B_of' hrb⟩, hP'⟩, hL'⟩

/-! ## `canon_eq_list` -/

mutual
/-- **The model of `canon_eq_list(o, l, o', l')`**. -/
def celW : Nat → Mem → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _ => none
  | k + 1, m, o1, l1, o2, l2 =>
    if l1 = 0 ∧ l2 = 0 then some (1, m)
    else if l1 = 0 ∨ l2 = 0 then some (0, m)
    else celK1 k o1 l1 o2 l2 (cieW k m (rdW (m.arr64 IW) o1) (rdW (m.arr64 IW) o2))

/-- After `ci_canon_eq`. -/
def celK1 (k : Nat) (o1 l1 o2 l2 : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (e, m1) => if e = 0 then some (0, m1) else celW k m1 (o1 + 1) (l1 - 1) (o2 + 1) (l2 - 1)
end

section arms
variable (k : Nat) (m m1 : Mem) (o1 l1 o2 l2 e : Word)
theorem celW_succ : celW (k + 1) m o1 l1 o2 l2 =
    (if l1 = 0 ∧ l2 = 0 then some (1, m)
    else if l1 = 0 ∨ l2 = 0 then some (0, m)
    else celK1 k o1 l1 o2 l2 (cieW k m (rdW (m.arr64 IW) o1) (rdW (m.arr64 IW) o2))) := by rw [celW]
theorem celK1_some : celK1 k o1 l1 o2 l2 (some (e, m1)) =
    (if e = 0 then some (0, m1) else celW k m1 (o1 + 1) (l1 - 1) (o2 + 1) (l2 - 1)) := by
  rw [celK1]
end arms

grind_pattern [ind_grind] celW_succ => celW (k + 1) m o1 l1 o2 l2
grind_pattern [ind_grind] celK1_some => celK1 k o1 l1 o2 l2 (some (e, m1))

theorem canonEqListL_spec (pr : Prog) (hp : CanonProg pr) (n : Nat) :
    ∀ (s₀ : St) (o1 l1 o2 l2 : Word),
    ⦃fun s => s = s₀⦄ invoke pr (exec pr n) "canon_eq_list" [o1, l1, o2, l2]
    ⦃fun x s' => LocEq s' s₀ ∧ celW n s₀.mem o1 l1 o2 l2 = some (x.headD 0, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ o1 l1 o2 l2
    rw [invoke_eq _ (hp.get "canon_eq_list")]; simp only [callFn, canonEqListL]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o1 l1 o2 l2
    rw [invoke_eq _ (hp.get "canon_eq_list")]
    simp only [callFn, canonEqListL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        ciCanonEq_spec pr hp n, ih] <;>
      finish (gen := 20) [rdW_eq]


theorem decPL_zero {α : Type} (m : Mem) (f : Nat → Option α) (o : Nat) : decPL m f o 0 = some [] := by
  simp [decPL]

/-- A pointer slice stays decoded when the pool grows (below its top) and the record decoder
only gains. -/
theorem decPL_grow {α : Type} {m m' : Mem} {f f' : Nat → Option α} (hg : IWGrow m m')
    (hf : ∀ q x, f q = some x → f' q = some x) :
    ∀ (c o : Nat) (xs : List α), o + c ≤ iwTop m → decPL m f o c = some xs →
    decPL m' f' o c = some xs := by
  intro c
  induction c with
  | zero => intro o xs _ h; rw [decPL_zero] at h ⊢; exact h
  | succ c ih =>
    intro o xs hb h
    rw [decPL_succ] at h ⊢
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h ⊢
    obtain ⟨v, hv, x, hfx, xs', hxs, rfl⟩ := h
    refine ⟨v, ?_, x, hf v x hfx, xs', ih (o + 1) xs' (by omega) hxs, rfl⟩
    simp only [iwN, nat?, iwA] at hv ⊢
    rw [hg.2.2.1 o (by omega)]; exact hv


theorem celW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (o1 l1 o2 l2 x : Word) (xs ys : List IConstantInfo),
    celW k m o1 l1 o2 l2 = some (x, m') → StageR dn vis fe m a →
    decPL m (fun q => decCI (erecP m) dn q) o1.toNat l1.toNat = some xs →
    decPL m (fun q => decCI (erecP m) dn q) o2.toNat l2.toNat = some ys →
    o1.toNat + l1.toNat ≤ iwTop m → o2.toNat + l2.toNat ≤ iwTop m → PoolSmall m → LitInj a →
    ∃ (b : Bool) (a' : AState), (ConRon.Arena.canonEqList xs ys).run a = .ok (b, a') ∧
      x = (if b then 1 else 0) ∧ CQ dn vis fe m m' a' := by
  induction k with
  | zero => intro m m' a o1 l1 o2 l2 x xs ys h; simp [celW] at h
  | succ k ih =>
    intro m m' a o1 l1 o2 l2 x xs ys h hS hxs hys hb1 hb2 hP hL
    rw [celW_succ] at h
    have lx := decPL_length (m := m) hxs
    have ly := decPL_length (m := m) hys
    by_cases h0 : l1 = 0 ∧ l2 = 0
    · rw [ite_eq_left h0] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have e1 : xs = [] := List.length_eq_zero_iff.mp (by rw [lx, h0.1]; rfl)
      have e2 : ys = [] := List.length_eq_zero_iff.mp (by rw [ly, h0.2]; rfl)
      subst e1 e2
      exact ⟨true, a, by simp [ConRon.Arena.canonEqList]; rfl, rfl, hS, IWGrow.refl _, hP, hL⟩
    rw [ite_eq_right h0] at h
    by_cases h1 : l1 = 0 ∨ l2 = 0
    · rw [ite_eq_left h1] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      refine ⟨false, a, ?_, rfl, hS, IWGrow.refl _, hP, hL⟩
      rcases xs with _ | ⟨x1, xs'⟩ <;> rcases ys with _ | ⟨y1, ys'⟩
      · exfalso; apply h0
        refine ⟨UInt64.toNat_inj.mp (by simpa using lx.symm), UInt64.toNat_inj.mp (by simpa using ly.symm)⟩
      · simp [ConRon.Arena.canonEqList]; rfl
      · simp [ConRon.Arena.canonEqList]; rfl
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
    have t := iwTop_lt m
    rw [l1e, decPL_succ] at hxs
    rw [l2e, decPL_succ] at hys
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hxs hys
    obtain ⟨v1, hv1, x1', hx1, xs'', hxs', hxeq⟩ := hxs
    obtain ⟨v2, hv2, y1', hy1, ys'', hys', hyeq⟩ := hys
    obtain ⟨rfl, rfl⟩ := List.cons.inj hxeq
    obtain ⟨rfl, rfl⟩ := List.cons.inj hyeq
    obtain ⟨r1, hr1⟩ := iwN_rdW (m := m) (i := o1.toNat) hv1 (by omega)
    obtain ⟨r2, hr2⟩ := iwN_rdW (m := m) (i := o2.toNat) hv2 (by omega)
    have eo1 : UInt64.ofNat o1.toNat = o1 := UInt64.ofNat_toNat
    have eo2 : UInt64.ofNat o2.toNat = o2 := UInt64.ofNat_toNat
    rw [eo1] at r1
    rw [eo2] at r2
    rw [r1, r2] at h
    have hw1 : (UInt64.ofNat v1).toNat = v1 := by simp; omega
    have hw2 : (UInt64.ofNat v2).toNat = v2 := by simp; omega
    unfold celK1 at h
    cases hc : cieW k m (UInt64.ofNat v1) (UInt64.ofNat v2) with
    | none => rw [hc] at h; simp at h
    | some xx =>
    obtain ⟨e1, m1⟩ := xx
    rw [hc] at h
    dsimp only at h
    obtain ⟨b1, a1, hb1', hr1', hS1, hg1, hP1, hL1⟩ := cieW_ok k hc hS (by rw [hw1]; exact hx1)
      (by rw [hw2]; exact hy1) hP hL
    have o1e : (o1 + 1).toNat = o1.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have o2e : (o2 + 1).toNat = o2.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have l1p : (l1 - 1).toNat = xs''.length := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp [l1e]
    have l2p : (l2 - 1).toNat = ys''.length := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp [l2e]
    simp only [ConRon.Arena.canonEqList]
    obtain ⟨b, a', hb, hr, hq⟩ := andThen_st (Q := CQ dn vis fe m m') (A := ConRon.Arena.IConstantInfo.canonEq x1' y1')
      (B := ConRon.Arena.canonEqList xs'' ys'') hb1' hr1'
      (fun hne => by
        rw [ite_eq_right hne] at h
        have hx2 := decPL_grow hg1 (fun q x hq => ArrExt.decCI (IWGrow.erecPExtR hg1) hq) xs''.length
          (o1.toNat + 1) xs'' (by omega) hxs'
        have hy2 := decPL_grow hg1 (fun q x hq => ArrExt.decCI (IWGrow.erecPExtR hg1) hq) ys''.length
          (o2.toNat + 1) ys'' (by omega) hys'
        obtain ⟨b2, a2, hb2, hr2', hq2⟩ := ih m1 m' a1 (o1 + 1) (l1 - 1) (o2 + 1) (l2 - 1) x xs'' ys'' h hS1
          (by rw [o1e, l1p]; exact hx2) (by rw [o2e, l2p]; exact hy2)
          (by rw [o1e, l1p]; have := hg1.1; omega) (by rw [o2e, l2p]; have := hg1.1; omega) hP1 hL1
        exact ⟨b2, a2, hb2, hr2', hq2.1, hg1.trans hq2.2.1, hq2.2.2.1, hq2.2.2.2⟩)
      (fun h0 => by
        rw [ite_eq_left h0] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        exact ⟨rfl, hS1, hg1, hP1, hL1⟩)
    exact ⟨b, a', hb, hr, hq⟩


/-- **`canon_eq_list` refines `canonEqList`.** The records are `EREC` pointers in two `IW` slices
(decoded below the record pool's top, as the other record statements). -/
@[refines ConRon.Arena.canonEqList]
theorem canonEqList_refines (pr : Prog) (hp : CanonProg pr) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (o1 l1 o2 l2 : Word) (xs ys : List IConstantInfo) :
    RefAM pr "canon_eq_list" [o1, l1, o2, l2]
      (fun m a => StageR dn vis fe m a ∧
        decPL m (fun q => decCI (erecP m) dn q) o1.toNat l1.toNat = some xs ∧
        decPL m (fun q => decCI (erecP m) dn q) o2.toNat l2.toNat = some ys ∧
        o1.toNat + l1.toNat ≤ iwTop m ∧ o2.toNat + l2.toNat ≤ iwTop m ∧ PoolSmall m ∧ LitInj a)
      (ConRon.Arena.canonEqList xs ys) (CPostL dn vis fe decW0B) := by
  intro n s₀ a₀ ⟨hS, hxs, hys, hb1, hb2, hP, hL⟩
  refine triple_post (canonEqListL_spec pr hp n s₀ o1 l1 o2 l2) ?_
  rintro x s' ⟨hl, hx⟩
  obtain ⟨b, a', hb, hrb, hS', hg, hP', hL'⟩ := celW_ok n _ _ a₀ o1 l1 o2 l2 _ xs ys hx hS hxs hys
    hb1 hb2 hP hL
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hb
  refine ⟨hl, hok, ?_⟩
  rw [hst, hres]
  exact ⟨⟨⟨hS', hg, decW0B_of' hrb⟩, hP'⟩, hL'⟩

end L.Ind
