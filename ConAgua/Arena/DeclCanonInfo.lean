module

public import ConAgua.Arena.DeclCanonRules
public import ConAgua.Arena.DeclCanonConst
import ConAgua.Arena.DeclCanonSpec2
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.DeclCanonEq
import ConAgua.Arena.DeclRec
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.DeclArmsCanon

@[expose] public section

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
  StageR vis fe m' a' ∧ IWGrow m m' ∧ PoolSmall m' ∧ LitInj a'


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
  sorry


/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem ciD_defn {a : Array Word} {dn : NIdx → Option ConLeche.Name} {p : Nat} {cv : IConstantVal}
    {v : EIdx} {hi : ConLeche.ReducibilityHint} (h : decCI (aread a) p = some (.defnInfo cv v hi)) :
    decCV (aread a) (p + 1) = some cv ∧ hd? (aread a) (p + 5) = some v ∧ decHint (aread a) (p + 6) = some hi := by
  obtain ⟨wk, e, hk⟩ := ciD h
  rcases hk with ⟨-, c, hc, hx⟩ | ⟨-, c, v', hi', hc, hv, hh, hx⟩ | ⟨-, c, hc, hx⟩ |
      ⟨-, c, caps, hc, hcaps, hx⟩ | ⟨-, c, np, nf, hc, hnp, hnf, hx⟩ |
      ⟨-, c, mi, rp, o, c', rules, hc, hmi, hrp, ho, hc', hr, hx⟩ <;>
    (cases hx <;> first | exact ⟨hc, hv, hh⟩ | skip)
-/

theorem cdW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} (k : Nat)
    {m m' : Mem} {p q x : Word} {cv cv' : IConstantVal} {v v' : EIdx}
    {hi hi' : ConLeche.ReducibilityHint}
    (h : cdW k m p q = some (x, m')) (hS : StageR vis fe m a)
    (hp : decCI (erecP m) p.toNat = some (.defnInfo cv v hi))
    (hq : decCI (erecP m) q.toNat = some (.defnInfo cv' v' hi'))
    (hP : PoolSmall m) (hL : LitInj a) :
    ∃ (b : Bool) (a' : AState),
      (IConstantInfo.canonEq (.defnInfo cv v hi) (.defnInfo cv' v' hi')).run a = .ok (b, a') ∧
      x = (if b then 1 else 0) ∧ CQ dn vis fe m m' a' := by
  sorry


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
  sorry


/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem ciD_rec {a : Array Word} {dn : NIdx → Option ConLeche.Name} {p : Nat} {cv : IConstantVal}
    {mi rp : Nat} {rules : List IRecRule} (h : decCI (aread a) p = some (.recInfo cv mi rp rules)) :
    decCV (aread a) (p + 1) = some cv ∧ nat? (aread a) (p + 5) = some mi ∧ nat? (aread a) (p + 6) = some rp ∧
    ∃ o c, nat? (aread a) (p + 7) = some o ∧ nat? (aread a) (p + 8) = some c ∧ decRules (aread a) o c = some rules := by
  obtain ⟨wk, e, hk⟩ := ciD h
  rcases hk with ⟨-, c, hc, hx⟩ | ⟨-, c, v', hi', hc, hv, hh, hx⟩ | ⟨-, c, hc, hx⟩ |
      ⟨-, c, caps, hc, hcaps, hx⟩ | ⟨-, c, np, nf, hc, hnp, hnf, hx⟩ |
      ⟨-, c, mi', rp', o, c', rules', hc, hmi, hrp, ho, hc', hr, hx⟩ <;>
    (cases hx <;> first | exact ⟨hc, hmi, hrp, o, c', ho, hc', hr⟩ | skip)
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem cwW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} (k : Nat)
    {m m' : Mem} {p q x : Word} {cv cv' : IConstantVal} {mi mi' rp rp' : Nat}
    {rules rules' : List IRecRule}
    (h : cwW k m p q = some (x, m')) (hS : StageR vis fe m a)
    (hp : decCI (erecP m) p.toNat = some (.recInfo cv mi rp rules))
    (hq : decCI (erecP m) q.toNat = some (.recInfo cv' mi' rp' rules'))
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
  have hsz : (m.arr64 EREC).size < 2 ^ 64 := hS.iw.erSize
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
        have hsz2 : (m2.arr64 EREC).size < 2 ^ 64 := hS2.iw.erSize
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
-/


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
  sorry


theorem cieW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {a : AState} (k : Nat) {m m' : Mem} {p q x : Word} {c c' : IConstantInfo}
    (h : cieW k m p q = some (x, m')) (hS : StageR vis fe m a)
    (hp : decCI (erecP m) p.toNat = some c) (hq : decCI (erecP m) q.toNat = some c')
    (hP : PoolSmall m) (hL : LitInj a) :
    ∃ (b : Bool) (a' : AState), (c.canonEq c').run a = .ok (b, a') ∧ x = (if b then 1 else 0) ∧
      CQ dn vis fe m m' a' := by
  sorry


/-- **`ci_canon_eq` refines `IConstantInfo.canonEq`.** -/
@[refines ConRon.Arena.IConstantInfo.canonEq]
theorem ciCanonEq_refines (pr : Prog) (hp : CanonProg pr) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (p q : Word) (c c' : IConstantInfo) :
    RefAM pr "ci_canon_eq" [p, q]
      (fun m a => StageR vis fe m a ∧ decCI (erecP m) p.toNat = some c ∧
        decCI (erecP m) q.toNat = some c' ∧ PoolSmall m ∧ LitInj a)
      (c.canonEq c') (CPostL dn vis fe decW0B) := by
  sorry

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
  sorry


theorem celW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (o1 l1 o2 l2 x : Word) (xs ys : List IConstantInfo),
    celW k m o1 l1 o2 l2 = some (x, m') → StageR vis fe m a →
    decPL m (fun q => decCI (erecP m) q) o1.toNat l1.toNat = some xs →
    decPL m (fun q => decCI (erecP m) q) o2.toNat l2.toNat = some ys →
    o1.toNat + l1.toNat ≤ iwTop m → o2.toNat + l2.toNat ≤ iwTop m → PoolSmall m → LitInj a →
    ∃ (b : Bool) (a' : AState), (ConRon.Arena.canonEqList xs ys).run a = .ok (b, a') ∧
      x = (if b then 1 else 0) ∧ CQ dn vis fe m m' a' := by
  sorry


/-- **`canon_eq_list` refines `canonEqList`.** The records are `EREC` pointers in two `IW` slices
(decoded below the record pool's top, as the other record statements). -/
@[refines ConRon.Arena.canonEqList]
theorem canonEqList_refines (pr : Prog) (hp : CanonProg pr) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (o1 l1 o2 l2 : Word) (xs ys : List IConstantInfo) :
    RefAM pr "canon_eq_list" [o1, l1, o2, l2]
      (fun m a => StageR vis fe m a ∧
        decPL m (fun q => decCI (erecP m) q) o1.toNat l1.toNat = some xs ∧
        decPL m (fun q => decCI (erecP m) q) o2.toNat l2.toNat = some ys ∧
        o1.toNat + l1.toNat ≤ iwTop m ∧ o2.toNat + l2.toNat ≤ iwTop m ∧ PoolSmall m ∧ LitInj a)
      (ConRon.Arena.canonEqList xs ys) (CPostL dn vis fe decW0B) := by
  sorry

end L.Ind
