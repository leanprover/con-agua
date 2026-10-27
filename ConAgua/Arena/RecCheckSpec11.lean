import ConAgua.Arena.RecCheckSpec10
import ConAgua.Arena.IndRealAbsPos

/-!
# `RecCheck`: `targetParamsDefEq`, the relational side (lane `indproofs3`, helper `rec`)

The twin's list recursion split at the head: `tpClosed` (the closedness test), `tpRest` (canon
forms, abstraction, syntactic or inferred-and-defeq), `tpd_cons` (the recursion's `cons` arm is
`tpStep` then the tails). The word models of `RecCheckSpec10` simulate them.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## The twin's step -/

/-- The closedness test of `targetParamsDefEq`'s `cons` arm. -/
def tpClosed (pfvs : List EIdx) (a b : EIdx) : AM Bool := do
  if (← bvarB coreWalkFuel a) != 0 then pure false
  else if (← bvarB coreWalkFuel b) != 0 then pure false
  else if (← fvarB coreWalkFuel a) > pfvs.length then pure false
  else pure (decide ((← fvarB coreWalkFuel b) ≤ pfvs.length))

/-- The rest of the head step: `true` to go on with the tails. -/
def tpRest (fe : IFEnv) (d : Nat) (names : List NIdx) (lvls : LsIdx) (holes pfvs : List EIdx) (a b : EIdx) :
    AM Bool := do
  let ac ← ConRon.Arena.targetCanonParams pfvs a
  let a' ← ConRon.Arena.targetAbs names lvls holes ac
  let bc ← ConRon.Arena.targetCanonParams pfvs b
  let b' ← ConRon.Arena.targetAbs names lvls holes bc
  if a' == b' then pure true
  else
    let _ ← inferTypeCore V fe checkFuel d a'
    let _ ← inferTypeCore V fe checkFuel d b'
    isDefEqCore V fe checkFuel d a' b'

/-- The head step of `targetParamsDefEq`. -/
def tpStep (fe : IFEnv) (d : Nat) (names : List NIdx) (lvls : LsIdx) (holes pfvs : List EIdx) (a b : EIdx) :
    AM Bool := do
  let closed ← tpClosed pfvs a b
  if !closed then pure false else tpRest fe d names lvls holes pfvs a b

theorem ite_bind' {m : Type → Type} [Monad m] {α β : Type} (c : Prop) [Decidable c] (x y : m α)
    (f : α → m β) : (if c then x else y) >>= f = if c then x >>= f else y >>= f := by
  split <;> rfl

theorem tpd_cons (fe : IFEnv) (d : Nat) (names : List NIdx) (lvls : LsIdx) (holes pfvs : List EIdx)
    (a b : EIdx) (as bs : List EIdx) :
    ConRon.Arena.targetParamsDefEq V fe d names lvls holes pfvs (a :: as) (b :: bs) =
      (do let c ← tpStep fe d names lvls holes pfvs a b
          if c then ConRon.Arena.targetParamsDefEq V fe d names lvls holes pfvs as bs else pure false) := by
  rw [ConRon.Arena.targetParamsDefEq]
  simp only [tpStep, tpClosed, tpRest, bind_assoc, ite_bind', pure_bind]
  rfl

theorem tpd_nil (fe : IFEnv) (d : Nat) (names : List NIdx) (lvls : LsIdx) (holes pfvs : List EIdx)
    (bs : List EIdx) :
    ConRon.Arena.targetParamsDefEq V fe d names lvls holes pfvs [] bs = pure (bs.isEmpty) := by
  cases bs <;> rfl

theorem tpd_nilr (fe : IFEnv) (d : Nat) (names : List NIdx) (lvls : LsIdx) (holes pfvs : List EIdx)
    (a : EIdx) (as : List EIdx) :
    ConRon.Arena.targetParamsDefEq V fe d names lvls holes pfvs (a :: as) [] = pure false := rfl

/-! ## The step simulated -/

section rel
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

theorem word_lt_iff {a b : Word} : a < b ↔ a.toNat < b.toNat := UInt64.lt_iff_toNat_lt

/-- The model's closedness prefix simulates `tpClosed`: a `false` answers `[0]` at once, a `true`
goes on with the canon forms. -/
theorem pdsC_ok (n : Nat) {cR : CallM} {m m' : Mem} {a : AState} {d no nl lvls ho hl pfo pfl x y : Word}
    {r : List Word} {pfvs : List EIdx} (h : pdsW cR n m vis d no nl lvls ho hl pfo pfl x y = some (r, m'))
    (hS : StageR dn vis fe m a) (hx : H x) (hy : H y) (hlen : pfvs.length = pfl.toNat) (hP : RcMR m) :
    (∃ a', (tpClosed pfvs (decE x) (decE y)).run a = .ok (false, a') ∧ r = [0] ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ RcMR m' ∧ AFr m m') ∨
    (∃ m4 a4, (tpClosed pfvs (decE x) (decE y)).run a = .ok (true, a4) ∧
      pdsK5 cR n vis d no nl lvls ho hl pfo pfl y (tcpF n m4 pfo pfl x) = some (r, m') ∧
      StageR dn vis fe m4 a4 ∧ IWGrow m m4 ∧ RcMR m4 ∧ AFr m m4) := by
  unfold pdsW at h
  rcases h1 : bvbW n m x CWF with _ | ⟨b1, m1⟩ <;> rw [h1] at h
  · cases h
  obtain ⟨a1, r1, hS1, hg1, hf1⟩ := bvbW_stageC dn fe vis hS n x b1 hx h1
  have hP1 := hP.fr hf1
  by_cases hb1 : b1 ≠ 0
  · rw [pdsK1_b (h := hb1)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have e1 : (b1.toNat != 0) = true := by
      simp only [bne_iff_ne, ne_eq]; intro h0; exact hb1 (UInt64.toNat_inj.mp (by simpa using h0))
    refine .inl ⟨a1, ?_, rfl, hS1, hg1, hP1, bvbW_afr h1⟩
    simp only [tpClosed, StateT.run_bind, r1, except_ok_bind, e1, ite_true]; rfl
  rw [pdsK1_ok (h := hb1)] at h
  have e1 : (b1.toNat != 0) = false := by simp at hb1; simp [hb1]
  rcases h2 : bvbW n m1 y CWF with _ | ⟨b2, m2⟩ <;> rw [h2] at h
  · cases h
  obtain ⟨a2, r2, hS2, hg2, hf2⟩ := bvbW_stageC dn fe vis hS1 n y b2 hy h2
  have hP2 := hP1.fr hf2
  by_cases hb2 : b2 ≠ 0
  · rw [pdsK2_b (h := hb2)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have e2 : (b2.toNat != 0) = true := by
      simp only [bne_iff_ne, ne_eq]; intro h0; exact hb2 (UInt64.toNat_inj.mp (by simpa using h0))
    refine .inl ⟨a2, ?_, rfl, hS2, hg1.trans hg2, hP2, (bvbW_afr h1).trans (bvbW_afr h2)⟩
    simp only [tpClosed, StateT.run_bind, r1, except_ok_bind, e1, r2, e2, ite_true, Bool.false_eq_true,
      ite_false]; rfl
  rw [pdsK2_ok (h := hb2)] at h
  have e2 : (b2.toNat != 0) = false := by simp at hb2; simp [hb2]
  rcases h3 : fvbF m2 [CWF, x] with _ | ⟨r3, m3⟩ <;> rw [h3] at h
  · cases h
  obtain ⟨k3, a3, run3, hS3, hg3, hd3⟩ := fvbF_ok dn vis fe CWF x hx m2 m3 a2 r3 h3 hS2
  rw [CWF_eq, ← decE_eq] at run3
  have hP3 := hP2.fr (MFr.ofFvbF h3)
  by_cases hc3 : pfl < r3.headD 0
  · rw [pdsK3_out (h := hc3)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have e3 : k3 > pfvs.length := by rw [word_lt_iff] at hc3; simp only [decW0Nat] at hd3; omega
    refine .inl ⟨a3, ?_, rfl, hS3, (hg1.trans hg2).trans hg3, hP3,
      ((bvbW_afr h1).trans (bvbW_afr h2)).trans (fvbF_afr h3)⟩
    simp only [tpClosed, StateT.run_bind, r1, except_ok_bind, e1, r2, e2, run3, e3, ite_true,
      Bool.false_eq_true, ite_false]; rfl
  rw [pdsK3_ok (h := hc3)] at h
  have e3 : ¬ k3 > pfvs.length := by rw [word_lt_iff] at hc3; simp only [decW0Nat] at hd3; omega
  rcases h4 : fvbF m3 [CWF, y] with _ | ⟨r4, m4⟩ <;> rw [h4] at h
  · cases h
  obtain ⟨k4, a4, run4, hS4, hg4, hd4⟩ := fvbF_ok dn vis fe CWF y hy m3 m4 a3 r4 h4 hS3
  rw [CWF_eq, ← decE_eq] at run4
  have hP4 := hP3.fr (MFr.ofFvbF h4)
  have hg14 := ((hg1.trans hg2).trans hg3).trans hg4
  by_cases hc4 : pfl < r4.headD 0
  · rw [pdsK4_out (h := hc4)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have e4 : decide (k4 ≤ pfvs.length) = false := by
      rw [word_lt_iff] at hc4; simp only [decW0Nat] at hd4; simp; omega
    refine .inl ⟨a4, ?_, rfl, hS4, hg14, hP4,
      (((bvbW_afr h1).trans (bvbW_afr h2)).trans (fvbF_afr h3)).trans (fvbF_afr h4)⟩
    simp only [tpClosed, StateT.run_bind, r1, except_ok_bind, e1, r2, e2, run3, e3, run4, e4,
      Bool.false_eq_true, ite_false]; rfl
  rw [pdsK4_ok (h := hc4)] at h
  have e4 : decide (k4 ≤ pfvs.length) = true := by
    rw [word_lt_iff] at hc4; simp only [decW0Nat] at hd4; simp; omega
  refine .inr ⟨m4, a4, ?_, h, hS4, hg14, hP4,
    (((bvbW_afr h1).trans (bvbW_afr h2)).trans (fvbF_afr h3)).trans (fvbF_afr h4)⟩
  simp only [tpClosed, StateT.run_bind, r1, except_ok_bind, e1, r2, e2, run3, e3, run4, e4,
    Bool.false_eq_true, ite_false]; rfl

end rel

end L.Ind
