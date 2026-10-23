import ConAgua.Arena.RecCheckSpec10
import ConAgua.Arena.IndRealWalk

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
theorem pdsC_ok (n : Nat) {m m' : Mem} {a : AState} {d no nl lvls ho hl pfo pfl x y : Word}
    {r : List Word} {pfvs : List EIdx} (h : pdsW n m vis d no nl lvls ho hl pfo pfl x y = some (r, m'))
    (hS : StageR dn vis fe m a) (hx : H x) (hy : H y) (hlen : pfvs.length = pfl.toNat) (hP : RcMR m) :
    (∃ a', (tpClosed pfvs (decE x) (decE y)).run a = .ok (false, a') ∧ r = [0] ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ RcMR m') ∨
    (∃ m4 a4, (tpClosed pfvs (decE x) (decE y)).run a = .ok (true, a4) ∧
      pdsK5 n vis d no nl lvls ho hl pfo pfl y (tcpF n m4 pfo pfl x) = some (r, m') ∧
      StageR dn vis fe m4 a4 ∧ IWGrow m m4 ∧ RcMR m4) := by
  unfold pdsW at h
  cases h1 : bvbW n m x CWF with
  | none => rw [h1] at h; cases h
  | some p1 =>
  obtain ⟨b1, m1⟩ := p1
  rw [h1] at h
  obtain ⟨a1, r1, hS1, hg1, hf1⟩ := bvbW_stageC dn fe vis hS n x b1 hx h1
  have hP1 := hP.fr hf1
  by_cases hb1 : b1 ≠ 0
  · rw [pdsK1_b (h := hb1)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have e1 : (b1.toNat != 0) = true := by
      simp only [bne_iff_ne, ne_eq]; intro h0; exact hb1 (UInt64.toNat_inj.mp (by simpa using h0))
    refine .inl ⟨a1, ?_, rfl, hS1, hg1, hP1⟩
    simp only [tpClosed, StateT.run_bind, r1, except_ok_bind, e1, if_true]; rfl
  rw [pdsK1_ok (h := hb1)] at h
  have e1 : (b1.toNat != 0) = false := by simp at hb1; simp [hb1]
  cases h2 : bvbW n m1 y CWF with
  | none => rw [h2] at h; cases h
  | some p2 =>
  obtain ⟨b2, m2⟩ := p2
  rw [h2] at h
  obtain ⟨a2, r2, hS2, hg2, hf2⟩ := bvbW_stageC dn fe vis hS1 n y b2 hy h2
  have hP2 := hP1.fr hf2
  by_cases hb2 : b2 ≠ 0
  · rw [pdsK2_b (h := hb2)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have e2 : (b2.toNat != 0) = true := by
      simp only [bne_iff_ne, ne_eq]; intro h0; exact hb2 (UInt64.toNat_inj.mp (by simpa using h0))
    refine .inl ⟨a2, ?_, rfl, hS2, hg1.trans hg2, hP2⟩
    simp only [tpClosed, StateT.run_bind, r1, except_ok_bind, e1, r2, e2, if_true, Bool.false_eq_true,
      if_false]; rfl
  rw [pdsK2_ok (h := hb2)] at h
  have e2 : (b2.toNat != 0) = false := by simp at hb2; simp [hb2]
  cases h3 : fvbF m2 [CWF, x] with
  | none => rw [h3] at h; cases h
  | some p3 =>
  obtain ⟨r3, m3⟩ := p3
  rw [h3] at h
  obtain ⟨k3, a3, run3, hS3, hg3, hd3⟩ := fvbF_ok dn vis fe CWF x hx m2 m3 a2 r3 h3 hS2
  rw [CWF_eq, ← decE_eq] at run3
  have hP3 := hP2.fr (MFr.ofFvbF h3)
  by_cases hc3 : pfl < r3.headD 0
  · rw [pdsK3_out (h := hc3)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have e3 : k3 > pfvs.length := by rw [word_lt_iff] at hc3; simp only [decW0Nat] at hd3; omega
    refine .inl ⟨a3, ?_, rfl, hS3, (hg1.trans hg2).trans hg3, hP3⟩
    simp only [tpClosed, StateT.run_bind, r1, except_ok_bind, e1, r2, e2, run3, e3, if_true,
      Bool.false_eq_true, if_false]; rfl
  rw [pdsK3_ok (h := hc3)] at h
  have e3 : ¬ k3 > pfvs.length := by rw [word_lt_iff] at hc3; simp only [decW0Nat] at hd3; omega
  cases h4 : fvbF m3 [CWF, y] with
  | none => rw [h4] at h; cases h
  | some p4 =>
  obtain ⟨r4, m4⟩ := p4
  rw [h4] at h
  obtain ⟨k4, a4, run4, hS4, hg4, hd4⟩ := fvbF_ok dn vis fe CWF y hy m3 m4 a3 r4 h4 hS3
  rw [CWF_eq, ← decE_eq] at run4
  have hP4 := hP3.fr (MFr.ofFvbF h4)
  have hg14 := ((hg1.trans hg2).trans hg3).trans hg4
  by_cases hc4 : pfl < r4.headD 0
  · rw [pdsK4_out (h := hc4)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have e4 : decide (k4 ≤ pfvs.length) = false := by
      rw [word_lt_iff] at hc4; simp only [decW0Nat] at hd4; simp; omega
    refine .inl ⟨a4, ?_, rfl, hS4, hg14, hP4⟩
    simp only [tpClosed, StateT.run_bind, r1, except_ok_bind, e1, r2, e2, run3, e3, run4, e4,
      Bool.false_eq_true, if_false]; rfl
  rw [pdsK4_ok (h := hc4)] at h
  have e4 : decide (k4 ≤ pfvs.length) = true := by
    rw [word_lt_iff] at hc4; simp only [decW0Nat] at hd4; simp; omega
  refine .inr ⟨m4, a4, ?_, h, hS4, hg14, hP4⟩
  simp only [tpClosed, StateT.run_bind, r1, except_ok_bind, e1, r2, e2, run3, e3, run4, e4,
    Bool.false_eq_true, if_false]; rfl

/-- The model's rest simulates `tpRest`. -/
theorem pdsR_ok (n : Nat) {m m' : Mem} {a : AState} {d no nl lvls ho hl pfo pfl x y : Word}
    {r : List Word} {names : List NIdx} {holes pfvs : List EIdx}
    (h : pdsK5 n vis d no nl lvls ho hl pfo pfl y (tcpF n m pfo pfl x) = some (r, m'))
    (hS : StageR dn vis fe m a) (hx : H x) (hy : H y) (hlv : H lvls)
    (hno : decHL m no.toNat nl.toNat = some names) (hnob : no.toNat + nl.toNat ≤ iwTop m)
    (hho : decHL m ho.toNat hl.toNat = some holes) (hhob : ho.toNat + hl.toNat ≤ iwTop m)
    (hpf : HSl0 m pfo pfl pfvs) (hP : RcMR m) :
    ∃ c a', (tpRest fe d.toNat names (decI lvls) holes pfvs (decE x) (decE y)).run a = .ok (c, a') ∧
      (r.headD 0 != 0) = c ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧ RcMR m' := by
  cases h5 : tcpF n m pfo pfl x with
  | none => rw [h5] at h; cases h
  | some p5 =>
  obtain ⟨r5, m5⟩ := p5
  rw [h5, pdsK5_some] at h
  obtain ⟨a5, run5, hH5, hS5, hg5, hP5⟩ := tcpF_ok dn fe vis n h5 hS hpf hx hP
  cases h6 : taF n m5 no nl lvls ho hl (r5.headD 0) with
  | none => rw [h6] at h; cases h
  | some p6 =>
  obtain ⟨av, m6⟩ := p6
  rw [h6] at h
  obtain ⟨a6, run6, hS6, hg6, hP6⟩ := taF_ok dn fe vis n h6 hS5 hH5 hlv
    (by rw [decHL_grow hg5 hnob]; exact hno) (by have := hg5.1; omega)
    (by rw [decHL_grow hg5 hhob]; exact hho) (by have := hg5.1; omega) hP5
  by_cases hb6 : 4294967296 ≤ av
  · rw [pdsK6_big (h := hb6)] at h; cases h
  rw [pdsK6_ok (h := hb6)] at h
  have hav : H av := by simp only [H]; rw [UInt64.le_iff_toNat_le] at hb6; simp at hb6; omega
  have hg56 := hg5.trans hg6
  cases h7 : tcpF n m6 pfo pfl y with
  | none => rw [h7] at h; cases h
  | some p7 =>
  obtain ⟨r7, m7⟩ := p7
  rw [h7, pdsK7_some] at h
  obtain ⟨a7, run7, hH7, hS7, hg7, hP7⟩ := tcpF_ok dn fe vis n h7 hS6 (hpf.grow hg56) hy hP6
  have hg57 := hg56.trans hg7
  cases h8 : taF n m7 no nl lvls ho hl (r7.headD 0) with
  | none => rw [h8] at h; cases h
  | some p8 =>
  obtain ⟨bv, m8⟩ := p8
  rw [h8] at h
  obtain ⟨a8, run8, hS8, hg8, hP8⟩ := taF_ok dn fe vis n h8 hS7 hH7 hlv
    (by rw [decHL_grow hg57 hnob]; exact hno) (by have := hg57.1; omega)
    (by rw [decHL_grow hg57 hhob]; exact hho) (by have := hg57.1; omega) hP7
  have hg58 := hg57.trans hg8
  by_cases hb8 : 4294967296 ≤ bv
  · rw [pdsK8_big (h := hb8)] at h; cases h
  have hbv : H bv := by simp only [H]; rw [UInt64.le_iff_toNat_le] at hb8; simp at hb8; omega
  by_cases he : av = bv
  · rw [pdsK8_eq (h := hb8) (he := he)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    refine ⟨true, a8, ?_, rfl, hS8, hg58, hP8⟩
    subst he
    simp only [tpRest, StateT.run_bind, run5, except_ok_bind, run6, run7, run8, beq_self_eq_true, if_true]
    rfl
  rw [pdsK8_ne (h := hb8) (he := he)] at h
  have hne : (decE av == decE bv) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; exact fun e => he (decE_inj av bv hav hbv e)
  cases h9 : stubM "infer_type_core" m8 [vis, d, av] with
  | none => rw [h9] at h; cases h
  | some p9 =>
  obtain ⟨r9, m9⟩ := p9
  rw [h9, pdsK9_some] at h
  obtain ⟨t9, a9, run9, hS9, hg9, -⟩ := inferTypeCore_spec dn vis fe d av hav m8 m9 a8 r9 h9 hS8
  cases h10 : stubM "infer_type_core" m9 [vis, d, bv] with
  | none => rw [h10] at h; cases h
  | some p10 =>
  obtain ⟨r10, m10⟩ := p10
  rw [h10, pdsK10_some] at h
  obtain ⟨t10, a10, run10, hS10, hg10, -⟩ := inferTypeCore_spec dn vis fe d bv hbv m9 m10 a9 r10 h10 hS9
  cases h11 : stubM "is_def_eq_core" m10 [vis, d, av, bv] with
  | none => rw [h11] at h; cases h
  | some p11 =>
  obtain ⟨r11, m11⟩ := p11
  rw [h11, pdsK11_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  obtain ⟨c, a11, run11, hS11, hg11, hd11, -⟩ := isDefEqCore_spec dn vis fe d av bv hav hbv m10 m11 a10 r11 h11 hS10
  refine ⟨c, a11, ?_, hd11, hS11, ((hg58.trans hg9).trans hg10).trans hg11,
    ((hP8.stub (by decide) h9).stub (by decide) h10).stub (by decide) h11⟩
  simp only [← decE_eq] at run9 run10 run11
  simp only [tpRest, StateT.run_bind, run5, except_ok_bind, run6, run7, run8, hne, Bool.false_eq_true,
    if_false, run9, run10, run11]

/-- The model's step simulates `tpStep`. -/
theorem pdsW_ok (n : Nat) {m m' : Mem} {a : AState} {d no nl lvls ho hl pfo pfl x y : Word}
    {r : List Word} {names : List NIdx} {holes pfvs : List EIdx}
    (h : pdsW n m vis d no nl lvls ho hl pfo pfl x y = some (r, m'))
    (hS : StageR dn vis fe m a) (hx : H x) (hy : H y) (hlv : H lvls)
    (hno : decHL m no.toNat nl.toNat = some names) (hnob : no.toNat + nl.toNat ≤ iwTop m)
    (hho : decHL m ho.toNat hl.toNat = some holes) (hhob : ho.toNat + hl.toNat ≤ iwTop m)
    (hpf : HSl0 m pfo pfl pfvs) (hP : RcMR m) :
    ∃ c a', (tpStep fe d.toNat names (decI lvls) holes pfvs (decE x) (decE y)).run a = .ok (c, a') ∧
      (r.headD 0 != 0) = c ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧ RcMR m' := by
  rcases pdsC_ok dn fe vis n h hS hx hy hpf.len hP with
    ⟨a', run, rfl, hS', hg, hP'⟩ | ⟨m4, a4, run, h4, hS4, hg4, hP4⟩
  · refine ⟨false, a', ?_, rfl, hS', hg, hP'⟩
    simp only [tpStep, StateT.run_bind, run, except_ok_bind, Bool.not_false, if_true]; rfl
  · obtain ⟨c, a', run', hc, hS', hg, hP'⟩ := pdsR_ok dn fe vis n h4 hS4 hx hy hlv
      (by rw [decHL_grow hg4 hnob]; exact hno) (by have := hg4.1; omega)
      (by rw [decHL_grow hg4 hhob]; exact hho) (by have := hg4.1; omega)
      (hpf.grow hg4) hP4
    refine ⟨c, a', ?_, hc, hS', hg4.trans hg, hP'⟩
    simp only [tpStep, StateT.run_bind, run, except_ok_bind, Bool.not_true, Bool.false_eq_true, if_false]
    exact run'

theorem pdeW_ok (n : Nat) : ∀ {m m' : Mem} {a : AState} {d no nl lvls ho hl pfo pfl ao al bo bl : Word}
    {r : List Word} {names : List NIdx} {holes pfvs as bs : List EIdx},
    pdeW n m vis d no nl lvls ho hl pfo pfl ao al bo bl = some (r, m') → StageR dn vis fe m a → H lvls →
    decHL m no.toNat nl.toNat = some names → no.toNat + nl.toNat ≤ iwTop m →
    decHL m ho.toNat hl.toNat = some holes → ho.toNat + hl.toNat ≤ iwTop m →
    HSl0 m pfo pfl pfvs → HSl0 m ao al as → HSl0 m bo bl bs → RcMR m →
    ∃ c a', (ConRon.Arena.targetParamsDefEq V fe d.toNat names (decI lvls) holes pfvs as bs).run a =
      .ok (c, a') ∧ (r.headD 0 != 0) = c ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧ RcMR m' := by
  induction n with
  | zero => intro m m' a d no nl lvls ho hl pfo pfl ao al bo bl r names holes pfvs as bs h; simp [pdeW] at h
  | succ n ih =>
  intro m m' a d no nl lvls ho hl pfo pfl ao al bo bl r names holes pfvs as bs h hS hlv hno hnob hho hhob
    hpf has hbs hP
  have hlt : ∀ {x : Nat}, x ≤ iwTop m → x < 2 ^ 64 := fun h => hS.lt64 h
  by_cases hal : al = 0
  · rw [pdeW_nil (h := hal)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    subst hal
    have : as = [] := by have := has.len; simpa using this
    subst this
    refine ⟨bs.isEmpty, a, by rw [tpd_nil]; rfl, ?_, hS, IWGrow.refl _, hP⟩
    have hbl : bs.length = bl.toNat := hbs.len
    by_cases hb0 : bl = 0
    · subst hb0; have : bs = [] := by simpa using hbl
      subst this; simp
    · have : bs ≠ [] := fun e => hb0 (UInt64.toNat_inj.mp (by rw [← hbl, e]; rfl))
      simp [hb0, List.isEmpty_iff, this]
  by_cases hbl : bl = 0
  · rw [pdeW_nilr (h := hal) (hb := hbl)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    subst hbl
    have : bs = [] := by have := hbs.len; simpa using this
    subst this
    have hasb : ao.toNat + al.toNat ≤ iwTop m := has.2.resolve_left hal
    obtain ⟨w, as', rfl, -, -, -⟩ := decHL_cons has.1 hal (hlt hasb)
    exact ⟨false, a, by rw [tpd_nilr]; rfl, rfl, hS, IWGrow.refl _, hP⟩
  rw [pdeW_cons (h := hal) (hb := hbl)] at h
  have hasb : ao.toNat + al.toNat ≤ iwTop m := has.2.resolve_left hal
  have hbsb : bo.toNat + bl.toNat ≤ iwTop m := hbs.2.resolve_left hbl
  obtain ⟨x, as', rfl, ex, hx, has'⟩ := decHL_cons has.1 hal (hlt hasb)
  obtain ⟨y, bs', rfl, ey, hy, hbs'⟩ := decHL_cons hbs.1 hbl (hlt hbsb)
  rw [ex, ey] at h
  obtain ⟨ea1, el1, hal0⟩ := slice_step hal (hlt hasb)
  obtain ⟨eb1, ebl1, hbl0⟩ := slice_step hbl (hlt hbsb)
  cases n with
  | zero => simp [pdsF, pdeK1] at h
  | succ k =>
  cases h1 : pdsW k m vis d no nl lvls ho hl pfo pfl x y with
  | none => simp only [pdsF] at h; rw [h1] at h; simp [pdeK1] at h
  | some p1 =>
  obtain ⟨r1, m1⟩ := p1
  simp only [pdsF] at h; rw [h1] at h
  obtain ⟨c, a1, run1, hc, hS1, hg1, hP1⟩ :=
    pdsW_ok dn fe vis k h1 hS hx hy hlv hno hnob hho hhob hpf hP
  by_cases hr1 : r1.headD 0 = 0
  · rw [pdeK1_stop (h := hr1)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have : c = false := by rw [← hc, hr1]; rfl
    subst this
    refine ⟨false, a1, ?_, rfl, hS1, hg1, hP1⟩
    rw [tpd_cons]; simp only [StateT.run_bind, ← decE_eq, run1, except_ok_bind, Bool.false_eq_true, if_false]; rfl
  rw [pdeK1_go (h := hr1)] at h
  have : c = true := by rw [← hc]; simpa using hr1
  subst this
  cases h2 : pdeW (k + 1) m1 vis d no nl lvls ho hl pfo pfl (ao + 1) (al - 1) (bo + 1) (bl - 1) with
  | none => rw [h2] at h; cases h
  | some p2 =>
  obtain ⟨r2, m2⟩ := p2
  rw [h2, pdsK11_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  have hgo := hg1.1
  obtain ⟨c2, a2, run2, hc2, hS2, hg2, hP2⟩ := ih h2 hS1 hlv
    (by rw [decHL_grow hg1 hnob]; exact hno) (by omega)
    (by rw [decHL_grow hg1 hhob]; exact hho) (by omega)
    (hpf.grow hg1)
    (HSl0.of (by rw [decHL_grow hg1 (by rw [ea1, el1]; omega)]; exact has') (by rw [ea1, el1]; omega))
    (HSl0.of (by rw [decHL_grow hg1 (by rw [eb1, ebl1]; omega)]; exact hbs') (by rw [eb1, ebl1]; omega)) hP1
  refine ⟨c2, a2, ?_, by simpa using hc2, hS2, hg1.trans hg2, hP2⟩
  rw [tpd_cons]; simp only [StateT.run_bind, ← decE_eq, run1, except_ok_bind, if_true]; exact run2

end rel

/-- **`target_params_def_eq` (with its step) refines `targetParamsDefEq`** (through the stubs
`fvar_b`, `infer_type_core`, `is_def_eq_core`, and `replace_fvars`'): from both slices, the member
names and the holes decoded below the top, the openers and both slices decoded (below the top unless
empty), the walk memos well formed; the verdict as
`r[0] ≠ 0`. -/
@[refines ConRon.Arena.targetParamsDefEq]
theorem targetParamsDefEq_refines (p : Prog) (L : TpLook p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis d no nl lvls ho hl pfo pfl ao al bo bl : Word)
    (names : List NIdx) (holes pfvs as bs : List EIdx) (hS : StageR dn vis fe s₀.mem a₀) (hlv : H lvls)
    (hno : decHL s₀.mem no.toNat nl.toNat = some names) (hnob : no.toNat + nl.toNat ≤ iwTop s₀.mem)
    (hho : decHL s₀.mem ho.toNat hl.toNat = some holes) (hhob : ho.toNat + hl.toNat ≤ iwTop s₀.mem)
    (hpf : HSl0 s₀.mem pfo pfl pfvs) (has : HSl0 s₀.mem ao al as) (hbs : HSl0 s₀.mem bo bl bs)
    (hP : RcMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_params_def_eq"
      [vis, d, no, nl, lvls, ho, hl, pfo, pfl, ao, al, bo, bl]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.targetParamsDefEq V fe d.toNat names (decI lvls) holes pfvs as bs) a₀ ∧
      (r.headD 0 != 0) = AM.res (ConRon.Arena.targetParamsDefEq V fe d.toNat names (decI lvls) holes pfvs as bs) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.targetParamsDefEq V fe d.toNat names (decI lvls) holes pfvs as bs) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ RcMR s'.mem; ⊤⦄ := by
  refine triple_post (tpd_spec p L n s₀ vis d no nl lvls ho hl pfo pfl ao al bo bl) ?_
  rintro r s' ⟨hl', hm⟩
  obtain ⟨c, a', run, hc, hS', hg, hP'⟩ := pdeW_ok dn fe vis n hm hS hlv hno hnob hho hhob hpf has hbs hP
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl', hok, by rw [hres]; exact hc, by rw [hst]; exact hS', hg, hP'⟩

end L.Ind
