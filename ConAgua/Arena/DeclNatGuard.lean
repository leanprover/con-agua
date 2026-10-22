import ConAgua.Arena.DeclNatLit

/-!
# The structural-`Nat` gate: `bool_ctor_ok` and `nat_op_guard` (lane `decls3`, helper `decls3-nat`)
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

structure NatGuardProg (p : Prog) : Prop extends NatLitProg p where
  lBoolCtorOk : p.lookup "bool_ctor_ok" = some boolCtorOkL
  lNatOpGuard : p.lookup "nat_op_guard" = some natOpGuardL

/-- A constant value record `[name, lps.off, lps.len, type]` at `q`: the length word and the type
word, and that they stay under growth. -/
theorem cvWordsAt {m : Mem} {q : Word} {cv : IConstantVal} (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (h : decCV (erecP m) q.toNat = some cv) :
    ∃ wt, ((rdW (m.arr64 EREC) (q + 2) = 0) ↔ cv.levelParams.isEmpty = true) ∧
      rdW (m.arr64 EREC) (q + 3) = wt ∧ wt.toNat < 2 ^ 32 ∧ cv.type = decI wt ∧
      ∀ m', IWGrow m m' → rdW (m'.arr64 EREC) (q + 2) = rdW (m.arr64 EREC) (q + 2) ∧
        rdW (m'.arr64 EREC) (q + 3) = wt := by
  obtain ⟨wl, hwl, hlen⟩ := decCV_lps_len h
  obtain ⟨wt, hwt, hlt, hty⟩ := decCV_typeW h
  have hwl' := erecP_get hwl
  have hwt' := erecP_get hwt
  have hb : q.toNat + 3 < (m.arr64 EREC).size := by
    have := (Array.getElem?_eq_some_iff.mp hwt').1; omega
  have hq2 : (q + 2).toNat = q.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have hq3 : (q + 3).toNat = q.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  have e2 : rdW (m.arr64 EREC) (q + 2) = wl := by
    simp only [rdW, hq2]; rw [hwl']; rfl
  have e3 : rdW (m.arr64 EREC) (q + 3) = wt := by
    simp only [rdW, hq3]; rw [hwt']; rfl
  have hst : ∀ m', IWGrow m m' → rdW (m'.arr64 EREC) (q + 2) = rdW (m.arr64 EREC) (q + 2) ∧
      rdW (m'.arr64 EREC) (q + 3) = wt := by
    intro m' hg
    constructor
    · rw [e2]; simp only [rdW, hq2]; rw [hg.erec_get hwl]; rfl
    · simp only [rdW, hq3]; rw [hg.erec_get hwt]; rfl
  refine ⟨wt, ?_, e3, hlt, hty, hst⟩
  rw [e2]
  simp only [List.isEmpty_iff_length_eq_zero]
  constructor
  · intro hw0; rw [← hlen, hw0]; rfl
  · intro hl; exact UInt64.toNat_inj.mp (by simpa [hlen] using hl)

section guard
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

/-! ### `bool_ctor_ok` -/

def boolCtorOkW (p : Prog) (n : Nat) (m : Mem) (c : Word) : Option (List Word × Mem) :=
  bW (callW p n "ci_to_cv" [c] m) fun r1 m1 =>
  if rdW (m1.arr64 EREC) (r1.headD 0 + 2) ≠ 0 then some ([0], m1) else
  bW (callW p n "pin_at" [29] m1) fun r2 m2 =>
  bW (callW p n "const_e" [r2.headD 0] m2) fun r3 m3 =>
  some ([if rdW (m3.arr64 EREC) (r1.headD 0 + 3) = r3.headD 0 then 1 else 0], m3)

theorem boolCtorOk_specW (p : Prog) (hp : p.lookup "bool_ctor_ok" = some boolCtorOkL) (n : Nat)
    (s₀ : St) (c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "bool_ctor_ok" [c]
    ⦃fun r s' => LocEq s' s₀ ∧ boolCtorOkW p n s₀.mem c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, boolCtorOkL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "ci_to_cv", callW_spec p n "pin_at", callW_spec p n "const_e"] <;>
    finish (gen := 20) [boolCtorOkW, bW]

theorem boolCtorOk_ref (hN : NatGuardProg p) (c : Word) (ci : IConstantInfo) :
    CallRef p "bool_ctor_ok" [c]
      (fun m a => StageR dn vis fe m a ∧ decCI (erecP m) dn c.toNat = some ci)
      (boolCtorOk ci) (KeepPost dn vis fe decW0B) := by
  refine CallRef.of_succ fun k m a r m' ⟨hS, hci⟩ hc => ?_
  have hw := callW_model (M := fun mm => boolCtorOkW p k mm c) (boolCtorOk_specW p hN.lBoolCtorOk k · c) hc
  unfold boolCtorOkW at hw
  cases h1 : callW p k "ci_to_cv" [c] m with
  | none => rw [h1] at hw; simp at hw
  | some q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, bW_some] at hw
  obtain ⟨cv, a1, hrun1, hS1, hg1, hcv⟩ := ciToCv_ref (dn := dn) (vis := vis) (fe := fe) hN.toNatCvProg
    c ci k m a r1 m1 ⟨hS, hci⟩ h1
  have hsz1 := hS1.2.2.2.2.1
  obtain ⟨wt, hiff, hrd, hlt, hty, hstay⟩ := cvWordsAt hsz1 hcv
  by_cases hl : rdW (m1.arr64 EREC) (r1.headD 0 + 2) = 0
  · rw [if_neg (by simpa using hl)] at hw
    have hisE : cv.levelParams.isEmpty = true := hiff.mp hl
    cases h2 : callW p k "pin_at" [29] m1 with
    | none => rw [h2] at hw; simp at hw
    | some q2 =>
    obtain ⟨r2, m2⟩ := q2
    rw [h2, bW_some] at hw
    obtain ⟨hm2, h0, hr2⟩ := pinAt_call hN.lPinAt (j := 30) rfl h2
    rw [hm2] at hw
    have hF := hS1.1.pins.full h0
    have hp2 : H (r2.headD 0) := by rw [hr2]; exact hF.names_lt 29 (by decide)
    cases h3 : callW p k "const_e" [r2.headD 0] m1 with
    | none => rw [h3] at hw; simp at hw
    | some q3 =>
    obtain ⟨r3, m3⟩ := q3
    rw [h3, bW_some] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    obtain ⟨x3, a3, hrun3, hS3, hg3, hx3l, hx3⟩ := constE_ref (dn := dn) (vis := vis) (fe := fe)
      hN.toMasterProg (r2.headD 0) k m1 a1 r3 m3 ⟨hS1, hp2⟩ h3
    obtain ⟨-, hst3⟩ := hstay m3 hg3
    rw [hst3] at *
    have e2 : (pinAt 29).run a1 = .ok (decI (r2.headD 0), a1) := by
      have := pinAt_run hF 29 (by decide)
      rw [hr2]; exact this
    have hrun : (boolCtorOk ci).run a = .ok (decide (wt = r3.headD 0), a3) := by
      simp only [boolCtorOk, StateT.run_bind, hrun1, exc_ok_bind', hisE, if_true, boolName_eq, e2, hrun3,
        hty, decI_beq_word hlt hx3l, ← hx3, StateT.run_pure]
      rfl
    refine ⟨_, a3, hrun, hS3, hg1.trans hg3, ?_⟩
    simp only [decW0B, List.headD_cons]
    by_cases he : wt = r3.headD 0
    · rw [if_pos he, decide_eq_true he]; decide
    · rw [if_neg he, decide_eq_false he]; decide
  · rw [if_pos (by simpa using hl)] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hisE : cv.levelParams.isEmpty = false := by
      cases h : cv.levelParams.isEmpty
      · rfl
      · exact absurd (hiff.mpr h) hl
    refine ⟨false, a1, ?_, hS1, hg1, by simp [decW0B]⟩
    simp only [boolCtorOk, StateT.run_bind, hrun1, exc_ok_bind', hisE]
    rfl

@[refines ConRon.Arena.boolCtorOk]
theorem boolCtorOk_refines (hN : NatGuardProg p) (c : Word) (ci : IConstantInfo) :
    RefAM p "bool_ctor_ok" [c]
      (fun m a => StageR dn vis fe m a ∧ decCI (erecP m) dn c.toNat = some ci)
      (boolCtorOk ci) (KeepPost dn vis fe decW0B) :=
  (boolCtorOk_ref hN c ci).refAM


/-- A pin read followed by the lookup of the pinned name: memory unchanged, the twin's pin read,
the decoded lookup. -/
theorem pinFind_call (hN : NatGuardProg p) {i : Word} (hi : i.toNat < 51) {k : Nat} {m m1 m2 : Mem}
    {a : AState} {r1 rf : List Word} (hS : StageR dn vis fe m a)
    (h1 : callW p k "pin_at" [i] m = some (r1, m1))
    (h2 : callW p k "env_find" [r1.headD 0, vis] m1 = some (rf, m2)) :
    m1 = m ∧ m2 = m ∧ pinW m 0 ≠ 0 ∧ H (r1.headD 0) ∧ r1.headD 0 = pinW m (1 + i.toNat) ∧
      (pinAt i.toNat).run a = .ok (decI (r1.headD 0), a) ∧
      decFd dn m rf (fe.find? (decI (r1.headD 0))) := by
  obtain ⟨hm1, h0, hr1⟩ := pinAt_call hN.lPinAt (j := 1 + i.toNat) rfl h1
  subst hm1
  have hF := hS.1.pins.full h0
  have hp : H (r1.headD 0) := by rw [hr1]; exact hF.names_lt i.toNat hi
  obtain ⟨hm2, hfd⟩ := envFind_call hN.toMasterProg (r1.headD 0) hp hS.1.env h2
  refine ⟨rfl, hm2, h0, hp, hr1, ?_, hfd⟩
  have := pinAt_run hF i.toNat hi
  rw [hr1]; exact this


/-! ### `nat_op_guard` -/

section ngmodel
variable (p : Prog) (n : Nat) (vis c : Word)

def ngK13 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r13, m13) => some ([r13.headD 0], m13)

def ngK12 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r12, m12) =>
    if r12.headD 0 = 0 then some ([0], m12)
    else ngK13 (callW p n "bool_ctor_ok" [r12.tail.headD 0] m12)

def ngK11 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r11, m11) => ngK12 p n (callW p n "env_find" [r11.headD 0, vis] m11)

def ngK10 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r10, m10) =>
    if r10.headD 0 = 0 then some ([0], m10) else ngK11 p n vis (callW p n "pin_at" [31] m10)

def ngK9 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r9, m9) =>
    if r9.headD 0 = 0 then some ([0], m9)
    else ngK10 p n vis (callW p n "bool_ctor_ok" [r9.tail.headD 0] m9)

def ngK8 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r8, m8) => ngK9 p n vis (callW p n "env_find" [r8.headD 0, vis] m8)

def ngK7 (r4 r5 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r7, m7) =>
    if c = r4.headD 0 ∨ c = r5.headD 0 ∨ r7.headD 0 ≠ 0 then
      ngK8 p n vis (callW p n "pin_at" [30] m7)
    else some ([1], m7)

def ngK6 (r4 r5 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r6, m6) =>
    ngK7 p n vis c r4 r5 (callW p n "sl_contains" [r6.headD 0, r6.tail.headD 0, c] m6)

def ngK5 (r4 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) => ngK6 p n vis c r4 r5 (callW p n "nat_div_mod_names" [] m5)

def ngK4 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => ngK5 p n vis c r4 (callW p n "pin_at" [20] m4)

def ngK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) =>
    if r3.headD 0 = 0 then some ([0], m3) else ngK4 p n vis c (callW p n "pin_at" [19] m3)

def ngK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    ngK3 p n vis c (callW p n "nat_op_deps_stored" [vis, r2.headD 0, r2.tail.headD 0] m2)

def ngK1 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 = 0 then some ([0], m1) else ngK2 p n vis c (callW p n "nat_op_deps" [c] m1)

end ngmodel

def natOpGuardW (p : Prog) (n : Nat) (m : Mem) (vis c : Word) : Option (List Word × Mem) :=
  ngK1 p n vis c (callW p n "nat_lit_supported" [vis] m)

section ngarms
variable (p : Prog) (n : Nat) (vis c : Word) (r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 : List Word)
  (m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 : Mem)
theorem ngK13_some : ngK13 (some (r13, m13)) = some ([r13.headD 0], m13) := rfl
theorem ngK12_some : ngK12 p n (some (r12, m12)) = if r12.headD 0 = 0 then some ([0], m12)
    else ngK13 (callW p n "bool_ctor_ok" [r12.tail.headD 0] m12) := rfl
theorem ngK11_some : ngK11 p n vis (some (r11, m11)) =
    ngK12 p n (callW p n "env_find" [r11.headD 0, vis] m11) := rfl
theorem ngK10_some : ngK10 p n vis (some (r10, m10)) =
    if r10.headD 0 = 0 then some ([0], m10) else ngK11 p n vis (callW p n "pin_at" [31] m10) := rfl
theorem ngK9_some : ngK9 p n vis (some (r9, m9)) = if r9.headD 0 = 0 then some ([0], m9)
    else ngK10 p n vis (callW p n "bool_ctor_ok" [r9.tail.headD 0] m9) := rfl
theorem ngK8_some : ngK8 p n vis (some (r8, m8)) =
    ngK9 p n vis (callW p n "env_find" [r8.headD 0, vis] m8) := rfl
theorem ngK7_some : ngK7 p n vis c r4 r5 (some (r7, m7)) =
    if c = r4.headD 0 ∨ c = r5.headD 0 ∨ r7.headD 0 ≠ 0 then
      ngK8 p n vis (callW p n "pin_at" [30] m7) else some ([1], m7) := rfl
theorem ngK6_some : ngK6 p n vis c r4 r5 (some (r6, m6)) =
    ngK7 p n vis c r4 r5 (callW p n "sl_contains" [r6.headD 0, r6.tail.headD 0, c] m6) := rfl
theorem ngK5_some : ngK5 p n vis c r4 (some (r5, m5)) =
    ngK6 p n vis c r4 r5 (callW p n "nat_div_mod_names" [] m5) := rfl
theorem ngK4_some : ngK4 p n vis c (some (r4, m4)) =
    ngK5 p n vis c r4 (callW p n "pin_at" [20] m4) := rfl
theorem ngK3_some : ngK3 p n vis c (some (r3, m3)) =
    if r3.headD 0 = 0 then some ([0], m3) else ngK4 p n vis c (callW p n "pin_at" [19] m3) := rfl
theorem ngK2_some : ngK2 p n vis c (some (r2, m2)) =
    ngK3 p n vis c (callW p n "nat_op_deps_stored" [vis, r2.headD 0, r2.tail.headD 0] m2) := rfl
theorem ngK1_some : ngK1 p n vis c (some (r1, m1)) =
    if r1.headD 0 = 0 then some ([0], m1) else ngK2 p n vis c (callW p n "nat_op_deps" [c] m1) := rfl
end ngarms

grind_pattern [ind_grind] ngK13_some => ngK13 (some (r13, m13))
grind_pattern [ind_grind] ngK12_some => ngK12 p n (some (r12, m12))
grind_pattern [ind_grind] ngK11_some => ngK11 p n vis (some (r11, m11))
grind_pattern [ind_grind] ngK10_some => ngK10 p n vis (some (r10, m10))
grind_pattern [ind_grind] ngK9_some => ngK9 p n vis (some (r9, m9))
grind_pattern [ind_grind] ngK8_some => ngK8 p n vis (some (r8, m8))
grind_pattern [ind_grind] ngK7_some => ngK7 p n vis c r4 r5 (some (r7, m7))
grind_pattern [ind_grind] ngK6_some => ngK6 p n vis c r4 r5 (some (r6, m6))
grind_pattern [ind_grind] ngK5_some => ngK5 p n vis c r4 (some (r5, m5))
grind_pattern [ind_grind] ngK4_some => ngK4 p n vis c (some (r4, m4))
grind_pattern [ind_grind] ngK3_some => ngK3 p n vis c (some (r3, m3))
grind_pattern [ind_grind] ngK2_some => ngK2 p n vis c (some (r2, m2))
grind_pattern [ind_grind] ngK1_some => ngK1 p n vis c (some (r1, m1))

set_option maxHeartbeats 8000000 in
theorem natOpGuard_specW (p : Prog) (hp : p.lookup "nat_op_guard" = some natOpGuardL) (n : Nat)
    (s₀ : St) (vis c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nat_op_guard" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ natOpGuardW p n s₀.mem vis c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, natOpGuardL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "nat_lit_supported", callW_spec p n "nat_op_deps",
      callW_spec p n "nat_op_deps_stored", callW_spec p n "pin_at",
      callW_spec p n "nat_div_mod_names", callW_spec p n "sl_contains",
      callW_spec p n "env_find", callW_spec p n "bool_ctor_ok"] <;>
    finish (gen := 20) [natOpGuardW]

end guard

end L.Ind
