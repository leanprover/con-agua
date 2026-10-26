import ConAgua.L.ModelGen
import ConAgua.Arena.DeclNatLit
import ConAgua.Arena.DeclNatDeps

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
  lBoolCtors : p.lookup "nat_op_bool_ctors" = some natOpBoolCtorsL

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

/-- **`bool_ctor_ok` is its model `boolCtorOkW`** (generated). -/
l_model boolCtorOk_specW (p : Prog) (hp : p.lookup "bool_ctor_ok" = some boolCtorOkL)
  fns [hp ↦ boolCtorOkW list]
  specs [callW_spec p n "ci_to_cv", callW_spec p n "pin_at", callW_spec p n "const_e"]
  grind [arena_grind] bind ntBW simp [ntBW]

theorem boolCtorOk_ref (hN : NatGuardProg p) (c : Word) (ci : IConstantInfo) :
    CallRef p "bool_ctor_ok" [c]
      (fun m a => StageR dn vis fe m a ∧ decCI (erecP m) dn c.toNat = some ci)
      (boolCtorOk ci) (KeepPost dn vis fe decW0B) := by
  refine CallRef.of_succ fun k m a r m' ⟨hS, hci⟩ hc => ?_
  have hw := callW_model (M := fun mm => boolCtorOkW p (k + 1) mm c) (boolCtorOk_specW p hN.lBoolCtorOk (k + 1) · c) hc
  rw [boolCtorOkW.eq_2] at hw
  replace hw := ntBW_some hw; obtain ⟨r1, m1, h1, hw⟩ := hw
  obtain ⟨cv, a1, hrun1, hS1, hg1, hcv⟩ := ciToCv_ref (dn := dn) (vis := vis) (fe := fe) hN.toNatCvProg
    c ci k m a r1 m1 ⟨hS, hci⟩ h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hrun1)
  have hsz1 := hS1.2.2.2.2.1
  obtain ⟨wt, hiff, hrd, hlt, hty, hstay⟩ := cvWordsAt hsz1 hcv
  by_cases hl : rdW (m1.arr64 EREC) (r1.headD 0 + 2) = 0
  · rw [if_neg (by simpa using hl)] at hw
    have hisE : ci.toConstantVal.levelParams.isEmpty = true := hiff.mp hl
    replace hw := ntBW_some hw; obtain ⟨r2, m2, h2, hw⟩ := hw
    obtain ⟨hm2, h0, hr2⟩ := pinAt_call hN.lPinAt (j := 30) rfl h2
    rw [hm2] at hw
    have hF := hS1.1.pins.full h0
    have hp2 : H (r2.headD 0) := by rw [hr2]; exact hF.names_lt 29 (by decide)
    replace hw := ntBW_some hw; obtain ⟨r3, m3, h3, hw⟩ := hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    obtain ⟨x3, a3, hrun3, hS3, hg3, hx3l, hx3⟩ := constE_ref (dn := dn) (vis := vis) (fe := fe)
      hN.toMasterProg (r2.headD 0) k m1 a r3 m3 ⟨hS1, hp2⟩ h3
    obtain ⟨-, hst3⟩ := hstay m3 hg3
    rw [hst3] at *
    have e2 : (pinAt 29).run a = .ok (decI (r2.headD 0), a) := by
      have := pinAt_run hF 29 (by decide)
      rw [hr2]; exact this
    have hrun : (boolCtorOk ci).run a = .ok (decide (wt = r3.headD 0), a3) := by
      simp only [boolCtorOk, hisE, if_true, StateT.run_bind, exc_ok_bind', boolName_eq, e2, hrun3,
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
    have hisE : ci.toConstantVal.levelParams.isEmpty = false := by
      cases h : ci.toConstantVal.levelParams.isEmpty
      · rfl
      · exact absurd (hiff.mpr h) hl
    refine ⟨false, a, ?_, hS1, hg1, by simp [decW0B]⟩
    simp only [boolCtorOk, hisE]
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


/-! ### `nat_op_bool_ctors` -/

/-- **`nat_op_bool_ctors` is its model `boolCtorsW`** (generated). -/
l_model boolCtors_specW (p : Prog) (hp : p.lookup "nat_op_bool_ctors" = some natOpBoolCtorsL)
  fns [hp ↦ boolCtorsW list]
  specs [callW_spec p n "pin_at", callW_spec p n "env_find", callW_spec p n "bool_ctor_ok"]
  grind [arena_grind] bind ntBW simp [ntBW]

/-! ### `nat_op_guard` -/

/-- **`nat_op_guard` is its model `natOpGuardW`** (generated). -/
l_model natOpGuard_specW (p : Prog) (hp : p.lookup "nat_op_guard" = some natOpGuardL)
  fns [hp ↦ natOpGuardW list]
  specs [callW_spec p n "nat_lit_supported", callW_spec p n "nat_op_deps", callW_spec p n "nat_op_deps_stored", callW_spec p n "pin_at", callW_spec p n "nat_div_mod_names", callW_spec p n "sl_contains", callW_spec p n "nat_op_bool_ctors"]
  grind [arena_grind] heartbeats 3200000 bind ntBW simp [ntBW]

/-- The `Bool` constructors' conjunct of `natOpGuard`, as a twin value. -/
def natBoolCtorsT (fe : IFEnv) : AM Bool := do
  let bt ← boolTrueName
  let okT ← match fe.find? bt with
    | some ci => boolCtorOk ci
    | none => pure false
  if !okT then pure false else do
    let bf ← boolFalseName
    match fe.find? bf with
    | some ci => boolCtorOk ci
    | none => pure false

theorem boolCtors_ref (hN : NatGuardProg p) :
    CallRef p "nat_op_bool_ctors" [vis] (StageR dn vis fe) (natBoolCtorsT fe)
      (KeepPost dn vis fe decW0B) := by
  refine CallRef.of_succ fun k m a r m' hS hc => ?_
  have hw := callW_model (M := fun mm => boolCtorsW p (k + 1) mm vis) (boolCtors_specW p hN.lBoolCtors (k + 1) · vis) hc
  rw [boolCtorsW.arm1] at hw
  have lastStep : ∀ (m4 : Mem) (a4 : AState) (rf : List Word) (mf : Mem) (ci : IConstantInfo)
      (rr : List Word) (mr : Mem), StageR dn vis fe m4 a4 →
      decFd dn m4 rf (some ci) → mf = m4 →
      (if rf.headD 0 = 0 then some ([0], mf) else
        ntBW (callW p k "bool_ctor_ok" [rf.tail.headD 0] mf) fun ρ μ => some ([ρ.headD 0], μ)) = some (rr, mr) →
      ∃ x a', (boolCtorOk ci).run a4 = .ok (x, a') ∧ KeepPost dn vis fe decW0B m4 mr a' rr x := by
    intro m4 a4 rf mf ci rr mr hS4 hfd hmf hb
    subst hmf
    obtain ⟨hf1, hci⟩ := hfd
    rw [if_neg (by rw [hf1]; decide)] at hb
    cases h : callW p k "bool_ctor_ok" [rf.tail.headD 0] mf with
    | none => rw [h] at hb; simp [ntBW] at hb
    | some q =>
    obtain ⟨ro, mo⟩ := q
    rw [h, bW_some] at hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    obtain ⟨x, a', hrun, hS', hg, hx⟩ := boolCtorOk_ref (dn := dn) (vis := vis) (fe := fe) hN
      (rf.tail.headD 0) ci k mf a4 ro mo ⟨hS4, hci⟩ h
    exact ⟨x, a', hrun, hS', hg, by simpa [decW0B] using hx⟩
  cases h1 : callW p k "pin_at" [30] m with
  | none => rw [h1] at hw; simp [ntBW] at hw
  | some q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, bW_some] at hw
  cases h2 : callW p k "env_find" [r1.headD 0, vis] m1 with
  | none => rw [h2] at hw; simp [ntBW] at hw
  | some q2 =>
  obtain ⟨rf, m2⟩ := q2
  rw [h2, bW_some] at hw
  obtain ⟨hm1, hm2, h0, hp1, hr1, e1, hfd⟩ := pinFind_call hN (i := 30) (by decide) hS h1 h2
  rw [hm2] at hw
  have hm1' : m1 = m := hm1
  have e1' : (pinAt 30).run a = .ok (decI (r1.headD 0), a) := e1
  cases hf : fe.find? (decI (r1.headD 0)) with
  | none =>
    rw [hf] at hfd
    have hz : rf.headD 0 = 0 := hfd
    rw [if_pos hz] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    refine ⟨false, a, ?_, hS, IWGrow.refl _, by simp [decW0B]⟩
    simp only [natBoolCtorsT, boolTrueName_eq, StateT.run_bind, e1', exc_ok_bind', hf]
    rfl
  | some ci =>
    rw [hf] at hfd
    obtain ⟨hf1, hci⟩ := hfd
    have hnz : ¬ rf.headD 0 = 0 := by rw [hf1]; decide
    rw [if_neg hnz] at hw
    cases h3 : callW p k "bool_ctor_ok" [rf.tail.headD 0] m with
    | none => rw [h3] at hw; simp [ntBW] at hw
    | some q3 =>
    obtain ⟨ro, mo⟩ := q3
    rw [h3, bW_some] at hw
    obtain ⟨x1, a1, hrun1, hS1, hg1, hx1⟩ := boolCtorOk_ref (dn := dn) (vis := vis) (fe := fe) hN
      (rf.tail.headD 0) ci k m a ro mo ⟨hS, hci⟩ h3
    by_cases hok : ro.headD 0 = 0
    · rw [if_pos hok] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      have hx : x1 = false := by
        have := hx1.1
        rw [hok] at this
        simpa using this.symm
      refine ⟨false, a1, ?_, hS1, hg1, by simp [decW0B]⟩
      simp only [natBoolCtorsT, boolTrueName_eq, StateT.run_bind, e1', exc_ok_bind', hf, hrun1, hx]
      rfl
    · rw [if_neg hok] at hw
      have hx : x1 = true := by
        have := hx1.1
        have hne : (ro.headD 0 != 0) = true := by simpa using hok
        rw [hne] at this; exact this.symm
      cases h4 : callW p k "pin_at" [31] mo with
      | none => rw [h4] at hw; simp [ntBW] at hw
      | some q4 =>
      obtain ⟨r4, m4⟩ := q4
      rw [h4, bW_some] at hw
      have hm4 : m4 = mo := (pinAt_call hN.lPinAt (j := 32) rfl h4).1
      rw [hm4] at hw
      cases h5 : callW p k "env_find" [r4.headD 0, vis] mo with
      | none => rw [h5] at hw; simp [ntBW] at hw
      | some q5 =>
      obtain ⟨rg, m5⟩ := q5
      rw [h5, bW_some] at hw
      obtain ⟨-, hm5, h0', hp4, hr4, e4, hfd2⟩ := pinFind_call hN (i := 31) (by decide) hS1 h4 (by rw [hm4]; exact h5)
      have e4' : (pinAt 31).run a1 = .ok (decI (r4.headD 0), a1) := e4
      have hm5' : m5 = mo := hm5
      cases hf2 : fe.find? (decI (r4.headD 0)) with
      | none =>
        rw [hf2] at hfd2
        have hz : rg.headD 0 = 0 := hfd2
        rw [hm5', if_pos hz] at hw
        simp only [Option.some.injEq, Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        refine ⟨false, a1, ?_, hS1, hg1, by simp [decW0B]⟩
        simp only [natBoolCtorsT, boolTrueName_eq, StateT.run_bind, e1', exc_ok_bind', hf, hrun1, hx,
          Bool.not_true, Bool.false_eq_true, if_false, boolFalseName_eq, e4', hf2]
        rfl
      | some ci2 =>
        rw [hf2] at hfd2
        obtain ⟨x2, a2, hrun2, hS2, hg2, hx2⟩ := lastStep mo a1 rg m5 ci2 r m' hS1 hfd2 hm5' hw
        refine ⟨x2, a2, ?_, hS2, hg1.trans hg2, hx2⟩
        simp only [natBoolCtorsT, boolTrueName_eq, StateT.run_bind, e1', exc_ok_bind', hf, hrun1, hx,
          Bool.not_true, Bool.false_eq_true, if_false, boolFalseName_eq, e4', hf2, hrun2]

theorem ntGetD0 (r : List Word) : r.getD 0 0 = r.headD 0 := by cases r <;> simp
theorem ntGetD1 (r : List Word) : r.getD 1 0 = r.tail.headD 0 := by
  cases r with
  | nil => simp
  | cons a t => cases t <;> simp

theorem natOpGuard_unfold (fe : IFEnv) (c : NIdx) : natOpGuard fe c = (do
    if !(← natLitSupported fe) then pure false else do
      let deps ← natOpDeps c
      if !(← natOpDepsStored fe deps) then pure false else do
        let be ← natBeqName
        let bl ← natBleName
        let dm ← natDivModNames
        if c == be || c == bl || dm.contains c then natBoolCtorsT fe else pure true) := rfl

theorem natOpGuard_ref (hN : NatGuardProg p) (c : Word) :
    CallRef p "nat_op_guard" [vis, c] (fun m a => StageR dn vis fe m a ∧ H c)
      (natOpGuard fe (decI c)) (KeepPost dn vis fe decW0B) := by
  refine CallRef.of_succ fun k m a r m' ⟨hS, hc⟩ hcall => ?_
  have hw := callW_model (M := fun mm => natOpGuardW p (k + 1) mm vis c) (natOpGuard_specW p hN.lNatOpGuard (k + 1) · vis c) hcall
  rw [natOpGuardW.arm1] at hw
  rw [natOpGuard_unfold]
  -- literals supported
  cases h1 : callW p k "nat_lit_supported" [vis] m with
  | none => rw [h1] at hw; simp [ntBW] at hw
  | some q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, bW_some] at hw
  obtain ⟨x1, a1, hrun1, hS1, hg1, hx1⟩ := natLitSupported_ref (dn := dn) (vis := vis) (fe := fe)
    hN.toNatLitProg k m a r1 m1 hS h1
  by_cases hz1 : r1.headD 0 = 0
  · rw [if_pos hz1] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hx : x1 = false := by have := hx1.1; rw [hz1] at this; simpa using this.symm
    refine ⟨false, a1, ?_, hS1, hg1, by simp [decW0B]⟩
    simp only [StateT.run_bind, hrun1, exc_ok_bind', hx, Bool.not_false, if_true]
    rfl
  rw [if_neg hz1] at hw
  have hx : x1 = true := by
    have := hx1.1; have hne : (r1.headD 0 != 0) = true := by simpa using hz1
    rw [hne] at this; exact this.symm
  -- the dependencies
  cases h2 : callW p k "nat_op_deps" [c] m1 with
  | none => rw [h2] at hw; simp [ntBW] at hw
  | some q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, bW_some] at hw
  obtain ⟨deps, a2, hrun2, hS2, hg2, hx2⟩ := natOpDeps_ref (dn := dn) (vis := vis) (fe := fe)
    hN.toNatGateProg c k m1 a1 r2 m2 ⟨hS1, hc⟩ h2
  have hd2 : decHL m2 (r2.headD 0).toNat (r2.tail.headD 0).toNat = some deps := by
    have := hx2.1; rw [ntGetD0, ntGetD1] at this; exact this
  cases h3 : callW p k "nat_op_deps_stored" [vis, r2.headD 0, r2.tail.headD 0] m2 with
  | none => rw [h3] at hw; simp [ntBW] at hw
  | some q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, bW_some] at hw
  obtain ⟨x3, a3, hrun3, hS3, hg3, hx3⟩ := natOpDepsStored_ref (dn := dn) (vis := vis) (fe := fe)
    hN.toNatGateProg (r2.headD 0) (r2.tail.headD 0) deps k m2 a2 r3 m3 ⟨hS2, hd2⟩ h3
  by_cases hz3 : r3.headD 0 = 0
  · rw [if_pos hz3] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hx' : x3 = false := by have := hx3.1; rw [hz3] at this; simpa using this.symm
    refine ⟨false, a3, ?_, hS3, hg1.trans (hg2.trans hg3), by simp [decW0B]⟩
    simp only [StateT.run_bind, hrun1, exc_ok_bind', hx, Bool.not_true, Bool.false_eq_true, if_false,
      hrun2, hrun3, hx']
    rfl
  rw [if_neg hz3] at hw
  have hx' : x3 = true := by
    have := hx3.1; have hne : (r3.headD 0 != 0) = true := by simpa using hz3
    rw [hne] at this; exact this.symm
  -- the two pinned comparison names, the division family, its membership test
  cases h4 : callW p k "pin_at" [19] m3 with
  | none => rw [h4] at hw; simp [ntBW] at hw
  | some q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [h4, bW_some] at hw
  obtain ⟨hm4, h0, hr4⟩ := pinAt_call hN.lPinAt (j := 20) rfl h4
  rw [hm4] at hw
  cases h5 : callW p k "pin_at" [20] m3 with
  | none => rw [h5] at hw; simp [ntBW] at hw
  | some q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [h5, bW_some] at hw
  obtain ⟨hm5, -, hr5⟩ := pinAt_call hN.lPinAt (j := 21) rfl h5
  rw [hm5] at hw
  have hF3 := hS3.1.pins.full h0
  have hp4 : H (r4.headD 0) := by rw [hr4]; exact hF3.names_lt 19 (by decide)
  have hp5 : H (r5.headD 0) := by rw [hr5]; exact hF3.names_lt 20 (by decide)
  have e4 : (pinAt 19).run a3 = .ok (decI (r4.headD 0), a3) := by
    have := pinAt_run hF3 19 (by decide)
    rw [hr4]; exact this
  have e5 : (pinAt 20).run a3 = .ok (decI (r5.headD 0), a3) := by
    have := pinAt_run hF3 20 (by decide)
    rw [hr5]; exact this
  cases h6 : callW p k "nat_div_mod_names" [] m3 with
  | none => rw [h6] at hw; simp [ntBW] at hw
  | some q6 =>
  obtain ⟨r6, m6⟩ := q6
  rw [h6, bW_some] at hw
  obtain ⟨dm, a6, hrun6, hS6, hg6, hx6⟩ := natDivModNames_ref (dn := dn) (vis := vis) (fe := fe)
    hN.toNatGateProg k m3 a3 r6 m6 hS3 h6
  have hd6 : decHL m6 (r6.headD 0).toNat (r6.tail.headD 0).toNat = some dm := by
    have := hx6.1; rw [ntGetD0, ntGetD1] at this; exact this
  cases h7 : callW p k "sl_contains" [r6.headD 0, r6.tail.headD 0, c] m6 with
  | none => rw [h7] at hw; simp [ntBW] at hw
  | some q7 =>
  obtain ⟨r7, m7⟩ := q7
  rw [h7, bW_some] at hw
  obtain ⟨x7, a7, hrun7, hS7, hg7, hx7⟩ := slContains_ref (dn := dn) (vis := vis) (fe := fe)
    hN.lSlContains (r6.headD 0) (r6.tail.headD 0) c dm hc k m6 a6 r7 m7 ⟨hS6, hd6⟩ h7
  have hx7a : (Except.ok (dm.contains (decI c), a6) : Except CheckError _) = Except.ok (x7, a7) := hrun7
  have hx7' : x7 = dm.contains (decI c) := (Prod.mk.inj (Except.ok.inj hx7a)).1.symm
  have ha7 : a7 = a6 := (Prod.mk.inj (Except.ok.inj hx7a)).2.symm
  subst ha7
  have hcond : ((decI c : NIdx) == decI (r4.headD 0) || (decI c : NIdx) == decI (r5.headD 0) || dm.contains (decI c)) =
      decide (c = r4.headD 0 ∨ c = r5.headD 0 ∨ r7.headD 0 ≠ 0) := by
    rw [decI_beq_word hc hp4, decI_beq_word hc hp5, ← hx7']
    have := hx7.1
    rw [← this]
    have hb : (r7.headD 0 != 0) = decide (r7.headD 0 ≠ 0) := by
      rw [Bool.eq_iff_iff]; simp
    rw [hb]
    simp only [Bool.decide_or, Bool.or_assoc]
  have hg67 : IWGrow m m7 := hg1.trans (hg2.trans (hg3.trans (hg6.trans hg7)))
  by_cases hP : c = r4.headD 0 ∨ c = r5.headD 0 ∨ r7.headD 0 ≠ 0
  · rw [if_pos hP] at hw
    cases h8 : callW p k "nat_op_bool_ctors" [vis] m7 with
    | none => rw [h8] at hw; simp [ntBW] at hw
    | some q8 =>
    obtain ⟨r8, m8⟩ := q8
    rw [h8, bW_some] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    obtain ⟨x8, a8, hrun8, hS8, hg8, hx8⟩ := boolCtors_ref (dn := dn) (vis := vis) (fe := fe) hN
      k m7 a7 r8 m8 hS7 h8
    refine ⟨x8, a8, ?_, hS8, hg67.trans hg8, by simpa [decW0B] using hx8⟩
    simp only [StateT.run_bind, hrun1, exc_ok_bind', hx, Bool.not_true, Bool.false_eq_true,
      if_false, hrun2, hrun3, hx', natBeqName_eq, natBleName_eq, e4, e5, hrun6, hrun7, hcond,
      decide_eq_true hP, Bool.not_false, if_true]
    exact hrun8
  · rw [if_neg hP] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    refine ⟨true, a7, ?_, hS7, hg67, by simp [decW0B]⟩
    simp only [StateT.run_bind, hrun1, exc_ok_bind', hx, Bool.not_true, Bool.false_eq_true,
      if_false, hrun2, hrun3, hx', natBeqName_eq, natBleName_eq, e4, e5, hrun6, hrun7, hcond,
      decide_eq_false hP]
    rfl


@[refines ConRon.Arena.natOpGuard]
theorem natOpGuard_refines (hN : NatGuardProg p) (c : Word) :
    RefAM p "nat_op_guard" [vis, c] (fun m a => StageR dn vis fe m a ∧ H c)
      (natOpGuard fe (decI c)) (KeepPost dn vis fe decW0B) :=
  (natOpGuard_ref hN c).refAM

end guard

end L.Ind
