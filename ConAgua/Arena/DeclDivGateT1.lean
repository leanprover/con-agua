import ConAgua.Arena.DeclDivMod10
import ConAgua.Arena.DeclCrpT
import ConAgua.Arena.IndStubsT
import ConRon.Bridge.Checker.DivMod

/-!
# The `Nat.div`-family pin gate under `StageC`, part 1: the guards (lane `loopt3`, `loopt3-div`)

`div_mod_pin_guard` (`pgC`) and `div_mod_cert_guard` (`cgC`) under `StageC`: their leaves by their
`StageR` refinements (`DeclDivMod*.lean`), the leaves' write set and con-ron's step lemmas
(`StageC.of_core`), the walks the stubs stand for by their `StageT` contracts (`IndStubsT.lean`)
and con-ron's `RunsC` lemmas (`lbbF_runsC`, `hasFvarF_runsC`, `alpd0_runsC`, `crF_runsC`). The twin
side follows con-ron's `divModPinGuard_run` and `divModCertGuard_run` (`Bridge/Checker/DivMod.lean`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.deprecated false

namespace L.Ind

open L.Arena
open L.Rom (PinSetsR PinSetR)
open ConRon.Bridge (CheckOK StepOK PinsDenote PinSetDenote CoreStep)

local notation "V" => ConLeche.CheckMode.verified

section helpers
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}

/-- **`StageC` across a leaf whose twin op is a `CoreStep`** (`StageC.of_leaf` for twin ops that
read through the walks' memos: con-ron gives `CheckOK` after rather than `IStepS`). -/
theorem StageC.of_core {m m' : Mem} {a a' : AState} (h : StageC dn vis fe env m a)
    (hS : StageR dn vis fe m' a') (hf : MemFrame leafA leafC m m') (hc : CoreStep V env fe a a') :
    StageC dn vis fe env m' a' :=
  ⟨hS, hc.ok,
    ⟨by rw [hf.2.2.1]; exact h.mem.erec, by rw [hf.2.2.1]; exact h.mem.spn,
      by rw [hf.2.2.1]; exact h.mem.bstk,
      h.mem.memos.frame hf leafA_memo leafC_memo leafA_walk leafC_walk leafA_lp leafC_lp,
      fun k x e => hc.ext.lss.ls.ns k x (h.mem.dnN k x e)⟩,
    by simp only [pinW, hf.1 PINS leafA_pins (by decide)]; exact h.flag⟩

/-- One leaf call of a model: its refinement's post and the leaves' frame. -/
theorem CallRef.bindL {α β : Type} {p : Prog} {f : FnName} {args : List Word}
    {pre : Mem → AState → Prop} {op : AM α} {post : Mem → Mem → AState → List Word → α → Prop}
    (h : CallRef p f args pre op post) (hcl : LeafClosed p) (hf : f ∈ leafFns) {n : Nat} {m : Mem}
    {a : AState} (hpre : pre m a) {K : List Word → Mem → Option β} {res : β}
    (hw : ntBW (callW p n f args m) K = some res) :
    ∃ r1 m1 x a1, op.run a = .ok (x, a1) ∧ post m m1 a1 r1 x ∧ MemFrame leafA leafC m m1 ∧
      K r1 m1 = some res := by
  cases hc : callW p n f args m with
  | none => rw [hc] at hw; simp at hw
  | some q =>
    obtain ⟨r1, m1⟩ := q
    rw [hc, bW_some] at hw
    obtain ⟨x, a1, hr, hp⟩ := h n m a r1 m1 hpre hc
    exact ⟨r1, m1, x, a1, hr, hp, callW_leafFrame hcl hf hc, hw⟩

/-- A twin op running as a `CoreStep`, from a `RunsC` fact. -/
theorem runsC_step {m : AM Bool} {a a' : AState} {b x : Bool}
    (h : ConRon.Bridge.RunsC V env fe m a b) (hr : m.run a = .ok (x, a')) :
    CoreStep V env fe a a' ∧ x = b :=
  h x a' hr

end helpers

/-! ## `div_mod_pin_guard` -/

section pg
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  {p : Prog}

/-- **`div_mod_pin_guard` under `StageC`** (`pg_ref`'s; con-ron's `divModPinGuard_run`): the pin by
`StageC.of_core`, the four walks by their `StageT` contracts and con-ron's `RunsC` lemmas. -/
theorem pgC (hD : DmProg6 p) (hcl : LeafClosed p) {ps c : Word} {ip : INatOpPinSet}
    {psP : ConLeche.NatOpPinSet} {nm : ConLeche.Name} {k : Nat} {m m' : Mem} {a : AState}
    {r : List Word} (hcall : callW p k "div_mod_pin_guard" [ps, vis, c] m = some (r, m'))
    (hC : StageC dn vis fe env m a) (hc : H c) (hP : PinSetR m ps ip)
    (hps : PinSetDenote a.store ip psP) (hn : denoteN a.store.ns (decI c) = some nm) :
    ∃ x a', (divModPinGuard ip fe (decI c)).run a = .ok (x, a') ∧ StageC dn vis fe env m' a' ∧
      CoreStep V env fe a a' ∧ IWGrow m m' ∧ decW0B m' r x ∧
      x = ConLeche.divModPinGuard psP env nm := by
  cases k with
  | zero => rw [callW_zero] at hcall; cases hcall
  | succ k =>
  have hw := callW_model (M := fun mq => dmPgW p k mq ps vis c)
    (pg_specW p hD.lDivModPinGuard k · ps vis c) hcall
  unfold dmPgW at hw
  have h0w : (0 : Word).toNat = 0 := rfl
  -- the run's twin facts, once the run is known
  have fin : ∀ x a', (divModPinGuard ip fe (decI c)).run a = .ok (x, a') →
      CoreStep V env fe a a' ∧ x = ConLeche.divModPinGuard psP env nm := fun x a' hr => by
    obtain ⟨h1, h2, h3, h4⟩ := ConRon.Bridge.divModPinGuard_run hC.check hps hn hr
    exact ⟨⟨h1, h2, h3⟩, h4⟩
  obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hg1, hl1, hx1⟩, hf1, hw⟩ :=
    (divModDeclPin_ref hD.toDmProg5.toDmProg2.toDmProg1 ps c ip).bindL hcl
      (leaf_mem _ (by decide)) ⟨hC.stage, hc, hP⟩ hw
  obtain ⟨e1, hpd⟩ := ConRon.Bridge.divModDeclPin_run hC.check.state hC.check.pins hps hn hrun1
  rw [e1] at hrun1 hS1
  have hC1 := StageC.of_core hC hS1 hf1 (CoreStep.refl hC.check)
  rw [← hx1] at hpd
  -- loose bvars
  cases h2 : stubM "loose_bvars_bounded_fast" m1 [4000000000, 0, r1.headD 0] with
  | none => rw [h2] at hw; simp at hw
  | some q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, bW_some] at hw
  obtain ⟨x2, a2, hrun2, hT2, hg2, hd2⟩ :=
    looseBVarsBoundedFastT_spec dn vis fe 4000000000 0 (r1.headD 0) hl1 m1 m2 a r2 h2 hC1.stageT
  rw [fuelW_eq, h0w] at hrun2
  obtain ⟨c2, -⟩ := runsC_step (ConRon.Bridge.lbbF_runsC hC1.check hpd) hrun2
  have hC2 := StageC.of_T hT2 c2.ok
  have hrun1' : (divModDeclPin ip (decI c)).run a = .ok (decI (r1.headD 0), a) := by
    rw [hx1]; exact hrun1
  by_cases z2 : r2.headD 0 = 0
  · rw [if_pos z2] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hx2 := decW0B_false hd2 z2
    have hrun : (divModPinGuard ip fe (decI c)).run a = .ok (false, a2) := by
      simp only [divModPinGuard, StateT.run_bind, hrun1', exc_ok_bind', hrun2, hx2]
      rfl
    obtain ⟨cs, hx⟩ := fin _ _ hrun
    exact ⟨false, a2, hrun, hC2, cs, hg1.trans hg2, decW0B_of_false _, hx⟩
  rw [if_neg z2] at hw
  have hx2 := decW0B_true hd2 z2
  have hpd2 := ConRon.Bridge.denote_ext hpd c2.ext
  -- has fvar
  cases h3 : stubM "has_fvar_fast" m2 [4000000000, r1.headD 0] with
  | none => rw [h3] at hw; simp at hw
  | some q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, bW_some] at hw
  obtain ⟨x3, a3, hrun3, hT3, hg3, hd3⟩ :=
    hasFvarFastT_spec dn vis fe 4000000000 (r1.headD 0) hl1 m2 m3 a2 r3 h3 hC2.stageT
  rw [fuelW_eq] at hrun3
  obtain ⟨c3, -⟩ := runsC_step (ConRon.Bridge.hasFvarF_runsC hC2.check hpd2) hrun3
  have hC3 := StageC.of_T hT3 c3.ok
  by_cases z3 : r3.headD 0 ≠ 0
  · rw [if_pos z3] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hx3 := decW0B_true hd3 z3
    have hrun : (divModPinGuard ip fe (decI c)).run a = .ok (false, a3) := by
      simp only [divModPinGuard, StateT.run_bind, hrun1', exc_ok_bind', hrun2, hx2, hrun3, hx3,
        Bool.not_true, Bool.not_false, Bool.false_eq_true, eq_self, if_true, if_false]
      rfl
    obtain ⟨cs, hx⟩ := fin _ _ hrun
    exact ⟨false, a3, hrun, hC3, cs, hg1.trans (hg2.trans hg3), decW0B_of_false _, hx⟩
  rw [if_neg z3] at hw
  have z3' : r3.headD 0 = 0 := by simpa using z3
  have hx3 := decW0B_false hd3 z3'
  have hpd3 := ConRon.Bridge.denote_ext hpd2 c3.ext
  -- all level params
  cases h4 : stubM "all_level_params_defined" m3 [0, 0, r1.headD 0] with
  | none => rw [h4] at hw; simp at hw
  | some q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [h4, bW_some] at hw
  obtain ⟨x4, a4, hrun4, hT4, hg4, hd4⟩ := allLevelParamsDefinedT_spec dn vis fe 0 0 (r1.headD 0)
    hl1 [] m3 m4 a3 r4 h4 ⟨hC3.stageT, by rw [h0w]; simp [decHL, hslice?]⟩
  obtain ⟨c4, -⟩ := runsC_step (ConRon.Bridge.alpd0_runsC hC3.check hpd3) hrun4
  have hC4 := StageC.of_T hT4 c4.ok
  by_cases z4 : r4.headD 0 = 0
  · rw [if_pos z4] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hx4 := decW0B_false hd4 z4
    have hrun : (divModPinGuard ip fe (decI c)).run a = .ok (false, a4) := by
      simp only [divModPinGuard, StateT.run_bind, hrun1', exc_ok_bind', hrun2, hx2, hrun3, hx3,
        hrun4, hx4, Bool.not_true, Bool.not_false, Bool.false_eq_true, eq_self, if_true, if_false]
      rfl
    obtain ⟨cs, hx⟩ := fin _ _ hrun
    exact ⟨false, a4, hrun, hC4, cs, hg1.trans (hg2.trans (hg3.trans hg4)), decW0B_of_false _, hx⟩
  rw [if_neg z4] at hw
  have hx4 := decW0B_true hd4 z4
  have hpd4 := ConRon.Bridge.denote_ext hpd3 c4.ext
  -- consts resolve
  cases h5 : stubM "consts_resolve_ffast" m4 [vis, r1.headD 0] with
  | none => rw [h5] at hw; simp at hw
  | some q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [h5, bW_some] at hw
  obtain ⟨x5, a5, hrun5, hT5, hg5, hd5⟩ :=
    constsResolveFFastT_spec dn vis fe (r1.headD 0) hl1 m4 m5 a4 r5 h5 hC4.stageT
  obtain ⟨c5, -⟩ := runsC_step (ConRon.Bridge.crF_runsC hC4.check hpd4) hrun5
  have hC5 := StageC.of_T hT5 c5.ok
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  have hrun : (divModPinGuard ip fe (decI c)).run a = .ok (x5, a5) := by
    simp only [divModPinGuard, StateT.run_bind, hrun1', exc_ok_bind', hrun2, hx2, hrun3, hx3,
      hrun4, hx4, Bool.not_true, Bool.not_false, Bool.false_eq_true, eq_self, if_true, if_false]
    exact hrun5
  obtain ⟨cs, hx⟩ := fin _ _ hrun
  exact ⟨x5, a5, hrun, hC5, cs, hg1.trans (hg2.trans (hg3.trans (hg4.trans hg5))), hd5, hx⟩

end pg

/-! ## `div_mod_cert_guard` -/

section cg
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  {p : Prog}

/-- **`div_mod_cert_guard` under `StageC`** (`cg_ref`'s; con-ron's `divModCertGuard_run`): the
substitutions and `consts_resolve_all` by `StageC.of_core`, the walks by their `StageT` contracts. -/
theorem cgC (hD : DmProg5 p) (hcl : LeafClosed p) (hs0 : SubstC0 p dn vis fe)
    (hsA : SubstCAll p dn vis fe) {c annVal ho hl eqE proof : Word} {hyps : List EIdx}
    {nm : ConLeche.Name} {v ex px : ConLeche.Expr} {hx : List ConLeche.Expr} {k : Nat} {m m' : Mem}
    {a : AState} {r : List Word}
    (hcall : callW p k "div_mod_cert_guard" [vis, c, annVal, ho, hl, eqE, proof] m = some (r, m'))
    (hC : StageC dn vis fe env m a) (hc : H c) (hann : H annVal) (heq : H eqE) (hpr : H proof)
    (hd : decHL m ho.toNat hl.toNat = some hyps) (hb : ho.toNat + hl.toNat ≤ iwTop m)
    (hn : denoteN a.store.ns (decI c) = some nm) (hv : denoteE a.store (decE annVal) = some v)
    (hh : Frontend.denoteEList a.store hyps = some hx) (he : denoteE a.store (decE eqE) = some ex)
    (hpf : denoteE a.store (decE proof) = some px) :
    ∃ x a', (divModCertGuard fe (decI c) (decE annVal) hyps (decE eqE) (decE proof)).run a =
        .ok (x, a') ∧ StageC dn vis fe env m' a' ∧ CoreStep V env fe a a' ∧ IWGrow m m' ∧
      decW0B m' r x ∧ x = ConLeche.divModCertGuard env nm v hx ex px := by
  cases k with
  | zero => rw [callW_zero] at hcall; cases hcall
  | succ k =>
  have hw := callW_model (M := fun mq => dmCgW p k mq vis c annVal ho hl eqE proof)
    (cg_specW p hD.lDivModCertGuard k · vis c annVal ho hl eqE proof) hcall
  unfold dmCgW at hw
  have h0w : (0 : Word).toNat = 0 := rfl
  have fin : ∀ x a', (divModCertGuard fe (decI c) (decE annVal) hyps (decE eqE) (decE proof)).run a =
      .ok (x, a') → CoreStep V env fe a a' ∧ x = ConLeche.divModCertGuard env nm v hx ex px :=
    fun x a' hr => ConRon.Bridge.divModCertGuard_run hC.check hn hv hh he hpf x a' hr
  -- subst_const_all
  obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hg1, hl1, hx1⟩, hf1, hw⟩ :=
    (hsA c annVal proof hc hann hpr).bindL hcl (leaf_mem _ (by decide)) hC.stage hw
  obtain ⟨hi1, hpd⟩ := ConRon.Bridge.substConstAll_run coreWalkFuel hC.check.state hC.check.pins
    hn hv hpf hrun1
  have c1 := ConRon.Bridge.CoreStep.of_istep hC.check hi1
  have hC1 := StageC.of_core hC hS1 hf1 c1
  -- loose bvars
  cases h2 : stubM "loose_bvars_bounded_fast" m1 [4000000000, 0, r1.headD 0] with
  | none => rw [h2] at hw; simp at hw
  | some q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, bW_some] at hw
  obtain ⟨x2, a2, hrun2, hT2, hg2, hd2⟩ :=
    looseBVarsBoundedFastT_spec dn vis fe 4000000000 0 (r1.headD 0) hl1 m1 m2 a1 r2 h2 hC1.stageT
  rw [fuelW_eq, h0w, hx1] at hrun2
  obtain ⟨c2, -⟩ := runsC_step (ConRon.Bridge.lbbF_runsC hC1.check hpd) hrun2
  have hC2 := StageC.of_T hT2 c2.ok
  by_cases z2 : r2.headD 0 = 0
  · rw [if_pos z2] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hx2 := decW0B_false hd2 z2
    have hrun : (divModCertGuard fe (decI c) (decE annVal) hyps (decE eqE) (decE proof)).run a =
        .ok (false, a2) := by
      simp only [divModCertGuard, StateT.run_bind, Bool.not_true, Bool.not_false,
        Bool.false_eq_true, eq_self, if_true, if_false, hrun1, exc_ok_bind', hrun2, hx2]
      rfl
    obtain ⟨cs, hx'⟩ := fin _ _ hrun
    exact ⟨false, a2, hrun, hC2, cs, hg1.trans hg2, decW0B_of_false _, hx'⟩
  rw [if_neg z2] at hw
  have hx2 := decW0B_true hd2 z2
  have hpd2 := ConRon.Bridge.denote_ext hpd c2.ext
  -- has fvar
  cases h3 : stubM "has_fvar_fast" m2 [4000000000, r1.headD 0] with
  | none => rw [h3] at hw; simp at hw
  | some q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, bW_some] at hw
  obtain ⟨x3, a3, hrun3, hT3, hg3, hd3⟩ :=
    hasFvarFastT_spec dn vis fe 4000000000 (r1.headD 0) hl1 m2 m3 a2 r3 h3 hC2.stageT
  rw [fuelW_eq, hx1] at hrun3
  obtain ⟨c3, -⟩ := runsC_step (ConRon.Bridge.hasFvarF_runsC hC2.check hpd2) hrun3
  have hC3 := StageC.of_T hT3 c3.ok
  by_cases z3 : r3.headD 0 ≠ 0
  · rw [if_pos z3] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hx3 := decW0B_true hd3 z3
    have hrun : (divModCertGuard fe (decI c) (decE annVal) hyps (decE eqE) (decE proof)).run a =
        .ok (false, a3) := by
      simp only [divModCertGuard, StateT.run_bind, Bool.not_true, Bool.not_false,
        Bool.false_eq_true, eq_self, if_true, if_false, hrun1, exc_ok_bind', hrun2, hx2, hrun3, hx3]
      rfl
    obtain ⟨cs, hx'⟩ := fin _ _ hrun
    exact ⟨false, a3, hrun, hC3, cs, hg1.trans (hg2.trans hg3), decW0B_of_false _, hx'⟩
  rw [if_neg z3] at hw
  have z3' : r3.headD 0 = 0 := by simpa using z3
  have hx3 := decW0B_false hd3 z3'
  have hpd3 := ConRon.Bridge.denote_ext hpd2 c3.ext
  -- all level params
  cases h4 : stubM "all_level_params_defined" m3 [0, 0, r1.headD 0] with
  | none => rw [h4] at hw; simp at hw
  | some q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [h4, bW_some] at hw
  obtain ⟨x4, a4, hrun4, hT4, hg4, hd4⟩ := allLevelParamsDefinedT_spec dn vis fe 0 0 (r1.headD 0)
    hl1 [] m3 m4 a3 r4 h4 ⟨hC3.stageT, by rw [h0w]; simp [decHL, hslice?]⟩
  rw [hx1] at hrun4
  obtain ⟨c4, -⟩ := runsC_step (ConRon.Bridge.alpd0_runsC hC3.check hpd3) hrun4
  have hC4 := StageC.of_T hT4 c4.ok
  by_cases z4 : r4.headD 0 = 0
  · rw [if_pos z4] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hx4 := decW0B_false hd4 z4
    have hrun : (divModCertGuard fe (decI c) (decE annVal) hyps (decE eqE) (decE proof)).run a =
        .ok (false, a4) := by
      simp only [divModCertGuard, StateT.run_bind, Bool.not_true, Bool.not_false,
        Bool.false_eq_true, eq_self, if_true, if_false, hrun1, exc_ok_bind', hrun2, hx2, hrun3, hx3,
        hrun4, hx4]
      rfl
    obtain ⟨cs, hx'⟩ := fin _ _ hrun
    exact ⟨false, a4, hrun, hC4, cs, hg1.trans (hg2.trans (hg3.trans hg4)), decW0B_of_false _, hx'⟩
  rw [if_neg z4] at hw
  have hx4 := decW0B_true hd4 z4
  have hpd4 := ConRon.Bridge.denote_ext hpd3 c4.ext
  -- consts resolve of the proof
  cases h5 : stubM "consts_resolve_ffast" m4 [vis, r1.headD 0] with
  | none => rw [h5] at hw; simp at hw
  | some q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [h5, bW_some] at hw
  obtain ⟨x5, a5, hrun5, hT5, hg5, hd5⟩ :=
    constsResolveFFastT_spec dn vis fe (r1.headD 0) hl1 m4 m5 a4 r5 h5 hC4.stageT
  rw [hx1] at hrun5
  obtain ⟨c5, -⟩ := runsC_step (ConRon.Bridge.crF_runsC hC4.check hpd4) hrun5
  have hC5 := StageC.of_T hT5 c5.ok
  have hG5 : IWGrow m m5 := hg1.trans (hg2.trans (hg3.trans (hg4.trans hg5)))
  have c15 := (((c1.trans c2).trans c3).trans c4).trans c5
  by_cases z5 : r5.headD 0 = 0
  · rw [if_pos z5] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hx5 := decW0B_false hd5 z5
    have hrun : (divModCertGuard fe (decI c) (decE annVal) hyps (decE eqE) (decE proof)).run a =
        .ok (false, a5) := by
      simp only [divModCertGuard, StateT.run_bind, Bool.not_true, Bool.not_false,
        Bool.false_eq_true, eq_self, if_true, if_false, hrun1, exc_ok_bind', hrun2, hx2, hrun3, hx3,
        hrun4, hx4, hrun5, hx5]
      rfl
    obtain ⟨cs, hx'⟩ := fin _ _ hrun
    exact ⟨false, a5, hrun, hC5, cs, hG5, decW0B_of_false _, hx'⟩
  rw [if_neg z5] at hw
  have hx5 := decW0B_true hd5 z5
  -- the hypotheses, substituted
  cases h6 : callW p k "subst_const0_list" [c, annVal, ho, hl] m5 with
  | none => rw [h6] at hw; simp at hw
  | some q6 =>
  obtain ⟨r6, m6⟩ := q6
  rw [h6, bW_some] at hw
  have hd5' : decHL m5 ho.toNat hl.toNat = some hyps := by
    rw [decHL_grow hG5 hb]; exact hd
  have hb5 : ho.toNat + hl.toNat ≤ iwTop m5 := Nat.le_trans hb hG5.1
  obtain ⟨x6, a6, hrun6, hS6, hg6, hd6⟩ :=
    sc0List_ref hD hs0 c annVal hc hann hyps ho hl k m5 a5 r6 m6 hC5.stage hd5' hb5 h6
  simp only [decRL, Nat.zero_add, ntGetD0, ntGetD1] at hd6
  obtain ⟨hi6, hhs⟩ := ConRon.Bridge.substConst0List_run hyps hx hC5.check.state hC5.check.pins
    (ConRon.Bridge.denoteN_ext hn c15.ext) (ConRon.Bridge.denote_ext hv c15.ext)
    (ConRon.Bridge.denoteEList_ext c15.ext _ _ hh) hrun6
  have c6 := ConRon.Bridge.CoreStep.of_istep hC5.check hi6
  have hC6 := StageC.of_core hC5 hS6 (callW_leafFrame hcl (leaf_mem _ (by decide)) h6) c6
  -- consts resolve of the hypotheses
  cases h7 : callW p k "consts_resolve_all" [vis, r6.headD 0, r6.tail.headD 0] m6 with
  | none => rw [h7] at hw; simp at hw
  | some q7 =>
  obtain ⟨r7, m7⟩ := q7
  rw [h7, bW_some] at hw
  obtain ⟨x7, a7, hrun7, hS7, hg7, hd7⟩ := cra_ref hD vis rfl x6 (r6.headD 0) (r6.tail.headD 0) k m6
    a6 r7 m7 hC6.stage hd6.1 hd6.2 h7
  obtain ⟨c7, -⟩ := runsC_step (ConRon.Bridge.constsResolveAll_runsC _ _ hC6.check hhs) hrun7
  have hC7 := StageC.of_core hC6 hS7 (callW_leafFrame hcl (leaf_mem _ (by decide)) h7) c7
  have hG7 : IWGrow m m7 := hG5.trans (hg6.trans hg7)
  by_cases z7 : r7.headD 0 = 0
  · rw [if_pos z7] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hx7 := decW0B_false hd7 z7
    have hrun : (divModCertGuard fe (decI c) (decE annVal) hyps (decE eqE) (decE proof)).run a =
        .ok (false, a7) := by
      simp only [divModCertGuard, StateT.run_bind, Bool.not_true, Bool.not_false,
        Bool.false_eq_true, eq_self, if_true, if_false, hrun1, exc_ok_bind', hrun2, hx2, hrun3, hx3,
        hrun4, hx4, hrun5, hx5, hrun6, hrun7, hx7]
      rfl
    obtain ⟨cs, hx'⟩ := fin _ _ hrun
    exact ⟨false, a7, hrun, hC7, cs, hG7, decW0B_of_false _, hx'⟩
  rw [if_neg z7] at hw
  have hx7 := decW0B_true hd7 z7
  have c17 := (c15.trans c6).trans c7
  -- the equation, substituted
  cases h8 : callW p k "subst_const0" [c, annVal, 4000000000, eqE] m7 with
  | none => rw [h8] at hw; simp at hw
  | some q8 =>
  obtain ⟨r8, m8⟩ := q8
  rw [h8, bW_some] at hw
  obtain ⟨x8, a8, hrun8, hS8, hg8, hl8, hx8⟩ := hs0 c annVal eqE hc hann heq k m7 a7 r8 m8 hC7.stage h8
  obtain ⟨hi8, he8⟩ := ConRon.Bridge.substConst0_run coreWalkFuel hC7.check.state hC7.check.pins
    (ConRon.Bridge.denoteN_ext hn c17.ext) (ConRon.Bridge.denote_ext hv c17.ext)
    (ConRon.Bridge.denote_ext he c17.ext) hrun8
  have c8 := ConRon.Bridge.CoreStep.of_istep hC7.check hi8
  have hC8 := StageC.of_core hC7 hS8 (callW_leafFrame hcl (leaf_mem _ (by decide)) h8) c8
  cases h9 : stubM "consts_resolve_ffast" m8 [vis, r8.headD 0] with
  | none => rw [h9] at hw; simp at hw
  | some q9 =>
  obtain ⟨r9, m9⟩ := q9
  rw [h9, bW_some] at hw
  obtain ⟨x9, a9, hrun9, hT9, hg9, hd9⟩ :=
    constsResolveFFastT_spec dn vis fe (r8.headD 0) hl8 m8 m9 a8 r9 h9 hC8.stageT
  rw [hx8] at hrun9
  obtain ⟨c9, -⟩ := runsC_step (ConRon.Bridge.crF_runsC hC8.check he8) hrun9
  have hC9 := StageC.of_T hT9 c9.ok
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  have hrun : (divModCertGuard fe (decI c) (decE annVal) hyps (decE eqE) (decE proof)).run a =
      .ok (x9, a9) := by
    simp only [divModCertGuard, StateT.run_bind, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, eq_self, if_true, if_false, hrun1, exc_ok_bind', hrun2, hx2, hrun3, hx3,
      hrun4, hx4, hrun5, hx5, hrun6, hrun7, hx7, hrun8, hrun9]
  obtain ⟨cs, hx'⟩ := fin _ _ hrun
  exact ⟨x9, a9, hrun, hC9, cs, hG7.trans (hg8.trans hg9), hd9, hx'⟩

end cg

end L.Ind
