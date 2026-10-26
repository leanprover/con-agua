import ConAgua.Arena.DeclDivMod10
import ConAgua.Arena.DeclCrpT
import ConAgua.Arena.StageTLift
import ConAgua.Arena.IndRealMemoCrT
import ConAgua.Arena.IndRealApdT
import ConAgua.Arena.IndRealWalkT
import ConRon.Bridge.Checker.DivMod

/-!
# The `Nat.div`-family pin gate under `StageC`, part 1: the guards (lane `loopt3`, `loopt3-div`)

`div_mod_pin_guard` (`pgC`) and `div_mod_cert_guard` (`cgC`) under `StageC`: their leaves by their
`StageR` refinements (`DeclDivMod*.lean`), the leaves' write set and con-ron's step lemmas
(`StageC.of_core`), the walks the stubs stand for by their `StageT` refinements (`IndRealWalkT.lean`, `apdF_okT`,
`crfF_okT` with `consts_resolve_ffast`'s memo threaded: `CrKeep`, `CrOKFrame.lean`)
and con-ron's `RunsC` lemmas (`lbbF_runsC`, `hasFvarF_runsC`, `alpd0_runsC`, `crF_runsC`). The twin
side follows con-ron's `divModPinGuard_run` and `divModCertGuard_run` (`Bridge/Checker/DivMod.lean`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

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

/-- `CallRef.bindL` with `consts_resolve_ffast`'s memo carried across the leaf (`CrKeep.call`). -/
theorem CallRef.bindLC {α β : Type} {p : Prog} {f : FnName} {args : List Word}
    {pre : Mem → AState → Prop} {op : AM α} {post : Mem → Mem → AState → List Word → α → Prop}
    (h : CallRef p f args pre op post) (hcl : LeafClosed p) (hf : f ∈ leafFns) (hkp : CrKeep p)
    (hfi : f ∈ imFns) {n : Nat} {m : Mem} {a : AState} (hpre : pre m a) (hCr : L.Stubs.CrOK m)
    {K : List Word → Mem → Option β} {res : β} (hw : ntBW (callW p n f args m) K = some res) :
    ∃ r1 m1 x a1, op.run a = .ok (x, a1) ∧ post m m1 a1 r1 x ∧ MemFrame leafA leafC m m1 ∧
      L.Stubs.CrOK m1 ∧ K r1 m1 = some res := by
  cases hc : callW p n f args m with
  | none => rw [hc] at hw; simp at hw
  | some q =>
    obtain ⟨r1, m1⟩ := q
    rw [hc, bW_some] at hw
    obtain ⟨x, a1, hr, hp⟩ := h n m a r1 m1 hpre hc
    exact ⟨r1, m1, x, a1, hr, hp, callW_leafFrame hcl hf hc, hkp.call hfi hc hCr, hw⟩

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
theorem pgC (hD : DmProg6 p) (hcl : LeafClosed p) (hkp : CrKeep p) {ps c : Word} {ip : INatOpPinSet}
    {psP : ConLeche.NatOpPinSet} {nm : ConLeche.Name} {k : Nat} {m m' : Mem} {a : AState}
    {r : List Word} (hcall : callW p k "div_mod_pin_guard" [ps, vis, c] m = some (r, m'))
    (hC : StageC dn vis fe env m a) (hc : H c) (hP : PinSetR m ps ip)
    (hps : PinSetDenote a.store ip psP) (hn : denoteN a.store.ns (decI c) = some nm)
    (hCr : L.Stubs.CrOK m) :
    ∃ x a', (divModPinGuard ip fe (decI c)).run a = .ok (x, a') ∧ StageC dn vis fe env m' a' ∧
      CoreStep V env fe a a' ∧ IWGrow m m' ∧ decW0B m' r x ∧
      x = ConLeche.divModPinGuard psP env nm := by
  cases k with
  | zero => rw [callW_zero] at hcall; cases hcall
  | succ k =>
  have hw := callW_model (M := fun mq => dmPgW p (realCall p) k mq ps vis c)
    (pg_specW p hD.bvb hD.hf hD.lDivModPinGuard (realCall p) (realCall_spec p) k · ps vis c) hcall
  unfold dmPgW at hw
  have h0w : (0 : Word).toNat = 0 := rfl
  -- the run's twin facts, once the run is known
  have fin : ∀ x a', (divModPinGuard ip fe (decI c)).run a = .ok (x, a') →
      CoreStep V env fe a a' ∧ x = ConLeche.divModPinGuard psP env nm := fun x a' hr => by
    obtain ⟨h1, h2, h3, h4⟩ := ConRon.Bridge.divModPinGuard_run hC.check hps hn hr
    exact ⟨⟨h1, h2, h3⟩, h4⟩
  obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hg1, hl1, hx1⟩, hf1, hCr1, hw⟩ :=
    (divModDeclPin_ref hD.toDmProg5.toDmProg2.toDmProg1 ps c ip).bindLC hcl
      (leaf_mem _ (by decide)) hkp (im_mem _ rfl) ⟨hC.stage, hc, hP⟩ hCr hw
  obtain ⟨e1, hpd⟩ := ConRon.Bridge.divModDeclPin_run hC.check.state hC.check.pins hps hn hrun1
  rw [e1] at hrun1 hS1
  have hC1 := StageC.of_core hC hS1 hf1 (CoreStep.refl hC.check)
  rw [← hx1] at hpd
  -- loose bvars
  cases h2 : lbbF m1 [4000000000, 0, r1.headD 0] with
  | none => rw [h2] at hw; simp at hw
  | some q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, bW_some] at hw
  have hCr2 := CrOK.frame hCr1 (lbbF_frame h2) (by decide) (by decide)
  obtain ⟨x2, a2, hrun2, hT2, hg2, hd2⟩ :=
    lbbF_okT dn vis fe 4000000000 0 (r1.headD 0) hl1 m1 m2 a r2 h2 hC1.stageT
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
  cases h3 : hffF m2 [4000000000, r1.headD 0] with
  | none => rw [h3] at hw; simp at hw
  | some q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, bW_some] at hw
  have hCr3 := CrOK.frame hCr2 (hffF_frame h3) (by decide) (by decide)
  obtain ⟨x3, a3, hrun3, hT3, hg3, hd3⟩ :=
    hffF_okT dn vis fe 4000000000 (r1.headD 0) hl1 m2 m3 a2 r3 h3 hC2.stageT
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
  cases h4 : realCall p k "all_level_params_defined" [0, 0, r1.headD 0] m3 with
  | none => rw [h4] at hw; simp at hw
  | some q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [h4, bW_some] at hw
  have hCr4 := CrOK.frame hCr3 (apdF_frame (apdF_of_callW hD.apd h4)) (by decide) (by decide)
  obtain ⟨x4, a4, hrun4, hT4, hg4, hd4⟩ := apdF_okT dn vis fe 0 0 (r1.headD 0)
    hl1 [] m3 m4 a3 r4 (apdF_of_callW hD.apd h4) ⟨hC3.stageT, by rw [h0w]; simp [decHL, hslice?], [], rfl⟩
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
  cases h5 : realCall p k "consts_resolve_ffast" [vis, r1.headD 0] m4 with
  | none => rw [h5] at hw; simp at hw
  | some q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [h5, bW_some] at hw
  obtain ⟨x5, a5, hrun5, ⟨hT5, hg5, hd5⟩, -⟩ :=
    crfF_okT dn vis fe (r1.headD 0) hl1 m4 m5 a4 r5 (crfF_of_callW hkp.crf h5) ⟨hC4.stageT, hCr4.crMemo⟩
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

/-- **`consts_resolve_all` under `StageT`** (`cra_ref`'s, `consts_resolve_ffast` by `crfF_okT`
with its memo `CrOK` threaded). -/
theorem cra_refT (hD : DmProg5 p) (hkp : CrKeep p) :
    ∀ (hyps : List EIdx) (o l : Word) (k : Nat) (m : Mem) (a : AState) (res : List Word) (m' : Mem),
      StageT dn vis fe m a → L.Stubs.CrOK m → decHL m o.toNat l.toNat = some hyps →
      o.toNat + l.toNat ≤ iwTop m →
      callW p k "consts_resolve_all" [vis, o, l] m = some (res, m') →
      ∃ x a', (constsResolveAll fe hyps).run a = .ok (x, a') ∧
        KeepPostT dn vis fe decW0B m m' a' res x ∧ L.Stubs.CrOK m' := by
  intro hyps
  induction hyps with
  | nil =>
    intro o l k m a res m' hT hCr hd hb hc
    have hl0 : l = 0 := by
      have := decHL_length m hd
      exact UInt64.toNat_inj.mp (by simp at this ⊢; omega)
    cases k with
    | zero => rw [callW_zero] at hc; cases hc
    | succ k =>
    have hw := callW_model (M := fun mm => craW p (realCall p) k mm vis o l)
      (cra_specW p hD.lConstsResolveAll (realCall p) (realCall_spec p) k · vis o l) hc
    simp only [craW, hl0, if_true, Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact ⟨true, a, rfl, ⟨hT, IWGrow.refl _, by simp [decW0B]⟩, hCr⟩
  | cons h hs ih =>
    intro o l k m a res m' hT hCr hd hb hc
    cases k with
    | zero => rw [callW_zero] at hc; cases hc
    | succ k =>
    obtain ⟨hl0, hwlt, hh, hrest⟩ := decHL_cons_iw hT.stage.2.2.2.1 hd
    subst hh
    have hw := callW_model (M := fun mm => craW p (realCall p) k mm vis o l)
      (cra_specW p hD.lConstsResolveAll (realCall p) (realCall_spec p) k · vis o l) hc
    unfold craW at hw
    rw [if_neg hl0] at hw
    cases h1 : realCall p k "consts_resolve_ffast" [vis, rdW (m.arr64 IW) o] m with
    | none => rw [h1] at hw; simp at hw
    | some q1 =>
    obtain ⟨r1, m1⟩ := q1
    rw [h1, bW_some] at hw
    obtain ⟨x1, a1, hrun1, ⟨hT1, hg1, hd1⟩, hCr1⟩ :=
      crfF_okT dn vis fe _ hwlt m m1 a r1 (crfF_of_callW hkp.crf h1) ⟨hT, hCr.crMemo⟩
    by_cases hz : r1.headD 0 = 0
    · rw [if_pos hz] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      have hx1 : x1 = false := by
        have := hd1.1; rw [hz] at this; simpa using this.symm
      refine ⟨false, a1, ?_, ⟨hT1, hg1, by simp [decW0B]⟩, hCr1.crOK⟩
      simp only [constsResolveAll, StateT.run_bind, hrun1, exc_ok_bind', hx1, Bool.false_eq_true,
        if_false, StateT.run_pure]
      rfl
    · rw [if_neg hz] at hw
      have hx1 : x1 = true := by
        have := hd1.1
        have e : (r1.headD 0 != 0) = true := by simpa using hz
        rw [e] at this; exact this.symm
      replace hw := ntBW_some hw; obtain ⟨r2, m2, h2, hw⟩ := hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      have hsz := hT.stage.2.2.2.1
      have hlpos : 0 < l.toNat := Nat.pos_of_ne_zero (fun e => hl0 (UInt64.toNat_inj.mp (by simpa using e)))
      have ho1 : (o + 1).toNat = o.toNat + 1 := by
        have hb := decHL_bnd m o l hd hsz
        rw [UInt64.toNat_add]; simp; omega
      have hl1' : (l - 1).toNat = l.toNat - 1 := by
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
      have hrest1 : decHL m1 (o + 1).toNat (l - 1).toNat = some hs := by
        rw [ho1, hl1']
        rw [ho1, hl1'] at hrest
        rw [decHL_grow hg1 (by omega)]; exact hrest
      obtain ⟨x2, a2, hrun2, ⟨hT2, hg2, hd2⟩, hCr2⟩ := ih (o + 1) (l - 1) k m1 a1 r2 m2 hT1 hCr1.crOK
        hrest1 (by rw [ho1, hl1']; have := hg1.1; omega) h2
      refine ⟨x2, a2, ?_, ⟨hT2, hg1.trans hg2, hd2⟩, hCr2⟩
      simp only [constsResolveAll, StateT.run_bind, hrun1, exc_ok_bind', hx1, if_true]
      exact hrun2

/-- **`div_mod_cert_guard` under `StageC`** (`cg_ref`'s; con-ron's `divModCertGuard_run`): the
substitutions and `consts_resolve_all` by `StageC.of_core`, the walks by their `StageT` contracts. -/
theorem cgC (hD : DmProg5 p) (hcl : LeafClosed p) (hkp : CrKeep p) (hs0 : SubstC0 p dn vis fe)
    (hsA : SubstCAll p dn vis fe) {c annVal ho hl eqE proof : Word} {hyps : List EIdx}
    {nm : ConLeche.Name} {v ex px : ConLeche.Expr} {hx : List ConLeche.Expr} {k : Nat} {m m' : Mem}
    {a : AState} {r : List Word}
    (hcall : callW p k "div_mod_cert_guard" [vis, c, annVal, ho, hl, eqE, proof] m = some (r, m'))
    (hC : StageC dn vis fe env m a) (hc : H c) (hann : H annVal) (heq : H eqE) (hpr : H proof)
    (hd : decHL m ho.toNat hl.toNat = some hyps) (hb : ho.toNat + hl.toNat ≤ iwTop m)
    (hn : denoteN a.store.ns (decI c) = some nm) (hv : denoteE a.store (decE annVal) = some v)
    (hh : Frontend.denoteEList a.store hyps = some hx) (he : denoteE a.store (decE eqE) = some ex)
    (hpf : denoteE a.store (decE proof) = some px) (hCr : L.Stubs.CrOK m) :
    ∃ x a', (divModCertGuard fe (decI c) (decE annVal) hyps (decE eqE) (decE proof)).run a =
        .ok (x, a') ∧ StageC dn vis fe env m' a' ∧ CoreStep V env fe a a' ∧ IWGrow m m' ∧
      decW0B m' r x ∧ x = ConLeche.divModCertGuard env nm v hx ex px := by
  cases k with
  | zero => rw [callW_zero] at hcall; cases hcall
  | succ k =>
  have hw := callW_model (M := fun mq => dmCgW p (realCall p) k mq vis c annVal ho hl eqE proof)
    (cg_specW p hD.bvb hD.hf hD.lDivModCertGuard (realCall p) (realCall_spec p) k · vis c annVal ho
      hl eqE proof) hcall
  unfold dmCgW at hw
  have h0w : (0 : Word).toNat = 0 := rfl
  have fin : ∀ x a', (divModCertGuard fe (decI c) (decE annVal) hyps (decE eqE) (decE proof)).run a =
      .ok (x, a') → CoreStep V env fe a a' ∧ x = ConLeche.divModCertGuard env nm v hx ex px :=
    fun x a' hr => ConRon.Bridge.divModCertGuard_run hC.check hn hv hh he hpf x a' hr
  -- subst_const_all
  obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hg1, hl1, hx1⟩, hf1, hCr1, hw⟩ :=
    (hsA c annVal proof hc hann hpr).bindLC hcl (leaf_mem _ (by decide)) hkp (im_mem _ rfl)
      hC.stage hCr hw
  obtain ⟨hi1, hpd⟩ := ConRon.Bridge.substConstAll_run coreWalkFuel hC.check.state hC.check.pins
    hn hv hpf hrun1
  have c1 := ConRon.Bridge.CoreStep.of_istep hC.check hi1
  have hC1 := StageC.of_core hC hS1 hf1 c1
  -- loose bvars
  cases h2 : lbbF m1 [4000000000, 0, r1.headD 0] with
  | none => rw [h2] at hw; simp at hw
  | some q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, bW_some] at hw
  have hCr2 := CrOK.frame hCr1 (lbbF_frame h2) (by decide) (by decide)
  obtain ⟨x2, a2, hrun2, hT2, hg2, hd2⟩ :=
    lbbF_okT dn vis fe 4000000000 0 (r1.headD 0) hl1 m1 m2 a1 r2 h2 hC1.stageT
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
  cases h3 : hffF m2 [4000000000, r1.headD 0] with
  | none => rw [h3] at hw; simp at hw
  | some q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, bW_some] at hw
  have hCr3 := CrOK.frame hCr2 (hffF_frame h3) (by decide) (by decide)
  obtain ⟨x3, a3, hrun3, hT3, hg3, hd3⟩ :=
    hffF_okT dn vis fe 4000000000 (r1.headD 0) hl1 m2 m3 a2 r3 h3 hC2.stageT
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
  cases h4 : realCall p k "all_level_params_defined" [0, 0, r1.headD 0] m3 with
  | none => rw [h4] at hw; simp at hw
  | some q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [h4, bW_some] at hw
  have hCr4 := CrOK.frame hCr3 (apdF_frame (apdF_of_callW hD.apd h4)) (by decide) (by decide)
  obtain ⟨x4, a4, hrun4, hT4, hg4, hd4⟩ := apdF_okT dn vis fe 0 0 (r1.headD 0)
    hl1 [] m3 m4 a3 r4 (apdF_of_callW hD.apd h4) ⟨hC3.stageT, by rw [h0w]; simp [decHL, hslice?], [], rfl⟩
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
  cases h5 : realCall p k "consts_resolve_ffast" [vis, r1.headD 0] m4 with
  | none => rw [h5] at hw; simp at hw
  | some q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [h5, bW_some] at hw
  obtain ⟨x5, a5, hrun5, ⟨hT5, hg5, hd5⟩, hCr5⟩ :=
    crfF_okT dn vis fe (r1.headD 0) hl1 m4 m5 a4 r5 (crfF_of_callW hkp.crf h5) ⟨hC4.stageT, hCr4.crMemo⟩
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
  replace hw := ntBW_some hw; obtain ⟨r6, m6, h6, hw⟩ := hw
  have hd5' : decHL m5 ho.toNat hl.toNat = some hyps := by
    rw [decHL_grow hG5 hb]; exact hd
  have hb5 : ho.toNat + hl.toNat ≤ iwTop m5 := Nat.le_trans hb hG5.1
  have hCr6 := hkp.call (im_mem _ rfl) h6 hCr5.crOK
  obtain ⟨x6, a6, hrun6, hS6, hg6, hd6⟩ :=
    sc0List_ref hD hs0 c annVal hc hann hyps ho hl k m5 a5 r6 m6 hC5.stage hd5' hb5 h6
  simp only [decRL, Nat.zero_add, ntGetD0, ntGetD1] at hd6
  obtain ⟨hi6, hhs⟩ := ConRon.Bridge.substConst0List_run hyps hx hC5.check.state hC5.check.pins
    (ConRon.Bridge.denoteN_ext hn c15.ext) (ConRon.Bridge.denote_ext hv c15.ext)
    (ConRon.Bridge.denoteEList_ext c15.ext _ _ hh) hrun6
  have c6 := ConRon.Bridge.CoreStep.of_istep hC5.check hi6
  have hC6 := StageC.of_core hC5 hS6 (callW_leafFrame hcl (leaf_mem _ (by decide)) h6) c6
  -- consts resolve of the hypotheses
  replace hw := ntBW_some hw; obtain ⟨r7, m7, h7, hw⟩ := hw
  obtain ⟨x7, a7, hrun7, ⟨hT7, hg7, hd7⟩, hCr7⟩ := cra_refT hD hkp x6 (r6.headD 0) (r6.tail.headD 0)
    k m6 a6 r7 m7 hC6.stageT hCr6 hd6.1 hd6.2 h7
  obtain ⟨c7, -⟩ := runsC_step (ConRon.Bridge.constsResolveAll_runsC _ _ hC6.check hhs) hrun7
  have hC7 := StageC.of_T hT7 c7.ok
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
  replace hw := ntBW_some hw; obtain ⟨r8, m8, h8, hw⟩ := hw
  have hCr8 := hkp.call (im_mem _ rfl) h8 hCr7
  obtain ⟨x8, a8, hrun8, hS8, hg8, hl8, hx8⟩ := hs0 c annVal eqE hc hann heq k m7 a7 r8 m8 hC7.stage h8
  obtain ⟨hi8, he8⟩ := ConRon.Bridge.substConst0_run coreWalkFuel hC7.check.state hC7.check.pins
    (ConRon.Bridge.denoteN_ext hn c17.ext) (ConRon.Bridge.denote_ext hv c17.ext)
    (ConRon.Bridge.denote_ext he c17.ext) hrun8
  have c8 := ConRon.Bridge.CoreStep.of_istep hC7.check hi8
  have hC8 := StageC.of_core hC7 hS8 (callW_leafFrame hcl (leaf_mem _ (by decide)) h8) c8
  cases h9 : realCall p k "consts_resolve_ffast" [vis, r8.headD 0] m8 with
  | none => rw [h9] at hw; simp at hw
  | some q9 =>
  obtain ⟨r9, m9⟩ := q9
  rw [h9, bW_some] at hw
  obtain ⟨x9, a9, hrun9, ⟨hT9, hg9, hd9⟩, -⟩ :=
    crfF_okT dn vis fe (r8.headD 0) hl8 m8 m9 a8 r9 (crfF_of_callW hkp.crf h9) ⟨hC8.stageT, hCr8.crMemo⟩
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

/-! ## `div_mod_certs_guard_go`, `div_mod_certs_guard` -/

section cgs
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  {p : Prog}

/-- **`div_mod_certs_guard_go` under `StageC`** (`cggo_ref`'s; con-ron's `divModCertsGuardGo_run`). -/
theorem cggoC (hD : DmProg6 p) (hcl : LeafClosed p) (hkp : CrKeep p) (hs0 : SubstC0 p dn vis fe)
    (hsA : SubstCAll p dn vis fe) (c annVal : Word) (hc : H c) (hann : H annVal)
    {nm : ConLeche.Name} {v : ConLeche.Expr} :
    ∀ (ss : List (List EIdx × EIdx)) (xs : List (List ConLeche.Expr × ConLeche.Expr))
      (proofs : List EIdx) (ps : List ConLeche.Expr) (so sl po pl : Word) (k : Nat) (m : Mem)
      (a : AState) (res : List Word) (m' : Mem), StageC dn vis fe env m a → L.Stubs.CrOK m →
      StmtL m so.toNat sl.toNat ss → decHL m po.toNat pl.toNat = some proofs →
      po.toNat + pl.toNat ≤ iwTop m → denoteN a.store.ns (decI c) = some nm →
      denoteE a.store (decE annVal) = some v → ConRon.Bridge.StmtsDenote a.store ss xs →
      Frontend.denoteEList a.store proofs = some ps →
      callW p k "div_mod_certs_guard_go" [vis, c, annVal, so, sl, po, pl] m = some (res, m') →
      ∃ x a', (divModCertsGuardGo fe (decI c) (decE annVal) ss proofs).run a = .ok (x, a') ∧
        StageC dn vis fe env m' a' ∧ CoreStep V env fe a a' ∧ IWGrow m m' ∧ decW0B m' res x := by
  intro ss
  induction ss with
  | nil =>
    intro xs proofs ps so sl po pl k m a res m' hC _ hs hd hb hn hv hsd hpr hc'
    have hsl : sl = 0 := UInt64.toNat_inj.mp (by have := hs.2.1; simpa using this)
    cases k with
    | zero => rw [callW_zero] at hc'; cases hc'
    | succ k =>
    have hw := callW_model (M := fun mq => cggoW p (k + 1) mq vis c annVal so sl po pl)
      (cggo_specW p hD.lCertsGuardGo (k + 1) · vis c annVal so sl po pl) hc'
    simp only [cggoW.eq_2, hsl, true_or, if_true, Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact ⟨true, a, by cases proofs <;> rfl, hC, CoreStep.refl hC.check, IWGrow.refl _,
      by simp [decW0B]⟩
  | cons st ss ih =>
    rcases st with ⟨hy, eqq⟩
    intro xs proofs ps so sl po pl k m a res m' hC hCr hs hd hb hn hv hsd hpr hc'
    cases xs with
    | nil => exact hsd.elim
    | cons xq xrest =>
    obtain ⟨hx, ex⟩ := xq
    obtain ⟨hsd1, hsd2, hsd3⟩ := hsd
    cases k with
    | zero => rw [callW_zero] at hc'; cases hc'
    | succ k =>
    have hw := callW_model (M := fun mq => cggoW p (k + 1) mq vis c annVal so sl po pl)
      (cggo_specW p hD.lCertsGuardGo (k + 1) · vis c annVal so sl po pl) hc'
    rw [cggoW.eq_2] at hw
    have hS := hC.stage
    cases proofs with
    | nil =>
      have hpl : pl = 0 := UInt64.toNat_inj.mp (by have := decHL_length m hd; simp at this ⊢; omega)
      simp only [hpl, or_true, if_true, Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      exact ⟨true, a, rfl, hC, CoreStep.refl hC.check, IWGrow.refl _, by simp [decW0B]⟩
    | cons pf pfs =>
    obtain ⟨px, pxs, hpx, hpxs, rfl⟩ := ConRon.Bridge.denoteEList_cons hpr
    obtain ⟨hsl0, q, hq, hstm, hrest⟩ := StmtL.cons hS.2 hs
    obtain ⟨hpl0, hpwlt, hpf, hdrest⟩ := decHL_cons_iw hS.2.2.2.1 hd
    subst hpf
    obtain ⟨ho, hl, e, hr3, hbd, hdh, he, hst2⟩ := hstm
    obtain ⟨hp3, h0, h1, h2⟩ := hr3
    have hst2' : eqq = decE e := hst2
    subst hst2'
    rw [if_neg (by simp [hsl0, hpl0])] at hw
    have hsz := hS.2.2.2.1
    have hI1 := hS.2.1
    have r0 : rdW (m.arr64 IW) so = q := hq
    have rq1 : rdW (m.arr64 IW) q = ho := rdW_iw_of h0 rfl
    have rq2 : rdW (m.arr64 IW) (q + 1) = hl :=
      rdW_iw_of h1 (word_add_one (by omega))
    have rq3 : rdW (m.arr64 IW) (q + 2) = e :=
      rdW_iw_of h2 (word_add_two (by omega))
    rw [r0, rq1, rq2, rq3] at hw
    replace hw := ntBW_some hw; obtain ⟨r1, m1, h1', hw⟩ := hw
    obtain ⟨x1, a1, hrun1, hC1, c1, hg1, hd1, -⟩ :=
      cgC hD.toDmProg5 hcl hkp hs0 hsA h1' hC hc hann he hpwlt hdh hbd hn hv hsd1 hsd2 hpx hCr
    have hrun1' : (divModCertGuard fe (decI c) (decE annVal) hy (decE e)
        (decI (rdW (m.arr64 IW) po))).run a = .ok (x1, a1) := hrun1
    have hlpos : 0 < pl.toNat :=
      Nat.pos_of_ne_zero (fun e' => hpl0 (UInt64.toNat_inj.mp (by simpa using e')))
    have hpo1 : (po + 1).toNat = po.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; omega
    have hpl1 : (pl - 1).toNat = pl.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
    by_cases z1 : r1.headD 0 = 0
    · rw [if_pos z1] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      have hx1 := decW0B_false hd1 z1
      refine ⟨false, a1, ?_, hC1, c1, hg1, decW0B_of_false _⟩
      simp only [divModCertsGuardGo, StateT.run_bind, hrun1', exc_ok_bind', hx1,
        Bool.false_eq_true, if_false]
      rfl
    rw [if_neg z1] at hw
    have hx1 := decW0B_true hd1 z1
    replace hw := ntBW_some hw; obtain ⟨r2, m2, h2, hw⟩ := hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hdr1 : decHL m1 (po + 1).toNat (pl - 1).toNat = some pfs := by
      rw [decHL_grow hg1 (by rw [hpo1, hpl1]; omega)]; exact hdrest
    obtain ⟨x2, a2, hrun2, hC2, c2, hg2, hd2⟩ := ih xrest pfs pxs (so + 1) (sl - 1) (po + 1) (pl - 1)
      k m1 a1 r2 m2 hC1 (hkp.call (im_mem _ rfl) h1' hCr) (hrest.grow hg1) hdr1 (by rw [hpo1, hpl1]; have := hg1.1; omega)
      (ConRon.Bridge.denoteN_ext hn c1.ext) (ConRon.Bridge.denote_ext hv c1.ext)
      (ConRon.Bridge.StmtsDenote.mono c1.ext _ _ hsd3)
      (ConRon.Bridge.denoteEList_ext c1.ext _ _ hpxs) h2
    refine ⟨x2, a2, ?_, hC2, c1.trans c2, hg1.trans hg2, hd2⟩
    simp only [divModCertsGuardGo, StateT.run_bind, hrun1', exc_ok_bind', hx1, if_true]
    exact hrun2

/-- **`div_mod_certs_guard` under `StageC`** (`cgs_ref`'s; con-ron's `divModCertsGuard_run`). -/
theorem cgsC (hD : DmProg6 p) (hcl : LeafClosed p) (hkp : CrKeep p) (hs0 : SubstC0 p dn vis fe)
    (hsA : SubstCAll p dn vis fe) {ps c annVal : Word} {ip : INatOpPinSet}
    {psP : ConLeche.NatOpPinSet} {nm : ConLeche.Name} {v : ConLeche.Expr} {k : Nat} {m m' : Mem}
    {a : AState} {r : List Word}
    (hcall : callW p k "div_mod_certs_guard" [ps, vis, c, annVal] m = some (r, m'))
    (hC : StageC dn vis fe env m a) (hc : H c) (hann : H annVal) (hP : PinSetR m ps ip)
    (hps : PinSetDenote a.store ip psP) (hn : denoteN a.store.ns (decI c) = some nm)
    (hv : denoteE a.store (decE annVal) = some v) (hCr : L.Stubs.CrOK m) :
    ∃ x a', (divModCertsGuard ip fe (decI c) (decE annVal)).run a = .ok (x, a') ∧
      StageC dn vis fe env m' a' ∧ CoreStep V env fe a a' ∧ IWGrow m m' ∧ decW0B m' r x := by
  cases k with
  | zero => rw [callW_zero] at hcall; cases hcall
  | succ k =>
  have hw := callW_model (M := fun mq => cgsW p (k + 1) mq ps vis c annVal)
    (cgs_specW p hD.lCertsGuard (k + 1) · ps vis c annVal) hcall
  rw [cgsW.arm1] at hw
  obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hg1, hd1⟩, hf1, hCr1, hw⟩ :=
    (divModCertStmts_ref hD.toDmProg5.toDmProg2 c).bindLC hcl (leaf_mem _ (by decide)) hkp
      (im_mem _ rfl) ⟨hC.stage, hc⟩ hCr hw
  obtain ⟨hi1, hsd⟩ := ConRon.Bridge.divModCertStmts_run hC.check.state hC.check.pins hn hrun1
  have c1 := ConRon.Bridge.CoreStep.of_istep hC.check hi1
  have hC1 := StageC.of_core hC hS1 hf1 c1
  obtain ⟨r2, m2, x2, a2, hrun2, ⟨hS2, hg2, hd2⟩, hf2, hCr2, hw⟩ :=
    (divModCertProofs_ref hD.toDmProg5.toDmProg2.toDmProg1 ps c ip).bindLC hcl
      (leaf_mem _ (by decide)) hkp (im_mem _ rfl) ⟨hS1, hc, PinSetR.grow hP hg1⟩ hCr1 hw
  have hps1 := (ConRon.Bridge.PinsDenote.mono c1.ext [ip] [psP] ⟨hps, trivial⟩).1
  have hn1 := ConRon.Bridge.denoteN_ext hn c1.ext
  obtain ⟨e2, hpr⟩ := ConRon.Bridge.divModCertProofs_run hC1.check.state hC1.check.pins hps1 hn1 hrun2
  rw [e2] at hrun2 hS2
  have hC2 := StageC.of_core hC1 hS2 hf2 (CoreStep.refl hC1.check)
  cases h3 : callW p k "div_mod_certs_guard_go" [vis, c, annVal, r1.headD 0, r1.tail.headD 0,
      r2.headD 0, r2.tail.headD 0] m2 with
  | none => rw [h3] at hw; simp at hw
  | some q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, bW_some] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  simp only [decStmtL, ntGetD0, ntGetD1] at hd1
  unfold decRL at hd2
  simp only [Nat.zero_add, ntGetD0, ntGetD1] at hd2
  obtain ⟨x3, a3, hrun3, hC3, c3, hg3, hd3⟩ := cggoC hD hcl hkp hs0 hsA c annVal hc hann x1 _ x2 _
    (r1.headD 0) (r1.tail.headD 0) (r2.headD 0) (r2.tail.headD 0) k m2 a1 r3 m3 hC2 hCr2
    (hd1.grow hg2) hd2.1 hd2.2 hn1 (ConRon.Bridge.denote_ext hv c1.ext) hsd hpr h3
  refine ⟨x3, a3, ?_, hC3, c1.trans c3, hg1.trans (hg2.trans hg3), hd3⟩
  simp only [divModCertsGuard, StateT.run_bind, hrun1, exc_ok_bind', hrun2]
  exact hrun3

end cgs

end L.Ind
