import ConAgua.Arena.DeclDivGateT2

/-!
# The `Nat.div`-family pin gate under `StageC` (lane `loopt3`, helper `loopt3-div`)

`defn_div_gate` (`DeclDivMod10.lean`, `divGateSpecD` at `StageR` through `stubCall`) runs after the
definition arm's push, at the pre-insertion view `vis` for its core calls and at the pushed view `w`
for the environment guard. It runs here from the real program (`realCall p`) under `StageC`
(`TwinStep.lean`), mirroring con-ron's `checkDivModPin_bridge` (`Bridge/Checker/DivMod.lean`), as
`crpW_okT` (`DeclCrpT.lean`) does for the reduce-pin gate:

* the leaves (`nat_div_mod_names`, `sl_contains`, `rom_pin_sets`, `div_mod_env_guard`,
  `div_mod_decl_pin`, `div_mod_cert_stmts`, `div_mod_cert_proofs`, the substitution walks,
  `consts_resolve_all`, `div_mod_cert_applied`) by `StageC.of_leaf`: their `StageR` refinements, the
  leaves' write set (`LeafClosed`), con-ron's `IStepS`;
* the walks the stubs stand for (`loose_bvars_bounded_fast`, `has_fvar_fast`,
  `all_level_params_defined`, `consts_resolve_ffast`) by their `StageT` contracts (`IndStubsT.lean`)
  and `CheckOK` after from con-ron's `RunsC` lemmas;
* the core calls (`infer_type_core`, `is_def_eq_core`) by the knot's `StageT` sims, `CheckOK` after
  from con-ron's `KnotSpec` (`StageC.of_T`).

Parts 1 and 2 (`DeclDivGateT1.lean`, `DeclDivGateT2.lean`) carry the guards and the attempt; here
the gate itself (`check_div_mod_pin`, `cpC`; `defn_div_gate`, `divGateSpecC`). The definition arm
(helper `loopt3-nat`'s `cdfW_okT`) consumes `DivGateSpecC`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace L.Ind

open L.Arena
open L.Rom (PinSetsR PinSetR)
open ConRon.Bridge (CheckOK StepOK PinsDenote CoreStep)

local notation "V" => ConLeche.CheckMode.verified

/-- **`check_div_mod_pin` under `StageC`** (`cp_ref`'s at the real program; con-ron's
`checkDivModPin_bridge`): the environment guard at the extended view `vis2` (`StepOK`), the stored
value's lookup, the variant loop at the pre-insertion view `vis` (`loopC`). -/
theorem cpC {p : Prog} (hD : DmProg9 p) (hq : KnotStageProg p) (hcl : LeafClosed p)
    {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn) {vis vis2 : Word} {fe2 : IFEnv}
    {env env2 : ConLeche.Env}
    (hs0 : SubstC0 p dn vis (fe2.restrictTo vis.toNat))
    (hsA : SubstCAll p dn vis (fe2.restrictTo vis.toNat)) (henv : ConLeche.EnvWF env)
    {po pl c : Word} {ips : List INatOpPinSet} {psPs : List ConLeche.NatOpPinSet}
    {nm : ConLeche.Name} {k : Nat} (hk : k ≤ 2 ^ 62) {m m' : Mem} {a : AState} {r : List Word}
    (hcall : callW p k "check_div_mod_pin" [po, pl, vis, vis2, c] m = some (r, m'))
    (hS : StageR dn vis2 fe2 m a) (hC : StageC dn vis (fe2.restrictTo vis.toNat) env m a)
    (hok2 : StepOK env2 fe2 a) (hc : H c) (hI : PinsIW m po.toNat pl.toNat ips)
    (hpd : PinsDenote a.store ips psPs) (hn : denoteN a.store.ns (decI c) = some nm) :
    ∃ a', (checkDivModPin V ips (fe2.restrictTo vis.toNat) fe2 (decI c)).run a = .ok ((), a') ∧
      StageR dn vis2 fe2 m' a' ∧ StageC dn vis (fe2.restrictTo vis.toNat) env m' a' ∧
      CoreStep V env (fe2.restrictTo vis.toNat) a a' ∧ IWGrow m m' := by
  cases k with
  | zero => rw [callW_zero] at hcall; cases hcall
  | succ k =>
  have hk' : k ≤ 2 ^ 62 := by omega
  have hw := callW_model (M := fun mq => dmCpW p k mq po pl vis vis2 c)
    (cp_specW p hD.lCheckDivModPin k · po pl vis vis2 c) hcall
  unfold dmCpW at hw
  have hD8 := hD.toDmProg8
  have hD7 := hD8.toDmProg7
  -- the environment guard, at the extended view
  obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hg1, hd1⟩, hf1, hw⟩ :=
    (eg_ref hD7 hdn c).bindL hcl (leaf_mem _ (by decide)) ⟨hS, hc⟩ hw
  obtain ⟨hst1, hx1, hc1, hp1, hgv⟩ :=
    ConRon.Bridge.divModEnvGuard_run hC.check.state hC.check.pins hok2.ienv hn hrun1
  have c1 : CoreStep V env (fe2.restrictTo vis.toNat) a a1 :=
    ⟨hC.check.mono hst1 hx1 hc1 hp1, hx1, hp1⟩
  have hC1 := StageC.of_core hC (hS1.restrict vis) hf1 c1
  by_cases z1 : r1.headD 0 = 0
  · rw [if_pos z1] at hw; cases hw
  rw [if_neg z1] at hw
  have hxt := decW0B_true hd1 z1
  have hrun1' : (divModEnvGuard fe2 (decI c)).run a = .ok (true, a1) := by
    rw [← hxt]; exact hrun1
  -- the stored value
  cases h2 : callW p k "env_find" [c, vis2] m1 with
  | none => rw [h2] at hw; simp at hw
  | some q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, bW_some] at hw
  obtain ⟨hm2, hfd⟩ := envFind_call hD7.toDmProg6.toDmProg5.toMasterProg c hc hS1.1.env h2
  subst hm2
  cases hf : fe2.find? (decI c) with
  | none =>
    rw [hf] at hfd
    rw [if_pos (show r2.headD 0 = 0 from hfd)] at hw; cases hw
  | some ci =>
  rw [hf] at hfd
  obtain ⟨hr2, hci⟩ := hfd
  rw [if_neg (by rw [hr2]; decide)] at hw
  have hsz := hS1.2.2.2.2.1
  obtain ⟨cv, v, hint, rfl, hk1, hcv⟩ : ∃ cv v hint, ci = .defnInfo cv v hint ∧
      (erecP m2)[(r2.tail.headD 0).toNat]? = some 1 ∧
      decCV (erecP m2) ((r2.tail.headD 0).toNat + 1) = some cv := by
    rcases decCI_defn_cases hci with h | ⟨w, hw', hne, hnd⟩
    · exact h
    · exfalso
      have := rdW_erec_of hsz hw'
      rw [if_pos (by rw [this]; exact hne)] at hw; cases hw
  obtain ⟨-, wv, hwv, hwlt, hvw⟩ := decCI_defn_value hci
  have hk1' : rdW (m2.arr64 EREC) (r2.tail.headD 0) = 1 := rdW_erec_of hsz hk1
  rw [if_neg (by rw [hk1']; simp)] at hw
  have hq5 : (r2.tail.headD 0 + 5).toNat = (r2.tail.headD 0).toNat + 5 := by
    have h1 : (r2.tail.headD 0).toNat + 5 < (erecP m2).size := by
      have := (Array.getElem?_eq_some_iff.mp hwv).1; omega
    have h2 : (erecP m2).size ≤ erTop m2 := erecP_size_le' m2
    have h3 : erTop m2 < 2 ^ 64 := (rdW (m2.arr64 CTL) 129).toNat_lt
    have h5 : (5 : Word).toNat = 5 := rfl
    rw [UInt64.toNat_add, h5]; exact Nat.mod_eq_of_lt (by omega)
  have hval : rdW (m2.arr64 EREC) (r2.tail.headD 0 + 5) = wv := by
    have : (erecP m2)[(r2.tail.headD 0 + 5).toNat]? = some wv := by rw [hq5]; exact hwv
    exact rdW_erec_of hsz this
  rw [hval] at hw
  -- the twin's stored value: its denotation and its scope (con-ron's `checkDivModPin_bridge`)
  obtain ⟨nm0, cc, hn0, hcid, hfindP⟩ := hok2.ienv.hit (decI c) _ hf
  rw [hn] at hn0
  obtain rfl := Option.some.inj hn0
  simp only [Frontend.denoteCI] at hcid
  cases hcvd : Frontend.denoteCV a.store cv with
  | none => rw [hcvd] at hcid; simp at hcid
  | some cv' =>
  cases hvv : denoteE a.store v with
  | none => rw [hcvd, hvv] at hcid; simp at hcid
  | some v' =>
  rw [hcvd, hvv] at hcid
  simp only [Option.some.injEq] at hcid
  subst hcid
  have hwc := hok2.envWF _ (List.mem_of_find?_eq_some hfindP)
  obtain ⟨hfv, -, -, -⟩ := hwc.2.2.2.2.1 cv' v' hint rfl
  have hwsv : ConLeche.Expr.WScoped 0 v' := ConLeche.Expr.WScoped.of_not_hasFvar hfv
  -- the variant loop, at the pre-insertion view
  cases h3 : callW p k "check_div_mod_pin_loop" [vis, c, wv, po, pl] m2 with
  | none => rw [h3] at hw; simp at hw
  | some q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, bW_some] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  have hv1 : denoteE a1.store (decE wv) = some v' := by
    have h := ConRon.Bridge.denote_ext hvv hx1
    rw [hvw] at h; exact h
  obtain ⟨x3, a3, hrun3, hC3, c3, hg3⟩ := loopC hD hq hcl hs0 hsA henv c wv hc hwlt hwsv ips psPs
    po pl [] k hk' m2 a1 r3 m3 hC1 (hI.grow hg1) (ConRon.Bridge.PinsDenote.mono hx1 _ _ hpd)
    (ConRon.Bridge.denoteN_ext hn hx1) hv1 h3
  have hS3' := StageR.restrict hC3.stage vis2
  rw [IFEnv.restrictTo_restrictTo, ← hS.1.env.vis, IFEnv.restrictTo_self] at hS3'
  have hx3 : x3 = () := rfl
  subst hx3
  refine ⟨a3, ?_, hS3', hC3, c1.trans c3, hg1.trans hg3⟩
  simp only [checkDivModPin, StateT.run_bind, hrun1', exc_ok_bind', if_true, hf]
  rw [hvw]
  exact hrun3

/-- **`defn_div_gate(vis, w, n)` under `StageC`**: from the stage relation at the pushed view `w`
(extended index `fe2`), `StageC` at the pre-insertion view `vis` (con-ron's `CheckOK` at the
environment `env` before the push), `env`'s well-formedness, the pushed index's `StepOK` (at
`env2`), the variant records in memory (`PinSetsR`) and in the twin's store (`PinsDenote`, from
`TwinFold.pinsD` and `Ext` since), the name's denotation; the gate's run, the stage relation at `w`,
`StageC` at `vis`, `Ext` of the twin's store, and the frame. -/
def DivGateSpecC (p : Prog) (pins : List INatOpPinSet) : Prop :=
  ∀ (dn : NIdx → Option ConLeche.Name), DnInj dn → ∀ (vis w : Word) (fe2 : IFEnv)
    (env env2 : ConLeche.Env) (n : Word) (nm : ConLeche.Name) (k : Nat), k ≤ 2 ^ 62 →
    ∀ (m m' : Mem) (a : AState) (r : List Word), n.toNat < 2 ^ 32 →
    callW p k "defn_div_gate" [vis, w, n] m = some (r, m') →
    StageR dn w fe2 m a → StageC dn vis (fe2.restrictTo vis.toNat) env m a →
    ConLeche.EnvWF env → StepOK env2 fe2 a → PinSetsR m pins →
    (∃ pinsP, PinsDenote a.store pins pinsP) →
    denoteN a.store.ns (decI n) = some nm →
    ∃ a', (divGateT pins (fe2.restrictTo vis.toNat) fe2 (decI n)).run a = .ok ((), a') ∧
      StageR dn w fe2 m' a' ∧ StageC dn vis (fe2.restrictTo vis.toNat) env m' a' ∧
      Ext a.store a'.store ∧ IWGrow m m' ∧ PinSetsR m' pins ∧ MemFrame stepA stepC m m'

/-- **The pin gate under `StageC`**, for a program with the gate's text (`DmProg10`), the knot
(`KnotStageProg`), the leaves' write set (`LeafClosed`), the gate's write set (`StepIn`) and the
substitution walks' refinements (`substC0_of`, `substCAll_of`). -/
theorem divGateSpecC {p : Prog} (hD : DmProg10 p) (hq : KnotStageProg p) (hcl : LeafClosed p)
    (hCl : StepIn p dgFns) (hs0 : ∀ dn vis fe, SubstC0 p dn vis fe)
    (hsA : ∀ dn vis fe, SubstCAll p dn vis fe) (pins : List INatOpPinSet) :
    DivGateSpecC p pins := by
  sorry

end L.Ind
