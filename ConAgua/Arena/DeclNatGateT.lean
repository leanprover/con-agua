import ConAgua.Arena.DeclNatGateSpec
import ConAgua.Arena.DeclNatOpEq
import ConAgua.Arena.DeclReducePin
import ConAgua.Arena.KnotEntry
import ConAgua.Arena.RecGenSpec.CruleProg
import ConAgua.Arena.StageC
import ConRon.Bridge.Checker.DeclVal
import ConAgua.Census.Attr

/-!
# The structural-`Nat` gate under `StageC` (lane `loopt3`, helper `loopt3-nat`)

`defn_nat_gate` (`DeclNatGateSpec.lean`, `defnNatGate_ref` at `StageR` through `stubCall`) runs
after the definition arm's push: its leaves at the pushed view `w`, its certificate's core calls
at the pre-insertion view `vis`. It runs here from the real program (`realCall p`) under `StageC`
(`TwinStep.lean`), mirroring con-ron's `checkDecl_bridge_defn` (`Bridge/Checker/Arms.lean`) and
`certifyNatEqs_bridge` (`Bridge/Checker/DeclVal.lean`):

* the leaves (`nat_op_names`, `sl_contains`, `nat_op_guard`, `nat_op_deps`,
  `nat_op_stored_ok_all`, `env_find`, `nat_op_equations`, `subst_const0_pairs`) by their `StageR`
  refinements, the leaves' write set (`LeafClosed`), and con-ron's run lemmas (`natOpNames_run`,
  `natOpGuard_run`, `natOpDeps_run`, `natOpStoredOkAll_run`, `natOpEquations_run`,
  `substConst0Pairs_run`: `StateOK` after, `Ext`, caches and pins unchanged; `StageC.of_run`);
* `certify_nat_eqs`'s `is_def_eq_core` calls by the knot's `StageT` sim (`certW_okT`), con-ron's
  `CheckOK` after from `certifyNatEqs_bridge` (`StageC.of_T`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

open L.Ind
open ConRon.Bridge (CheckOK StepOK)

local notation "V" => ConLeche.CheckMode.verified

/-- **`StageC` across a leaf**, the twin's step given by the four facts con-ron's `*_run` lemmas
state (`StateOK` after, `Ext`, caches and pins unchanged). -/
theorem StageC.of_run {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {env : ConLeche.Env} {m m' : Mem} {a a' : AState} (h : StageC dn vis fe env m a)
    (hS : StageR dn vis fe m' a') (hf : MemFrame leafA leafC m m')
    (hok : ConRon.Bridge.StateOK a') (hx : Ext a.store a'.store) (hc : a'.caches = a.caches)
    (hp : a'.pins = a.pins) : StageC dn vis fe env m' a' :=
  ⟨hS, h.check.mono hok hx hc hp,
    ⟨by rw [hf.2.2.1]; exact h.mem.erec, by rw [hf.2.2.1]; exact h.mem.spn,
      by rw [hf.2.2.1]; exact h.mem.bstk,
      h.mem.memos.frame hf leafA_memo leafC_memo leafA_walk leafC_walk leafA_lp leafC_lp,
      fun k x e => hx.lss.ls.ns k x (h.mem.dnN k x e)⟩,
    by simp only [pinW, hf.1 PINS leafA_pins (by decide)]; exact h.flag⟩

/-- The stage relation at the pushed view `w`, back from the pre-insertion view. -/
theorem stageR_of_restrict {dn : NIdx → Option ConLeche.Name} {vis w : Word} {fe2 : IFEnv}
    {m : Mem} {a : AState} (h : StageR dn vis (fe2.restrictTo vis.toNat) m a)
    (hvb : fe2.visibleBelow = w.toNat) : StageR dn w fe2 m a := by
  have := h.restrict w
  rw [IFEnv.restrictTo_restrictTo, ← hvb, IFEnv.restrictTo_self] at this
  exact this

/-! ## `certify_nat_eqs` -/

section cert
variable {p : Prog} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-- **`certify_nat_eqs` under `StageT`** (`certify_ref`'s, the program's own `is_def_eq_core`
through the knot's `StageT` sim). -/
@[refines ConRon.Arena.certifyNatEqs]
theorem certW_okT (hN : NatEqProg p) (hq : KnotStageProg p) (o l : Word)
    (ps : List (EIdx × EIdx)) :
    ∀ (k : Nat), k ≤ 2 ^ 62 → ∀ (m : Mem) (a : AState) (r : List Word) (m' : Mem),
      StageT dn vis fe m a → EqL m o.toNat l.toNat ps → o.toNat + l.toNat < 2 ^ 64 →
      callW p k "certify_nat_eqs" [vis, o, l] m = some (r, m') →
      ∃ x a', (certifyNatEqs V fe ps).run a = .ok (x, a') ∧ StageT dn vis fe m' a' ∧
        IWGrow m m' ∧ decW0B m' r x := by
  induction ps generalizing o l with
  | nil =>
    intro k _ m a r m' hS hE _ hc
    have hl0 : l = 0 := UInt64.toNat_inj.mp (by have := hE.2.1; simpa using this)
    cases k with
    | zero => rw [callW_zero] at hc; cases hc
    | succ k =>
    have hw := callW_model (M := fun mm => certW p (realCall p) k mm vis o l)
      (certify_specW p hN.lNatCertify (realCall p) (realCall_spec p) k · vis o l) hc
    simp only [certW, hl0, ite_true, Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact ⟨true, a, rfl, hS, IWGrow.refl _, by simp [decW0B]⟩
  | cons e es ih =>
    intro k hk m a r m' hS hE hb hc
    cases k with
    | zero => rw [callW_zero] at hc; cases hc
    | succ k =>
    have hk' : k ≤ 2 ^ 62 := by omega
    obtain ⟨pp, ea, eb, hl0, hpp, hrec, hea, heb, he, hrest⟩ := hE.cons
    have hw := callW_model (M := fun mm => certW p (realCall p) k mm vis o l)
      (certify_specW p hN.lNatCertify (realCall p) (realCall_spec p) k · vis o l) hc
    unfold certW at hw
    rw [ite_eq_right (fun h => hl0 (by simp [h]))] at hw
    have hpp' : rdW (m.arr64 IW) o = pp := by
      simp only [iwA] at hpp; simp [rdW, hpp]
    have hea' : rdW (m.arr64 IW) pp = ea := by
      obtain ⟨-, h2, -⟩ := hrec; simp only [iwA] at h2; simp [rdW, h2]
    have heb' : rdW (m.arr64 IW) (pp + 1) = eb := by
      obtain ⟨h1, -, h3⟩ := hrec
      have hpb : (pp + 1).toNat = pp.toNat + 1 := by
        have e1 := hS.stage.2.1; have e2 := hS.stage.2.2.2.1
        have e3 : pp.toNat + 1 < 2 ^ 64 := by omega
        rw [UInt64.toNat_add]; simp only [UInt64.toNat_one]; exact Nat.mod_eq_of_lt e3
      simp only [iwA] at h3; simp [rdW, hpb, h3]
    rw [hpp', hea', heb'] at hw
    cases h1 : callW p k "is_def_eq_core" [vis, 2, ea, eb] m with
    | none => simp only [realCall] at hw; rw [h1] at hw; simp at hw
    | some q1 =>
    obtain ⟨r1, m1⟩ := q1
    simp only [realCall] at hw
    rw [h1, bW_some] at hw
    obtain ⟨x1, a1, hrun1, hS1, hg1, hx1⟩ := hq.isDefEqCore_sim k hk' hS 2 ea eb hea heb r1 m1 h1
    have hrun1' : (isDefEqCore V fe checkFuel 2 (decE ea) (decE eb)).run a = .ok (x1, a1) := hrun1
    by_cases hz : r1.headD 0 = 0
    · rw [ite_eq_left hz] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      have hx : x1 = false := by rw [← hx1]; simp only [decBool, hz]; rfl
      refine ⟨false, a1, ?_, hS1, hg1, by simp [decW0B]⟩
      subst he
      simp only [certifyNatEqs, StateT.run_bind, hrun1', exc_ok_bind', hx, Bool.false_eq_true,
        ite_false]
      rfl
    · rw [ite_eq_right hz] at hw
      have hx : x1 = true := by rw [← hx1]; simpa [decBool] using hz
      replace hw := ntBW_some hw; obtain ⟨r2, m2, h2, hw⟩ := hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      have ho1 : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hl1 : (l - 1).toNat = l.toNat - 1 := by
        have : 0 < l.toNat := Nat.pos_of_ne_zero hl0
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
      have hrest1 : EqL m1 (o + 1).toNat (l - 1).toNat es := by
        rw [ho1, hl1]; exact hrest.grow hg1
      have hb1 : (o + 1).toNat + (l - 1).toNat < 2 ^ 64 := by omega
      obtain ⟨x, a2, hrun2, hS2, hg2, hd2⟩ := ih (o + 1) (l - 1) k hk' m1 a1 r2 m2 hS1 hrest1 hb1 h2
      refine ⟨x, a2, ?_, hS2, hg1.trans hg2, by simpa [decW0B] using hd2⟩
      subst he
      simp only [certifyNatEqs, StateT.run_bind, hrun1', exc_ok_bind', hx, ite_true]
      exact hrun2

/-- **`certify_nat_eqs` under `StageC`**: `certW_okT`, and con-ron's `CheckOK` after from
`certifyNatEqs_bridge` (the pairs' denotations, scoped at depth 2). -/
theorem certW_okC (hN : NatEqProg p) (hq : KnotStageProg p) {env : ConLeche.Env}
    (henv : ConLeche.EnvWF env) {o l : Word} {ps : List (EIdx × EIdx)}
    {xs : List (ConLeche.Expr × ConLeche.Expr)} {k : Nat} (hk : k ≤ 2 ^ 62) {m m' : Mem}
    {a : AState} {r : List Word} (hS : StageC dn vis fe env m a) (hE : EqL m o.toNat l.toNat ps)
    (hb : o.toNat + l.toNat < 2 ^ 64) (hden : ConRon.Bridge.EqPairsDenote a.store ps xs)
    (hws : ∀ q ∈ xs, ConLeche.Expr.WScoped 2 q.1 ∧ ConLeche.Expr.WScoped 2 q.2)
    (hc : callW p k "certify_nat_eqs" [vis, o, l] m = some (r, m')) :
    ∃ x a', (certifyNatEqs V fe ps).run a = .ok (x, a') ∧ StageC dn vis fe env m' a' ∧
      IWGrow m m' ∧ decW0B m' r x ∧ Ext a.store a'.store := by
  obtain ⟨x, a', hrun, hT, hg, hd⟩ := certW_okT hN hq o l ps k hk m a r m' hS.stageT hE hb hc
  obtain ⟨hstep, -⟩ := ConRon.Bridge.certifyNatEqs_bridge rfl (ConRon.Bridge.CoreSpec.of_core rfl)
    hS.check henv hden hws hrun
  exact ⟨x, a', hrun, StageC.of_T hT hstep.ok, hg, hd, hstep.ext⟩

end cert

/-! ## `defn_nat_cert` and `defn_nat_gate` -/

section gate
variable {p : Prog} {dn : NIdx → Option ConLeche.Name}

/-- **`defn_nat_cert` under `StageC`** (`defnNatCert_ref`'s; con-ron's `checkDecl_bridge_defn`, the
stored value's branch): `env_find` reads the pushed index (the twin's `IFEnvOK.hit` at `env2`), the
equations and their substitution are leaves at the pushed view, the certificate runs at the
pre-insertion view (`certW_okC`). -/
theorem defnNatCert_okC (hN : NatSubProg' p) (hc : p.lookup "defn_nat_cert" = some defnNatCert)
    (hq : KnotStageProg p) (hcl : LeafClosed p) {vis w n : Word} {fe2 : IFEnv}
    {env env2 : ConLeche.Env} {nm : ConLeche.Name} {k : Nat} (hk : k ≤ 2 ^ 62) {m m' : Mem}
    {a : AState} {r : List Word} (hn : H n)
    (hcall : callW p k "defn_nat_cert" [vis, w, n] m = some (r, m'))
    (hSw : StageR dn w fe2 m a) (hC : StageC dn vis (fe2.restrictTo vis.toNat) env m a)
    (henv : ConLeche.EnvWF env) (hie : StepOK env2 fe2 a)
    (hnm : denoteN a.store.ns (decI n) = some nm) :
    ∃ a', (natCertT fe2 (fe2.restrictTo vis.toNat) (decI n)).run a = .ok ((), a') ∧
      StageC dn vis (fe2.restrictTo vis.toNat) env m' a' ∧ IWGrow m m' ∧
      Ext a.store a'.store := by
  cases k with
  | zero => rw [callW_zero] at hcall; cases hcall
  | succ k =>
  have hk' : k ≤ 2 ^ 62 := by omega
  have hw := callW_model (M := fun mm => defnNatCertW p (k + 1) mm vis w n)
    (defnNatCert_specW p hc (k + 1) · vis w n) hcall
  rw [defnNatCertW.arm1] at hw
  have hE := hN.toNatSubProg.toNatEqProg
  have hG := hE.toNatTyProg.toNatGuardProg.toNatLitProg.toNatCvProg.toNatGateProg
  replace hw := ntBW_some hw; obtain ⟨r1, m1, h1, hw⟩ := hw
  obtain ⟨hm1, hfd⟩ := envFind_call hG.toMasterProg n hn hSw.1.env h1
  subst hm1
  cases hf : fe2.find? (decI n) with
  | none =>
    rw [hf] at hfd
    have hz : r1.headD 0 = 0 := hfd
    rw [ite_eq_left hz] at hw; cases hw
  | some ci =>
  rw [hf] at hfd
  obtain ⟨hf1, hci⟩ := hfd
  have hnz : ¬ r1.headD 0 = 0 := by rw [hf1]; decide
  rw [ite_eq_right hnz] at hw
  have hsz := hSw.2.2.2.2.1
  generalize hq0 : r1.tail.headD 0 = q at hw hci
  rcases decCI_defn_cases hci with ⟨cv, v, hint, rfl, hk1, hcv⟩ | ⟨w1, hw1, hne, hnd⟩
  rotate_left
  · have hk' := erecP_get hw1
    have : rdW (m1.arr64 EREC) q ≠ 1 := by rw [rdW, hk']; exact hne
    rw [ite_eq_left this] at hw; cases hw
  obtain ⟨wv, hk1, hk5, hwl, hwd⟩ := decCI_defn_val hci
  have e1 : rdW (m1.arr64 EREC) q = 1 := by rw [rdW, erecP_get hk1]; rfl
  rw [ite_eq_right (by rw [e1]; simp)] at hw
  have hq5 : (q + 5).toNat = q.toNat + 5 := by
    have : q.toNat + 5 < (m1.arr64 EREC).size := (Array.getElem?_eq_some_iff.mp (erecP_get hk5)).1
    rw [UInt64.toNat_add]; simp; omega
  have hqlt : q.toNat + 5 < erTop m1 := erecP_lt (erecP_get_rev hk5)
  -- the twin's stored value (`IFEnvOK.hit` at the pushed index)
  obtain ⟨nm', c', hnm', hci', hfindP⟩ := hie.ienv.hit (decI n) _ hf
  have hnmEq : nm' = nm := by rw [hnm] at hnm'; exact (Option.some.inj hnm').symm
  subst hnmEq
  simp only [Frontend.denoteCI] at hci'
  cases hcv' : Frontend.denoteCV a.store cv with
  | none => rw [hcv'] at hci'; simp at hci'
  | some cvP =>
  cases hjv : denoteE a.store v with
  | none => rw [hcv', hjv] at hci'; simp at hci'
  | some vP =>
  rw [hcv', hjv] at hci'
  simp only [Option.some.injEq] at hci'
  subst hci'
  have hv : decE wv = v := hwd
  -- the equations
  replace hw := ntBW_some hw; obtain ⟨r2, m2, h2, hw⟩ := hw
  obtain ⟨x2, a2, hrun2, hS2, hg2, hd2⟩ :=
    natOpEquations_ref hN 0 n k m1 a r2 m2 ⟨hSw, by decide, hn⟩ h2
  have hrun2' : (natOpEquations 0 (decI n)).run a = .ok (x2, a2) := hrun2
  obtain ⟨hst2, hx2, hc2, hp2, hdeq⟩ :=
    ConRon.Bridge.natOpEquations_run hC.check.state hC.check.pins hnm hrun2'
  have hC2 := StageC.of_run hC (hS2.restrict vis) (callW_leafFrame hcl (leaf_mem _ (by decide)) h2)
    hst2 hx2 hc2 hp2
  have hE2 := decEqRL_headD hd2
  have e5' : rdW (m2.arr64 EREC) (q + 5) = wv := by
    simp only [rdW, hq5]; rw [hg2.2.2.2 _ hqlt, erecP_get hk5]; rfl
  rw [e5'] at hw
  -- their substitution
  replace hw := ntBW_some hw; obtain ⟨r3, m3, h3, hw⟩ := hw
  obtain ⟨x3, a3, hrun3, hS3, hg3, hd3⟩ := pairs_ref hN.toNatSubProg n wv hn hwl x2 (r2.headD 0)
    (r2.tail.headD 0) k m2 a2 r3 m3 hS2 hE2 (EqL.lt64 hE2 hS2.2) h3
  have hvP2 : denoteE a2.store (decE wv) = some vP := by
    rw [hv]; exact ConRon.Bridge.denote_ext hjv hx2
  obtain ⟨hst3, hx3, hc3, hp3, hdps⟩ := ConRon.Bridge.substConst0Pairs_run hst2 hC2.check.pins
    (ConRon.Bridge.denoteN_ext hnm hx2) hvP2 hdeq hrun3
  have hC3 := StageC.of_run hC2 (hS3.restrict vis) (callW_leafFrame hcl (leaf_mem _ (by decide)) h3)
    hst3 hx3 hc3 hp3
  have hE3 := decEqRL_headD hd3
  -- the certificate, at the pre-insertion view
  replace hw := ntBW_some hw; obtain ⟨r4, m4, h4, hw⟩ := hw
  obtain ⟨x4, a4, hrun4, hC4, hg4, hd4, hx4⟩ := certW_okC hE hq henv hk' hC3 hE3
    (EqL.lt64 hE3 hS3.2) hdps (ConRon.Bridge.natOpEqs_wscoped hie.envWF hfindP) h4
  by_cases e4 : r4.headD 0 = 0
  · rw [ite_eq_left e4] at hw; cases hw
  rw [ite_eq_right e4] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨-, rfl⟩ := hw
  have t4 : x4 = true := by rw [← hd4.1]; simpa using e4
  refine ⟨a4, ?_, hC4, (hg2.trans hg3).trans hg4, hx2.trans (hx3.trans hx4)⟩
  have hrun3' : (substConst0Pairs (decI n) (decE wv) x2).run a2 = .ok (x3, a3) := hrun3
  simp only [natCertT, hf, StateT.run_bind, hrun2', exc_ok_bind']
  rw [← hv, hrun3']
  simp only [exc_ok_bind', hrun4, t4, ite_true]
  rfl

/-- **`defn_nat_gate` under `StageC`** (`defnNatGate_ref`'s; con-ron's `checkDecl_bridge_defn`, the
structural-`Nat` gate): from the stage relation at the pushed view `w` (extended index `fe2`),
`StageC` at the pre-insertion view `vis` (con-ron's `CheckOK` at `env`, the environment before the
push), `env`'s well-formedness, the pushed index's `StepOK` (at `env2`) and the name's
denotation; the gate's run, the stage relation at `w`, `StageC` at `vis`, `Ext` of the twin's
store. -/
theorem defnNatGate_okC (hN : NatSubProg' p) (hg : p.lookup "defn_nat_gate" = some defnNatGate)
    (hc : p.lookup "defn_nat_cert" = some defnNatCert) (hq : KnotStageProg p) (hcl : LeafClosed p)
    {vis w n : Word} {fe2 : IFEnv} {env env2 : ConLeche.Env} {nm : ConLeche.Name} {k : Nat}
    (hk : k ≤ 2 ^ 62) {m m' : Mem} {a : AState} {r : List Word} (hn : H n)
    (hcall : callW p k "defn_nat_gate" [vis, w, n] m = some (r, m'))
    (hSw : StageR dn w fe2 m a) (hC : StageC dn vis (fe2.restrictTo vis.toNat) env m a)
    (henv : ConLeche.EnvWF env) (hie : StepOK env2 fe2 a)
    (hnm : denoteN a.store.ns (decI n) = some nm) :
    ∃ a', (natGateT (fe2.restrictTo vis.toNat) fe2 (decI n)).run a = .ok ((), a') ∧
      StageR dn w fe2 m' a' ∧ StageC dn vis (fe2.restrictTo vis.toNat) env m' a' ∧
      IWGrow m m' ∧ Ext a.store a'.store := by
  cases k with
  | zero => rw [callW_zero] at hcall; cases hcall
  | succ k =>
  have hk' : k ≤ 2 ^ 62 := by omega
  have hw := callW_model (M := fun mm => defnNatGateW p (k + 1) mm vis w n)
    (defnNatGate_specW p hg (k + 1) · vis w n) hcall
  rw [defnNatGateW.arm1] at hw
  have hE := hN.toNatSubProg.toNatEqProg
  have hT := hE.toNatTyProg
  have hGd := hT.toNatGuardProg
  have hG := hGd.toNatLitProg.toNatCvProg.toNatGateProg
  have hvb : fe2.visibleBelow = w.toNat := hSw.1.env.vis
  rw [natGateT_eq]
  -- the operation names
  replace hw := ntBW_some hw; obtain ⟨r1, m1, h1, hw⟩ := hw
  obtain ⟨xs, a1, hrun1, hS1, hg1, hd1⟩ := natOpNames_ref hG k m a r1 m1 hSw h1
  obtain ⟨e1, -⟩ := ConRon.Bridge.natOpNames_run hC.check.pins hrun1
  have e1' := e1.symm
  subst e1'
  have hC1 := StageC.of_run hC (hS1.restrict vis) (callW_leafFrame hcl (leaf_mem _ (by decide)) h1)
    hC.check.state (Ext.refl _) rfl rfl
  obtain ⟨hdh1, hb1⟩ := decRL0 hd1
  -- membership
  replace hw := ntBW_some hw; obtain ⟨r2, m2, h2, hw⟩ := hw
  obtain ⟨x2, a2, hrun2, hS2, hg2, hd2⟩ := slContains_ref hG.lSlContains (r1.headD 0)
    (r1.tail.headD 0) n xs hn k m1 a r2 m2 ⟨hS1, hdh1⟩ h2
  have ha2 : a2 = a := by
    simp only [pure, StateT.pure, StateT.run, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun2
    exact hrun2.2.symm
  subst ha2
  have hx2 : x2 = xs.contains (decI n) := by
    simp only [pure, StateT.pure, StateT.run, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun2
    exact hrun2.1.symm
  have hC2 := StageC.of_run hC1 (hS2.restrict vis) (callW_leafFrame hcl (leaf_mem _ (by decide)) h2)
    hC.check.state (Ext.refl _) rfl rfl
  by_cases e2 : r2.headD 0 = 0
  · rw [ite_eq_right (show ¬ (r2.headD 0 ≠ 0) from fun h => h e2), defnNatGateW.j1] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hf : xs.contains (decI n) = false := by
      rw [← hx2]; have := hd2.1; rw [e2] at this; simpa using this.symm
    refine ⟨a2, ?_, hS2, hC2, hg1.trans hg2, Ext.refl _⟩
    simp only [StateT.run_bind, hrun1, exc_ok_bind', hf]
    rfl
  rw [ite_eq_left (show r2.headD 0 ≠ 0 from e2)] at hw
  have hx2t : xs.contains (decI n) = true := by
    rw [← hx2, ← hd2.1]; simpa using e2
  -- the guard
  replace hw := ntBW_some hw; obtain ⟨r3, m3, h3, hw⟩ := hw
  obtain ⟨x3, a3, hrun3, hS3, hg3, hd3⟩ := natOpGuard_ref hGd n k m2 a2 r3 m3 ⟨hS2, hn⟩ h3
  obtain ⟨hst3, hx3, hc3, hp3, -⟩ :=
    ConRon.Bridge.natOpGuard_run hC2.check.state hC2.check.pins hie.ienv hnm hrun3
  have hC3 := StageC.of_run hC2 (hS3.restrict vis) (callW_leafFrame hcl (leaf_mem _ (by decide)) h3)
    hst3 hx3 hc3 hp3
  have hnm3 := ConRon.Bridge.denoteN_ext hnm hx3
  -- the dependencies
  replace hw := ntBW_some hw; obtain ⟨r4, m4, h4, hw⟩ := hw
  obtain ⟨ds, a4, hrun4, hS4, hg4, hd4⟩ := natOpDeps_ref hG n k m3 a3 r4 m4 ⟨hS3, hn⟩ h4
  obtain ⟨hst4, hx4, hc4, hp4, hdeps⟩ :=
    ConRon.Bridge.natOpDeps_run hst3 hC3.check.pins hnm3 hrun4
  have hC4 := StageC.of_run hC3 (hS4.restrict vis) (callW_leafFrame hcl (leaf_mem _ (by decide)) h4)
    hst4 hx4 hc4 hp4
  obtain ⟨hdh4, hb4⟩ := decRL0 hd4
  -- the stored dependencies
  replace hw := ntBW_some hw; obtain ⟨r5, m5, h5, hw⟩ := hw
  obtain ⟨x5, a5, hrun5, hS5, hg5, hd5⟩ :=
    okAll_ref hT (r4.headD 0) (r4.tail.headD 0) ds k m4 a4 r5 m5 hS4 hdh4 hb4 h5
  obtain ⟨hst5, hx5, hc5, hp5, -⟩ := ConRon.Bridge.natOpStoredOkAll_run hst4 hC4.check.pins
    (hie.mono (hx3.trans hx4)).ienv hdeps hrun5
  have hC5 := StageC.of_run hC4 (hS5.restrict vis) (callW_leafFrame hcl (leaf_mem _ (by decide)) h5)
    hst5 hx5 hc5 hp5
  by_cases e35 : r3.headD 0 = 0 ∨ r5.headD 0 = 0
  · rw [ite_eq_left e35] at hw; cases hw
  rw [ite_eq_right e35] at hw
  have t3 : x3 = true := by rw [← hd3.1]; simp at e35; simp [e35.1]
  have t5 : x5 = true := by rw [← hd5.1]; simp at e35; simp [e35.2]
  -- the certificate
  replace hw := ntBW_some hw; obtain ⟨r6, m6, h6, hw⟩ := hw
  simp only [defnNatGateW.j1, Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨-, rfl⟩ := hw
  have hx35 := hx3.trans (hx4.trans hx5)
  obtain ⟨a6, hrun6, hC6, hg6, hx6⟩ := defnNatCert_okC hN hc hq hcl hk' hn h6 hS5 hC5 henv
    (hie.mono hx35) (ConRon.Bridge.denoteN_ext hnm hx35)
  refine ⟨a6, ?_, stageR_of_restrict hC6.stage hvb, hC6,
    (((((hg1.trans hg2).trans hg3).trans hg4).trans hg5).trans hg6), hx35.trans hx6⟩
  simp only [StateT.run_bind, hrun1, exc_ok_bind', hx2t, ite_true, hrun3, hrun4, hrun5, t3, t5,
    Bool.and_self, hrun6]

end gate

end L.Arena
