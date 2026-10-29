import ConAgua.Arena.KnotEntry
import ConAgua.Verdict.VCtx
import ConAgua.Arena.DeclNatGateSpec
import ConAgua.Arena.DeclNatOpEq
import ConAgua.Arena.DeclReducePin
import ConAgua.Arena.RecGenSpec.CruleProg
import ConAgua.Arena.StageC
import ConRon.Bridge.Checker.DeclVal
import ConAgua.L.ModelGen

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
* `certify_nat_eqs` (one model and one refinement for both outcomes, `cert_ref`): its
  `is_def_eq_core` calls by the knot's `StageT` sim, their failures by `CoreStubsE`; con-ron's
  `CheckOK` after from `certifyNatEqs_bridge` (`certW_okC`, `StageC.of_T`).
-/

set_option experimental.vcgen true

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
    ⟨by rw [hf.size]; exact h.mem.erec, by rw [hf.size]; exact h.mem.spn,
      by rw [hf.size]; exact h.mem.bstk,
      h.mem.memos.frame hf leafA_memo leafC_memo leafA_walk leafC_walk leafA_lp leafC_lp,
      fun k x e => hx.lss.ls.ns k x (h.mem.dnN k x e)⟩,
    by simp only [pinW, hf.arr PINS leafA_pins (by decide)]; exact h.flag⟩

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

/-- **The model of `certify_nat_eqs`, both outcomes**: `is_def_eq_core` (a core stub) through its
run. -/
l_model certifyNatEqs_specE (p : Prog) (hf : p.lookup "certify_nat_eqs" = some certifyNatEqsL)
  fns [hf ↦ certifyNatEqsE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 unified

/-- What `certify_nat_eqs` gives besides the twin's answer `x` (from `m`): `StageT` after, the
growth, the result word decoding `x`. -/
structure CertPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m : Mem)
    (r : Word) (m' : Mem) (x : Bool) (a' : AState) : Prop where
  stage : StageT dn vis fe m' a'
  grow : IWGrow m m'
  res : decW0B m' [r] x

/-- **`certify_nat_eqs` refines `certifyNatEqs` under `StageT`, both outcomes**, by induction on
the pairs: the program's own `is_def_eq_core` by the knot's `StageT` sim, its failure by
`CoreStubsE`. -/
theorem cert_ref (hq : KnotStageProg p) (o l : Word) (ps : List (EIdx × EIdx)) :
    ∀ (k : Nat), k ≤ 2 ^ 62 → ∀ (m : Mem) (a : AState),
      StageT dn vis fe m a → EqL m o.toNat l.toNat ps → o.toNat + l.toNat < 2 ^ 64 →
      RefE (CoreStubsE p) (certifyNatEqsE p k m vis o l) (certifyNatEqs V fe ps) a
        (fun v x a' => CertPost dn vis fe m v.1 v.2 x a') := by
  induction ps generalizing o l with
  | nil =>
    intro k _ m a hS hE _
    have hl0 : l = 0 := UInt64.toNat_inj.mp (by have := hE.2.1; simpa using this)
    cases k with
    | zero => rw [certifyNatEqsE.eq_1]; exact RefE.of_cls0 (by simp)
    | succ k =>
    rw [certifyNatEqsE.arm1 p k m vis o l hl0]
    exact RefE.ret rfl ⟨hS, IWGrow.refl _, by simp [decW0B]⟩
  | cons e0 es ih =>
    intro k hk m a hS hE hb
    cases k with
    | zero => rw [certifyNatEqsE.eq_1]; exact RefE.of_cls0 (by simp)
    | succ k =>
    have hk' : k ≤ 2 ^ 62 := by omega
    obtain ⟨pp, ea, eb, hl0, hpp, hrec, hea, heb, he, hrest⟩ := hE.cons
    rw [certifyNatEqsE.arm2 p k m vis o l (fun h => hl0 (by simp [h]))]
    have hpp' : rdW (m.arr64 IW) o = pp := by
      simp only [iwA] at hpp; simp [rdW, hpp]
    have hea' : rdW (m.arr64 IW) pp = ea := by
      obtain ⟨-, h2, -⟩ := hrec; simp only [iwA] at h2; simp [rdW, h2]
    have heb' : rdW (m.arr64 IW) (pp + 1) = eb := by
      obtain ⟨h1, -, h3⟩ := hrec
      have hpb : (pp + 1).toNat = pp.toNat + 1 := by
        have e1 := hS.stage.iw.iw; have e2 := hS.stage.iw.iwSize
        have e3 : pp.toNat + 1 < 2 ^ 64 := by omega
        rw [UInt64.toNat_add]; simp only [UInt64.toNat_one]; exact Nat.mod_eq_of_lt e3
      simp only [iwA] at h3; simp [rdW, hpb, h3]
    rw [hpp', hea', heb']
    subst he
    simp only [certifyNatEqs]
    rcases h1 : callE p k "is_def_eq_core" [vis, 2, ea, eb] m with e1 | ⟨r1, m1⟩
    · rw [certifyNatEqsE.k_is_def_eq_core.none]
      exact RefE.bind_left fun hcE => hcE.isDefEqCore k hk' hS 2 ea eb hea heb _ h1
    obtain ⟨x1, a1, hrun1, hS1, hg1, hx1⟩ := hq.isDefEqCore_sim k hk' hS 2 ea eb hea heb r1 m1
      (callW_of_callE h1)
    have hrun1' : (isDefEqCore V fe checkFuel 2 (decE ea) (decE eb)).run a = .ok (x1, a1) := hrun1
    refine RefE.bind_right hrun1' ?_
    by_cases hz : r1.headD 0 = 0
    · rw [certifyNatEqsE.k_is_def_eq_core.arm1 p k vis o l r1 m1 hz]
      have hx : x1 = false := by rw [← hx1]; simp only [decBool, hz]; rfl
      rw [hx]
      exact RefE.ite_neg (by decide) (RefE.ret rfl ⟨hS1, hg1, by simp [decW0B]⟩)
    rw [certifyNatEqsE.k_is_def_eq_core.arm2 p k vis o l r1 m1 hz]
    have hx : x1 = true := by rw [← hx1]; simpa [decBool] using hz
    rw [hx]
    refine RefE.ite_pos rfl ?_
    have ho1 : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hl1 : (l - 1).toNat = l.toNat - 1 := by
      have : 0 < l.toNat := Nat.pos_of_ne_zero (fun h0 => hl0 (by simp [h0]))
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
    have hrest1 : EqL m1 (o + 1).toNat (l - 1).toNat es := by
      rw [ho1, hl1]; exact hrest.grow hg1
    have hb1 : (o + 1).toNat + (l - 1).toNat < 2 ^ 64 := by omega
    exact (ih (o + 1) (l - 1) k hk' m1 a1 hS1 hrest1 hb1).mono
      fun _ _ _ hR => ⟨hR.stage, hg1.trans hR.grow, hR.res⟩

/-- **`certify_nat_eqs` under `StageT`** from the call's run (`cert_ref`'s ok half). -/
@[refines ConRon.Arena.certifyNatEqs]
theorem certW_okT (hN : NatEqProg p) (hq : KnotStageProg p) (o l : Word)
    (ps : List (EIdx × EIdx)) :
    ∀ (k : Nat), k ≤ 2 ^ 62 → ∀ (m : Mem) (a : AState) (r : List Word) (m' : Mem),
      StageT dn vis fe m a → EqL m o.toNat l.toNat ps → o.toNat + l.toNat < 2 ^ 64 →
      callW p k "certify_nat_eqs" [vis, o, l] m = some (r, m') →
      ∃ x a', (certifyNatEqs V fe ps).run a = .ok (x, a') ∧ StageT dn vis fe m' a' ∧
        IWGrow m m' ∧ decW0B m' r x := by
  intro k hk m a r m' hS hE hb hc
  obtain ⟨s', rfl, -, x, a', hrun, hR⟩ := RefE.run_okW (s₀ := ⟨m, Locals.init []⟩)
    (certifyNatEqs_specE p hN.lNatCertify k _ vis o l) (cert_ref hq o l ps k hk m a hS hE hb) hc
  exact ⟨x, a', hrun, hR.stage, hR.grow, by simpa [decW0B] using hR.res⟩

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

/-! ## `defn_nat_cert` and `defn_nat_gate`: one model and one refinement for both outcomes -/

/-- **The model of `defn_nat_cert`, both outcomes**: the leaves outside the verdict closure
(`env_find`, `nat_op_equations`, `subst_const0_pairs`) through their `Option` models,
`certify_nat_eqs` through its run. -/
l_model defnNatCert_specE (p : Prog) (hf : p.lookup "defn_nat_cert" = some defnNatCert)
  fns [hf ↦ defnNatCertE]
  specs [callW_spec p n "env_find", callW_spec p n "nat_op_equations",
    callW_spec p n "subst_const0_pairs"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **The model of `defn_nat_gate`, both outcomes**: the leaves through their `Option` models,
`defn_nat_cert` through its model. -/
l_model defnNatGate_specE (p : Prog) (hf : p.lookup "defn_nat_gate" = some defnNatGate)
  (hc : p.lookup "defn_nat_cert" = some defnNatCert)
  fns [hf ↦ defnNatGateE]
  specs [callW_spec p n "nat_op_names", callW_spec p n "sl_contains", callW_spec p n "nat_op_guard",
    callW_spec p n "nat_op_deps", callW_spec p n "nat_op_stored_ok_all", defnNatCert_specE p hc n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

section gate
variable {p : Prog} {dn : NIdx → Option ConLeche.Name}

/-- What `defn_nat_cert` gives besides the twin's run (from `m`, `a`): `StageC` at the
pre-insertion view, the growth, `Ext` of the twin's store. -/
structure DncPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe2 : IFEnv)
    (env : ConLeche.Env) (m m' : Mem) (a a' : AState) : Prop where
  stage : StageC dn vis (fe2.restrictTo vis.toNat) env m' a'
  grow : IWGrow m m'
  ext : Ext a.store a'.store

/-- **`defn_nat_cert` refines `natCertT` under `StageC`, both outcomes** (con-ron's
`checkDecl_bridge_defn`, the stored value's branch): `env_find` reads the pushed index (the twin's
`IFEnvOK.hit` at `env2`), the equations and their substitution are leaves at the pushed view, the
certificate runs at the pre-insertion view (`cert_ref`); its failure is
the twin's `notImplemented`. -/
theorem dnc_ref (hN : NatSubProg' p) (hq : KnotStageProg p) (hcl : LeafClosed p) {vis w n : Word}
    {fe2 : IFEnv} {env env2 : ConLeche.Env} {nm : ConLeche.Name} (k : Nat) (hk : k ≤ 2 ^ 62)
    {m : Mem} {a : AState} (hn : H n)
    (hSw : StageR dn w fe2 m a) (hC : StageC dn vis (fe2.restrictTo vis.toNat) env m a)
    (henv : ConLeche.EnvWF env) (hie : StepOK env2 fe2 a)
    (hnm : denoteN a.store.ns (decI n) = some nm) :
    RefE (CoreStubsE p) (defnNatCertE p k m vis w n) (natCertT fe2 (fe2.restrictTo vis.toNat) (decI n))
      a (fun v _ a' => DncPost dn vis fe2 env m v.2 a a') := by
  cases k with
  | zero => rw [defnNatCertE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ k =>
  have hk' : k ≤ 2 ^ 62 := by omega
  rw [defnNatCertE.arm1]
  have hE := hN.toNatSubProg.toNatEqProg
  have hG := hE.toNatTyProg.toNatGuardProg.toNatLitProg.toNatCvProg.toNatGateProg
  rcases h1 : callW p k "env_find" [n, w] m with _ | ⟨r1, m1⟩
  · rw [liftE_none, defnNatCertE.k_env_find.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨hm1, hfd⟩ := envFind_call hG.toMasterProg n hn hSw.check.env h1
  subst hm1
  cases hf : fe2.find? (decI n) with
  | none =>
    rw [hf] at hfd
    have hz : r1.headD 0 = 0 := hfd
    rw [defnNatCertE.k_env_find.abort1 p _ _ _ _ _ hz]; exact RefE.of_cls0 rfl
  | some ci =>
  rw [hf] at hfd
  obtain ⟨hf1, hci⟩ := hfd
  have hnz : ¬ r1.headD 0 = 0 := by rw [hf1]; decide
  have hsz := hSw.iw.erSize
  by_cases hkk' : ¬ rdW (m1.arr64 EREC) (r1.tail.headD 0) = 1
  · rw [defnNatCertE.k_env_find.abort2 p _ _ _ _ _ hnz hkk']; exact RefE.of_cls0 rfl
  have hkk : rdW (m1.arr64 EREC) (r1.tail.headD 0) = 1 := Classical.not_not.mp hkk'
  rw [defnNatCertE.k_env_find.arm1 p _ _ _ _ _ hnz hkk]
  generalize hq0 : r1.tail.headD 0 = q at hci hkk ⊢
  rcases decCI_defn_cases hci with ⟨cv, v, hint, rfl, hk1, hcv⟩ | ⟨w1, hw1, hne, hnd⟩
  rotate_left
  · have hk' := erecP_get hw1
    exact absurd hkk (by rw [rdW, hk']; exact hne)
  obtain ⟨wv, hk1', hk5, hwl, hwd⟩ := decCI_defn_val hci
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
  simp only [natCertT, hf]
  -- the equations
  rcases h2 : callW p k "nat_op_equations" [0, n] m1 with _ | ⟨r2, m2⟩
  · rw [liftE_none, defnNatCertE.k_nat_op_equations.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, defnNatCertE.k_nat_op_equations.arm1]
  obtain ⟨x2, a2, hrun2, hS2, hg2, hd2⟩ :=
    natOpEquations_ref hN 0 n k m1 a r2 m2 ⟨hSw, by decide, hn⟩ h2
  have hrun2' : (natOpEquations 0 (decI n)).run a = .ok (x2, a2) := hrun2
  obtain ⟨hst2, hx2, hc2, hp2, hdeq⟩ :=
    ConRon.Bridge.natOpEquations_run hC.check.state hC.check.pins hnm hrun2'
  have hC2 := StageC.of_run hC (hS2.restrict vis) (callW_leafFrame hcl (leaf_mem _ (by decide)) h2)
    hst2 hx2 hc2 hp2
  have hE2 := decEqRL_headD hd2
  have e5' : rdW (m2.arr64 EREC) (q + 5) = wv := by
    simp only [rdW, hq5]; rw [hg2.erGet _ hqlt, erecP_get hk5]; rfl
  rw [e5']
  refine RefE.bind_right hrun2' ?_
  -- their substitution
  rcases h3 : callW p k "subst_const0_pairs" [n, wv, r2.headD 0, r2.tail.headD 0] m2 with
    _ | ⟨r3, m3⟩
  · rw [liftE_none, defnNatCertE.k_subst_const0_pairs.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, defnNatCertE.k_subst_const0_pairs.arm1]
  obtain ⟨x3, a3, hrun3, hS3, hg3, hd3⟩ := pairs_ref hN.toNatSubProg n wv hn hwl x2 (r2.headD 0)
    (r2.tail.headD 0) k m2 a2 r3 m3 hS2 hE2 (EqL.lt64 hE2 hS2.iw) h3
  have hvP2 : denoteE a2.store (decE wv) = some vP := by
    rw [hv]; exact ConRon.Bridge.denote_ext hjv hx2
  obtain ⟨hst3, hx3, hc3, hp3, hdps⟩ := ConRon.Bridge.substConst0Pairs_run hst2 hC2.check.pins
    (ConRon.Bridge.denoteN_ext hnm hx2) hvP2 hdeq hrun3
  have hC3 := StageC.of_run hC2 (hS3.restrict vis) (callW_leafFrame hcl (leaf_mem _ (by decide)) h3)
    hst3 hx3 hc3 hp3
  have hE3 := decEqRL_headD hd3
  have hrun3' : (substConst0Pairs (decI n) (decE wv) x2).run a2 = .ok (x3, a3) := hrun3
  rw [← hv]
  refine RefE.bind_right hrun3' ?_
  -- the certificate, at the pre-insertion view
  rcases h4 : callE p k "certify_nat_eqs" [vis, r3.headD 0, r3.tail.headD 0] m3 with e4 | ⟨r4, m4⟩
  · rw [defnNatCertE.k_certify_nat_eqs.none]
    exact RefE.bind_left fun hcE => RefE.run_err (s₀ := ⟨m3, Locals.init []⟩)
      (certifyNatEqs_specE p hE.lNatCertify k _ vis (r3.headD 0) (r3.tail.headD 0)) trivial hcE
      (cert_ref hq _ _ x3 k hk' m3 a3 hC3.stageT hE3 (EqL.lt64 hE3 hS3.iw)) h4
  obtain ⟨x4, a4, hrun4, hC4, hg4, hd4, hx4⟩ := certW_okC hE hq henv hk' hC3 hE3
    (EqL.lt64 hE3 hS3.iw) hdps (ConRon.Bridge.natOpEqs_wscoped hie.envWF hfindP) (callW_of_callE h4)
  refine RefE.bind_right hrun4 ?_
  by_cases e4 : r4.headD 0 = 0
  · rw [defnNatCertE.k_certify_nat_eqs.abort1 p r4 m4 e4]
    have t4 : x4 = false := by rw [← hd4.1, e4]; rfl
    rw [t4]
    exact RefE.ite_neg (by decide) fun _ => ErrClaim.fail _ _ rfl
  rw [defnNatCertE.k_certify_nat_eqs.arm1 p r4 m4 e4]
  have t4 : x4 = true := by rw [← hd4.1]; simpa using e4
  rw [t4]
  exact RefE.ite_pos rfl (RefE.ret rfl ⟨hC4, (hg2.trans hg3).trans hg4, hx2.trans (hx3.trans hx4)⟩)

/-- What `defn_nat_gate` gives besides the twin's run (from `m`, `a`): the stage relation at the
pushed view `w`, `StageC` at the pre-insertion view `vis`, the growth, `Ext` of the twin's
store. -/
structure DngPost (dn : NIdx → Option ConLeche.Name) (vis w : Word) (fe2 : IFEnv)
    (env : ConLeche.Env) (m m' : Mem) (a a' : AState) : Prop where
  stageW : StageR dn w fe2 m' a'
  stage : StageC dn vis (fe2.restrictTo vis.toNat) env m' a'
  grow : IWGrow m m'
  ext : Ext a.store a'.store

/-- **`defn_nat_gate` refines `natGateT` under `StageC`, both outcomes** (con-ron's
`checkDecl_bridge_defn`, the structural-`Nat` gate): from the stage relation at the pushed view
`w` (extended index `fe2`), `StageC` at the pre-insertion view `vis` (con-ron's `CheckOK` at
`env`, the environment before the push), `env`'s well-formedness, the pushed index's `StepOK` (at
`env2`) and the name's denotation; a nonstandard environment is the twin's `notImplemented`, the
certificate by `dnc_ref`. -/
theorem dng_ref (hN : NatSubProg' p) (hq : KnotStageProg p) (hcl : LeafClosed p) {vis w n : Word} {fe2 : IFEnv}
    {env env2 : ConLeche.Env} {nm : ConLeche.Name} (k : Nat) (hk : k ≤ 2 ^ 62) {m : Mem}
    {a : AState} (hn : H n)
    (hSw : StageR dn w fe2 m a) (hC : StageC dn vis (fe2.restrictTo vis.toNat) env m a)
    (henv : ConLeche.EnvWF env) (hie : StepOK env2 fe2 a)
    (hnm : denoteN a.store.ns (decI n) = some nm) :
    RefE (CoreStubsE p) (defnNatGateE p k m vis w n)
      (natGateT (fe2.restrictTo vis.toNat) fe2 (decI n)) a
      (fun v _ a' => DngPost dn vis w fe2 env m v.2 a a') := by
  cases k with
  | zero => rw [defnNatGateE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ k =>
  have hk' : k ≤ 2 ^ 62 := by omega
  rw [defnNatGateE.arm1]
  have hE := hN.toNatSubProg.toNatEqProg
  have hT := hE.toNatTyProg
  have hGd := hT.toNatGuardProg
  have hG := hGd.toNatLitProg.toNatCvProg.toNatGateProg
  have hvb : fe2.visibleBelow = w.toNat := hSw.check.env.vis
  rw [natGateT_eq]
  -- the operation names
  rcases h1 : callW p k "nat_op_names" [] m with _ | ⟨r1, m1⟩
  · rw [liftE_none, defnNatGateE.k_nat_op_names.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, defnNatGateE.k_nat_op_names.arm1]
  obtain ⟨xs, a1, hrun1, hS1, hg1, hd1⟩ := natOpNames_ref hG k m a r1 m1 hSw h1
  obtain ⟨e1, -⟩ := ConRon.Bridge.natOpNames_run hC.check.pins hrun1
  have e1' := e1.symm
  subst e1'
  refine RefE.bind_right hrun1 ?_
  have hC1 := StageC.of_run hC (hS1.restrict vis) (callW_leafFrame hcl (leaf_mem _ (by decide)) h1)
    hC.check.state (Ext.refl _) rfl rfl
  obtain ⟨hdh1, hb1⟩ := decRL0 hd1
  -- membership
  rcases h2 : callW p k "sl_contains" [r1.headD 0, r1.tail.headD 0, n] m1 with _ | ⟨r2, m2⟩
  · rw [liftE_none, defnNatGateE.k_sl_contains.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
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
  · rw [defnNatGateE.k_sl_contains.arm2 p _ _ _ _ _ _ e2, defnNatGateE.j1.arm1]
    have hf : xs.contains (decI n) = false := by
      rw [← hx2]; have := hd2.1; rw [e2] at this; simpa using this.symm
    rw [hf]
    exact RefE.ite_neg (by decide) (RefE.ret rfl ⟨hS2, hC2, hg1.trans hg2, Ext.refl _⟩)
  rw [defnNatGateE.k_sl_contains.arm1 p _ _ _ _ _ _ e2]
  have hx2t : xs.contains (decI n) = true := by
    rw [← hx2, ← hd2.1]; simpa using e2
  rw [hx2t]
  refine RefE.ite_pos rfl ?_
  -- the guard
  rcases h3 : callW p k "nat_op_guard" [w, n] m2 with _ | ⟨r3, m3⟩
  · rw [liftE_none, defnNatGateE.k_nat_op_guard.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, defnNatGateE.k_nat_op_guard.arm1]
  obtain ⟨x3, a3, hrun3, hS3, hg3, hd3⟩ := natOpGuard_ref hGd n k m2 a2 r3 m3 ⟨hS2, hn⟩ h3
  obtain ⟨hst3, hx3, hc3, hp3, -⟩ :=
    ConRon.Bridge.natOpGuard_run hC2.check.state hC2.check.pins hie.ienv hnm hrun3
  have hC3 := StageC.of_run hC2 (hS3.restrict vis) (callW_leafFrame hcl (leaf_mem _ (by decide)) h3)
    hst3 hx3 hc3 hp3
  have hnm3 := ConRon.Bridge.denoteN_ext hnm hx3
  refine RefE.bind_right hrun3 ?_
  -- the dependencies
  rcases h4 : callW p k "nat_op_deps" [n] m3 with _ | ⟨r4, m4⟩
  · rw [liftE_none, defnNatGateE.k_nat_op_deps.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, defnNatGateE.k_nat_op_deps.arm1]
  obtain ⟨ds, a4, hrun4, hS4, hg4, hd4⟩ := natOpDeps_ref hG n k m3 a3 r4 m4 ⟨hS3, hn⟩ h4
  obtain ⟨hst4, hx4, hc4, hp4, hdeps⟩ :=
    ConRon.Bridge.natOpDeps_run hst3 hC3.check.pins hnm3 hrun4
  have hC4 := StageC.of_run hC3 (hS4.restrict vis) (callW_leafFrame hcl (leaf_mem _ (by decide)) h4)
    hst4 hx4 hc4 hp4
  obtain ⟨hdh4, hb4⟩ := decRL0 hd4
  refine RefE.bind_right hrun4 ?_
  -- the stored dependencies
  rcases h5 : callW p k "nat_op_stored_ok_all" [w, r4.headD 0, r4.tail.headD 0] m4 with
    _ | ⟨r5, m5⟩
  · rw [liftE_none, defnNatGateE.k_nat_op_stored_ok_all.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨x5, a5, hrun5, hS5, hg5, hd5⟩ :=
    okAll_ref hT (r4.headD 0) (r4.tail.headD 0) ds k m4 a4 r5 m5 hS4 hdh4 hb4 h5
  obtain ⟨hst5, hx5, hc5, hp5, -⟩ := ConRon.Bridge.natOpStoredOkAll_run hst4 hC4.check.pins
    (hie.mono (hx3.trans hx4)).ienv hdeps hrun5
  have hC5 := StageC.of_run hC4 (hS5.restrict vis) (callW_leafFrame hcl (leaf_mem _ (by decide)) h5)
    hst5 hx5 hc5 hp5
  refine RefE.bind_right hrun5 ?_
  by_cases e35 : r3.headD 0 = 0 ∨ r5.headD 0 = 0
  · rw [defnNatGateE.k_nat_op_stored_ok_all.abort1 p _ _ _ _ _ _ _ e35]
    have hbool : (x3 && x5) = false := by
      rcases e35 with e | e
      · have : x3 = false := by rw [← hd3.1, e]; rfl
        simp [this]
      · have : x5 = false := by rw [← hd5.1, e]; rfl
        simp [this]
    rw [hbool]
    exact RefE.ite_neg (by decide) (RefE.bind_left fun _ => ErrClaim.fail _ _ rfl)
  rw [defnNatGateE.k_nat_op_stored_ok_all.arm1 p _ _ _ _ _ _ _ e35]
  have t3 : x3 = true := by rw [← hd3.1]; simp at e35; simp [e35.1]
  have t5 : x5 = true := by rw [← hd5.1]; simp at e35; simp [e35.2]
  rw [t3, t5]
  refine RefE.ite_pos rfl ?_
  -- the certificate
  have hx35 := hx3.trans (hx4.trans hx5)
  have h6r := dnc_ref hN hq hcl k hk' hn hS5 hC5 henv (hie.mono hx35)
    (ConRon.Bridge.denoteN_ext hnm hx35)
  rcases h6 : defnNatCertE p k m5 vis w n with e6 | ⟨r6, m6⟩ <;> rw [h6] at h6r
  · rw [defnNatGateE.k_defn_nat_cert.none]; exact h6r
  rw [defnNatGateE.k_defn_nat_cert.arm1, defnNatGateE.j1.arm1]
  obtain ⟨_, a6, hrun6, hC6, hg6, hx6⟩ := h6r
  exact RefE.ret hrun6 ⟨stageR_of_restrict hC6.stage hvb, hC6,
    (((((hg1.trans hg2).trans hg3).trans hg4).trans hg5).trans hg6), hx35.trans hx6⟩

/-- **`defn_nat_gate` under `StageC`** from the call's run (`dng_ref`'s ok half). -/
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
  obtain ⟨s', rfl, -, ⟨⟩, a', hrun, hR⟩ := RefE.run_okW (s₀ := ⟨m, Locals.init []⟩)
    (defnNatGate_specE p hg hc k _ vis w n) (dng_ref hN hq hcl k hk hn hSw hC henv hie hnm) hcall
  exact ⟨a', hrun, hR.stageW, hR.stage, hR.grow, hR.ext⟩

end gate

end L.Arena
