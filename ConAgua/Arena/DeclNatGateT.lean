module

public import ConAgua.Arena.KnotEntry
public import ConAgua.Verdict.VCtx
public import ConAgua.Arena.DeclNatGateSpec
public import ConAgua.Arena.DeclNatOpEq
import ConAgua.Arena.DeclReducePin
import ConAgua.Arena.RecGenSpec.CruleProg
import ConAgua.Arena.StageC
public import ConRon.Bridge.Checker.DeclVal
import ConAgua.L.ModelGen
import ConAgua.Arena.DeclNatGate
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.LeafFns
public import ConAgua.Arena.TwinStep
import all ConAgua.Arena.DeclArms
import all ConAgua.Arena.DeclArmsNat

@[expose] public section

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
    (hS : StageR vis fe m' a') (hf : MemFrame leafA leafC m m')
    (hok : ConRon.Bridge.StateOK a') (hx : Ext a.store a'.store) (hc : a'.caches = a.caches)
    (hp : a'.pins = a.pins) : StageC dn vis fe env m' a' := by
  sorry

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- The stage relation at the pushed view `w`, back from the pre-insertion view. -/
theorem stageR_of_restrict {dn : NIdx → Option ConLeche.Name} {vis w : Word} {fe2 : IFEnv}
    {m : Mem} {a : AState} (h : StageR vis (fe2.restrictTo vis.toNat) m a)
    (hvb : fe2.visibleBelow = w.toNat) : StageR w fe2 m a := by
  sorry

-/

/-! ## `certify_nat_eqs` -/

section cert
variable {p : Prog} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-- **The model of `certify_nat_eqs`, both outcomes**: `is_def_eq_core` (a core stub) through its
run. -/
l_model certifyNatEqs_specE (p : Prog) (hf : p.lookup "certify_nat_eqs" = some certifyNatEqsL)
  fns [hf ↦ certifyNatEqsE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
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
  sorry

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
  sorry

end cert

/-! ## `defn_nat_cert` and `defn_nat_gate`: one model and one refinement for both outcomes -/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **The model of `defn_nat_cert`, both outcomes**: the leaves outside the verdict closure
(`env_find`, `nat_op_equations`, `subst_const0_pairs`) through their `Option` models,
`certify_nat_eqs` through its run. -/
l_model defnNatCert_specE (p : Prog) (hf : p.lookup "defn_nat_cert" = some defnNatCert)
  fns [hf ↦ defnNatCertE]
  specs [callW_spec p n "env_find", callW_spec p n "nat_op_equations",
    callW_spec p n "subst_const0_pairs"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **The model of `defn_nat_gate`, both outcomes**: the leaves through their `Option` models,
`defn_nat_cert` through its model. -/
l_model defnNatGate_specE (p : Prog) (hf : p.lookup "defn_nat_gate" = some defnNatGate)
  (hc : p.lookup "defn_nat_cert" = some defnNatCert)
  fns [hf ↦ defnNatGateE]
  specs [callW_spec p n "nat_op_names", callW_spec p n "sl_contains", callW_spec p n "nat_op_guard",
    callW_spec p n "nat_op_deps", callW_spec p n "nat_op_stored_ok_all", defnNatCert_specE p hc n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]
-/

section gate
variable {p : Prog} {dn : NIdx → Option ConLeche.Name}

/-- What `defn_nat_cert` gives besides the twin's run (from `m`, `a`): `StageC` at the
pre-insertion view, the growth, `Ext` of the twin's store. -/
structure DncPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe2 : IFEnv)
    (env : ConLeche.Env) (m m' : Mem) (a a' : AState) : Prop where
  grow : IWGrow m m'
  ext : Ext a.store a'.store

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`defn_nat_cert` refines `natCertT` under `StageC`, both outcomes** (con-ron's
`checkDecl_bridge_defn`, the stored value's branch): `env_find` reads the pushed index (the twin's
`IFEnvOK.hit` at `env2`), the equations and their substitution are leaves at the pushed view, the
certificate runs at the pre-insertion view (`cert_ref`); its failure is
the twin's `notImplemented`. -/
theorem dnc_ref (hN : NatSubProg' p) (hq : KnotStageProg p) (hcl : LeafClosed p) {vis w n : Word}
    {fe2 : IFEnv} {env env2 : ConLeche.Env} {nm : ConLeche.Name} (k : Nat) (hk : k ≤ 2 ^ 62)
    {m : Mem} {a : AState} (hn : H n)
    (hSw : StageR w fe2 m a) (hC : StageC dn vis (fe2.restrictTo vis.toNat) env m a)
    (henv : ConLeche.EnvWF env) (hie : StepOK env2 fe2 a)
    (hnm : denoteN a.store.ns (decI n) = some nm) :
    RefE (CoreStubsE p) (defnNatCertE p k m vis w n) (natCertT fe2 (fe2.restrictTo vis.toNat) (decI n))
      a (fun v _ a' => DncPost dn vis fe2 env m v.2 a a') := by
  sorry

-/

/-- What `defn_nat_gate` gives besides the twin's run (from `m`, `a`): the stage relation at the
pushed view `w`, `StageC` at the pre-insertion view `vis`, the growth, `Ext` of the twin's
store. -/
structure DngPost (dn : NIdx → Option ConLeche.Name) (vis w : Word) (fe2 : IFEnv)
    (env : ConLeche.Env) (m m' : Mem) (a a' : AState) : Prop where
  stageW : StageR w fe2 m' a'
  grow : IWGrow m m'
  ext : Ext a.store a'.store

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`defn_nat_gate` refines `natGateT` under `StageC`, both outcomes** (con-ron's
`checkDecl_bridge_defn`, the structural-`Nat` gate): from the stage relation at the pushed view
`w` (extended index `fe2`), `StageC` at the pre-insertion view `vis` (con-ron's `CheckOK` at
`env`, the environment before the push), `env`'s well-formedness, the pushed index's `StepOK` (at
`env2`) and the name's denotation; a nonstandard environment is the twin's `notImplemented`, the
certificate by `dnc_ref`. -/
theorem dng_ref (hN : NatSubProg' p) (hq : KnotStageProg p) (hcl : LeafClosed p) {vis w n : Word} {fe2 : IFEnv}
    {env env2 : ConLeche.Env} {nm : ConLeche.Name} (k : Nat) (hk : k ≤ 2 ^ 62) {m : Mem}
    {a : AState} (hn : H n)
    (hSw : StageR w fe2 m a) (hC : StageC dn vis (fe2.restrictTo vis.toNat) env m a)
    (henv : ConLeche.EnvWF env) (hie : StepOK env2 fe2 a)
    (hnm : denoteN a.store.ns (decI n) = some nm) :
    RefE (CoreStubsE p) (defnNatGateE p k m vis w n)
      (natGateT (fe2.restrictTo vis.toNat) fe2 (decI n)) a
      (fun v _ a' => DngPost dn vis w fe2 env m v.2 a a') := by
  sorry

-/

end gate

end L.Arena
