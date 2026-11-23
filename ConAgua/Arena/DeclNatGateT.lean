module

public import ConAgua.Arena.KnotEntry
public import ConAgua.Verdict.VCtx
public import ConAgua.Arena.DeclNatGateSpec
public import ConAgua.Arena.DeclNatOpEq
import ConAgua.Arena.StageC
public import ConRon.Bridge.Checker.DeclVal
public import ConAgua.Arena.DeclNatPushPop
import ConAgua.L.ModelGen
import ConAgua.Arena.DeclNatGate
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.LeafFns
public import ConAgua.Arena.TwinStep
import all ConAgua.Arena.DeclArms
import all ConAgua.Arena.DeclArmsNat
import ConAgua.Arena.IndSumSpec.ConsSumCtors

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
    (hp : a'.pins = a.pins) : StageC dn vis fe env m' a' :=
  ⟨hS, h.check.mono hok hx hc hp,
    ⟨by rw [hf.size]; exact h.mem.erec, by rw [hf.size]; exact h.mem.spn,
      by rw [hf.size]; exact h.mem.bstk,
      h.mem.memos.frame hf leafA_memo leafC_memo leafA_walk leafC_walk leafA_lp leafC_lp leafA_hb leafC_hb,
      fun k x e => hx.lss.ls.ns k x (h.mem.dnN k x e)⟩,
    by simp only [pinW, hf.arr PINS leafA_pins (by decide)]; exact h.flag⟩

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
      simp only [iwA, aread_apply] at hpp; simp [rdW, hpp]
    have hea' : rdW (m.arr64 IW) pp = ea := by
      obtain ⟨-, h2, -⟩ := hrec; simp only [iwA, aread_apply] at h2; simp [rdW, h2]
    have heb' : rdW (m.arr64 IW) (pp + 1) = eb := by
      obtain ⟨h1, -, h3⟩ := hrec
      have hpb : (pp + 1).toNat = pp.toNat + 1 := by
        have e1 := hS.stage.iw.iw; have e2 := hS.stage.iw.iwSize
        have e3 : pp.toNat + 1 < 2 ^ 64 := by omega
        rw [UInt64.toNat_add]; simp only [UInt64.toNat_one]; exact Nat.mod_eq_of_lt e3
      simp only [iwA, aread_apply] at h3; simp [rdW, hpb, h3]
    rw [hpp', hea', heb']
    subst he
    simp only [certifyNatEqs]
    refine RefE.bindCall (fun _ => certifyNatEqsE.k_is_def_eq_core.none ..)
      (fun hcE _ h1 => hcE.isDefEqCore k hk' hS 2 ea eb hea heb _ h1)
      (fun b h1 => hq.isDefEqCore_sim k hk' hS 2 ea eb hea heb b.1 b.2 h1)
      fun r1 m1 x1 a1 _ _ ⟨hS1, hg1, hx1⟩ => ?_
    rw [certifyNatEqsE.k_is_def_eq_core.eq_2]
    refine RefE.retIf (fun hz => hx1 ▸ L.Arena.decBool_false_of hz) (fun hb => by simpa [← hx1, decBool] using hb)
      (fun _ => ⟨hS1, hg1, by simp [decW0B]⟩) fun _ _ => ?_
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
  obtain ⟨hstep, -⟩ := ConRon.Bridge.certifyNatEqs_bridge ConRon.Bridge.CoreSpec.of_core
    hS.check henv hden hws hrun
  exact ⟨x, a', hrun, L.Ind.StageC.of_T hT hstep.ok, hg, hd, hstep.ext⟩

end cert

/-! ## `check_structural_nat_pin`: one model and one refinement for both outcomes -/

/-- **The model of `check_structural_nat_pin_at_fe2`, both outcomes**: the leaves through their
`Option` models. -/
l_model snpFe2_specE (p : Prog)
  (hf : p.lookup "check_structural_nat_pin_at_fe2" = some checkStructuralNatPinAtFe2L)
  fns [hf ↦ snpFe2E]
  specs [callW_spec p n "nat_op_guard", callW_spec p n "nat_op_stored_ok", callW_spec p n "env_find"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **The model of `check_structural_nat_pin`, both outcomes**: the leaves through their `Option`
models, the reads at the pushed view and `certify_nat_eqs` through their models. -/
l_model snp_specE (p : Prog)
  (hf : p.lookup "check_structural_nat_pin" = some checkStructuralNatPinL)
  (h2 : p.lookup "check_structural_nat_pin_at_fe2" = some checkStructuralNatPinAtFe2L)
  (hc : p.lookup "certify_nat_eqs" = some certifyNatEqsL)
  fns [hf ↦ snpE]
  specs [callW_spec p n "env_row_get", callW_spec p n "env_push", snpFe2_specE p h2 n,
    callW_spec p n "env_pop_temp", callW_spec p n "env_set_flags", callW_spec p n "nat_op_equations",
    callW_spec p n "subst_const0_pairs", certifyNatEqs_specE p hc n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

section snp
variable {p : Prog} {dn : NIdx → Option ConLeche.Name}

/-- What the reads at the pushed view give (from `m`): the stage relation there, the growth, the
stored value's word. -/
structure SnpFe2Post (w : Word) (fe2 : IFEnv) (m m' : Mem) (r : Word) (v : EIdx) (a' : AState) :
    Prop where
  stage : StageR w fe2 m' a'
  grow : IWGrow m m'
  hw : H r
  dec : decE r = v
  frame : MemFrame leafA leafC m m'
  own : ownC m' = ownC m

/-- **`check_structural_nat_pin_at_fe2` refines `checkStructuralNatPinAtFe2`, both outcomes**: the
guard, the dependencies and their storage by the leaves' refinements at the pushed view, the
stored definition's value word. -/
theorem snpFe2_ref (hN : NatSubProg' p) (hcl : LeafClosed p) (hF2 : Fe2Closed p) {w n : Word}
    {fe2 : IFEnv} (k : Nat) {m : Mem}
    {a : AState} (hn : H n) (hS : StageR w fe2 m a) :
    RefE True (snpFe2E p k m w n) (checkStructuralNatPinAtFe2 fe2 (decI n)) a
      (fun v x a' => SnpFe2Post w fe2 m v.2 v.1 x a') := by
  cases k with
  | zero => rw [snpFe2E.eq_1]; exact RefE.of_cls0 (by simp)
  | succ k =>
  rw [snpFe2E.arm1]
  have hE := hN.toNatSubProg.toNatEqProg
  have hT := hE.toNatTyProg
  have hGd := hT.toNatGuardProg
  have hG := hGd.toNatLitProg.toNatCvProg.toNatGateProg
  simp only [checkStructuralNatPinAtFe2]
  refine RefE.bindSim (fun _ => rfl) (natOpGuard_ref hGd n k m a · · ⟨hS, hn⟩ ·)
    fun r1 x1 m1 a1 h1 hrun1 ⟨hS1, hg1, hd1⟩ => ?_
  dsimp only [snpFe2E.k_nat_op_guard]
  refine RefE.bindSim (fun _ => rfl) (natOpStoredOk_ref hT n k m1 a1 · · ⟨hS1, hn⟩ ·)
    fun r3 x3 m3 a3 h3 hrun3 ⟨hS3, hg3, hd3⟩ => ?_
  dsimp only [snpFe2E.k_nat_op_stored_ok]
  have hfr : MemFrame leafA leafC m m3 :=
    (callW_leafFrame hcl (leaf_mem _ (by decide)) h1).trans
      (callW_leafFrame hcl (leaf_mem _ (by decide)) h3)
  have hown : ownC m3 = ownC m :=
    (callW_fe2_ownC hF2 (by simp [fe2Fns]) h3).trans (callW_fe2_ownC hF2 (by simp [fe2Fns]) h1)
  have e1 := hd1.1
  have e3 := hd3.1
  refine RefE.guard rfl (fun e => by grind) (fun hb => by grind) fun _ _ => ?_
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r4 m4 h4 => ?_
  obtain ⟨hm4, hfd⟩ := envFind_call hG.toMasterProg n hn hS3.check.env h4
  subst hm4
  cases hf : fe2.find? (decI n) with
  | none =>
    rw [hf] at hfd
    have hz : r4.headD 0 = 0 := hfd
    rw [snpFe2E.k_env_find.abort1 p _ _ hz]; exact RefE.of_cls0 rfl
  | some ci =>
  rw [hf] at hfd
  obtain ⟨hf1, hci⟩ := hfd
  have hnz : r4.headD 0 ≠ 0 := by rw [hf1]; decide
  by_cases hkk' : ¬ erRd m4 (r4.tail.headD 0) = 1
  · rw [snpFe2E.k_env_find.abort2 p _ _ hnz hkk']; exact RefE.of_cls0 rfl
  have hkk : erRd m4 (r4.tail.headD 0) = 1 := Classical.not_not.mp hkk'
  rw [snpFe2E.k_env_find.arm1 p _ _ hnz hkk]
  simp only [erRd_foldN]
  generalize r4.tail.headD 0 = q at hci hkk ⊢
  rcases decCI_defn_cases hci with ⟨cv, v, hint, rfl, -, -⟩ | ⟨w1, hw1, hne, -⟩
  rotate_left
  · exact absurd hkk (by rw [(erRd_of_erecP hw1).1]; exact hne)
  obtain ⟨wv, -, hk5, hwl, hwd⟩ := decCI_defn_val hci
  have e5 : erRd m4 (q + CI.defnValue) = wv := (erRdOK m4).at _ rfl hk5
  rw [e5]
  exact RefE.ret rfl ⟨hS3, hg1.trans hg3, hwl, hwd, hfr, hown⟩

/-- **`StageC` across a leaf frame to another stage**: the stage relation and `CheckOK` after given,
the memory's half of `TwinOK` by the frame. -/
theorem StageC.of_frame {vis vis' : Word} {fe fe' : IFEnv} {env : ConLeche.Env} {m m' : Mem}
    {a a' : AState} (h : StageC dn vis fe env m a) (hS : StageR vis' fe' m' a')
    (hck : CheckOK false env fe' a') (hf : MemFrame leafA leafC m m')
    (hx : Ext a.store a'.store) : StageC dn vis' fe' env m' a' :=
  ⟨hS, hck,
    ⟨by rw [hf.size]; exact h.mem.erec, by rw [hf.size]; exact h.mem.spn,
      by rw [hf.size]; exact h.mem.bstk,
      h.mem.memos.frame hf leafA_memo leafC_memo leafA_walk leafC_walk leafA_lp leafC_lp leafA_hb leafC_hb,
      fun k x e => hx.lss.ls.ns k x (h.mem.dnN k x e)⟩,
    by simp only [pinW, hf.arr PINS leafA_pins (by decide)]; exact h.flag⟩

/-- The structural gate's program facts: the leaves' (`NatSubProg'`), the gate's two functions,
the push and the pop, and the reads' frame (`Fe2Closed`). -/
structure SnpProg (p : Prog) : Prop extends NatSubProg' p where
  snp : p.lookup "check_structural_nat_pin" = some checkStructuralNatPinL
  snpFe2 : p.lookup "check_structural_nat_pin_at_fe2" = some checkStructuralNatPinAtFe2L
  rs : p.lookup "env_row_set" = some envRowSetL
  push : p.lookup "env_push" = some envPushL
  pop : p.lookup "env_pop_temp" = some envPopTempL
  ef : EnvFlagsProg p
  fe2 : Fe2Closed p

/-- What the structural gate gives besides the twin's run (from `m`, `a`): `StageC` at the
returned index (the push popped), the growth, `Ext` of the twin's store, the view back at `vis`,
the returned index answering as `fe`, the pins unchanged. -/
structure SnpPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (env : ConLeche.Env) (m m' : Mem) (r : Word) (fe' : IFEnv) (a a' : AState) : Prop where
  stage : StageC dn vis fe' env m' a'
  grow : IWGrow m m'
  ext : Ext a.store a'.store
  ret : r = vis
  same : ConRon.Bridge.IFEnv.SameView fe' fe
  pins : a'.pins = a.pins

/-- **`check_structural_nat_pin` refines `checkStructuralNatPin` under `StageC`, both outcomes**
(con-ron's `checkStructuralNatPin_bridge`): the own row read, the push, the reads at the pushed
view (`snpFe2_ref`), the pop (`pushPop_stage`: the twin's popped index, which answers as `fe`),
then the equations and their substitution (leaves) and the certificate (`cert_ref`) at `vis`; a
failed certificate is the twin's `notImplemented`. -/
theorem snp_ref (hN : SnpProg p) (hq : KnotStageProg p) (hcl : LeafClosed p) {vis pw n : Word}
    {fe : IFEnv} {env env2 : ConLeche.Env} {nm : ConLeche.Name} {ci : IConstantInfo} (k : Nat)
    (hk : k ≤ 2 ^ 62) {m : Mem} {a : AState} (hn : H n) (hC : StageC dn vis fe env m a)
    (henv : ConLeche.EnvWF env) (hci : decCI (erecP m) pw.toNat = some ci)
    (hname : ci.name = decI n) (hok2 : StepOK env2 (fe.push ci) a)
    (hnm : denoteN a.store.ns (decI n) = some nm) :
    RefE (CoreStubsE p) (snpE p k m vis pw n) (checkStructuralNatPin V fe ci (decI n)) a
      (fun v fe' a' => SnpPost dn vis fe env m v.2 v.1 fe' a a') := by
  cases k with
  | zero => rw [snpE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ k =>
  have hk' : k ≤ 2 ^ 62 := by omega
  rw [snpE.arm1]
  have hE := hN.toNatSubProg.toNatEqProg
  have hM := hE.toNatTyProg.toNatGuardProg.toNatLitProg.toNatCvProg.toNatGateProg.toMasterProg
  have hsv := ConRon.Bridge.IFEnv.sameView_popTemp fe ci
  simp only [checkStructuralNatPin]
  -- the own row the push displaces
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r1 m1 h1 => ?_
  obtain ⟨s1, hs1, hm1, -, hr1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envRowGet_spec p hM.lEnvRowGet k _ n) h1
  have hm1' : m1 = m := by rw [← hs1, hm1]
  subst hm1'
  rw [snpE.k_env_row_get.arm1, hr1]
  simp only [List.headD_cons, List.tail_cons]
  -- the push
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r2 m2 h2 => ?_
  rw [snpE.k_env_push.arm1]
  obtain ⟨hS2, hg2⟩ := envPush_stage hN.ef h2 hC.stage hci
  have hf2 := callW_leafFrame hcl (leaf_mem _ (by decide)) h2
  -- the reads at the pushed view
  refine RefE.bindE (fun _ => rfl) (fun _ => trivial)
    (snpFe2_ref hN.toNatSubProg' hcl hN.fe2 k hn hS2) fun ⟨v3, m3⟩ y3 a3 hrun3 hQ3 => ?_
  rw [snpE.k_check_structural_nat_pin_at_fe2.arm1]
  dsimp only at hQ3
  obtain ⟨hst3, hx3, hc3, hp3, -, cv', v', hint', hfindP, hv3⟩ :=
    ConRon.Bridge.checkStructuralNatPinAtFe2_bridge hC.check.state hC.check.pins hok2 hnm hrun3
  -- the pop
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r4 m4 h4 => ?_
  rw [snpE.k_env_pop_temp.arm1]
  obtain ⟨hS4, hg4, hr4⟩ := pushPop_stage hN.ef hN.pop hC.stage hci hname hn h2 hQ3.stage
    (hg2.trans hQ3.grow) hQ3.own h4
  have hf4 := callW_leafFrame hcl (leaf_mem _ (by decide)) h4
  -- the flags set back
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r45 m45 h45 => ?_
  rw [snpE.k_env_set_flags.arm1]
  obtain ⟨hS45, hg45, -⟩ := setFlags_stage hN.ef hS4 hC.stage.check.env.natLit
    hC.stage.check.env.strLit h45
  have hf45 := callW_leafFrame hcl (leaf_mem _ (by decide)) h45
  rw [hname] at hS45
  have hck4 : CheckOK false env
      (((fe.push ci).popTemp ci.name fe.idx[ci.name]?).setFlags fe.natLit fe.strLit) a3 :=
    (hC.check.mono hst3 hx3 hc3 hp3).congr_find hsv.find hsv.tbls hsv.base
      (hsv.flags hC.check.ienv.flags)
  rw [hname] at hck4 hsv
  have hC4 := StageC.of_frame hC hS45 hck4 (((hf2.trans hQ3.frame).trans hf4).trans hf45) hx3
  have hnm4 := ConRon.Bridge.denoteN_ext hnm hx3
  -- the equations
  refine RefE.bindLift (fun _ => rfl) fun r5 m5 h5 => ?_
  obtain ⟨x5, a5, hrun5, hS5, hg5, hd5⟩ :=
    natOpEquations_ref hN.toNatSubProg' 0 n k m45 a3 r5 m5 ⟨hS45, by decide, hn⟩ h5
  have hrun5' : (natOpEquations 0 (decI n)).run a3 = .ok (x5, a5) := hrun5
  refine ⟨_, _, hrun5', ?_⟩
  dsimp only [snpE.k_nat_op_equations]
  obtain ⟨hst5, hx5, hc5, hp5, hdeq⟩ :=
    ConRon.Bridge.natOpEquations_run hC4.check.state hC4.check.pins hnm4 hrun5'
  have hC5 := StageC.of_run hC4 hS5 (callW_leafFrame hcl (leaf_mem _ (by decide)) h5)
    hst5 hx5 hc5 hp5
  have hE5 := decEqRL_headD hd5
  -- their substitution
  rw [← hQ3.dec]
  refine RefE.bindLift (fun _ => rfl) fun r6 m6 h6 => ?_
  obtain ⟨x6, a6, hrun6, hS6, hg6, hd6⟩ := pairs_ref hN.toNatSubProg n v3 hn hQ3.hw x5 (r5.headD 0)
    (r5.tail.headD 0) k m5 a5 r6 m6 hS5 hE5 (EqL.lt64 hE5 hS5.iw) h6
  have hvP5 : denoteE a5.store (decE v3) = some v' := by
    rw [hQ3.dec]; exact ConRon.Bridge.denote_ext hv3 hx5
  obtain ⟨hst6, hx6, hc6, hp6, hdps⟩ := ConRon.Bridge.substConst0Pairs_run hst5 hC5.check.pins
    (ConRon.Bridge.denoteN_ext hnm4 hx5) hvP5 hdeq hrun6
  have hC6 := StageC.of_run hC5 hS6 (callW_leafFrame hcl (leaf_mem _ (by decide)) h6)
    hst6 hx6 hc6 hp6
  have hE6 := decEqRL_headD hd6
  refine ⟨_, _, (hrun6 : (substConst0Pairs (decI n) (decE v3) x5).run a5 = .ok (x6, a6)), ?_⟩
  dsimp only [snpE.k_subst_const0_pairs]
  -- the certificate
  refine RefE.bindE (fun _ => rfl) id
    (cert_ref hq _ _ x6 k hk' m6 a6 hC6.stageT hE6 (EqL.lt64 hE6 hS6.iw))
    fun ⟨r7, m7⟩ x7 a7 hrun7 hQ7 => ?_
  dsimp only at hQ7
  obtain ⟨hstep7, -⟩ := ConRon.Bridge.certifyNatEqs_bridge ConRon.Bridge.CoreSpec.of_core
    hC6.check henv hdps (ConRon.Bridge.natOpEqs_wscoped hok2.envWF hfindP) hrun7
  have hC7 := L.Ind.StageC.of_T hQ7.stage hstep7.ok
  refine RefE.guardIf rfl (fun e7 => by rw [← hQ7.res.1, e7]; rfl)
    (fun e7 => by rw [← hQ7.res.1] at e7; simpa using e7) fun _ _ => ?_
  rw [hr4] at hC7
  exact RefE.ret rfl ⟨hC7, (((((hg2.trans hQ3.grow).trans hg4).trans hg45).trans hg5).trans hg6).trans hQ7.grow,
    ((hx3.trans hx5).trans hx6).trans hstep7.ext, hr4, hsv, by rw [hstep7.pins, hp6, hp5, hp3]⟩

end snp

end L.Arena
