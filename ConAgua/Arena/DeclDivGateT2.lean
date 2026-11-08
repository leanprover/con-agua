module

import ConAgua.Arena.DeclDivGateT1
public import ConAgua.Arena.DeclDivModSpec.RomPinSets
import ConAgua.Arena.DeclCrpT
import all ConRon.Bridge.Checker.DivMod
import ConAgua.Arena.DeclDivModSpec.CertDivModEqs
import ConAgua.Arena.DeclDivModSpec.CertTwoEqs
import ConAgua.Arena.DeclNatGate
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.RefWalk
import ConAgua.Arena.StageC
import ConAgua.Checker.NoVerdictTree
import ConAgua.L.ModelGen
public import ConAgua.Arena.CrOKFrame
public import ConAgua.Arena.DeclDivModSpec.SubstConst0List
public import ConAgua.Arena.KnotEntry
public import ConAgua.Arena.LeafFns
public import ConAgua.Arena.TwinStep
public import ConAgua.Verdict.VCtx
public import ConRon.Bridge.Checker.DivMod
import all ConAgua.Arena.DeclArmsNat

@[expose] public section

/-!
# The `Nat.div`-family pin gate under `StageC`, part 2: the attempt (lane `loopt3`, `loopt3-div`)

`check_div_mod_certs` (`cm_ref`), `check_type_pins` (`ctp_ref`), `check_div_mod_pin_value`
(`cpv_ref`), `check_div_mod_pin_at` (`cpa_ref`), each one refinement of its unified model for both
outcomes (the variant loop and the gate over them: `Verdict/DivModPinE.lean`): the core calls
`infer_type_core`, `is_def_eq_core` by the knot's `StageT` sims (`KnotStageProg`; their failures
by `CoreStubsE`) and `CheckOK` after from con-ron's `KnotSpec` (`StageC.of_T`), the leaves as in
part 1, lifted (their failures are of class `0`). The twin side follows con-ron's
`checkDivModCerts_bridge_aux`, `checkTypePins_spec` and `checkDivModPinAt_bridge`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena
open L.Rom (PinSetsR PinSetR)
open ConRon.Bridge (CheckOK StepOK PinsDenote PinSetDenote CoreStep CoreSpec)

local notation "V" => ConLeche.CheckMode.verified

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`infer_type_core`'s twin side** (`defeq_check`'s): con-ron's `KnotSpec.infer` at `checkFuel`. -/
theorem infer_check {env : ConLeche.Env} {fe : IFEnv} {a a' : AState} {d : Nat} {i t : EIdx}
    {x : ConLeche.Expr} (henv : ConLeche.EnvWF env) (hck : CheckOK V env fe a)
    (hi : denoteE a.store i = some x) (hws : ConLeche.Expr.WScoped d x)
    (hrun : (inferTypeCore V fe checkFuel d i).run a = .ok (t, a')) :
    CheckOK V env fe a' ∧ Ext a.store a'.store ∧ a'.pins = a.pins ∧
      ConRon.Bridge.Core.SimE (ConLeche.inferTypeCore V env) d x a'.store t := by
  sorry

-/

l_model checkDivModCerts_specE (p : Prog)
  (hf : p.lookup "check_div_mod_certs" = some checkDivModCertsL)
  fns [hf ↦ checkDivModCertsE]
  specs [callW_spec p n "div_mod_cert_guard", callW_spec p n "subst_const_all",
    callW_spec p n "subst_const0_list", callW_spec p n "div_mod_cert_applied",
    callW_spec p n "subst_const0"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What the `Nat.div`-family pin gate's checks give besides the twin's answer `x` (from `m`,
`a`): `StageC` after, the twin's core step, the growth, the result word decoding `x`,
`consts_resolve_ffast`'s memo kept. -/
structure DmPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (a : AState) (r : Word) (m' : Mem) (x : Bool) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  res : decW0B m' [r] x
  cr : L.Stubs.CrOK m'

section certs
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  {p : Prog}

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`check_div_mod_certs` refines `checkDivModCerts` under `StageC`, both outcomes** (con-ron's
`checkDivModCerts_bridge_aux`), by induction on the statements. -/
theorem cm_ref (hD : DmProg8 p) (hq : KnotStageProg p) (hcl : LeafClosed p) (hkp : CrKeep p)
    (hs0 : SubstC0 p dn vis fe) (hsA : SubstCAll p dn vis fe) (henv : ConLeche.EnvWF env)
    (c annVal : Word) (hc : H c) (hann : H annVal) {nm : ConLeche.Name} {v : ConLeche.Expr}
    (hwsv : ConLeche.Expr.WScoped 0 v) :
    ∀ (ss : List (List EIdx × EIdx)) (xs : List (List ConLeche.Expr × ConLeche.Expr))
      (proofs : List EIdx) (ps : List ConLeche.Expr) (so sl po pl : Word) (k : Nat), k ≤ 2 ^ 62 →
      ∀ (m : Mem) (a : AState), StageC dn vis fe env m a →
      L.Stubs.CrOK m →
      StmtL m so.toNat sl.toNat ss → decHL m po.toNat pl.toNat = some proofs →
      po.toNat + pl.toNat ≤ iwTop m → denoteN a.store.ns (decI c) = some nm →
      denoteE a.store (decE annVal) = some v → ConRon.Bridge.StmtsDenote a.store ss xs →
      Frontend.denoteEList a.store proofs = some ps →
      (∀ q ∈ xs, (∀ h ∈ q.1, ConLeche.Expr.WScoped 2 h) ∧ ConLeche.Expr.WScoped 2 q.2) →
      RefE (CoreStubsE p) (checkDivModCertsE p k m vis c annVal so sl po pl)
        (checkDivModCerts V fe (decI c) (decE annVal) ss proofs) a
        (fun v x a' => DmPost dn vis fe env m a v.1 v.2 x a') := by
  sorry

-/

end certs

l_model checkTypePins_specE (p : Prog) (hf : p.lookup "check_type_pins" = some checkTypePinsL)
  fns [hf ↦ checkTypePinsE]
  specs [callW_spec p n "type_pin_stored"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specT, ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

section typePins
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  {p : Prog}

-- RS2B ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`check_type_pins` refines `checkTypePins` under `StageC`, both outcomes** (con-ron's
`checkTypePins_spec`): per pair the stored type by `tps_ref`, then `is_def_eq_core` by the knot's
`StageT` sim (its failure by `CoreStubsE`), `CheckOK` after from con-ron's `KnotSpec`; both sides
closed by the variant's pin guard (`hcl'`). -/
theorem ctp_ref (hD : DmProg8 p) (hq : KnotStageProg p) (hcl : LeafClosed p) (hkp : CrKeep p)
    (henv : ConLeche.EnvWF env) :
    ∀ (tps : List (NIdx × EIdx)) (tpsP : List (ConLeche.Name × ConLeche.Expr)) (o l : Word)
      (k : Nat), k ≤ 2 ^ 62 → ∀ (m : Mem) (a : AState),
      StageC dn vis fe env m a → L.Stubs.CrOK m → L.Rom.TPinsR m o l tps →
      ConRon.Bridge.TypePinsDenote a.store tps tpsP →
      (∀ q ∈ tpsP, (ConLeche.typePinStored env q.1).hasFvar = false ∧ q.2.hasFvar = false) →
      RefE (CoreStubsE p) (checkTypePinsE p k m vis o l) (checkTypePins V fe tps) a
        (fun v x a' => DmPost dn vis fe env m a v.1 v.2 x a') := by
  sorry

-- RS2E

end typePins

l_model checkDivModPinValue_specE (p : Prog)
  (hf : p.lookup "check_div_mod_pin_value" = some checkDivModPinValueL)
  (hc : p.lookup "check_div_mod_certs" = some checkDivModCertsL)
  fns [hf ↦ checkDivModPinValueE]
  specs [callW_spec p n "div_mod_decl_pin", callW_spec p n "div_mod_cert_stmts",
    callW_spec p n "div_mod_cert_proofs", checkDivModCerts_specE p hc n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

section pinValue
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  {p : Prog}

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`check_div_mod_pin_value` refines `checkDivModPinValue` under `StageC`, both outcomes** (the
second half of con-ron's `checkDivModPinAt_bridge`, which takes the pin guard's `true` for the
pin's scope). -/
theorem cpv_ref (hD : DmProg8 p) (hq : KnotStageProg p) (hcl : LeafClosed p) (hkp : CrKeep p)
    (hs0 : SubstC0 p dn vis fe) (hsA : SubstCAll p dn vis fe) (henv : ConLeche.EnvWF env)
    {c value ps : Word} {ip : INatOpPinSet} {psP : ConLeche.NatOpPinSet} {nm : ConLeche.Name}
    {v : ConLeche.Expr} {k : Nat} (hk : k ≤ 2 ^ 62) {m : Mem} {a : AState}
    (hC : StageC dn vis fe env m a) (hc : H c) (hval : H value) (hP : PinSetR m ps ip)
    (hps : PinSetDenote a.store ip psP) (hn : denoteN a.store.ns (decI c) = some nm)
    (hv : denoteE a.store (decE value) = some v) (hwsv : ConLeche.Expr.WScoped 0 v)
    (hpg : ConLeche.divModPinGuard psP env nm = true) (hCr : L.Stubs.CrOK m) :
    RefE (CoreStubsE p) (checkDivModPinValueE p k m vis c value ps)
      (checkDivModPinValue V fe (decI c) (decE value) ip) a
      (fun v x a' => DmPost dn vis fe env m a v.1 v.2 x a') := by
  sorry

-/

end pinValue

l_model checkDivModPinAt_specE (p : Prog)
  (hf : p.lookup "check_div_mod_pin_at" = some checkDivModPinAtL)
  (ht : p.lookup "check_type_pins" = some checkTypePinsL)
  (hv : p.lookup "check_div_mod_pin_value" = some checkDivModPinValueL)
  (hc : p.lookup "check_div_mod_certs" = some checkDivModCertsL)
  fns [hf ↦ checkDivModPinAtE]
  specs [callW_spec p n "div_mod_type_pins", checkTypePins_specE p ht n,
    checkDivModPinValue_specE p hv hc n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

section pinAt
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  {p : Prog}

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`check_div_mod_pin_at` refines `checkDivModPinAt` under `StageC`, both outcomes** (con-ron's
`checkDivModPinAt_bridge`, which takes the pin guard's `true` for the type pins' and the pin's
scope): the type pins (`ctp_ref`), then the value pin and the certificates (`cpv_ref`). -/
theorem cpa_ref (hD : DmProg8 p) (hq : KnotStageProg p) (hcl : LeafClosed p) (hkp : CrKeep p)
    (hs0 : SubstC0 p dn vis fe) (hsA : SubstCAll p dn vis fe) (henv : ConLeche.EnvWF env)
    {c value ps : Word} {ip : INatOpPinSet} {psP : ConLeche.NatOpPinSet} {nm : ConLeche.Name}
    {v : ConLeche.Expr} {k : Nat} (hk : k ≤ 2 ^ 62) {m : Mem} {a : AState}
    (hC : StageC dn vis fe env m a) (hc : H c) (hval : H value) (hP : PinSetR m ps ip)
    (hps : PinSetDenote a.store ip psP) (hn : denoteN a.store.ns (decI c) = some nm)
    (hv : denoteE a.store (decE value) = some v) (hwsv : ConLeche.Expr.WScoped 0 v)
    (hpg : ConLeche.divModPinGuard psP env nm = true) (hCr : L.Stubs.CrOK m) :
    RefE (CoreStubsE p) (checkDivModPinAtE p k m vis c value ps)
      (checkDivModPinAt V fe (decI c) (decE value) ip) a
      (fun v x a' => DmPost dn vis fe env m a v.1 v.2 x a') := by
  cases k with
  | zero => rw [checkDivModPinAtE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ k =>
  have hk' : k ≤ 2 ^ 62 := by omega
  rw [checkDivModPinAtE.arm1]
  have hD1 := hD.toDmProg7.toDmProg6.toDmProg5.toDmProg2.toDmProg1
  simp only [checkDivModPinAt]
  -- the type pins
  refine RefE.bindSim (fun _ => rfl) ((divModTypePins_ref hD1 ps c ip) k m a · · ⟨hC.stage, hc, hP⟩ ·)
    fun r1 x1 m1 a1 h1 hrun1 ⟨hS1, hg1, hd1⟩ => ?_
  dsimp only [checkDivModPinAtE.k_div_mod_type_pins]
  have hCr1 := hkp.call (im_mem _ rfl) h1 hCr
  obtain ⟨e1, htd⟩ := ConRon.Bridge.divModTypePins_run hC.check.state hC.check.pins hps hn hrun1
  subst a1
  have hC1 := StageC.of_core hC hS1 (callW_leafFrame hcl (leaf_mem _ (by decide)) h1)
    (CoreStep.refl hC.check)
  refine RefE.bindE (fun _ => rfl) id (ctp_ref hD hq hcl hkp henv x1 _ _ _ k hk' m1 a hC1 hCr1 hd1 htd
    (ConRon.Bridge.divModTypePins_closed hpg)) fun ⟨r2, m2⟩ x2 a2 _ hR2 => ?_
  rw [checkDivModPinAtE.k_check_type_pins.eq_2]
  refine RefE.retIf (fun z2 => decW0B_false hR2.res (by simpa using z2))
    (fun hb => by rw [← hR2.res.1] at hb; simpa using hb)
    (fun _ => ⟨hR2.stage, hR2.core, hg1.trans hR2.grow, by simp [decW0B], hR2.cr⟩) fun z2 _ => ?_
  -- the value pin and the certificates
  refine (cpv_ref hD hq hcl hkp hs0 hsA henv hk' hR2.stage hc hval
    (PinSetR.grow hP (hg1.trans hR2.grow))
    (ConRon.Bridge.PinsDenote.mono hR2.core.ext [ip] [psP] ⟨hps, trivial⟩).1
    (ConRon.Bridge.denoteN_ext hn hR2.core.ext) (ConRon.Bridge.denote_ext hv hR2.core.ext) hwsv hpg
    hR2.cr).mono ?_
  exact fun _ _ _ hR => ⟨hR.stage, hR2.core.trans hR.core, hg1.trans (hR2.grow.trans hR.grow), hR.res, hR.cr⟩
-/

end pinAt

/-! ## The ok halves from the run (the census links) -/

section okRuns
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  {p : Prog}

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`check_div_mod_certs` under `StageC`** from the call's run (`cm_ref`'s ok half). -/
@[refines ConRon.Arena.checkDivModCerts]
theorem cmC (hD : DmProg8 p) (hq : KnotStageProg p) (hcl : LeafClosed p) (hkp : CrKeep p)
    (hs0 : SubstC0 p dn vis fe) (hsA : SubstCAll p dn vis fe) (henv : ConLeche.EnvWF env)
    (c annVal : Word) (hc : H c) (hann : H annVal) {nm : ConLeche.Name} {v : ConLeche.Expr}
    (hwsv : ConLeche.Expr.WScoped 0 v) {ss : List (List EIdx × EIdx)}
    {xs : List (List ConLeche.Expr × ConLeche.Expr)} {proofs : List EIdx} {ps : List ConLeche.Expr}
    {so sl po pl : Word} {k : Nat} (hk : k ≤ 2 ^ 62) {m : Mem} {a : AState} {res : List Word}
    {m' : Mem} (hC : StageC dn vis fe env m a) (hCr : L.Stubs.CrOK m)
    (hs : StmtL m so.toNat sl.toNat ss) (hd : decHL m po.toNat pl.toNat = some proofs)
    (hb : po.toNat + pl.toNat ≤ iwTop m) (hn : denoteN a.store.ns (decI c) = some nm)
    (hv : denoteE a.store (decE annVal) = some v) (hsd : ConRon.Bridge.StmtsDenote a.store ss xs)
    (hpr : Frontend.denoteEList a.store proofs = some ps)
    (hwq : ∀ q ∈ xs, (∀ h ∈ q.1, ConLeche.Expr.WScoped 2 h) ∧ ConLeche.Expr.WScoped 2 q.2)
    (hcall : callW p k "check_div_mod_certs" [vis, c, annVal, so, sl, po, pl] m = some (res, m')) :
    ∃ x a', (checkDivModCerts V fe (decI c) (decE annVal) ss proofs).run a = .ok (x, a') ∧
      StageC dn vis fe env m' a' ∧ CoreStep V env fe a a' ∧ IWGrow m m' ∧ decW0B m' res x := by
  sorry

-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`check_div_mod_pin_value` under `StageC`** from the call's run (`cpv_ref`'s ok half). -/
@[refines ConRon.Arena.checkDivModPinValue]
theorem cpvC (hD : DmProg8 p) (hq : KnotStageProg p) (hcl : LeafClosed p) (hkp : CrKeep p)
    (hs0 : SubstC0 p dn vis fe) (hsA : SubstCAll p dn vis fe) (henv : ConLeche.EnvWF env)
    {c value ps : Word} {ip : INatOpPinSet} {psP : ConLeche.NatOpPinSet} {nm : ConLeche.Name}
    {v : ConLeche.Expr} {k : Nat} (hk : k ≤ 2 ^ 62) {m m' : Mem} {a : AState} {r : List Word}
    (hcall : callW p k "check_div_mod_pin_value" [vis, c, value, ps] m = some (r, m'))
    (hC : StageC dn vis fe env m a) (hc : H c) (hval : H value) (hP : PinSetR m ps ip)
    (hps : PinSetDenote a.store ip psP) (hn : denoteN a.store.ns (decI c) = some nm)
    (hv : denoteE a.store (decE value) = some v) (hwsv : ConLeche.Expr.WScoped 0 v)
    (hpg : ConLeche.divModPinGuard psP env nm = true) (hCr : L.Stubs.CrOK m) :
    ∃ x a', (checkDivModPinValue V fe (decI c) (decE value) ip).run a = .ok (x, a') ∧
      StageC dn vis fe env m' a' ∧ CoreStep V env fe a a' ∧ IWGrow m m' ∧ decW0B m' r x := by
  sorry

-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`check_div_mod_pin_at` under `StageC`** from the call's run (`cpa_ref`'s ok half). -/
@[refines ConRon.Arena.checkDivModPinAt]
theorem cpaC (hD : DmProg8 p) (hq : KnotStageProg p) (hcl : LeafClosed p) (hkp : CrKeep p)
    (hs0 : SubstC0 p dn vis fe) (hsA : SubstCAll p dn vis fe) (henv : ConLeche.EnvWF env)
    {c value ps : Word} {ip : INatOpPinSet} {psP : ConLeche.NatOpPinSet} {nm : ConLeche.Name}
    {v : ConLeche.Expr} {k : Nat} (hk : k ≤ 2 ^ 62) {m m' : Mem} {a : AState} {r : List Word}
    (hcall : callW p k "check_div_mod_pin_at" [vis, c, value, ps] m = some (r, m'))
    (hC : StageC dn vis fe env m a) (hc : H c) (hval : H value) (hP : PinSetR m ps ip)
    (hps : PinSetDenote a.store ip psP) (hn : denoteN a.store.ns (decI c) = some nm)
    (hv : denoteE a.store (decE value) = some v) (hwsv : ConLeche.Expr.WScoped 0 v)
    (hpg : ConLeche.divModPinGuard psP env nm = true) (hCr : L.Stubs.CrOK m) :
    ∃ x a', (checkDivModPinAt V fe (decI c) (decE value) ip).run a = .ok (x, a') ∧
      StageC dn vis fe env m' a' ∧ CoreStep V env fe a a' ∧ IWGrow m m' ∧ decW0B m' r x := by
  sorry

-/

end okRuns

end L.Ind
