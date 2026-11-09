module

public import ConAgua.Arena.DeclDivGateT2
import ConAgua.L.ModelGen
import ConAgua.Arena.DeclDivGateT1
import ConAgua.Arena.DeclNatGate
import ConAgua.Arena.DeclReducePin
import ConAgua.Arena.RecGenSpec.CruleProg
import ConAgua.Arena.RefWalk
import ConAgua.Arena.StageC
import ConAgua.Checker.NoVerdictTree
import all ConAgua.Arena.DeclArmsNat

@[expose] public section

/-!
# The `Nat.div` family's variant loop `check_div_mod_pin_loop`

One model (`l_model … unified`) and one refinement for both outcomes, under `StageC`
(con-ron's `checkDivModPinLoop_bridge`): the loop over the variant records
(`loop_ref`; the guards lifted, the attempt by `cpa_ref`). Its errors claim from the core stubs'
(`CoreStubsE`). The pin gate `check_div_mod_pin` (`cdmp_ref`, `DeclDivGateT.lean`) reads it.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena
open L.Rom (PinSetsR PinSetR)
open ConRon.Bridge (CheckOK StepOK PinsDenote CoreStep)

local notation "V" => ConLeche.CheckMode.verified

/-- **The model of `check_div_mod_pin_loop`, both outcomes**: the two guards (outside the verdict
closure) lifted, `check_div_mod_pin_at` by its model. -/
l_model checkDivModPinLoop_specE (p : Prog) (hD : DmProg8 p)
  fns [hD.lCheckDivModPinLoop ↦ checkDivModPinLoopE]
  specs [callW_spec p n "div_mod_pin_guard", callW_spec p n "div_mod_certs_guard",
    checkDivModPinAt_specE p hD.lCheckDivModPinAt hD.lCheckTypePins hD.lCheckDivModPinValue
      hD.lCheckDivModCerts n]
  grind [arena_grind] extra [ld64_rdW_specE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What the variant loop and the gate give besides the twin's run (from `m`, `a`): `StageC`
after, the twin's core step, the growth. -/
structure PinPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (env : ConLeche.Env) (m : Mem) (a : AState) (m' : Mem) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  ext : Ext a.store a'.store
  pins : a'.pins = a.pins

section loop
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  {p : Prog}

/-- **`check_div_mod_pin_loop` refines `checkDivModPinLoop` under `StageC`, both outcomes**
(con-ron's `checkDivModPinLoop_bridge`): the pin guard (`pgC`), on `true` the certificates' guard
(`cgsC`), on `true` the attempt (`cpa_ref`); every other outcome moves on to the next variant; no
variant left is the twin's `fail`. -/
theorem loop_ref (hD : DmProg8 p) (hq : KnotStageProg p) (hcl : LeafClosed p) (hkp : CrKeep p)
    (hs0 : SubstC0 p vis fe) (hsA : SubstCAll p vis fe) (henv : ConLeche.EnvWF env)
    (c value : Word) (hc : H c) (hval : H value) {nm : ConLeche.Name} {v : ConLeche.Expr}
    (hwsv : ConLeche.Expr.WScoped 0 v) :
    ∀ (ips : List INatOpPinSet) (psPs : List ConLeche.NatOpPinSet) (po pl : Word)
      (tried : List String) (k : Nat), k ≤ 2 ^ 62 → ∀ (m : Mem) (a : AState),
      StageC dn vis fe env m a → L.Stubs.CrOK m → PinsIW m po.toNat pl.toNat ips →
      PinsDenote a.store ips psPs → denoteN a.store.ns (decI c) = some nm →
      denoteE a.store (decE value) = some v →
      RefE (CoreStubsE p) (checkDivModPinLoopE p k m vis c value po pl)
        (checkDivModPinLoop V fe (decI c) (decE value) ips tried) a
        (fun w _ a' => PinPost dn vis fe env m a w.2 a') := by
  sorry

end loop

end L.Ind
