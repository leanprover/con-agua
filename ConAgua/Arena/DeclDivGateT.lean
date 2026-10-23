import ConAgua.Arena.DeclDivMod10
import ConAgua.Arena.DeclCrpT
import ConAgua.Arena.IndStubsT
import ConRon.Bridge.Checker.DivMod

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

The definition arm (helper `loopt3-nat`'s `cdfW_okT`) consumes `DivGateSpecC`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.deprecated false

namespace L.Ind

open L.Arena
open L.Rom (PinSetsR PinSetR)
open ConRon.Bridge (CheckOK StepOK PinsDenote)

local notation "V" => ConLeche.CheckMode.verified

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
