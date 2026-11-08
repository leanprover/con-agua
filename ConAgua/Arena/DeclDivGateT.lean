module

public import ConAgua.Verdict.DivModPinE
public import ConAgua.Arena.DeclArmDefn
import ConAgua.Arena.DeclDivGateT1
import ConAgua.Arena.RecGenSpec.CruleProg
import ConAgua.Arena.RefWalk
import ConAgua.Arena.StageC
import ConAgua.Checker.NoVerdictTree
import ConAgua.L.ModelGen
import ConRon.Bridge.Checker.DeclVal
import all ConAgua.Arena.DeclArms

@[expose] public section

/-!
# The `Nat.div`-family pin gate under `StageC` (lane `loopt3`, helper `loopt3-div`)

`defn_div_gate` runs after the definition arm's push, at the pre-insertion view `vis` for its core
calls and at the pushed view `w` for the environment guard, under `StageC` (`TwinStep.lean`),
mirroring con-ron's `checkDivModPin_bridge` (`Bridge/Checker/DivMod.lean`), as `crp_ref`
(`DeclCrpT.lean`) does for the reduce-pin gate. One model and one refinement for both outcomes
(`dg_ref`): the leaves (`nat_div_mod_names`, `sl_contains`, `rom_pin_sets`) lifted, by their
`StageR` refinements and the leaves' write set (`LeafClosed`); the gate `check_div_mod_pin` by
`cp_ref` (`Verdict/DivModPinE.lean`; parts 1 and 2, `DeclDivGateT1.lean`, `DeclDivGateT2.lean`,
carry the guards and the attempt). The definition arm (`cdf_ref`) consumes the halves from the
call's run: `DivGateSpecC` (with the variant records after and the frame) and `DivGateSpecE`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Ind

open L.Arena
open L.Rom (PinSetsR PinSetR)
open ConRon.Bridge (CheckOK StepOK PinsDenote CoreStep)

local notation "V" => ConLeche.CheckMode.verified

/- ronsync2 stage 2: commented out (statement at the old twin/L)
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
    StageR w fe2 m a → StageC dn vis (fe2.restrictTo vis.toNat) env m a →
    ConLeche.EnvWF env → StepOK env2 fe2 a → PinSetsR m pins →
    (∃ pinsP, PinsDenote a.store pins pinsP) →
    denoteN a.store.ns (decI n) = some nm → L.Stubs.CrOK m →
    ∃ a', (divGateT pins (fe2.restrictTo vis.toNat) fe2 (decI n)).run a = .ok ((), a') ∧
      StageR w fe2 m' a' ∧ StageC dn vis (fe2.restrictTo vis.toNat) env m' a' ∧
      Ext a.store a'.store ∧ IWGrow m m' ∧ PinSetsR m' pins ∧ MemFrame stepA stepC m m'
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`defn_div_gate`'s error claim under `StageC`** (the error half of `DivGateSpecC`). -/
def DivGateSpecE (p : Prog) (pins : List INatOpPinSet) : Prop :=
  ∀ (dn : NIdx → Option ConLeche.Name), DnInj dn → ∀ (vis w : Word) (fe2 : IFEnv)
    (env env2 : ConLeche.Env) (n : Word) (nm : ConLeche.Name) (k : Nat), k ≤ 2 ^ 62 →
    ∀ (m : Mem) (a : AState), n.toNat < 2 ^ 32 →
    StageR w fe2 m a → StageC dn vis (fe2.restrictTo vis.toNat) env m a →
    ConLeche.EnvWF env → StepOK env2 fe2 a → PinSetsR m pins →
    (∃ pinsP, PinsDenote a.store pins pinsP) →
    denoteN a.store.ns (decI n) = some nm → L.Stubs.CrOK m →
    ∀ e, callE p k "defn_div_gate" [vis, w, n] m = .error e →
    ErrClaim (divGateT pins (fe2.restrictTo vis.toNat) fe2 (decI n)) a e
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
set_option experimental.vcgen true in
/-- **The model of `defn_div_gate`, both outcomes**: the family's names, the membership and the
variant records (outside the verdict closure) lifted, `check_div_mod_pin` by its model. -/
l_model defnDivGate_specE (p : Prog) (hD : DmProg10 p)
  fns [hD.lDefnDivGate ↦ defnDivGateE]
  specs [callW_spec p n "nat_div_mod_names", callW_spec p n "sl_contains",
    callW_spec p n "rom_pin_sets", checkDivModPin_specE p hD.toDmProg8 n]
  grind [arena_grind] extra [ld64_rdW_specE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]
-/

/-- What the pin gate gives besides the twin's run (from `m`, `a`): the stage relation at the
pushed view `w`, `StageC` at the pre-insertion view `vis`, `Ext` of the twin's store, the growth.
(The variant records after and the frame come from the call's run: `divGateSpecC`.) -/
structure DgPost (dn : NIdx → Option ConLeche.Name) (vis w : Word) (fe2 : IFEnv)
    (env : ConLeche.Env) (m : Mem) (a : AState) (m' : Mem) (a' : AState) : Prop where
  stageW : StageR w fe2 m' a'
  ext : Ext a.store a'.store
  grow : IWGrow m m'

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`defn_div_gate(vis, w, n)` refines `divGateT` under `StageC`, both outcomes**: from the stage
relation at the pushed view `w` (extended index `fe2`), `StageC` at the pre-insertion view `vis`
(con-ron's `CheckOK` at the environment `env` before the push), `env`'s well-formedness, the pushed
index's `StepOK` (at `env2`), the variant records in memory (`PinSetsR`) and in the twin's store
(`PinsDenote`), the name's denotation: the family's names, the membership, the variant records,
the gate (`cp_ref`). -/
theorem dg_ref {p : Prog} (hD : DmProg10 p) (hq : KnotStageProg p) (hcl : LeafClosed p)
    (hCl : StepIn p dgFns) (hs0 : ∀ dn vis fe, SubstC0 p dn vis fe)
    (hsA : ∀ dn vis fe, SubstCAll p dn vis fe) (hkp : CrKeep p) {pins : List INatOpPinSet}
    {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn) {vis w : Word} {fe2 : IFEnv}
    {env env2 : ConLeche.Env} {n : Word} {nm : ConLeche.Name} {k : Nat} (hk : k ≤ 2 ^ 62)
    {m : Mem} {a : AState} (hn : n.toNat < 2 ^ 32) (hS : StageR w fe2 m a)
    (hC : StageC dn vis (fe2.restrictTo vis.toNat) env m a) (henv : ConLeche.EnvWF env)
    (hok2 : StepOK env2 fe2 a) (hP : PinSetsR m pins) (hpd : ∃ pinsP, PinsDenote a.store pins pinsP)
    (hnm : denoteN a.store.ns (decI n) = some nm) (hCr : L.Stubs.CrOK m) :
    RefE (CoreStubsE p) (defnDivGateE p k m vis w n)
      (divGateT pins (fe2.restrictTo vis.toNat) fe2 (decI n)) a
      (fun x _ a' => DgPost dn vis w fe2 env m a x.2 a') := by
  sorry

-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`defn_div_gate` under `StageC`** from the call's run (`dg_ref`'s ok half; the variant records
after and the frame from the gate's write set). -/
theorem divGateSpecC {p : Prog} (hD : DmProg10 p) (hq : KnotStageProg p) (hcl : LeafClosed p)
    (hCl : StepIn p dgFns) (hs0 : ∀ dn vis fe, SubstC0 p dn vis fe)
    (hsA : ∀ dn vis fe, SubstCAll p dn vis fe) (hkp : CrKeep p) (pins : List INatOpPinSet) :
    DivGateSpecC p pins := by
  sorry

-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`defn_div_gate`'s error claim under `StageC`** (`dg_ref`'s error half). -/
theorem divGateSpecE_of {p : Prog} (hD : DmProg10 p) (hq : KnotStageProg p) (hcl : LeafClosed p)
    (hCl : StepIn p dgFns) (hs0 : ∀ dn vis fe, SubstC0 p dn vis fe)
    (hsA : ∀ dn vis fe, SubstCAll p dn vis fe) (hkp : CrKeep p) (hcE : CoreStubsE p)
    (hnv : closedNV p L.Checker.nvFns = true) (pins : List INatOpPinSet) :
    DivGateSpecE p pins := by
  sorry

-/

end L.Ind
