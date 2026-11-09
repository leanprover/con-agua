module

public import ConAgua.Verdict.DivModPinE
public import ConAgua.Arena.DeclArmDefn
import ConAgua.Arena.DeclDivGateT1
public import ConAgua.Arena.DeclNatGateT
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

/-- **`rom_pin_sets()`, then `check_div_mod_pin(po, pl, vis, p, n)` refines `checkDivModPin` under
`StageC`, both outcomes** (con-ron's `checkDivModPin_bridge`): the own row read, the push, the
environment guard and the stored value at the pushed view (`check_div_mod_pin_at_fe2`), the pop
(`pushPop_stage`), then the variant loop (`check_div_mod_pin_loop`) at `vis` over the ROM's
variant records (`PinSetsR`, their twin denotations `PinsDenote`). -/
theorem cdmp_ref {p : Prog} (hD : DmProg10 p) (hq : KnotStageProg p) (hcl : LeafClosed p)
    (hkp : CrKeep p) {dn : NIdx → Option ConLeche.Name} {pins : List INatOpPinSet}
    {pinsP : List ConLeche.NatOpPinSet} {vis pw n : Word} {fe : IFEnv} {env env2 : ConLeche.Env}
    {nm : ConLeche.Name} {ci : IConstantInfo} (k : Nat) (hk : k ≤ 2 ^ 62) {m m0 : Mem}
    {a : AState} {r0 : List Word} (hn : H n) (hC : StageC dn vis fe env m a)
    (henv : ConLeche.EnvWF env) (hci : decCI (erecP m) pw.toNat = some ci)
    (hname : ci.name = decI n) (hok2 : StepOK env2 (fe.push ci) a)
    (hnm : denoteN a.store.ns (decI n) = some nm) (hPS : PinSetsR m pins)
    (hPD : PinsDenote a.store pins pinsP) (hCr : L.Stubs.CrOK m)
    (h0 : callW p k "rom_pin_sets" [] m = some (r0, m0)) :
    RefE (CoreStubsE p)
      (callE p k "check_div_mod_pin" [r0.headD 0, r0.tail.headD 0, vis, pw, n] m0)
      (checkDivModPin V pins fe ci (decI n)) a
      (fun v fe' a' => L.Arena.SnpPost dn vis fe env m v.2 (v.1.headD 0) fe' a a') := by
  sorry

end L.Ind
