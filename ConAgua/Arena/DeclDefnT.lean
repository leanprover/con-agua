module

public import ConAgua.Arena.DeclNatGateT
public import ConAgua.Arena.DeclAxQuotT
public import ConAgua.Arena.DeclArmLoop
public import ConAgua.Arena.DeclDivGateT
import ConAgua.Arena.DeclArmT
import ConAgua.Arena.DeclStepSpec
import ConAgua.Arena.RecGenSpec.CruleProg
import ConAgua.Arena.RefWalk
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
import ConRon.Bridge.Checker.Arms
import ConRon.Bridge.Checker.Base
public import ConAgua.Arena.DeclNatGateSpec
public import ConAgua.Arena.DeclNatOpEq
public import ConAgua.Verdict.DeclValE
import all ConAgua.Arena.DeclArms

@[expose] public section

/-!
# The definition arm under `StageT` (lane `loopt3`, helper `loopt3-nat`)

`check_decl_defn`'s unified model and its refinement for both outcomes (`cdf_ref`), from `StageT`:
the constant check and the definition check (`ccv_ref`, `dv_ref`), then the two gates under
`StageC` at the pre-insertion view (con-ron's `CheckOK` restricted, the memory's half of `TwinOK`):
the structural-`Nat` gate (`dng_ref`, `DeclNatGateT.lean`) and the `Nat.div`-family pin gate
(`DivGateSpecC`/`DivGateSpecE`, `DeclDivGateT.lean`). The twin side is con-ron's
`checkDecl_bridge_defn`: `FoldOK` at the arm's entry carried across the constant check
(`checkConstantVal_bridge_of_fold`) and the definition check (`checkDefnVal_bridge`, which gives
the pushed index's `StepOK` at `env2`, what the gates read the stored value and guards through).
The variant records (`PinSetsR`, carried by the step's write set) and their twin denotations
(`PinsDenote`, carried by `Ext`) reach the pin gate.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


noncomputable section

namespace L.Arena

open L.Ind
open L.Rom (PinSetsR)
open L.Front (DECL DLP DeclsF)
open ConRon.Bridge (CheckOK StepOK FoldOK CoreSpec PinsDenote)

local notation "V" => ConLeche.CheckMode.verified

/-- `check_defn_val` is one of the loop's functions. -/
theorem checkDefnVal_loop : "check_defn_val" ∈ loopFns := loop_mem _ rfl

/-- The definition arm's callees up to the pin gate (their frames keep `PinSetsR`). -/
def defnCallFns : List FnName :=
  ["check_constant_val", "check_defn_val", "nat_op_names", "sl_contains",
    "check_structural_nat_pin", "nat_div_mod_names"]

/-- The definition arm's program facts under `StageT`: its text, the constant and value checks',
the structural gate's (`SnpProg`), the pin gate's (`DmProg10`). -/
structure DefnProgT (p : Prog) : Prop where
  df : p.lookup "check_decl_defn" = some checkDeclDefn
  ccv : CcvProg p
  snp : SnpProg p
  dm : DmProg10 p
  /-- the arm's callees keep the memory outside a step's write set (the pin variants' header) -/
  step : StepIn p defnCallFns

set_option experimental.vcgen true in
/-- **The model of `check_decl_defn`, both outcomes**: `erec_ci` and the leaves through their runs,
the constant and value checks and the two gates through `callE` (read by their unified models'
specs in `cdf_ref`). -/
l_model checkDeclDefn_specE (p : Prog) (hX : DefnProgT p)
  fns [hX.df ↦ checkDeclDefnE]
  specs [erecCi_specW p hX.ccv.val.rcp n, callW_spec p n "nat_op_names",
    callW_spec p n "sl_contains", callW_spec p n "nat_div_mod_names",
    callW_spec p n "rom_pin_sets", callW_spec p n "env_push"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

end L.Arena
