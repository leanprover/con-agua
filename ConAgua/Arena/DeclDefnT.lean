module

import ConAgua.Arena.DeclNatGateT
public import ConAgua.Arena.DeclArmLoop
public import ConAgua.Arena.DeclDivGateT
import ConAgua.Arena.DeclArmT
import ConAgua.Arena.DeclStepSpec
import ConAgua.Arena.RecGenSpec.CruleProg
import ConAgua.Arena.RefWalk
import ConAgua.L.ModelGen
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

/-- The definition arm's program facts under `StageT`: its text, the structural gate's text (a
`NatSubProg'` with the two gate functions, its functions with a step's write set), and the pin
gate's `StageC` spec. -/
structure DefnProgT (p : Prog) (pins : List INatOpPinSet) : Prop where
  df : p.lookup "check_decl_defn" = some checkDeclDefn
  nat : NatSubProg' p
  natIn : StepIn p natGateFns

set_option experimental.vcgen true in
/-- **The model of `check_decl_defn`, both outcomes**: its callees through their runs. -/
l_model checkDeclDefn_specE (p : Prog) (hf : p.lookup "check_decl_defn" = some checkDeclDefn)
  fns [hf ↦ checkDeclDefnE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specT, ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified

/-- What the definition arm's error arms assume: `check_constant_val`'s (`VerdictCtxU`),
`install_value_guards`' claim (`check_defn_val`), the pin gate's claim. -/
structure CdfCtx (p : Prog) (pins : List INatOpPinSet) : Prop extends VerdictCtxU p where

/-- What the definition arm gives besides the twin's run: the stage at the twin's environment,
the core's memos, the growth, the variant records. -/
structure CdfPost (dn : NIdx → Option ConLeche.Name) (pins : List INatOpPinSet) (m : Mem)
    (w : Word × Mem) (y : IFEnv) (a' : AState) : Prop where
  stage : StageR w.1 y w.2 a'
  memos : CoreMemos w.2
  grow : IWGrow m w.2
  pins : PinSetsR w.2 pins

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **The definition arm refines `checkDecl`, both outcomes**, under `StageT` (con-ron's
`checkDecl_bridge_defn`'s decomposition): from `StageT`, the fold invariant `FoldOK`, the
declaration's constant and value denoting, the variant records in memory (`PinSetsR`) and in the
twin's store (`PinsDenote`): the constant check (`ccv_ref`), the definition check (`dv_ref`), the
structural gate (`dng_ref`), the pin gate (`DivGateSpecC`, `DivGateSpecE`). -/
theorem cdf_ref {p : Prog} (hA : ArmProg p) (hV : ValProg p) {pins : List INatOpPinSet}
    (hDP : DefnProgT p pins) (hq : KnotStageProg p) (hcl : LeafClosed p) (hlc : LoopClosed p)
    (hap : ApdF p) (hkp : CrKeep p) {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn)
    {vis : Word} {fe : IFEnv} {env : ConLeche.Env} {a : AState} (n : Nat) (hn : n ≤ 2 ^ 62)
    {m : Mem} {i : Word} {ds : Array IDeclaration} {cv : IConstantVal} {v : EIdx}
    {hh : ConLeche.ReducibilityHint} {c : ConLeche.ConstantVal} {x : ConLeche.Expr}
    (hS : StageT dn vis fe m a) (hPS : PinSetsR m pins)
    (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds) (hi : i.toNat < ds.size)
    (hd : ds[i.toNat] = .defnDecl cv v hh) (hfold : FoldOK V env fe a)
    (hcvd : Frontend.denoteCV a.store cv = some c) (hvd : denoteE a.store v = some x)
    (hPD : ∃ pinsP, PinsDenote a.store pins pinsP) (hCr : L.Stubs.CrOK m) :
    RefE (CdfCtx p pins) (checkDeclDefnE p n m i vis) (checkDecl V pins fe (.defnDecl cv v hh)) a
      (fun w y a' => CdfPost dn pins m w y a') := by
  sorry

-/

end L.Arena
