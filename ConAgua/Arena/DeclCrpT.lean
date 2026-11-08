module

public import ConAgua.Arena.DeclArmT
import ConAgua.Arena.RecGenSpec.CruleProg
public import ConAgua.Arena.DeclReducePin
import ConAgua.Arena.DeclStepSpec
import ConAgua.Arena.IndRealMemoCrT
import ConAgua.Arena.IndRealWalkT
import ConAgua.Arena.RefWalk
import ConAgua.Arena.StageC
import ConAgua.L.ModelGen
import ConRon.Bridge.Checker.Arms
import ConRon.Bridge.Checker.Base
import ConRon.Bridge.Checker.DeclVal
public import ConAgua.Arena.LeafFns
public import ConRon.Bridge.Core.Knot
import all ConAgua.Arena.DeclArms

@[expose] public section

/-!
# The reduce-pin gate and the opaque arm under `StageC` (lane `loopt2`)

`check_reduce_pin` (`DeclReducePin.lean`) runs after the opaque's push, interning between its two
core calls: `TwinOK` cannot be tracked on the L side there (landing 6). It runs here under `StageC`
(`TwinStep.lean`): the stage relation, con-ron's `CheckOK`, the memory's half of `TwinOK`, the pin
flag. Mirrors con-ron's `checkReducePin_bridge`:

* the leaves (`reduce_stored_ok`, `reduce_elem_ok`, `reduce_decl_pin`, `reduce_cert_var`, `mk_app`)
  by `StageC.of_leaf`: their `StageR` refinements, the leaves' write set (`LeafClosed`), con-ron's
  `IStepS` (`reduceStoredOk_run`, `reduceElemOk_run`, `reduceDeclPin_run`, `reduceCertVar_run`,
  `Frontend.internE_sstep`);
* `reduce_pin_guard` (`rpgW_okC`): its leaf `reduce_decl_pin` as above, then the walks' `StageT`
  contracts (`IndStubsT.lean`), and `CheckOK` after from con-ron's `reducePinGuard_run`;
* the two `is_def_eq_core` calls by the knot's `StageT` sim and `CheckOK` after from con-ron's
  `KnotSpec.defeq` (`StageC.of_T`).

The opaque arm (`cdo_ref`) carries con-ron's fold invariant `FoldOK` from its entry across the
constant check (`checkConstantVal_bridge_of_fold`) and the value check (`checkOpaqueVal_bridge`),
as con-ron's `checkDecl_bridge_opaque` does; the gate's `CheckOK` at the restricted pushed index
is `CheckOK.congr_find` of it (`restrict_pushed_find`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


noncomputable section

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsF)
open ConRon.Bridge (CheckOK StepOK FoldOK CoreSpec)

local notation "V" => ConLeche.CheckMode.verified

theorem leafA_app : ∀ b ∈ ([AREC, ASLOT, ADER, tier1 AREC, tier1 ASLOT, tier1 ADER] : List TieredArray),
    b ∈ leafA := by
  decide +kernel
theorem leafC_app₀ : (4 : Word) ∈ leafC ∧ (5 : Word) ∈ leafC := by decide +kernel
/-- By cases: `decide +kernel` on the bounded form over `Word` takes >16 GB. -/
theorem leafC_app : ∀ x ∈ ([4, 5] : List Word), x ∈ leafC := by
  intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl
  · exact leafC_app₀.1
  · exact leafC_app₀.2

/-- `mk_app`'s frame is a leaf's. -/
theorem mkAppW_leafFrame {m m' : Mem} {f x r : Word} (h : mkAppW m f x = some (r, m')) :
    MemFrame leafA leafC m m' :=
  (mkAppW_frame m m' f x r h).mono leafA_app leafC_app

/-- `check_opaque_val` is one of the loop's functions. -/
theorem checkOpaqueVal_loop : "check_opaque_val" ∈ loopFns := loop_mem _ rfl

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- `StageC` after a twin run, from `StageT` after it and con-ron's `CheckOK` from the start. -/
theorem rpg_fin {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
    {m : Mem} {a a' : AState} {c : Word} {cn : ConLeche.Name} {x : Bool}
    (hck : CheckOK V env fe a) (hd : denoteN a.store.ns (decI c) = some cn)
    (hrun : (reducePinGuard fe (decI c)).run a = .ok (x, a')) (hT : StageT dn vis fe m a') :
    StageC dn vis fe env m a' ∧ Ext a.store a'.store ∧
      x = ConLeche.reducePinGuard env cn := by
  sorry

-/

/-- **`reduce_pin_guard` under `StageC`** (`reducePinGuard_refines`'s): the pin by
`StageC.of_leaf`, the walks by their `StageT` contracts, `CheckOK` after by con-ron's
`reducePinGuard_run`. -/
theorem rpgW_okC {p : Prog} (hpa : p.lookup "pin_at" = some pinAtL)
    (hpd : p.lookup "reduce_decl_pin" = some reduceDeclPinL) (hR : L.Rom.RomRefs p)
    (hcl : LeafClosed p) (hap : ApdF p) (hck : CrKeep p) {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv}
    {env : ConLeche.Env} {a : AState} {n : Nat} {m m' : Mem} {c : Word} {r : List Word}
    {cn : ConLeche.Name}
    (h : rpgW p (realCall p) n m vis c = some (r, m')) (hS : StageC dn vis fe env m a) (hc : c.toNat < 2 ^ 32)
    (hd : denoteN a.store.ns (decI c) = some cn) (hCr : L.Stubs.CrOK m) :
    ∃ x a', (reducePinGuard fe (decI c)).run a = .ok (x, a') ∧ StageC dn vis fe env m' a' ∧
      Ext a.store a'.store ∧ x = ConLeche.reducePinGuard env cn ∧
      IWGrow m m' ∧ decW0B m' r x := by
  sorry

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`is_def_eq_core`'s twin side**: con-ron's `KnotSpec.defeq` at `checkFuel` (`CoreSpec.of_core`)
gives `CheckOK` and `Ext` after a run from `CheckOK` and the two sides' denotations. -/
theorem defeq_check {env : ConLeche.Env} {fe : IFEnv} {a a' : AState} {d : Nat} {i j : EIdx}
    {x y : ConLeche.Expr} {b : Bool} (henv : ConLeche.EnvWF env) (hck : CheckOK V env fe a)
    (hi : denoteE a.store i = some x) (hj : denoteE a.store j = some y)
    (hwx : ConLeche.Expr.WScoped d x) (hwy : ConLeche.Expr.WScoped d y)
    (hrun : (isDefEqCore V fe checkFuel d i j).run a = .ok (b, a')) :
    CheckOK V env fe a' ∧ Ext a.store a'.store ∧ a'.pins = a.pins ∧
      ConRon.Bridge.Core.SimV (ConLeche.isDefEqCore V env) d x y b := by
  sorry

-/

/-- What `check_reduce_pin` gives besides the twin's run (from `m`): the stage relation at the
pushed view `vis2`, `StageC` at the pre-insertion view `vis`, the growth. -/
structure CrpPost (dn : NIdx → Option ConLeche.Name) (vis vis2 : Word) (fe2 : IFEnv)
    (env : ConLeche.Env) (m m' : Mem) (a' : AState) : Prop where
  stage2 : StageR vis2 fe2 m' a'
  grow : IWGrow m m'

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`check_reduce_pin` refines `checkReducePin`, both outcomes** (con-ron's
`checkReducePin_bridge`'s decomposition): from the stage relation at the pushed view `vis2`,
con-ron's `CheckOK` at the pre-insertion view `vis` of the index (at `env`, the environment before
the push), the pushed index's `StepOK` (at `env2`), the memory's half of `TwinOK`, the pin flag, the
name's and the value's denotations. The three guards and the spelling test decline; the identity
certificate failing is the twin's `internal` (class `0`); `is_def_eq_core`'s errors are the core
stub's claims. -/
@[refines ConRon.Arena.checkReducePin]
theorem crp_ref {p : Prog} (hC : CrpProg p) (hq : KnotStageProg p) (hcl : LeafClosed p)
    (hkp : CrKeep p) {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn) {vis vis2 : Word}
    {fe2 : IFEnv} {env env2 : ConLeche.Env} {a : AState} {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem}
    {c v : Word} {nm : ConLeche.Name} {x : ConLeche.Expr}
    (hS : StageR vis2 fe2 m a)
    (hck : CheckOK V env (fe2.restrictTo vis.toNat) a) (henv : ConLeche.EnvWF env)
    (hok2 : StepOK env2 fe2 a) (hmem : TwinMem dn m a) (hflag : pinW m 0 ≠ 0)
    (hnm : denoteN a.store.ns (decI c) = some nm) (hvx : denoteE a.store (decI v) = some x)
    (hws : ConLeche.Expr.WScoped 0 x) (hc : c.toNat < 2 ^ 32) (hv : v.toNat < 2 ^ 32)
    (hCr : L.Stubs.CrOK m) :
    RefE (CoreStubsE p) (checkReducePinE p n m vis vis2 c v)
      (checkReducePin V (fe2.restrictTo vis.toNat) fe2 (decI c) (decI v)) a
      (fun w _ a' => CrpPost dn vis vis2 fe2 env m w.2 a') := by
  sorry

-/

set_option experimental.vcgen true in
/-- **The model of `check_decl_opaque`, both outcomes**: its callees through their runs. -/
l_model checkDeclOpaque_specE (p : Prog)
  (hf : p.lookup "check_decl_opaque" = some checkDeclOpaque)
  fns [hf ↦ checkDeclOpaqueE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specT, ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **The opaque arm refines `checkDecl`, both outcomes**, under `StageT` (con-ron's
`checkDecl_bridge_opaque`): the constant check and the value check (`ccv_ref`, `ov_ref`), then for
`Lean.reduceNat`/`Lean.reduceBool` the reduce-pin gate under `StageC` (`crp_ref`) at the
pre-insertion view (con-ron's `CheckOK`, restricted, and the memory's half: the call's frame by
`LoopClosed`, the core memos by `ov_ref`). From the fold invariant `FoldOK` at the arm's entry and
the declaration's constant and value denoting. -/
theorem cdo_ref {p : Prog} (hV : ValProg p) (hC : CrpProg p) (hq : KnotStageProg p)
    (hcl : LeafClosed p) (hlc : LoopClosed p) (hap : ApdF p) (hkp : CrKeep p)
    {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn)
    {vis : Word} {fe : IFEnv} {env : ConLeche.Env} {a : AState} (n : Nat) (hn : n ≤ 2 ^ 62)
    {m : Mem} {i : Word} {ds : Array IDeclaration} {pins : List INatOpPinSet}
    {cv : IConstantVal} {v : EIdx} {c : ConLeche.ConstantVal} {x : ConLeche.Expr}
    (hS : StageT dn vis fe m a)
    (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds) (hi : i.toNat < ds.size)
    (hd : ds[i.toNat] = .opaqueDecl cv v) (hfold : FoldOK V env fe a)
    (hcvd : Frontend.denoteCV a.store cv = some c) (hvd : denoteE a.store v = some x)
    (hCr : L.Stubs.CrOK m) :
    RefE (CdtCtx p) (checkDeclOpaqueE p n m i vis) (checkDecl V pins fe (.opaqueDecl cv v)) a
      (fun w y a' => ArmPost dn m w.1 w.2 y a') := by
  sorry

-/

end L.Arena
