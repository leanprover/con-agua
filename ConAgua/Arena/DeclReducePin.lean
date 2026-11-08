module

public import ConAgua.Arena.DeclReduceSpec2
public import ConAgua.Arena.IndRealApdT
import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.DeclReduceSpec
import all ConAgua.Arena.DeclArms

@[expose] public section

/-!
# `check_reduce_pin(vis, vis2, c, v)` refines `checkReducePin` (lane `decls3`)

The `Lean.reduceNat`/`Lean.reduceBool` install gate, after the opaque's push: the stored constant
at the pushed view `vis2` (`reduce_stored_ok`), then at the pre-insertion view `vis` the element
inductive, the pin's guards, the value against the pin, and the identity certificate. The stage
relation at `vis2` gives it at `vis` (`fe2.restrictTo vis`: the same index, `EnvR.restrictTo`) and
back. L change: a handle guard after `reduce_cert_var` (`is_def_eq_core`'s spec needs it).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Ind

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- The stage relation at another view of the same environment. -/
theorem StageR.restrict {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (h : StageR vis fe m a) (k : Word) :
    StageR k (fe.restrictTo k.toNat) m a :=
  ⟨⟨h.check.arena, h.check.core, h.check.pins, h.check.env.restrictTo k, h.check.mode⟩, h.iw⟩
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem IFEnv.restrictTo_restrictTo (fe : IFEnv) (j k : Nat) :
    (fe.restrictTo j).restrictTo k = fe.restrictTo k := rfl
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
theorem IFEnv.restrictTo_self (fe : IFEnv) : fe.restrictTo fe.visibleBelow = fe := rfl
-/

/-! ## The model -/

/-- The lookups of `check_reduce_pin`. -/
structure CrpProg (p : Prog) : Prop where
  red : RedProg p
  rcv : RcvProg p
  crp : p.lookup "check_reduce_pin" = some checkReducePinL
  rpg : p.lookup "reduce_pin_guard" = some reducePinGuardL
  rdp : p.lookup "reduce_decl_pin" = some reduceDeclPinL
  db : p.lookup "der_b" = some derB
  af : p.lookup "app_find" = some appFind
  ap : p.lookup "app_push" = some appPush
  ia : p.lookup "intern_app" = some internApp
  ma : p.lookup "mk_app" = some mkApp
  bvb : BvbProg p
  hf : HfF p
  /-- `all_level_params_defined`'s program (`reduce_pin_guard` under `StageT`, `DeclCrpT.lean`). -/
  apd : L.Ind.ApdF p

/-- **The model of `check_reduce_pin(vis, vis2, c, v)`, both outcomes**: the leaves outside
the verdict closure lifted, `is_def_eq_core` through its run (its errors are the core stub's
claims). -/
l_model checkReducePin_specE (p : Prog) (hC : CrpProg p)
  fns [hC.crp ↦ checkReducePinE]
  specs [callW_spec p n "reduce_stored_ok", callW_spec p n "reduce_elem_ok",
    callW_spec p n "reduce_pin_guard", callW_spec p n "reduce_decl_pin",
    callW_spec p n "reduce_cert_var", mkApp_spec p hC.db hC.af hC.ap hC.ia hC.ma n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]


local notation "V" => ConLeche.CheckMode.verified

end L.Arena
