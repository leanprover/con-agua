module

public import ConAgua.Arena.DeclReduceSpec2
import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.DeclReduceSpec
import all ConAgua.Arena.DeclArms

@[expose] public section

/-!
# The models of the reduce-pin gate (`check_reduce_pin`, `check_reduce_pin_pre`)

The `Lean.reduceNat`/`Lean.reduceBool` install gate (con-ron's `checkReducePin`): the opaque's
record pushed for one read (`reduce_stored_ok` at the pushed view) and popped (`env_pop_temp`),
then at the popped view (`check_reduce_pin_pre`) the element inductive, the pin's guards
(`reduce_pin_guard`), the value against the pin and the identity certificate, both through
`is_def_eq_core`. The refinements are in `DeclCrpT.lean`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

noncomputable section

namespace L.Arena

open L.Ind

/-- The lookups of the reduce-pin gate. -/
structure CrpProg (p : Prog) : Prop where
  red : RedProg p
  rcv : RcvProg p
  crp : p.lookup "check_reduce_pin" = some checkReducePinL
  crpp : p.lookup "check_reduce_pin_pre" = some checkReducePinPreL
  rpg : p.lookup "reduce_pin_guard" = some reducePinGuardL
  rdp : p.lookup "reduce_decl_pin" = some reduceDeclPinL
  db : p.lookup "der_b" = some derB
  af : p.lookup "app_find" = some appFind
  ap : p.lookup "app_push" = some appPush
  ia : p.lookup "intern_app" = some internApp
  ma : p.lookup "mk_app" = some mkApp
  bvb : BvbProg p
  hf : HfF p
  push : p.lookup "env_push" = some envPushL
  pop : p.lookup "env_pop_temp" = some envPopTempL
  rs : p.lookup "env_row_set" = some envRowSetL
  /-- `reduce_op_cv_a` leaves the own rows alone (the pop after `reduce_stored_ok`). -/
  rcva : RcvaClosed p

set_option experimental.vcgen true in
/-- **The model of `reduce_pin_guard(vis, c)`, both outcomes**: the pin through its run, the two
walks through their `Option` models, the gates through `callE`. -/
l_model reducePinGuard_specE (p : Prog) (hC : CrpProg p)
  fns [hC.rpg ↦ reducePinGuardE]
  specs [callW_spec p n "reduce_decl_pin", lbbF_spec p hC.bvb n, hffF_spec p hC.hf n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

set_option experimental.vcgen true in
/-- **The model of `check_reduce_pin_pre(vis, c, v)`, both outcomes**: the leaves through their
runs, `reduce_pin_guard` by its unified model, `is_def_eq_core` through `callE`. -/
l_model checkReducePinPre_specE (p : Prog) (hC : CrpProg p)
  fns [hC.crpp ↦ checkReducePinPreE]
  specs [callW_spec p n "reduce_elem_ok", reducePinGuard_specE p hC n,
    callW_spec p n "reduce_decl_pin", callW_spec p n "reduce_cert_var", callW_spec p n "mk_app"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

set_option experimental.vcgen true in
/-- **The model of `check_reduce_pin(vis, p, c, v)`, both outcomes**: the push, the stored
constant's read and the pop through their runs, `check_reduce_pin_pre` by its unified model. -/
l_model checkReducePin_specE (p : Prog) (hC : CrpProg p)
  fns [hC.crp ↦ checkReducePinE]
  specs [callW_spec p n "env_row_get", callW_spec p n "env_push", callW_spec p n "reduce_stored_ok",
    callW_spec p n "env_pop_temp", checkReducePinPre_specE p hC n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

end L.Arena

end
