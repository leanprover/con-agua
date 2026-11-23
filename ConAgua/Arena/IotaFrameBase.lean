module

public import ConAgua.Arena.IotaFrameModels
public import ConAgua.Arena.StripTeleSpec
public import ConAgua.Arena.IndPartsSpec.IndPartsProg2
public import ConAgua.Arena.IndRealSpine
public import ConAgua.Arena.RecClass
public import ConAgua.Arena.IndDeclConstsDrop
public import ConAgua.Arena.IndRealFvt
public import ConAgua.Arena.IndRealAbs
public import ConAgua.Arena.IndRealMemo

@[expose] public section

/-!
# The ι reading rule, part 1: the program bundle of the refinements (lane ronsync8)

`IotaFrameProg` names what the phase-1 refinements (`IotaFrame*.lean`) need of a program; it gains
fields as the proofs land (callers only pass it on). The refinements of the three entries phase 2
calls are `IotaFrameIface.lean`'s.
-/

open ConRon.Arena

namespace L.Ind

open L.Arena

/-- The arrays the reading functions `iota_rec_of`, `iota_parts_of_at` may write (both tiers): all but
the walk memos `AbsOK` reads (`memoFreeA`). -/
def iotaRA : List TieredArray := checkerWordArrays.filter fun b => memoFreeA [b]

/-- The `CTL` words they may write: all but the memos' epoch words (`memoFreeC`). -/
def iotaRC : List Word := ((List.range 1024).map UInt64.ofNat).filter fun x => memoFreeC [x]

/-- The call closure of `iota_rec_of` and `iota_parts_of_at` (computed from the program's call
graph); `IotaFrameProg.rclosed` says it writes only `iotaRA`, `iotaRC`, so the walk memos are kept
(`iota_afr`). -/
def iotaRFns : List FnName :=
  ["app_count", "app_fill", "app_find", "app_push", "bvar_find", "bvar_push", "der_b", "der_bv",
   "e_view", "expr_drop_vars", "expr_drop_vars_list", "expr_get_d", "forall_find", "forall_push",
   "get_app_args", "get_app_args_f", "get_app_fn", "get_app_fn_f", "if_clear", "if_find", "if_put",
   "inst_app", "inst_entry", "inst_forall", "inst_go", "inst_lam", "inst_let", "inst_proj",
   "instantiate1_fast", "intern_app", "intern_bvar", "intern_forall", "intern_lam", "intern_letE",
   "intern_proj", "intern_sort", "iota_frame", "iota_parts_of_at", "iota_read_major",
   "iota_rec_of", "is_minor_at", "iw_alloc", "iw_copy", "lam_find", "lam_push", "letE_find",
   "letE_push", "lf_clear", "lf_find", "lf_put", "lift_app", "lift_entry", "lift_field_doms",
   "lift_forall", "lift_go", "lift_idx_args", "lift_lam", "lift_let", "lift_proj", "minors_from",
   "mk_app", "mk_forall", "mk_lam", "mk_let", "mk_proj", "motive_level", "pi_result",
   "pi_result_f", "pi_tele", "pin_word", "proj_find", "proj_push", "sl_cons", "sort_find",
   "sort_push", "spn_to_iw", "strip_pis"]

/-- What the phase-1 refinements need of a program. -/
structure IotaFrameProg (p : Prog) : Prop where
  pi_tele : p.lookup "pi_tele" = some piTeleL
  motive_level : p.lookup "motive_level" = some motiveLevelL
  iota_frame : p.lookup "iota_frame" = some iotaFrameL
  is_minor_at : p.lookup "is_minor_at" = some isMinorAtL
  minors_from : p.lookup "minors_from" = some minorsFromL
  iota_read_major : p.lookup "iota_read_major" = some iotaReadMajorL
  iota_rec_of : p.lookup "iota_rec_of" = some iotaRecOfL
  lift_field_doms : p.lookup "lift_field_doms" = some liftFieldDomsL
  lift_idx_args : p.lookup "lift_idx_args" = some liftIdxArgsL
  iota_parts_of_at : p.lookup "iota_parts_of_at" = some iotaPartsOfAtL
  ctor_levels_at : p.lookup "ctor_levels_at" = some ctorLevelsAtL
  iota_bvars : p.lookup "iota_bvars" = some iotaBVarsL
  iota_params_at : p.lookup "iota_params_at" = some iotaParamsAtL
  iota_parts_at_body : p.lookup "iota_parts_at_body" = some iotaPartsAtBodyL
  iota_parts_at : p.lookup "iota_parts_at" = some iotaPartsAtL
  e_view : p.lookup "e_view" = some eView
  gaf : GafF p
  pir : PirF p
  bvar_find : p.lookup "bvar_find" = some bvarFind
  bvar_push : p.lookup "bvar_push" = some bvarPush
  intern_bvar : p.lookup "intern_bvar" = some internBVar
  expr_get_d : p.lookup "expr_get_d" = some exprGetD
  strip : StripProg p
  lift : LiftProg p
  lift_entry : p.lookup "lift_entry" = some liftEntry
  drop : DropProg p
  gaa : GaaF p
  i1l : I1lF p
  er_copy : p.lookup "er_copy" = some erCopy
  er_to_iw : p.lookup "er_to_iw" = some erToIw
  il : IlF p
  iw_copy : p.lookup "iw_copy" = some iwCopy
  sl_cons : p.lookup "sl_cons" = some slCons
  sl_get : p.lookup "sl_get" = some slGet
  param_find : p.lookup "param_find" = some paramFind
  param_push : p.lookup "param_push" = some paramPush
  intern_param : p.lookup "intern_param" = some internParam
  param_levels_go : p.lookup "param_levels_go" = some paramLevelsGoL
  param_levels : p.lookup "param_levels" = some paramLevelsL
  /-- The reading functions' write set: no walk memo (decided on the concrete program). -/
  rclosed : closedA p iotaRA iotaRC iotaRFns = true

theorem iotaRA_free : memoFreeA iotaRA = true := by
  unfold iotaRA memoFreeA; rw [List.all_eq_true]; intro x hx
  have := (List.mem_filter.mp hx).2; simpa [memoFreeA] using this

theorem iotaRC_free : memoFreeC iotaRC = true := by
  unfold iotaRC memoFreeC; rw [List.all_eq_true]; intro x hx
  have := (List.mem_filter.mp hx).2; simpa [memoFreeC] using this

/-- **A call of a reading function keeps the walk memos** (its write set). -/
theorem iota_afr {p : Prog} (P : IotaFrameProg p) {f : FnName} (hf : f ∈ iotaRFns) {n : Nat}
    {args r : List Word} {m m' : Mem} (hc : callW p n f args m = some (r, m')) : AFr m m' :=
  AFr.of_frame (run_memFrame P.rclosed hf (run_of_callW hc)).1 iotaRA_free iotaRC_free

end L.Ind
