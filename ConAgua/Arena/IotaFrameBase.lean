module

public import ConAgua.Arena.IotaFrameModels
public import ConAgua.Arena.StripTeleSpec
public import ConAgua.Arena.IndPartsSpec.IndPartsProg2
public import ConAgua.Arena.IndRealSpine
public import ConAgua.Arena.RecClass
public import ConAgua.Arena.IndDeclConstsDrop
public import ConAgua.Arena.IndRealFvt

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

end L.Ind
