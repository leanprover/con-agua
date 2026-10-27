import ConAgua.Arena.IndPosSpec.EnvFindWHit
import ConAgua.Arena.IndPosSpec.FgW2
import ConAgua.Arena.IndPosSpec.NtyLook
import ConAgua.Arena.IndPosSpec.U4W
import ConAgua.Arena.IndRealNames

/-!
# NbLook

`NbLook`.
-/


/-! # `IndPos2`, the `nestPos` block (lane `indproofs2`, helper `pos2`): the L side — every
function of the block refines its word model, by one induction on the exec fuel. -/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The lookups of the `nestPos` block (and its leaves). -/
structure NbLook (p : Prog) : Prop where
  hi1 : I1Prog p
  ab : AbF p
  na : NaF p
  ct : CtLook p
  nit : NitLook p
  nag : NagLook p
  dc : DcLook p
  fm : FmLook p
  nt : NtLook p
  pf : PfLook p
  usl : UslLook p
  h3 : p.lookup "rec3" = some rec3
  h6 : p.lookup "rec6" = some rec6
  hap : p.lookup "sl_append" = some slAppend
  hn1 : p.lookup "sl_new1" = some slNew1
  hfg : p.lookup "nest_frame_grp" = some nestFrameGrpL
  hgc : p.lookup "nest_group_ctors" = some nestGroupCtorsL
  hfh : p.lookup "nest_frame_holes" = some nestFrameHolesL
  hgg : p.lookup "nest_grow_group" = some nestGrowGroupL
  hca : p.lookup "nest_cont_new_active" = some nestContNewActiveL
  hcf : p.lookup "nest_cont_new_finish" = some nestContNewFinishL
  hpc : p.lookup "nest_cont_params_closed" = some nestContParamsClosedL
  hcc : p.lookup "nest_cont_checks" = some nestContChecksL
  hpa : p.lookup "pin_at" = some pinAtL
  hws : p.lookup "nest_walk_stack" = some nestWalkStackL
  hrh : p.lookup "nest_res_head" = some nestResHeadL
  hro : p.lookup "nest_ctors_res_ok" = some nestCtorsResOkL
  hu4 : p.lookup "nest_ctors_u4" = some nestCtorsU4L
  hnf : p.lookup "nest_ctor_nf" = some nestCtorNfL
  hcl : p.lookup "close_telescope" = some closeTelescope
  hdf : p.lookup "dp_find" = some (memoFindG dpSch)
  hdp : p.lookup "dp_put" = some (memoPutG dpSch)
  hdg : p.lookup "depth_go" = some depthGo
  hdn : p.lookup "depth_node" = some depthNode
  hdc : p.lookup "dp_clear" = some (memoClearG dpSch)
  hdd : p.lookup "depth" = some depth
  hwf : p.lookup "whnf_walk_fuel" = some whnfWalkFuel
  pfields : p.lookup "nest_fields" = some nestFieldsL
  pwalk : p.lookup "nest_ctors_walk" = some nestCtorsWalkL
  pone : p.lookup "nest_ctors_one" = some nestCtorsOneL
  pctors : p.lookup "nest_ctors" = some nestCtorsL
  pframe : p.lookup "nest_frame" = some nestFrameL
  pnew : p.lookup "nest_cont_new" = some nestContNewL
  pkey : p.lookup "nest_cont_key" = some nestContKeyL
  pcont : p.lookup "nest_cont" = some nestContL
  papp : p.lookup "nest_pos_app" = some nestPosAppL
  pbind : p.lookup "nest_pos_bind" = some nestPosBindL
  ppos : p.lookup "nest_pos" = some nestPosL

end L.Ind

end
