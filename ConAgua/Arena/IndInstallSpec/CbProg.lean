import ConAgua.Arena.IndInstallSpec.GrcProg
import ConAgua.Arena.IndInstallSpec.IagW
import ConAgua.Arena.IndInstallSpec.Pos3Init
import ConAgua.Arena.IndSumSpec.ConsBlockRecsTF
import ConAgua.Arena.RecGenSpec.ClassSeeds
import ConAgua.Arena.RecGenSpec.Classes
import ConAgua.Arena.RecGenSpec.OcW

/-!
# CbProg

`IndsProg`, `PassProg`, `CbProg`.
-/

section

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- The lookups of stage 1. -/
structure IndsProg (p : Prog) : Prop extends InstProg p, ConsIndsProg p where
  agreeP : AgreeProg p
  pinWord : p.lookup "pin_word" = some pinWordL
  withSort : p.lookup "block_shape_with_sort" = some blockShapeWithSort
  cvTas : p.lookup "check_block_inds_cv_tas" = some checkBlockIndsCvTas
  cvTasGo : p.lookup "check_block_inds_cv_tas_go" = some checkBlockIndsCvTasGo
  inds : p.lookup "check_block_inds" = some checkBlockInds

end L.Ind

end

end

section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `check_block_pass` -/

/-- The lookups of `check_block_pass`. -/
structure PassProg (p : Prog) : Prop where
  inds : IndsProg p
  flush : FlushProg p
  ctors : CtorsProg p
  nck : NckProg p
  nhl : NhLook p
  bnc : p.lookup "block_nest_ctx" = some blockNestCtx
  cbc : CbcProg p
  pos : PosBlkProg p
  sds : SdProg p
  rs : RsLook p
  ha : p.lookup "iw_alloc" = some iwAlloc
  prec : p.lookup "check_block_pass_rec" = some checkBlockPassRec
  pass : p.lookup "check_block_pass" = some checkBlockPass

end L.Ind

end

section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- The lookups of `check_block`. -/
structure CbProg (p : Prog) : Prop where
  pass : PassProg p
  tail : TailProg p
  cbr : CbrLook p
  ma : MaProg p
  ha : p.lookup "iw_alloc" = some iwAlloc
  cp : p.lookup "iw_copy" = some iwCopy
  nco : p.lookup "num_ctors_of" = some numCtorsOf
  acc : p.lookup "block_shape_ctors_copy" = some blockShapeCtorsCopy
  acg : p.lookup "block_shape_all_ctors_go" = some blockShapeAllCtorsGo
  ac : p.lookup "block_shape_all_ctors" = some blockShapeAllCtors
  mnc : p.lookup "member_names_copy" = some memberNamesCopy
  bccn : p.lookup "block_caps_ctor_names" = some blockCapsCtorNames
  bsmn : p.lookup "block_shape_member_names" = some blockShapeMemberNames
  slc : p.lookup "sl_contains" = some slContains
  nodup : p.lookup "sl_nodup" = some slNodup
  pdm : p.lookup "pi_doms_mention_any" = some piDomsMentionAny
  brm : p.lookup "block_raw_rec_member" = some blockRawRecMember
  brg : p.lookup "block_raw_rec_go" = some blockRawRecGo
  brr : p.lookup "block_raw_rec" = some blockRawRec
  cb : p.lookup "check_block" = some checkBlock

end L.Ind

end
