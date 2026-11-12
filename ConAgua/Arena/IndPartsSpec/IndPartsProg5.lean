module

public import ConAgua.Arena.IndPartsSpec.Bsp
public import ConAgua.Arena.IndCallM
public import ConAgua.Arena.IndPartsSpec.BlockRecNameSetOk
public import ConAgua.Arena.IndPartsSpec.BmoW
public import ConAgua.Arena.IndPartsSpec.BpcW
public import ConAgua.Arena.IndPartsSpec.BsoK2
public import ConAgua.Arena.IndSumSpec.ColW
import ConAgua.Arena.IndSumSpec.Row
import ConAgua.L.ModelGen
import all ConAgua.Arena.IndParts

@[expose] public section

/-!
# IndPartsProg5

`IndPartsProg5`, the models of `block_shape_fin` and `block_shape_tail`.
-/

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **The program bundle of `readBlock`.** -/
structure IndPartsProg5 (p : Prog) : Prop extends IndPartsProg4 p where
  erCopy : p.lookup "er_copy" = some erCopy
  erToIw : p.lookup "er_to_iw" = some erToIw
  slEq : p.lookup "sl_eq" = some slEq
  slGetD : p.lookup "sl_getd" = some slGetD
  pinWord : p.lookup "pin_word" = some pinWordL
  rec4 : p.lookup "rec4" = some rec4
  rec7 : p.lookup "rec7" = some rec7
  slGet : p.lookup "sl_get" = some slGet
  paramFind : p.lookup "param_find" = some paramFind
  paramPush : p.lookup "param_push" = some paramPush
  internParam : p.lookup "intern_param" = some internParam
  plGo : p.lookup "param_levels_go" = some paramLevelsGoL
  pl : p.lookup "param_levels" = some paramLevelsL
  il : IlF p
  namesOf : p.lookup "block_shape_names_of" = some blockShapeNamesOf
  flo : p.lookup "formers_lps_ok" = some formersLpsOk
  cpo : p.lookup "ctors_params_ok" = some ctorsParamsOk
  clo : p.lookup "ctors_lps_ok" = some ctorsLpsOk
  sort : p.lookup "block_shape_result_sort" = some blockShapeResultSort
  ctorsOf : p.lookup "block_shape_ctors_of" = some blockShapeCtorsOf
  membersOf : p.lookup "block_shape_members_of" = some blockShapeMembersOf
  recsOf : p.lookup "block_shape_recs_of" = some blockShapeRecsOf
  large : p.lookup "block_shape_large" = some blockShapeLarge
  pack : p.lookup "block_shape_pack" = some blockShapePack
  sealF : p.lookup "block_shape_seal" = some blockShapeSeal
  fin : p.lookup "block_shape_fin" = some blockShapeFin
  tail : p.lookup "block_shape_tail" = some blockShapeTail
  readAt : p.lookup "read_block_at" = some readBlockAt
  read : p.lookup "read_block" = some readBlock
  na : NaF p

/-- **The model of `block_shape_fin`** (at exec fuel `n + 2`). -/
l_model bf_spec (p : Prog) (hP : IndPartsProg5 p)
  fns [hP.fin ↦ bfW list]
  specs [bct_spec p hP.alloc hP.copy hP.cons hP.rec2 hP.ctorsOf (n + 1),
      plW_spec p hP.alloc hP.copy hP.cons hP.slGet hP.paramFind hP.paramPush hP.internParam hP.plGo hP.pl hP.il (n + 1),
      bg_spec p hP.toIndPartsProg hP.view hP.find hP.midx hP.cmem hP.gone hP.rec2 hP.ggo hP.groups n,
      bmo_spec p hP.alloc hP.copy hP.cons hP.rec5 hP.membersOf (n + 1),
      brs_spec p hP.toIndPartsProg4 hP.rec7 hP.recsOf (n + 1),
      bsl_spec p hP.toIndPartsProg4 hP.erCopy hP.erToIw hP.slEq hP.large (n + 1),
      bseal_spec p hP.na hP.alloc hP.pack hP.sealF (n + 1)]
  grind [arena_grind, ind_grind] pfuel 2

/-- **The model of `block_shape_tail`** (at exec fuel `n + 3`). -/
l_model bt_spec (p : Prog) (hP : IndPartsProg5 p) (c : CallM) (hc : CallSpec p c)
  fns [hP.tail ↦ btW list]
  specs [bso_spec p hP.view hP.pinWord hP.slGetD hP.sort hP.strip (n + 2), pinWord_specV p hP.pinWord (n + 2),
      hc (n + 2) "lvl_eq_c", bf_spec p hP n]
  grind [arena_grind, ind_grind] fold [erRd] pfuel 3

end L.Ind

end

end
