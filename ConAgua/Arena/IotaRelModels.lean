module

public import ConAgua.Arena.IotaRel
public import ConAgua.Arena.WhnfBase
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.Verdict
public import Std.WP.Tactic
import all ConAgua.Arena.IotaRel

@[expose] public section

/-!
# The ι reading rule, part 2: the generated models (lane ronsync8)

One `l_model` per function of `IotaRel.lean`, every callee through its run (`callW`); the
recursions of `expr_lvl_eq` and `ann_eq` are calls through their runs too (the twin's fuel is an
argument of the L function).
-/

open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

l_model exprLvlEq_specW (p : Prog) (hf : p.lookup "expr_lvl_eq" = some exprLvlEqL)
  fns [hf ↦ exprLvlEqW list]
  specs [callW_spec p n "e_view", callW_spec p n "lvl_eq", callW_spec p n "lvls_eq"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model nameOptParam_specW (p : Prog) (hf : p.lookup "name_opt_param" = some nameOptParamL)
  fns [hf ↦ nameOptParamW list]
  specs [callW_spec p n "intern_nanon", callW_spec p n "pool_room", callW_spec p n "intern_nstr"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model nameAutoParam_specW (p : Prog) (hf : p.lookup "name_auto_param" = some nameAutoParamL)
  fns [hf ↦ nameAutoParamW list]
  specs [callW_spec p n "intern_nanon", callW_spec p n "pool_room", callW_spec p n "intern_nstr"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model nameOutParam_specW (p : Prog) (hf : p.lookup "name_out_param" = some nameOutParamL)
  fns [hf ↦ nameOutParamW list]
  specs [callW_spec p n "intern_nanon", callW_spec p n "pool_room", callW_spec p n "intern_nstr"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model nameSemiOutParam_specW (p : Prog) (hf : p.lookup "name_semi_out_param" = some nameSemiOutParamL)
  fns [hf ↦ nameSemiOutParamW list]
  specs [callW_spec p n "intern_nanon", callW_spec p n "pool_room", callW_spec p n "intern_nstr"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model nameMissing_specW (p : Prog) (hf : p.lookup "name_missing" = some nameMissingL)
  fns [hf ↦ nameMissingW list]
  specs [callW_spec p n "pool_room", callW_spec p n "intern_nstr"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model annWitness_specW (p : Prog) (hf : p.lookup "ann_witness" = some annWitnessL)
  fns [hf ↦ annWitnessW list]
  specs [callW_spec p n "e_view", callW_spec p n "view_ls_len", callW_spec p n "name_missing", callW_spec p n "env_find"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model annIdentBody_specW (p : Prog) (hf : p.lookup "ann_ident_body" = some annIdentBodyL)
  fns [hf ↦ annIdentBodyW list]
  specs [callW_spec p n "e_view", callW_spec p n "intern_bvar", callW_spec p n "ann_witness"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model annIdentVal_specW (p : Prog) (hf : p.lookup "ann_ident_val" = some annIdentValL)
  fns [hf ↦ annIdentValW list]
  specs [callW_spec p n "e_view", callW_spec p n "lv_node", callW_spec p n "ann_ident_body"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model annIdent_specW (p : Prog) (hf : p.lookup "ann_ident" = some annIdentL)
  fns [hf ↦ annIdentW list]
  specs [callW_spec p n "env_find", callW_spec p n "ann_ident_val"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model annEq_specW (p : Prog) (hf : p.lookup "ann_eq" = some annEqL)
  fns [hf ↦ annEqW list]
  specs [callW_spec p n "expr_lvl_eq", callW_spec p n "e_view", callW_spec p n "view_ls_len", callW_spec p n "name_opt_param", callW_spec p n "name_auto_param", callW_spec p n "name_out_param", callW_spec p n "name_semi_out_param", callW_spec p n "ann_ident"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model listLvlEq_specW (p : Prog) (hf : p.lookup "list_lvl_eq" = some listLvlEqL)
  fns [hf ↦ listLvlEqW list]
  specs [callW_spec p n "expr_lvl_eq"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model listAnnEq_specW (p : Prog) (hf : p.lookup "list_ann_eq" = some listAnnEqL)
  fns [hf ↦ listAnnEqW list]
  specs [callW_spec p n "ann_eq"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model paramsAnnEq_specW (p : Prog) (hf : p.lookup "params_ann_eq" = some paramsAnnEqL)
  fns [hf ↦ paramsAnnEqW list]
  specs [callW_spec p n "strip_pis", callW_spec p n "list_ann_eq"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model iotaPartsRel_specW (p : Prog) (hf : p.lookup "iota_parts_rel" = some iotaPartsRelL)
  fns [hf ↦ iotaPartsRelW list]
  specs [callW_spec p n "sl_eq", callW_spec p n "list_lvl_eq", callW_spec p n "params_ann_eq", callW_spec p n "list_ann_eq"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model ruleReads_specW (p : Prog) (hf : p.lookup "rule_reads" = some ruleReadsL)
  fns [hf ↦ ruleReadsW list]
  specs [callW_spec p n "iota_parts_of_at", callW_spec p n "env_find", callW_spec p n "iota_parts_at", callW_spec p n "iota_parts_rel"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model rulesRead_specW (p : Prog) (hf : p.lookup "rules_read" = some rulesReadL)
  fns [hf ↦ rulesReadW list]
  specs [callW_spec p n "rule_reads"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model recReads_specW (p : Prog) (hf : p.lookup "rec_reads" = some recReadsL)
  fns [hf ↦ recReadsW list]
  specs [callW_spec p n "iota_rec_of", callW_spec p n "rules_read"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model recsRead_specW (p : Prog) (hf : p.lookup "recs_read" = some recsReadL)
  fns [hf ↦ recsReadW list]
  specs [callW_spec p n "rec_reads"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model blockReadsAt_specW (p : Prog) (hf : p.lookup "block_reads_at" = some blockReadsAtL)
  fns [hf ↦ blockReadsAtW list]
  specs [callW_spec p n "block_constants", callW_spec p n "block_recs", callW_spec p n "cons_block_recs_temp", callW_spec p n "recs_read", callW_spec p n "gen_rec_check_pop_all", callW_spec p n "env_set_flags"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

end L.Ind
