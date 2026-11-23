module

public import ConAgua.Arena.Needs
public import ConAgua.Arena.WhnfBase
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.Verdict
public import Std.WP.Tactic
import all ConAgua.Arena.Needs

@[expose] public section

/-!
# What a record reads, in L: the generated models (lane compare, helper H1)

One `l_model` per function of `Needs.lean`, every callee through its run (`callW`); `needs_go`'s
recursion is its own model at the fuel below (the twin's fuel is the L function's first argument).
-/

open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Ind L.Stubs

l_model needsReset_specW (p : Prog) (hf : p.lookup "needs_reset" = some needsResetL)
  fns [hf ↦ needsResetW list]
  specs [callW_spec p n "nd_clear"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model needsName_specW (p : Prog) (hf : p.lookup "needs_name" = some needsNameL)
  fns [hf ↦ needsNameW list]
  specs []
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model needsNames_specW (p : Prog) (hf : p.lookup "needs_names" = some needsNamesL)
  fns [hf ↦ needsNamesW list]
  specs [callW_spec p n "needs_name"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model needsNamesIw_specW (p : Prog) (hf : p.lookup "needs_names_iw" = some needsNamesIwL)
  fns [hf ↦ needsNamesIwW list]
  specs [callW_spec p n "needs_name"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model litNeeds_specW (p : Prog) (hf : p.lookup "lit_needs" = some litNeedsL)
  fns [hf ↦ litNeedsW list]
  specs [callW_spec p n "pin_at", callW_spec p n "needs_name"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model needsGo_specW (p : Prog) (hf : p.lookup "needs_go" = some needsGoL)
  fns [hf ↦ needsGoW list]
  specs [callW_spec p n "e_view", callW_spec p n "lit_needs", callW_spec p n "needs_name",
    callW_spec p n "nd_find", callW_spec p n "nd_put"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model needsExpr_specW (p : Prog) (hf : p.lookup "needs_expr" = some needsExprL)
  fns [hf ↦ needsExprW list]
  specs [callW_spec p n "needs_go"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model needsExprs_specW (p : Prog) (hf : p.lookup "needs_exprs" = some needsExprsL)
  fns [hf ↦ needsExprsW list]
  specs [callW_spec p n "needs_expr"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model needsRule_specW (p : Prog) (hf : p.lookup "needs_rule" = some needsRuleL)
  fns [hf ↦ needsRuleW list]
  specs [callW_spec p n "needs_expr", callW_spec p n "needs_name", callW_spec p n "needs_exprs"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model needsRules_specW (p : Prog) (hf : p.lookup "needs_rules" = some needsRulesL)
  fns [hf ↦ needsRulesW list]
  specs [callW_spec p n "needs_rule"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model pinFootprintReduce_specW (p : Prog) (hf : p.lookup "pin_footprint_reduce" = some pinFootprintReduceL)
  fns [hf ↦ pinFootprintReduceW list]
  specs [callW_spec p n "pin_at", callW_spec p n "needs_name"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model pinFootprintNat_specW (p : Prog) (hf : p.lookup "pin_footprint_nat" = some pinFootprintNatL)
  fns [hf ↦ pinFootprintNatW list]
  specs [callW_spec p n "nat_op_deps", callW_spec p n "pin_at", callW_spec p n "needs_names_iw",
    callW_spec p n "needs_name", callW_spec p n "pin_range_has"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model pinFootprint_specW (p : Prog) (hf : p.lookup "pin_footprint" = some pinFootprintL)
  fns [hf ↦ pinFootprintW list]
  specs [callW_spec p n "nat_op_name", callW_spec p n "pin_footprint_nat",
    callW_spec p n "pin_footprint_reduce"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model needsConst_specW (p : Prog) (hf : p.lookup "needs_const" = some needsConstL)
  fns [hf ↦ needsConstW list]
  specs [callW_spec p n "needs_expr", callW_spec p n "needs_rules", callW_spec p n "needs_names",
    callW_spec p n "pin_footprint"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model needsTable_specW (p : Prog) (hf : p.lookup "needs_table" = some needsTableL)
  fns [hf ↦ needsTableW list]
  specs [callW_spec p n "needs_name", callW_spec p n "needs_exprs"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

end L.Arena
