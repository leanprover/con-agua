module

public import ConAgua.Arena.Justify
public import ConAgua.Arena.WhnfBase
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
public import ConAgua.Checker.NoVerdictTree
public import ConAgua.Verdict.DeclValsE
public import ConAgua.Arena.CheckerT
import ConAgua.L.ModelGen
import ConAgua.Arena.Verdict
public import Std.WP.Tactic
meta import ConAgua.Checker.NoVerdictTree
import all ConAgua.Arena.Justify

@[expose] public section

/-!
# The justification in L: the generated models (lane compare, helper compare-cone)

One `l_model` per function of `Justify.lean`. The comparisons and the cone abort only with
class-`0` codes (capacities, bounds, fuel): `Option` models, every callee through its run
(`callW`). `check_justified` and `check_record_sol` reject (`R_NOT_JUSTIFIED_BY`, the reserved
names, `check_constant_val`, `check_decl`): unified models.

**The no-verdict closure.** Until the comparison is wired into `check`, the functions here and
the needs walk's are not in `checkerProg`, so not in `nvFns` (`scripts/nv_fns.py`). The unified
models therefore call `justify_why` and `justifiable` through their runs (`callE`), not lifted;
the refinements read the runs by the `Option` specs and the closure `jfNvFns = nvFns ++ jfOwnNv`
(`jfOwnNv`: the `Option`-model functions of the walk, the comparison, the solution's lookups).
-/

open Std.WP
open scoped Lean.Order

noncomputable section

set_option experimental.vcgen true

namespace L.Arena

open L.Ind L.Stubs
open L.Front (DECL)

/-! ## The no-verdict closure of the justification -/

/-- The functions of the justification, the needs walk and the solution's rows that claim no
verdict (class-`0` aborts only). -/
def jfOwnNv : List FnName :=
  ["justifiable", "levels_renaming", "same_cv_up_to_levels", "tbl_eq", "tbl_beq_p",
   "is_stmt_kind", "copy_b", "refines_b", "rec_names", "entry_needs", "cone_entry", "cone_push",
   "cone_go", "justify_why",
   "needs_reset", "needs_name", "needs_names", "needs_names_iw", "lit_needs", "needs_go",
   "needs_expr", "needs_exprs", "needs_rule", "needs_rules", "pin_footprint_reduce",
   "pin_footprint_nat", "pin_footprint", "needs_const", "needs_table",
   "sol_row_get", "sol_row_set", "sol_tbl_get", "sol_tbl_set", "mates_get", "mates_set",
   "sol_find", "sol_find_table", "nd_find", "nd_put", "nd_clear", "cs_find", "cs_put", "cs_clear",
   "builtin_axiom_name"]

/-- The unified models' closure: `nvFns` and the justification's own. -/
def jfNvFns : List FnName := L.Checker.nvFns ++ jfOwnNv

open L.Compiler in
names_tree jfOwnTree : jfOwnNv

open L.Compiler in
/-- `f ∈ jfNvFns` by lookups in the two name trees (use with `by decide +kernel`). -/
theorem jfNv_mem {f : FnName}
    (h : ((L.Checker.nvTree.find (nameCode f)).isSome || (jfOwnTree.find (nameCode f)).isSome) = true) :
    f ∈ jfNvFns := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact List.mem_append_left _ (L.Checker.nv_mem h)
  · rw [namesTree_spec jfOwnTree.eq] at h
    exact List.mem_append_right _ (of_decide_eq_true h)

/-! ## The comparisons -/

l_model justifiable_specW (p : Prog) (hf : p.lookup "justifiable" = some justifiableL)
  fns [hf ↦ justifiableW list]
  specs [callW_spec p n "builtin_axiom_name", callW_spec p n "nat_op_name", callW_spec p n "pin_at"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model levelsRenaming_specW (p : Prog) (hf : p.lookup "levels_renaming" = some levelsRenamingL)
  fns [hf ↦ levelsRenamingW list]
  specs [callW_spec p n "cv_lps", callW_spec p n "sl_nodup"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model sameCvUpToLevels_specW (p : Prog)
    (hf : p.lookup "same_cv_up_to_levels" = some sameCvUpToLevelsL)
  fns [hf ↦ sameCvUpToLevelsW list]
  specs [callW_spec p n "er_sl_eq", callW_spec p n "cv_eq", callW_spec p n "levels_renaming",
    callW_spec p n "erec_alloc", callW_spec p n "cv_at_lps"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model tblEq_specW (p : Prog) (hf : p.lookup "tbl_eq" = some tblEqL)
  fns [hf ↦ tblEqW list]
  specs [callW_spec p n "er_sl_eq"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model tblBeqP_specW (p : Prog) (hf : p.lookup "tbl_beq_p" = some tblBeqPL)
  fns [hf ↦ tblBeqPW list]
  specs [callW_spec p n "tbl_eq"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model isStmtKind_specW (p : Prog) (hf : p.lookup "is_stmt_kind" = some isStmtKindL)
  fns [hf ↦ isStmtKindW list]
  specs []
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model copyB_specW (p : Prog) (hf : p.lookup "copy_b" = some copyBL)
  fns [hf ↦ copyBW list]
  specs [callW_spec p n "er_sl_eq", callW_spec p n "ci_eq", callW_spec p n "is_stmt_kind",
    callW_spec p n "reserved_contains", callW_spec p n "levels_renaming",
    callW_spec p n "ci_at_lps"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model refinesB_specW (p : Prog) (hf : p.lookup "refines_b" = some refinesBL)
  fns [hf ↦ refinesBW list]
  specs [callW_spec p n "copy_b", callW_spec p n "is_stmt_kind", callW_spec p n "pin_at",
    callW_spec p n "erec_alloc", callW_spec p n "erec_put"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

/-! ## The cone -/

l_model recNames_specW (p : Prog) (hf : p.lookup "rec_names" = some recNamesL)
  fns [hf ↦ recNamesW list]
  specs [callW_spec p n "name_rec", callW_spec p n "erec_put"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model entryNeeds_specW (p : Prog) (hf : p.lookup "entry_needs" = some entryNeedsL)
  fns [hf ↦ entryNeedsW list]
  specs [callW_spec p n "needs_reset", callW_spec p n "needs_const", callW_spec p n "needs_names",
    callW_spec p n "erec_alloc", callW_spec p n "rec_names", callW_spec p n "mates_get",
    callW_spec p n "find_table", callW_spec p n "needs_table"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model coneEntry_specW (p : Prog) (hf : p.lookup "cone_entry" = some coneEntryL)
  fns [hf ↦ coneEntryW list]
  specs [callW_spec p n "env_find", callW_spec p n "sol_find", callW_spec p n "refines_b",
    callW_spec p n "find_table", callW_spec p n "sol_find_table", callW_spec p n "tbl_beq_p",
    callW_spec p n "entry_needs"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model conePush_specW (p : Prog) (hf : p.lookup "cone_push" = some conePushL)
  fns [hf ↦ conePushW list]
  specs []
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model coneGo_specW (p : Prog) (hf : p.lookup "cone_go" = some coneGoL)
  fns [hf ↦ coneGoW list]
  specs [callW_spec p n "cs_find", callW_spec p n "cone_entry", callW_spec p n "cs_put",
    callW_spec p n "cone_push"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model justifyWhy_specW (p : Prog) (hf : p.lookup "justify_why" = some justifyWhyL)
  fns [hf ↦ justifyWhyW list]
  specs [callW_spec p n "sol_find", callW_spec p n "same_cv_up_to_levels",
    callW_spec p n "needs_reset", callW_spec p n "needs_expr", callW_spec p n "cs_clear",
    callW_spec p n "cone_push", callW_spec p n "cone_go"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

/-! ## The check of one record, with a solution: unified models -/

/-- **`check_justified`'s unified model**: `check_constant_val` by its unified model, every other
callee lifted but `justify_why`, through its run. -/
l_model checkJustified_specE (p : Prog) (hf : p.lookup "check_justified" = some checkJustifiedL)
    (hc : CcvProg p)
  fns [hf ↦ checkJustifiedE]
  specs [callW_spec p n "erec_ci", checkConstantVal_specE p hc n,
    callW_spec p n "basis_names_ok", callW_spec p n "basis_names_error", callW_spec p n "env_push"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`check_record_sol`'s unified model**: `check_decl` and `check_justified` by their unified
models, `justifiable` through its run. -/
l_model checkRecordSol_specE (p : Prog) (hf : p.lookup "check_record_sol" = some checkRecordSolL)
    (hd : p.lookup "check_decl" = some checkDeclL) (hk : p.lookup "check_decl_kind" = some checkDeclKindL)
    (hj : p.lookup "check_justified" = some checkJustifiedL) (hc : CcvProg p)
  fns [hf ↦ checkRecordSolE]
  specs [checkDecl_specE p hd hk n, checkJustified_specE p hj hc n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

end L.Arena

end
