module

public import ConAgua.Arena.BasisBlockC
public import ConAgua.Arena.IndDeclConstsRef
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
import ConRon.Bridge.Checker.Basis
import all ConAgua.Arena.DeclArms

@[expose] public section

/-!
# `check_basis_block` refines `checkBasisBlock` (lane `ronsync2`, stage 3)

`check_basis_block(vis, kind, bo, bl)` (`DeclArms.lean`): the pinned block read
(`rom_basis_decls`, `RomRefs`), the block copied to `IW` (`er_to_iw`), compared with the pin
(`pin_list_ok`, its contract `PinListOkRef`), each pin at the names its record declares
(`basis_at_block`, `BasisRefs`) installed (`install_basis_decls`, `ibds_ref`). The memos by the
call closure's write set (`cbbFns`, the stream index's `dcA`/`dcC` with `dc0Leaves`: `DcMem`,
`I1Memo`), the twin's `CheckOK` by con-ron's `RStep`s. `cbbRef_of` is `CbbRef`.
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **The call closure of `check_basis_block`** in the checker's program, without
`dc0Leaves` (`inst_lp_core`, `erec_alloc`) and what only they reach. -/
def cbbFns : List FnName :=
  ["check_basis_block", "install_basis_decls", "install_basis_decl", "env_push", "env_row_set",
   "env_find", "base_row_get", "env_row_get", "basis_at_block", "at_block_go", "sl_cons", "iw_copy",
   "iw_alloc", "ci_at_lps", "erec_put", "rules_at_lps_go", "fire_levels_at", "spn_to_er", "sle_go",
   "lv_sub_int", "lv_intern", "intern_imax", "imax_push", "imax_find", "intern_max", "max_push",
   "max_find", "intern_succ", "succ_push", "succ_find", "intern_param", "param_push", "param_find",
   "intern_zero", "zero_push", "zero_find", "lv_node", "lp_substl", "lh_mk", "lp_lookup",
   "keys_push", "ek_copy", "ls_node", "inst_lp", "param_levels", "intern_ls_iw", "intern_ls",
   "ls_push", "ls_find", "ls_match", "limbs_eq", "lit_hash", "iw_pool", "pool_room",
   "param_levels_go", "sl_get", "er_to_iw", "er_copy", "er_copy_er", "cv_at_lps", "rom_basis_decls",
   "rci_block", "rci_block_to", "rci_ci", "rci_rules_to", "rci_rule", "rom_expr_c", "rom_ex_two_c",
   "memo_push", "rset_put", "rset_find", "mk_let", "intern_letE", "letE_push", "letE_find", "der_b",
   "mk_forall", "intern_forall", "forall_push", "forall_find", "mk_lam", "intern_lam", "lam_push",
   "lam_find", "mk_app", "intern_app", "app_push", "app_find", "rom_ex_one_c", "mk_proj",
   "intern_proj", "proj_push", "proj_find", "rom_u64_c", "rom_name_c", "intern_nnum", "nnum_push",
   "nnum_find", "intern_nstr", "nstr_push", "nstr_find", "nstr_match", "rom_put_c", "intern_nanon",
   "nanon_push", "nanon_find", "intern_fvar", "fvar_push", "fvar_find", "rom_ex_leaf_c",
   "intern_const", "const_push", "const_find", "rom_levels_c", "stk_pool", "rom_lvls_go_c",
   "stk_push", "rom_level_c", "rom_lit", "intern_lit", "lit_push", "lit_find", "lit_match",
   "intern_sort", "sort_push", "sort_find", "intern_bvar", "bvar_push", "bvar_find", "rom_ex_ref_c",
   "memo_get", "rom_exprs_to_c", "rci_lvls_to", "rci_caps", "rci_name_sl", "rci_names_to", "rci_cv",
   "rci_fresh", "rset_clear", "rci_slot", "pin_list_ok", "block_links_ok", "block_links_ok_go",
   "block_link_ok_at", "rules_link_ok", "pin_link_ok", "pin_link_go", "canon_name_map", "sl_getd",
   "sl_find", "cv_lps", "const_named", "er_sl_eq", "pin_copies_ok", "pin_copy_ok", "pin_agrees",
   "ci_eq", "ci_eq_rest", "b_eq", "rules_eq", "rule_eq_but_rhs", "rule_eq_b", "er_sl_at",
   "rule_eq_a", "caps_eq", "caps_eq_c", "caps_eq_b", "caps_eq_a", "hint_eq", "cv_eq", "sl_nodup",
   "sl_contains"]

/-- **`cbbFns` stores into `dcA`/`dcC` only** (`Checker/BasisBlockClosed.lean`). -/
def CbbClosed (p : Prog) : Prop := closedAL p dcA dcC cbbFns dc0Leaves = true

/-- **A call of `cbbFns` keeps the stream index's memory invariants**, the `instantiate1Lift`
memo too (`dc_keep`'s and `dc0_keepI1`'s leaf arms). -/
theorem cbb_keep {p : Prog} (hP : DcLeafProg p) (hcl : CbbClosed p) {f : FnName} (hf : f ∈ cbbFns)
    {n : Nat} {vs : List Word} {m m' : Mem} {r : List Word} (h : callW p n f vs m = some (r, m'))
    (hM : DcMem m) (hI : I1Memo m) : DcMem m' ∧ DcIdx m m' ∧ I1Memo m' := by
  refine callW_keepL (P := fun x => DcMem x ∧ DcIdx m x ∧ I1Memo x) hcl
    (fun _ _ hfr hx => ⟨hx.1.frameDc hfr, hx.2.1.frameDc hfr, hx.2.2.frameDc hfr⟩) ?_ hf h
    ⟨hM, DcIdx.refl m, hI⟩
  intro g hg n vs m₁ r m₂ hc hx
  simp only [dc0Leaves, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact ⟨dcMem_ma hP.ma hc hx.1, hx.2.1.frame (maLeaf_frame hP.ma hc)
      (fun b hb h' => by simp at h'; subst h'; revert hb; decide)
      (by decide) (by decide) (by decide) (by decide),
      I1Memo.frame hx.2.2 (maLeaf_frame hP.ma hc) (by decide) (by decide)⟩
  · exact ⟨dcMem_ilp hP.ilpf hc hx.1, hx.2.1.frame (instLPCore_frame hP.ilpf hc)
      (fun b hb h' => ilpfA_idx b h' hb) (by decide) (by decide) (by decide) ilpfA_pins,
      I1Memo.frame hx.2.2 (instLPCore_frame hP.ilpf hc) (by decide) (by decide)⟩
  · refine ⟨dcMem_alloc hP.alloc hc hx.1, dcIdx_alloc hP.alloc hc hx.2.1, ?_⟩
    rw [erecAlloc_mem hP.alloc hc]
    rcases erAllocMem_frame m₁ (vs.getD 0 0) with hfr | hfr
    · exact I1Memo.frame hx.2.2 hfr (by simp) (by decide)
    · exact I1Memo.frame hx.2.2 hfr (by simp) (by decide)

end L.Ind
