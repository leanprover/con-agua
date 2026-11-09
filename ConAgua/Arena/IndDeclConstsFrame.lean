module

public import ConAgua.Arena.IndDeclConstsLp
public import ConAgua.Arena.IndDeclConstsSpec
public import ConAgua.Arena.IndRealMemo
public import ConAgua.Arena.CrOKFrame
import ConAgua.Arena.IndPosSpec.MentionsAnyGo
import ConAgua.Arena.TwinStep
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.IndIface

@[expose] public section

/-!
# What `decl_constants` and `decl_tables` keep (lane `ronsync2`, stage 3)

The two refinements' frame facts (`IndDeclConstsSpec.lean`: `IndMemos`, `IdxKeep`, the memory's
half of `DeclTwin`) from one write set: `dcFns`, the call closure of `decl_constants` and
`decl_tables` in the checker's program with four **leaves** (`dcLeaves`: `mentions_any_const`,
`inst_lp_core`, `erec_alloc`, `instantiate1_lift_fast`), stores only into `dcA`/`dcC` (`DcClosed`,
decided for the checker's program in `Checker/IndDeclConstsClosed.lean`). `dcA` leaves out the
front's records, the pins, the stream index's rows, the core's walk memos and the inductive
memos; `dcC` their control words and the scratch flag. Each leaf keeps the memory invariant
`DcMem` and the builder's words (`DcIdx`) at any memory: its own write set and, for the memos it
writes, its keep fact (`maLeaf_keep`, `instLPCore_keepCM`/`_keepWk`; `erec_alloc` writes `CTL[130]`
only with the scratch flag on). `dc0Fns` (the closure without the projection tables: no
`instantiate1_lift_fast`) keeps the `instantiate1Lift` memo too.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The write set -/

/-- The arrays the closure may write: none of the front's records, the pins and the stream
index's rows (128‥134), the core's walk memos (48‥54, 151‥158), the inductive memos (201‥208). -/
def dcArrOk (b : TieredArray) : Bool :=
  !(b.arr == L.Front.DECL || b.arr == L.Front.DLP || b.arr == L.Arena.FIRSTS ||
    (48 ≤ b.arr && b.arr ≤ 54) || (128 ≤ b.arr && b.arr ≤ 134) || (151 ≤ b.arr && b.arr ≤ 158) ||
    (201 ≤ b.arr && b.arr ≤ 208))

/-- The `CTL` words the closure may write: none of the scratch flag (1), the memos' (48, 50,
52‥59, 152‥158, 202‥219) and the stream index's counters (128‥130). -/
def dcCtlOk (x : Nat) : Bool :=
  !(x == 1 || x == 48 || x == 50 || (52 ≤ x && x ≤ 59) || (128 ≤ x && x ≤ 130) ||
    (152 ≤ x && x ≤ 158) || (202 ≤ x && x ≤ 219))

def dcA : List TieredArray := checkerWordArrays.filter dcArrOk
def dcC : List Word := ((List.range 1024).filter dcCtlOk).map UInt64.ofNat

theorem dcA_spec {b : TieredArray} (h : b ∈ dcA) : dcArrOk b = true := by
  simp only [dcA, List.mem_filter] at h; exact h.2

theorem dcC_spec {x : Word} (h : x ∈ dcC) : dcCtlOk x.toNat = true := by
  simp only [dcC, List.mem_map, List.mem_filter, List.mem_range] at h
  obtain ⟨n, ⟨h1, h2⟩, rfl⟩ := h
  have : (UInt64.ofNat n).toNat = n := by simp; omega
  rw [this]; exact h2

theorem dcA_not {b : TieredArray} (h : dcArrOk b = false) : b ∉ dcA := fun h' => by
  rw [dcA_spec h'] at h; cases h

theorem dcC_not {x : Word} (h : dcCtlOk x.toNat = false) : x ∉ dcC := fun h' => by
  rw [dcC_spec h'] at h; cases h

/-- The leaves. -/
def dcLeaves : List FnName :=
  ["mentions_any_const", "inst_lp_core", "erec_alloc", "instantiate1_lift_fast"]

/-- The leaves of the closure without the projection tables. -/
def dc0Leaves : List FnName := ["mentions_any_const", "inst_lp_core", "erec_alloc"]

/-- **The call closure of `decl_constants` and `decl_tables`** in the checker's program, without
the leaves and what only they reach. -/
def dcFns : List FnName :=
  ["decl_tables", "block_tables", "sl_cons", "iw_copy", "iw_alloc", "block_table", "erec_put",
   "er_from_iw", "er_from_iw_go", "block_shape_lps", "er_to_iw", "er_copy", "struct_proj_bodies",
   "struct_proj_bodies_go", "struct_proj_arg_p", "mk_proj", "intern_proj", "proj_push",
   "proj_find", "der_b", "intern_bvar", "bvar_push", "bvar_find", "e_view", "inst_pis_at_lift",
   "struct_proj_ps", "struct_ps_at", "struct_ps_at_go", "block_shape", "block_shape_build",
   "block_shape_tail", "block_shape_fin", "block_shape_seal", "block_shape_pack", "intern_nanon",
   "nanon_push", "nanon_find", "block_shape_large", "sl_contains", "sl_eq", "block_shape_recs_of",
   "rec7", "rec_target_of", "sl_find", "get_app_fn_f", "get_app_fn", "strip_pis",
   "block_shape_members_of", "rec5", "block_groups", "block_groups_go", "rec2", "block_groups_one",
   "ctor_member", "member_idx_at", "param_levels", "intern_ls_iw", "intern_ls", "ls_push",
   "ls_find", "ls_match", "limbs_eq", "lit_hash", "iw_pool", "pool_room", "param_levels_go",
   "intern_param", "param_push", "param_find", "sl_get", "block_shape_ctors_of", "lvl_eq_c",
   "lvl_eq_rec", "lq_put", "lq_find", "lvl_eq", "lv_equiv", "lv_leq", "lv_rest", "lv_imax",
   "lv_imax_l", "lv_imax_r", "lv_dist2", "lv_simp", "lh_mk", "lv_comb", "lv_node", "lv_dist1",
   "lv_cases", "lv_cases_at", "lv_subsimp", "lv_subst", "lv_eq", "pin_word",
   "block_shape_result_sort", "sl_getd", "block_shape_pins_ok", "block_shape_pins_ctors",
   "reserved_contains", "reserved_from", "block_shape_pins_recs", "block_shape_pins_formers",
   "block_member_counts", "block_member_counts_go", "block_counts", "block_counts_pure",
   "block_counts_head", "pi_binders", "block_member_counts_find", "block_shape_names_of",
   "block_split", "rec6", "block_split_ctors", "rec3", "block_split_recs", "basis_name_hit",
   "basis_name_hit_go", "block_names_eq", "rom_basis_decls", "rci_block", "rci_block_to", "rci_ci",
   "rci_rules_to", "rci_rule", "rom_expr_c", "rom_ex_two_c", "memo_push", "rset_put", "rset_find",
   "mk_let", "intern_letE", "letE_push", "letE_find", "mk_forall", "intern_forall", "forall_push",
   "forall_find", "mk_lam", "intern_lam", "lam_push", "lam_find", "mk_app", "intern_app",
   "app_push", "app_find", "rom_ex_one_c", "rom_u64_c", "rom_name_c", "intern_nnum", "nnum_push",
   "nnum_find", "intern_nstr", "nstr_push", "nstr_find", "nstr_match", "rom_put_c", "intern_fvar",
   "fvar_push", "fvar_find", "rom_ex_leaf_c", "intern_const", "const_push", "const_find",
   "rom_levels_c", "stk_pool", "rom_lvls_go_c", "stk_push", "rom_level_c", "intern_imax",
   "imax_push", "imax_find", "intern_max", "max_push", "max_find", "intern_succ", "succ_push",
   "succ_find", "intern_zero", "zero_push", "zero_find", "rom_lit", "intern_lit", "lit_push",
   "lit_find", "lit_match", "intern_sort", "sort_push", "sort_find", "rom_ex_ref_c", "memo_get",
   "rom_exprs_to_c", "rci_lvls_to", "rci_caps", "rci_name_sl", "rci_names_to", "rci_cv",
   "rci_fresh", "rset_clear", "rci_slot", "ind_block_to_erec", "ind_copy_go", "ind_rec_copy",
   "dind_copy", "decl_constants", "decl_constants_ind", "block_constants", "sl_append",
   "block_recs", "block_rec", "rec_info_rec", "rules_refire", "rec_fire", "expr_drop_vars_list",
   "expr_drop_vars", "instantiate1_fast", "inst_entry", "if_clear", "inst_go", "inst_proj",
   "if_put", "if_find", "inst_let", "inst_forall", "inst_lam", "inst_app", "der_bv",
   "get_app_args_f", "spn_to_iw", "get_app_args", "app_fill", "app_count", "view_ls", "pool_copy",
   "ls_node", "block_ctors", "block_ctors_go", "ctor_info_rec", "block_shape_all_ctors",
   "block_shape_all_ctors_go", "block_shape_ctors_copy", "num_ctors_of", "block_formers",
   "block_formers_go", "ind_info_rec", "er_put5", "block_caps_at", "block_caps_fin",
   "block_caps_at_er_copy", "block_caps_at_er_copy_go", "block_caps_ctor_names",
   "member_names_copy", "block_shape_member_names", "block_caps_one", "block_caps_head",
   "block_shape_declared", "member_field_copy", "block_is_rec", "block_is_rec_go",
   "block_is_rec_member", "pi_doms_mention_any", "basis_at_block", "at_block_go", "ci_at_lps",
   "rules_at_lps_go", "fire_levels_at", "spn_to_er", "sle_go", "lv_sub_int", "lv_intern",
   "lp_substl", "lp_lookup", "keys_push", "ek_copy", "inst_lp", "er_copy_er", "cv_at_lps",
   "sl_new1", "quot_at", "quot_pin", "erec_ci", "dlp_copy", "decl_constants_axiom", "pin_at"]

/-- **The call closure of `decl_constants`, `ind_block_to_erec`, `basis_name_hit` and
`block_shape`** (what `decl_tables` calls before `block_tables`), without the leaves. -/
def dc0Fns : List FnName :=
  ["block_shape", "block_shape_build", "block_shape_tail", "block_shape_fin", "block_shape_seal",
   "block_shape_pack", "iw_alloc", "intern_nanon", "nanon_push", "nanon_find", "block_shape_large",
   "sl_contains", "sl_eq", "er_to_iw", "er_copy", "block_shape_recs_of", "sl_cons", "iw_copy",
   "rec7", "rec_target_of", "sl_find", "e_view", "get_app_fn_f", "get_app_fn", "strip_pis",
   "block_shape_members_of", "rec5", "block_groups", "block_groups_go", "rec2", "block_groups_one",
   "ctor_member", "member_idx_at", "param_levels", "intern_ls_iw", "intern_ls", "ls_push",
   "ls_find", "ls_match", "limbs_eq", "lit_hash", "iw_pool", "pool_room", "param_levels_go",
   "intern_param", "param_push", "param_find", "sl_get", "block_shape_ctors_of", "lvl_eq_c",
   "lvl_eq_rec", "lq_put", "lq_find", "lvl_eq", "lv_equiv", "lv_leq", "lv_rest", "lv_imax",
   "lv_imax_l", "lv_imax_r", "lv_dist2", "lv_simp", "lh_mk", "lv_comb", "lv_node", "lv_dist1",
   "lv_cases", "lv_cases_at", "lv_subsimp", "lv_subst", "lv_eq", "pin_word",
   "block_shape_result_sort", "sl_getd", "block_shape_pins_ok", "block_shape_pins_ctors",
   "reserved_contains", "reserved_from", "block_shape_pins_recs", "block_shape_pins_formers",
   "block_member_counts", "block_member_counts_go", "block_counts", "block_counts_pure",
   "block_counts_head", "pi_binders", "block_member_counts_find", "block_shape_names_of",
   "block_split", "rec6", "block_split_ctors", "rec3", "block_split_recs", "basis_name_hit",
   "basis_name_hit_go", "block_names_eq", "rom_basis_decls", "rci_block", "rci_block_to", "rci_ci",
   "rci_rules_to", "rci_rule", "erec_put", "rom_expr_c", "rom_ex_two_c", "memo_push", "rset_put",
   "rset_find", "mk_let", "intern_letE", "letE_push", "letE_find", "der_b", "mk_forall",
   "intern_forall", "forall_push", "forall_find", "mk_lam", "intern_lam", "lam_push", "lam_find",
   "mk_app", "intern_app", "app_push", "app_find", "rom_ex_one_c", "mk_proj", "intern_proj",
   "proj_push", "proj_find", "rom_u64_c", "rom_name_c", "intern_nnum", "nnum_push", "nnum_find",
   "intern_nstr", "nstr_push", "nstr_find", "nstr_match", "rom_put_c", "intern_fvar", "fvar_push",
   "fvar_find", "rom_ex_leaf_c", "intern_const", "const_push", "const_find", "rom_levels_c",
   "stk_pool", "rom_lvls_go_c", "stk_push", "rom_level_c", "intern_imax", "imax_push", "imax_find",
   "intern_max", "max_push", "max_find", "intern_succ", "succ_push", "succ_find", "intern_zero",
   "zero_push", "zero_find", "rom_lit", "intern_lit", "lit_push", "lit_find", "lit_match",
   "intern_sort", "sort_push", "sort_find", "intern_bvar", "bvar_push", "bvar_find",
   "rom_ex_ref_c", "memo_get", "rom_exprs_to_c", "rci_lvls_to", "rci_caps", "rci_name_sl",
   "rci_names_to", "rci_cv", "rci_fresh", "rset_clear", "rci_slot", "ind_block_to_erec",
   "ind_copy_go", "ind_rec_copy", "dind_copy", "decl_constants", "decl_constants_ind",
   "block_constants", "sl_append", "block_recs", "block_rec", "rec_info_rec", "rules_refire",
   "er_from_iw", "er_from_iw_go", "rec_fire", "expr_drop_vars_list", "expr_drop_vars",
   "instantiate1_fast", "inst_entry", "if_clear", "inst_go", "inst_proj", "if_put", "if_find",
   "inst_let", "inst_forall", "inst_lam", "inst_app", "der_bv", "get_app_args_f", "spn_to_iw",
   "get_app_args", "app_fill", "app_count", "view_ls", "pool_copy", "ls_node", "block_ctors",
   "block_ctors_go", "ctor_info_rec", "block_shape_all_ctors", "block_shape_all_ctors_go",
   "block_shape_ctors_copy", "num_ctors_of", "block_formers", "block_formers_go", "ind_info_rec",
   "er_put5", "block_caps_at", "block_caps_fin", "block_caps_at_er_copy",
   "block_caps_at_er_copy_go", "block_caps_ctor_names", "member_names_copy",
   "block_shape_member_names", "block_caps_one", "block_caps_head", "block_shape_declared",
   "member_field_copy", "block_is_rec", "block_is_rec_go", "block_is_rec_member",
   "pi_doms_mention_any", "basis_at_block", "at_block_go", "ci_at_lps", "rules_at_lps_go",
   "fire_levels_at", "spn_to_er", "sle_go", "lv_sub_int", "lv_intern", "lp_substl", "lp_lookup",
   "keys_push", "ek_copy", "inst_lp", "er_copy_er", "cv_at_lps", "sl_new1", "quot_at", "quot_pin",
   "erec_ci", "dlp_copy", "decl_constants_axiom", "pin_at"]

/-- **The program hypothesis**: both closures store only into `dcA`/`dcC`. -/
structure DcClosed (p : Prog) : Prop where
  all : closedAL p dcA dcC dcFns dcLeaves = true
  c0 : closedAL p dcA dcC dc0Fns dc0Leaves = true

/-! ## What the write set keeps -/

/-- **The memory invariants the closure keeps**: the core's memos, the inductive stage's memos
but `instantiate1Lift`'s, the `constsResolveF` memo, the `abstract1`/`instantiateList` memos,
`WkOK` (the walk memos, the three sizes, the pin flag). -/
structure DcMem (m : Mem) : Prop where
  core : CoreMemos m
  stage : StageMemos m
  cr : L.Stubs.CrOK m
  ab : AbMemo m
  il : IlMemo m
  wk : WkOK m

/-- **What the stream index's builder reads, kept**: the front's records, the first counters, the
index rows (both tiers), `CTL[128]`, the scratch flag, and `CTL[130]` while the flag is off. -/
structure DcIdx (m₀ m : Mem) : Prop where
  arr : ∀ b : TieredArray, (b.arr = L.Front.DECL ∨ b.arr = L.Front.DLP ∨ b.arr = L.Arena.FIRSTS ∨
    (129 ≤ b.arr ∧ b.arr ≤ 134)) → m.arr64 b = m₀.arr64 b
  c128 : rdW (m.arr64 CTL) 128 = rdW (m₀.arr64 CTL) 128
  c1 : rdW (m.arr64 CTL) 1 = rdW (m₀.arr64 CTL) 1
  c130 : rdW (m₀.arr64 CTL) 1 = 0 → rdW (m.arr64 CTL) 130 = rdW (m₀.arr64 CTL) 130
  /-- The pin table. -/
  pins : m.arr64 PINS = m₀.arr64 PINS
  /-- Every array's size. -/
  sz : ∀ b, (m.arr64 b).size = (m₀.arr64 b).size

theorem DcIdx.refl (m : Mem) : DcIdx m m := ⟨fun _ _ => rfl, rfl, rfl, fun _ => rfl, rfl, fun _ => rfl⟩

/-- `DcIdx` across a writer of other arrays and words. -/
theorem DcIdx.frame {A : List TieredArray} {C : List Word} {m₀ m m' : Mem} (h : DcIdx m₀ m)
    (hf : MemFrame A C m m')
    (hA : ∀ b : TieredArray, (b.arr = L.Front.DECL ∨ b.arr = L.Front.DLP ∨ b.arr = L.Arena.FIRSTS ∨
      (129 ≤ b.arr ∧ b.arr ≤ 134)) → b ∉ A)
    (h128 : (128 : Word) ∉ C) (h1 : (1 : Word) ∉ C) (h130 : (130 : Word) ∉ C)
    (hP : (PINS : TieredArray) ∉ A) : DcIdx m₀ m' :=
  ⟨fun b hb => by
      rw [hf.arr b (hA b hb) (fun e => by subst e; revert hb; decide)]; exact h.arr b hb,
    by rw [hf.ctl _ h128]; exact h.c128, by rw [hf.ctl _ h1]; exact h.c1,
    fun h0 => by rw [hf.ctl _ h130]; exact h.c130 h0,
    by rw [hf.arr PINS hP (by decide)]; exact h.pins, fun b => (hf.size b).trans (h.sz b)⟩

theorem dcIdx_dcA : ∀ b : TieredArray, (b.arr = L.Front.DECL ∨ b.arr = L.Front.DLP ∨
    b.arr = L.Arena.FIRSTS ∨ (129 ≤ b.arr ∧ b.arr ≤ 134)) → b ∉ dcA := by
  intro b hb
  apply dcA_not
  simp only [dcArrOk, Bool.not_eq_false', Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
    decide_eq_true_eq]
  omega

theorem DcIdx.frameDc {m₀ m m' : Mem} (h : DcIdx m₀ m) (hf : MemFrame dcA dcC m m') : DcIdx m₀ m' :=
  h.frame hf dcIdx_dcA (dcC_not (by decide)) (dcC_not (by decide)) (dcC_not (by decide))
    (dcA_not (by decide))

/-- The arrays `DcMem` reads (its memos, the pins). -/
def dcMemArrOk (b : TieredArray) : Bool :=
  !((48 ≤ b.arr && b.arr ≤ 50) || (52 ≤ b.arr && b.arr ≤ 54) || (151 ≤ b.arr && b.arr ≤ 155) ||
    (201 ≤ b.arr && b.arr ≤ 208) || b.arr == 128)

/-- The `CTL` words `DcMem` reads (its memos' control words). -/
def dcMemCtlOk (x : Nat) : Bool :=
  !(x == 48 || x == 50 || (54 ≤ x && x ≤ 58) || (152 ≤ x && x ≤ 158) || (202 ≤ x && x ≤ 219))

/-- `DcMem` across a writer of other arrays and words (the conditions as tests). -/
theorem DcMem.frame {A : List TieredArray} {C : List Word} {m m' : Mem} (h : DcMem m)
    (hf : MemFrame A C m m') (hA : ∀ b ∈ A, dcMemArrOk b = true)
    (hC : ∀ x ∈ C, dcMemCtlOk x.toNat = true) : DcMem m' := by
  have nA : ∀ b : TieredArray, dcMemArrOk b = false → b ∉ A := fun b hb h' => by
    rw [hA b h'] at hb; cases hb
  have nC : ∀ x : Word, dcMemCtlOk x.toNat = false → x ∉ C := fun x hx h' => by
    rw [hC x h'] at hx; cases hx
  obtain ⟨hcore, hst, hcr, ⟨mpa, ha⟩, ⟨mpi, hi⟩, ⟨hw, h1, h2, h3, h4⟩⟩ := h
  refine ⟨hcore.frame hf ⟨nA _ (by decide), nA _ (by decide)⟩ ⟨nC _ (by decide), nC _ (by decide)⟩
      ⟨nA _ (by decide), nA _ (by decide), nA _ (by decide)⟩
      ⟨nC _ (by decide), nC _ (by decide), nC _ (by decide)⟩
      ⟨nA _ (by decide), nA _ (by decide), nA _ (by decide)⟩
      ⟨nC _ (by decide), nC _ (by decide), nC _ (by decide)⟩ (nA _ (by decide)) (nC _ (by decide)),
    hst.frame hf (fun b hb => ?_) (fun x hx => ?_),
    CrOK.frame hcr hf (nA _ (by decide)) (nC _ (by decide)),
    ⟨mpa, memoRG_frame ⟨ABMEMO, 48⟩ ⟨by decide, by decide⟩ lfKey decE A C (nA _ (by decide))
      (nC _ (by decide)) m m' hf mpa ha⟩,
    ⟨mpi, memoRG_frame ⟨ILMEMO, 50⟩ ⟨by decide, by decide⟩ lfKey decE A C (nA _ (by decide))
      (nC _ (by decide)) m m' hf mpi hi⟩,
    ⟨hw.frame hf ⟨nA _ (by decide), nA _ (by decide), nA _ (by decide)⟩
      ⟨nC _ (by decide), nC _ (by decide), nC _ (by decide)⟩
      ⟨nA _ (by decide), nA _ (by decide), nA _ (by decide)⟩
      ⟨nC _ (by decide), nC _ (by decide), nC _ (by decide)⟩,
      by rw [hf.size]; exact h1, by rw [hf.size]; exact h2, by rw [hf.size]; exact h3,
      by rw [pinW_frame hf (nA _ (by decide))]; exact h4⟩⟩
  · have := hA b hb
    simp only [dcMemArrOk, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
      Bool.and_eq_false_imp, decide_eq_true_eq, decide_eq_false_iff_not] at this
    omega
  · have := hC x hx
    simp only [dcMemCtlOk, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
      Bool.and_eq_false_imp, decide_eq_true_eq, decide_eq_false_iff_not] at this
    omega

theorem dcA_mem {b : TieredArray} (h : b ∈ dcA) : dcMemArrOk b = true := by
  have := dcA_spec h
  revert this
  simp only [dcArrOk, dcMemArrOk, Bool.or_eq_false_iff, beq_eq_false_iff_ne,
    ne_eq, Bool.and_eq_false_imp, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_eq_eq_not,
    Bool.not_true]
  omega

theorem dcC_mem {x : Word} (h : x ∈ dcC) : dcMemCtlOk x.toNat = true := by
  have := dcC_spec h
  revert this
  simp only [dcCtlOk, dcMemCtlOk, Bool.or_eq_false_iff, beq_eq_false_iff_ne,
    ne_eq, Bool.and_eq_false_imp, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_eq_eq_not,
    Bool.not_true]
  omega

theorem DcMem.frameDc {m m' : Mem} (h : DcMem m) (hf : MemFrame dcA dcC m m') : DcMem m' :=
  h.frame hf (fun _ hb => dcA_mem hb) (fun _ hx => dcC_mem hx)

/-- The `instantiate1Lift` memo across the write set. -/
theorem I1Memo.frameDc {m m' : Mem} (h : I1Memo m) (hf : MemFrame dcA dcC m m') : I1Memo m' :=
  I1Memo.frame h hf (dcA_not (by decide)) (dcC_not (by decide))

/-! ## The leaves -/

theorem ma_frame (n : Nat) :
    (∀ m m' no nl f h r, maGoW n m no nl f h = some (r, m') → MemFrame [maSch.arr] [maSch.cs + 1] m m') ∧
    (∀ m m' no nl f1 g x y z r, maNodeW n m no nl f1 g x y z = some (r, m') →
      MemFrame [maSch.arr] [maSch.cs + 1] m m') := by
  induction n with
  | zero => exact ⟨fun _ _ _ _ _ _ _ hh => by simp [maGoW] at hh,
      fun _ _ _ _ _ _ _ _ _ _ hh => by simp [maNodeW] at hh⟩
  | succ n ih =>
    obtain ⟨igo, inode⟩ := ih
    refine ⟨fun m m' no nl f h r hh => ?_, fun m m' no nl f1 g x y z r hh => ?_⟩
    · by_cases hf0 : f = 0
      · rw [maGoW_abort n m no nl f h hf0] at hh; cases hh
      rw [maGoW_view n m no nl f h hf0] at hh
      generalize hv : eViewW m h = v at hh
      by_cases hv0 : v = []
      · subst hv0; simp [maG1] at hh
      by_cases hg : v.headD 0 = 0 ∨ v.headD 0 = 2 ∨ v.headD 0 = 8
      · rw [maG1_leaf n m no nl f h v hv0 hg] at hh
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hh); exact MemFrame.refl _ _ _
      by_cases h3 : v.headD 0 = 3
      · rw [maG1_const n m no nl f h v hv0 hg h3] at hh
        cases hc : containsW n m no nl (v.tail.headD 0) with
        | none => rw [hc] at hh; simp [maC] at hh
        | some b =>
          rw [hc, maC_some] at hh
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hh); exact MemFrame.refl _ _ _
      rw [maG1_node n m no nl f h v hv0 hg h3] at hh
      by_cases hfr : mfindG maSch m h 0 = []
      · rw [maG3_abort n m no nl f h v _ hfr] at hh; cases hh
      by_cases hhit : (mfindG maSch m h 0).headD 0 ≠ 0
      · rw [maG3_hit n m no nl f h v _ hfr hhit] at hh
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hh); exact MemFrame.refl _ _ _
      rw [maG3_miss n m no nl f h v _ hfr hhit] at hh
      rcases h2 : maNodeW n m no nl (f - 1) (v.headD 0) (v.tail.headD 0) (v.tail.tail.headD 0)
        (v.tail.tail.tail.headD 0) with _ | ⟨r2, m2⟩
      · rw [h2] at hh; simp [maG4] at hh
      rw [h2, maG4_some] at hh
      have f2 := inode _ _ _ _ _ _ _ _ _ _ h2
      cases hm : msetG maSch m2 h 0 r2 with
      | none => rw [hm] at hh; simp [maG5] at hh
      | some m3 =>
        rw [hm, maG5_some] at hh
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hh)
        exact f2.trans (msetG_frame maSch maSch_wf _ _ _ _ _ hm)
    · by_cases g1 : g = 1
      · rw [maNodeW_fvar n m no nl f1 g x y z g1] at hh; exact igo _ _ _ _ _ _ _ hh
      by_cases gb : g = 4 ∨ g = 5 ∨ g = 6
      · rw [maNodeW_bin n m no nl f1 g x y z gb] at hh
        rcases h1 : maGoW n m no nl f1 x with _ | ⟨b1, m1⟩
        · rw [h1] at hh; simp [maB1] at hh
        rw [h1, maB1_some] at hh
        rcases h2 : maGoW n m1 no nl f1 y with _ | ⟨b2, m2⟩
        · rw [h2] at hh; simp [maB2] at hh
        rw [h2, maB2_some] at hh
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hh)
        exact (igo _ _ _ _ _ _ _ h1).trans (igo _ _ _ _ _ _ _ h2)
      by_cases g7 : g = 7
      · rw [maNodeW_let n m no nl f1 g x y z g7] at hh
        rcases h1 : maGoW n m no nl f1 x with _ | ⟨b1, m1⟩
        · rw [h1] at hh; simp [maL1] at hh
        rw [h1, maL1_some] at hh
        rcases h2 : maGoW n m1 no nl f1 y with _ | ⟨b2, m2⟩
        · rw [h2] at hh; simp [maL2] at hh
        rw [h2, maL2_some] at hh
        rcases h3 : maGoW n m2 no nl f1 z with _ | ⟨b3, m3⟩
        · rw [h3] at hh; simp [maL3] at hh
        rw [h3, maL3_some] at hh
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hh)
        exact ((igo _ _ _ _ _ _ _ h1).trans (igo _ _ _ _ _ _ _ h2)).trans (igo _ _ _ _ _ _ _ h3)
      rw [maNodeW_proj n m no nl f1 g x y z g1 gb g7] at hh
      rcases h1 : maGoW n m no nl f1 z with _ | ⟨b1, m1⟩
      · rw [h1] at hh; simp [maP1] at hh
      rw [h1, maP1_some] at hh
      cases hc : containsW n m1 no nl x with
      | none => rw [hc] at hh; simp [maP2] at hh
      | some b2 =>
        rw [hc, maP2_some] at hh
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hh)
        exact igo _ _ _ _ _ _ _ h1


/-- **`mentions_any_const`'s model writes only its memo.** -/
theorem maConstW_frame {n : Nat} {m m' : Mem} {no nl e r : Word} (h : maConstW n m no nl e = some (r, m')) :
    MemFrame [maSch.arr] [maSch.cs, maSch.cs + 1] m m' := by
  by_cases h0 : rdW (m.arr64 CTL) maSch.cs + 2 = 0
  · simp [maConstW, h0] at h
  rw [maConstW_eq n m no nl e h0] at h
  rcases h1 : maGoW n (mclearG maSch m) no nl CWF e with _ | ⟨r1, m1⟩
  · rw [h1] at h; simp [maClrK] at h
  rw [h1] at h
  have f1 := (ma_frame n).1 _ _ _ _ _ _ _ h1
  by_cases h2 : rdW (m1.arr64 CTL) maSch.cs + 2 = 0
  · simp [maClrK, h2] at h
  rw [maClrK_some r1 m1 h2] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact (((mclearG_frame maSch m).mono (by simp) (by simp)).trans (f1.mono (by simp) (by simp))).trans
    ((mclearG_frame maSch m1).mono (by simp) (by simp))

theorem maLeaf_frame {p : Prog} (hM : MaProg p) {n : Nat} {vs : List Word} {m m' : Mem} {r : List Word}
    (hc : callW p n "mentions_any_const" vs m = some (r, m')) :
    MemFrame [maSch.arr] [maSch.cs, maSch.cs + 1] m m' := by
  obtain ⟨s'', hm, -, hu⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (mentionsAnyConst_specV hM n _ vs) (callW_mono hc (Nat.le_add_right n 1))
  rw [hm] at hu
  exact maConstW_frame hu

/-- `erec_alloc`'s model at any argument list. -/
theorem erecAlloc_specV (p : Prog) (hp : p.lookup "erec_alloc" = some erecAlloc) (n : Nat) (s₀ : St)
    (vs : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "erec_alloc" vs
    ⦃fun r s' => LocEq s' s₀ ∧ erAllocW s₀.mem (vs.getD 0 0) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, erecAlloc]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, L.evalC_spec, L.evalE_spec, evalArgs, setLoc, setLocs, st64]
    all_goals simp only [Cond.pval, Expr.pval, St.setLoc_loc, St.setLoc_mem, Locals.init,
      Cmp.eval, BinOp.eval, rd64_rdWC, beq_iff_eq] at *
    all_goals subst_vars
    all_goals simp_all [LocEq, Sig.retVal, Sig.retOr, erAllocW, erAllocMem, ctl_t0', tierA]

theorem erecAlloc_mem {p : Prog} (hp : p.lookup "erec_alloc" = some erecAlloc) {n : Nat}
    {vs : List Word} {m m' : Mem} {r : List Word} (hc : callW p n "erec_alloc" vs m = some (r, m')) :
    m' = erAllocMem m (vs.getD 0 0) := by
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (erecAlloc_specV p hp n _ vs) hc
  rw [hs'] at hW
  simp only [erAllocW] at hW
  split at hW <;> split at hW <;> (try split at hW) <;> first
    | cases hW
    | (simp only [Option.some.injEq, Prod.mk.injEq] at hW; exact hW.2.symm)


/-! ## Each leaf keeps the invariants, at any memory -/

/-- The builder's arrays. -/
abbrev DcIdxArr (b : TieredArray) : Prop := b.arr = L.Front.DECL ∨ b.arr = L.Front.DLP ∨
  b.arr = L.Arena.FIRSTS ∨ (129 ≤ b.arr ∧ b.arr ≤ 134)

theorem ilpfA_idx : ∀ b ∈ ilpfA, ¬ DcIdxArr b := by decide +kernel
theorem i1lA_idx : ∀ b ∈ i1lA, ¬ DcIdxArr b := by decide +kernel
theorem ilpfA_pins : (PINS : TieredArray) ∉ ilpfA := by decide +kernel
theorem i1lA_pins : (PINS : TieredArray) ∉ i1lA := by decide +kernel
theorem dcIlpfA_stage : ∀ b ∈ ilpfA, b.arr < 201 ∨ 208 < b.arr := by decide +kernel
theorem dcIlpfC_stage : ∀ x ∈ ilpfC, x.toNat < 202 ∨ 219 < x.toNat := by simp [ilpfC]
theorem i1lA_mem : ∀ b ∈ i1lA, dcMemArrOk b = true := by decide +kernel
theorem i1lC_mem : ∀ x ∈ i1lC, dcMemCtlOk x.toNat = true := by simp [i1lC, walkC, liftC, dcMemCtlOk]

theorem ma_mfr {m m' : Mem} (hf : MemFrame [maSch.arr] [maSch.cs, maSch.cs + 1] m m') :
    MFr [maSch.arr] [maSch.cs, maSch.cs + 1] m m' :=
  ⟨_, _, hf, fun _ hb => Or.inr (Or.inr hb), fun _ hx => Or.inr (Or.inr hx)⟩

theorem dcMem_ma {p : Prog} (hM : MaProg p) {n : Nat} {vs : List Word} {m m' : Mem} {r : List Word}
    (hc : callW p n "mentions_any_const" vs m = some (r, m')) (h : DcMem m) : DcMem m' := by
  have hf := maLeaf_frame hM hc
  obtain ⟨hcore, ⟨hpos, hma, ⟨mpc, hmc⟩, ⟨mpt, hta⟩⟩, hcr, ⟨mpa, ha⟩, ⟨mpi, hi⟩, ⟨hw, h1, h2, h3, h4⟩⟩ := h
  exact ⟨hcore.frame hf (by decide) (by decide),
    ⟨hpos.mfr (ma_mfr hf) (by decide), maLeaf_keep hM _ _ _ _ _ hc hma,
      ⟨mpc, memoRG_frame mcSch mcSch_wf _ _ _ _ (by decide) (by decide) m m' hf mpc hmc⟩,
      ⟨mpt, memoRG_frame taSch taSch_wf _ _ _ _ (by decide) (by decide) m m' hf mpt hta⟩⟩,
    CrOK.frame hcr hf (by decide) (by decide),
    ⟨mpa, memoRG_frame ⟨ABMEMO, 48⟩ ⟨by decide, by decide⟩ lfKey decE _ _ (by decide) (by decide)
      m m' hf mpa ha⟩,
    ⟨mpi, memoRG_frame ⟨ILMEMO, 50⟩ ⟨by decide, by decide⟩ lfKey decE _ _ (by decide) (by decide)
      m m' hf mpi hi⟩,
    ⟨hw.frame hf (by decide) (by decide), by rw [hf.size]; exact h1, by rw [hf.size]; exact h2,
      by rw [hf.size]; exact h3, by rw [pinW_frame hf (by decide)]; exact h4⟩⟩

theorem dcMem_ilp {p : Prog} (hI : IlpfF p) {n : Nat} {vs : List Word} {m m' : Mem} {r : List Word}
    (hc : callW p n "inst_lp_core" vs m = some (r, m')) (h : DcMem m) : DcMem m' := by
  have hf := instLPCore_frame hI hc
  obtain ⟨hcore, hst, hcr, ⟨mpa, ha⟩, ⟨mpi, hi⟩, hwk⟩ := h
  exact ⟨instLPCore_keepCM hI hc hcore, hst.frame hf dcIlpfA_stage dcIlpfC_stage,
    CrOK.frame hcr hf (by decide) (by decide),
    ⟨mpa, memoRG_frame ⟨ABMEMO, 48⟩ ⟨by decide, by decide⟩ lfKey decE _ _ (by decide) (by decide)
      m m' hf mpa ha⟩,
    ⟨mpi, memoRG_frame ⟨ILMEMO, 50⟩ ⟨by decide, by decide⟩ lfKey decE _ _ (by decide) (by decide)
      m m' hf mpi hi⟩,
    instLPCore_keepWk hI hc hwk⟩

theorem erAllocMem_frame (m : Mem) (k : Word) :
    MemFrame [] [129] m (erAllocMem m k) ∨ MemFrame [] [130] m (erAllocMem m k) := by
  unfold erAllocMem; split
  · exact .inl (MemFrame.setCtl _ _ _)
  · exact .inr (MemFrame.setCtl _ _ _)

theorem dcMem_alloc {p : Prog} (hp : p.lookup "erec_alloc" = some erecAlloc) {n : Nat}
    {vs : List Word} {m m' : Mem} {r : List Word} (hc : callW p n "erec_alloc" vs m = some (r, m'))
    (h : DcMem m) : DcMem m' := by
  rw [erecAlloc_mem hp hc]
  rcases erAllocMem_frame m (vs.getD 0 0) with hf | hf
  · exact h.frame hf (by simp) (by simp [dcMemCtlOk])
  · exact h.frame hf (by simp) (by simp [dcMemCtlOk])

theorem i1lF_call {p : Prog} (hI : I1lF p) {n : Nat} {vs : List Word} {m m' : Mem} {r : List Word}
    (hc : callW p n "instantiate1_lift_fast" vs m = some (r, m')) : MemFrame i1lA i1lC m m' := by
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (i1lF_spec p hI n _ vs) hc
  rw [hs'] at hW
  exact i1lF_frame hW

theorem dcMem_i1 {p : Prog} (hI : I1lF p) {n : Nat} {vs : List Word} {m m' : Mem} {r : List Word}
    (hc : callW p n "instantiate1_lift_fast" vs m = some (r, m')) (h : DcMem m) : DcMem m' :=
  h.frame (i1lF_call hI hc) i1lA_mem i1lC_mem

theorem dcIdx_alloc {p : Prog} (hp : p.lookup "erec_alloc" = some erecAlloc) {n : Nat}
    {vs : List Word} {m₀ m m' : Mem} {r : List Word} (hc : callW p n "erec_alloc" vs m = some (r, m'))
    (h : DcIdx m₀ m) : DcIdx m₀ m' := by
  rw [erecAlloc_mem hp hc]
  unfold erAllocMem
  split
  · exact h.frame (MemFrame.setCtl _ _ _) (fun _ _ => by simp) (by decide) (by decide) (by decide)
      (by simp)
  · rename_i h1
    have hf := MemFrame.setCtl m 130 (rdW (m.arr64 CTL) 130 + vs.getD 0 0)
    refine ⟨fun b hb => ?_, by rw [hf.ctl _ (by decide)]; exact h.c128,
      by rw [hf.ctl _ (by decide)]; exact h.c1, fun h0 => absurd (h.c1.trans h0) h1,
      by rw [hf.arr PINS (by simp) (by decide)]; exact h.pins, fun b => (hf.size b).trans (h.sz b)⟩
    rw [hf.arr b (by simp) (fun e => by subst e; revert hb; decide)]; exact h.arr b hb

/-! ## The invariants across a call of the closure -/

/-- The leaves' program bundles and the write sets. -/
structure DcLeafProg (p : Prog) : Prop where
  ma : MaProg p
  ilpf : IlpfF p
  alloc : p.lookup "erec_alloc" = some erecAlloc
  i1 : I1lF p
  closed : DcClosed p

/-- **A call of `dcFns` keeps `DcMem` and what the builder reads.** -/
theorem dc_keep {p : Prog} (hP : DcLeafProg p) {f : FnName} (hf : f ∈ dcFns) {n : Nat}
    {vs : List Word} {m m' : Mem} {r : List Word} (h : callW p n f vs m = some (r, m'))
    (hM : DcMem m) : DcMem m' ∧ DcIdx m m' := by
  refine callW_keepL (P := fun x => DcMem x ∧ DcIdx m x) hP.closed.all
    (fun _ _ hfr hx => ⟨hx.1.frameDc hfr, hx.2.frameDc hfr⟩) ?_ hf h ⟨hM, DcIdx.refl m⟩
  intro g hg n vs m₁ r m₂ hc hx
  simp only [dcLeaves, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact ⟨dcMem_ma hP.ma hc hx.1, hx.2.frame (maLeaf_frame hP.ma hc)
      (fun b hb h' => by simp at h'; subst h'; revert hb; decide)
      (by decide) (by decide) (by decide) (by decide)⟩
  · exact ⟨dcMem_ilp hP.ilpf hc hx.1, hx.2.frame (instLPCore_frame hP.ilpf hc)
      (fun b hb h' => ilpfA_idx b h' hb) (by decide) (by decide) (by decide) ilpfA_pins⟩
  · exact ⟨dcMem_alloc hP.alloc hc hx.1, dcIdx_alloc hP.alloc hc hx.2⟩
  · exact ⟨dcMem_i1 hP.i1 hc hx.1, hx.2.frame (i1lF_call hP.i1 hc) (fun b hb h' => i1lA_idx b h' hb)
      (by decide) (by decide) (by decide) i1lA_pins⟩

/-- **A call of `dc0Fns` keeps the `instantiate1Lift` memo** too. -/
theorem dc0_keepI1 {p : Prog} (hP : DcLeafProg p) {f : FnName} (hf : f ∈ dc0Fns) {n : Nat}
    {vs : List Word} {m m' : Mem} {r : List Word} (h : callW p n f vs m = some (r, m'))
    (hM : I1Memo m) : I1Memo m' := by
  refine callW_keepL (P := I1Memo) hP.closed.c0 (fun _ _ hfr hx => hx.frameDc hfr) ?_ hf h hM
  intro g hg n vs m₁ r m₂ hc hx
  simp only [dc0Leaves, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact I1Memo.frame hx (maLeaf_frame hP.ma hc) (by decide) (by decide)
  · exact I1Memo.frame hx (instLPCore_frame hP.ilpf hc) (by decide) (by decide)
  · rw [erecAlloc_mem hP.alloc hc]
    rcases erAllocMem_frame m₁ (vs.getD 0 0) with hfr | hfr
    · exact I1Memo.frame hx hfr (by simp) (by decide)
    · exact I1Memo.frame hx hfr (by simp) (by decide)

end L.Ind
