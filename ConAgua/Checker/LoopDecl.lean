module

public import ConAgua.Checker.Prog
public import ConAgua.Arena.DeclArmLoop
public import ConAgua.Arena.DeclDivModSpec.RomPinSets
public import ConAgua.Arena.DeclNatGateSpec
meta import ConAgua.Checker.Prog
meta import ConAgua.Arena.DeclArmLoop
meta import ConAgua.Arena.DeclDivModSpec.RomPinSets
meta import ConAgua.Arena.DeclNatGateSpec
import all ConAgua.Arena.Abs1
import all ConAgua.Arena.AppStore
import all ConAgua.Arena.ArRange
import all ConAgua.Arena.ArRangeSpec
import all ConAgua.Arena.BVarStore
import all ConAgua.Arena.BvarB
import all ConAgua.Arena.CheckerL
import all ConAgua.Arena.ConsLib
import all ConAgua.Arena.ConsPresize
import all ConAgua.Arena.ConstStore
import all ConAgua.Arena.ConstsResolveF
import all ConAgua.Arena.CoreCaches
import all ConAgua.Arena.CoreLevels
import all ConAgua.Arena.CoreWalks
import all ConAgua.Arena.DeclAndPin
import all ConAgua.Arena.DeclApd
import all ConAgua.Arena.DeclArms
import all ConAgua.Arena.DeclArmsCanon
import all ConAgua.Arena.DeclArmsNat
import all ConAgua.Arena.DeclStep
import all ConAgua.Arena.DefEq
import all ConAgua.Arena.Env
import all ConAgua.Arena.ExprMk
import all ConAgua.Arena.FVarRange
import all ConAgua.Arena.FVarStore
import all ConAgua.Arena.ForallStore
import all ConAgua.Arena.Freeze
import all ConAgua.Arena.HasFvar
import all ConAgua.Arena.ImaxStore
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.IndInstall
import all ConAgua.Arena.IndParts
import all ConAgua.Arena.IotaFrame
import all ConAgua.Arena.IotaRel
import all ConAgua.Arena.JustifyIface
import all ConAgua.Arena.Needs
import all ConAgua.Arena.Justify
import all ConAgua.Arena.JustifySide
import all ConAgua.Checker.CompareEntry
import all ConAgua.Arena.FreezeCmp
import all ConAgua.Checker.CmpSeqEntry
import all ConAgua.Arena.IndPos
import all ConAgua.Arena.IndPos2
import all ConAgua.Arena.IndSum
import all ConAgua.Arena.Infer
import all ConAgua.Arena.InferFieldSort
import all ConAgua.Arena.Inst1
import all ConAgua.Arena.Inst1Spec
import all ConAgua.Arena.InstLP
import all ConAgua.Arena.InstList
import all ConAgua.Arena.InstListSpec
import all ConAgua.Arena.Knot
import all ConAgua.Arena.LamStore
import all ConAgua.Arena.LetStore
import all ConAgua.Arena.LevelApd
import all ConAgua.Arena.LevelEquiv
import all ConAgua.Arena.LevelHeap
import all ConAgua.Arena.LevelIntern
import all ConAgua.Arena.LevelLeq
import all ConAgua.Arena.LevelSimp
import all ConAgua.Arena.LevelStore
import all ConAgua.Arena.LevelSubst
import all ConAgua.Arena.LevelSubstL
import all ConAgua.Arena.LevelSubstLP
import all ConAgua.Arena.LevelZero
import all ConAgua.Arena.LiftL
import all ConAgua.Arena.LsStore
import all ConAgua.Arena.MaxStore
import all ConAgua.Arena.MemoLib
import all ConAgua.Arena.NAnonStore
import all ConAgua.Arena.NNumStore
import all ConAgua.Arena.NStrStore
import all ConAgua.Arena.NatAdd
import all ConAgua.Arena.NatLeaf
import all ConAgua.Arena.NatArms
import all ConAgua.Arena.NatBits
import all ConAgua.Arena.NatCmp
import all ConAgua.Arena.NatDiv
import all ConAgua.Arena.NatDivKstep
import all ConAgua.Arena.NatDivSubmul
import all ConAgua.Arena.NatDivWord
import all ConAgua.Arena.NatGcd
import all ConAgua.Arena.NatMul
import all ConAgua.Arena.NatSized
import all ConAgua.Arena.NatPow
import all ConAgua.Arena.NatShl
import all ConAgua.Arena.NatShr
import all ConAgua.Arena.NatSub
import all ConAgua.Arena.ParamStore
import all ConAgua.Arena.Pins
import all ConAgua.Arena.Prelude
import all ConAgua.Arena.ProjStore
import all ConAgua.Arena.PropRead
import all ConAgua.Arena.RecCheck
import all ConAgua.Arena.RecClass
import all ConAgua.Arena.RecGen
import all ConAgua.Arena.Refine
import all ConAgua.Arena.Rom
import all ConAgua.Arena.RomCI
import all ConAgua.Arena.RomExpr
import all ConAgua.Arena.RomItems
import all ConAgua.Arena.RomLevel
import all ConAgua.Arena.RomLevels
import all ConAgua.Arena.RomPins
import all ConAgua.Arena.Scratch
import all ConAgua.Arena.SortStore
import all ConAgua.Arena.Store
import all ConAgua.Arena.StrLit
import all ConAgua.Arena.StripTele
import all ConAgua.Arena.StubInd
import all ConAgua.Arena.StubNames
import all ConAgua.Arena.TeleLift
import all ConAgua.Arena.Walk
import all ConAgua.Arena.WalkLeaves
import all ConAgua.Arena.WalkLift
import all ConAgua.Arena.WalkScope
import all ConAgua.Arena.WhnfCore
import all ConAgua.Arena.WhnfCoreApp
import all ConAgua.Arena.WhnfDelta
import all ConAgua.Arena.WhnfEntry
import all ConAgua.Arena.WhnfIota
import all ConAgua.Arena.WhnfIotaRec
import all ConAgua.Arena.WhnfM2C
import all ConAgua.Arena.WhnfProj
import all ConAgua.Arena.WhnfSpineArgs
import all ConAgua.Arena.WhnfSpineRefine
import all ConAgua.Arena.ZeroStore
import all ConAgua.Checker.Entry
import all ConAgua.Checker.Hoist
import all ConAgua.Checker.Prelude
import all ConAgua.Checker.Presize
import all ConAgua.Front.Apply
import all ConAgua.Front.ApplyDecl
import all ConAgua.Front.ApplyExpr
import all ConAgua.Front.Driver
import all ConAgua.Front.Fields
import all ConAgua.Front.FieldsDecl
import all ConAgua.Front.IdTable
import all ConAgua.Front.IndApply
import all ConAgua.Front.IndFields
import all ConAgua.Front.Line
import all ConAgua.Front.LineRec
import all ConAgua.Front.NatDec
import all ConAgua.Front.Unescape
import all ConAgua.L.Examples
import all ConAgua.Rom.CIRead
import all ConAgua.Rom.PinRead
import all ConAgua.Rom.PinReadSpec
import all ConAgua.Scan.Key
import all ConAgua.Scan.Leaves
import all ConAgua.Scan.Line
import all ConAgua.Scan.Lit
import all ConAgua.Scan.Member
import all ConAgua.Scan.Records
import all ConAgua.Scan.Str
import all ConAgua.Scan.Utf8
import all ConAgua.Scan.Values
import all ConAgua.Rom.CIConst
import all ConAgua.Arena.BasisL

@[expose] public section

/-!
# The declaration texts' write set in the checker's program (lane `loopt2`)

The declaration loop's program hypotheses (`CvgProg`, `IvProg`, `ArmProg`, `CheckDeclProg`'s
`natText` and `dgClosed`) ask for a step's write set (`stepA`, `stepC`: no `PEND`, `DECL`, `DLP`,
promotion memos, `CTL[130]`, `CTL[140‥147]`, `CTL[150]`, `CTL[151]`) on a call-closed superset of
their function lists (`StepIn`). In the checker's program the texts' open callees (`openFns`: the
core's entry points, the walks, the ROM readers) are real code, so the superset is the texts'
lists, the core's (`stageCoreFns`) and the open callees' own callees (`declExtFns`). Decided by
per-chunk kernel checks as `LoopCore.lean`.
-/

namespace L.Checker

open L.Arena L.Ind L.Compiler
open L.Front (DECL DLP)

/-- The functions the declaration texts reach in the checker's program outside the texts' lists
and `stageCoreFns`: the callees of the walks, of the ROM readers and of the `Nat.div`-family gate's
certificate checks (computed from `checkerProg`'s call graph; the check below fails if one is
missing). -/
def declExtFns : List FnName :=
  ["apd_clear", "has_loose_bvar_in", "has_loose_bvar_in_go", "alpd_go", "apd_find", "lv_apd", "lv_mem", "alpd_ls", "apd_put", "rci_slot",
   "rom_u64", "rci_fresh", "rset_clear", "rci_cv", "rom_name", "rom_put", "rci_name_sl",
   "rci_names_to", "rom_expr", "rom_ex_ref", "memo_get", "rom_ex_leaf", "rom_level", "rom_levels",
   "rom_lvls_go", "stk_push", "stk_pool", "rom_ex_one", "memo_push", "rset_find", "rset_put",
   "rom_ex_two", "rci_ci", "rci_caps", "rci_rules_to", "rci_rule", "rci_lvls_to", "rom_exprs_to",
   "rci_block", "rci_block_to", "div_mod_env_guard", "bool_ctor_typed", "check_div_mod_pin_loop",
   "div_mod_pin_guard", "div_mod_decl_pin", "div_mod_slot", "div_mod_certs_guard",
   "div_mod_cert_stmts", "cert_ctx", "nat_var", "nat_one", "cert_ctx_pins", "cert_ctx_main",
   "div_mod_cert_stmts_at", "cert_gcd", "cert_guard", "eq_at1", "sl_new1", "intern_ls_iw",
   "cert_two_eqs", "cert_eq", "stmt1", "rec3", "cert_shift_left", "cert_shift_right", "cert_land",
   "cert_halves", "cert_lor", "cert_lor_rhs", "cert_xor", "cert_xor_rhs", "cert_div_mod",
   "cert_rec_rhs", "cert_div_mod_guards", "cert_div_mod_eqs", "div_mod_cert_proofs",
   "div_mod_certs_guard_go", "div_mod_cert_guard", "subst_const_all", "subst_const0_list",
   "consts_resolve_all", "check_div_mod_pin_at", "check_div_mod_certs", "div_mod_cert_applied",
   "ground_guards", "div_mod_type_pins", "type_pins_guard", "type_pin_guard", "type_pin_stored",
   "check_type_pins", "check_div_mod_pin_value", "intern_nstr", "nstr_find", "nstr_match",
   "nstr_push",
   -- lane `stubs`: the callees of `intern_ls_iw` and `consts_resolve_ffast`
   "pool_room", "iw_pool", "crf_go", "cr_leaf", "cr_lit_pins", "pin_found", "crm_find", "crm_put",
   "crm_clear", "is_str_lit",
   "unresolved_consts_error", "has_str_lit_go", "ue_mentions_go",
   -- ronsync2: the quotient pins at a stream's names, the core's leaves, the definition arm
   "char_of_nat_ty_ok", "char_ty_ok", "check_decl_defn", "check_div_mod_pin_at_fe2",
   "check_quot_record", "check_reduce_pin_pre", "check_structural_nat_pin",
   "check_structural_nat_pin_at_fe2", "ci_at_lps", "cv_at_lps", "env_pop_temp", "eq_stored",
   "er_copy_er", "fire_levels_at", "has_loose_b_var_b_fast", "has_loose_b_var_b_go",
   "has_loose_b_var_b_ins", "hb_clear", "hb_find", "hb_put", "list_cons_ty_ok", "list_nil_ty_ok",
   "list_ty_ok", "lit_shape_ok", "nat_ind_at_cv", "nat_ind_ok", "nat_op_name", "nat_succ_at_cv",
   "nat_succ_ok", "nat_zero_at_cv", "nat_zero_ok",
   "open_pis_at_fvars_f", "param_levels", "param_levels_go", "pin_range_has", "quot_at",
   "quot_pin", "quot_preds_ok", "rom_ex_leaf_c", "rom_ex_one_c", "rom_ex_ref_c", "rom_ex_two_c",
   "rom_expr_c", "rom_exprs_to_c", "rom_level_c", "rom_levels_c", "rom_lvls_go_c", "rom_name_c",
   "rom_put_c", "rom_u64_c", "rules_at_lps_go", "sl_get", "spn_to_er", "spn_to_iw", "str_cv",
   "str_param_sort", "string_of_list_ty_ok", "string_ty_ok", "strip_pis", "struct_used_later",
   "value_guards"]

/-- The call-closed superset: the texts' lists, their open callees' callees and the core. -/
def declLoopFns : List FnName :=
  cvgFns ++ ivFns ++ armFns ++ natGateFns ++ dgFns ++ declExtFns ++ stageCoreFns

/-- `declLoopFns` as a tree of name codes. -/
names_tree declLoopTree : declLoopFns

/-- The arrays of `stepA`, as a test. -/
def stepPa (a : TieredArray) : Bool :=
  checkerWordArrays.contains a && a != DECL && a != DLP

/-- The `CTL` words of `stepC`, as a test. -/
def stepPc (w : Word) : Bool :=
  decide (w.toNat < 1024) && w.toNat != 150 && w.toNat != 151 &&
    (decide (w.toNat < 140) || decide (147 < w.toNat))

theorem stepPa_mem (a : TieredArray) (h : stepPa a = true) : a ∈ stepA := by
  simp only [stepPa, Bool.and_eq_true, bne_iff_ne, ne_eq,
    List.contains_iff_mem] at h
  simp only [stepA, List.mem_filter, decide_eq_true_eq]
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem stepPc_mem (w : Word) (h : stepPc w = true) : w ∈ stepC := by
  simp only [stepPc, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne,
    ne_eq] at h
  simp only [stepC, List.mem_map, List.mem_filter, List.mem_range]
  refine ⟨w.toNat, ⟨h.1.1.1, ?_⟩, UInt64.ofNat_toNat⟩
  simp only [decide_eq_true_eq]
  exact ⟨h.1.1.2, h.1.2, h.2⟩

/-- Every function of the checker passes the declaration texts' per-function check. -/
prog_all checkerProg_declChk : checkerProg (wsChk CTL stepPa stepPc declLoopTree)

theorem checkerProg_declClosed : closedA checkerProg stepA stepC declLoopFns = true :=
  closedW_of_all declLoopTree.eq stepPa_mem stepPc_mem checkerProg_declChk

theorem checkerProg_stepIn {fs : List FnName} (h : ∀ f ∈ fs, f ∈ declLoopFns) :
    StepIn checkerProg fs :=
  ⟨_, h, checkerProg_declClosed⟩

theorem checkerProg_cvgIn : StepIn checkerProg cvgFns :=
  checkerProg_stepIn fun _ h => by simp only [declLoopFns, List.mem_append]; simp [h]

theorem checkerProg_ivIn : StepIn checkerProg ivFns :=
  checkerProg_stepIn fun _ h => by simp only [declLoopFns, List.mem_append]; simp [h]

theorem checkerProg_armIn : StepIn checkerProg armFns :=
  checkerProg_stepIn fun _ h => by simp only [declLoopFns, List.mem_append]; simp [h]

theorem checkerProg_natGateIn : StepIn checkerProg natGateFns :=
  checkerProg_stepIn fun _ h => by simp only [declLoopFns, List.mem_append]; simp [h]

theorem checkerProg_dgIn : StepIn checkerProg dgFns :=
  checkerProg_stepIn fun _ h => by simp only [declLoopFns, List.mem_append]; simp [h]

end L.Checker
