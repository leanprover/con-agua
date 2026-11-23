module

public import ConAgua.Checker.PreLoopWSBase
meta import ConAgua.Checker.PreLoopWSBase
import all ConAgua.Arena.Abs1
import all ConAgua.Arena.AppStore
import all ConAgua.Arena.ArRange
import all ConAgua.Arena.ArRangeSpec
import all ConAgua.Arena.BVarStore
import all ConAgua.Arena.BasisL
import all ConAgua.Arena.BvarB
import all ConAgua.Arena.CheckerL
import all ConAgua.Arena.ConsLib
import all ConAgua.Arena.ConsPresize
import all ConAgua.Arena.ConstStore
import all ConAgua.Arena.ConstsResolveF
import all ConAgua.Arena.CoreCaches
import all ConAgua.Arena.CoreLevels
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
import all ConAgua.Arena.IndDeclConsts
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.IndInstall
import all ConAgua.Arena.IndParts
import all ConAgua.Arena.IndPos
import all ConAgua.Arena.IndPos2
import all ConAgua.Arena.IndStream
import all ConAgua.Arena.IndSum
import all ConAgua.Arena.Infer
import all ConAgua.Arena.Inst1
import all ConAgua.Arena.Inst1Spec
import all ConAgua.Arena.InstLP
import all ConAgua.Arena.InstList
import all ConAgua.Arena.InstListSpec
import all ConAgua.Arena.IotaFrame
import all ConAgua.Arena.IotaRel
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
import all ConAgua.Arena.NatArms
import all ConAgua.Arena.NatBits
import all ConAgua.Arena.NatCmp
import all ConAgua.Arena.NatDiv
import all ConAgua.Arena.NatDivKstep
import all ConAgua.Arena.NatDivSubmul
import all ConAgua.Arena.NatDivWord
import all ConAgua.Arena.NatGcd
import all ConAgua.Arena.NatLeaf
import all ConAgua.Arena.NatMul
import all ConAgua.Arena.NatPow
import all ConAgua.Arena.NatShl
import all ConAgua.Arena.NatShr
import all ConAgua.Arena.NatSized
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
import all ConAgua.Rom.CIConst
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

@[expose] public section

/-!
# The pre-loop stages' write sets, part 0 (lane `pipeline`)

The stages `cap_check`, `pb_check`, `intern_reserved_pins`, `intern_all_pins` of `PreLoopWSStages.lean` (generated by
`scripts/preloop_ws.py`). Do not edit by hand: rerun the script.
-/

namespace L.Checker

open L L.Arena L.Compiler
open Std.WP
open scoped Lean.Order

/-! ## `cap_check` -/

/-- The call closure of `cap_check` in `checkerProg` (1 functions). -/
def stageFns_cap_check : List FnName := [
  "cap_check"]

/-- The word arrays (other than `CTL`) the functions of `stageFns_cap_check` store
into. -/
def stageA_cap_check : List TieredArray :=
  []

/-- The `CTL` words the functions of `stageFns_cap_check` store into. -/
def stageC_cap_check : List Word := []

names_tree stageTree_cap_check : stageFns_cap_check

prog_all checkerProg_stageChk_cap_check : checkerProg
  (wsChk CTL (fun a => stageA_cap_check.contains a)
    (fun w => stageC_cap_check.contains w) stageTree_cap_check)

theorem checkerProg_stageClosed_cap_check :
    closedA checkerProg stageA_cap_check stageC_cap_check
      stageFns_cap_check = true :=
  closedW_of_all stageTree_cap_check.eq (fun _ h => List.contains_iff_mem.mp h)
    (fun _ h => List.contains_iff_mem.mp h) checkerProg_stageChk_cap_check

/-- **A run of `cap_check` is a frame of its own write set.** -/
theorem stageFrame_cap_check (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "cap_check" []
    ⦃fun _ s' =>
      MemFrame stageA_cap_check stageC_cap_check s₀.mem s'.mem; ⊤⦄ :=
  memFrame_of_closed checkerProg_stageClosed_cap_check n
    (mem_of_tree stageTree_cap_check.eq "cap_check" (by decide +kernel)) s₀

/-- Of the `CTL` words 131, 132, 148, 149, 150, 151, 240, `cap_check` writes
none. -/
theorem stageC_cap_check_off :
    ∀ w : Word, w.toNat ∈ ([131, 132, 148, 149, 150, 151, 240] : List Nat) →
      w ∉ stageC_cap_check :=
  not_mem_of_toNat (by decide +kernel)

/-! ## `pb_check` -/

/-- The call closure of `pb_check` in `checkerProg` (1 functions). -/
def stageFns_pb_check : List FnName := [
  "pb_check"]

/-- The word arrays (other than `CTL`) the functions of `stageFns_pb_check` store
into. -/
def stageA_pb_check : List TieredArray :=
  []

/-- The `CTL` words the functions of `stageFns_pb_check` store into. -/
def stageC_pb_check : List Word := []

names_tree stageTree_pb_check : stageFns_pb_check

prog_all checkerProg_stageChk_pb_check : checkerProg
  (wsChk CTL (fun a => stageA_pb_check.contains a)
    (fun w => stageC_pb_check.contains w) stageTree_pb_check)

theorem checkerProg_stageClosed_pb_check :
    closedA checkerProg stageA_pb_check stageC_pb_check
      stageFns_pb_check = true :=
  closedW_of_all stageTree_pb_check.eq (fun _ h => List.contains_iff_mem.mp h)
    (fun _ h => List.contains_iff_mem.mp h) checkerProg_stageChk_pb_check

/-- **A run of `pb_check` is a frame of its own write set.** -/
theorem stageFrame_pb_check (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "pb_check" []
    ⦃fun _ s' =>
      MemFrame stageA_pb_check stageC_pb_check s₀.mem s'.mem; ⊤⦄ :=
  memFrame_of_closed checkerProg_stageClosed_pb_check n
    (mem_of_tree stageTree_pb_check.eq "pb_check" (by decide +kernel)) s₀

/-- Of the `CTL` words 131, 132, 148, 149, 150, 151, 240, `pb_check` writes
none. -/
theorem stageC_pb_check_off :
    ∀ w : Word, w.toNat ∈ ([131, 132, 148, 149, 150, 151, 240] : List Nat) →
      w ∉ stageC_pb_check :=
  not_mem_of_toNat (by decide +kernel)

/-! ## `intern_reserved_pins` -/

/-- The call closure of `intern_reserved_pins` in `checkerProg` (30 functions). -/
def stageFns_intern_reserved_pins : List FnName := [
  "intern_ls", "intern_nanon", "intern_nnum", "intern_nstr", "intern_reserved_pins", "intern_sort",
  "intern_succ", "intern_zero", "limbs_eq", "lit_hash", "ls_find", "ls_match", "ls_push",
  "nanon_find", "nanon_push", "nnum_find", "nnum_push", "nstr_find", "nstr_match", "nstr_push",
  "rom_name", "rom_names_to", "rom_put", "rom_u64", "sort_find", "sort_push", "succ_find",
  "succ_push", "zero_find", "zero_push"]

/-- The word arrays (other than `CTL`) the functions of `stageFns_intern_reserved_pins` store
into. -/
def stageA_intern_reserved_pins : List TieredArray :=
  tier0s [
  POOL, SREC, SSLOT, ZREC, ZSLOT, SOREC, SOSLOT, NAREC, NASLOT, NSREC, NSSLOT, NNREC, NNSLOT,
  LSREC, LSSLOT, SHP, LSHP, SOLP, PINS] ++
  tier1s [
  POOL, SREC, SSLOT, ZREC, ZSLOT, SOREC, SOSLOT, NAREC, NASLOT, NSREC, NSSLOT, NNREC, NNSLOT,
  LSREC, LSSLOT, SHP, LSHP, SOLP]

/-- The `CTL` words the functions of `stageFns_intern_reserved_pins` store into. -/
def stageC_intern_reserved_pins : List Word := [
  0, 6, 7, 8, 9, 16, 17, 34, 35, 36, 37, 38, 39, 40, 41]

names_tree stageTree_intern_reserved_pins : stageFns_intern_reserved_pins

prog_all checkerProg_stageChk_intern_reserved_pins : checkerProg
  (wsChk CTL (fun a => stageA_intern_reserved_pins.contains a)
    (fun w => stageC_intern_reserved_pins.contains w) stageTree_intern_reserved_pins)

theorem checkerProg_stageClosed_intern_reserved_pins :
    closedA checkerProg stageA_intern_reserved_pins stageC_intern_reserved_pins
      stageFns_intern_reserved_pins = true :=
  closedW_of_all stageTree_intern_reserved_pins.eq (fun _ h => List.contains_iff_mem.mp h)
    (fun _ h => List.contains_iff_mem.mp h) checkerProg_stageChk_intern_reserved_pins

/-- **A run of `intern_reserved_pins` is a frame of its own write set.** -/
theorem stageFrame_intern_reserved_pins (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "intern_reserved_pins" []
    ⦃fun _ s' =>
      MemFrame stageA_intern_reserved_pins stageC_intern_reserved_pins s₀.mem s'.mem; ⊤⦄ :=
  memFrame_of_closed checkerProg_stageClosed_intern_reserved_pins n
    (mem_of_tree stageTree_intern_reserved_pins.eq "intern_reserved_pins" (by decide +kernel)) s₀

/-- Of the `CTL` words 131, 132, 148, 149, 150, 151, 240, `intern_reserved_pins` writes
none. -/
theorem stageC_intern_reserved_pins_off :
    ∀ w : Word, w.toNat ∈ ([131, 132, 148, 149, 150, 151, 240] : List Nat) →
      w ∉ stageC_intern_reserved_pins :=
  not_mem_of_toNat (by decide +kernel)

/-! ## `intern_all_pins` -/

/-- The call closure of `intern_all_pins` in `checkerProg` (98 functions). -/
def stageFns_intern_all_pins : List FnName := [
  "app_find", "app_push", "bvar_find", "bvar_push", "const_find", "const_push", "der_b",
  "erec_alloc", "erec_put", "forall_find", "forall_push", "fvar_find", "fvar_push", "imax_find",
  "imax_push", "intern_all_pins", "intern_app", "intern_bvar", "intern_const", "intern_forall",
  "intern_fvar", "intern_imax", "intern_lam", "intern_letE", "intern_lit", "intern_ls",
  "intern_max", "intern_nanon", "intern_nnum", "intern_nstr", "intern_param", "intern_pin_sets",
  "intern_proj", "intern_sort", "intern_succ", "intern_zero", "lam_find", "lam_push", "letE_find",
  "letE_push", "limbs_eq", "lit_find", "lit_hash", "lit_match", "lit_push", "ls_find", "ls_match",
  "ls_push", "max_find", "max_push", "memo_get", "memo_push", "mk_app", "mk_forall", "mk_lam",
  "mk_let", "mk_proj", "nanon_find", "nanon_push", "nnum_find", "nnum_push", "nstr_find",
  "nstr_match", "nstr_push", "param_find", "param_push", "proj_find", "proj_push", "rom_ex_leaf",
  "rom_ex_one", "rom_ex_ref", "rom_ex_two", "rom_expr", "rom_exprs_to", "rom_items", "rom_level",
  "rom_levels", "rom_lists_to", "rom_lit", "rom_lvls_go", "rom_name", "rom_pins_to", "rom_put",
  "rom_sets_to", "rom_tpairs_to", "rom_tpins_to", "rom_u64", "rset_clear", "rset_find", "rset_put",
  "sort_find", "sort_push", "stk_pool", "stk_push", "succ_find", "succ_push", "zero_find",
  "zero_push"]

/-- The word arrays (other than `CTL`) the functions of `stageFns_intern_all_pins` store
into. -/
def stageA_intern_all_pins : List TieredArray :=
  tier0s [
  POOL, REC, SLOT, AREC, ASLOT, SREC, SSLOT, ZREC, ZSLOT, MREC, MSLOT, IREC, ISLOT, PREC, PSLOT,
  SOREC, SOSLOT, CREC, CSLOT, LEREC, LESLOT, BREC, BSLOT, FVREC, FVSLOT, LAREC, LASLOT, FAREC,
  FASLOT, PJREC, PJSLOT, NAREC, NASLOT, NSREC, NSSLOT, NNREC, NNSLOT, LSREC, LSSLOT, ADER, LADER,
  FADER, LEDER, PJDER, SHP, MHP, IHP, LSHP, SOLP, CLP, FVLP, EREC, Rom.RSTK, Rom.RMEMO, Rom.RSET] ++
  tier1s [
  POOL, REC, SLOT, AREC, ASLOT, SREC, SSLOT, ZREC, ZSLOT, MREC, MSLOT, IREC, ISLOT, PREC, PSLOT,
  SOREC, SOSLOT, CREC, CSLOT, LEREC, LESLOT, BREC, BSLOT, FVREC, FVSLOT, LAREC, LASLOT, FAREC,
  FASLOT, PJREC, PJSLOT, NAREC, NASLOT, NSREC, NSSLOT, NNREC, NNSLOT, LSREC, LSSLOT, ADER, LADER,
  FADER, LEDER, PJDER, SHP, MHP, IHP, LSHP, SOLP, CLP, FVLP, EREC]

/-- The `CTL` words the functions of `stageFns_intern_all_pins` store into. -/
def stageC_intern_all_pins : List Word := [
  0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 26, 27, 28,
  29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 129, 130, 131, 132, 148, 149, 150, 151]

names_tree stageTree_intern_all_pins : stageFns_intern_all_pins

prog_all checkerProg_stageChk_intern_all_pins : checkerProg
  (wsChk CTL (fun a => stageA_intern_all_pins.contains a)
    (fun w => stageC_intern_all_pins.contains w) stageTree_intern_all_pins)

theorem checkerProg_stageClosed_intern_all_pins :
    closedA checkerProg stageA_intern_all_pins stageC_intern_all_pins
      stageFns_intern_all_pins = true :=
  closedW_of_all stageTree_intern_all_pins.eq (fun _ h => List.contains_iff_mem.mp h)
    (fun _ h => List.contains_iff_mem.mp h) checkerProg_stageChk_intern_all_pins

/-- **A run of `intern_all_pins` is a frame of its own write set.** -/
theorem stageFrame_intern_all_pins (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "intern_all_pins" []
    ⦃fun _ s' =>
      MemFrame stageA_intern_all_pins stageC_intern_all_pins s₀.mem s'.mem; ⊤⦄ :=
  memFrame_of_closed checkerProg_stageClosed_intern_all_pins n
    (mem_of_tree stageTree_intern_all_pins.eq "intern_all_pins" (by decide +kernel)) s₀

/-- Of the `CTL` words 131, 132, 148, 149, 150, 151, 240, `intern_all_pins` writes
131, 132, 148, 149, 150, 151. -/
theorem stageC_intern_all_pins_off :
    ∀ w : Word, w.toNat ∈ ([240] : List Nat) →
      w ∉ stageC_intern_all_pins :=
  not_mem_of_toNat (by decide +kernel)

end L.Checker
