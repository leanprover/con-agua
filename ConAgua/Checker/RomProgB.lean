module

import ConAgua.Checker.RomProgA
meta import ConAgua.Checker.RomProgA
import ConAgua.Checker.LoopProgTac
public import ConAgua.Checker.Prog
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
import all ConAgua.Arena.NatSized

@[expose] public section

/-!
# The checker's program under the pin-data substitution: expressions, items, pin sets

`ExprProg`, `ItemsProg` and `PinProg` for `Prog.subPB bs checkerProg`, every `bs`: one
lookup per function by `chk_lk` (`lkN`, `lkR`).
-/

namespace L.Checker

open L L.Rom L.Arena L.Ind

set_option maxRecDepth 100000

theorem checkerProg_exprProg (bs : List UInt8) : ExprProg bs (Prog.subPB bs checkerProg) where
  toLevelsProg := checkerProg_levelsProg bs
  rom_expr := lkR bs (f := "rom_expr") (by chk_lk) (romExpr_subPB bs)
  rom_ex_leaf := lkN bs (f := "rom_ex_leaf") (by chk_lk) rfl
  memo_get := lkN bs (f := "memo_get") (by chk_lk) rfl
  rom_ex_ref := lkN bs (f := "rom_ex_ref") (by chk_lk) rfl
  rom_ex_one := lkN bs (f := "rom_ex_one") (by chk_lk) rfl
  rom_ex_two := lkN bs (f := "rom_ex_two") (by chk_lk) rfl
  memo_push := lkN bs (f := "memo_push") (by chk_lk) rfl
  rset_find := lkN bs (f := "rset_find") (by chk_lk) rfl
  rset_put := lkN bs (f := "rset_put") (by chk_lk) rfl
  lit_match := lkN bs (f := "lit_match") (by chk_lk) rfl
  lit_find := lkN bs (f := "lit_find") (by chk_lk) rfl
  lit_push := lkN bs (f := "lit_push") (by chk_lk) rfl
  intern_lit := lkN bs (f := "intern_lit") (by chk_lk) rfl
  rom_lit := lkN bs (f := "rom_lit") (by chk_lk) rfl
  bvar_find := lkN bs (f := "bvar_find") (by chk_lk) rfl
  bvar_push := lkN bs (f := "bvar_push") (by chk_lk) rfl
  intern_bvar := lkN bs (f := "intern_bvar") (by chk_lk) rfl
  sort_find := lkN bs (f := "sort_find") (by chk_lk) rfl
  sort_push := lkN bs (f := "sort_push") (by chk_lk) rfl
  intern_sort := lkN bs (f := "intern_sort") (by chk_lk) rfl
  const_find := lkN bs (f := "const_find") (by chk_lk) rfl
  const_push := lkN bs (f := "const_push") (by chk_lk) rfl
  intern_const := lkN bs (f := "intern_const") (by chk_lk) rfl
  fvar_find := lkN bs (f := "fvar_find") (by chk_lk) rfl
  fvar_push := lkN bs (f := "fvar_push") (by chk_lk) rfl
  intern_fvar := lkN bs (f := "intern_fvar") (by chk_lk) rfl
  der_b := lkN bs (f := "der_b") (by chk_lk) rfl
  app_find := lkN bs (f := "app_find") (by chk_lk) rfl
  app_push := lkN bs (f := "app_push") (by chk_lk) rfl
  intern_app := lkN bs (f := "intern_app") (by chk_lk) rfl
  mk_app := lkN bs (f := "mk_app") (by chk_lk) rfl
  lam_find := lkN bs (f := "lam_find") (by chk_lk) rfl
  lam_push := lkN bs (f := "lam_push") (by chk_lk) rfl
  intern_lam := lkN bs (f := "intern_lam") (by chk_lk) rfl
  mk_lam := lkN bs (f := "mk_lam") (by chk_lk) rfl
  forall_find := lkN bs (f := "forall_find") (by chk_lk) rfl
  forall_push := lkN bs (f := "forall_push") (by chk_lk) rfl
  intern_forall := lkN bs (f := "intern_forall") (by chk_lk) rfl
  mk_forall := lkN bs (f := "mk_forall") (by chk_lk) rfl
  letE_find := lkN bs (f := "letE_find") (by chk_lk) rfl
  letE_push := lkN bs (f := "letE_push") (by chk_lk) rfl
  intern_letE := lkN bs (f := "intern_letE") (by chk_lk) rfl
  mk_let := lkN bs (f := "mk_let") (by chk_lk) rfl
  proj_find := lkN bs (f := "proj_find") (by chk_lk) rfl
  proj_push := lkN bs (f := "proj_push") (by chk_lk) rfl
  intern_proj := lkN bs (f := "intern_proj") (by chk_lk) rfl
  mk_proj := lkN bs (f := "mk_proj") (by chk_lk) rfl

theorem checkerProg_itemsProg (bs : List UInt8) : ItemsProg bs (Prog.subPB bs checkerProg) where
  toExprProg := checkerProg_exprProg bs
  rom_items := lkR bs (f := "rom_items") (by chk_lk) (romItems_subPB bs)
  rset_clear := lkN bs (f := "rset_clear") (by chk_lk) rfl

/-- **The pin-data stage's program hypothesis** for the substituted checker program. -/
theorem checkerProg_pinProg (bs : List UInt8) : PinProg bs (Prog.subPB bs checkerProg) where
  toItemsProg := checkerProg_itemsProg bs
  pb_check := lkR bs (f := "pb_check") (by chk_lk) rfl
  rom_exprs_to := lkN bs (f := "rom_exprs_to") (by chk_lk) rfl
  rom_pins_to := lkN bs (f := "rom_pins_to") (by chk_lk) rfl
  rom_lists_to := lkN bs (f := "rom_lists_to") (by chk_lk) rfl
  rom_tpairs_to := lkN bs (f := "rom_tpairs_to") (by chk_lk) rfl
  rom_tpins_to := lkN bs (f := "rom_tpins_to") (by chk_lk) rfl
  rom_sets_to := lkN bs (f := "rom_sets_to") (by chk_lk) rfl
  intern_pin_sets := lkN bs (f := "intern_pin_sets") (by chk_lk) rfl
  rom_pin_sets := lkN bs (f := "rom_pin_sets") (by chk_lk) rfl
  intern_all_pins := lkR bs (f := "intern_all_pins") (by chk_lk) rfl
  erec_alloc := lkN bs (f := "erec_alloc") (by chk_lk) rfl
  iw_alloc := lkN bs (f := "iw_alloc") (by chk_lk) rfl
  er_copy := lkN bs (f := "er_copy") (by chk_lk) rfl
  er_to_iw := lkN bs (f := "er_to_iw") (by chk_lk) rfl
  erec_put := lkN bs (f := "erec_put") (by chk_lk) rfl

end L.Checker
