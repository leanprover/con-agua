module

import ConAgua.Checker.LoopProgTac
meta import ConAgua.Checker.LoopProgTac
public import ConAgua.Checker.Prog
import all ConAgua.Arena.ConsLib
import all ConAgua.Arena.NNumStore
import all ConAgua.Arena.ParamStore
import all ConAgua.Arena.RomLevels
import all ConAgua.Arena.RomPins
import all ConAgua.Arena.Abs1
import all ConAgua.Arena.AppStore
import all ConAgua.Arena.ArRange
import all ConAgua.Arena.ArRangeSpec
import all ConAgua.Arena.BVarStore
import all ConAgua.Arena.BvarB
import all ConAgua.Arena.CheckerL
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
# The checker's program under the pin-data substitution: names, levels, reserved pins

`NameProg`, `LevelsProg` and `IrpProg` (at offset `0`) for `Prog.subPB bs checkerProg`, every `bs`:
one lookup per function by `chk_lk` (`lkN`: no pin-data read; `lkR`: a reader, `romName_subPB`, …).
-/

namespace L.Checker

open L L.Rom L.Arena L.Ind

set_option maxRecDepth 100000

theorem checkerProg_nameProg (bs : List UInt8) : NameProg bs (Prog.subPB bs checkerProg) where
  rom_name := lkR bs (f := "rom_name") (by chk_lk) (romName_subPB bs)
  rom_u64 := lkR bs (f := "rom_u64") (by chk_lk) (romU64PB_subPB bs)
  rom_put := lkR bs (f := "rom_put") (by chk_lk) (romPutPB_subPB bs)
  nanon_find := lkN bs (f := "nanon_find") (by chk_lk) rfl
  nanon_push := lkN bs (f := "nanon_push") (by chk_lk) rfl
  intern_nanon := lkN bs (f := "intern_nanon") (by chk_lk) rfl
  lit_hash := lkN bs (f := "lit_hash") (by chk_lk) rfl
  limbs_eq := lkN bs (f := "limbs_eq") (by chk_lk) rfl
  nstr_match := lkN bs (f := "nstr_match") (by chk_lk) rfl
  nstr_find := lkN bs (f := "nstr_find") (by chk_lk) rfl
  nstr_push := lkN bs (f := "nstr_push") (by chk_lk) rfl
  intern_nstr := lkN bs (f := "intern_nstr") (by chk_lk) rfl
  nnum_find := lkN bs (f := "nnum_find") (by chk_lk) rfl
  nnum_push := lkN bs (f := "nnum_push") (by chk_lk) rfl
  intern_nnum := lkN bs (f := "intern_nnum") (by chk_lk) rfl
  no_st8 := checkerProg_subPB_noSt8 bs

theorem checkerProg_levelProg (bs : List UInt8) : LevelProg bs (Prog.subPB bs checkerProg) where
  toNameProg := checkerProg_nameProg bs
  rom_level := lkR bs (f := "rom_level") (by chk_lk) (romLevel_subPB bs)
  zero_find := lkN bs (f := "zero_find") (by chk_lk) rfl
  zero_push := lkN bs (f := "zero_push") (by chk_lk) rfl
  intern_zero := lkN bs (f := "intern_zero") (by chk_lk) rfl
  succ_find := lkN bs (f := "succ_find") (by chk_lk) rfl
  succ_push := lkN bs (f := "succ_push") (by chk_lk) rfl
  intern_succ := lkN bs (f := "intern_succ") (by chk_lk) rfl
  max_find := lkN bs (f := "max_find") (by chk_lk) rfl
  max_push := lkN bs (f := "max_push") (by chk_lk) rfl
  intern_max := lkN bs (f := "intern_max") (by chk_lk) rfl
  imax_find := lkN bs (f := "imax_find") (by chk_lk) rfl
  imax_push := lkN bs (f := "imax_push") (by chk_lk) rfl
  intern_imax := lkN bs (f := "intern_imax") (by chk_lk) rfl
  param_find := lkN bs (f := "param_find") (by chk_lk) rfl
  param_push := lkN bs (f := "param_push") (by chk_lk) rfl
  intern_param := lkN bs (f := "intern_param") (by chk_lk) rfl

theorem checkerProg_levelsProg (bs : List UInt8) : LevelsProg bs (Prog.subPB bs checkerProg) where
  toLevelProg := checkerProg_levelProg bs
  stk_push := lkN bs (f := "stk_push") (by chk_lk) rfl
  rom_lvls_go := lkN bs (f := "rom_lvls_go") (by chk_lk) rfl
  stk_pool := lkN bs (f := "stk_pool") (by chk_lk) rfl
  ls_match := lkN bs (f := "ls_match") (by chk_lk) rfl
  ls_find := lkN bs (f := "ls_find") (by chk_lk) rfl
  ls_push := lkN bs (f := "ls_push") (by chk_lk) rfl
  intern_ls := lkN bs (f := "intern_ls") (by chk_lk) rfl
  rom_levels := lkN bs (f := "rom_levels") (by chk_lk) rfl

/-- **The reserved pins' program hypothesis** for the substituted checker program. -/
theorem checkerProg_irp (bs : List UInt8) : IrpProg bs 0 (Prog.subPB bs checkerProg) where
  toNameProg := checkerProg_nameProg bs
  rom_names_to := lkN bs (f := "rom_names_to") (by chk_lk) rfl
  ls_match := lkN bs (f := "ls_match") (by chk_lk) rfl
  ls_find := lkN bs (f := "ls_find") (by chk_lk) rfl
  ls_push := lkN bs (f := "ls_push") (by chk_lk) rfl
  intern_ls := lkN bs (f := "intern_ls") (by chk_lk) rfl
  zero_find := lkN bs (f := "zero_find") (by chk_lk) rfl
  zero_push := lkN bs (f := "zero_push") (by chk_lk) rfl
  intern_zero := lkN bs (f := "intern_zero") (by chk_lk) rfl
  succ_find := lkN bs (f := "succ_find") (by chk_lk) rfl
  succ_push := lkN bs (f := "succ_push") (by chk_lk) rfl
  intern_succ := lkN bs (f := "intern_succ") (by chk_lk) rfl
  sort_find := lkN bs (f := "sort_find") (by chk_lk) rfl
  sort_push := lkN bs (f := "sort_push") (by chk_lk) rfl
  intern_sort := lkN bs (f := "intern_sort") (by chk_lk) rfl
  irp := lkN bs (f := "intern_reserved_pins") (by chk_lk) rfl

end L.Checker
