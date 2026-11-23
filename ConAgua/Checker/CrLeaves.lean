module

public import ConAgua.Arena.CrOKFrame
public import ConAgua.Checker.Prog
import ConAgua.Checker.LoopProg
import ConAgua.Checker.LoopProgTac
meta import ConAgua.Checker.LoopProg
meta import ConAgua.Checker.LoopProgTac
import all ConAgua.Arena.Abs1
import all ConAgua.Arena.BasisL
import all ConAgua.Arena.IndDeclConsts
import all ConAgua.Arena.IndStream
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
import all ConAgua.Arena.IndSum
import all ConAgua.Arena.Env
import all ConAgua.Arena.NatSized

@[expose] public section

/-!
# The leaves of `imFns` keep `CrOK` at the checker's program

`checkerProg_crLeavesPB`: `CrLeaves` (`Arena/CrOKFrame.lean`) at the substituted checker program,
the `CrKeep.leaves` field of the inductive arm's bundle. `consts_resolve_ffast` by its model
(`CrfF`, a `prog_bundle` lookup), `struct_used_later` by its call closure's write set
(`sulFns`: no write to `CRM` or `CTL[158]`, `checkerProg_sulW`).
-/

namespace L.Checker

open L L.Arena L.Compiler

/-- `struct_used_later`'s call closure in the checker's program. -/
def sulFns : List FnName :=
  ["struct_used_later", "has_loose_bvar_in", "has_loose_bvar_in_go", "strip_pis", "has_loose_b_var_b_fast", "e_view", "iw_alloc", "hb_clear",
    "has_loose_b_var_b_go", "bvar_b", "hb_find", "has_loose_b_var_b_ins", "der_bv", "bb_memo",
    "hb_put", "bm_clear", "bb_go", "bm_find", "bb_node", "bm_put"]

names_tree sulTree : sulFns

/-- The arrays of `crA`, as a test. -/
def crPa (b : TieredArray) : Bool := checkerWordArrays.contains b && b != L.Stubs.CRM

/-- The `CTL` words of `crC`, as a test. -/
def crPc (x : Word) : Bool := decide (x.toNat < 1024) && x.toNat != 158

theorem crPa_mem (b : TieredArray) (h : crPa b = true) : b ∈ crA := by
  simp only [crPa, Bool.and_eq_true, bne_iff_ne, ne_eq, List.contains_iff_mem] at h
  simp only [crA, List.mem_filter, decide_eq_true_eq]
  exact ⟨h.1, h.2⟩

theorem crPc_mem (x : Word) (h : crPc x = true) : x ∈ crC := by
  simp only [crPc, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  simp only [crC, List.mem_filter, List.mem_map, List.mem_range, decide_eq_true_eq]
  refine ⟨x.toNat, ⟨h.1, h.2⟩, UInt64.ofNat_toNat⟩

/-- Every function of the checker passes `struct_used_later`'s per-function check. -/
prog_all checkerProg_sulChk : checkerProg (wsChk CTL crPa crPc sulTree)

theorem checkerProg_sulW : closedA checkerProg crA crC sulFns = true :=
  closedW_of_all sulTree.eq crPa_mem crPc_mem checkerProg_sulChk

theorem checkerProg_crLeavesPB (bs : List UInt8) : CrLeaves (Prog.subPB bs checkerProg) :=
  crLeaves_of (by prog_bundle [] : L.Ind.CrfF (Prog.subPB bs checkerProg))
    (closedW_subPB bs checkerProg_sulW) (by decide)

end L.Checker
