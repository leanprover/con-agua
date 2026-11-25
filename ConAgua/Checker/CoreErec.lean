module

public import ConAgua.Checker.Prog
public import ConAgua.Arena.CoreErec
public import ConAgua.Compiler.WriteSetSplit
public import ConAgua.Arena.LevelIntern
public import ConAgua.Arena.LevelSubstLP
meta import ConAgua.Checker.Prog
meta import ConAgua.Arena.CoreErec
meta import ConAgua.Compiler.WriteSetSplit
meta import ConAgua.Arena.LevelIntern
meta import ConAgua.Arena.LevelSubstLP
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
import all ConAgua.Arena.ProjStore
import all ConAgua.Arena.PropRead
import all ConAgua.Arena.RecCheck
import all ConAgua.Arena.RecClass
import all ConAgua.Arena.RecGen
import all ConAgua.Arena.Refine
import all ConAgua.Arena.Rom
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
import all ConAgua.Scan.Key
import all ConAgua.Scan.Leaves
import all ConAgua.Scan.Lit
import all ConAgua.Scan.Member
import all ConAgua.Scan.Records
import all ConAgua.Scan.Str
import all ConAgua.Scan.Utf8
import all ConAgua.Scan.Values
import all ConAgua.Arena.NatSized

@[expose] public section

/-!
# The checker's core leaves `EREC` alone (lane `whnf3`)

`ConAgua/Arena/CoreErec.lean`'s program hypothesis, for the checker's program: every function the
core reaches (`coreFns`) stores into arrays other than the record pool. Discharges the
`ErecKept*` hypotheses of the ι refinements at `checkerProg`.

One `decide +kernel` on `closedA checkerProg …` took 20 GB (lane `erecfix`): it is split into
per-chunk checks of the functions (`prog_all`, `Compiler/WriteSetSplit.lean`), with the function
set as a tree of name codes (`names_tree`) and the store sets as predicates.
-/

namespace L.Checker

open L.Arena L.Compiler

/-- `coreFns` as a tree of name codes. -/
names_tree coreTree : coreFns

/-- The arrays of `coreErecA`, as a test. -/
def coreErecPa (a : TieredArray) : Bool :=
  checkerWordArrays.contains a && a != EREC && a != tier1 EREC

/-- The `CTL` words of `coreErecC`, as a test. -/
def coreErecPc (w : Word) : Bool := decide (w.toNat < 256) && w != 129 && w != 130

theorem coreErecPa_mem (a : TieredArray) (h : coreErecPa a = true) : a ∈ coreErecA := by
  simp only [coreErecPa, Bool.and_eq_true, bne_iff_ne, ne_eq, List.contains_iff_mem] at h
  simp [coreErecA, List.mem_filter, h.1.1, h.1.2, h.2]

theorem coreErecPc_mem (w : Word) (h : coreErecPc w = true) : w ∈ coreErecC := by
  simp only [coreErecPc, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨hl, h1⟩, h2⟩ := h
  simp only [coreErecC, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
  refine ⟨w.toNat, ⟨hl, fun e => h1 ?_, fun e => h2 ?_⟩, UInt64.ofNat_toNat⟩ <;>
    exact UInt64.toNat_inj.mp (by simpa using e)

/-- Every function of the checker passes the core's per-function check. -/
prog_all checkerProg_coreChk : checkerProg (wsChk CTL coreErecPa coreErecPc coreTree)

theorem checkerProg_coreErec : closedA checkerProg coreErecA coreErecC coreFns = true :=
  closedW_of_all coreTree.eq coreErecPa_mem coreErecPc_mem checkerProg_coreChk

end L.Checker
