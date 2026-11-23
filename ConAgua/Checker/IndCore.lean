module

public import ConAgua.Checker.Prog
public import ConAgua.Arena.IndTwin
meta import ConAgua.Checker.Prog
meta import ConAgua.Arena.IndTwin
meta import ConAgua.Arena.LeafFrame
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

@[expose] public section

/-!
# The core leaves the stage's pools and the pins alone (lane `indproofs3`)

`ConAgua/Arena/IndTwin.lean`'s write set of the core, for the checker's program: every function
the stage's core entry points reach (`stageCoreFns`) stores into arrays other than `IW`, `EREC`,
`PINS`, and into `CTL` words other than `129`, `200`, and calls only `stageCoreFns` and the two
leaves `coreLeaves` (`struct_used_later`, `open_pis_at_fvars_f`; their bundles `UsF`, `OpfF` are
lookups, at the substituted program in `Checker/IndArm.lean`).

Split into per-chunk kernel checks as `checkerProg_coreErec` (lane `erecfix`,
`Compiler/WriteSetSplit.lean`): one `decide +kernel` on the whole closure took tens of GB.
-/

namespace L.Checker

open L.Arena L.Ind L.Compiler

/-- `stageCoreFns` as a tree of name codes. -/
names_tree stageCoreTree : stageCoreFns

/-- The arrays of `coreStageA`, as a test. -/
def coreStagePa (a : TieredArray) : Bool := checkerWordArrays.contains a && a != ↑EREC &&
  a != ↑IW && a != ↑PINS && a != ↑ILFM && a != ↑Stubs.CRM &&
  (decide (a.arr < 201) || decide (208 < a.arr)) && a != tier1 EREC

/-- The `CTL` words of `coreStageC`, as a test. -/
def coreStagePc (w : Word) : Bool := decide (w.toNat < 256) && w.toNat != 129 && w.toNat != 200 &&
  w.toNat != 52 && w.toNat != 158 && (decide (w.toNat < 202) || decide (219 < w.toNat)) &&
  w.toNat != 130

theorem coreStagePa_mem (a : TieredArray) (h : coreStagePa a = true) : a ∈ coreStageA := by
  simp only [coreStagePa, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, Bool.or_eq_true,
    List.contains_iff_mem] at h
  simp only [coreStageA, List.mem_filter, decide_eq_true_eq]
  exact ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem coreStagePc_mem (w : Word) (h : coreStagePc w = true) : w ∈ coreStageC := by
  simp only [coreStagePc, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  simp only [coreStageC, List.mem_map, List.mem_filter, List.mem_range]
  exact ⟨w.toNat, ⟨h.1.1.1.1.1.1, by simp only [decide_eq_true_eq]; omega⟩, UInt64.ofNat_toNat⟩

/-- `stageCoreFns` and the leaves, the callee tree of the check. -/
names_tree stageCoreCallTree : stageCoreFns ++ coreLeaves

/-- Every function of the checker passes the stage core's per-function check with the leaves. -/
prog_all checkerProg_stageChk : checkerProg (wsChkL CTL coreStagePa coreStagePc stageCoreTree stageCoreCallTree)

/-- **The core's write set with its leaves**, at the checker's program. -/
theorem checkerProg_coreStageW : closedAL checkerProg coreStageA coreStageC stageCoreFns coreLeaves = true :=
  closedWL_of_all stageCoreTree.eq stageCoreCallTree.eq coreStagePa_mem coreStagePc_mem checkerProg_stageChk
/-- `lvl_eq_c`'s call closure as a tree of name codes. -/
names_tree lvlCoreTree : lvlCoreFns

/-- Every function of the checker passes `lvl_eq_c`'s per-function check (no leaf). -/
prog_all checkerProg_lvlChk : checkerProg (wsChk CTL coreStagePa coreStagePc lvlCoreTree)

theorem checkerProg_lvlCoreW : closedA checkerProg coreStageA coreStageC lvlCoreFns = true :=
  closedW_of_all lvlCoreTree.eq coreStagePa_mem coreStagePc_mem checkerProg_lvlChk

end L.Checker
