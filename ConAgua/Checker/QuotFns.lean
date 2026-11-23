module

public import ConAgua.Checker.Prog
public import ConAgua.Arena.QuotFns
public import ConAgua.Compiler.WriteSetSplit
meta import ConAgua.Checker.Prog
meta import ConAgua.Arena.CoreErec
meta import ConAgua.Arena.QuotFns
meta import ConAgua.Compiler.WriteSetSplit
meta import ConAgua.Arena.LevelIntern
meta import ConAgua.Arena.LevelSubstLP
import all ConAgua.Arena.Abs1
import all ConAgua.Arena.BasisL
import all ConAgua.Rom.CIConst
import all ConAgua.Rom.CIRead
import all ConAgua.Rom.PinRead
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
# The quotient pins' functions leave the environment alone, for the checker's program

`ConAgua/Arena/QuotFns.lean`'s program hypothesis `QuotClosed checkerProg`, split into per-chunk
checks (`prog_all`) as `ConAgua/Checker/CoreErec.lean` does.
-/

namespace L.Checker

open L.Arena L.Compiler L.Ind

/-- `quotFns` as a tree of name codes. -/
names_tree quotTree : quotFns

/-- The arrays of `quotA`, as a test (`EnvR`'s arrays by their numbers, `not_mem_envArrs`). -/
def quotPa (a : TieredArray) : Bool :=
  checkerWordArrays.contains a && decide (a.arr = 136 ∨ a.arr < 129 ∨ 149 ≤ a.arr ∨ a.arr = 135 ∨
    (137 ≤ a.arr ∧ a.arr < 140) ∨ (143 ≤ a.arr ∧ a.arr < 146))

/-- The `CTL` words of `quotC`, as a test. -/
def quotPc (w : Word) : Bool :=
  decide (w.toNat < 256 ∧ (w.toNat = 129 ∨ w.toNat = 130 ∨ (w.toNat ≠ 133 ∧ w.toNat ≠ 134 ∧ w.toNat ≠ 135 ∧
    (w.toNat < 160 ∨ 172 ≤ w.toNat))))

theorem quotPa_mem (a : TieredArray) (h : quotPa a = true) : a ∈ quotA := by
  simp only [quotPa, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at h
  simp only [quotA, List.mem_filter, decide_eq_true_eq]
  refine ⟨h.1, ?_⟩
  rcases h.2 with h2 | h2
  · exact .inl h2
  · exact .inr (not_mem_envArrs h2)

theorem quotPc_mem (w : Word) (h : quotPc w = true) : w ∈ quotC := by
  simp only [quotPc, decide_eq_true_eq] at h
  obtain ⟨hl, h1⟩ := h
  simp only [quotC, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
  refine ⟨w.toNat, ⟨hl, ?_⟩, UInt64.ofNat_toNat⟩
  rcases h1 with h1 | h1 | h1
  · exact .inl h1
  · exact .inr (.inl h1)
  · by_cases e1 : w.toNat = 129
    · exact .inl e1
    by_cases e2 : w.toNat = 130
    · exact .inr (.inl e2)
    refine .inr (.inr ?_)
    have e : w.toNat.toUInt64 = w := UInt64.ofNat_toNat
    rw [e]; simp only [envCtl, List.mem_cons, List.not_mem_nil, or_false]
    intro hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> revert h1 e1 e2 <;> decide

/-- Every function of the checker passes the quotient functions' per-function check. -/
prog_all checkerProg_quotChk : checkerProg (wsChk CTL quotPa quotPc quotTree)

theorem checkerProg_quotClosed : QuotClosed checkerProg :=
  closedW_of_all quotTree.eq quotPa_mem quotPc_mem checkerProg_quotChk

/-- `plFns` as a tree of name codes. -/
names_tree plTree : plFns

def plPa (a : TieredArray) : Bool := checkerWordArrays.contains a && !plBad.contains a
def plPc (w : Word) : Bool := decide (w.toNat < 256) && !plBadC.contains w

theorem plPa_mem (a : TieredArray) (h : plPa a = true) : a ∈ plA := by
  simp only [plPa, Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem] at h
  simp only [plA, List.mem_filter, decide_eq_true_eq]
  exact ⟨h.1, by simpa using h.2⟩

theorem plPc_mem (w : Word) (h : plPc w = true) : w ∈ plC := by
  simp only [plPc, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  simp only [plC, List.mem_filter, List.mem_map, List.mem_range, decide_eq_true_eq]
  exact ⟨⟨w.toNat, h.1, UInt64.ofNat_toNat⟩, by simpa using h.2⟩

prog_all checkerProg_plChk : checkerProg (wsChk CTL plPa plPc plTree)

theorem checkerProg_plClosed : PlClosed checkerProg :=
  closedW_of_all plTree.eq plPa_mem plPc_mem checkerProg_plChk

end L.Checker
