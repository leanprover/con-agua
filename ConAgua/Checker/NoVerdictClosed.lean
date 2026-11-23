module

public import ConAgua.Checker.Prog
public import ConAgua.L.ErrSpec
public import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.LevelIntern
public import ConAgua.Arena.LevelSubstLP
meta import ConAgua.Checker.Prog
meta import ConAgua.L.ErrSpec
meta import ConAgua.Checker.NoVerdictTree
meta import ConAgua.Arena.LevelIntern
meta import ConAgua.Arena.LevelSubstLP
import all Init.Data.Repr
import all ConAgua.Arena.Abs1
import all ConAgua.Rom.CIConst
import all ConAgua.Rom.PinReadSpec
import all ConAgua.Scan.Line
import all ConAgua.Arena.WhnfCoreApp
import all ConAgua.Arena.RomCI
import all ConAgua.Arena.Prelude
import all ConAgua.Arena.IndStream
import all ConAgua.Arena.IndDeclConsts
import all ConAgua.Arena.CoreWalks
import all ConAgua.Arena.BasisL
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

@[expose] public section

/-!
# The functions of `checkerProg` that claim no verdict

`nvFns` (`Checker/NoVerdictFns.lean`, generated by `scripts/nv_fns.py`) is call-closed in
`checkerProg` and every body in it aborts only with a constant class-`0` code
(`checkerProg_nv : closedNV checkerProg nvFns`). So every failing call of one of them fails with
class `0` (`callE_nv`), and claims nothing: these are the functions outside the verdict closure.
Per-function kernel checks (`prog_all`) over the name tree, as `Compiler/WriteSetSplit.lean`'s
write sets.
-/

namespace L

open L.Compiler

/-- `Stmt.noV` with the callee set as a name tree. -/
def Stmt.noVB (t : NTree) : Stmt → Bool
  | .seq s u => s.noVB t && u.noVB t
  | .ite _ s u => s.noVB t && u.noVB t
  | .while _ s => s.noVB t
  | .call _ f _ => (t.find (nameCode f)).isSome
  | .abort e => e.cls0
  | _ => true

theorem Stmt.noV_of_noVB {t : NTree} {fs : List FnName} (ht : namesTree fs = some t) :
    ∀ {s : Stmt}, s.noVB t = true → s.noV fs = true := by
  intro s h
  induction s with
  | seq s u ihs ihu | ite _ s u ihs ihu =>
    simp only [Stmt.noVB, Bool.and_eq_true] at h
    simp only [Stmt.noV, Bool.and_eq_true]
    exact ⟨ihs h.1, ihu h.2⟩
  | «while» _ s ih => exact ih h
  | «call» _ f _ =>
    simp only [Stmt.noVB, namesTree_spec ht] at h
    exact h
  | «abort» e => exact h
  | _ => rfl

/-- One function's check: not in the set, or its body passes `noVB`. -/
def nvChk (t : NTree) (x : FnName × FunDecl) : Bool :=
  !(t.find (nameCode x.1)).isSome || x.2.body.noVB t

theorem closedNV_of_all {p : Prog} {fs : List FnName} {t : NTree} (ht : namesTree fs = some t)
    (h : ∀ x ∈ p, nvChk t x = true) : closedNV p fs = true := by
  simp only [closedNV, List.all_eq_true]
  intro f hf
  split
  · rename_i fd hfd
    obtain ⟨_, _, hp, -⟩ := List.lookup_eq_some_iff.mp hfd
    have hx := h _ (hp ▸ List.mem_append_right _ List.mem_cons_self)
    simp only [nvChk, namesTree_spec ht, hf, decide_true, Bool.not_true, Bool.false_or] at hx
    exact Stmt.noV_of_noVB ht hx
  · rfl

end L

namespace L.Checker

open L.Compiler

prog_all checkerProg_nvChk : checkerProg (nvChk nvTree)

/-- **The functions outside the verdict closure claim nothing.** -/
theorem checkerProg_nv : closedNV checkerProg nvFns = true :=
  closedNV_of_all nvTree.eq checkerProg_nvChk

end L.Checker
