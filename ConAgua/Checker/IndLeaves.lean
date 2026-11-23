module

public import ConAgua.Arena.IndSumSpec.StructUsedLeaf
import ConAgua.Arena.IndRealCrFKeep
public import ConAgua.Checker.Prog
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
public import ConAgua.Arena.IndRealCrF

@[expose] public section

set_option experimental.vcgen true


/-!
# The leaves of `imFns` keep `IndMemos` at the checker's program

`checkerProg_indLeavesPB`: `IndLeaves` (`Arena/LoopT.lean`) at the substituted checker program.
`consts_resolve_ffast` by its model (`crfF`: it writes only the walk memo `CRM` and `CTL[158]`,
`CTL[159]`, and keeps `CrOK`), `struct_used_later` by `indMemos_usLeaf` (`UsF`, a `prog_bundle`
lookup).
-/

namespace L.Checker

open L L.Arena L.Compiler
open Std.WP
open scoped Lean.Order

/-- **`consts_resolve_ffast` keeps `IndMemos`**, at any arguments: the stage memos and the
`instantiate1Lift` memo by its frame, `CrOK` by `crfF_keepsCrOK`. -/
theorem indMemos_crf {p : Prog} (hp : L.Ind.CrfF p) (n : Nat) (m₀ : Mem) (vs : List Word) :
    ⦃fun s => IndMemos m₀ → IndMemos s.mem⦄ invoke p (exec p n) "consts_resolve_ffast" vs
    ⦃fun _ s => IndMemos m₀ → IndMemos s.mem; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨-, hc⟩ := M.of_run (P := fun t => t = s) rfl hrun (L.Ind.crfF_spec p hp n s vs)
  intro h0
  have hI := hs h0
  have hf := L.Ind.crfF_frame hc
  exact ⟨hI.stage.frame hf (fun b hb => by simp at hb; subst hb; decide)
      (fun x hx => by simp at hx; rcases hx with rfl | rfl <;> decide),
    L.Ind.I1Memo.frame hI.i1 hf (by decide) (by decide),
    L.Ind.crfF_keepsCrOK hc hI.cr⟩

/-- **The leaves keep `IndMemos`** at a program with `consts_resolve_ffast`'s and
`struct_used_later`'s texts. -/
theorem indLeaves_of {p : Prog} (hc : L.Ind.CrfF p) (hu : L.Ind.UsF p) (hl : ProgHas p L.Ind.hbLeafP) :
    IndLeaves p := by
  intro g hg n m₀ vs
  simp only [imLeaves, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact indMemos_crf hc n m₀ vs
  · exact L.Ind.indMemos_usLeaf hu n m₀ vs
  · exact L.Ind.indMemos_hlLeaf hl (.inl rfl) n m₀ vs
  · exact L.Ind.indMemos_hlLeaf hl (.inr rfl) n m₀ vs

theorem checkerProg_indLeavesPB (bs : List UInt8) : IndLeaves (Prog.subPB bs checkerProg) :=
  indLeaves_of (by prog_bundle [] : L.Ind.CrfF (Prog.subPB bs checkerProg))
    (by prog_bundle [] : L.Ind.UsF (Prog.subPB bs checkerProg))
    (by prog_bundle [] : ProgHas (Prog.subPB bs checkerProg) L.Ind.hbLeafP)

end L.Checker
