module

public import ConAgua.Checker.ArmsT
public import ConAgua.Checker.DefnFe2Closed
import ConAgua.Checker.LoopProgTac
meta import ConAgua.Checker.LoopProgTac
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
import all ConAgua.Arena.IndDeclConsts
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
import all ConAgua.Arena.IndStream
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
import all ConAgua.Arena.NatSized

@[expose] public section

/-!
# The definition arm's contract at the substituted checker program

`checkerProg_defnArmPB`: the definition arm's program facts (`DefnProgT`, `Arena/DeclDefnT.lean`)
at `Prog.subPB bs checkerProg`: the lookups, the callees' write set, the structural gate's reads'
frame (`checkerProg_fe2Closed`). `checkerProg_defnLoopPB`: the arm's `ArmSpecT`
(`checkDeclDefn_loopT`), `checkerProg_cdProgPB`'s premise `hdf`.
-/

namespace L.Checker

open L.Arena L.Ind L.Compiler L.Rom ConRon.Arena

/-- Membership in `declLoopFns` by its tree of name codes. -/
theorem declLoop_mem (f : FnName) (h : (declLoopTree.find (L.Compiler.nameCode f)).isSome = true) :
    f ∈ declLoopFns := by
  have := L.Compiler.namesTree_spec declLoopTree.eq f
  rw [h] at this; exact of_decide_eq_true this.symm

theorem defnCall_stepIn : StepIn checkerProg defnCallFns :=
  checkerProg_stepIn fun f hf => by
    simp only [defnCallFns, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> exact declLoop_mem _ rfl

section defn
variable (bs : List UInt8)

theorem checkerProg_defnArmPB (hr : RomOK bs) (hpre : bs = romData ++ bs.drop romData.length) :
    DefnProgT (Prog.subPB bs checkerProg) := by
  have hR := checkerProg_romRefsPB bs hr hpre
  prog_bundle [hR.ci, hR.cv, hR.expr, hR.basis, hR.quot, hR.andPin, (checkerProg_thmArmPB bs hr hpre).ccv, closedW_subPB bs checkerProg_fe2Closed,
    StepIn.subPB bs defnCall_stepIn]

/-- **The definition arm's contract at the substituted checker program** (`checkerProg_cdProgPB`'s
`hdf`). -/
theorem checkerProg_defnLoopPB (hr : RomOK bs) (hpre : bs = romData ++ bs.drop romData.length)
    {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name}
    {ds : Array IDeclaration} :
    ∀ cv v hh, ArmSpecT pins dn ds (Prog.subPB bs checkerProg) "check_decl_defn"
      (.defnDecl cv v hh) :=
  checkDeclDefn_loopT (checkerProg_defnArmPB bs hr hpre) (checkerProg_knotStagePB bs)
    (checkerProg_leafClosedPB bs) (checkerProg_apdPB bs) (checkerProg_crKeepPB bs)
    (checkerProg_crfPB bs) (checkerProg_ccvSimsPB bs dn) (checkerProg_armStepPB bs (by decide))
    (checkerProg_indMemoPB bs) (checkerProg_indLeavesPB bs)

end defn

end L.Checker
