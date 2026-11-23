module

public import ConAgua.Checker.Prog
public import ConAgua.Checker.IndArmTrees1
public import ConAgua.Checker.IndArmTrees2
meta import ConAgua.Checker.Prog
meta import ConAgua.Arena.LeafFrame
meta import ConAgua.Checker.IndArmTrees1
meta import ConAgua.Checker.IndArmTrees2
import all ConAgua.Arena.Abs1
import all ConAgua.Arena.BasisL
import all ConAgua.Arena.IndDeclConsts
import all ConAgua.Arena.IndStream
import all ConAgua.Rom.CIConst
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
# The write sets of the inductive arm's callees in `checkerProg` (lane `indproofs4`)

The per-function checks (`prog_all`) behind the `closedA` facts `cid_ref`
(`Arena/IndT/CheckIndDecl.lean`) takes, for the checker's program, over the call-closed function
sets of `Checker/IndArmFns.lean`; and behind the write set (apart from the walk memos) of the arm's
`AbsKeep` callees that reach no walk (`armAbsFns`). As `Checker/IndMemoClosed.lean`. They are put
together by `closedW_of_all` in `Checker/IndArm.lean`: this module needs only `checkerProg` and
the array names, so its kernel checks run early in the build, beside the arm's proofs. The
nine arms are checked together, one `prog_all` over `wsChkM` (each function's name code and body
reduced once per chunk check, not once per arm: ~26 CPU-s instead of ~90 in three modules). The
arms that reach `struct_used_later` or `mentions_any_const` take them as leaves (`wsChkL`).
-/

namespace L.Checker

open L.Arena L.Ind L.Compiler

/-! ## The checks -/

prog_all checkerProg_armChk : checkerProg
  (wsChkM CTL [armPosT, armHbT, armRcT, armTaT, armCidT, armRcHbT, armMaT, armMcT, armAbsT, armOwnT])

theorem checkerProg_armPosChk :
    ∀ x ∈ checkerProg, wsChkL CTL armPosT.1 armPosT.2.1 armPosT.2.2.1 armPosT.2.2.2 x = true :=
  wsChk_of_all checkerProg_armChk (by simp)
theorem checkerProg_armHbChk :
    ∀ x ∈ checkerProg, wsChkL CTL armHbT.1 armHbT.2.1 armHbT.2.2.1 armHbT.2.2.2 x = true :=
  wsChk_of_all checkerProg_armChk (by simp)
theorem checkerProg_armRcChk :
    ∀ x ∈ checkerProg, wsChkL CTL armRcT.1 armRcT.2.1 armRcT.2.2.1 armRcT.2.2.2 x = true :=
  wsChk_of_all checkerProg_armChk (by simp)
theorem checkerProg_armTaChk :
    ∀ x ∈ checkerProg, wsChkL CTL armTaT.1 armTaT.2.1 armTaT.2.2.1 armTaT.2.2.2 x = true :=
  wsChk_of_all checkerProg_armChk (by simp)
theorem checkerProg_armCidChk :
    ∀ x ∈ checkerProg, wsChkL CTL armCidT.1 armCidT.2.1 armCidT.2.2.1 armCidT.2.2.2 x = true :=
  wsChk_of_all checkerProg_armChk (by simp)
theorem checkerProg_armRcHbChk :
    ∀ x ∈ checkerProg, wsChkL CTL armRcHbT.1 armRcHbT.2.1 armRcHbT.2.2.1 armRcHbT.2.2.2 x = true :=
  wsChk_of_all checkerProg_armChk (by simp)
theorem checkerProg_armMaChk :
    ∀ x ∈ checkerProg, wsChkL CTL armMaT.1 armMaT.2.1 armMaT.2.2.1 armMaT.2.2.2 x = true :=
  wsChk_of_all checkerProg_armChk (by simp)
theorem checkerProg_armMcChk :
    ∀ x ∈ checkerProg, wsChkL CTL armMcT.1 armMcT.2.1 armMcT.2.2.1 armMcT.2.2.2 x = true :=
  wsChk_of_all checkerProg_armChk (by simp)
theorem checkerProg_armAbsChk :
    ∀ x ∈ checkerProg, wsChkL CTL armAbsT.1 armAbsT.2.1 armAbsT.2.2.1 armAbsT.2.2.2 x = true :=
  wsChk_of_all checkerProg_armChk (by simp)
theorem checkerProg_armOwnChk :
    ∀ x ∈ checkerProg, wsChkL CTL armOwnT.1 armOwnT.2.1 armOwnT.2.2.1 armOwnT.2.2.2 x = true :=
  wsChk_of_all checkerProg_armChk (by simp)

end L.Checker
