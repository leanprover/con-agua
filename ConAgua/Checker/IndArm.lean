module

import ConAgua.Checker.LoopProg
import ConAgua.Checker.IndArmClosed
public import ConAgua.Arena.IndArm
meta import ConAgua.Checker.LoopProg
meta import ConAgua.Checker.IndArmClosed
meta import ConAgua.Arena.IndArm
import ConAgua.Checker.CoreErec
import ConAgua.Checker.IndCore
import ConAgua.Checker.IndMemoClosed
import ConAgua.Checker.CrLeaves
import ConAgua.Checker.LoopDecl
import ConAgua.Checker.LoopProgTac
import ConAgua.Checker.IotaArm
public import ConAgua.Arena.IndInstallSpec.ConsRecsTFSimOf
public import ConAgua.Arena.IndInstallSpec.OfClosed
public import ConAgua.Arena.IndInstallSpec.ShapeCVOfDecB
public import ConAgua.Arena.IndT.ArmMemos
public import ConAgua.Arena.IndT.GenRec2
public import ConAgua.Checker.IndArmTrees2
public import ConAgua.Checker.Prog
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
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.IndInstall
import all ConAgua.Arena.IndParts
import all ConAgua.Arena.IotaFrame
import all ConAgua.Arena.IotaRel
import all ConAgua.Arena.IndPos
import all ConAgua.Arena.IndPos2
import all ConAgua.Arena.IndRealIpo
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
import all ConAgua.Arena.RecCheckSpec.CnfW
import all ConAgua.Arena.RecClass
import all ConAgua.Arena.RecGen
import all ConAgua.Arena.RecGenSpec.DecB
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
import all ConAgua.Rom.CIConst
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
# The inductive arm's contract at the checker's program (lane `indproofs4`)

`indArmSpec_of` (`Arena/IndArm.lean`) at `checkerProg.subPB bs`: the lookups by `prog_bundle`
(`indArmProgs_checker`, shared with the verdict side's `indArmVerdict_proved`), the write sets
from `Checker/IndArmClosed.lean`'s per-function checks (carried to the substituted program by
`closedW_subPB`), the `AbsKeep` facts of the callees that reach no walk from their write set
(`absKeep_of_closed`). The callees whose closure writes the walk memos (`armAbsWalk`: they reach
the core or the `instantiate`/`abstract` walks) keep `AbsKeep` as a hypothesis.
-/

namespace L.Checker

open L L.Rom L.Arena L.Ind L.Compiler

/-! ## The write sets (`Checker/IndArmClosed.lean`'s per-function checks) -/

theorem checkerProg_armPos : closedAL checkerProg posFreeA posFreeC armPosFns usLeaves = true :=
  closedWL_of_all armPosTree.eq armPosCallTree.eq (fun _ h => tA_mem h) (fun _ h => tC_mem h) checkerProg_armPosChk
theorem checkerProg_armHb : closedAL checkerProg hbFreeA hbFreeC armHbFns usLeaves = true :=
  closedWL_of_all armHbTree.eq armHbCallTree.eq (fun _ h => tA_mem h) (fun _ h => tC_mem h) checkerProg_armHbChk
theorem checkerProg_armRc : closedAL checkerProg rcFreeA rcFreeC armRcFns usLeaves = true :=
  closedWL_of_all armRcTree.eq armRcCallTree.eq (fun _ h => tA_mem h) (fun _ h => tC_mem h) checkerProg_armRcChk
theorem checkerProg_armTa : closedA checkerProg taFreeA taFreeC armTaFns = true :=
  closedW_of_all armTaTree.eq (fun _ h => tA_mem h) (fun _ h => tC_mem h) checkerProg_armTaChk
theorem checkerProg_armCid : closedA checkerProg cidFreeA cidFreeC armCidFns = true :=
  closedW_of_all armCidTree.eq (fun _ h => tA_mem h) (fun _ h => tC_mem h) checkerProg_armCidChk
theorem checkerProg_armRcHb : closedA checkerProg rcHbFreeA rcHbFreeC armRcHbFns = true :=
  closedW_of_all armRcHbTree.eq (fun _ h => tA_mem h) (fun _ h => tC_mem h) checkerProg_armRcHbChk
theorem checkerProg_armMa : closedAL checkerProg maFreeA maFreeC armMaFns maLeaves = true :=
  closedWL_of_all armMaTree.eq armMaCallTree.eq (fun _ h => tA_mem h) (fun _ h => tC_mem h) checkerProg_armMaChk
theorem checkerProg_armMc : closedA checkerProg mcFreeA mcFreeC armMcFns = true :=
  closedW_of_all armMcTree.eq (fun _ h => tA_mem h) (fun _ h => tC_mem h) checkerProg_armMcChk
theorem checkerProg_armOwn : closedA checkerProg
    (checkerWordArrays.filter fun b => decide (b ∉ ([OIXA, OIXS, OIXN, tier1 OIXA, tier1 OIXS, tier1 OIXN] :
      List TieredArray)))
    (((List.range 256).filter fun c => decide (c ≠ 133)).map Nat.toUInt64) armOwnFns = true :=
  closedW_of_all armOwnTree.eq (fun _ h => tA_mem h) (fun _ h => tC_mem h) checkerProg_armOwnChk
theorem checkerProg_armAbs : closedA checkerProg armAbsA armAbsC armAbsFns = true :=
  closedW_of_all armAbsTree.eq (fun _ h => tA_mem h) (fun _ h => tC_mem h) checkerProg_armAbsChk

/-! ## The roots in the function sets, by their name trees -/

/-- A list in a function set, from the set's name tree: `nameCode`s looked up in the tree, no
`String` comparison (`decide +kernel` on `l ⊆ fs` compares each name of `l` with every name of
`fs`, ~1 s per list). -/
theorem subset_of_tree {fs : List FnName} {t : NTree} (ht : namesTree fs = some t)
    {l : List FnName} (h : l.all (fun f => (t.find (nameCode f)).isSome) = true) :
    ∀ f ∈ l, f ∈ fs := fun f hf => by
  have := List.all_eq_true.mp h f hf
  rw [namesTree_spec ht] at this
  exact of_decide_eq_true this

theorem mem_of_tree {fs : List FnName} {t : NTree} (ht : namesTree fs = some t) {f : FnName}
    (h : (t.find (nameCode f)).isSome = true) : f ∈ fs := by
  rw [namesTree_spec ht] at h
  exact of_decide_eq_true h

theorem armPos_pass : ∀ f ∈ passCallees, f ∈ armPosFns := subset_of_tree armPosTree.eq (by decide +kernel)
theorem armPos_raw : "block_is_rec" ∈ armPosFns := mem_of_tree armPosTree.eq (by decide +kernel)
theorem armHb_tail : ∀ f ∈ tailCallees, f ∈ armHbFns := subset_of_tree armHbTree.eq (by decide +kernel)
theorem armRc_tail : ∀ f ∈ tailRcCallees, f ∈ armRcFns := subset_of_tree armRcTree.eq (by decide +kernel)
theorem armTa_block : ∀ f ∈ blockTaCallees, f ∈ armTaFns :=
  subset_of_tree armTaTree.eq (by decide +kernel)
theorem armCid_frame : ∀ f ∈ cidFrameCallees, f ∈ armCidFns :=
  subset_of_tree armCidTree.eq (by decide +kernel)
theorem armRc_grc : ∀ f ∈ grcRcCallees, f ∈ armRcFns :=
  subset_of_tree armRcTree.eq (by decide +kernel)
theorem armRcHb_tables : "check_block_tables" ∈ armRcHbFns :=
  mem_of_tree armRcHbTree.eq (by decide +kernel)
theorem armMa_pass : ∀ f ∈ ["check_block_pass", "check_block_tail"], f ∈ armMaFns :=
  subset_of_tree armMaTree.eq (by decide +kernel)
theorem armMc_block : "check_block" ∈ armMcFns := mem_of_tree armMcTree.eq (by decide +kernel)
theorem armAbs_split : ∀ f ∈ passKeepCalleesC ++ tailKeepCalleesC ++ ["block_is_rec"],
    f ∈ armAbsFns := subset_of_tree armAbsTree.eq (by decide +kernel)

/-! ## The program facts at the substituted checker program -/

/-- The program facts `indArmSpec_of` takes (and the verdict side's `indArmSpecE_of`), as one
bundle: proved once (`indArmProgs_checker`) for both. -/
structure IndArmProgs (p : Prog) : Prop where
  kp : KnotStageProg p
  v : ValProg p
  opf : OpfF p
  lc : LvlCacheProg p
  lt : p.lookup "lv_leq_top" = some lvLeqTop
  apd : ApdF p
  crk : CrKeep p
  ilpf : IlpfF p
  cid : CidProg p

/-- **The core's write set with its two leaves at the substituted checker program**
(`checkerProg_coreStageW`; the leaves' bundles by lookups). -/
theorem checkerProg_coreStagePB (bs : List UInt8) : L.Ind.CoreStageClosed (Prog.subPB bs checkerProg) :=
  ⟨closedWL_subPB bs checkerProg_coreStageW, by prog_bundle [], by prog_bundle [], by prog_bundle [],
    closedW_subPB bs checkerProg_lvlCoreW⟩

/-- **The inductive arm's program facts at the substituted checker program** (one `prog_bundle`:
a lookup two fields share is proved once). -/
theorem indArmProgs_checker (bs : List UInt8) (hr : RomOK bs)
    (hpre : bs = romData ++ bs.drop romData.length) : IndArmProgs (Prog.subPB bs checkerProg) := by
  have hrom := checkerProg_romRefsPB bs hr hpre
  prog_bundle [checkerProg_cvgAgreePB bs, checkerProg_ivAgreePB bs, checkerProg_armAgreePB bs,
    checkerProg_cvgIn.subPB bs, checkerProg_ivIn.subPB bs, checkerProg_armIn.subPB bs,
    checkerProg_coreStagePB bs,
    closedW_subPB bs checkerProg_coreErec, checkerProg_natAgreePB bs, checkerProg_lvlTextPB bs,
    hrom, closedWL_subPB bs checkerProg_indMemo, checkerProg_crLeavesPB bs]

/-- `AbsKeep` of the arm's callees that reach no walk, from their write set. -/
theorem indArmKeep_checker (bs : List UInt8) :
    ∀ f ∈ passKeepCalleesC ++ tailKeepCalleesC ++ ["block_is_rec"],
      AbsKeep (Prog.subPB bs checkerProg) f := fun f hf =>
  absKeep_of_closed (closedW_subPB bs checkerProg_armAbs) armAbsA_free armAbsC_free (armAbs_split f hf)

/-- **`check_block`'s contract at the substituted checker program** (`blockRefS_of`), from its
callees' contracts (`Checker/BlockRefsProg`'s `cbRefs_checker`, from the caller). -/
theorem blockRefS_checker (bs : List UInt8)
    (hR : ∀ dn, DnInj dn → CbRefs (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) dn) :
    ∀ dn, DnInj dn → BlockRefS (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) dn :=
  fun dn hdn => blockRefS_of (hR dn hdn) fun hG => hG.nv

/-- **The inductive arm's contract at the substituted checker program**, from the contract of
its returning callee (`blockRefS_checker`). -/
theorem indArmSpec_checker (bs : List UInt8) (hr : RomOK bs)
    (hpre : bs = romData ++ bs.drop romData.length)
    (hR : ∀ dn, DnInj dn → CbRefs (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) dn) :
    ∀ dn, DnInj dn → IndArmSpec (Prog.subPB bs checkerProg) dn := by
  have H := indArmProgs_checker bs hr hpre
  exact indArmSpec_of ⟨H.cid, checkerProg_coreStagePB bs, H.lc, iotaArmProg_checker bs⟩
    (blockRefS_checker bs hR) (closedW_subPB bs checkerProg_armCid) armCid_frame

end L.Checker
