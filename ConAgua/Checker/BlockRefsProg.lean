module

public import ConAgua.Checker.IndDeclConstsProg
public import ConAgua.Arena.IndT.BlockCS
public import ConAgua.Arena.IndT.BlockWM
public import ConAgua.Arena.IndT.BlockPD
public import ConAgua.Arena.IndT.BlockNames
public import ConAgua.Arena.IndT.BlockRMS
public import ConAgua.Arena.IndT.PassCS
import ConAgua.Checker.ArmsT
import ConAgua.Verdict.PosKnotE
meta import ConAgua.Checker.IndDeclConstsProg
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
import all ConAgua.Arena.NatArms
import all ConAgua.Arena.NatBits
import all ConAgua.Arena.NatCmp
import all ConAgua.Arena.NatDiv
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
import all ConAgua.Rom.CIConst
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
# `check_block`'s callees' contracts at the substituted checker program (lane `ronsync2`)

`cbRefs_checker`: `IndT/BlockC`'s `CbRefs` at `Prog.subPB bs checkerProg`, what `Checker/IndArm`'s
`indArmSpec_checker` takes. The contracts proved so far come from their generic proofs
(`IndT/BlockCS`) at the stream index's program facts (`declConstsProg_checker`).
-/

open L L.Rom L.Arena L.Ind L.Compiler

namespace L.Checker

set_option maxRecDepth 20000 in
/-- **`check_block`'s callees' contracts at the substituted checker program.** -/
theorem cbRefs_checker (bs : List UInt8) (hr : RomOK bs)
    (hpre : bs = romData ++ bs.drop romData.length) :
    ∀ dn, DnInj dn → CbRefs (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) dn := by
  intro dn _
  have H := declConstsProg_checker bs hr hpre
  have look : CbLook (Prog.subPB bs checkerProg) := by prog_bundle []
  have hF : FlushProg (Prog.subPB bs checkerProg) := by prog_bundle []
  have hnv : VerdictCtxU (Prog.subPB bs checkerProg) → closedNV (Prog.subPB bs checkerProg) nvFns = true :=
    fun hG => hG.nv
  -- ronsync2 p3e: the tail: its contract still to prove
  have hfl : FlushRefS (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) dn :=
    flushRefS_of (dn := dn) hF hnv
  have hbr : BrRefS (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) :=
    brRefS_of H.toTablesProg.toBlockProg.toRecsProg H.leaf hnv
  have hbt : BtRefS (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) :=
    btRefS_of H.toTablesProg H.leaf hnv
  have hwl : BswmLook (Prog.subPB bs checkerProg) := by prog_bundle []
  have hwm : BswmRefS (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) dn :=
    bswmRefS_of hwl hnv
  have hpdP : PdProg (Prog.subPB bs checkerProg) := by prog_bundle []
  have hpd : PdRefS (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) :=
    pdRefS_of hpdP hnv
  have hnP : NamesProg (Prog.subPB bs checkerProg) := by prog_bundle []
  have hnm : NamesRefS (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) dn :=
    namesRefS_of hnP hnv
  have hbir : BirRefS (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) dn :=
    birRefS_of H.toTablesProg.toBlockProg H.leaf hnv
  have hrmP : RmsProg (Prog.subPB bs checkerProg) := by prog_bundle []
  have hWt : WhnfTopE (Prog.subPB bs checkerProg) :=
    whnfTop_stageE (by prog_bundle []) (fun n => (checkerProg_knotTopPB bs).knotOK n) (checkerProg_knotEPB bs)
  have hrm : RmRefS (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) dn :=
    rmRefS_of (checkerProg_thmArmPB bs hr hpre).ccv (checkerProg_knotStagePB bs) (checkerProg_apdPB bs)
      (checkerProg_crKeepPB bs) (checkerProg_crfPB bs) hrmP hWt (checkerProg_indLeavesPB bs)
      (checkerProg_ccvSimsPB bs dn)
  -- the pass: `passRefS_of` from its callees' contracts
  have hAP := indArmProgs_checker bs hr hpre
  have hccv := (checkerProg_thmArmPB bs hr hpre).ccv
  have hsc : SctsRefS (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) dn :=
    sctsRefS_of hAP.kp hAP.opf hAP.lc hAP.lt hAP.apd hAP.crk (by prog_bundle []) hccv
      (checkerProg_crfPB bs) (checkerProg_ccvSimsPB bs dn)
  have hinds : IndsRefS (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) dn :=
    indsRefS_of hAP.kp hccv (checkerProg_crfPB bs) (checkerProg_ccvSimsPB bs dn) hAP.opf hAP.lc
      hAP.apd hAP.crk (by prog_bundle [])
      (fun f hf => indArmKeep_checker bs f (by
        simp only [indsKeepCalleesC, List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl <;>
          simp [passKeepCalleesC, tailKeepCalleesC, grcKeepCalleesC, indsKeepCalleesC, posKeepCalleesC]))
      (checkerProg_indLeavesPB bs)
  have hct : CtorsRefS (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) dn :=
    ctorsRefS_of (by prog_bundle []) hsc hAP.crk (checkerProg_indLeavesPB bs)
  have hpl : PassLook (Prog.subPB bs checkerProg) := by prog_bundle []
  -- ronsync2 p3e: block_nest_ctx, check_block_classes, check_block_positivity, class_seeds,
  -- nest_seeds: their contracts still to prove (Pass.lean's BncRefS … NsdRefS)
  have hbnc : BncRefS (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) dn := sorry
  have hcls : ClsRefS (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) dn := sorry
  have hpos : PosRefS (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) dn := sorry
  have hsd : SeedsRefS (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) dn := sorry
  have hnsd : NsdRefS (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) dn := sorry
  have hpass : PassRefS (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) dn :=
    passRefS_of ⟨hpl, hinds, hct, hbnc, hcls, hpos, hsd, hnsd⟩ hnv
  exact ⟨look, hnm, hrm, hfl, hbir, hwm, hpass, sorry, hbr, hbt, hpd⟩

end L.Checker
