module

public import ConAgua.Checker.IndDeclConstsProg
public import ConAgua.Arena.IndT.BlockCS
public import ConAgua.Arena.IndT.BlockWM
public import ConAgua.Arena.IndT.BlockPD
public import ConAgua.Arena.IndT.BlockNames
public import ConAgua.Arena.IndT.BlockRMS
public import ConAgua.Arena.IndT.PassCS
public import ConAgua.Arena.IndT.PassNsd
public import ConAgua.Arena.IndT.PassBnc
public import ConAgua.Arena.IndT.Positivity
public import ConAgua.Arena.IndT.RecGen21
public import ConAgua.Arena.IndT.TailRef
public import ConAgua.Checker.StreamRecsProg
import ConAgua.Checker.ArmsT
import ConAgua.Verdict.PosKnotE
import ConAgua.Checker.IndArmTrees1
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
import all ConAgua.Arena.IotaFrame
import all ConAgua.Arena.IotaRel
import all ConAgua.Arena.JustifyIface
import all ConAgua.Arena.Needs
import all ConAgua.Arena.Justify
import all ConAgua.Arena.JustifySide
import all ConAgua.Checker.CompareEntry
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
import all ConAgua.Arena.NatSized

@[expose] public section

/-!
# `check_block`'s callees' contracts at the substituted checker program (lane `ronsync2`)

`cbRefs_checker`: `IndT/BlockC`'s `CbRefs` at `Prog.subPB bs checkerProg`, what `Checker/IndArm`'s
`indArmSpec_checker` takes. The contracts proved so far come from their generic proofs
(`IndT/BlockCS`) at the stream index's program facts (`declConstsProg_checker`).
-/

open L L.Rom L.Arena L.Ind L.Compiler

namespace L.Checker

/-- **The walk memos outside the positivity check's kept** by a function in the arm's `maFree`,
`mcFree`, `taFree` write sets (`checkerProg_armMa`, `_armMc`, `_armTa`), at the substituted program. -/
theorem wmKeep_checker (bs : List UInt8) {f : FnName} (ha : f ∈ armMaFns) (hc : f ∈ armMcFns)
    (ht : f ∈ armTaFns) : WmKeep (Prog.subPB bs checkerProg) f := by
  have hma : MaProg (Prog.subPB bs checkerProg) := by prog_bundle []
  exact ⟨fun _ _ _ _ _ h hM => maMR.ofClosedL (closedWL_subPB bs checkerProg_armMa) hma ha h hM,
    fun _ _ _ _ _ h hM => mcMR.ofClosed (closedW_subPB bs checkerProg_armMc) hc h hM,
    fun _ _ _ _ _ h hM => taMR.ofClosed (closedW_subPB bs checkerProg_armTa) ht h hM⟩

/-- **`class_seeds`' contract at the substituted checker program** (`seedsRefS_of`). -/
theorem seedsRefS_checker (bs : List UInt8) (dn : ConRon.Arena.NIdx → Option ConLeche.Name) :
    SeedsRefS (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) dn := by
  have hP : SdProg (Prog.subPB bs checkerProg) := by prog_bundle []
  exact seedsRefS_of hP (indArmKeep_checker bs _ (by simp [passKeepCalleesC]))
    (wmKeep_checker bs (mem_of_tree armMaTree.eq (by decide +kernel))
      (mem_of_tree armMcTree.eq (by decide +kernel)) (mem_of_tree armTaTree.eq (by decide +kernel)))

/-- **`block_nest_ctx`'s contract at the substituted checker program** (`bncRefS_of`). -/
theorem bncRefS_checker (bs : List UInt8) (hr : RomOK bs) (hpre : bs = romData ++ bs.drop romData.length)
    (dn : ConRon.Arena.NIdx → Option ConLeche.Name) :
    BncRefS (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) dn := by
  have hAP := indArmProgs_checker bs hr hpre
  have hP : PosBlkProg (Prog.subPB bs checkerProg) := by prog_bundle []
  exact bncRefS_of hP hAP.opf hAP.crk (checkerProg_indLeavesPB bs)

set_option maxRecDepth 20000 in
/-- **`check_block_positivity`'s contract at the substituted checker program** (`posRefS_of`;
`check_abs_ctor_sorts_all` keeps the walk memos by the arm's `armPosFns` closure). -/
theorem posRefS_checker (bs : List UInt8) (hr : RomOK bs) (hpre : bs = romData ++ bs.drop romData.length)
    (dn : ConRon.Arena.NIdx → Option ConLeche.Name) :
    PosRefS (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) dn := by
  have hAP := indArmProgs_checker bs hr hpre
  have hP : PosBlkProg (Prog.subPB bs checkerProg) := by prog_bundle []
  have hMc : McLook (Prog.subPB bs checkerProg) := by prog_bundle []
  have hF : FtProg (Prog.subPB bs checkerProg) := by prog_bundle []
  have hFk : FkcProg (Prog.subPB bs checkerProg) := by prog_bundle []
  have hus : UsF (Prog.subPB bs checkerProg) := by prog_bundle []
  have hWt : WhnfTopE (Prog.subPB bs checkerProg) :=
    whnfTop_stageE (by prog_bundle []) (fun n => (checkerProg_knotTopPB bs).knotOK n) (checkerProg_knotEPB bs)
  have hmem : "check_abs_ctor_sorts_all" ∈ armPosFns := mem_of_tree armPosTree.eq (by decide +kernel)
  exact posRefS_of hAP.kp hAP.ilpf hAP.opf hAP.lc hAP.lt hAP.apd hP hMc hF hFk hWt
    (bncRefS_checker bs hr hpre dn)
    (fun f hf => indArmKeep_checker bs f (by
      simp only [posKeepCalleesC, List.mem_cons, List.not_mem_nil, or_false] at hf
      subst hf; simp [passKeepCalleesC, posKeepCalleesC]))
    (fun h hM => PosMR.ofClosedL (by prog_bundle [] : ProgHas (Prog.subPB bs checkerProg) L.Ind.hbLeafP) (closedWL_subPB bs checkerProg_armPos) hus hmem h hM)
    (wmKeep_checker bs (mem_of_tree armMaTree.eq (by decide +kernel))
      (mem_of_tree armMcTree.eq (by decide +kernel)) (mem_of_tree armTaTree.eq (by decide +kernel)))

set_option maxRecDepth 20000 in
/-- **`check_block_classes`' contract at the substituted checker program** (`clsRefS_of`; the walk
memos across `class_read`, `class_read_classes` by the arm's `armPosFns` closure). -/
theorem clsRefS_checker (bs : List UInt8) (hr : RomOK bs) (hpre : bs = romData ++ bs.drop romData.length)
    (dn : ConRon.Arena.NIdx → Option ConLeche.Name) :
    ClsRefS (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) dn := by
  have hAP := indArmProgs_checker bs hr hpre
  have hP : CbcProg (Prog.subPB bs checkerProg) := by prog_bundle []
  have hF : FtProg (Prog.subPB bs checkerProg) := by prog_bundle []
  have hFk : FkcProg (Prog.subPB bs checkerProg) := by prog_bundle []
  have hus : UsF (Prog.subPB bs checkerProg) := by prog_bundle []
  have hWt : WhnfTopE (Prog.subPB bs checkerProg) :=
    whnfTop_stageE (by prog_bundle []) (fun n => (checkerProg_knotTopPB bs).knotOK n) (checkerProg_knotEPB bs)
  have hm1 : "class_read" ∈ armPosFns := mem_of_tree armPosTree.eq (by decide +kernel)
  have hm2 : "class_read_classes" ∈ armPosFns := mem_of_tree armPosTree.eq (by decide +kernel)
  exact clsRefS_of hAP.kp hAP.ilpf hAP.lc hP hF hFk hWt hAP.opf
    (indArmKeep_checker bs _ (by simp [passKeepCalleesC]))
    (indArmKeep_checker bs _ (by simp [passKeepCalleesC]))
    (fun h hM => PosMR.ofClosedL (by prog_bundle [] : ProgHas (Prog.subPB bs checkerProg) L.Ind.hbLeafP) (closedWL_subPB bs checkerProg_armPos) hus hm1 h hM)
    (fun h hM => PosMR.ofClosedL (by prog_bundle [] : ProgHas (Prog.subPB bs checkerProg) L.Ind.hbLeafP) (closedWL_subPB bs checkerProg_armPos) hus hm2 h hM)
    (wmKeep_checker bs (mem_of_tree armMaTree.eq (by decide +kernel))
      (mem_of_tree armMcTree.eq (by decide +kernel)) (mem_of_tree armTaTree.eq (by decide +kernel)))

set_option maxRecDepth 20000 in
/-- **`nest_seeds`' contract at the substituted checker program** (`nsdRefS_of`). -/
theorem nsdRefS_checker (bs : List UInt8) (hr : RomOK bs) (hpre : bs = romData ++ bs.drop romData.length)
    (dn : ConRon.Arena.NIdx → Option ConLeche.Name) :
    NsdRefS (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) dn := by
  have hAP := indArmProgs_checker bs hr hpre
  have L : RsLook (Prog.subPB bs checkerProg) := by prog_bundle []
  have hF : FtProg (Prog.subPB bs checkerProg) := by prog_bundle []
  have hFk : FkcProg (Prog.subPB bs checkerProg) := by prog_bundle []
  have hWt : WhnfTopE (Prog.subPB bs checkerProg) :=
    whnfTop_stageE (by prog_bundle []) (fun n => (checkerProg_knotTopPB bs).knotOK n) (checkerProg_knotEPB bs)
  exact nsdRefS_of L hAP.kp hAP.ilpf hAP.lc hF hFk hWt
    (wmKeep_checker bs (mem_of_tree armMaTree.eq (by decide +kernel))
      (mem_of_tree armMcTree.eq (by decide +kernel)) (mem_of_tree armTaTree.eq (by decide +kernel)))

/-! ## The tail's facts -/

/-- **The own rows' counters kept** by a function of `armOwnFns` (`checkerProg_armOwn`). -/
theorem ownKeep_checker (bs : List UInt8) {f : FnName} (hf : f ∈ armOwnFns) :
    OwnKeepF (Prog.subPB bs checkerProg) f := by
  intro n vs m r m' h
  refine ownC_frame (run_memFrame (closedW_subPB bs checkerProg_armOwn) hf (Arena.run_of_callW h)).1 ?_
    (by decide +kernel)
  intro b hb g t he
  have hn := (List.mem_filter.mp hb).2
  subst he
  revert hn
  unfold tierA oixArr; generalize (t &&& 1 != 0) = c
  cases c <;> split <;> (try split) <;> decide

/-- **The recursor stage's memos kept** by a function of `armRcFns` (`checkerProg_armRc`). -/
theorem rcKeep_checker (bs : List UInt8) {f : FnName} (hf : f ∈ armRcFns) :
    RcKeepF (Prog.subPB bs checkerProg) f := by
  have hus : UsF (Prog.subPB bs checkerProg) := by prog_bundle []
  exact fun _ _ _ _ _ h hM => RcMR.ofClosedL (by prog_bundle [] : ProgHas (Prog.subPB bs checkerProg) L.Ind.hbLeafP) (closedWL_subPB bs checkerProg_armRc) hus hf h hM

/-- **A well-formed `MAM` memo kept** by a function of `armMaFns` (`checkerProg_armMa`). -/
theorem maKeep_checker (bs : List UInt8) {f : FnName} (hf : f ∈ armMaFns) :
    MaKeepF (Prog.subPB bs checkerProg) f := by
  have hma : MaProg (Prog.subPB bs checkerProg) := by prog_bundle []
  exact fun _ _ _ _ _ h hM => maMR.ofClosedL (closedWL_subPB bs checkerProg_armMa) hma hf h hM

/-- `check_block_rec`'s `MaKeepF` callees (`icr_ref`'s `hMa`). -/
theorem grcMaKeep_checker (bs : List UInt8) :
    ∀ f ∈ ["gen_rec_check_prep", "class_fe_r", "block_shape_names_of", "flush_caches"],
      MaKeepF (Prog.subPB bs checkerProg) f := by
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> exact maKeep_checker bs (mem_of_tree armMaTree.eq (by decide +kernel))

set_option maxRecDepth 20000 in
/-- **`gen_rec_check`'s program bundle** (`GrcProgE`; `CrsProgE.maKeep` by `maKeep_checker`). -/
theorem grcProgE_checker (bs : List UInt8) : GrcProgE (Prog.subPB bs checkerProg) := by
  have hmk : ∀ (n : Nat) (vs : List Word) (m : Mem) (r : List Word) (m' : Mem),
      callW (Prog.subPB bs checkerProg) n "class_gen_rule" vs m = some (r, m') →
        (∃ mp, maMR m mp) → ∃ mp, maMR m' mp :=
    maKeep_checker bs (mem_of_tree armMaTree.eq (by decide +kernel))
  prog_bundle [hmk, checkerProg_cvgAgreePB bs, checkerProg_ivAgreePB bs, checkerProg_armAgreePB bs,
    checkerProg_cvgIn.subPB bs, checkerProg_ivIn.subPB bs, checkerProg_armIn.subPB bs]

set_option maxRecDepth 20000 in
/-- **`check_block_tail_stream`'s contract at the substituted checker program** (`tsRefS_of`), from
`stream_recs_check`'s. -/
theorem tsRefS_checker (bs : List UInt8) (dn : ConRon.Arena.NIdx → Option ConLeche.Name)
    (hsr : StreamRecsRefS (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) dn) :
    TsRefS (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) dn := by
  have P : TsProg (Prog.subPB bs checkerProg) := by prog_bundle []
  refine tsRefS_of P hsr (fun f hf => rcKeep_checker bs ?_)
    (absKeep_of_closed (closedW_subPB bs checkerProg_armAbs) armAbsA_free armAbsC_free
      (mem_of_tree armAbsTree.eq (by decide +kernel)))
    (indArmKeep_checker bs _ (by simp [tailKeepCalleesC, grcKeepCalleesC]))
    (ownKeep_checker bs (mem_of_tree armOwnTree.eq (by decide +kernel)))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl <;> exact mem_of_tree armRcTree.eq (by decide +kernel)

set_option maxRecDepth 20000 in
/-- **`check_block_tail`'s contract at the substituted checker program** (`tailRefS_of`), from
`stream_nested_ok`'s step (`SnoSim`, through `streamRecsRefS_checker` and `tsRefS_checker`). -/
theorem tailRefS_checker (bs : List UInt8) (hr : RomOK bs) (hpre : bs = romData ++ bs.drop romData.length)
    (dn : ConRon.Arena.NIdx → Option ConLeche.Name) (hSno : SnoSim (Prog.subPB bs checkerProg) dn) :
    TailRefS (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) dn := by
  have hAP := indArmProgs_checker bs hr hpre
  have hP : TailProg (Prog.subPB bs checkerProg) := by prog_bundle []
  have hMc : McLook (Prog.subPB bs checkerProg) := by prog_bundle []
  have hF : FtProg (Prog.subPB bs checkerProg) := by prog_bundle []
  have hWt : WhnfTopE (Prog.subPB bs checkerProg) :=
    whnfTop_stageE (by prog_bundle []) (fun n => (checkerProg_knotTopPB bs).knotOK n) (checkerProg_knotEPB bs)
  have hfR : ∀ f ∈ grcMemoCallees, RcKeepF (Prog.subPB bs checkerProg) f := by
    intro f hf
    simp only [grcMemoCallees, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl <;> exact rcKeep_checker bs (mem_of_tree armRcTree.eq (by decide +kernel))
  have hRk : ∀ f ∈ tailPreCallees, RcKeepF (Prog.subPB bs checkerProg) f := by
    intro f hf
    simp only [tailPreCallees, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl <;> exact rcKeep_checker bs (mem_of_tree armRcTree.eq (by decide +kernel))
  have hMk : ∀ f ∈ tailPreCallees, MaKeepF (Prog.subPB bs checkerProg) f := by
    intro f hf
    simp only [tailPreCallees, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl <;> exact maKeep_checker bs (mem_of_tree armMaTree.eq (by decide +kernel))
  exact tailRefS_of hAP.kp (checkerProg_thmArmPB bs hr hpre).ccv hAP.apd hAP.crk (checkerProg_crfPB bs)
    hAP.ilpf hAP.opf hAP.lc hAP.lt hP hMc (grcProgE_checker bs) hF hWt (checkerProg_ccvSimsPB bs dn) hfR
    (fun f hf => rcKeep_checker bs (armRc_grc f hf)) (grcMaKeep_checker bs)
    (ownKeep_checker bs (mem_of_tree armOwnTree.eq (by decide +kernel)))
    (fun f hf => indArmKeep_checker bs f (List.mem_append_left _ (List.mem_append_right _ hf))) hRk hMk
    (tsRefS_checker bs dn (streamRecsRefS_checker bs dn hSno))
    (maKeep_checker bs (armMa_pass _ (by simp)))
    (fun _ _ _ _ _ h hM => mcMR.ofClosed (closedW_subPB bs checkerProg_armMc)
      (mem_of_tree armMcTree.eq (by decide +kernel)) h hM)

set_option maxRecDepth 20000 in
/-- **`check_block`'s callees' contracts at the substituted checker program** (from
`stream_nested_ok`'s step `SnoSim`, the tail's last hypothesis). -/
theorem cbRefs_checker (bs : List UInt8) (hr : RomOK bs)
    (hpre : bs = romData ++ bs.drop romData.length) (hSno : ∀ dn, SnoSim (Prog.subPB bs checkerProg) dn) :
    ∀ dn, DnInj dn → CbRefs (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) dn := by
  intro dn _
  have H := declConstsProg_checker bs hr hpre
  have look : CbLook (Prog.subPB bs checkerProg) := by prog_bundle []
  have hF : FlushProg (Prog.subPB bs checkerProg) := by prog_bundle []
  have hnv : VerdictCtxU (Prog.subPB bs checkerProg) → closedNV (Prog.subPB bs checkerProg) nvFns = true :=
    fun hG => hG.nv
  have hfl : FlushRefS (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) dn :=
    flushRefS_of (dn := dn) hF hnv
  have hbr : BrRefS (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) :=
    brRefS_of H.toTablesProg.toBlockProg.toRecsProg H.leaf hnv
  have hbt : BtRefS (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) dn :=
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
  -- nest_seeds: their contracts still to prove (class_seeds, nest_seeds done) (Pass.lean's BncRefS … NsdRefS)
  have hbnc : BncRefS (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) dn :=
    bncRefS_checker bs hr hpre dn
  have hcls : ClsRefS (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) dn :=
    clsRefS_checker bs hr hpre dn
  have hpos : PosRefS (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) dn :=
    posRefS_checker bs hr hpre dn
  have hsd : SeedsRefS (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) dn :=
    seedsRefS_checker bs dn
  have hnsd : NsdRefS (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) dn :=
    nsdRefS_checker bs hr hpre dn
  have hpass : PassRefS (VerdictCtxU (Prog.subPB bs checkerProg)) (Prog.subPB bs checkerProg) dn :=
    passRefS_of ⟨hpl, hinds, hct, hbnc, hcls, hpos, hsd, hnsd⟩ hnv
  exact ⟨look, hnm, hrm, hfl, hbir, hwm, hpass, tailRefS_checker bs hr hpre dn (hSno dn), hbr, hbt, hpd⟩

end L.Checker
