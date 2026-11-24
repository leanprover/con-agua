module

public import ConAgua.Arena.DeclCheckT
public import ConAgua.Checker.LitClosed
public import ConAgua.Checker.IndLeaves
public import ConAgua.Checker.LeafAll
public import ConAgua.Checker.LoopProg
public import ConAgua.Checker.LoopDecl
public import ConAgua.Checker.QuotFns
public import ConAgua.Checker.IndMemoClosed
public import ConAgua.Checker.IndArm
public import ConAgua.Checker.LoopProgInd
public import ConAgua.Checker.CrLeaves
public import ConAgua.Verdict.KnotAllE
public import ConAgua.Arena.PinListRef
public import ConAgua.Checker.KindIn
import ConAgua.Checker.LoopProgTac
meta import ConAgua.Checker.LoopProgTac
meta import ConAgua.Checker.LitClosed
meta import ConAgua.Checker.LeafAll
meta import ConAgua.Arena.DeclReduceSpec2
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
# `check_decl`'s program facts at the substituted checker program

`CdProg pins dn ds (Prog.subPB bs checkerProg)` (`Arena/DeclCheckT.lean`), the pipeline's
`JobProg.cd`: the lookups (`CheckDeclProg`, `IbeProg`), the write sets (`StepIn`, `IndMemoClosed`,
`LeafClosed`, `LitShapeClosed`, through `closedW_subPB`), the one-constant arms' contracts (`ArmsT`)
and the inductive arm's (`IndArmSpec`, a premise: the inductive stage's top theorem).
-/

namespace L.Checker

open L.Arena L.Ind L.Compiler

/-! ## The leaves' write set -/

names_tree leafTree : leafFns

/-- Every function of the checker passes the leaves' per-function check. -/
prog_all checkerProg_leafChk : checkerProg (wsChk CTL leafPa leafPc leafTree)

theorem checkerProg_leafClosed : LeafClosed checkerProg :=
  closedW_of_all leafTree.eq leafPa_mem leafPc_mem checkerProg_leafChk

theorem checkerProg_leafClosedPB (bs : List UInt8) : LeafClosed (Prog.subPB bs checkerProg) :=
  closedW_subPB bs checkerProg_leafClosed

/-- `rcvaFns` (the closure of `reduce_op_cv_a`) as a tree of name codes. -/
names_tree rcvaTree : rcvaFns

/-- The arrays of `rcvaA`, as a test. -/
def rcvaPa (a : TieredArray) : Bool :=
  leafPa a && a != OIXA && a != OIXS && a != OIXN && a != tier1 OIXA && a != tier1 OIXS &&
    a != tier1 OIXN

/-- The `CTL` words of `rcvaC`, as a test. -/
def rcvaPc (w : Word) : Bool := leafPc w && w != 133

theorem rcvaPa_mem (a : TieredArray) (h : rcvaPa a = true) : a ∈ rcvaA := by
  simp only [rcvaPa, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  simp only [rcvaA, List.mem_filter, decide_eq_true_eq]
  exact ⟨leafPa_mem a h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem rcvaPc_mem (w : Word) (h : rcvaPc w = true) : w ∈ rcvaC := by
  simp only [rcvaPc, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  simp only [rcvaC, List.mem_filter, decide_eq_true_eq]
  exact ⟨leafPc_mem w h.1, h.2⟩

/-- Every function of the checker passes `reduce_op_cv_a`'s per-function check. -/
prog_all checkerProg_rcvaChk : checkerProg (wsChk CTL rcvaPa rcvaPc rcvaTree)

theorem checkerProg_rcvaClosed : RcvaClosed checkerProg :=
  closedW_of_all rcvaTree.eq rcvaPa_mem rcvaPc_mem checkerProg_rcvaChk

theorem checkerProg_rcvaClosedPB (bs : List UInt8) : RcvaClosed (Prog.subPB bs checkerProg) :=
  closedW_subPB bs checkerProg_rcvaClosed

theorem checkerProg_litShapeClosedPB (bs : List UInt8) :
    LitShapeClosed (Prog.subPB bs checkerProg) :=
  closedW_subPB bs checkerProg_litShapeClosed

theorem checkerProg_knotStagePB (bs : List UInt8) : KnotStageProg (Prog.subPB bs checkerProg) :=
  ⟨checkerProg_knotTopPB bs, checkerProg_coreStagePB bs⟩

/-! ## The arms -/

open L.Rom ConRon.Arena

section arms
variable (bs : List UInt8)

theorem checkerProg_axArmPB (hr : RomOK bs) (hpre : bs = romData ++ bs.drop romData.length) :
    AxArmProg (Prog.subPB bs checkerProg) := by
  have hR := checkerProg_romRefsPB bs hr hpre
  prog_bundle [checkerProg_cvgAgreePB bs, StepIn.subPB bs checkerProg_cvgIn, hR.ci, hR.cv,
    hR.expr, hR.basis, hR.quot, hR.andPin]
theorem checkerProg_thmArmPB (hr : RomOK bs) (hpre : bs = romData ++ bs.drop romData.length) :
    ThmArmProg (Prog.subPB bs checkerProg) :=
  ⟨by chk_lk, (checkerProg_axArmPB bs hr hpre).ccv⟩

theorem checkerProg_opqArmPB (hr : RomOK bs) (hpre : bs = romData ++ bs.drop romData.length) :
    OpqArmProg (Prog.subPB bs checkerProg) := by
  have hR := checkerProg_romRefsPB bs hr hpre
  prog_bundle [checkerProg_cvgAgreePB bs, StepIn.subPB bs checkerProg_cvgIn, hR.ci, hR.cv,
    hR.expr, hR.basis, hR.quot, hR.andPin, checkerProg_rcvaClosedPB bs]
theorem checkerProg_quotArmPB : QuotArmProg (Prog.subPB bs checkerProg) := by
  prog_bundle [checkerProg_leafClosedPB bs]
theorem checkerProg_rulesPB : RulesProg (Prog.subPB bs checkerProg) := by
  prog_bundle [(checkerProg_knotTopPB bs).knot.instLP, (checkerProg_knotTopPB bs).knot.hcl,
    (checkerProg_knotTopPB bs).knot.ls, checkerProg_coreStagePB bs,
    closedW_subPB bs checkerProg_quotClosed, closedW_subPB bs checkerProg_plClosed]
theorem checkerProg_strLitPB : StrLitProg (Prog.subPB bs checkerProg) :=
  (checkerProg_knotTopPB bs).knot.str

theorem checkerProg_ccvSimsPB (dn : NIdx → Option ConLeche.Name) :
    CcvSims (Prog.subPB bs checkerProg) dn :=
  ccvSims_of (checkerProg_strLitPB bs) (checkerProg_litShapeClosedPB bs) (by chk_lk) (by chk_lk) dn

theorem checkerProg_quotSimsPB (hr : RomOK bs) (hpre : bs = romData ++ bs.drop romData.length)
    {dn : NIdx → Option ConLeche.Name} (hq : QuotDn dn) :
    QuotSims (Prog.subPB bs checkerProg) dn :=
  quotSims_of'' (checkerProg_rulesPB bs) (by chk_lk) ((checkerProg_romRefsPB bs hr hpre).quot dn)
    (checkerProg_leafClosedPB bs) hq

/-- **The pinned basis blocks' program facts at the checker** (`basisRefs_of`'s premise; the
stream index's `DeclConstsProg.basis`). -/
theorem checkerProg_basisLProgPB (hr : RomOK bs) (hpre : bs = romData ++ bs.drop romData.length) :
    BasisLProg (Prog.subPB bs checkerProg) := by
  prog_bundle [checkerProg_rulesPB bs, checkerProg_leafClosedPB bs, checkerProg_romRefsPB bs hr hpre]

/-- **`pin_list_ok` refines `pinListOk` at the checker** (`check_basis_block`'s comparison,
`CbbProg.pl`). -/
theorem checkerProg_pinListOkRefPB (hr : RomOK bs) (hpre : bs = romData ++ bs.drop romData.length) :
    PinListOkRef (Prog.subPB bs checkerProg) :=
  pinListOkRef_of (by prog_bundle [checkerProg_basisLProgPB bs hr hpre])

theorem checkerProg_armStepPB {f : FnName} (hf : f ∈ declLoopFns) :
    StepIn (Prog.subPB bs checkerProg) [f] :=
  StepIn.subPB bs (checkerProg_stepIn fun _ h => by simp only [List.mem_singleton] at h; exact h ▸ hf)

/-! ## `check_decl` -/

theorem checkerProg_indMemoPB : IndMemoClosed (Prog.subPB bs checkerProg) :=
  closedWL_subPB bs checkerProg_indMemo

theorem checkerProg_apdPB : ApdF (Prog.subPB bs checkerProg) := by prog_bundle []
theorem checkerProg_crfPB : CrfF (Prog.subPB bs checkerProg) := by prog_bundle []
theorem checkerProg_crKeepPB : CrKeep (Prog.subPB bs checkerProg) :=
  ⟨checkerProg_indMemoPB bs, checkerProg_crLeavesPB bs⟩
theorem checkerProg_ibePB : IbeProg (Prog.subPB bs checkerProg) := by prog_bundle []
theorem checkerProg_checkDeclPB : CheckDeclProg (Prog.subPB bs checkerProg) := by prog_bundle []
theorem checkerProg_flushPB : FlushProg (Prog.subPB bs checkerProg) := by prog_bundle []

theorem checkerProg_kindInPB : KindIn (Prog.subPB bs checkerProg) :=
  ⟨_, kindFns_sub, closedW_subPB bs checkerProg_kindStepClosed⟩

/-- **The reserved names' check's program facts at the checker** (`CdProg.bno`). -/
theorem checkerProg_bnoPB (hr : RomOK bs) (hpre : bs = romData ++ bs.drop romData.length) :
    L.Ind.BnoProg (Prog.subPB bs checkerProg) := by
  prog_bundle [basisRefs_of (checkerProg_basisLProgPB bs hr hpre), checkerProg_romRefsPB bs hr hpre,
    checkerProg_pinListOkRefPB bs hr hpre, checkerProg_leafClosedPB bs]

/-- **`check_decl`'s program facts at the substituted checker program**: the axiom and quotient
arms here, the value arms' contracts and the inductive arm's as premises; the decoder `dn`
injective (`DnInj`), with `Quot`'s universe name under it (`QuotDn`). -/
theorem checkerProg_cdProgPB (hr : RomOK bs) (hpre : bs = romData ++ bs.drop romData.length)
    {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration}
    (hdn : DnInj dn) (hq : QuotDn dn)
    (hdf : ∀ cv v hh, ArmSpecT pins dn ds (Prog.subPB bs checkerProg) "check_decl_defn"
      (.defnDecl cv v hh))
    (hind : IndArmSpec (Prog.subPB bs checkerProg) dn) :
    CdProg pins dn ds (Prog.subPB bs checkerProg) where
  cd := checkerProg_checkDeclPB bs
  ibe := checkerProg_ibePB bs
  indIn := StepIn.subPB bs checkerProg_indIn
  kindIn := checkerProg_kindInPB bs
  indMemo := checkerProg_indMemoPB bs
  indLeaves := checkerProg_indLeavesPB bs
  fl := checkerProg_flushPB bs
  bno := checkerProg_bnoPB bs hr hpre
  arms :=
    { axiom_ := checkDeclAxiom_loopT (checkerProg_axArmPB bs hr hpre) (checkerProg_knotStagePB bs)
        (checkerProg_leafClosedPB bs) (checkerProg_apdPB bs) (checkerProg_crKeepPB bs)
        (checkerProg_crfPB bs) (checkerProg_ccvSimsPB bs dn) (checkerProg_quotSimsPB bs hr hpre hq) hdn
        (checkerProg_armStepPB bs (by decide)) (checkerProg_indMemoPB bs) (checkerProg_indLeavesPB bs)
      defn := hdf
      thm := checkDeclThm_loopT (checkerProg_thmArmPB bs hr hpre) (checkerProg_knotStagePB bs)
        (checkerProg_leafClosedPB bs) (checkerProg_apdPB bs) (checkerProg_crKeepPB bs)
        (checkerProg_crfPB bs) (checkerProg_ccvSimsPB bs dn) (checkerProg_armStepPB bs (by decide))
        (checkerProg_indMemoPB bs) (checkerProg_indLeavesPB bs)
      opaque_ := checkDeclOpaque_loopT (checkerProg_opqArmPB bs hr hpre) (checkerProg_knotStagePB bs)
        (checkerProg_leafClosedPB bs) (checkerProg_apdPB bs) (checkerProg_crKeepPB bs)
        (checkerProg_crfPB bs) (checkerProg_ccvSimsPB bs dn) (checkerProg_armStepPB bs (by decide))
        (checkerProg_indMemoPB bs) (checkerProg_indLeavesPB bs)
      quot := checkDeclQuot_loopT (checkerProg_quotArmPB bs) (checkerProg_quotSimsPB bs hr hpre hq)
        (checkerProg_armStepPB bs (by decide)) (checkerProg_indMemoPB bs) (checkerProg_indLeavesPB bs) }
  ind := hind

end arms

end L.Checker
