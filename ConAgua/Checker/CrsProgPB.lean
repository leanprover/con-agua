module

public import ConAgua.Checker.Prog
public import ConAgua.Arena.Jobs
public import ConAgua.Arena.JobsCrs
public import ConAgua.Checker.JobsClosed
public import ConAgua.Checker.ArmsT
import ConAgua.Checker.LoopProgTac
meta import ConAgua.Checker.LoopProgTac
meta import ConAgua.Checker.JobsClosed
meta import ConAgua.Checker.ArmsT
meta import ConAgua.Checker.Prog
meta import ConAgua.Arena.Jobs
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
# `check_record_sol`'s facts at the checker's program (lane compare)

`CrsSpec` (`Arena/Jobs.lean`, what `record_job` takes of `check_record_sol` with a solution) at the
substituted checker program, by `crsSpec_of` (`Arena/JobsCrs.lean`): the comparisons' write set
(`ConeProg.cmpClosed`, one kernel check per chunk, `prog_all`), the lookups, the arms' facts
(`Checker/ArmsT.lean`) and `check_record_sol`'s write set (`checkerProg_crsW`). The route's kept
memory `CrsKeep` (semantic facts on the models) is taken as a hypothesis.
-/

namespace L.Checker

open L.Arena L.Ind L.Compiler L.Rom ConRon.Arena

/-- `cmpFns` as a tree of name codes. -/
names_tree cmpTree : cmpFns

/-- The arrays of `cmpA`, as a test. -/
def cmpPa (b : TieredArray) : Bool := checkerWordArrays.contains b && !(cmpKeep.contains b)

/-- The `CTL` words of `cmpC`, as a test. -/
def cmpPc (x : Word) : Bool :=
  decide (x.toNat < 1024) && (decide (x.toNat < 220) || decide (228 < x.toNat))

theorem cmpPa_mem (b : TieredArray) (h : cmpPa b = true) : b ∈ cmpA := by
  simp only [cmpPa, Bool.and_eq_true, List.contains_iff_mem, Bool.not_eq_true'] at h
  simp only [cmpA, List.mem_filter, decide_eq_true_eq]
  exact ⟨h.1, by simpa using h.2⟩

theorem cmpPc_mem (x : Word) (h : cmpPc x = true) : x ∈ cmpC := by
  simp only [cmpPc, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  simp only [cmpC, List.mem_filter, List.mem_map, List.mem_range, decide_eq_true_eq]
  exact ⟨x.toNat, ⟨h.1, h.2⟩, UInt64.ofNat_toNat⟩

/-- Every function of the checker passes the comparisons' per-function check. -/
prog_all checkerProg_cmpChk : checkerProg (wsChk CTL cmpPa cmpPc cmpTree)

/-- **The comparisons' write set** (`ConeProg.cmpClosed`). -/
theorem checkerProg_cmpClosed : closedA checkerProg cmpA cmpC cmpFns = true :=
  closedW_of_all cmpTree.eq cmpPa_mem cmpPc_mem checkerProg_cmpChk

/-- `ndFns` and `ndDepFns` as trees of name codes. -/
names_tree ndTree : ndFns
names_tree ndDepTree : ndDepFns

/-- The arrays of `ndA`, as a test. -/
def ndPa (b : TieredArray) : Bool := b == (NDM : TieredArray) || b == (NACC : TieredArray)
/-- The `CTL` words of `ndC`, as a test. -/
def ndPc (x : Word) : Bool := x == 220 || x == 221 || x == 227
/-- The arrays of `nat_op_deps`' write set, as a test. -/
def ndDepPa (b : TieredArray) : Bool := b == (IW : TieredArray)
/-- The `CTL` words of `nat_op_deps`' write set, as a test. -/
def ndDepPc (x : Word) : Bool := x == 200

theorem ndPa_mem (b : TieredArray) (h : ndPa b = true) : b ∈ ndA := by
  simp only [ndPa, Bool.or_eq_true, beq_iff_eq] at h; rcases h with rfl | rfl <;> simp [ndA]
theorem ndPc_mem (x : Word) (h : ndPc x = true) : x ∈ ndC := by
  simp only [ndPc, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (rfl | rfl) | rfl <;> simp [ndC, NTOPC]
theorem ndDepPa_mem (b : TieredArray) (h : ndDepPa b = true) : b ∈ [(IW : TieredArray)] := by
  simp only [ndDepPa, beq_iff_eq] at h; simp [h]
theorem ndDepPc_mem (x : Word) (h : ndDepPc x = true) : x ∈ ([200] : List Word) := by
  simp only [ndDepPc, beq_iff_eq] at h; simp [h]

/-- Every function of the checker passes the needs walk's per-function check. -/
prog_all checkerProg_ndChk : checkerProg (wsChk CTL ndPa ndPc ndTree)
/-- Every function of the checker passes `nat_op_deps`' per-function check. -/
prog_all checkerProg_ndDepChk : checkerProg (wsChk CTL ndDepPa ndDepPc ndDepTree)

/-- **The needs walk's write set** (`NeedsProg.closed`). -/
theorem checkerProg_ndClosed : closedA checkerProg ndA ndC ndFns = true :=
  closedW_of_all ndTree.eq ndPa_mem ndPc_mem checkerProg_ndChk
/-- **`nat_op_deps`' write set** (`NeedsFpProg.closedDeps`). -/
theorem checkerProg_ndDepClosed : closedA checkerProg [IW] [200] ndDepFns = true :=
  closedW_of_all ndDepTree.eq ndDepPa_mem ndDepPc_mem checkerProg_ndDepChk

section crs
variable (bs : List UInt8)

/-- **The cone's program facts at the checker.** -/
theorem checkerProg_coneProgPB (hr : RomOK bs) (hpre : bs = romData ++ bs.drop romData.length) :
    ConeProg (Prog.subPB bs checkerProg) := by
  have hR := checkerProg_romRefsPB bs hr hpre
  prog_bundle [closedW_subPB bs checkerProg_cmpClosed, closedW_subPB bs checkerProg_ndClosed,
    closedW_subPB bs checkerProg_ndDepClosed, checkerProg_cvgAgreePB bs,
    StepIn.subPB bs checkerProg_cvgIn, hR.ci, hR.cv, hR.expr, hR.basis, hR.quot, hR.andPin,
    checkerProg_leafClosedPB bs, (checkerProg_knotTopPB bs).knot.instLP, (checkerProg_knotTopPB bs).knot.hcl,
    (checkerProg_knotTopPB bs).knot.ls, checkerProg_coreStagePB bs, checkerProg_rulesPB bs]

/-- **`check_record_sol`'s program facts at the checker**, given the route's kept memory. -/
theorem checkerProg_crsProgPB (hr : RomOK bs) (hpre : bs = romData ++ bs.drop romData.length)
    (hkeep : L.Arena.CrsKeep (Prog.subPB bs checkerProg)) : L.Arena.CrsProg (Prog.subPB bs checkerProg) :=
  ⟨checkerProg_coneProgPB bs hr hpre, by chk_lk, by chk_lk, by chk_lk, by chk_lk,
    checkerProg_axArmPB bs hr hpre, checkerProg_bnoPB bs hr hpre, checkerProg_leafClosedPB bs, hkeep⟩

/-- **What `record_job` takes of `check_record_sol` at the checker** (`CrsSpec`), given `check_decl`'s
program facts and the route's kept memory. -/
theorem checkerProg_crsSpecPB (hr : RomOK bs) (hpre : bs = romData ++ bs.drop romData.length)
    {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {ds : Array IDeclaration}
    (hcdP : CdProg pins dn ds (Prog.subPB bs checkerProg))
    (hkeep : L.Arena.CrsKeep (Prog.subPB bs checkerProg)) : CrsSpec pins dn ds (Prog.subPB bs checkerProg) :=
  crsSpec_of (checkerProg_crsProgPB bs hr hpre hkeep) hcdP (checkerProg_knotStagePB bs)
    (checkerProg_apdPB bs) (checkerProg_crKeepPB bs) (checkerProg_crfPB bs) (checkerProg_ccvSimsPB bs dn)
    (let ⟨F, h, hc⟩ := checkerProg_crsW; ⟨F, h, closedW_subPB bs hc⟩)

end crs

end L.Checker
