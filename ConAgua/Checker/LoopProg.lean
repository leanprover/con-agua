module

import ConAgua.Checker.LoopDeclArm
import ConAgua.Checker.LoopDeclAgree
import ConAgua.Rom.CIReadRefs
public import ConAgua.Arena.LoopStart
public import ConAgua.Checker.RomCProg
meta import ConAgua.Checker.LoopProgInd
meta import ConAgua.Checker.LoopDeclArm
meta import ConAgua.Checker.LoopDeclAgree
meta import ConAgua.Checker.IndCore
meta import ConAgua.Checker.CoreErec
meta import ConAgua.Checker.LeafAll
meta import ConAgua.Checker.LoopAll
meta import ConAgua.Checker.RomProgB
meta import ConAgua.Rom.CIReadRefs
meta import ConAgua.Arena.LoopStart
meta import ConAgua.Checker.IndMemoClosed
import ConAgua.Checker.LoopProgTac
public import ConAgua.Checker.Prog
public import ConAgua.Rom.Stage
import all ConAgua.Arena.BasisL
import all ConAgua.Arena.IndDeclConsts
import all ConAgua.Arena.IndStream
import all ConAgua.Rom.CIConst
import all ConAgua.Arena.Abs1
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
import all ConAgua.Arena.FreezeCmp
import all ConAgua.Checker.CmpSeqEntry
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
import all ConAgua.Arena.NatSized
public import ConAgua.Arena.DeclArmLoop
import ConAgua.Compiler.Main

@[expose] public section

/-!
# The declaration loop's program hypotheses at the substituted checker program (lane `loopt3`)

The ROM readers' refinements (`RomRefs`) hold of a program whose readers read the ROM as constant
data (`romRefs_of`), not of `checkerProg`, whose readers read the buffer `PB`. As for the ROM
stages (`Rom/Stage.lean`), the check phase is proved at `checkerProg.subPB bs` (`bs` the buffer
`pb_check` accepted) and carried to `checkerProg` by `triple_subPB`. Here the pieces of its program
hypotheses at the substituted program (assembled for the jobs in `JobsProg.lean`) and
`LoopTopProg` (`checkerProg_loopTopPB`).

* Lookups: `prog_bundle` (`LoopProgTac.lean`): a function that reads no pin data is unchanged
  (`lkN`), the seven readers (`pbReadFns`) are their `subPB` (`lkR`).
* Write sets: `subPB` changes no store and no call (`Stmt.okW_subPB`), so `closedW` carries over
  (`closedW_subPB`, `StepIn.subPB`).
* Text agreements: on a name that is not a reader, the two programs agree
  (`checkerProg_subPB_lookup`, from the per-chunk check `checkerProg_pbFree`).
* `RomRefs`: `romRefs_of` from `RomCIProg bs` (`checkerProg_itemsProg` and the readers' lookups),
  for a buffer `bs` with `RomOK bs` starting with `romData` (what `pb_check` establishes).
-/

namespace L.Checker

open L L.Rom L.Arena L.Compiler

set_option maxRecDepth 100000

/-! ## Write sets under the substitution -/

theorem _root_.L.ctlIdx_subPB (bs : List UInt8) {e : Expr} {ws : List Word} (h : ctlIdx e = some ws) :
    ctlIdx (e.subPB bs) = some ws := by
  unfold ctlIdx at h
  split at h
  · cases h; rfl
  · cases h; rfl
  · cases h

theorem _root_.L.Stmt.okW_subPB (bs : List UInt8) {ctl : ArrId} {A : List TieredArray} {C : List Word}
    {fs : List FnName} : ∀ {s : Stmt}, s.okW ctl A C fs = true → (s.subPB bs).okW ctl A C fs = true
  | .st64 a i e, h => by
    simp only [Stmt.okW, Stmt.subPB] at h ⊢
    split at h
    · rename_i hc
      simp only [hc, ite_true] at h ⊢
      split at h
      · rename_i ws hw; rw [ctlIdx_subPB bs hw]; exact h
      · cases h
    · rename_i hc; simp only [hc, ite_false] at h ⊢; exact h
  | .seq s t, h | .ite _ s t, h => by
    simp only [Stmt.okW, Stmt.subPB, Bool.and_eq_true] at h ⊢
    exact ⟨Stmt.okW_subPB bs h.1, Stmt.okW_subPB bs h.2⟩
  | .while _ s, h => by
    simp only [Stmt.okW, Stmt.subPB] at h ⊢; exact Stmt.okW_subPB bs h
  | .st8 .., h => by simp [Stmt.okW] at h
  | .call .., h => by simpa [Stmt.okW, Stmt.subPB] using h
  | .st64t .., h => by simpa [Stmt.okW, Stmt.subPB] using h
  | .st32t .., h => by simpa [Stmt.okW, Stmt.subPB] using h
  | .copy64 d .., h | .copy8w d .., h => by cases d <;> simpa [Stmt.okW, Stmt.subPB, WArr.okW, WArr.subPB] using h
  | .scan8 .., _ => rfl
  | .skip, _ | .set .., _ | .brk, _ | .ret _, _ | .abort _, _ | .gset .., _ => rfl

theorem closedW_subPB (bs : List UInt8) {ctl : ArrId} {p : Prog} {A : List TieredArray} {C : List Word}
    {fs : List FnName} (h : closedW ctl p A C fs = true) :
    closedW ctl (Prog.subPB bs p) A C fs = true := by
  simp only [closedW, List.all_eq_true] at h ⊢
  intro f hf
  have := h f hf
  rw [lookup_subPB]
  cases e : p.lookup f with
  | none => rfl
  | some fd =>
    simp only [e] at this
    exact Stmt.okW_subPB bs this

theorem closedWL_subPB (bs : List UInt8) {ctl : ArrId} {p : Prog} {A : List TieredArray} {C : List Word}
    {fs L : List FnName} (h : closedWL ctl p A C fs L = true) :
    closedWL ctl (Prog.subPB bs p) A C fs L = true := by
  simp only [closedWL, List.all_eq_true] at h ⊢
  intro f hf
  have := h f hf
  rw [lookup_subPB]
  cases e : p.lookup f with
  | none => rfl
  | some fd =>
    simp only [e] at this
    exact Stmt.okW_subPB bs this

theorem _root_.L.Arena.StepIn.subPB (bs : List UInt8) {p : Prog} {fs : List FnName} (h : StepIn p fs) :
    StepIn (Prog.subPB bs p) fs :=
  let ⟨F, hF, hc⟩ := h; ⟨F, hF, closedW_subPB bs hc⟩

/-! ## The functions that read no pin data -/

/-- The functions of `checkerProg` that read the pin-data buffer. -/
def pbReadFns : List FnName :=
  ["pb_check", "rom_expr", "rom_items", "rom_level", "rom_name", "rom_put", "rom_u64"]

names_tree pbReadTree : pbReadFns

/-- Every function of `checkerProg` but the readers reads no pin data. -/
prog_all checkerProg_pbFree : checkerProg
  (fun x => (pbReadTree.find (nameCode x.1)).isSome || x.2.body.noPB)

/-- **Off the readers the substituted program is `checkerProg`.** -/
theorem checkerProg_subPB_lookup (bs : List UInt8) {f : FnName}
    (hf : (pbReadTree.find (nameCode f)).isSome = false) :
    (Prog.subPB bs checkerProg).lookup f = checkerProg.lookup f := by
  cases e : checkerProg.lookup f with
  | none => rw [lookup_subPB, e]; rfl
  | some fd =>
    have h := checkerProg_pbFree _ (L.Compiler.mem_of_lookup e)
    simp only [hf, Bool.false_or] at h
    exact lookup_subPB_noPB bs e h

/-- Agreement of the substituted program with a text, off the readers. -/
theorem agree_subPB (bs : List UInt8) {q : Prog} {fs : List FnName}
    (hn : fs.all (fun f => !(pbReadTree.find (nameCode f)).isSome) = true)
    (h : ∀ f ∈ fs, f ∉ openFns → checkerProg.lookup f = q.lookup f) :
    ∀ f ∈ fs, f ∉ openFns → (Prog.subPB bs checkerProg).lookup f = q.lookup f := by
  intro f hf ho
  have := List.all_eq_true.mp hn f hf
  rw [checkerProg_subPB_lookup bs (by simpa using this)]
  exact h f hf ho

theorem cvgFns_noPB : cvgFns.all (fun f => !(pbReadTree.find (nameCode f)).isSome) = true := by
  decide +kernel
theorem ivFns_noPB : ivFns.all (fun f => !(pbReadTree.find (nameCode f)).isSome) = true := by
  decide +kernel
theorem armFns_noPB : armFns.all (fun f => !(pbReadTree.find (nameCode f)).isSome) = true := by
  decide +kernel

theorem checkerProg_cvgAgreePB (bs : List UInt8) :
    ∀ f ∈ cvgFns, f ∉ openFns → (Prog.subPB bs checkerProg).lookup f = cvgProg.lookup f :=
  agree_subPB bs cvgFns_noPB checkerProg_cvgAgree

theorem checkerProg_ivAgreePB (bs : List UInt8) :
    ∀ f ∈ ivFns, f ∉ openFns → (Prog.subPB bs checkerProg).lookup f = ivProg.lookup f :=
  agree_subPB bs ivFns_noPB checkerProg_ivAgree

theorem checkerProg_armAgreePB (bs : List UInt8) :
    ∀ f ∈ armFns, f ∉ openFns → (Prog.subPB bs checkerProg).lookup f = armText.lookup f :=
  agree_subPB bs armFns_noPB checkerProg_armAgree

theorem lvlFns_cvg : ∀ f ∈ lvlFns, f ∈ cvgFns ∧ f ∉ openFns := by decide +kernel

theorem checkerProg_lvlTextPB (bs : List UInt8) :
    ∀ f ∈ lvlFns, (Prog.subPB bs checkerProg).lookup f = cvgProg.lookup f :=
  fun f hf => checkerProg_cvgAgreePB bs f (lvlFns_cvg f hf).1 (lvlFns_cvg f hf).2

theorem checkerProg_natArmPB (bs : List UInt8) :
    ProgHas (Prog.subPB bs checkerProg) natArmProg' := by prog_bundle []

/-- The canonical comparisons' lookups at the substituted checker. -/
theorem checkerProg_canonPB (bs : List UInt8) : L.Ind.CanonProg (Prog.subPB bs checkerProg) := by
  prog_bundle []

theorem checkerProg_natAgreePB (bs : List UInt8) :
    ∀ f ∈ natFns, (Prog.subPB bs checkerProg).lookup f = natArmProg'.lookup f :=
  ProgHas.agreeNames (checkerProg_natArmPB bs)

/-! ## The ROM readers -/

theorem checkerProg_romCIProg (bs : List UInt8) :
    RomCIProg romDataLit (Prog.subPB bs checkerProg) := by
  prog_bundle [checkerProg_romCVia bs, checkerProg_romCRen bs]

/-- **The ROM readers of the substituted program refine the twin** (they read the constant data,
so any buffer). -/
theorem checkerProg_romRefsPB (bs : List UInt8) (_hr : RomOK bs)
    (_hpre : bs = romData ++ bs.drop romData.length) : RomRefs (Prog.subPB bs checkerProg) :=
  romRefs_of _ (checkerProg_romCIProg bs)

/-! ## The loop's program hypotheses -/

/-- **The loop's own program hypotheses at the substituted checker program.** -/
theorem checkerProg_loopTopPB (bs : List UInt8) : LoopTopProg (Prog.subPB bs checkerProg) := by
  prog_bundle []

end L.Checker
