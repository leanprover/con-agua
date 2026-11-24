module

public import ConAgua.Checker.CmpSeqRun
import ConAgua.Verdict.ThreadsE
import ConAgua.Checker.NoVerdictTree
import ConAgua.Checker.NoVerdictClosed
import ConAgua.Compiler.WriteSetSplit
import ConAgua.Checker.PhaseBReads
meta import ConAgua.Checker.PhaseBReads
import ConAgua.Checker.LoopProgTac
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
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
# Modes `8` and `9`'s program facts at the checker (lane compare2, the sJ variant)

`checkerProg_cqSeq : CqSeqProg checkerProg`: the lookups, the switches' and the flush's triples
with their errors of class `0` (they are in the no-verdict set, `invoke_nv`), and the read set
(`check_bs`, `check_bc` are among the jobs' functions, `checkerProg_phaseBReads`).
-/

namespace L.Checker

open L L.Arena L.Compiler
open Std.WP
open scoped Lean.Order

/-- A spec of a no-verdict function of the checker, error-precise: its errors have class `0`. -/
theorem cq_nv {f : FnName} (hm : f ∈ nvFns) {n : Nat} {s₀ : St} {Q : List Word → St → Prop}
    (hS : ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) f [] ⦃fun r s' => Q r s'; ⊤⦄) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) f [] ⦃fun r s' => Q r s'; fun e => e.cls = 0⦄ := by
  have hN := invoke_nv checkerProg checkerProg_nv n f hm []
  apply M.triple_of_run'
  · intro s r s' hp hr
    exact M.of_run' (P := fun s => s = s₀) (Q := Q) (E := ⊤) hp hr hS
  · intro s e _ hr
    exact M.of_run_err (P := fun _ => True) trivial hr hN

/-- Modes `8` and `9`'s functions: the jobs' and the switches'. -/
def cqReadFns : List FnName :=
  ["check_bs", "check_bc", "cq_bank_s", "cq_ctl_s", "cq_bank_c", "cq_ctl_c",
   "cq_swap_eixa", "cq_swap_tixa", "cq_swap_eixs", "cq_swap_tixs", "cq_swap_eixn", "cq_swap_tixn",
   "cq_back_eixa", "cq_back_tixa", "cq_back_eixs", "cq_back_tixs", "cq_back_eixn", "cq_back_tixn"] ++
    phaseBJobFns

names_tree cqReadTree : cqReadFns

/-- Every function of the checker passes modes `8` and `9`'s per-function read check. -/
prog_all checkerProg_cqReadsChk : checkerProg (rdChk phaseBPa (fun _ => false) cqReadTree)

/-- **Modes `8` and `9`'s read set**: the call closure of `check_bs` and `check_bc` names only
word arrays other than `OUT`, `HDRF`, `CTLF` and no byte array. -/
theorem checkerProg_cqReads : readsIn checkerProg phaseBPa (fun _ => false) cqReadFns = true :=
  readsIn_of_all cqReadTree.eq checkerProg_cqReadsChk

/-- **Modes `8` and `9`'s program facts at the checker.** -/
theorem checkerProg_cqSeq : CqSeqProg checkerProg where
  check := by chk_lk
  bs := by chk_lk
  bc := by chk_lk
  bankS n s₀ := cq_nv (nv_mem (by decide +kernel))
    (cqBankS_spec checkerProg (by chk_lk) ⟨by chk_lk, by chk_lk, by chk_lk, by chk_lk, by chk_lk, by chk_lk⟩ n s₀)
  ctlS n s₀ := cq_nv (nv_mem (by decide +kernel)) (cqCtlS_spec checkerProg (by chk_lk) n s₀)
  bankC n s₀ := cq_nv (nv_mem (by decide +kernel))
    (cqBankC_spec checkerProg (by chk_lk) ⟨by chk_lk, by chk_lk, by chk_lk, by chk_lk, by chk_lk, by chk_lk⟩ n s₀)
  ctlC n s₀ := cq_nv (nv_mem (by decide +kernel)) (cqCtlC_spec checkerProg (by chk_lk) n s₀)
  flush n s₀ := flushCaches_specNV n s₀
  reads := ⟨cqReadFns, by simp [cqReadFns], by simp [cqReadFns], checkerProg_cqReads⟩


end L.Checker
