module

public import ConAgua.Arena.IndT.CheckIndDecl
public import ConAgua.Checker.Prog
public import ConAgua.Checker.IotaArmClosed
public import ConAgua.Checker.IotaArmTrees
import ConAgua.Checker.LoopProg
import ConAgua.Checker.LoopProgTac
import ConAgua.Arena.IndArm
import ConAgua.Checker.IndArmTests
import ConAgua.Arena.RecGenSpec.ClassFeR
meta import ConAgua.Checker.LoopProg
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
import all ConAgua.Arena.Inst1
import all ConAgua.Arena.Inst1Spec
import all ConAgua.Arena.InstLP
import all ConAgua.Arena.InstList
import all ConAgua.Arena.InstListSpec
import all ConAgua.Arena.IotaFrame
import all ConAgua.Arena.IotaRel
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
import all ConAgua.Arena.NatDivKstep
import all ConAgua.Arena.NatDivSubmul
import all ConAgua.Arena.NatDivWord
import all ConAgua.Arena.NatGcd
import all ConAgua.Arena.NatLeaf
import all ConAgua.Arena.NatMul
import all ConAgua.Arena.NatPow
import all ConAgua.Arena.NatShl
import all ConAgua.Arena.NatShr
import all ConAgua.Arena.NatSized
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

@[expose] public section

/-!
# The ι reading rule's program facts at the checker's program (lane ronsync8)

`IotaArmProg` (what `cid_ref` takes for `block_reads_at`) at `checkerProg.subPB bs`: the write
sets from `Checker/IotaArmClosed.lean`'s per-function checks (`closedW_of_all`, carried to the
substituted program by `closedW_subPB`), the facts they give (`AbsKeep`, `ownC` kept, `BrMem`
kept), the lookups by `prog_bundle`.
-/

namespace L.Checker

open L L.Rom L.Arena L.Ind L.Compiler

theorem iotaSubset_of_tree {fs : List FnName} {t : NTree} (ht : namesTree fs = some t)
    {l : List FnName} (h : l.all (fun f => (t.find (nameCode f)).isSome) = true) :
    ∀ f ∈ l, f ∈ fs := fun f hf => by
  have := List.all_eq_true.mp h f hf
  rw [namesTree_spec ht] at this
  exact of_decide_eq_true this

theorem iotaMem_of_tree {fs : List FnName} {t : NTree} (ht : namesTree fs = some t) {f : FnName}
    (h : (t.find (nameCode f)).isSome = true) : f ∈ fs := by
  rw [namesTree_spec ht] at h
  exact of_decide_eq_true h

theorem iotaRC_mem {w : Word} (h : tC1 (fun c => memoFreeC [UInt64.ofNat c]) w = true) : w ∈ iotaRC := by
  simp only [tC1, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [iotaRC, List.mem_filter, List.mem_map, List.mem_range]
  refine ⟨⟨w.toNat, h.1, UInt64.ofNat_toNat⟩, ?_⟩
  have := h.2; rwa [UInt64.ofNat_toNat] at this

/-- The arrays `recs_read`'s closure may write: all but the own rows'. -/
def iotaOwnA : List TieredArray :=
  checkerWordArrays.filter fun b =>
    decide (b ∉ ([OIXA, OIXS, OIXN, tier1 OIXA, tier1 OIXS, tier1 OIXN] : List TieredArray))

/-- The `CTL` words it may write: all below 1024 but the stamp (`133`). -/
def iotaOwnC : List Word := ((List.range 1024).filter fun c => decide (c ≠ 133)).map Nat.toUInt64

theorem checkerProg_bri : closedAL checkerProg briA briC briFns briLeaves = true :=
  closedWL_of_all briTree.eq briCallTree.eq (fun _ h => tA_mem h) (fun _ h => tC1_mem h) checkerProg_briChk
theorem checkerProg_iotaR : closedA checkerProg iotaRA iotaRC iotaRFns = true :=
  closedW_of_all iotaRTree.eq (fun _ h => tA_mem h) (fun _ h => iotaRC_mem h) checkerProg_iotaRChk
theorem checkerProg_iotaKeep : closedA checkerProg iotaRA iotaRC iotaKeepFns = true :=
  closedW_of_all iotaKeepTree.eq (fun _ h => tA_mem h) (fun _ h => iotaRC_mem h) checkerProg_iotaKeepChk
theorem checkerProg_iotaOwn : closedA checkerProg iotaOwnA iotaOwnC iotaOwnFns = true :=
  closedW_of_all iotaOwnTree.eq (fun _ h => tA_mem h) (fun _ h => tC1_mem h) checkerProg_iotaOwnChk

/-- `AbsKeep` of a function of `iotaKeepFns`, from its write set. -/
theorem iotaKeep_checker (bs : List UInt8) {f : FnName} (hf : f ∈ iotaKeepFns) :
    AbsKeep (Prog.subPB bs checkerProg) f :=
  absKeep_of_closed (closedW_subPB bs checkerProg_iotaKeep) iotaRA_free iotaRC_free hf

/-- **`recs_read` keeps the own rows' counters** (its write set). -/
theorem iotaOwn_checker (bs : List UInt8) :
    ∀ (k : Nat) (vs : List Word) (m₀ : Mem) (r₀ : List Word) (m₁ : Mem),
      callW (Prog.subPB bs checkerProg) k "recs_read" vs m₀ = some (r₀, m₁) → ownC m₁ = ownC m₀ := by
  intro n vs m r m' h
  refine ownC_frame (run_memFrame (closedW_subPB bs checkerProg_iotaOwn)
    (iotaMem_of_tree iotaOwnTree.eq (by decide +kernel)) (Arena.run_of_callW h)).1 ?_ ?_
  · intro b hb g t he
    have hn := (List.mem_filter.mp hb).2
    subst he
    revert hn
    unfold tierA oixArr; generalize (t &&& 1 != 0) = c
    cases c <;> split <;> (try split) <;> decide
  · simp only [iotaOwnC, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq, not_exists,
      not_and]
    intro x hx h1
    have : (Nat.toUInt64 x).toNat = 133 := by rw [h1]; rfl
    simp at this; omega

/-- **`block_reads_at` keeps `BrMem`** (its write set with leaves). -/
theorem iotaBri_checker (bs : List UInt8) (hM : MaProg (Prog.subPB bs checkerProg))
    (hI : IlpfF (Prog.subPB bs checkerProg)) (hi : I1lF (Prog.subPB bs checkerProg)) :
    ∀ (n : Nat) (vs : List Word) (m : Mem) (r : List Word) (m' : Mem),
      callW (Prog.subPB bs checkerProg) n "block_reads_at" vs m = some (r, m') → BrMem m → BrMem m' :=
  fun _ _ _ _ _ h h0 => bri_keep (closedWL_subPB bs checkerProg_bri) hM hI hi
    (iotaMem_of_tree briTree.eq (by decide +kernel)) h h0

theorem iotaKeep_mem : ∀ f ∈ ["iota_parts_rel", "block_constants", "block_recs",
    "cons_block_recs_temp", "gen_rec_check_pop_all", "env_set_flags"], f ∈ iotaKeepFns :=
  iotaSubset_of_tree iotaKeepTree.eq (by decide +kernel)

/-- **The ι reading rule's program facts at the substituted checker program.** -/
theorem iotaArmProg_checker (bs : List UInt8) : IotaArmProg (Prog.subPB bs checkerProg) := by
  have hM : MaProg (Prog.subPB bs checkerProg) := by prog_bundle []
  have hI : IlpfF (Prog.subPB bs checkerProg) := by prog_bundle []
  have hi : I1lF (Prog.subPB bs checkerProg) := by prog_bundle []
  prog_bundle [closedW_subPB bs checkerProg_iotaR,
    iotaKeep_checker bs (iotaKeep_mem _ (by simp)) (f := "iota_parts_rel"),
    iotaKeep_checker bs (iotaKeep_mem _ (by simp)) (f := "block_constants"),
    iotaKeep_checker bs (iotaKeep_mem _ (by simp)) (f := "block_recs"),
    iotaKeep_checker bs (iotaKeep_mem _ (by simp)) (f := "cons_block_recs_temp"),
    iotaKeep_checker bs (iotaKeep_mem _ (by simp)) (f := "gen_rec_check_pop_all"),
    iotaKeep_checker bs (iotaKeep_mem _ (by simp)) (f := "env_set_flags"),
    iotaOwn_checker bs, iotaBri_checker bs hM hI hi, hM, hI, hi]

end L.Checker
