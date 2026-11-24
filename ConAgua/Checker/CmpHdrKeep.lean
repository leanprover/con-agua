module

public import ConAgua.Checker.PhaseBReads
meta import ConAgua.Checker.PhaseBReads
import ConAgua.Checker.LoopProgTac
meta import ConAgua.Checker.LoopProgTac
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
public import ConAgua.Arena.Globals

@[expose] public section

/-!
# The solution's jobs keep the frozen buffer's header and seed (lane compare)

A worker call of the compared run (`check` with the mode word `2`, `check_b`) runs on the buffer as
the previous job left it; the buffer's geometry stays because no function of `check_b`'s call
closure (`phaseBFns`) stores into the header `HDRF` or the seed `CTLF` (one kernel check per chunk
of the program's functions, `prog_all`, composed by `closedW_of_all` at the control array `HDRF`,
which no store may name): `checkerProg_hkW`. Then `check` with the mode word `2` ends with both as
it started (`check_mode2_hk`; `Final/CmpChain.lean`: `CmpHdrKeep` for `checkerProg`).
-/

open Std.WP
open scoped Lean.Order

namespace L.Checker

open L L.Arena L.Compiler

/-- The arrays phase B may store into: every word array but the header `HDRF` and the seed `CTLF`. -/
def hkA : List TieredArray := checkerWordArrays.filter fun b => b ≠ HDRF ∧ b ≠ CTLF

/-- `hkA` as a test. -/
def hkPa (b : TieredArray) : Bool := checkerWordArrays.contains b && b != HDRF && b != CTLF

theorem hkPa_mem (b : TieredArray) (h : hkPa b = true) : b ∈ hkA := by
  simp only [hkPa, Bool.and_eq_true, List.contains_iff_mem, bne_iff_ne, ne_eq] at h
  simp only [hkA, List.mem_filter, decide_eq_true_eq]
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- Every function of the checker passes the header's per-function check. -/
prog_all checkerProg_hkChk : checkerProg (wsChk HDRF hkPa (fun _ => false) phaseBTree)

/-- **Phase B's stores miss the header and the seed**: the call closure of `check_b` stores only
into `hkA` (the control array `HDRF`: no word of it). -/
theorem checkerProg_hkW : closedW HDRF checkerProg hkA [] phaseBFns = true :=
  closedW_of_all phaseBTree.eq hkPa_mem (fun _ h => absurd h (by simp)) checkerProg_hkChk

/-- The header and the seed are as in `m`. -/
def HkFr (m m' : Mem) : Prop := m'.arr64 HDRF = m.arr64 HDRF ∧ m'.arr64 CTLF = m.arr64 CTLF

theorem hkFr_wframe : WFrame HDRF hkA [] HkFr where
  refl _ := ⟨rfl, rfl⟩
  st64 m₀ m a i v h ha := by
    rcases ha with ⟨h1, h2⟩ | ⟨-, h2⟩
    · simp only [hkA, List.mem_filter, decide_eq_true_eq] at h2
      exact ⟨by rw [Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm h2.2.1)]; exact h.1,
        by rw [Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm h2.2.2)]; exact h.2⟩
    · simp at h2
  setG _ _ _ _ h := h

set_option experimental.vcgen true in
/-- **`check` with the mode word `2`** keeps the header and the seed (`check_b`'s frame). -/
theorem check_mode2_hk (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "check" []
    ⦃fun _ s' => s₀.mem.glob MODE = 2 → HkFr s₀.mem s'.mem; ⊤⦄ := by
  rw [invoke_eq _ (show checkerProg.lookup "check" = some checkL by chk_lk)]
  simp only [callFn, checkL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hC := fun (s₁ : St) => invoke_frame checkerProg checkerProg_hkW hkFr_wframe n "check_b"
      check_b_mem_phaseBFns [] s₁
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, (hC ·),
      (L.invoke_loc checkerProg (exec checkerProg n) "check_a" [·] ·), (L.invoke_loc checkerProg (exec checkerProg n) "check_bs" [] ·), (L.invoke_loc checkerProg (exec checkerProg n) "check_bc" [] ·),
      (L.invoke_loc checkerProg (exec checkerProg n) "check_c1" [] ·),
      (L.invoke_loc checkerProg (exec checkerProg n) "check_c2" [] ·),
      (L.invoke_loc checkerProg (exec checkerProg n) "check_c3" [·] ·)]
    all_goals (try simp only [L.St.setLoc_mem, St.setLocs_cons, St.setLocs_nil, Cmp.eval, beq_iff_eq] at *)
    all_goals first
      | (simp_all (config := { decide := true }); done)
      | (simp_all [St.setLoc, HkFr]; done)

end L.Checker
