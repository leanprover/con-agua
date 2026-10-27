import ConAgua.Checker.Prog
import ConAgua.Checker.IndArmFns
import ConAgua.Arena.IndInstallSpec.GrcTwinA
import ConAgua.Arena.IndInstallSpec.HbFreeMfr
import ConAgua.Arena.IndT.ArmMemos

/-!
# The write sets of the inductive arm's callees in `checkerProg` (lane `indproofs4`)

The `closedA` facts `cidW_okC` (`Arena/IndT/CheckIndDecl.lean`) takes, for the checker's program,
over the call-closed function sets of `Checker/IndArmFns.lean`; and the write set (apart from the
walk memos) of the arm's `AbsKeep` callees that reach no walk (`armAbsFns`). Per-chunk kernel
checks (`prog_all`, `closedW_of_all`) as `Checker/IndMemoClosed.lean`.
-/

namespace L.Checker

open L.Arena L.Ind L.Compiler

/-- An array test: below 320 (both tiers) and `f`. -/
def tA (f : Nat → Bool) (a : ArrId) : Bool := decide (a < 388) && f a

/-- A `CTL` word test: below 256 and `g`. -/
def tC (g : Nat → Bool) (w : Word) : Bool := decide (w.toNat < 256) && g w.toNat

theorem tA_mem {f : Nat → Bool} {a : ArrId} (h : tA f a = true) : a ∈ (List.range 388).filter f := by
  simp only [tA, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [List.mem_filter, List.mem_range]
  exact ⟨h.1, h.2⟩

theorem tC_mem {g : Nat → Bool} {w : Word} (h : tC g w = true) :
    w ∈ ((List.range 256).filter g).map Nat.toUInt64 := by
  simp only [tC, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [List.mem_map, List.mem_filter, List.mem_range]
  exact ⟨w.toNat, ⟨h.1, h.2⟩, UInt64.ofNat_toNat⟩

/-! ## `posFree`: `check_block_pass`' callees and `block_raw_rec` -/

names_tree armPosTree : armPosFns
prog_all checkerProg_armPosChk : checkerProg (wsChk CTL
  (tA fun b => decide (b ∉ [NOM, DPM, RAM, HBM, RFM]))
  (tC fun c => decide (c ∉ [204, 206, 208, 210, 214, 218, 219])) armPosTree)
theorem checkerProg_armPos : closedA checkerProg posFreeA posFreeC armPosFns = true :=
  closedW_of_all armPosTree.eq (fun _ h => tA_mem h) (fun _ h => tC_mem h) checkerProg_armPosChk

/-! ## `hbFree`: `tailCallees` -/

names_tree armHbTree : armHbFns
prog_all checkerProg_armHbChk : checkerProg (wsChk CTL
  (tA fun b => decide (b ≠ HBM)) (tC fun c => decide (c ≠ 214)) armHbTree)
theorem checkerProg_armHb : closedA checkerProg hbFreeA hbFreeC armHbFns = true :=
  closedW_of_all armHbTree.eq (fun _ h => tA_mem h) (fun _ h => tC_mem h) checkerProg_armHbChk

/-! ## `rcFree`: `tailRcCallees`, `grcRcCallees`, `cons_block_recs_tf` -/

names_tree armRcTree : armRcFns
prog_all checkerProg_armRcChk : checkerProg (wsChk CTL
  (tA fun b => decide (b ∉ [NOM, DPM, RAM, HBM, RFM, TAM]))
  (tC fun c => decide (c ∉ [204, 206, 208, 210, 212, 213, 214, 218, 219])) armRcTree)
theorem checkerProg_armRc : closedA checkerProg rcFreeA rcFreeC armRcFns = true :=
  closedW_of_all armRcTree.eq (fun _ h => tA_mem h) (fun _ h => tC_mem h) checkerProg_armRcChk

/-! ## `taFree`: `blockTaCallees` -/

names_tree armTaTree : armTaFns
prog_all checkerProg_armTaChk : checkerProg (wsChk CTL
  (tA fun b => decide (b ≠ TAM)) (tC fun c => decide (c ≠ 212 ∧ c ≠ 213)) armTaTree)
theorem checkerProg_armTa : closedA checkerProg taFreeA taFreeC armTaFns = true :=
  closedW_of_all armTaTree.eq (fun _ h => tA_mem h) (fun _ h => tC_mem h) checkerProg_armTaChk

/-! ## `cidFree`: `cidFrameCallees`, `check_basis_decl` -/

names_tree armCidTree : armCidFns
prog_all checkerProg_armCidChk : checkerProg (wsChk CTL
  (tA fun b => decide ((b < 201 ∨ 208 < b) ∧ b ≠ 49 ∧ b ≠ 50 ∧ b ≠ 51 ∧ b ≠ 155 ∧
    b ≠ PINS ∧ b ≠ 151 ∧ b ≠ 152 ∧ b ≠ 153 ∧ b ≠ 52 ∧ b ≠ 53 ∧ b ≠ 54))
  (tC fun c => decide ((c < 202 ∨ 219 < c) ∧ c ≠ 48 ∧ c ≠ 50 ∧ c ≠ 52 ∧ c ≠ 158 ∧
    c ≠ 152 ∧ c ≠ 154 ∧ c ≠ 156 ∧ c ≠ 54 ∧ c ≠ 56 ∧ c ≠ 58)) armCidTree)
theorem checkerProg_armCid : closedA checkerProg cidFreeA cidFreeC armCidFns = true :=
  closedW_of_all armCidTree.eq (fun _ h => tA_mem h) (fun _ h => tC_mem h) checkerProg_armCidChk

/-! ## `rcHbFree`: `check_block_tables` -/

names_tree armRcHbTree : armRcHbFns
prog_all checkerProg_armRcHbChk : checkerProg (wsChk CTL
  (tA fun b => decide (b ∉ [NOM, DPM, RAM, RFM, TAM]))
  (tC fun c => decide (c ∉ [204, 206, 208, 210, 212, 213, 218, 219])) armRcHbTree)
theorem checkerProg_armRcHb : closedA checkerProg rcHbFreeA rcHbFreeC armRcHbFns = true :=
  closedW_of_all armRcHbTree.eq (fun _ h => tA_mem h) (fun _ h => tC_mem h) checkerProg_armRcHbChk

/-! ## `maFree`: `check_block_pass`, `check_block_tail` -/

names_tree armMaTree : armMaFns
prog_all checkerProg_armMaChk : checkerProg (wsChk CTL
  (tA fun b => decide (b ≠ MAM)) (tC fun c => decide (c ≠ 202 ∧ c ≠ 203)) armMaTree)
theorem checkerProg_armMa : closedA checkerProg maFreeA maFreeC armMaFns = true :=
  closedW_of_all armMaTree.eq (fun _ h => tA_mem h) (fun _ h => tC_mem h) checkerProg_armMaChk

/-! ## `mcFree`: `check_block` -/

names_tree armMcTree : armMcFns
prog_all checkerProg_armMcChk : checkerProg (wsChk CTL
  (tA fun b => decide (b ≠ MCM)) (tC fun c => decide (c ≠ 216 ∧ c ≠ 217)) armMcTree)
theorem checkerProg_armMc : closedA checkerProg mcFreeA mcFreeC armMcFns = true :=
  closedW_of_all armMcTree.eq (fun _ h => tA_mem h) (fun _ h => tC_mem h) checkerProg_armMcChk

/-! ## The walk memos: the `AbsKeep` callees that reach no walk -/

/-- The arrays below 256 apart from the walk memos'. -/
def armAbsA : List ArrId := (List.range 388).filter fun b => memoFreeA [b]
/-- The `CTL` words below 256 apart from the walk memos' epoch words. -/
def armAbsC : List Word := ((List.range 256).filter fun c => memoFreeC [c.toUInt64]).map Nat.toUInt64

theorem armAbsA_free : memoFreeA armAbsA = true := by decide +kernel
theorem armAbsC_free : memoFreeC armAbsC = true := by decide +kernel

names_tree armAbsTree : armAbsFns
prog_all checkerProg_armAbsChk : checkerProg (wsChk CTL
  (tA fun b => memoFreeA [b]) (tC fun c => memoFreeC [c.toUInt64]) armAbsTree)
theorem checkerProg_armAbs : closedA checkerProg armAbsA armAbsC armAbsFns = true :=
  closedW_of_all armAbsTree.eq (fun _ h => tA_mem h) (fun _ h => tC_mem h) checkerProg_armAbsChk

end L.Checker
