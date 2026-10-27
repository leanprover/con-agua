import ConAgua.Checker.PhaseBReads
import ConAgua.Arena.LevelIntern
import ConAgua.Arena.LevelSubstLP

/-!
# Phase B's read set is the thread's arrays (lane parmode)

docs/design/parmode.md, "Step 4". A thread's worker memory (`bufMem`, `Arena/FreezeRel.lean`) has
content only in the frozen arrays (the buffer's images) and the worker's own arrays
(`parOwnedL`); every other word array is empty. `checkerProg_thrReads`: phase B's loop
(`phaseBFns`, the closure of `check_pending_go`) names only those, without the header `HDRF` and
the seed `CTLF` (`thrS`), so by `L/Agree.lean` a run on the worker memory is the run on any memory
that agrees with it on `thrS` (the same per-function kernel check as `checkerProg_phaseBReads`,
with the smaller set; `Checker/ParOwned.lean`'s `parMissing` is its unproved precursor).
-/

namespace L.Checker

set_option exponentiation.threshold 400

open L.Arena L.Compiler

/-- The bit mask of `thrS` (bit `a` set iff `a` is frozen, but not `HDRF`/`CTLF`, or owned). -/
def thrMask : Nat :=
  551628086749522708972436402352967658729048754803515707150741647335134399667481627801985302793320559149169795695378431

/-- **The arrays a thread's run of phase B names**: the frozen arrays but the header `HDRF` and the
seed `CTLF`, and the owned arrays. -/
def thrS (a : ArrId) : Bool := Nat.testBit thrMask a

/-- `thrS` against the two lists, on every id below `388`. -/
theorem thrS_all : (List.range 388).all (fun a => thrS a == (a != HDRF && a != CTLF &&
    (frozenIdsL.contains a || parOwnedL.contains a))) = true := by decide +kernel

theorem thrMask_lt : thrMask < 2 ^ 388 := by decide +kernel

theorem thrS_ge {a : ArrId} (h : 388 ≤ a) : thrS a = false := by
  simp only [thrS]
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le thrMask_lt (Nat.pow_le_pow_right (by decide) h))

theorem lists_lt : (frozenIdsL ++ parOwnedL).all (· < 388) = true := by decide +kernel

/-- **What `thrS` holds**: a frozen id (not the header or the seed) or an owned one. -/
theorem thrS_iff (a : ArrId) : thrS a = true ↔
    a ≠ HDRF ∧ a ≠ CTLF ∧ (a ∈ frozenIdsL ∨ a ∈ parOwnedL) := by
  by_cases h : a < 388
  · have := List.all_eq_true.mp thrS_all a (List.mem_range.mpr h)
    rw [beq_iff_eq] at this
    rw [this]; simp [and_assoc]
  · rw [thrS_ge (Nat.le_of_not_lt h)]
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨-, -, h'⟩
    have := List.all_eq_true.mp lists_lt a (List.mem_append.mpr h')
    simp only [decide_eq_true_eq] at this; exact absurd this h

/-- Every function of the checker passes the thread's per-function read check. -/
prog_all checkerProg_thrReadsChk : checkerProg (rdChk thrS (fun _ => false) phaseBTree)

/-- **Phase B's read set, for a thread**: the call closure of `check_pending_go` names only word
arrays of `thrS`, no byte array, and calls only into itself. -/
theorem checkerProg_thrReads : readsIn checkerProg thrS (fun _ => false) phaseBFns = true :=
  readsIn_of_all phaseBTree.eq checkerProg_thrReadsChk

end L.Checker
