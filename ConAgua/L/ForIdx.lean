module

public import ConAgua.L.Syntax

@[expose] public section

/-!
# L: a counted loop's index as a `Nat`

A refinement of a counted loop's model states its index as `UInt64.ofNat j` with `j ≤ n.toNat`
(the twin's index, `List.drop j`, `xs[j]`); these turn the model's guard, its exit and its step
into `Nat` facts.
-/

namespace L

theorem forIdx_toNat {j : Nat} {n : Word} (h : j ≤ n.toNat) : (UInt64.ofNat j).toNat = j :=
  UInt64.toNat_ofNat_of_lt' (by have := n.toNat_lt; simp only [UInt64.size]; omega)

/-- The guard `j < n`. -/
theorem forIdx_lt {j : Nat} {n : Word} (h : j ≤ n.toNat) : UInt64.ofNat j < n ↔ j < n.toNat := by
  rw [UInt64.lt_iff_toNat_lt, forIdx_toNat h]

/-- The exit: `j < n` fails at `j = n`. -/
theorem forIdx_exit {j : Nat} {n : Word} (h : j ≤ n.toNat) (hn : ¬ UInt64.ofNat j < n) :
    j = n.toNat := by
  rw [forIdx_lt h] at hn; omega

/-- The step `j += 1`. -/
theorem forIdx_succ (j : Nat) : UInt64.ofNat j + 1 = UInt64.ofNat (j + 1) := by
  apply UInt64.toBitVec_inj.mp; simp

/-- An address `a + j` inside the word range. -/
theorem forIdx_add {a : Word} {j : Nat} (h : a.toNat + j < 2 ^ 64) :
    (a + UInt64.ofNat j).toNat = a.toNat + j := by
  rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
  exact Nat.mod_eq_of_lt h

end L
