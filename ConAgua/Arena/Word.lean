module

public import ConAgua.L.Syntax
import ConAgua.Arena.GrindAttr

@[expose] public section

/-!
# Word arithmetic for the limb pool: high words of products and sums

Pure Lean facts about `UInt64` that the multiply loop needs, each as an equation over a named
function (`mulHiN`, `adcHi`) with a `grind` pattern, so that the ring solver sees the
digit equation `low + high · 2^64 = …` directly.
-/

namespace L.Arena

/-! ## The high word of a product -/

/-- The high word of `x * y`, as a number. -/
def mulHiN (x y : Word) : Nat := x.toNat * y.toNat / 2 ^ 64

theorem mul_split (x y : Word) : (x * y).toNat + mulHiN x y * 2 ^ 64 = x.toNat * y.toNat := by
  simp only [mulHiN, UInt64.toNat_mul]; omega
grind_pattern [arena_grind] mul_split => mulHiN x y

theorem mulHiN_le (x y : Word) : x.toNat * y.toNat + 2 ^ 65 ≤ 2 ^ 128 + 1 := by
  have hx := x.toNat_lt; have hy := y.toNat_lt
  have : x.toNat * y.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  omega
grind_pattern [arena_grind] mulHiN_le => mulHiN x y

/-- L's `mulhi(x, y)` is `UInt64.ofNat (x.toNat * y.toNat / 2^64)`; that is `mulHiN x y`. -/
theorem mulhi_toNat (x y : Word) : (UInt64.ofNat (x.toNat * y.toNat / 2 ^ 64)).toNat = mulHiN x y := by
  have := mulHiN_le x y
  simp only [mulHiN]
  apply Nat.mod_eq_of_lt
  exact Nat.div_lt_of_lt_mul (by omega)
grind_pattern [arena_grind] mulhi_toNat => UInt64.ofNat (x.toNat * y.toNat / 2 ^ 64)



end L.Arena
