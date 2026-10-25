module

public import ConAgua.L.Blocks

@[expose] public section

/-!
# Byte classes for `scan` (lane blkcopy)

A class is a 256-byte table (constant data): `c[x] ≠ 0` iff byte `x` is in it. `scan` stops at the
first byte in the class.
-/

namespace L

/-- The class of the bytes satisfying `p`. -/
def tblOf (p : Nat → Bool) : List UInt8 := (List.range 256).map fun b => if p b then 1 else 0

theorem tblOf_length (p : Nat → Bool) : (tblOf p).length = 256 := by simp [tblOf]

theorem tblOf_get (p : Nat → Bool) {y : Nat} (hy : y < 256) :
    (tblOf p)[y]! = if p y then 1 else 0 := by
  simp [tblOf, hy]

theorem tblOf_ne (p : Nat → Bool) (x : UInt8) : (tblOf p)[x.toNat]! ≠ 0 ↔ p x.toNat = true := by
  rw [tblOf_get p x.toNat_lt]; split <;> simp_all

/-- Not JSON whitespace (`skip_ws` stops there). -/
def notWsC : List UInt8 := tblOf fun x => !(x == 32 || x == 9 || x == 13)
/-- Not a decimal digit. -/
def notDigitC : List UInt8 := tblOf fun x => !(48 ≤ x && x ≤ 57)
/-- The end of a run of plain string bytes: `"`, `\`, a control byte. -/
def strStopC : List UInt8 := tblOf fun x => x == 34 || x == 92 || x < 32
/-- A backslash. -/
def bslashC : List UInt8 := tblOf fun x => x == 92
/-- A byte that is not ASCII. -/
def hiC : List UInt8 := tblOf fun x => 128 ≤ x

/-! Membership, byte by byte (`decide` over the 256 bytes). -/

theorem notWsC_mem : ∀ x : UInt8, notWsC[x.toNat]! ≠ 0 ↔ ¬ (x = 32 ∨ x = 9 ∨ x = 13) := by decide
theorem notDigitC_mem : ∀ x : UInt8, notDigitC[x.toNat]! ≠ 0 ↔ ¬ (48 ≤ x ∧ x ≤ 57) := by decide
theorem strStopC_mem : ∀ x : UInt8, strStopC[x.toNat]! ≠ 0 ↔ (x = 34 ∨ x = 92 ∨ x < 32) := by decide
theorem bslashC_mem : ∀ x : UInt8, bslashC[x.toNat]! ≠ 0 ↔ x = 92 := by decide
theorem hiC_mem : ∀ x : UInt8, hiC[x.toNat]! ≠ 0 ↔ 128 ≤ x := by decide

end L
