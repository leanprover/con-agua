/-!
`simp only [Nat.add_zero]` on `t + 0`, where `t` is the `toNat` of a `UInt64` product with a
large constant, produces a proof the kernel rejects with "deep recursion detected" (the
elaborator accepts it). `rw [Nat.add_zero]` works. With a small constant (`x * 3`) it works.
Presumably the kernel, checking a definitional step `t + 0 ≡ t`, tries to reduce `t` to a
literal and unfolds the 64-bit multiplication.

Met in `ConAgua/Arena/LitRefine.lean` (`intern_correct`, the start of the probe at
`homeW h n + 0`); worked around with a separate lemma proved by `rw` (`start_pos`).

nightly-2026-10-20.
-/

/-- error: (kernel) deep recursion detected, use `set_option maxRecDepth <num>` to increase the limit -/
#guard_msgs in
example (x : UInt64) (k : Nat) :
    ((x * 0x9e3779b97f4a7c15).toNat + 0) % k = (x * 0x9e3779b97f4a7c15).toNat % k := by
  simp only [Nat.add_zero]

-- `rw` is fine:
example (x : UInt64) (k : Nat) :
    ((x * 0x9e3779b97f4a7c15).toNat + 0) % k = (x * 0x9e3779b97f4a7c15).toNat % k := by
  rw [Nat.add_zero]

-- a small constant is fine:
example (x : UInt64) (k : Nat) : ((x * 3).toNat + 0) % k = (x * 3).toNat % k := by
  simp only [Nat.add_zero]
