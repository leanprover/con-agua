module

public import ConAgua.L.Syntax

public section

/-!
# L: words at a literal offset

A packed record is a base word plus a literal field offset, `b + 9`. `off_toNat` turns
`(b + 9).toNat` into `b.toNat + 9` when the sum fits; used as
`simp (disch := omega) only [off_toNat]`, it rewrites every literal offset of a goal and leaves
`omega` a context without chained `(b + k).toNat = b.toNat + k` facts (with many of those in
context, `omega`'s equality elimination slows down exponentially).

The literal is matched as `no_index (OfNat.ofNat k)`, and the right side is the `Nat` numeral
`OfNat.ofNat k`, not the raw `k`, which `omega` would treat as an atom.
-/

namespace L

/-- A word plus a literal offset, when the sum fits. -/
theorem off_toNat {b : Word} {k : Nat} (h : b.toNat + (OfNat.ofNat k : Nat) < 2 ^ 64) :
    (b + (no_index (OfNat.ofNat k) : Word)).toNat = b.toNat + (OfNat.ofNat k : Nat) := by
  change b.toNat + k < 2 ^ 64 at h
  show (b + UInt64.ofNat k).toNat = b.toNat + k
  rw [UInt64.toNat_add, UInt64.toNat_ofNat']; omega

end L
