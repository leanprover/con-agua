module

public import ConAgua.Scan.WordLink
public import ConAgua.Scan.LeafLink
public import ConAgua.Scan.Key

@[expose] public section

/-!
# `key_at`/`value_at` against con-leche's `keyAt`/`valueAt`

`keyAt`/`keyAtN` are the same decision tree, generated from the same source branch for branch
(`ConAgua.Scan.Key`'s doc comment): a switch on the byte at `i + 1`, then on `kl`, then an
unrolled compare of the remaining bytes (`lit1`…`lit10` on the `ByteArray` side, a conjunction of
`byteW` reads on the model side). `UInt8_ofNat_toUInt64`/`byteAt_pos_iff` are the bridge: for a
position `pos : USize` and its word form `wpos : Word` with equal `.toNat` (always arithmetic,
discharged by the shared `h64`/`hsize`-driven `simp … <;> omega`), a `byteAt` equality against a
byte literal holds iff the matching `byteW` equality does.

The proof of `keyAt_eq_keyAtN`: `split` on `byteAt b (i + 1)`'s match (one goal per recognised
first byte, plus the catch-all), and in each goal `simp` the whole remaining decision tree — `kl`'s
own match and the unrolled literal compares — over to the `keyAtN` side using `byteAt_pos_iff` at
every position the branch reads, `eq_toUInt64_iff` for every `kl` value it tests, `and_assoc` to
realign `lit1`…`lit10`'s left-associated `&&` against the model's right-associated `∧`, and
`apply_ite` to push `Key.ctorIdx`/`UInt64.ofNat` through what is left of the tree; `rfl` closes
every leaf (both sides compute the same `Key`'s/number's `UInt64.ofNat … .ctorIdx`). The catch-all
goal instead collects one `byteAt_pos_iff`-derived disequality per recognised byte and `simp`s the
model's whole chain down to `0`, matching `keyAt`'s `.kUnknown`.
-/

namespace ConAgua.Scan

open ConLeche.Frontend
open L (Word)
open L.Scan.Key (keyAtN valueAtN)
open L.Scan.Leaves (skipWsN)
open L.Scan.Utf8 (byteW)

/-- A byte literal transports along `.toUInt64`: `(97 : UInt8).toUInt64 = (97 : Word)`. -/
theorem UInt8_ofNat_toUInt64 (n : Nat) (hn : n < 256) :
    (OfNat.ofNat n : UInt8).toUInt64 = (OfNat.ofNat n : UInt64) := by
  apply UInt64.toNat_inj.mp
  rw [UInt8.toNat_toUInt64, UInt8.toNat_ofNat, UInt64.toNat_ofNat]
  omega

variable (b : ByteArray) (h64 : System.Platform.numBits = 64)

include h64 in
/-- The bridge every byte compare in `keyAt`/`keyAtN` goes through: at matching positions (equal
`.toNat`, the arithmetic left to `simp … <;> omega`), con-leche's `byteAt` agrees with a byte
literal iff the model's `byteW` does with its word form. -/
theorem byteAt_pos_iff (hsize : b.size < 2 ^ 64) (pos : USize) (wpos : Word) (lit : Nat)
    (hlit : lit < 256) (heq : pos.toNat = wpos.toNat) :
    byteAt b pos = (OfNat.ofNat lit : UInt8) ↔ byteW b.data wpos = (OfNat.ofNat lit : Word) := by
  rw [byteAt_eq_getD b h64 hsize, heq]
  unfold byteW
  constructor
  · intro h
    apply UInt64.toNat_inj.mp
    rw [h, UInt8.toNat_toUInt64, UInt8.toNat_ofNat, UInt64.toNat_ofNat]
    omega
  · intro h
    apply UInt8.toNat_inj.mp
    have h' := congrArg UInt64.toNat h
    rw [UInt8.toNat_toUInt64, UInt64.toNat_ofNat] at h'
    rw [h', UInt8.toNat_ofNat]
    omega

/-! ## `key_at` -/

include h64 in
theorem keyAt_eq_keyAtN (hsize : b.size < 2 ^ 63) (i kl : USize)
    (hi : i.toNat + 1 + kl.toNat < b.size) :
    UInt64.ofNat (keyAt b i kl).ctorIdx = keyAtN b.data i.toUInt64 kl.toUInt64 := by
  have hsize64 : b.size < 2 ^ 64 := by omega
  have hp1 : (i + 1).toNat = (i.toUInt64 + 1).toNat := by
    simp only [USize.toNat_add, UInt64.toNat_add, USize.toNat_ofNat, UInt64.toNat_ofNat,
      USize.toNat_toUInt64, h64] <;> omega
  have hp2 : (i + 1 + 1).toNat = (i.toUInt64 + 2).toNat := by
    simp only [USize.toNat_add, UInt64.toNat_add, USize.toNat_ofNat, UInt64.toNat_ofNat,
      USize.toNat_toUInt64, h64] <;> omega
  have hp3 : (i + 1 + 1 + 1).toNat = (i.toUInt64 + 3).toNat := by
    simp only [USize.toNat_add, UInt64.toNat_add, USize.toNat_ofNat, UInt64.toNat_ofNat,
      USize.toNat_toUInt64, h64] <;> omega
  have hp4 : (i + 1 + 1 + 2).toNat = (i.toUInt64 + 4).toNat := by
    simp only [USize.toNat_add, UInt64.toNat_add, USize.toNat_ofNat, UInt64.toNat_ofNat,
      USize.toNat_toUInt64, h64] <;> omega
  have hp5 : (i + 1 + 1 + 3).toNat = (i.toUInt64 + 5).toNat := by
    simp only [USize.toNat_add, UInt64.toNat_add, USize.toNat_ofNat, UInt64.toNat_ofNat,
      USize.toNat_toUInt64, h64] <;> omega
  have hp6 : (i + 1 + 1 + 4).toNat = (i.toUInt64 + 6).toNat := by
    simp only [USize.toNat_add, UInt64.toNat_add, USize.toNat_ofNat, UInt64.toNat_ofNat,
      USize.toNat_toUInt64, h64] <;> omega
  have hp7 : (i + 1 + 1 + 5).toNat = (i.toUInt64 + 7).toNat := by
    simp only [USize.toNat_add, UInt64.toNat_add, USize.toNat_ofNat, UInt64.toNat_ofNat,
      USize.toNat_toUInt64, h64] <;> omega
  have hp8 : (i + 1 + 1 + 6).toNat = (i.toUInt64 + 8).toNat := by
    simp only [USize.toNat_add, UInt64.toNat_add, USize.toNat_ofNat, UInt64.toNat_ofNat,
      USize.toNat_toUInt64, h64] <;> omega
  have hp9 : (i + 1 + 1 + 7).toNat = (i.toUInt64 + 9).toNat := by
    simp only [USize.toNat_add, UInt64.toNat_add, USize.toNat_ofNat, UInt64.toNat_ofNat,
      USize.toNat_toUInt64, h64] <;> omega
  have hp10 : (i + 1 + 1 + 8).toNat = (i.toUInt64 + 10).toNat := by
    simp only [USize.toNat_add, UInt64.toNat_add, USize.toNat_ofNat, UInt64.toNat_ofNat,
      USize.toNat_toUInt64, h64] <;> omega
  have hp11 : (i + 1 + 1 + 9).toNat = (i.toUInt64 + 11).toNat := by
    simp only [USize.toNat_add, UInt64.toNat_add, USize.toNat_ofNat, UInt64.toNat_ofNat,
      USize.toNat_toUInt64, h64] <;> omega
  unfold keyAt keyAtN lit1 lit2 lit3 lit4 lit5 lit6 lit7 lit8 lit9 lit10
  dsimp only
  split
  · rename_i heq
    have hcw : byteW b.data (i.toUInt64 + 1) = 97 :=
      (byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 97 (by decide) hp1).mp heq
    simp only [hcw, Bool.and_eq_true, beq_iff_eq,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 108 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 112 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 114 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 120 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 103 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 105 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 108 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 112 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 111 (by decide) hp4,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 3) (i.toUInt64 + 5) 109 (by decide) hp5,
      eq_toUInt64_iff kl 3,
      eq_toUInt64_iff kl 5,
      ofNat_toUInt64 h64, apply_ite Key.ctorIdx, apply_ite UInt64.ofNat, ite_true, ite_false, and_assoc]
    rfl
  · rename_i heq
    have hcw : byteW b.data (i.toUInt64 + 1) = 98 :=
      (byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 98 (by decide) hp1).mp heq
    simp only [hcw, Bool.and_eq_true, beq_iff_eq,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 105 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 111 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 118 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 97 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 100 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 110 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 100 (by decide) hp4,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 114 (by decide) hp4,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 121 (by decide) hp4,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 3) (i.toUInt64 + 5) 101 (by decide) hp5,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 4) (i.toUInt64 + 6) 114 (by decide) hp6,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 5) (i.toUInt64 + 7) 73 (by decide) hp7,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 6) (i.toUInt64 + 8) 110 (by decide) hp8,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 7) (i.toUInt64 + 9) 102 (by decide) hp9,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 8) (i.toUInt64 + 10) 111 (by decide) hp10,
      eq_toUInt64_iff kl 4,
      eq_toUInt64_iff kl 10,
      ofNat_toUInt64 h64, apply_ite Key.ctorIdx, apply_ite UInt64.ofNat, ite_true, ite_false, and_assoc]
    rfl
  · rename_i heq
    have hcw : byteW b.data (i.toUInt64 + 1) = 99 :=
      (byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 99 (by decide) hp1).mp heq
    simp only [hcw, Bool.and_eq_true, beq_iff_eq,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 105 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 111 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 116 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 100 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 110 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 111 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 114 (by decide) hp4,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 115 (by decide) hp4,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 120 (by decide) hp4,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 3) (i.toUInt64 + 5) 115 (by decide) hp5,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 3) (i.toUInt64 + 5) 116 (by decide) hp5,
      eq_toUInt64_iff kl 4,
      eq_toUInt64_iff kl 5,
      ofNat_toUInt64 h64, apply_ite Key.ctorIdx, apply_ite UInt64.ofNat, ite_true, ite_false, and_assoc]
    rfl
  · rename_i heq
    have hcw : byteW b.data (i.toUInt64 + 1) = 100 :=
      (byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 100 (by decide) hp1).mp heq
    simp only [hcw, Bool.and_eq_true, beq_iff_eq,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 101 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 102 (by decide) hp3,
      eq_toUInt64_iff kl 3,
      ofNat_toUInt64 h64, apply_ite Key.ctorIdx, apply_ite UInt64.ofNat, ite_true, ite_false, and_assoc]
    rfl
  · rename_i heq
    have hcw : byteW b.data (i.toUInt64 + 1) = 102 :=
      (byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 102 (by decide) hp1).mp heq
    simp only [hcw, Bool.and_eq_true, beq_iff_eq,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 110 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 111 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 114 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 97 (by decide) hp4,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 3) (i.toUInt64 + 5) 108 (by decide) hp5,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 4) (i.toUInt64 + 6) 108 (by decide) hp6,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 5) (i.toUInt64 + 7) 69 (by decide) hp7,
      eq_toUInt64_iff kl 2,
      eq_toUInt64_iff kl 7,
      ofNat_toUInt64 h64, apply_ite Key.ctorIdx, apply_ite UInt64.ofNat, ite_true, ite_false, and_assoc]
    rfl
  · rename_i heq
    have hcw : byteW b.data (i.toUInt64 + 1) = 104 :=
      (byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 104 (by decide) hp1).mp heq
    simp only [hcw, Bool.and_eq_true, beq_iff_eq,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 105 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 110 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 116 (by decide) hp4,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 3) (i.toUInt64 + 5) 115 (by decide) hp5,
      eq_toUInt64_iff kl 5,
      ofNat_toUInt64 h64, apply_ite Key.ctorIdx, apply_ite UInt64.ofNat, ite_true, ite_false, and_assoc]
    rfl
  · rename_i heq
    have hcw : byteW b.data (i.toUInt64 + 1) = 105 :=
      (byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 105 (by decide) hp1).mp heq
    simp only [hcw, Bool.and_eq_true, beq_iff_eq,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 100 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 101 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 108 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 109 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 110 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 115 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 82 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 85 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 97 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 100 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 120 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 101 (by decide) hp4,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 110 (by decide) hp4,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 117 (by decide) hp4,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 120 (by decide) hp4,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 3) (i.toUInt64 + 5) 99 (by decide) hp5,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 3) (i.toUInt64 + 5) 102 (by decide) hp5,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 3) (i.toUInt64 + 5) 115 (by decide) hp5,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 4) (i.toUInt64 + 6) 97 (by decide) hp6,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 4) (i.toUInt64 + 6) 108 (by decide) hp6,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 4) (i.toUInt64 + 6) 116 (by decide) hp6,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 5) (i.toUInt64 + 7) 101 (by decide) hp7,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 5) (i.toUInt64 + 7) 102 (by decide) hp7,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 5) (i.toUInt64 + 7) 105 (by decide) hp7,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 6) (i.toUInt64 + 8) 101 (by decide) hp8,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 6) (i.toUInt64 + 8) 118 (by decide) hp8,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 6) (i.toUInt64 + 8) 120 (by decide) hp8,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 7) (i.toUInt64 + 9) 101 (by decide) hp9,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 7) (i.toUInt64 + 9) 105 (by decide) hp9,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 8) (i.toUInt64 + 10) 118 (by decide) hp10,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 9) (i.toUInt64 + 11) 101 (by decide) hp11,
      eq_toUInt64_iff kl 1,
      eq_toUInt64_iff kl 2,
      eq_toUInt64_iff kl 3,
      eq_toUInt64_iff kl 4,
      eq_toUInt64_iff kl 5,
      eq_toUInt64_iff kl 6,
      eq_toUInt64_iff kl 8,
      eq_toUInt64_iff kl 9,
      eq_toUInt64_iff kl 11,
      ofNat_toUInt64 h64, apply_ite Key.ctorIdx, apply_ite UInt64.ofNat, ite_true, ite_false, and_assoc]
    rfl
  · rename_i heq
    have hcw : byteW b.data (i.toUInt64 + 1) = 107 :=
      (byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 107 (by decide) hp1).mp heq
    simp only [hcw, Bool.and_eq_true, beq_iff_eq,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 105 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 110 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 100 (by decide) hp4,
      eq_toUInt64_iff kl 1,
      eq_toUInt64_iff kl 4,
      ofNat_toUInt64 h64, apply_ite Key.ctorIdx, apply_ite UInt64.ofNat, ite_true, ite_false, and_assoc]
    rfl
  · rename_i heq
    have hcw : byteW b.data (i.toUInt64 + 1) = 108 :=
      (byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 108 (by decide) hp1).mp heq
    simp only [hcw, Bool.and_eq_true, beq_iff_eq,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 97 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 101 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 109 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 116 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 118 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 69 (by decide) hp4,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 101 (by decide) hp4,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 3) (i.toUInt64 + 5) 108 (by decide) hp5,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 4) (i.toUInt64 + 6) 80 (by decide) hp6,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 5) (i.toUInt64 + 7) 97 (by decide) hp7,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 6) (i.toUInt64 + 8) 114 (by decide) hp8,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 7) (i.toUInt64 + 9) 97 (by decide) hp9,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 8) (i.toUInt64 + 10) 109 (by decide) hp10,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 9) (i.toUInt64 + 11) 115 (by decide) hp11,
      eq_toUInt64_iff kl 3,
      eq_toUInt64_iff kl 4,
      eq_toUInt64_iff kl 11,
      ofNat_toUInt64 h64, apply_ite Key.ctorIdx, apply_ite UInt64.ofNat, ite_true, ite_false, and_assoc]
    rfl
  · rename_i heq
    have hcw : byteW b.data (i.toUInt64 + 1) = 109 :=
      (byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 109 (by decide) hp1).mp heq
    simp only [hcw, Bool.and_eq_true, beq_iff_eq,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 97 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 101 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 116 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 120 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 97 (by decide) hp4,
      eq_toUInt64_iff kl 3,
      eq_toUInt64_iff kl 4,
      ofNat_toUInt64 h64, apply_ite Key.ctorIdx, apply_ite UInt64.ofNat, ite_true, ite_false, and_assoc]
    rfl
  · rename_i heq
    have hcw : byteW b.data (i.toUInt64 + 1) = 110 :=
      (byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 110 (by decide) hp1).mp heq
    simp only [hcw, Bool.and_eq_true, beq_iff_eq,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 97 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 102 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 111 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 117 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 105 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 109 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 110 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 116 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 70 (by decide) hp4,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 73 (by decide) hp4,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 77 (by decide) hp4,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 78 (by decide) hp4,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 80 (by decide) hp4,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 86 (by decide) hp4,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 100 (by decide) hp4,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 101 (by decide) hp4,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 3) (i.toUInt64 + 5) 97 (by decide) hp5,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 3) (i.toUInt64 + 5) 101 (by decide) hp5,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 3) (i.toUInt64 + 5) 105 (by decide) hp5,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 3) (i.toUInt64 + 5) 108 (by decide) hp5,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 3) (i.toUInt64 + 5) 110 (by decide) hp5,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 3) (i.toUInt64 + 5) 111 (by decide) hp5,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 4) (i.toUInt64 + 6) 100 (by decide) hp6,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 4) (i.toUInt64 + 6) 101 (by decide) hp6,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 4) (i.toUInt64 + 6) 108 (by decide) hp6,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 4) (i.toUInt64 + 6) 110 (by decide) hp6,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 4) (i.toUInt64 + 6) 112 (by decide) hp6,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 4) (i.toUInt64 + 6) 114 (by decide) hp6,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 4) (i.toUInt64 + 6) 115 (by decide) hp6,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 4) (i.toUInt64 + 6) 116 (by decide) hp6,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 5) (i.toUInt64 + 7) 97 (by decide) hp7,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 5) (i.toUInt64 + 7) 105 (by decide) hp7,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 5) (i.toUInt64 + 7) 108 (by decide) hp7,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 5) (i.toUInt64 + 7) 111 (by decide) hp7,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 5) (i.toUInt64 + 7) 115 (by decide) hp7,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 5) (i.toUInt64 + 7) 116 (by decide) hp7,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 6) (i.toUInt64 + 8) 99 (by decide) hp8,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 6) (i.toUInt64 + 8) 100 (by decide) hp8,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 6) (i.toUInt64 + 8) 101 (by decide) hp8,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 6) (i.toUInt64 + 8) 109 (by decide) hp8,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 6) (i.toUInt64 + 8) 114 (by decide) hp8,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 6) (i.toUInt64 + 8) 118 (by decide) hp8,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 7) (i.toUInt64 + 9) 100 (by decide) hp9,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 7) (i.toUInt64 + 9) 101 (by decide) hp9,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 7) (i.toUInt64 + 9) 115 (by decide) hp9,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 8) (i.toUInt64 + 10) 115 (by decide) hp10,
      eq_toUInt64_iff kl 3,
      eq_toUInt64_iff kl 4,
      eq_toUInt64_iff kl 6,
      eq_toUInt64_iff kl 7,
      eq_toUInt64_iff kl 9,
      eq_toUInt64_iff kl 10,
      ofNat_toUInt64 h64, apply_ite Key.ctorIdx, apply_ite UInt64.ofNat, ite_true, ite_false, and_assoc]
    rfl
  · rename_i heq
    have hcw : byteW b.data (i.toUInt64 + 1) = 111 :=
      (byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 111 (by decide) hp1).mp heq
    simp only [hcw, Bool.and_eq_true, beq_iff_eq,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 112 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 97 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 113 (by decide) hp4,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 3) (i.toUInt64 + 5) 117 (by decide) hp5,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 4) (i.toUInt64 + 6) 101 (by decide) hp6,
      eq_toUInt64_iff kl 6,
      ofNat_toUInt64 h64, apply_ite Key.ctorIdx, apply_ite UInt64.ofNat, ite_true, ite_false, and_assoc]
    rfl
  · rename_i heq
    have hcw : byteW b.data (i.toUInt64 + 1) = 112 :=
      (byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 112 (by decide) hp1).mp heq
    simp only [hcw, Bool.and_eq_true, beq_iff_eq,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 97 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 114 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 101 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 111 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 114 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 97 (by decide) hp4,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 106 (by decide) hp4,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 3) (i.toUInt64 + 5) 109 (by decide) hp5,
      eq_toUInt64_iff kl 3,
      eq_toUInt64_iff kl 4,
      eq_toUInt64_iff kl 5,
      ofNat_toUInt64 h64, apply_ite Key.ctorIdx, apply_ite UInt64.ofNat, ite_true, ite_false, and_assoc]
    rfl
  · rename_i heq
    have hcw : byteW b.data (i.toUInt64 + 1) = 113 :=
      (byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 113 (by decide) hp1).mp heq
    simp only [hcw, Bool.and_eq_true, beq_iff_eq,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 117 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 111 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 116 (by decide) hp4,
      eq_toUInt64_iff kl 4,
      ofNat_toUInt64 h64, apply_ite Key.ctorIdx, apply_ite UInt64.ofNat, ite_true, ite_false, and_assoc]
    rfl
  · rename_i heq
    have hcw : byteW b.data (i.toUInt64 + 1) = 114 :=
      (byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 114 (by decide) hp1).mp heq
    simp only [hcw, Bool.and_eq_true, beq_iff_eq,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 101 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 104 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 117 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 99 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 103 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 108 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 115 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 101 (by decide) hp4,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 115 (by decide) hp4,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 117 (by decide) hp4,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 3) (i.toUInt64 + 5) 108 (by decide) hp5,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 3) (i.toUInt64 + 5) 115 (by decide) hp5,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 4) (i.toUInt64 + 6) 97 (by decide) hp6,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 5) (i.toUInt64 + 7) 114 (by decide) hp7,
      eq_toUInt64_iff kl 3,
      eq_toUInt64_iff kl 4,
      eq_toUInt64_iff kl 5,
      eq_toUInt64_iff kl 7,
      ofNat_toUInt64 h64, apply_ite Key.ctorIdx, apply_ite UInt64.ofNat, ite_true, ite_false, and_assoc]
    rfl
  · rename_i heq
    have hcw : byteW b.data (i.toUInt64 + 1) = 115 :=
      (byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 115 (by decide) hp1).mp heq
    simp only [hcw, Bool.and_eq_true, beq_iff_eq,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 97 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 111 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 116 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 117 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 99 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 102 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 114 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 86 (by decide) hp4,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 99 (by decide) hp4,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 101 (by decide) hp4,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 116 (by decide) hp4,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 117 (by decide) hp4,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 3) (i.toUInt64 + 5) 97 (by decide) hp5,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 3) (i.toUInt64 + 5) 99 (by decide) hp5,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 3) (i.toUInt64 + 5) 116 (by decide) hp5,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 4) (i.toUInt64 + 6) 108 (by decide) hp6,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 4) (i.toUInt64 + 6) 116 (by decide) hp6,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 4) (i.toUInt64 + 6) 121 (by decide) hp6,
      eq_toUInt64_iff kl 3,
      eq_toUInt64_iff kl 4,
      eq_toUInt64_iff kl 6,
      ofNat_toUInt64 h64, apply_ite Key.ctorIdx, apply_ite UInt64.ofNat, ite_true, ite_false, and_assoc]
    rfl
  · rename_i heq
    have hcw : byteW b.data (i.toUInt64 + 1) = 116 :=
      (byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 116 (by decide) hp1).mp heq
    simp only [hcw, Bool.and_eq_true, beq_iff_eq,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 104 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 121 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 109 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 112 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 101 (by decide) hp4,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 3) (i.toUInt64 + 5) 78 (by decide) hp5,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 3) (i.toUInt64 + 5) 115 (by decide) hp5,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 4) (i.toUInt64 + 6) 97 (by decide) hp6,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 5) (i.toUInt64 + 7) 109 (by decide) hp7,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 6) (i.toUInt64 + 8) 101 (by decide) hp8,
      eq_toUInt64_iff kl 3,
      eq_toUInt64_iff kl 4,
      eq_toUInt64_iff kl 5,
      eq_toUInt64_iff kl 8,
      ofNat_toUInt64 h64, apply_ite Key.ctorIdx, apply_ite UInt64.ofNat, ite_true, ite_false, and_assoc]
    rfl
  · rename_i heq
    have hcw : byteW b.data (i.toUInt64 + 1) = 117 :=
      (byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 117 (by decide) hp1).mp heq
    simp only [hcw, Bool.and_eq_true, beq_iff_eq,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 115 (by decide) hp2,
      eq_toUInt64_iff kl 2,
      ofNat_toUInt64 h64, apply_ite Key.ctorIdx, apply_ite UInt64.ofNat, ite_true, ite_false, and_assoc]
    rfl
  · rename_i heq
    have hcw : byteW b.data (i.toUInt64 + 1) = 118 :=
      (byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 118 (by decide) hp1).mp heq
    simp only [hcw, Bool.and_eq_true, beq_iff_eq,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1) (i.toUInt64 + 2) 97 (by decide) hp2,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 1) (i.toUInt64 + 3) 108 (by decide) hp3,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 2) (i.toUInt64 + 4) 117 (by decide) hp4,
      byteAt_pos_iff b h64 hsize64 (i + 1 + 1 + 3) (i.toUInt64 + 5) 101 (by decide) hp5,
      eq_toUInt64_iff kl 5,
      ofNat_toUInt64 h64, apply_ite Key.ctorIdx, apply_ite UInt64.ofNat, ite_true, ite_false, and_assoc]
    rfl
  · rename_i heq1 heq2 heq3 heq4 heq5 heq6 heq7 heq8 heq9 heq10 heq11 heq12 heq13 heq14 heq15 heq16 heq17 heq18 heq19
    have hcw1 : ¬ byteW b.data (i.toUInt64 + 1) = 97 := fun h =>
      heq1 ((byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 97 (by decide) hp1).mpr h)
    have hcw2 : ¬ byteW b.data (i.toUInt64 + 1) = 98 := fun h =>
      heq2 ((byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 98 (by decide) hp1).mpr h)
    have hcw3 : ¬ byteW b.data (i.toUInt64 + 1) = 99 := fun h =>
      heq3 ((byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 99 (by decide) hp1).mpr h)
    have hcw4 : ¬ byteW b.data (i.toUInt64 + 1) = 100 := fun h =>
      heq4 ((byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 100 (by decide) hp1).mpr h)
    have hcw5 : ¬ byteW b.data (i.toUInt64 + 1) = 102 := fun h =>
      heq5 ((byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 102 (by decide) hp1).mpr h)
    have hcw6 : ¬ byteW b.data (i.toUInt64 + 1) = 104 := fun h =>
      heq6 ((byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 104 (by decide) hp1).mpr h)
    have hcw7 : ¬ byteW b.data (i.toUInt64 + 1) = 105 := fun h =>
      heq7 ((byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 105 (by decide) hp1).mpr h)
    have hcw8 : ¬ byteW b.data (i.toUInt64 + 1) = 107 := fun h =>
      heq8 ((byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 107 (by decide) hp1).mpr h)
    have hcw9 : ¬ byteW b.data (i.toUInt64 + 1) = 108 := fun h =>
      heq9 ((byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 108 (by decide) hp1).mpr h)
    have hcw10 : ¬ byteW b.data (i.toUInt64 + 1) = 109 := fun h =>
      heq10 ((byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 109 (by decide) hp1).mpr h)
    have hcw11 : ¬ byteW b.data (i.toUInt64 + 1) = 110 := fun h =>
      heq11 ((byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 110 (by decide) hp1).mpr h)
    have hcw12 : ¬ byteW b.data (i.toUInt64 + 1) = 111 := fun h =>
      heq12 ((byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 111 (by decide) hp1).mpr h)
    have hcw13 : ¬ byteW b.data (i.toUInt64 + 1) = 112 := fun h =>
      heq13 ((byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 112 (by decide) hp1).mpr h)
    have hcw14 : ¬ byteW b.data (i.toUInt64 + 1) = 113 := fun h =>
      heq14 ((byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 113 (by decide) hp1).mpr h)
    have hcw15 : ¬ byteW b.data (i.toUInt64 + 1) = 114 := fun h =>
      heq15 ((byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 114 (by decide) hp1).mpr h)
    have hcw16 : ¬ byteW b.data (i.toUInt64 + 1) = 115 := fun h =>
      heq16 ((byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 115 (by decide) hp1).mpr h)
    have hcw17 : ¬ byteW b.data (i.toUInt64 + 1) = 116 := fun h =>
      heq17 ((byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 116 (by decide) hp1).mpr h)
    have hcw18 : ¬ byteW b.data (i.toUInt64 + 1) = 117 := fun h =>
      heq18 ((byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 117 (by decide) hp1).mpr h)
    have hcw19 : ¬ byteW b.data (i.toUInt64 + 1) = 118 := fun h =>
      heq19 ((byteAt_pos_iff b h64 hsize64 (i+1) (i.toUInt64+1) 118 (by decide) hp1).mpr h)
    simp [hcw1, hcw2, hcw3, hcw4, hcw5, hcw6, hcw7, hcw8, hcw9, hcw10, hcw11, hcw12, hcw13, hcw14, hcw15, hcw16, hcw17, hcw18, hcw19]
    rfl

/-! ## `value_at` -/

/-- `byteW` is `0` past the end, exactly as `byteAt` (`WordLink.byteAt_toUInt64_eq`) — used by
`value_at`'s link for the (actually redundant, but present in the model) `p < len(IN.u8)` guard. -/
theorem byteW_eq_zero_of_ge (b : Array UInt8) (pos : Word) (h : b.size ≤ pos.toNat) :
    byteW b pos = 0 := by
  unfold byteW
  rw [Array.getD, dite_eq_right (by omega : ¬ pos.toNat < b.size)]
  decide

include h64 in
/-- con-leche's `valueAt`, through the model: past the colon, whitespace skipped on both sides
(`skip_ws`'s `LeafLink.skipWs_toUInt64_eq`); `i` when the colon is missing. The model's extra
`p < len(IN.u8)` guard is implied either way (`byteW_eq_zero_of_ge`'s contrapositive: a colon
isn't `0`), so the two conditions agree without it mattering which side needs it. -/
theorem valueAt_eq_valueAtN (hsize : b.size < 2 ^ 63) (i ke : USize) :
    (valueAt b i ke).toUInt64 = valueAtN b.data i.toUInt64 ke.toUInt64 := by
  have hsize64 : b.size < 2 ^ 64 := by omega
  have hbsize : (UInt64.ofNat b.data.size).toNat = b.data.size := UInt64.toNat_ofNat_of_lt' hsize64
  have hke1 : (ke + 1).toNat = (ke.toUInt64 + 1).toNat := by
    simp only [USize.toNat_add, UInt64.toNat_add, USize.toNat_ofNat, UInt64.toNat_ofNat,
      USize.toNat_toUInt64, h64] <;> omega
  unfold valueAt valueAtN
  dsimp only
  have hp_eq : (skipWs b (ke + 1)).toUInt64 = UInt64.ofNat (skipWsN b.data (ke.toUInt64 + 1).toNat) := by
    rw [skipWs_toUInt64_eq b h64 hsize64, hke1]
  have hcond : byteAt b (skipWs b (ke + 1)) = 58 ↔
      byteW b.data (skipWs b (ke + 1)).toUInt64 = 58 :=
    byteAt_pos_iff b h64 hsize64 (skipWs b (ke + 1)) (skipWs b (ke + 1)).toUInt64 58 (by decide)
      (by rw [USize.toNat_toUInt64])
  rw [hp_eq] at hcond
  by_cases hc : byteAt b (skipWs b (ke + 1)) = 58
  · have hcw : byteW b.data (UInt64.ofNat (skipWsN b.data (ke.toUInt64 + 1).toNat)) = 58 := hcond.mp hc
    have hcb : (byteAt b (skipWs b (ke + 1)) == 58) = true := by simpa using hc
    have hpbound : UInt64.ofNat (skipWsN b.data (ke.toUInt64 + 1).toNat) < UInt64.ofNat b.data.size := by
      rw [UInt64.lt_iff_toNat_lt, hbsize]
      by_cases hb : (UInt64.ofNat (skipWsN b.data (ke.toUInt64 + 1).toNat)).toNat < b.data.size
      · exact hb
      · exfalso
        rw [byteW_eq_zero_of_ge b.data _ (by omega)] at hcw
        exact absurd hcw (by decide)
    simp only [hcb, ite_true, hpbound, hcw, and_self]
    have hke2 : (skipWs b (ke + 1) + 1).toNat =
        (UInt64.ofNat (skipWsN b.data (ke.toUInt64 + 1).toNat) + 1).toNat := by
      rw [← hp_eq]
      simp only [USize.toNat_add, UInt64.toNat_add, USize.toNat_ofNat, UInt64.toNat_ofNat,
        USize.toNat_toUInt64, h64] <;> omega
    rw [skipWs_toUInt64_eq b h64 hsize64, hke2]
  · have hcw : ¬ byteW b.data (UInt64.ofNat (skipWsN b.data (ke.toUInt64 + 1).toNat)) = 58 :=
      fun h => hc (hcond.mpr h)
    have hcb : ¬ (byteAt b (skipWs b (ke + 1)) == 58) = true := by simpa using hc
    simp only [hcb, ite_false, hcw, and_false]
    simp

end ConAgua.Scan
