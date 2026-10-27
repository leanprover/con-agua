module

public import ConAgua.Scan.Key
import ConAgua.Census.Attr
public import ConLeche.Frontend.Scan.Fast
import ConAgua.Scan.LeafLink
import ConAgua.Scan.WordLink
import Std.Data.DTreeMap.Internal.Operations
import Std.Tactic.BVDecide.Normalize.Prop

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
first byte, plus the catch-all); in each goal one `simp only` turns every `byteAt b (i + 1 + … + k)`
compare into the model's `byteW b.data (i.toUInt64 + k')` compare (`hb`, `add_toUInt64`,
`UInt64.add_assoc`) and every `kl` test into a test on `kl.toUInt64`, also in the split's
hypotheses; a `simp` with those hypotheses, `apply_ite` and `and_assoc` (realigning `lit1`…`lit10`'s
left-associated `&&` against the model's right-associated `∧`) then leaves both sides computing the
same number, closed by `rfl`.
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
@[refines ConLeche.Frontend.keyAt]
theorem keyAt_eq_keyAtN (hsize : b.size < 2 ^ 63) (i kl : USize)
    (_hi : i.toNat + 1 + kl.toNat < b.size) :
    UInt64.ofNat (keyAt b i kl).ctorIdx = keyAtN b.data i.toUInt64 kl.toUInt64 := by
  have hb : ∀ (pos : USize) (c : UInt8), byteAt b pos = c ↔ byteW b.data pos.toUInt64 = c.toUInt64 := by
    intro pos c
    rw [byteAt_eq_getD b h64 (by omega)]
    exact ⟨congrArg _, fun h => UInt8.toUInt64_inj.mp h⟩
  unfold keyAt keyAtN lit1 lit2 lit3 lit4 lit5 lit6 lit7 lit8 lit9 lit10
  dsimp only
  split <;> simp only [hb, add_toUInt64 h64, ofNat_toUInt64 h64, UInt8.toUInt64_ofNat, Nat.reduceLT, UInt64.add_assoc, UInt64.reduceAdd,
    Bool.and_eq_true, beq_iff_eq, eq_toUInt64_iff kl, imp_false] at * <;>
    simp [*, apply_ite Key.ctorIdx, apply_ite UInt64.ofNat, and_assoc] <;> rfl

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
@[refines ConLeche.Frontend.valueAt]
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
