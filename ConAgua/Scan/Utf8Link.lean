module

public import ConAgua.Scan.Utf8
import Std.Data.DTreeMap.Internal.Operations
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-!
# `utf8_decode` against Lean's UTF-8 decoder

con-leche decodes a string body with `String.fromUTF8?` (`ConLeche/Frontend/Scan/Fast.lean`), which
is `ByteArray.utf8Decode?`: `ByteArray.utf8DecodeChar?` (lead byte by bit masks, then
`assemble₁…₄` with the overlong, surrogate and range checks) in a loop. Rust's `utf8_decode`
(and the word-level model `utf8LoopN` of the L code) tests the lead byte by ranges instead.

* `utf8CharN_eq`: one code point. The two decoders agree byte for byte: the lead byte classes
  by `decide` over the 256 values (`pfb`, `cont_eq`), the assembled values as natural numbers
  (`v2W`…`v4L`, bit operations turned into `%`, `*`, `+`), and six cases on the lead byte
  (`decA`…`decF`), where Rust's `0xC0`/`0xC1` and `0xF5`–`0xF7` rejections are Lean's overlong
  and range checks.
* `loop_go`: the loop, by `fun_induction` on `utf8Decode?.go`; the model also stops when `OUT`
  is full (L's store fails there).
* `utf8Decode_run`: the end-to-end statement about `run utf8Prog`.
-/

namespace ConAgua.Scan

open L L.Scan.Utf8 ByteArray.utf8DecodeChar?

theorem u8_all {P : UInt8 → Prop} (h : ∀ n, n < 256 → P (UInt8.ofNat n)) (w : UInt8) : P w := by
  have := h w.toNat w.toNat_lt
  simpa using this

theorem cont_eq (x : UInt8) : x.isUTF8ContinuationByte = decide (128 ≤ x.toNat ∧ x.toNat < 192) :=
  u8_all (P := fun x => x.isUTF8ContinuationByte = decide (128 ≤ x.toNat ∧ x.toNat < 192))
    (by decide +kernel) x

theorem pfb (w : UInt8) : parseFirstByte w =
    if w.toNat < 128 then .done else if w.toNat < 192 then .invalid else if w.toNat < 224 then .oneMore
    else if w.toNat < 240 then .twoMore else if w.toNat < 248 then .threeMore else .invalid := by
  have h1 := u8_all (P := fun x => (x &&& 0x80 == 0) = decide (x.toNat < 128)) (by decide +kernel) w
  have h2 := u8_all (P := fun x => (x &&& 0xe0 == 0xc0) = decide (192 ≤ x.toNat ∧ x.toNat < 224))
    (by decide +kernel) w
  have h3 := u8_all (P := fun x => (x &&& 0xf0 == 0xe0) = decide (224 ≤ x.toNat ∧ x.toNat < 240))
    (by decide +kernel) w
  have h4 := u8_all (P := fun x => (x &&& 0xf8 == 0xf0) = decide (240 ≤ x.toNat ∧ x.toNat < 248))
    (by decide +kernel) w
  have := w.toNat_lt
  unfold parseFirstByte
  rw [h1, h2, h3, h4]
  simp only [decide_eq_true_eq]
  repeat' split
  all_goals first | rfl | omega

theorem and_mask (a k : Nat) : a &&& (2 ^ k - 1) = a % 2 ^ k := Nat.and_two_pow_sub_one_eq_mod a k

theorem or_shift (a b k : Nat) (hb : b < 2 ^ k) : a <<< k ||| b = a * 2 ^ k + b := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt hb, Nat.shiftLeft_eq]

/-! Values as natural numbers. -/

theorem v2W (w x : UInt8) : (((w.toUInt64 &&& 0x1F) <<< 6) ||| (x.toUInt64 &&& 0x3F)).toNat =
    w.toNat % 32 * 64 + x.toNat % 64 := by
  have hw := w.toNat_lt; have hx := x.toNat_lt
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_and, UInt8.toNat_toUInt64]
  rw [show (UInt64.toNat 0x1F) = 2 ^ 5 - 1 from rfl, show (UInt64.toNat 0x3F) = 2 ^ 6 - 1 from rfl,
    and_mask, and_mask, show (UInt64.toNat 6) % 64 = 6 from rfl, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega), ← Nat.shiftLeft_eq, or_shift _ _ _ (by omega)]
  omega

theorem v2L (w x : UInt8) : (assemble₂Unchecked w x).toNat = w.toNat % 32 * 64 + x.toNat % 64 := by
  have hw := w.toNat_lt; have hx := x.toNat_lt
  simp only [assemble₂Unchecked, UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32,
    UInt8.toNat_and]
  rw [show (UInt8.toNat 0x1f) = 2 ^ 5 - 1 from rfl, show (UInt8.toNat 0x3f) = 2 ^ 6 - 1 from rfl,
    and_mask, and_mask, show (UInt32.toNat 6) % 32 = 6 from rfl, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega), ← Nat.shiftLeft_eq, or_shift _ _ _ (by omega)]
  omega

theorem or_eq_add {a b : Nat} (k : Nat) (ha : 2 ^ k ∣ a) (hb : b < 2 ^ k) : a ||| b = a + b := by
  obtain ⟨c, rfl⟩ := ha; exact (Nat.two_pow_add_eq_or_of_lt hb c).symm

theorem v3W (w x y : UInt8) : (((w.toUInt64 &&& 0x0F) <<< 12) ||| ((x.toUInt64 &&& 0x3F) <<< 6) |||
    (y.toUInt64 &&& 0x3F)).toNat = w.toNat % 16 * 4096 + x.toNat % 64 * 64 + y.toNat % 64 := by
  have hw := w.toNat_lt; have hx := x.toNat_lt; have hy := y.toNat_lt
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_and, UInt8.toNat_toUInt64]
  rw [show (UInt64.toNat 0x0F) = 2 ^ 4 - 1 from rfl, show (UInt64.toNat 0x3F) = 2 ^ 6 - 1 from rfl,
    and_mask, and_mask, and_mask, show (UInt64.toNat 6) % 64 = 6 from rfl,
    show (UInt64.toNat 12) % 64 = 12 from rfl, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (a := w.toNat % 2 ^ 4 * 2 ^ 12) (by omega),
    Nat.mod_eq_of_lt (a := x.toNat % 2 ^ 6 * 2 ^ 6) (by omega),
    or_eq_add 12 (Nat.dvd_mul_left _ _) (by omega),
    or_eq_add 6 (by simp only [Nat.reducePow]; omega) (by omega)]

theorem v3L (w x y : UInt8) : (assemble₃Unchecked w x y).toNat =
    w.toNat % 16 * 4096 + x.toNat % 64 * 64 + y.toNat % 64 := by
  have hw := w.toNat_lt; have hx := x.toNat_lt; have hy := y.toNat_lt
  simp only [assemble₃Unchecked, UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32,
    UInt8.toNat_and]
  rw [show (UInt8.toNat 0x0f) = 2 ^ 4 - 1 from rfl, show (UInt8.toNat 0x3f) = 2 ^ 6 - 1 from rfl,
    and_mask, and_mask, and_mask, show (UInt32.toNat 6) % 32 = 6 from rfl,
    show (UInt32.toNat 12) % 32 = 12 from rfl, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (a := w.toNat % 2 ^ 4 * 2 ^ 12) (by omega),
    Nat.mod_eq_of_lt (a := x.toNat % 2 ^ 6 * 2 ^ 6) (by omega),
    or_eq_add 12 (Nat.dvd_mul_left _ _) (by omega),
    or_eq_add 6 (by simp only [Nat.reducePow]; omega) (by omega)]

theorem v4W (w x y z : UInt8) : (((w.toUInt64 &&& 0x07) <<< 18) ||| ((x.toUInt64 &&& 0x3F) <<< 12) |||
    ((y.toUInt64 &&& 0x3F) <<< 6) ||| (z.toUInt64 &&& 0x3F)).toNat =
    w.toNat % 8 * 262144 + x.toNat % 64 * 4096 + y.toNat % 64 * 64 + z.toNat % 64 := by
  have hw := w.toNat_lt; have hx := x.toNat_lt; have hy := y.toNat_lt; have hz := z.toNat_lt
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_and, UInt8.toNat_toUInt64]
  rw [show (UInt64.toNat 0x07) = 2 ^ 3 - 1 from rfl, show (UInt64.toNat 0x3F) = 2 ^ 6 - 1 from rfl,
    and_mask, and_mask, and_mask, and_mask, show (UInt64.toNat 6) % 64 = 6 from rfl,
    show (UInt64.toNat 12) % 64 = 12 from rfl, show (UInt64.toNat 18) % 64 = 18 from rfl,
    Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (a := w.toNat % 2 ^ 3 * 2 ^ 18) (by omega),
    Nat.mod_eq_of_lt (a := x.toNat % 2 ^ 6 * 2 ^ 12) (by omega),
    Nat.mod_eq_of_lt (a := y.toNat % 2 ^ 6 * 2 ^ 6) (by omega),
    or_eq_add 18 (Nat.dvd_mul_left _ _) (by omega),
    or_eq_add (a := w.toNat % 2 ^ 3 * 2 ^ 18 + x.toNat % 2 ^ 6 * 2 ^ 12) (b := y.toNat % 2 ^ 6 * 2 ^ 6) 12
      (by simp only [Nat.reducePow]; omega) (by omega),
    or_eq_add (a := w.toNat % 2 ^ 3 * 2 ^ 18 + x.toNat % 2 ^ 6 * 2 ^ 12 + y.toNat % 2 ^ 6 * 2 ^ 6)
      (b := z.toNat % 2 ^ 6) 6 (by simp only [Nat.reducePow]; omega) (by omega)]

theorem v4L (w x y z : UInt8) : (assemble₄Unchecked w x y z).toNat =
    w.toNat % 8 * 262144 + x.toNat % 64 * 4096 + y.toNat % 64 * 64 + z.toNat % 64 := by
  have hw := w.toNat_lt; have hx := x.toNat_lt; have hy := y.toNat_lt; have hz := z.toNat_lt
  simp only [assemble₄Unchecked, UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32,
    UInt8.toNat_and]
  rw [show (UInt8.toNat 0x07) = 2 ^ 3 - 1 from rfl, show (UInt8.toNat 0x3f) = 2 ^ 6 - 1 from rfl,
    and_mask, and_mask, and_mask, and_mask, show (UInt32.toNat 6) % 32 = 6 from rfl,
    show (UInt32.toNat 12) % 32 = 12 from rfl, show (UInt32.toNat 18) % 32 = 18 from rfl,
    Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (a := w.toNat % 2 ^ 3 * 2 ^ 18) (by omega),
    Nat.mod_eq_of_lt (a := x.toNat % 2 ^ 6 * 2 ^ 12) (by omega),
    Nat.mod_eq_of_lt (a := y.toNat % 2 ^ 6 * 2 ^ 6) (by omega),
    or_eq_add 18 (Nat.dvd_mul_left _ _) (by omega),
    or_eq_add (a := w.toNat % 2 ^ 3 * 2 ^ 18 + x.toNat % 2 ^ 6 * 2 ^ 12) (b := y.toNat % 2 ^ 6 * 2 ^ 6) 12
      (by simp only [Nat.reducePow]; omega) (by omega),
    or_eq_add (a := w.toNat % 2 ^ 3 * 2 ^ 18 + x.toNat % 2 ^ 6 * 2 ^ 12 + y.toNat % 2 ^ 6 * 2 ^ 6)
      (b := z.toNat % 2 ^ 6) 6 (by simp only [Nat.reducePow]; omega) (by omega)]

/-- One code point as `utf8_char` returns it. -/
def encChar : Option Char → Word × Word
  | some c => (c.val.toUInt64, UInt64.ofNat c.utf8Size)
  | none => (0, 0)

section
variable (B : ByteArray) (i : Nat) (hi : i < B.size)
include hi

attribute [local simp] UInt32.le_iff_toNat_le UInt32.lt_iff_toNat_lt UInt8.toNat_toUInt32

theorem decA (h : B[i].toNat < 128) : encChar (B.utf8DecodeChar? i) = (B[i].toUInt64, 1) := by
  unfold ByteArray.utf8DecodeChar?
  rw [dite_eq_left hi]
  split <;> rename_i heq <;> rw [pfb] at heq <;> simp [h] at heq
  simp [assemble₁, encChar, Char.utf8Size, show B[i].toNat ≤ 127 by omega]

theorem decB (h : 128 ≤ B[i].toNat ∧ B[i].toNat < 194) : encChar (B.utf8DecodeChar? i) = (0, 0) := by
  unfold ByteArray.utf8DecodeChar?
  rw [dite_eq_left hi]
  split <;> rename_i heq <;> rw [pfb] at heq <;> repeat' (split at heq)
  all_goals first | rfl | (exfalso; omega) | exact FirstByte.noConfusion heq | skip
  split
  · simp only [assemble₂]
    split
    · rfl
    · rename_i h1 hc
      have hv := v2L B[i] B[i + 1]
      rw [ite_eq_left (show assemble₂Unchecked B[i] B[i + 1] < 128 by
        rw [UInt32.lt_iff_toNat_lt, hv]; simp only [UInt32.reduceToNat]; omega)]
      rfl
  · rfl

theorem decC (h : 194 ≤ B[i].toNat ∧ B[i].toNat < 224) : encChar (B.utf8DecodeChar? i) =
    if h1 : i + 1 < B.size then
      (if 128 ≤ B[i + 1].toNat ∧ B[i + 1].toNat < 192 then
        (UInt64.ofNat (B[i].toNat % 32 * 64 + B[i + 1].toNat % 64), 2) else (0, 0))
    else (0, 0) := by
  unfold ByteArray.utf8DecodeChar?
  rw [dite_eq_left hi]
  split <;> rename_i heq <;> rw [pfb] at heq <;> repeat' (split at heq)
  all_goals first | (exfalso; omega) | exact FirstByte.noConfusion heq | skip
  by_cases h1 : i + 1 < B.size
  · simp only [h1, dite_true, assemble₂, cont_eq]
    by_cases hc : 128 ≤ B[i + 1].toNat ∧ B[i + 1].toNat < 192
    · have hv := v2L B[i] B[i + 1]
      simp only [hc, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, and_self, ite_true]
      rw [ite_eq_right (show ¬ assemble₂Unchecked B[i] B[i + 1] < 128 by
        rw [UInt32.lt_iff_toNat_lt, hv]; simp only [UInt32.reduceToNat]; omega)]
      simp only [encChar, Char.utf8Size, UInt32.le_iff_toNat_le, hv, UInt32.toNat_ofNatLT]
      rw [ite_eq_right (by omega), ite_eq_left (by omega)]
      have := B[i].toNat_lt; have := B[i + 1].toNat_lt
      congr 1
      apply UInt64.toNat_inj.mp
      simp [hv]; omega
    · simp [hc, encChar]
  · simp [h1, encChar]

theorem decD (h : 224 ≤ B[i].toNat ∧ B[i].toNat < 240) : encChar (B.utf8DecodeChar? i) =
    if h2 : i + 2 < B.size then
      (if (128 ≤ B[i + 1].toNat ∧ B[i + 1].toNat < 192) ∧ (128 ≤ B[i + 2].toNat ∧ B[i + 2].toNat < 192) then
        (if B[i].toNat % 16 * 4096 + B[i + 1].toNat % 64 * 64 + B[i + 2].toNat % 64 < 2048 ∨
            (55296 ≤ B[i].toNat % 16 * 4096 + B[i + 1].toNat % 64 * 64 + B[i + 2].toNat % 64 ∧
             B[i].toNat % 16 * 4096 + B[i + 1].toNat % 64 * 64 + B[i + 2].toNat % 64 ≤ 57343) then (0, 0)
         else (UInt64.ofNat (B[i].toNat % 16 * 4096 + B[i + 1].toNat % 64 * 64 + B[i + 2].toNat % 64), 3))
       else (0, 0))
    else (0, 0) := by
  unfold ByteArray.utf8DecodeChar?
  rw [dite_eq_left hi]
  split <;> rename_i heq <;> rw [pfb] at heq <;> repeat' (split at heq)
  all_goals first | (exfalso; omega) | exact FirstByte.noConfusion heq | skip
  by_cases h2 : i + 2 < B.size
  · simp only [h2, dite_true, assemble₃, cont_eq]
    by_cases hc : (128 ≤ B[i + 1].toNat ∧ B[i + 1].toNat < 192) ∧ (128 ≤ B[i + 2].toNat ∧ B[i + 2].toNat < 192)
    · have hv := v3L B[i] B[i + 1] B[i + 2]
      simp only [hc, decide_true, Bool.not_true, Bool.or_self, Bool.false_eq_true, ite_false, ite_true,
        and_self]
      simp only [UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le, hv, UInt32.reduceToNat]
      by_cases hr : B[i].toNat % 16 * 4096 + B[i + 1].toNat % 64 * 64 + B[i + 2].toNat % 64 < 2048
      · simp [hr, encChar]
      · by_cases hs : 55296 ≤ B[i].toNat % 16 * 4096 + B[i + 1].toNat % 64 * 64 + B[i + 2].toNat % 64 ∧
            B[i].toNat % 16 * 4096 + B[i + 1].toNat % 64 * 64 + B[i + 2].toNat % 64 ≤ 57343
        · simp [hr, hs, encChar]
        · simp only [hr, hs, ite_false, dite_false, false_or]
          simp only [encChar, Char.utf8Size, UInt32.le_iff_toNat_le, hv, UInt32.toNat_ofNatLT]
          rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
          have := B[i].toNat_lt; have := B[i + 1].toNat_lt; have := B[i + 2].toNat_lt
          congr 1
          apply UInt64.toNat_inj.mp
          simp [hv]; omega
    · simp only [encChar]
      rw [ite_eq_left (by simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]; omega),
        ite_eq_right hc]
  · simp [h2, encChar]

theorem decE (h : 240 ≤ B[i].toNat ∧ B[i].toNat < 245) : encChar (B.utf8DecodeChar? i) =
    if h3 : i + 3 < B.size then
      (if (128 ≤ B[i + 1].toNat ∧ B[i + 1].toNat < 192) ∧ (128 ≤ B[i + 2].toNat ∧ B[i + 2].toNat < 192) ∧
          (128 ≤ B[i + 3].toNat ∧ B[i + 3].toNat < 192) then
        (if B[i].toNat % 8 * 262144 + B[i + 1].toNat % 64 * 4096 + B[i + 2].toNat % 64 * 64 +
              B[i + 3].toNat % 64 < 65536 ∨
            1114111 < B[i].toNat % 8 * 262144 + B[i + 1].toNat % 64 * 4096 + B[i + 2].toNat % 64 * 64 +
              B[i + 3].toNat % 64 then (0, 0)
         else (UInt64.ofNat (B[i].toNat % 8 * 262144 + B[i + 1].toNat % 64 * 4096 +
           B[i + 2].toNat % 64 * 64 + B[i + 3].toNat % 64), 4))
       else (0, 0))
    else (0, 0) := by
  unfold ByteArray.utf8DecodeChar?
  rw [dite_eq_left hi]
  split <;> rename_i heq <;> rw [pfb] at heq <;> repeat' (split at heq)
  all_goals first | (exfalso; omega) | exact FirstByte.noConfusion heq | skip
  by_cases h3 : i + 3 < B.size
  · simp only [h3, dite_true, assemble₄, cont_eq]
    by_cases hc : (128 ≤ B[i + 1].toNat ∧ B[i + 1].toNat < 192) ∧ (128 ≤ B[i + 2].toNat ∧ B[i + 2].toNat < 192) ∧
          (128 ≤ B[i + 3].toNat ∧ B[i + 3].toNat < 192)
    · have hv := v4L B[i] B[i + 1] B[i + 2] B[i + 3]
      simp only [hc, decide_true, Bool.not_true, Bool.or_self, Bool.false_eq_true, ite_false, ite_true,
        and_self]
      have e1 : assemble₄Unchecked B[i] B[i + 1] B[i + 2] B[i + 3] < 0x10000 ↔
          B[i].toNat % 8 * 262144 + B[i + 1].toNat % 64 * 4096 + B[i + 2].toNat % 64 * 64 +
            B[i + 3].toNat % 64 < 65536 := by
        rw [UInt32.lt_iff_toNat_lt, hv]; rfl
      have e2 : 0x10ffff < assemble₄Unchecked B[i] B[i + 1] B[i + 2] B[i + 3] ↔
          1114111 < B[i].toNat % 8 * 262144 + B[i + 1].toNat % 64 * 4096 + B[i + 2].toNat % 64 * 64 +
            B[i + 3].toNat % 64 := by
        rw [UInt32.lt_iff_toNat_lt, hv]; rfl
      by_cases hr : B[i].toNat % 8 * 262144 + B[i + 1].toNat % 64 * 4096 + B[i + 2].toNat % 64 * 64 +
              B[i + 3].toNat % 64 < 65536
      · rw [dite_eq_left (e1.2 hr)]; simp [hr, encChar]
      · rw [dite_eq_right (mt e1.1 hr)]
        by_cases hs : 1114111 < B[i].toNat % 8 * 262144 + B[i + 1].toNat % 64 * 4096 +
            B[i + 2].toNat % 64 * 64 + B[i + 3].toNat % 64
        · rw [dite_eq_left (e2.2 hs)]; simp [hr, hs, encChar]
        · rw [dite_eq_right (mt e2.1 hs)]
          simp only [hr, hs, ite_false, false_or]
          simp only [encChar, Char.utf8Size, UInt32.le_iff_toNat_le, hv, UInt32.toNat_ofNatLT]
          rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
          have := B[i].toNat_lt; have := B[i + 1].toNat_lt; have := B[i + 2].toNat_lt
          have := B[i + 3].toNat_lt
          congr 1
          apply UInt64.toNat_inj.mp
          simp [hv]; omega
    · simp only [encChar]
      rw [ite_eq_left (by simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]; omega),
        ite_eq_right hc]
  · simp [h3, encChar]

theorem decF (h : 245 ≤ B[i].toNat) : encChar (B.utf8DecodeChar? i) = (0, 0) := by
  unfold ByteArray.utf8DecodeChar?
  rw [dite_eq_left hi]
  split <;> rename_i heq <;> rw [pfb] at heq <;> repeat' (split at heq)
  all_goals first | rfl | (exfalso; omega) | exact FirstByte.noConfusion heq | skip
  split
  · simp only [assemble₄]
    split
    · rfl
    · have hv := v4L B[i] B[i + 1] B[i + 2] B[i + 3]
      have := B[i].toNat_lt
      rw [dite_eq_right (show ¬ assemble₄Unchecked B[i] B[i + 1] B[i + 2] B[i + 3] < 0x10000 by
        rw [UInt32.lt_iff_toNat_lt, hv]; simp only [UInt32.reduceToNat]; omega)]
      rw [dite_eq_left (show 0x10ffff < assemble₄Unchecked B[i] B[i + 1] B[i + 2] B[i + 3] by
        rw [UInt32.lt_iff_toNat_lt, hv]; simp only [UInt32.reduceToNat]; omega)]
      rfl
  · rfl

end

theorem u8lt (a : UInt8) (c : UInt64) : (a.toUInt64 < c) = (a.toNat < c.toNat) := by
  simp [UInt64.lt_iff_toNat_lt]
theorem u8le (a : UInt8) (c : UInt64) : (c ≤ a.toUInt64) = (c.toNat ≤ a.toNat) := by
  simp [UInt64.le_iff_toNat_le]
theorem wlt (a : Word) (c : UInt64) : (a < c) = (a.toNat < c.toNat) := by
  simp [UInt64.lt_iff_toNat_lt]
theorem wle (a : Word) (c : UInt64) : (c ≤ a) = (c.toNat ≤ a.toNat) := by
  simp [UInt64.le_iff_toNat_le]

theorem ofNat_eq (v : Nat) (x : Word) (h : x.toNat = v) : x = UInt64.ofNat v := by
  subst h; simp

theorem utf8CharN_eq (b : Array UInt8) (k n : Word) (B : ByteArray) (i : Nat) (hi : i < B.size)
    (hkn : n.toNat = k.toNat + (B.size - i)) (hn : n.toNat + 4 < 2 ^ 64)
    (hB : ∀ t (h : i + t < B.size), b.getD (k.toNat + t) 0 = B[i + t]) :
    utf8CharN b k n = encChar (B.utf8DecodeChar? i) := by
  have hkt : ∀ t : Nat, t < 4 → (k + UInt64.ofNat t).toNat = k.toNat + t := by
    intro t ht; rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)]
    simp; omega
  have hle : ∀ t : Nat, t < 4 → (n ≤ k + UInt64.ofNat t ↔ B.size ≤ i + t) := by
    intro t ht; rw [UInt64.le_iff_toNat_le, hkt t ht]; omega
  have hbt : ∀ t : Nat, t < 4 → (h : i + t < B.size) →
      byteW b (k + UInt64.ofNat t) = B[i + t].toUInt64 := by
    intro t ht h; simp only [byteW, hkt t ht, hB t h]
  have hb0 : byteW b k = B[i].toUInt64 := by simpa using hbt 0 (by omega) (by omega)
  have hle1 := hle 1 (by omega); have hle2 := hle 2 (by omega); have hle3 := hle 3 (by omega)
  simp only [UInt64.reduceOfNat] at hle1 hle2 hle3
  have hw := B[i].toNat_lt
  unfold utf8CharN
  rw [hb0]
  simp only [u8lt, UInt64.reduceToNat]
  rcases (show B[i].toNat < 128 ∨ (128 ≤ B[i].toNat ∧ B[i].toNat < 194) ∨
      (194 ≤ B[i].toNat ∧ B[i].toNat < 224) ∨ (224 ≤ B[i].toNat ∧ B[i].toNat < 240) ∨
      (240 ≤ B[i].toNat ∧ B[i].toNat < 245) ∨ 245 ≤ B[i].toNat by omega) with h | h | h | h | h | h
  · rw [decA B i hi h]; simp [h]
  · rw [decB B i hi h]; simp [show ¬ B[i].toNat < 128 by omega, show B[i].toNat < 194 by omega]
  · rw [decC B i hi h]
    simp only [show ¬ B[i].toNat < 128 by omega, show ¬ B[i].toNat < 194 by omega,
      show B[i].toNat < 224 by omega, ite_false, ite_true]
    by_cases h1 : i + 1 < B.size
    · have hb1 := hbt 1 (by omega) h1
      simp only [UInt64.reduceOfNat] at hb1
      simp only [show ¬ n ≤ k + 1 by rw [hle1]; omega, h1, ite_false, dite_true, hb1, u8lt, u8le,
        UInt64.reduceToNat]
      by_cases hc : 128 ≤ B[i + 1].toNat ∧ B[i + 1].toNat < 192
      · rw [ite_eq_right (by omega), ite_eq_left hc]
        congr 1
        exact ofNat_eq _ _ (v2W _ _)
      · rw [ite_eq_left (by omega), ite_eq_right hc]
    · simp [show n ≤ k + 1 by rw [hle1]; omega, h1]
  · rw [decD B i hi h]
    simp only [show ¬ B[i].toNat < 128 by omega, show ¬ B[i].toNat < 194 by omega,
      show ¬ B[i].toNat < 224 by omega, show B[i].toNat < 240 by omega, ite_false, ite_true]
    by_cases h2 : i + 2 < B.size
    · have hb1 := hbt 1 (by omega) (by omega)
      have hb2 := hbt 2 (by omega) h2
      simp only [UInt64.reduceOfNat] at hb1 hb2
      simp only [show ¬ n ≤ k + 2 by rw [hle2]; omega, h2, ite_false, dite_true, hb1, hb2,
        UInt64.reduceToNat, wlt, wle, v3W, UInt8.toNat_toUInt64]
      by_cases hc : (128 ≤ B[i + 1].toNat ∧ B[i + 1].toNat < 192) ∧ (128 ≤ B[i + 2].toNat ∧ B[i + 2].toNat < 192)
      · rw [ite_eq_right (by omega), ite_eq_left hc]
        by_cases hr : B[i].toNat % 16 * 4096 + B[i + 1].toNat % 64 * 64 + B[i + 2].toNat % 64 < 2048 ∨
            (55296 ≤ B[i].toNat % 16 * 4096 + B[i + 1].toNat % 64 * 64 + B[i + 2].toNat % 64 ∧
             B[i].toNat % 16 * 4096 + B[i + 1].toNat % 64 * 64 + B[i + 2].toNat % 64 ≤ 57343)
        · rw [ite_eq_left (by omega), ite_eq_left hr]
        · rw [ite_eq_right (by omega), ite_eq_right hr]
          congr 1
          exact ofNat_eq _ _ (v3W _ _ _)
      · rw [ite_eq_left (by omega), ite_eq_right hc]
    · simp [show n ≤ k + 2 by rw [hle2]; omega, h2]
  · rw [decE B i hi h]
    simp only [show ¬ B[i].toNat < 128 by omega, show ¬ B[i].toNat < 194 by omega,
      show ¬ B[i].toNat < 224 by omega, show ¬ B[i].toNat < 240 by omega, show B[i].toNat < 245 by omega,
      ite_false, ite_true]
    by_cases h3 : i + 3 < B.size
    · have hb1 := hbt 1 (by omega) (by omega)
      have hb2 := hbt 2 (by omega) (by omega)
      have hb3 := hbt 3 (by omega) h3
      simp only [UInt64.reduceOfNat] at hb1 hb2 hb3
      simp only [show ¬ n ≤ k + 3 by rw [hle3]; omega, h3, ite_false, dite_true, hb1, hb2, hb3,
        UInt64.reduceToNat, wlt, wle, v4W, UInt8.toNat_toUInt64]
      by_cases hc : (128 ≤ B[i + 1].toNat ∧ B[i + 1].toNat < 192) ∧
          (128 ≤ B[i + 2].toNat ∧ B[i + 2].toNat < 192) ∧ (128 ≤ B[i + 3].toNat ∧ B[i + 3].toNat < 192)
      · rw [ite_eq_right (by omega), ite_eq_left hc]
        by_cases hr : B[i].toNat % 8 * 262144 + B[i + 1].toNat % 64 * 4096 + B[i + 2].toNat % 64 * 64 +
              B[i + 3].toNat % 64 < 65536 ∨
            1114111 < B[i].toNat % 8 * 262144 + B[i + 1].toNat % 64 * 4096 + B[i + 2].toNat % 64 * 64 +
              B[i + 3].toNat % 64
        · rw [ite_eq_left (by omega), ite_eq_left hr]
        · rw [ite_eq_right (by omega), ite_eq_right hr]
          congr 1
          exact ofNat_eq _ _ (v4W _ _ _ _)
      · rw [ite_eq_left (by omega), ite_eq_right hc]
    · simp [show n ≤ k + 3 by rw [hle3]; omega, h3]
  · rw [decF B i hi h]
    simp [show ¬ B[i].toNat < 128 by omega, show ¬ B[i].toNat < 194 by omega,
      show ¬ B[i].toNat < 224 by omega, show ¬ B[i].toNat < 240 by omega, show ¬ B[i].toNat < 245 by omega]

theorem size_set64 (m : Mem) (a : ArrId) (c v : Word) :
    ((m.set64 a c v).arr64 a).size = (m.arr64 a).size := by
  simp only [Mem.set64, Mem.arr64, Array.getD_eq_getD_getElem?, Array.set!, Array.getElem?_setIfInBounds]
  by_cases h : a < m.words.size <;> simp [h]

theorem word_add (k : Word) (i : Nat) (h : k.toNat + i < 2 ^ 64) :
    (k + UInt64.ofNat i).toNat = k.toNat + i := by
  rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)]
  simp; omega

theorem arr64_set64_same (m : Mem) (c v : Word) :
    (m.set64 OUT c v).arr64 OUT = (m.arr64 OUT).set! c.toNat v := by
  simp only [Mem.set64, Mem.arr64, Array.getD_eq_getD_getElem?, Array.set!, Array.getElem?_setIfInBounds]
  by_cases h : OUT < m.words.size <;> simp [h]

end ConAgua.Scan
