module

public import ConAgua.Scan.Utf8

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
      simp only [UInt32.lt_iff_toNat_lt, hv, UInt32.reduceToNat]
      by_cases hr : B[i].toNat % 8 * 262144 + B[i + 1].toNat % 64 * 4096 + B[i + 2].toNat % 64 * 64 +
              B[i + 3].toNat % 64 < 65536
      · simp [hr, encChar]
      · by_cases hs : 1114111 < B[i].toNat % 8 * 262144 + B[i + 1].toNat % 64 * 4096 +
            B[i + 2].toNat % 64 * 64 + B[i + 3].toNat % 64
        · simp [hr, hs, encChar]
        · simp only [hr, hs, ite_false, dite_false, false_or]
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


/-- The memory after writing `vs` to `OUT` from `cnt` on. -/
def writeCps (m : Mem) (cnt : Word) : List Word → Mem
  | [] => m
  | v :: vs => writeCps (m.set64 OUT cnt v) (cnt + 1) vs

theorem size_set64 (m : Mem) (a : ArrId) (c v : Word) :
    ((m.set64 a c v).arr64 a).size = (m.arr64 a).size := by
  simp only [Mem.set64, Mem.arr64, Array.getD_eq_getD_getElem?, Array.set!, Array.getElem?_setIfInBounds]
  by_cases h : a < m.words.size <;> simp [h]

theorem go_prefix (B : ByteArray) (i : Nat) (acc : Array Char) (hi : i ≤ B.size) (arr : Array Char)
    (h : ByteArray.utf8Decode?.go B i acc hi = some arr) : acc.toList <+: arr.toList := by
  fun_induction ByteArray.utf8Decode?.go B i acc hi generalizing arr with
  | case1 => simp at h
  | case2 i acc hi h1 c h2 ih =>
    exact (List.prefix_append _ _).trans (by simpa using ih arr h)
  | case3 => simp_all

theorem word_add (k : Word) (i : Nat) (h : k.toNat + i < 2 ^ 64) :
    (k + UInt64.ofNat i).toNat = k.toNat + i := by
  rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)]
  simp; omega

theorem loop_go (b : Array UInt8) (k0 n : Word) (B : ByteArray)
    (hkn : n.toNat = k0.toNat + B.size) (hn : n.toNat + 4 < 2 ^ 64)
    (hB : ∀ t (h : t < B.size), b.getD (k0.toNat + t) 0 = B[t])
    (i : Nat) (acc : Array Char) (hi : i ≤ B.size) (cnt : Word) (m : Mem)
    (hc : cnt.toNat ≤ (m.arr64 OUT).size) (hO : (m.arr64 OUT).size < 2 ^ 64) :
    match ByteArray.utf8Decode?.go B i acc hi with
    | none => (utf8LoopN b (k0 + UInt64.ofNat i) n cnt m).1 = none
    | some arr =>
      if cnt.toNat + (arr.size - acc.size) ≤ (m.arr64 OUT).size then
        utf8LoopN b (k0 + UInt64.ofNat i) n cnt m =
          (some (cnt + UInt64.ofNat (arr.size - acc.size)),
           writeCps m cnt ((arr.toList.drop acc.size).map (·.val.toUInt64)))
      else (utf8LoopN b (k0 + UInt64.ofNat i) n cnt m).1 = none := by
  fun_induction ByteArray.utf8Decode?.go B i acc hi generalizing cnt m with
  | case1 i acc hi h1 h2 =>
    have hk := word_add k0 i (by omega)
    have hch := utf8CharN_eq b (k0 + UInt64.ofNat i) n B i h1 (by omega) hn
      (fun t ht => by rw [hk, Nat.add_assoc]; exact hB (i + t) ht)
    rw [h2] at hch
    simp only
    rw [utf8LoopN, ite_eq_left (by rw [UInt64.lt_iff_toNat_lt, hk]; omega), hch]
    rfl
  | case2 i acc hi h1 c h2 ih =>
    have hk := word_add k0 i (by omega)
    have hsz := ByteArray.le_size_of_utf8DecodeChar?_eq_some h2
    have hpos := c.utf8Size_pos
    have h4 := c.utf8Size_le_four
    have hch := utf8CharN_eq b (k0 + UInt64.ofNat i) n B i h1 (by omega) hn
      (fun t ht => by rw [hk, Nat.add_assoc]; exact hB (i + t) ht)
    rw [h2] at hch
    simp only [encChar] at hch
    have hlen : (UInt64.ofNat c.utf8Size).toNat = c.utf8Size :=
      UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
    have hk' : k0 + UInt64.ofNat i + UInt64.ofNat c.utf8Size = k0 + UInt64.ofNat (i + c.utf8Size) := by
      rw [UInt64.ofNat_add, UInt64.add_assoc]
    have hstep : k0 + UInt64.ofNat i < k0 + UInt64.ofNat i + UInt64.ofNat c.utf8Size := by
      rw [UInt64.lt_iff_toNat_lt, hk', word_add k0 (i + c.utf8Size) (by omega), hk]; omega
    rw [utf8LoopN, ite_eq_left (by rw [UInt64.lt_iff_toNat_lt, hk]; omega), hch]
    simp only [show ¬ UInt64.ofNat c.utf8Size = 0 from fun h => by
      have := congrArg UInt64.toNat h; rw [hlen] at this; simp at this; omega, ite_false]
    by_cases hcnt : cnt.toNat < (m.arr64 OUT).size
    · simp only [hcnt, hstep, and_self, ite_true]
      rw [hk']
      have hc1 : (cnt + 1).toNat = cnt.toNat + 1 := by
        rw [UInt64.toNat_add]; simp; omega
      have ih' := ih (cnt + 1) (m.set64 OUT cnt c.val.toUInt64) (by rw [size_set64, hc1]; omega)
        (by rw [size_set64]; exact hO)
      revert ih'
      cases hgo : ByteArray.utf8Decode?.go B (i + c.utf8Size) (acc.push c) (by omega) with
      | none => simp
      | some arr =>
        have hpre := go_prefix B (i + c.utf8Size) (acc.push c) (by omega) arr hgo
        have hpl := hpre.length_le
        simp only [Array.toList_push, List.length_append, List.length_cons, List.length_nil,
          Array.length_toList] at hpl
        simp only [size_set64, hc1]
        intro ih'
        have hd : arr.toList.drop acc.size = c :: arr.toList.drop (acc.size + 1) := by
          obtain ⟨t, ht⟩ := hpre; rw [← ht]
          simp only [Array.toList_push, List.append_assoc, List.cons_append, List.nil_append]
          rw [List.drop_left' (by simp), show acc.size + 1 = (acc.toList ++ [c]).length by simp,
            show acc.toList ++ c :: t = (acc.toList ++ [c]) ++ t by simp, List.drop_left]
        have hsz' : (acc.push c).size = acc.size + 1 := by simp
        rw [hsz', show cnt.toNat + 1 + (arr.size - (acc.size + 1)) = cnt.toNat + (arr.size - acc.size) by
          omega] at ih'
        split <;> rename_i hcond <;> simp only [hcond, ite_true, ite_false] at ih'
        · rw [ih', hd, List.map_cons, writeCps, show arr.size - acc.size = (arr.size - (acc.size + 1)) + 1 by
            omega, UInt64.ofNat_add]
          congr 2
          rw [UInt64.add_assoc, UInt64.add_comm 1]
          rfl
        · exact ih'
    · cases hgo : ByteArray.utf8Decode?.go B (i + c.utf8Size) (acc.push c) (by omega) with
      | none => simp [hcnt]
      | some arr =>
        have hpre := go_prefix B (i + c.utf8Size) (acc.push c) (by omega) arr hgo
        have hpl := hpre.length_le
        simp only [Array.toList_push, List.length_append, List.length_cons, List.length_nil,
          Array.length_toList] at hpl
        simp only
        rw [ite_eq_right (by omega)]
        simp [hcnt]
  | case3 i acc hi h1 =>
    have hk := word_add k0 i (by omega)
    simp only [Nat.sub_self, Nat.add_zero, hc, ite_true, List.drop_eq_nil_of_le (by simp : acc.toList.length ≤ acc.size),
      List.map_nil]
    rw [utf8LoopN, ite_eq_right (by rw [UInt64.lt_iff_toNat_lt, hk]; omega)]
    simp [writeCps]

theorem decode_some (B : ByteArray) (s : String) (h : String.fromUTF8? B = some s) :
    B.utf8Decode? = some s.toList.toArray := by
  unfold String.fromUTF8? at h
  split at h
  · rename_i hv
    cases h
    have hs := ByteArray.isSome_utf8Decode?_iff.mpr hv
    obtain ⟨arr, ha⟩ := Option.isSome_iff_exists.mp hs
    rw [ha]
    simp only [String.toList, String.Internal.toArray, String.fromUTF8]
    simp [ha]
  · cases h

theorem decode_none (B : ByteArray) (h : String.fromUTF8? B = none) : B.utf8Decode? = none := by
  unfold String.fromUTF8? at h
  split at h
  · cases h
  · rename_i hv
    cases hd : B.utf8Decode? with
    | none => rfl
    | some arr => exact absurd (ByteArray.isSome_utf8Decode?_iff.mp (by simp [hd])) hv

theorem utf8DecodeN_link (b : ByteArray) (hb : b.size + 4 < 2 ^ 64) (j e : Word) (m : Mem)
    (hO : (m.arr64 OUT).size < 2 ^ 64) :
    match String.fromUTF8? (b.extract j.toNat (min e.toNat b.size)) with
    | none => (utf8DecodeN b.data j e m).1 = none
    | some s =>
      if s.length ≤ (m.arr64 OUT).size then
        utf8DecodeN b.data j e m =
          (some (UInt64.ofNat s.length), writeCps m 0 (s.toList.map (·.val.toUInt64)))
      else (utf8DecodeN b.data j e m).1 = none := by
  have hbs : b.data.size = b.size := rfl
  have hsz : (UInt64.ofNat b.size).toNat = b.size := UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  have hn' : (if e < UInt64.ofNat b.size then e else UInt64.ofNat b.size).toNat = min e.toNat b.size := by
    by_cases h : e < UInt64.ofNat b.size
    · rw [ite_eq_left h]; rw [UInt64.lt_iff_toNat_lt, hsz] at h; omega
    · rw [ite_eq_right h, hsz]; rw [UInt64.lt_iff_toNat_lt, hsz] at h; omega
  unfold utf8DecodeN
  rw [hbs]
  generalize hN : (if e < UInt64.ofNat b.size then e else UInt64.ofNat b.size) = n' at hn' ⊢
  generalize hB : b.extract j.toNat (min e.toNat b.size) = B
  have hBs : B.size = min e.toNat b.size - j.toNat := by rw [← hB, ByteArray.size_extract]; omega
  have hdec : B.utf8Decode? = ByteArray.utf8Decode?.go B 0 #[] (by simp) := rfl
  by_cases hj : j.toNat < n'.toNat
  · have hl := loop_go b.data j n' B (by omega) (by omega)
      (fun t ht => by
        subst hB
        rw [ByteArray.getElem_extract]
        have := ByteArray.getElem_extract_aux ht
        simp [Array.getD, hbs, this]; rfl)
      0 #[] (Nat.zero_le _) 0 m (by simp) hO
    rw [show j + UInt64.ofNat 0 = j by simp] at hl
    rw [← hdec] at hl
    cases hs : String.fromUTF8? B with
    | none => rw [decode_none B hs] at hl; exact hl
    | some s =>
      rw [decode_some B s hs] at hl
      simp only [List.size_toArray, String.length_toList] at hl
      simpa using hl
  · have hB0 : B.size = 0 := by omega
    have hd : B.utf8Decode? = some #[] := by
      rw [hdec, ByteArray.utf8Decode?.go]; simp [hB0]
    have hjw : ¬ j < n' := by rw [UInt64.lt_iff_toNat_lt]; exact hj
    cases hs : String.fromUTF8? B with
    | none => rw [decode_none B hs] at hd; cases hd
    | some s =>
      rw [decode_some B s hs] at hd
      have hs0 : s.toList = [] := by simpa using hd
      have hl : s.length = 0 := by rw [← String.length_toList, hs0]; rfl
      simp only [hl, Nat.zero_le, ite_true, hs0, List.map_nil]
      rw [utf8LoopN, ite_eq_right hjw]
      rfl


theorem arr64_set64_same (m : Mem) (c v : Word) :
    (m.set64 OUT c v).arr64 OUT = (m.arr64 OUT).set! c.toNat v := by
  simp only [Mem.set64, Mem.arr64, Array.getD_eq_getD_getElem?, Array.set!, Array.getElem?_setIfInBounds]
  by_cases h : OUT < m.words.size <;> simp [h]

theorem writeCps_get (cs : List Word) : ∀ (m : Mem) (c : Word),
    c.toNat + cs.length ≤ (m.arr64 OUT).size → (m.arr64 OUT).size < 2 ^ 64 →
    ((writeCps m c cs).arr64 OUT).size = (m.arr64 OUT).size ∧
    (∀ p < c.toNat, ((writeCps m c cs).arr64 OUT)[p]? = (m.arr64 OUT)[p]?) ∧
    ∀ t (h : t < cs.length), ((writeCps m c cs).arr64 OUT)[c.toNat + t]? = some cs[t] := by
  induction cs with
  | nil => intro m c _ _; simp [writeCps]
  | cons v cs ih =>
    intro m c h hO
    simp only [List.length_cons] at h
    have hc1 : (c + 1).toNat = c.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    obtain ⟨ihs, ihf, ihg⟩ := ih (m.set64 OUT c v) (c + 1) (by rw [size_set64, hc1]; omega)
      (by rw [size_set64]; exact hO)
    simp only [writeCps]
    refine ⟨by rw [ihs, size_set64], fun p hp => ?_, fun t ht => ?_⟩
    · rw [ihf p (by omega), arr64_set64_same, Array.set!, Array.getElem?_setIfInBounds_ne (by omega)]
    · cases t with
      | zero =>
        rw [Nat.add_zero, ihf c.toNat (by omega), arr64_set64_same, Array.set!,
          Array.getElem?_setIfInBounds_self_of_lt (by omega)]
        rfl
      | succ t =>
        have := ihg t (by simpa using ht)
        rw [hc1, show c.toNat + 1 + t = c.toNat + (t + 1) by omega] at this
        simpa using this

theorem writeCps_take (m : Mem) (cs : List Word) (h : cs.length ≤ (m.arr64 OUT).size)
    (hO : (m.arr64 OUT).size < 2 ^ 64) :
    ((writeCps m 0 cs).arr64 OUT).toList.take cs.length = cs := by
  obtain ⟨hs, -, hg⟩ := writeCps_get cs m 0 (by simpa using h) hO
  apply List.ext_getElem?
  intro t
  by_cases ht : t < cs.length
  · rw [List.getElem?_take, ite_eq_left ht, Array.getElem?_toList]
    simpa [ht] using hg t ht
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

/-- Partial correctness of the whole program: whenever `run` returns, it returns what Lean's
`String.fromUTF8?` says about the bytes `[j, min(e, len))`, `(1, length)` with the code points in
`OUT`, or `(0, 0)` for invalid UTF-8. (The model also says `(0, 0)` when `OUT` is too small for
the code points; the L code then fails with an out-of-bounds store and does not return.) -/
theorem utf8Decode_run (b : ByteArray) (hb : b.size + 4 < 2 ^ 64) (out : Array Word)
    (hO : out.size < 2 ^ 64) (fuel : Nat) (j e : Word) (r : List Word) (m' : Mem)
    (h : run utf8Prog fuel "utf8_decode" [j, e] { bytes := #[b.data], words := #[out] } = .ok (r, m')) :
    match String.fromUTF8? (b.extract j.toNat (min e.toNat b.size)) with
    | none => r = [0, 0]
    | some s =>
      if s.length ≤ out.size then
        r = [1, UInt64.ofNat s.length] ∧
          (m'.arr64 OUT).toList.take s.length = s.toList.map (·.val.toUInt64)
      else r = [0, 0] := by
  simp only [run] at h
  cases hr : (invoke utf8Prog (exec utf8Prog fuel) "utf8_decode" [j, e]).run
      { mem := { bytes := #[b.data], words := #[out] }, loc := Locals.init [] } with
  | error x => simp [hr, Except.map] at h
  | ok rs =>
    simp only [hr, Except.map] at h
    injection h with h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    have hsp := M.of_run
      (P := fun s => s = { mem := { bytes := #[b.data], words := #[out] }, loc := Locals.init [] }) rfl hr
      (utf8Decode_spec utf8Prog rfl rfl b.data (by simpa using hb) fuel _ rfl j e)
    obtain ⟨-, hr1, hm1⟩ := hsp
    have hout : (Mem.arr64 { bytes := #[b.data], words := #[out] } OUT) = out := rfl
    have hl := utf8DecodeN_link b hb j e { bytes := #[b.data], words := #[out] } (by rw [hout]; exact hO)
    rw [hout] at hl
    revert hl
    cases String.fromUTF8? (b.extract j.toNat (min e.toNat b.size)) with
    | none => intro hl; simp only at hl ⊢; rw [hr1, hl]; rfl
    | some s =>
      intro hl
      simp only at hl ⊢
      split
      · rename_i hle
        rw [ite_eq_left hle] at hl
        rw [hr1, hm1, hl]
        refine ⟨rfl, ?_⟩
        have := writeCps_take { bytes := #[b.data], words := #[out] } (s.toList.map (·.val.toUInt64))
          (by simpa [hout, String.length_toList] using hle) (by rw [hout]; exact hO)
        simpa [String.length_toList] using this
      · rename_i hle
        rw [ite_eq_right hle] at hl
        rw [hr1, hl]; rfl

end ConAgua.Scan
