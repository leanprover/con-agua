import ConAgua.Front.Unescape
import ConAgua.Arena.DerRel
import ConAgua.Front.FieldsLink
import ConAgua.Scan.Link
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# `str_put_esc` against con-leche's `scanString`

On a string con-leche's `scanString` reads (`StrR`), `str_put_esc` writes the string's UTF-8 bytes
to the pool, one per word (`strWords`, the name `str` table's key).

* `encW_eq`: `utf8_put`'s bytes are core's `String.utf8EncodeChar`.
* `escOneN_eq`: `esc_one` at a backslash is con-leche's escape (`escCL`, `ConAgua.Scan.StrLink`),
  whose code point is a valid `Char` (`escCL_valid`).
* `esc_main`: the induction over the body: con-leche's `unescape` with the bytes `acc` collected
  so far against the loop model with `acc` in the pool (`PoolInv`).
* `strPutEsc_link`, `strPutEsc_spec`.
-/

open L L.Arena L.Front.Unescape L.Scan.Utf8 L.Scan.Str ConLeche.Frontend ConAgua.Scan
open ConAgua.Scan.StrLink ConAgua.Front.FieldsLink
open Std.WP
open scoped Lean.Order


namespace ConAgua.Front.UnescapeLink

/-! ## UTF-8 -/

theorem and63 (x : UInt64) : (x &&& 63).toNat = x.toNat % 64 := by
  rw [UInt64.toNat_and]; simpa using Nat.and_two_pow_sub_one_eq_mod x.toNat 6
theorem shr (x : UInt64) (k : Nat) (hk : k < 64) : (x >>> (UInt64.ofNat k)).toNat = x.toNat / 2 ^ k := by
  rw [UInt64.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hk]
theorem cofn (n : Nat) (h : n.isValidChar) : (Char.ofNat n).val.toNat = n := by
  simp [Char.ofNat, h, Char.ofNatAux]
theorem u8w (m : Nat) : (UInt8.ofNat m).toUInt64.toNat = m % 256 := by simp

/-- **`utf8_put`'s bytes are the character's UTF-8.** -/
theorem encW_eq (n : Nat) (hv : n.isValidChar) :
    encW (UInt64.ofNat n) = (String.utf8EncodeChar (Char.ofNat n)).map UInt8.toUInt64 := by
  have hn : n < 0x110000 := by unfold Nat.isValidChar at hv; omega
  have hx : (UInt64.ofNat n).toNat = n := UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  have s6 := shr (UInt64.ofNat n) 6 (by decide)
  have s12 := shr (UInt64.ofNat n) 12 (by decide)
  have s18 := shr (UInt64.ofNat n) 18 (by decide)
  simp only [UInt64.reduceOfNat] at s6 s12 s18
  have c1 : UInt64.ofNat n < 128 ↔ n < 128 := by rw [UInt64.lt_iff_toNat_lt, hx]; simp
  have c2 : UInt64.ofNat n < 2048 ↔ n < 2048 := by rw [UInt64.lt_iff_toNat_lt, hx]; simp
  have c3 : UInt64.ofNat n < 65536 ↔ n < 65536 := by rw [UInt64.lt_iff_toNat_lt, hx]; simp
  have c4 : UInt64.ofNat n < 2097152 ↔ n < 2097152 := by rw [UInt64.lt_iff_toNat_lt, hx]; simp
  unfold encW String.utf8EncodeChar
  rw [cofn n hv]
  have e : ∀ (a : UInt64) (m : Nat), a.toNat = m % 256 → a = (UInt8.ofNat m).toUInt64 :=
    fun a m h => UInt64.toNat_inj.mp (by rw [h, u8w])
  by_cases h1 : n ≤ 0x7f
  · rw [ite_eq_left (c1.mpr (by omega)), ite_eq_left h1]
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    exact e _ _ (by rw [hx]; omega)
  rw [ite_eq_right (fun h => h1 (by have := c1.mp h; omega)), ite_eq_right h1]
  by_cases h2 : n ≤ 0x7ff
  · rw [ite_eq_left (c2.mpr (by omega)), ite_eq_left h2]
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    refine ⟨e _ _ ?_, e _ _ ?_⟩ <;>
      simp only [UInt64.toNat_add, and63, s6, hx] <;> simp <;> omega
  rw [ite_eq_right (fun h => h2 (by have := c2.mp h; omega)), ite_eq_right h2]
  by_cases h3 : n ≤ 0xffff
  · rw [ite_eq_left (c3.mpr (by omega)), ite_eq_left h3]
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    refine ⟨e _ _ ?_, e _ _ ?_, e _ _ ?_⟩ <;>
      simp only [UInt64.toNat_add, and63, s6, s12, hx] <;> simp <;> omega
  rw [ite_eq_right (fun h => h3 (by have := c3.mp h; omega)), ite_eq_right h3]
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
  refine ⟨e _ _ ?_, e _ _ ?_, e _ _ ?_, e _ _ ?_⟩ <;>
    simp only [UInt64.toNat_add, and63, s6, s12, s18, hx] <;> simp <;> omega

/-- `utf8Of` as words. -/
theorem utf8Of_words (v : UInt32) (hv : v.toNat.isValidChar) :
    (utf8Of v).data.toList.map UInt8.toUInt64 = encW v.toUInt64 := by
  have : v.toUInt64 = UInt64.ofNat v.toNat := by
    apply UInt64.toNat_inj.mp; simp
  rw [this, encW_eq _ hv, utf8Of_eq, List.utf8Encode_singleton]
  simp

/-! ## `esc_one` is con-leche's escape -/

/-- The model's words for con-leche's escape. -/
def escRes (s : Word) : Option (UInt32 × USize) → Word × Word × Word
  | none => (0, 0, 0)
  | some (v, j') => (1, v.toUInt64, pw s j'.toNat)

theorem pw_add7 (s : Word) (n : Nat) : pw s n + 7 = pw s (n + 7) := pw_addk s n 7
theorem pw_add8 (s : Word) (n : Nat) : pw s n + 8 = pw s (n + 8) := pw_addk s n 8
theorem pw_add9 (s : Word) (n : Nat) : pw s n + 9 = pw s (n + 9) := pw_addk s n 9
theorem pw_add12 (s : Word) (n : Nat) : pw s n + 12 = pw s (n + 12) := pw_addk s n 12

theorem cv_toNat (v v2 : UInt32) :
    ((((v &&& 1023) <<< 10) ||| (v2 &&& 1023)) + 65536 : UInt32).toNat =
      v.toNat % 1024 * 1024 + v2.toNat % 1024 + 65536 := by
  have h1 : (v &&& 1023).toNat = v.toNat % 1024 := by
    rw [UInt32.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 10
  have h2 : (v2 &&& 1023).toNat = v2.toNat % 1024 := by
    rw [UInt32.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 10
  have h3 : ((v &&& 1023) <<< 10).toNat = v.toNat % 1024 * 1024 := by
    rw [UInt32.toNat_shiftLeft, h1]; simp; omega
  have h4 : (((v &&& 1023) <<< 10) ||| (v2 &&& 1023)).toNat =
      v.toNat % 1024 * 1024 + v2.toNat % 1024 := by
    rw [UInt32.toNat_or, h3, h2]
    have := Nat.shiftLeft_add_eq_or_of_lt (i := 10) (b := v2.toNat % 1024) (by omega) (v.toNat % 1024)
    simp only [Nat.shiftLeft_eq, Nat.reducePow] at this; omega
  rw [UInt32.toNat_add, h4]; simp; omega

theorem pairCp_eq (v v2 : UInt32) :
    pairCp v.toUInt64 v2.toUInt64 = ((((v &&& 0x3FF) <<< 10) ||| (v2 &&& 0x3FF)) + 0x10000).toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt32.toNat_toUInt64, cv_toNat]
  have h1 : (v.toUInt64 &&& 1023).toNat = v.toNat % 1024 := by
    rw [UInt64.toNat_and]; simpa using Nat.and_two_pow_sub_one_eq_mod v.toNat 10
  have h2 : (v2.toUInt64 &&& 1023).toNat = v2.toNat % 1024 := by
    rw [UInt64.toNat_and]; simpa using Nat.and_two_pow_sub_one_eq_mod v2.toNat 10
  have h3 : ((v.toUInt64 &&& 1023) <<< 10).toNat = v.toNat % 1024 * 1024 := by
    rw [UInt64.toNat_shiftLeft, h1]; simp; omega
  unfold pairCp
  rw [UInt64.toNat_add, UInt64.toNat_add, h3, h2]; simp; omega

section body
variable (h64 : System.Platform.numBits = 64) (b : ByteArray) (hsize : b.size < 2 ^ 63) (s e : Word)
    (hse : s.toNat ≤ e.toNat) (he : e.toNat ≤ b.size)
include h64 hsize hse he

theorem escOneN_eq (n : Nat) (hn : n < e.toNat - s.toNat) :
    escOneN b.data e (pw s n) = escRes s (escCL (b.extract s.toNat e.toNat) (USize.ofNat n)) := by
  have hu : ∀ k, k ≤ 16 → (USize.ofNat (n + k)).toNat = n + k := fun k hk => usz h64 _ (by omega)
  unfold escOneN escSurN escCL
  simp only [uofs, pw_add1, pw_add2, pw_add6, pw_add7, pw_add8, pw_add9, pw_add12, Nat.add_assoc,
    Nat.reduceAdd,
    byteAt_eq h64 b hsize s e hse he (n + 1) (by omega),
    byteAt_eq h64 b hsize s e hse he (n + 6) (by omega),
    byteAt_eq h64 b hsize s e hse he (n + 7) (by omega),
    byteAt_eq h64 b hsize s e hse he (n + 8) (by omega),
    hex4_eq h64 b hsize s e hse he (n + 2) (by omega),
    hex3_eq h64 b hsize s e hse he (n + 9) (by omega)]
  have hu2 := hu 2 (by omega)
  have hu6 := hu 6 (by omega)
  have hu12 := hu 12 (by omega)
  have hm2 : (n + 2) % 2 ^ System.Platform.numBits = n + 2 := by rw [h64]; omega
  have hm6 : (n + 6) % 2 ^ System.Platform.numBits = n + 6 := by rw [h64]; omega
  have hm12 : (n + 12) % 2 ^ System.Platform.numBits = n + 12 := by rw [h64]; omega
  generalize byteAt (b.extract s.toNat e.toNat) (USize.ofNat (n + 1)) = d
  generalize byteAt (b.extract s.toNat e.toNat) (USize.ofNat (n + 6)) = d6
  generalize byteAt (b.extract s.toNat e.toNat) (USize.ofNat (n + 7)) = d7
  generalize byteAt (b.extract s.toNat e.toNat) (USize.ofNat (n + 8)) = d8
  generalize ConLeche.Frontend.hex4 (b.extract s.toNat e.toNat) (USize.ofNat (n + 2)) = H4
  generalize ConLeche.Frontend.hex3 (b.extract s.toNat e.toNat) (USize.ofNat (n + 9)) = H3
  simp only [u8eq, u8beq, u8bne, UInt64.reduceToNat, UInt8.reduceToNat, Bool.or_eq_true,
    decide_eq_true_eq]
  have w : ∀ (x : UInt8) (k : Nat), x.toNat = k → k < 256 → x.toUInt64 = UInt64.ofNat k :=
    fun x k h hk => UInt64.toNat_inj.mp (by simp [h]; omega)
  by_cases h1 : d.toNat = 34
  · simp [h1, escRes, hm2, w d 34 h1 (by decide)]
  by_cases h2 : d.toNat = 92
  · simp [h2, escRes, hm2, w d 92 h2 (by decide)]
  by_cases h3 : d.toNat = 47
  · simp [h3, escRes, hm2, w d 47 h3 (by decide)]
  by_cases h4 : d.toNat = 98
  · simp [h4, escRes, hm2]
  by_cases h5 : d.toNat = 102
  · simp [h5, escRes, hm2]
  by_cases h6 : d.toNat = 110
  · simp [h6, escRes, hm2]
  by_cases h7 : d.toNat = 114
  · simp [h7, escRes, hm2]
  by_cases h8 : d.toNat = 116
  · simp [h8, escRes, hm2]
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, or_self, ite_false]
  by_cases h117 : d.toNat = 117
  · have h117' : d.toUInt64 = 117 := w d 117 h117 (by decide)
    simp only [h117', h117, ne_eq, not_true_eq_false, ite_false]
    rcases H4 with _ | v
    · simp [optW, escRes]
    simp only [optW, u32lt, u32le, UInt64.reduceToNat, UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le,
      UInt32.reduceToNat]
    have h10 : ((1 : Word) = 0) = False := by decide
    simp only [h10, ite_false]
    by_cases hv1 : v.toNat < 55296 ∨ 57344 ≤ v.toNat
    · simp [hv1, escRes, hm6]
    by_cases hv2 : 56320 ≤ v.toNat
    · simp [hv1, hv2, escRes, hm6, replacementChar]
    simp only [hv1, hv2, ite_false]
    simp only [u8beq, Bool.and_eq_true, Bool.or_eq_true, UInt8.reduceToNat, and_assoc]
    by_cases hcont : d6.toNat = 92 ∧ d7.toNat = 117 ∧ (d8.toNat = 100 ∨ d8.toNat = 68)
    · obtain ⟨c1, c2, c3⟩ := hcont
      simp only [c1, c2, c3, true_and, ite_true]
      rcases H3 with _ | v2
      · simp [escRes, hm6, replacementChar]
      · by_cases hv3 : v2.toNat < 3072
        · simp [escRes, hm6, replacementChar, hv3, u32lt]
        · simp [escRes, hm12, hv3, pairCp_eq, u32lt]
    · have hn' : ∀ P : Prop, ¬ (d6.toNat = 92 ∧ d7.toNat = 117 ∧ (d8.toNat = 100 ∨ d8.toNat = 68) ∧ P) :=
        fun _ h => hcont ⟨h.1, h.2.1, h.2.2.1⟩
      simp [hn', hcont, escRes, hm6, replacementChar]
  · have h117' : ¬ d.toUInt64 = 117 := fun h => h117 (by have := (u8eq d 117).mp h; simpa using this)
    simp [h117', h117, escRes]

end body

/-! ## The code point of an escape is a `Char` -/

theorem comb4_lt (a c d e : UInt32) (ha : a.toNat < 16) (hc : c.toNat < 16) (hd : d.toNat < 16)
    (he : e.toNat < 16) : ((a <<< 12) ||| (c <<< 8) ||| (d <<< 4) ||| e).toNat < 65536 := by
  simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft]
  have s : ∀ (x : UInt32) (k : Nat), x.toNat < 16 → k ≤ 12 → x.toNat * 2 ^ k % 2 ^ 32 < 2 ^ 16 := by
    intro x k hx hk
    have : 2 ^ k ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) hk
    have : x.toNat * 2 ^ k < 2 ^ 16 := by
      calc x.toNat * 2 ^ k < 16 * 2 ^ k := Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos _)
        _ ≤ 16 * 2 ^ 12 := Nat.mul_le_mul_left _ this
        _ = 2 ^ 16 := by decide
    omega
  refine Nat.or_lt_two_pow (n := 16) (Nat.or_lt_two_pow (Nat.or_lt_two_pow ?_ ?_) ?_) (by omega)
  · have := s a 12 ha (by decide); simpa [Nat.shiftLeft_eq] using this
  · have := s c 8 hc (by decide); simpa [Nat.shiftLeft_eq] using this
  · have := s d 4 hd (by decide); simpa [Nat.shiftLeft_eq] using this

theorem hex4_lt (B : ByteArray) (j : USize) (v : UInt32) (h : ConLeche.Frontend.hex4 B j = some v) :
    v.toNat < 65536 := by
  unfold ConLeche.Frontend.hex4 at h
  cases h1 : ConLeche.Frontend.hexVal (byteAt B j) <;>
  cases h2 : ConLeche.Frontend.hexVal (byteAt B (j + 1)) <;>
  cases h3 : ConLeche.Frontend.hexVal (byteAt B (j + 1 + 1)) <;>
  cases h4 : ConLeche.Frontend.hexVal (byteAt B (j + 1 + 1 + 1)) <;>
  simp only [h1, h2, h3, h4, Option.bind_eq_bind, Option.bind_none, Option.bind_some,
    reduceCtorEq, Option.some.injEq] at h
  subst h
  exact comb4_lt _ _ _ _ (hexVal_lt' _ _ h1) (hexVal_lt' _ _ h2) (hexVal_lt' _ _ h3)
    (hexVal_lt' _ _ h4)

theorem cv_range (v v2 : UInt32) :
    65536 ≤ ((((v &&& 1023) <<< 10) ||| (v2 &&& 1023)) + 65536 : UInt32).toNat ∧
      ((((v &&& 1023) <<< 10) ||| (v2 &&& 1023)) + 65536 : UInt32).toNat < 1114112 := by
  rw [cv_toNat]; omega

/-- **An escape's code point is a valid `Char`.** -/
theorem escCL_valid (B : ByteArray) (j : USize) (v : UInt32) (j' : USize)
    (h : escCL B j = some (v, j')) : v.toNat.isValidChar := by
  unfold escCL at h
  unfold Nat.isValidChar
  generalize byteAt B (j + 1) = d at h
  generalize hH : ConLeche.Frontend.hex4 B (j + 1 + 1) = H4 at h
  generalize ConLeche.Frontend.hex3 B (j + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = H3 at h
  simp only [beq_iff_eq] at h
  by_cases h1 : d = 34
  · simp [h1] at h; obtain ⟨rfl, -⟩ := h; decide
  by_cases h2 : d = 92
  · simp [h2] at h; obtain ⟨rfl, -⟩ := h; decide
  by_cases h3 : d = 47
  · simp [h3] at h; obtain ⟨rfl, -⟩ := h; decide
  by_cases h4 : d = 98
  · simp [h4] at h; obtain ⟨rfl, -⟩ := h; decide
  by_cases h5 : d = 102
  · simp [h5] at h; obtain ⟨rfl, -⟩ := h; decide
  by_cases h6 : d = 110
  · simp [h6] at h; obtain ⟨rfl, -⟩ := h; decide
  by_cases h7 : d = 114
  · simp [h7] at h; obtain ⟨rfl, -⟩ := h; decide
  by_cases h8 : d = 116
  · simp [h8] at h; obtain ⟨rfl, -⟩ := h; decide
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, ite_false] at h
  by_cases h117 : d = 117
  · simp only [h117, bne_self_eq_false, Bool.false_eq_true, ite_false] at h
    rcases H4 with _ | w
    · simp at h
    have hw := hex4_lt B _ w hH
    simp only at h
    by_cases hv1 : w < 55296 || 57344 ≤ w
    · simp only [hv1, ite_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp only [Bool.or_eq_true, decide_eq_true_eq, UInt32.lt_iff_toNat_lt,
        UInt32.le_iff_toNat_le, UInt32.reduceToNat] at hv1
      omega
    simp only [hv1, Bool.false_eq_true, ite_false] at h
    by_cases hv2 : 56320 ≤ w
    · simp only [hv2, ite_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h; decide
    simp only [hv2, ite_false] at h
    split at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; decide
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        have := cv_range w ‹_›; omega
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; decide
  · simp [h117] at h

/-! ## What the loop has written -/

/-- `x - base(x)` is `x`'s index in its tier. -/
theorem tag_sub_base (x : Word) : x - (x >>> 40) <<< 40 = x &&& 1099511627775 := by
  apply UInt64.toNat_inj.mp; rw [tag_off_toNat, tag_idx_toNat]

/-- `utf8_put`'s base-relative index `top + k - base` is the top's index plus `k`. -/
theorem tag_rel_add (x k : Word) : x + k - (x >>> 40) <<< 40 = (x &&& 1099511627775) + k := by
  rw [← tag_sub_base]; grind

/-- The loop has written the bytes `L` at `[top, top + k)` of the virtual pool (in the top's tier,
from the top's index on), and changed nothing else of the memory `m₀` it started from. -/
def PoolInv (m₀ m : Mem) (top k : Word) (L : List UInt8) : Prop :=
  PFrame m₀ m ∧ Agree (vpool m) (vpool m₀) top.toNat ∧
  (top &&& 1099511627775).toNat + k.toNat ≤ (m.arr64 (tierA 0 (top >>> 40))).size ∧
  k.toNat = L.length ∧ sliceL (vpool m) top.toNat k.toNat = L.map UInt8.toUInt64

theorem poolInv_init (m : Mem) (hp : PoolOK m) : PoolInv m m m.top 0 [] :=
  ⟨PFrame.refl _, fun _ _ => rfl, by simpa using hp.2.2.2.2.2, rfl, by simp [sliceL]⟩

section inv
variable (m₀ : Mem) (hs : PSmall m₀) (top : Word) (ht : top.toNat < 2 ^ 41)
include hs ht

theorem poolInv_write (m : Mem) (k : Word) (L : List UInt8) (h : PoolInv m₀ m top k L)
    (hl : ¬ m.len64 (tierA 0 (top >>> 40)) ≤ (top &&& 1099511627775) + k) (x : UInt8) :
    PoolInv m₀ (m.set64 (tierA 0 (top >>> 40)) ((top &&& 1099511627775) + k) x.toUInt64) top
      (k + 1) (L ++ [x]) := by
  obtain ⟨hf, hag, hb, hk, hsl⟩ := h
  have hsz : (m.arr64 (tierA 0 (top >>> 40))).size < 2 ^ 40 := by
    rw [PFrame.tsize _ hf]; exact hs.tier _
  have hI := tag_idx_lt top
  have hsp := tag_split top
  have htr := tag_tier_le top ht
  have hlen : (m.len64 (tierA 0 (top >>> 40))).toNat = (m.arr64 (tierA 0 (top >>> 40))).size := by
    simp only [Mem.len64]; exact UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  have hIk : ((top &&& 1099511627775) + k).toNat = (top &&& 1099511627775).toNat + k.toNat := by
    rw [UInt64.toNat_add]; omega
  have hlt : (top &&& 1099511627775).toNat + k.toNat < (m.arr64 (tierA 0 (top >>> 40))).size := by
    rw [UInt64.le_iff_toNat_le, hlen, hIk] at hl; omega
  have htk : (top + k).toNat = top.toNat + k.toNat := by rw [UInt64.toNat_add]; omega
  have hk1 : (k + 1).toNat = k.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hvs : top.toNat + k.toNat < (vpool m).size := by rw [vpool_size]; omega
  have hset : vpool (m.set64 (tierA 0 (top >>> 40)) ((top &&& 1099511627775) + k) x.toUInt64) =
      (vpool m).set! (top.toNat + k.toNat) x.toUInt64 := by
    rw [vpool_stidx m top k _ ht (by rw [hIk]; exact hlt) (by omega) (by omega), htk]
  refine ⟨PFrame.set64 _ _ _ hf, fun j hj => ?_, ?_, ?_, ?_⟩
  · rw [hset, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, ite_eq_right (by omega)]
    exact hag j hj
  · rw [Mem.size_arr64_set64, hk1]; omega
  · rw [hk1, hk]; simp
  · rw [hset, hk1, sliceL, List.ext_getElem_iff]
    refine ⟨by simp [hk], fun i h1 h2 => ?_⟩
    simp only [List.length_ofFn] at h1
    simp only [List.getElem_ofFn, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds,
      List.map_append, List.map_cons, List.map_nil]
    by_cases hi : i < k.toNat
    · rw [ite_eq_right (by omega), List.getElem_append_left (by simp; omega)]
      have := List.getElem_of_eq hsl (i := i) (by simp [sliceL]; exact hi)
      simp only [sliceL, List.getElem_ofFn, List.getElem_map] at this
      rw [this]; simp
    · have hik : i = k.toNat := by omega
      subst hik
      rw [ite_eq_left (by omega), List.getElem_append_right (by simp; omega)]
      simp [hk, show top.toNat + L.length < (vpool m).size by omega]

theorem poolInv_wrs (bs : List UInt8) : ∀ (m : Mem) (k : Word) (L : List UInt8),
    PoolInv m₀ m top k L →
    (top &&& 1099511627775).toNat + k.toNat + bs.length ≤ (m.arr64 (tierA 0 (top >>> 40))).size →
    PoolInv m₀ (wrs m (top >>> 40) (top + k) ((top >>> 40) <<< 40) (bs.map UInt8.toUInt64)) top
      (k + UInt64.ofNat bs.length) (L ++ bs) := by
  induction bs with
  | nil =>
    intro m k L h _
    simp only [List.map_nil, wrs_nil, List.length_nil, List.append_nil]
    have e : k + UInt64.ofNat 0 = k := by simp
    rw [e]; exact h
  | cons x xs ih =>
    intro m k L h hb
    simp only [List.length_cons] at hb
    have hsz : (m.arr64 (tierA 0 (top >>> 40))).size < 2 ^ 40 := by
      rw [PFrame.tsize _ h.1]; exact hs.tier _
    have hI := tag_idx_lt top
    have hlen : (m.len64 (tierA 0 (top >>> 40))).toNat = (m.arr64 (tierA 0 (top >>> 40))).size := by
      simp only [Mem.len64]; exact UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
    have hIk : ((top &&& 1099511627775) + k).toNat = (top &&& 1099511627775).toNat + k.toNat := by
      rw [UInt64.toNat_add]; omega
    have hl : ¬ m.len64 (tierA 0 (top >>> 40)) ≤ (top &&& 1099511627775) + k := by
      rw [UInt64.le_iff_toNat_le, hlen, hIk]; omega
    have h1 := poolInv_write m₀ hs top ht m k L h hl x
    have hk1 : (k + 1).toNat = k.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have := ih _ (k + 1) _ h1 (by rw [Mem.size_arr64_set64, hk1]; omega)
    simp only [List.map_cons, wrs_cons, List.length_cons]
    rw [tag_rel_add, show top + k + 1 = top + (k + 1) by ac_rfl,
      show k + UInt64.ofNat (xs.length + 1) = k + 1 + UInt64.ofNat xs.length by
        rw [UInt64.ofNat_add]; simp; ac_rfl]
    simpa using this

omit hs ht in
/-- What `utf8_put` did, when it returned. -/
theorem u8PutW_eq (m : Mem) (k cp k' : Word) (m' : Mem) (h : u8PutW m top k cp = some (k', m')) :
    k' = k + UInt64.ofNat (encW cp).length ∧
      m' = wrs m (top >>> 40) (top + k) ((top >>> 40) <<< 40) (encW cp) ∧
      ¬ m.len64 (tierA 0 (top >>> 40)) ≤
        top + k + UInt64.ofNat ((encW cp).length - 1) - (top >>> 40) <<< 40 ∧
      (encW cp).length ≤ 4 := by
  unfold u8PutW at h
  by_cases c1 : cp < 128
  · rw [ite_eq_left c1] at h
    split at h
    · cases h
    · rename_i hl
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      have e : encW cp = [cp] := by simp [encW, c1]
      rw [e]; exact ⟨by simp, rfl, by simpa using hl, by simp⟩
  rw [ite_eq_right c1] at h
  by_cases c2 : cp < 2048
  · rw [ite_eq_left c2] at h
    split at h
    · cases h
    · rename_i hl
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      have e : encW cp = [(192 : Word) + (cp >>> 6), (128 : Word) + (cp &&& 63)] := by simp [encW, c1, c2]
      rw [e]; exact ⟨by simp, rfl, by simpa using hl, by simp⟩
  rw [ite_eq_right c2] at h
  by_cases c3 : cp < 65536
  · rw [ite_eq_left c3] at h
    split at h
    · cases h
    · rename_i hl
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      have e : encW cp = [(224 : Word) + (cp >>> 12), (128 : Word) + ((cp >>> 6) &&& 63), (128 : Word) + (cp &&& 63)] := by simp [encW, c1, c2, c3]
      rw [e]; exact ⟨by simp, rfl, by simpa using hl, by simp⟩
  rw [ite_eq_right c3] at h
  split at h
  · cases h
  · rename_i hl
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have e : encW cp = [(240 : Word) + (cp >>> 18), (128 : Word) + ((cp >>> 12) &&& 63),
        (128 : Word) + ((cp >>> 6) &&& 63), (128 : Word) + (cp &&& 63)] := by simp [encW, c1, c2, c3]
    rw [e]; exact ⟨by simp, rfl, by simpa using hl, by simp⟩

theorem poolInv_u8 (m : Mem) (k : Word) (L : List UInt8) (v : UInt32) (k' : Word) (m' : Mem)
    (h : PoolInv m₀ m top k L) (hv : v.toNat.isValidChar)
    (hu : u8PutW m top k v.toUInt64 = some (k', m')) :
    PoolInv m₀ m' top k' (L ++ (utf8Of v).data.toList) := by
  obtain ⟨rfl, rfl, hl, h4⟩ := u8PutW_eq top m k _ k' m' hu
  have hw := utf8Of_words v hv
  have hlen' : (encW v.toUInt64).length = (utf8Of v).data.toList.length := by
    rw [← hw, List.length_map]
  have hsz : (m.arr64 (tierA 0 (top >>> 40))).size < 2 ^ 40 := by
    rw [PFrame.tsize _ h.1]; exact hs.tier _
  have hb := h.2.2.1
  have hI := tag_idx_lt top
  have hlen : (m.len64 (tierA 0 (top >>> 40))).toNat = (m.arr64 (tierA 0 (top >>> 40))).size := by
    simp only [Mem.len64]; exact UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  have hc : (UInt64.ofNat ((encW v.toUInt64).length - 1)).toNat = (encW v.toUInt64).length - 1 :=
    UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  have htk : ((top &&& 1099511627775) + (k + UInt64.ofNat ((encW v.toUInt64).length - 1))).toNat =
      (top &&& 1099511627775).toNat + k.toNat + ((encW v.toUInt64).length - 1) := by
    rw [UInt64.toNat_add, UInt64.toNat_add, hc]; omega
  rw [UInt64.add_assoc, tag_rel_add, UInt64.le_iff_toNat_le, hlen, htk] at hl
  have hpos : 0 < (encW v.toUInt64).length := by
    unfold encW; split <;> (try split) <;> (try split) <;> simp
  rw [hlen', ← hw]
  exact poolInv_wrs m₀ hs top ht _ m k L h (by omega)

end inv

/-! ## The induction over the body -/

theorem fromUTF8?_toByteArray' (a : ByteArray) (str : String) (h : String.fromUTF8? a = some str) :
    str.toByteArray = a := by
  unfold String.fromUTF8? at h
  split at h
  · cases h; rfl
  · cases h

section main
variable (h64 : System.Platform.numBits = 64) (b : ByteArray) (hsize : b.size < 2 ^ 63) (s e : Word)
    (hse : s.toNat ≤ e.toNat) (he : e.toNat ≤ b.size) (m₀ : Mem) (hs : PSmall m₀)
    (top : Word) (ht : top.toNat < 2 ^ 41)
include h64 hsize hse he hs ht

/-- **The induction**: con-leche's `unescape` on the body from `n`, with the bytes `acc` collected
so far, against the loop model from `pw s n` with `acc` in the pool. -/
theorem esc_main (n : Nat) (L : List UInt8) (k : Word) (m : Mem) (acc : ByteArray) (str : String)
    (k' : Word) (m' : Mem) (hnL : n ≤ e.toNat - s.toNat + 12) (hL : acc.data.toList = L)
    (hI : PoolInv m₀ m top k L)
    (hU : ConLeche.Frontend.unescape (b.extract s.toNat e.toNat) (USize.ofNat n)
      (b.extract s.toNat e.toNat).usize acc = some str)
    (hM : escLoopW b.data m top e (pw s n) k = some (k', m')) :
    PoolInv m₀ m' top k' str.toByteArray.data.toList := by
  induction hd : e.toNat - s.toNat - n using Nat.strongRecOn generalizing n L k m acc with
  | _ d ih =>
  have hBs := body_size b s e he
  have hu := body_usize h64 b hsize s e hse he
  have hn' := usz h64 n (by omega)
  have hp0 := pw_toNat s n (by omega)
  by_cases hnl : n < e.toNat - s.toNat
  · have h1 : USize.ofNat n < (b.extract s.toNat e.toNat).usize :=
      USize.lt_iff_toNat_lt.mpr (by omega)
    have hcond : pw s n < e := by rw [UInt64.lt_iff_toNat_lt, hp0]; omega
    have hbw := byteW_eq h64 b hsize s e hse he n hnl (by rw [hn', hBs]; exact hnl)
    rw [uget_eq'] at hbw
    simp only [hn'] at hbw
    rw [escLoopW, dite_eq_left hcond, hbw] at hM
    by_cases hc : (b.extract s.toNat e.toNat)[n]'(by omega) = 92
    · -- an escape
      rw [unescape_esc h64 _ (by omega) n (by omega) hc acc] at hU
      have hc' : ((b.extract s.toNat e.toNat)[n]'(by omega)).toUInt64 = 92 := by rw [hc]; rfl
      rw [ite_eq_right (by simp [hc']), escOneN_eq h64 b hsize s e hse he n hnl] at hM
      cases hE : escCL (b.extract s.toNat e.toNat) (USize.ofNat n) with
      | none => rw [hE] at hU; cases hU
      | some p =>
        obtain ⟨v, j'⟩ := p
        rw [hE] at hU hM
        obtain ⟨kk, hk2, hk12, rfl⟩ := escCL_next _ n v j' hE
        have hv := escCL_valid _ _ v _ hE
        simp only [escRes, usz h64 _ (by omega : n + kk < 2 ^ 64)] at hM
        rw [ite_eq_right (by decide)] at hM
        cases hU8 : u8PutW m top k v.toUInt64 with
        | none => rw [hU8] at hM; cases hM
        | some q =>
          obtain ⟨k1, m1⟩ := q
          rw [hU8] at hM
          simp only at hM
          have hlt : ¬ pw s (n + kk) ≤ pw s n := by
            rw [UInt64.le_iff_toNat_le, hp0, pw_toNat s _ (by omega)]; omega
          rw [dite_eq_right hlt] at hM
          exact ih (e.toNat - s.toNat - (n + kk)) (by omega) (n + kk) (L ++ (utf8Of v).data.toList)
            k1 m1 (acc ++ utf8Of v) (by omega) (by rw [← hL]; simp)
            (poolInv_u8 m₀ hs top ht m k L v k1 m1 hI hv hU8) hU hM rfl
    · -- a raw byte
      have hlt1 : USize.ofNat n < USize.ofNat (n + 1) :=
        USize.lt_iff_toNat_lt.mpr (by rw [hn', usz h64 _ (by omega)]; omega)
      have hc' : ((b.extract s.toNat e.toNat).uget (USize.ofNat n) (by rw [hn']; omega) != 92) = true := by
        rw [uget_eq']; simp only [hn']; simpa using hc
      rw [ConLeche.Frontend.unescape] at hU
      simp only [h1, dite_true, ite_true, hc', uofs, hlt1] at hU
      rw [uget_eq'] at hU
      simp only [hn'] at hU
      have hne : ¬ ((b.extract s.toNat e.toNat)[n]'(by omega)).toUInt64 = 92 := by
        intro h; apply hc; rw [u8eq] at h; exact UInt8.toNat_inj.mp h
      rw [ite_eq_left hne] at hM
      split at hM
      · cases hM
      rename_i hl
      rw [pw_add1] at hM
      exact ih (e.toNat - s.toNat - (n + 1)) (by omega) (n + 1) (L ++ [(b.extract s.toNat e.toNat)[n]'(by omega)])
        (k + 1) _ _ (by omega) (by rw [← hL]; simp)
        (poolInv_write m₀ hs top ht m k L hI hl _) hU hM rfl
  · -- the end of the body
    have h1 : ¬ USize.ofNat n < (b.extract s.toNat e.toNat).usize := fun h => by
      rw [USize.lt_iff_toNat_lt] at h; omega
    rw [ConLeche.Frontend.unescape] at hU
    simp only [h1, dite_false] at hU
    have hcond : ¬ pw s n < e := by rw [UInt64.lt_iff_toNat_lt, hp0]; omega
    rw [escLoopW, dite_eq_right hcond] at hM
    simp only [Option.some.injEq, Prod.mk.injEq] at hM
    obtain ⟨rfl, rfl⟩ := hM
    rw [fromUTF8?_toByteArray' _ _ hU, hL]
    exact hI

end main

/-! ## A body without escapes -/

theorem unescape_noesc (h64 : System.Platform.numBits = 64) (B : ByteArray) (hB : B.size < 2 ^ 63)
    (n : Nat) (hnB : n ≤ B.size) (acc : ByteArray) (hno : ∀ i (hi : i < B.size), n ≤ i → B[i] ≠ 92) :
    ConLeche.Frontend.unescape B (USize.ofNat n) B.usize acc =
      String.fromUTF8? (acc ++ B.extract n B.size) := by
  induction hd : B.size - n using Nat.strongRecOn generalizing n acc with
  | _ d ih =>
  have hu := usize_toNat_eq B h64 (by omega)
  by_cases hn : n < B.size
  · have hn' := usz h64 n (by omega)
    have h1 : USize.ofNat n < B.usize := USize.lt_iff_toNat_lt.mpr (by omega)
    have hlt1 : USize.ofNat n < USize.ofNat (n + 1) :=
      USize.lt_iff_toNat_lt.mpr (by rw [hn', usz h64 _ (by omega)]; omega)
    have hc' : (B.uget (USize.ofNat n) (by rw [hn']; omega) != 92) = true := by
      rw [uget_eq']; simp only [hn']; simpa using hno n hn (Nat.le_refl _)
    rw [ConLeche.Frontend.unescape]
    simp only [h1, dite_true, ite_true, hc', uofs, hlt1]
    rw [uget_eq']
    simp only [hn']
    rw [ih (B.size - (n + 1)) (by omega) (n + 1) (by omega) _ (fun i hi h => hno i hi (by omega)) rfl,
      ByteArray.extract_eq_extract_append_extract (a := B) (i := n) (k := B.size) (n + 1) (by omega)
        (by omega), ByteArray.extract_add_one (by omega), ← ByteArray.append_assoc,
      ByteArray.append_toByteArray_singleton]
  · have h1 : ¬ USize.ofNat n < B.usize := fun h => by
      rw [USize.lt_iff_toNat_lt, hu, usz h64 n (by omega)] at h; omega
    rw [ConLeche.Frontend.unescape]
    simp only [h1, dite_false]
    rw [ByteArray.extract_eq_empty_iff.mpr (by omega), ByteArray.append_empty]

theorem hasEscape_false (h64 : System.Platform.numBits = 64) (b : ByteArray) (hsize : b.size < 2 ^ 63)
    (j e : USize) (h : hasEscape b j e = false) :
    ∀ k (hk : k < b.size), j.toNat ≤ k → k < e.toNat → b[k] ≠ 92 := by
  fun_induction hasEscape b j e with
  | case1 j hj hlt hc => simp at h
  | case2 j hj hlt hc ih =>
    intro k hk h1 h2
    have := usizeStep b j hj
    by_cases hkj : k = j.toNat
    · subst hkj
      have hc' : ¬ (b.uget j (usizeInBounds b j hj) == 92) = true := hc
      simpa [uget_eq'] using hc'
    · exact ih h k hk (by omega) h2
  | case3 j hj hlt => intro k hk h1 h2; exact absurd (USize.lt_iff_toNat_lt.mpr (by omega)) hlt
  | case4 j hj =>
    intro k hk h1 h2
    have := usizeGe b j h64 (by omega) hj
    have : b.data.size = b.size := rfl
    omega

/-! ## The link -/

/-- On a string con-leche reads, its body `[c, d)` (sliced out) unescapes to the string. -/
theorem strR_body (h64 : System.Platform.numBits = 64) (b : ByteArray) (hsize : b.size < 2 ^ 63)
    (c d : Word) (str : String) (hS : StrR b c d str) :
    c ≤ d ∧ d.toNat < b.size ∧
    ConLeche.Frontend.unescape (b.extract c.toNat d.toNat) 0 (b.extract c.toNat d.toNat).usize
      ByteArray.empty = some str := by
  obtain ⟨v, e, hc, hd, h⟩ := hS
  unfold ConLeche.Frontend.scanString at h
  split at h
  · cases h
  rename_i hq
  have hv : v < b.usize := by
    refine Classical.byContradiction fun hn => ?_
    have h0 : byteAt b v = 0 := by unfold byteAt; rw [dite_eq_right hn]
    rw [h0] at hq; exact hq (by decide)
  have hv1 : (v + 1).toNat = v.toNat + 1 := usizeStep b v hv
  have hcU : (v + 1).toUInt64 = c := by
    rw [ConAgua.Scan.RecordsLink.succ_toUInt64 h64, hc]
  have hsc := strClose_toNat_eq b h64 (by omega) (v + 1)
  dsimp only at h
  split at h
  · cases h
  rename_i hz
  have hz' : strClose b (v + 1) ≠ 0 := by simpa using hz
  have hcn : L.Examples.strCloseN b.data (v + 1).toNat ≠ 0 := by
    rw [← hsc]; intro h0; exact hz' (USize.toNat_inj.mp (by rw [h0]; rfl))
  have hbd := L.Examples.strCloseN_bounds b.data (v + 1).toNat hcn
  have hbs : b.data.size = b.size := rfl
  have hcN : c.toNat = (v + 1).toNat := by rw [← hcU, USize.toNat_toUInt64]
  have hE : e = strClose b (v + 1) + 1 → d.toNat = (strClose b (v + 1)).toNat := by
    intro he'
    rw [← hd, he', ConAgua.Scan.RecordsLink.succ_toUInt64 h64, UInt64.add_sub_cancel,
      USize.toNat_toUInt64]
  split at h
  · rename_i hesc
    split at h
    · rename_i str' hstr
      simp only [ScanRes.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hdN := hE rfl
      refine ⟨UInt64.le_iff_toNat_le.mpr (by omega), by omega, ?_⟩
      rw [hcN, hdN]; exact hstr
    · cases h
  · rename_i hesc
    split at h
    · rename_i str' hstr
      simp only [ScanRes.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hdN := hE rfl
      refine ⟨UInt64.le_iff_toNat_le.mpr (by omega), by omega, ?_⟩
      have hno := hasEscape_false h64 b hsize _ _ (by simpa using hesc)
      rw [hcN, hdN]
      have hBs : (b.extract (v + 1).toNat (strClose b (v + 1)).toNat).size =
          (strClose b (v + 1)).toNat - (v + 1).toNat := by rw [ByteArray.size_extract]; omega
      have := unescape_noesc h64 (b.extract (v + 1).toNat (strClose b (v + 1)).toNat) (by omega)
        0 (by omega) ByteArray.empty (fun i hi _ => by
          rw [ByteArray.getElem_extract]
          exact hno _ (by omega) (by omega) (by omega))
      rw [show (USize.ofNat 0) = 0 from rfl] at this
      rw [this, ByteArray.empty_append, ByteArray.extract_zero_size]
      exact hstr
    · cases h

/-- **`str_put_esc` writes the string con-leche reads**: on a string body `[c, d)` con-leche's
`scanString` reads as `str` (`StrR`), if `str_put_esc`'s model returns, the pool grew
(`Grows`) by the slice `(m.top, l)`, which holds the string's UTF-8 bytes. -/
@[refines_part ConLeche.Frontend.scanString "the body decoded into the pool"]
theorem strPutEsc_link (h64 : System.Platform.numBits = 64) (b : ByteArray)
    (hsize : b.size < 2 ^ 63) (m m' : Mem) (hpool : PoolOK m) (c d : Word) (str : String)
    (hS : StrR b c d str) (l : Word) (h : strPutEscW b.data m c d = some (l, m')) :
    Grows m m' ∧ SliceOK m' m.top l ∧ sliceL (vpool m') m.top.toNat l.toNat = strWords str := by
  obtain ⟨hcd, hdb, hU⟩ := strR_body h64 b hsize c d str hS
  have hsm := hpool.small
  have h41 := hpool.top41
  unfold strPutEscW at h
  split at h
  · cases h
  cases hL : escLoopW b.data m m.top d c 0 with
  | none => rw [hL] at h; cases h
  | some q =>
  obtain ⟨l₁, m₁⟩ := q
  rw [hL, finK_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hc0 : pw c 0 = c := by simp [pw]
  rw [← hc0] at hL
  have hI := esc_main h64 b hsize c d (UInt64.le_iff_toNat_le.mp hcd) (by omega) m hsm m.top h41 0 []
    0 m ByteArray.empty str l₁ m₁ (by omega) rfl (poolInv_init m hpool)
    (by rw [show (USize.ofNat 0) = 0 from rfl]; exact hU) hL
  obtain ⟨hf, hag, hb, -, hsl⟩ := hI
  have hg := Grows.write m m₁ l₁ hpool hf hag (by rw [← PFrame.tsize _ hf]; exact hb)
  have hctl₁ : 0 < (m₁.arr64 CTL).size := by rw [hf.ctl]; exact hpool.2.1
  have htop' := Mem.top_set64 m₁ (m.top + l₁) hctl₁
  refine ⟨hg, SliceOK.fresh hg htop', ?_⟩
  rw [vpool_set64_ne _ _ _ _ (by decide), hsl, strWords]

/-- The pool growing keeps `DerR` (it reads none of the pool). -/
theorem DerR.grow (m m' : Mem) (hg : Grows m m') (a : ConRon.Arena.AState) (hD : DerR m a) : DerR m' a :=
  DerR.frameM _ _ m m' (grows_frame m m' hg) (by simp [POOL, POOL1]) a hD

/-- **`str_put_esc(c, d)` on a string con-leche reads**: the pool grows by the string's UTF-8
bytes, one per word, at the old top; `ArenaR` and `DerR` are kept. -/
theorem strPutEsc_spec (p : Prog) (hpb : p.lookup "byte_in" = some L.Scan.Str.byteIn)
    (hph : p.lookup "hex_val" = some L.Scan.Str.hexVal) (hp4 : p.lookup "hex4" = some L.Scan.Str.hex4)
    (hp3 : p.lookup "hex3" = some L.Scan.Str.hex3) (hps : p.lookup "esc_sur" = some escSur)
    (hpo : p.lookup "esc_one" = some escOne) (hpu : p.lookup "utf8_put" = some utf8Put)
    (hpe : p.lookup "str_put_esc" = some strPutEsc)
    (h64 : System.Platform.numBits = 64) (b : ByteArray) (hsize : b.size < 2 ^ 63) (n : Nat)
    (s₀ : St) (hm : s₀.mem.arr8 L.Front.Unescape.IN = b.data) (a₀ : ConRon.Arena.AState) (hR : ArenaR s₀.mem a₀)
    (c d : Word) (str : String) (hS : StrR b c d str) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "str_put_esc" [c, d]
    ⦃fun r s' => LocEq s' s₀ ∧ r.headD 0 = s₀.mem.top ∧ Grows s₀.mem s'.mem ∧
      SliceOK s'.mem s₀.mem.top (r.tail.headD 0) ∧
      sliceL (vpool s'.mem) s₀.mem.top.toNat (r.tail.headD 0).toNat = strWords str ∧
      ArenaR s'.mem a₀ ∧ (DerR s₀.mem a₀ → DerR s'.mem a₀); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hr, hW⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (strPutEsc_specW p b.data hsize hpb hph hp4 hp3 hps hpo hpu hpe n s₀ hm c d)
  subst hs
  obtain ⟨hg, hsl, hk⟩ := strPutEsc_link h64 b hsize s.mem s'.mem hR.lit.1 c d str hS _ hW
  exact ⟨hloc, hr, hg, hsl, hk, ArenaR.grow _ _ hg _ hR, DerR.grow _ _ hg _⟩

end ConAgua.Front.UnescapeLink

/-- info: 'ConAgua.Front.UnescapeLink.strPutEsc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConAgua.Front.UnescapeLink.strPutEsc_spec
