module

public import ConAgua.L.Semantics

@[expose] public section

/-!
# `read_nat`'s eight-digit step (SWAR)

`read_nat` converts up to eight ASCII digits with one 8-byte load and three multiply-shift-mask
steps (`swar8`) instead of one byte per step. This file proves the arithmetic, over `Nat` and with
`omega`, one byte lane at a time:

* `swar8_toNat`: if the bytes of `x` (little-endian) are the digit values `x₀, …, x₇ ≤ 9`, then
  `swar8 x` is `x₀·10⁷ + … + x₇`. Each multiplication adds a lane to its neighbour scaled by
  `10`, `100`, `10⁴`; no lane overflows (`10·9 + 9 < 2⁸`, `100·99 + 99 < 2¹⁶`), so the shifted
  product is the next level's lanes (`mul_shr`) and the mask keeps every other lane (`w8_and`).
* `w1_digits`: the word of the 8 bytes ending at `e` (`le64`), masked to the low nibbles of its top
  `L` bytes, converts to `dval`, the value of those `L` digits.
-/

namespace L.Front.Fields

/-- The value of the `n` decimal digits at `b[s], …, b[s + n - 1]`. -/
def dval (b : Array UInt8) (s : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (b[s]!.toNat - 48) * 10 ^ n + dval b (s + 1) n

theorem dval_add (b : Array UInt8) (m n : Nat) :
    ∀ s, dval b s (m + n) = dval b s m * 10 ^ n + dval b (s + m) n := by
  induction m with
  | zero => intro s; simp [dval]
  | succ m ih =>
    intro s
    rw [show m + 1 + n = (m + n) + 1 by omega, dval, dval, ih (s + 1), Nat.pow_add,
      show s + 1 + m = s + (m + 1) by omega]
    simp only [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

/-- The little-endian word of the bytes `x₀, …, x₇`. -/
def w8 (x0 x1 x2 x3 x4 x5 x6 x7 : Nat) : Nat :=
  x0 + 256 * (x1 + 256 * (x2 + 256 * (x3 + 256 * (x4 + 256 * (x5 + 256 * (x6 + 256 * x7))))))

theorem le64_toNat (b : Array UInt8) (n : Nat) :
    (le64 b n).toNat = w8 b[n]!.toNat b[n+1]!.toNat b[n+2]!.toNat b[n+3]!.toNat b[n+4]!.toNat
      b[n+5]!.toNat b[n+6]!.toNat b[n+7]!.toNat := by
  unfold le64 w8
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, List.foldr_append, List.foldr_cons, List.foldr_nil, Nat.add_zero, UInt64.toNat_ofNat']
  have := (b[n]!).toNat_lt; have := (b[n+1]!).toNat_lt; have := (b[n+2]!).toNat_lt
  have := (b[n+3]!).toNat_lt; have := (b[n+4]!).toNat_lt; have := (b[n+5]!).toNat_lt
  have := (b[n+6]!).toNat_lt; have := (b[n+7]!).toNat_lt
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem and_lane (k a c x y : Nat) (ha : a < 2 ^ k) (hc : c < 2 ^ k) :
    (a + 2 ^ k * x) &&& (c + 2 ^ k * y) = (a &&& c) + 2 ^ k * (x &&& y) := by
  have h := Nat.div_add_mod ((a + 2 ^ k * x) &&& (c + 2 ^ k * y)) (2 ^ k)
  have hk : 0 < 2 ^ k := Nat.two_pow_pos k
  rw [Nat.and_div_two_pow, Nat.and_mod_two_pow] at h
  have e1 : (a + 2 ^ k * x) / 2 ^ k = x := by
    rw [Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt ha, Nat.zero_add]
  have e2 : (c + 2 ^ k * y) / 2 ^ k = y := by
    rw [Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt hc, Nat.zero_add]
  have e3 : (a + 2 ^ k * x) % 2 ^ k = a := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  have e4 : (c + 2 ^ k * y) % 2 ^ k = c := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
  rw [e1, e2, e3, e4] at h
  rw [← h, Nat.mul_comm, Nat.add_comm]

theorem and_byte (a c x y : Nat) (ha : a < 256) (hc : c < 256) :
    (a + 256 * x) &&& (c + 256 * y) = (a &&& c) + 256 * (x &&& y) := and_lane 8 a c x y ha hc
theorem and_half (a c x y : Nat) (ha : a < 65536) (hc : c < 65536) :
    (a + 65536 * x) &&& (c + 65536 * y) = (a &&& c) + 65536 * (x &&& y) := and_lane 16 a c x y ha hc

theorem mul_shr (P lo R hi k : Nat) (hP : P = lo + 2 ^ k * R + 2 ^ 64 * hi) (hlo : lo < 2 ^ k)
    (hb : lo + 2 ^ k * R < 2 ^ 64) : P % 2 ^ 64 / 2 ^ k = R := by
  rw [hP, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb, Nat.add_mul_div_left _ _ (Nat.two_pow_pos k),
    Nat.div_eq_of_lt hlo, Nat.zero_add]

theorem and_self_lt (a k : Nat) (h : a < 2 ^ k) : a &&& (2 ^ k - 1) = a :=
  Nat.and_two_pow_sub_one_of_lt_two_pow h

/-- The SWAR conversion of eight digit values (byte `k` the digit of weight `10^(7-k)`). -/
def swar8 (x : UInt64) : UInt64 :=
  (((((((x * 2561) >>> 8) &&& 0x00FF00FF00FF00FF) * 6553601) >>> 16) &&& 0x0000FFFF0000FFFF)
    * 42949672960001) >>> 32

theorem swar8_toNat (x : UInt64) (x0 x1 x2 x3 x4 x5 x6 x7 : Nat)
    (hx : x.toNat = w8 x0 x1 x2 x3 x4 x5 x6 x7) (h0 : x0 ≤ 9) (h1 : x1 ≤ 9) (h2 : x2 ≤ 9)
    (h3 : x3 ≤ 9) (h4 : x4 ≤ 9) (h5 : x5 ≤ 9) (h6 : x6 ≤ 9) (h7 : x7 ≤ 9) :
    (swar8 x).toNat = x0 * 10000000 + x1 * 1000000 + x2 * 100000 + x3 * 10000 + x4 * 1000 +
      x5 * 100 + x6 * 10 + x7 := by
  unfold swar8
  simp only [UInt64.toNat_shiftRight, UInt64.toNat_and, UInt64.toNat_mul, hx, UInt64.reduceToNat,
    Nat.reduceMod, Nat.shiftRight_eq_div_pow]
  -- step 1
  rw [mul_shr _ x0 (w8 (10 * x0 + x1) (10 * x1 + x2) (10 * x2 + x3) (10 * x3 + x4) (10 * x4 + x5)
      (10 * x5 + x6) (10 * x6 + x7) 0) (10 * x7) 8 (by unfold w8; omega) (by omega) (by unfold w8; omega)]
  -- mask 1
  rw [show (71777214294589695 : Nat) = w8 255 0 255 0 255 0 255 0 from rfl]
  unfold w8
  simp (disch := omega) only [and_byte]
  simp only [Nat.and_zero, Nat.mul_zero, Nat.add_zero,
    and_self_lt _ 8 (show 10 * x0 + x1 < 2 ^ 8 by omega), and_self_lt _ 8 (show 10 * x2 + x3 < 2 ^ 8 by omega),
    and_self_lt _ 8 (show 10 * x4 + x5 < 2 ^ 8 by omega), and_self_lt _ 8 (show 10 * x6 + x7 < 2 ^ 8 by omega)]
  -- step 2
  rw [mul_shr _ (10 * x0 + x1) ((100 * (10 * x0 + x1) + (10 * x2 + x3)) + 65536 * ((100 * (10 * x2 + x3) + (10 * x4 + x5))
      + 65536 * ((100 * (10 * x4 + x5) + (10 * x6 + x7)) + 65536 * 0))) (100 * (10 * x6 + x7)) 16
      (by omega) (by omega) (by omega)]
  -- mask 2
  rw [show (281470681808895 : Nat) = 65535 + 65536 * (0 + 65536 * (65535 + 65536 * 0)) from rfl]
  simp (disch := omega) only [and_half]
  simp only [Nat.and_zero, Nat.mul_zero, Nat.add_zero,
    and_self_lt _ 16 (show 100 * (10 * x0 + x1) + (10 * x2 + x3) < 2 ^ 16 by omega),
    and_self_lt _ 16 (show 100 * (10 * x4 + x5) + (10 * x6 + x7) < 2 ^ 16 by omega)]
  -- step 3
  rw [mul_shr _ (100 * (10 * x0 + x1) + (10 * x2 + x3))
      (10000 * (100 * (10 * x0 + x1) + (10 * x2 + x3)) + (100 * (10 * x4 + x5) + (10 * x6 + x7)))
      (10000 * (100 * (10 * x4 + x5) + (10 * x6 + x7))) 32 (by omega) (by omega) (by omega)]
  omega

theorem w8_split (M : Nat) (h : M < 2 ^ 64) :
    M = w8 (M % 256) (M / 2 ^ 8 % 256) (M / 2 ^ 16 % 256) (M / 2 ^ 24 % 256) (M / 2 ^ 32 % 256)
      (M / 2 ^ 40 % 256) (M / 2 ^ 48 % 256) (M / 2 ^ 56 % 256) := by
  unfold w8; omega

theorem w8_and (a0 a1 a2 a3 a4 a5 a6 a7 c0 c1 c2 c3 c4 c5 c6 c7 : Nat) (ha0 : a0 < 256)
    (ha1 : a1 < 256) (ha2 : a2 < 256) (ha3 : a3 < 256) (ha4 : a4 < 256) (ha5 : a5 < 256)
    (ha6 : a6 < 256) (hc0 : c0 < 256) (hc1 : c1 < 256) (hc2 : c2 < 256) (hc3 : c3 < 256)
    (hc4 : c4 < 256) (hc5 : c5 < 256) (hc6 : c6 < 256) :
    w8 a0 a1 a2 a3 a4 a5 a6 a7 &&& w8 c0 c1 c2 c3 c4 c5 c6 c7 =
      w8 (a0 &&& c0) (a1 &&& c1) (a2 &&& c2) (a3 &&& c3) (a4 &&& c4) (a5 &&& c5) (a6 &&& c6) (a7 &&& c7) := by
  unfold w8
  rw [and_byte _ _ _ _ ha0 hc0, and_byte _ _ _ _ ha1 hc1, and_byte _ _ _ _ ha2 hc2, and_byte _ _ _ _ ha3 hc3,
    and_byte _ _ _ _ ha4 hc4, and_byte _ _ _ _ ha5 hc5, and_byte _ _ _ _ ha6 hc6]

theorem dig_and (c : Nat) (h1 : 48 ≤ c) (h2 : c ≤ 57) : c &&& 15 = c - 48 := by
  rw [show (15 : Nat) = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega

theorem w1_digits (b : Array UInt8) (n0 L : Nat) (hL1 : 1 ≤ L) (hL : L ≤ 8)
    (hd : ∀ k, 8 - L ≤ k → k < 8 → 48 ≤ b[n0 + k]!.toNat ∧ b[n0 + k]!.toNat ≤ 57) :
    swar8 (le64 b n0 &&& ((0x0F0F0F0F0F0F0F0F : UInt64) <<< ((7 - UInt64.ofNat (L - 1)) <<< 3))) =
      UInt64.ofNat (dval b (n0 + (8 - L)) L) := by
  have := (b[n0]!).toNat_lt; have := (b[n0+1]!).toNat_lt; have := (b[n0+2]!).toNat_lt
  have := (b[n0+3]!).toNat_lt; have := (b[n0+4]!).toNat_lt; have := (b[n0+5]!).toNat_lt
  have := (b[n0+6]!).toNat_lt; have := (b[n0+7]!).toNat_lt
  have d0 := hd 0; have d1 := hd 1; have d2 := hd 2; have d3 := hd 3
  have d4 := hd 4; have d5 := hd 5; have d6 := hd 6; have d7 := hd 7
  simp only [Nat.add_zero] at d0
  apply UInt64.toNat_inj.mp
  obtain ⟨X, hX0⟩ : ∃ X, (le64 b n0 &&& ((0x0F0F0F0F0F0F0F0F : UInt64) <<< ((7 - UInt64.ofNat (L - 1)) <<< 3))).toNat = X := ⟨_, rfl⟩
  rcases (by omega : L = 1 ∨ L = 2 ∨ L = 3 ∨ L = 4 ∨ L = 5 ∨ L = 6 ∨ L = 7 ∨ L = 8) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceLT, forall_const, false_implies]
      at d0 d1 d2 d3 d4 d5 d6 d7
    have hX1 := hX0
    rw [UInt64.toNat_and, le64_toNat, w8_split (UInt64.toNat _) (UInt64.toNat_lt _)] at hX1
    simp only [Nat.reduceSub, UInt64.reduceOfNat, UInt64.reduceSub, UInt64.reduceShiftLeft, UInt64.reduceToNat,
      Nat.reduceDiv, Nat.reduceMod, Nat.reducePow] at hX1
    rw [w8_and _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)] at hX1
    simp (disch := omega) only [dig_and, Nat.and_zero] at hX1
    rw [swar8_toNat _ _ _ _ _ _ _ _ _ (hX0.trans hX1.symm) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)]
    simp only [dval, UInt64.toNat_ofNat', Nat.add_assoc, Nat.reduceAdd, Nat.reduceSub, Nat.reducePow, Nat.add_zero]
    omega

end L.Front.Fields
