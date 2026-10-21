module

public import ConAgua.Arena.Pool

@[expose] public section

/-!
# Word arithmetic for the limb pool: high words of products and sums

Pure Lean facts about `UInt64` that the multiply loop needs, each as an equation over a named
function (`mulHiN`, `macHiN`, `adcHi`) with a `grind` pattern, so that the ring solver sees the
digit equation `low + high · 2^64 = …` directly.
-/

namespace L.Arena

/-! ## The high word of a product -/

theorem mulHi_key (a b c d : Nat) :
    ((b*2^32+a) * (d*2^32+c)) / 2^64 =
      b*d + (a*d)/2^32 + (b*c)/2^32 + ((a*c)/2^32 + (a*d)%2^32 + (b*c)%2^32)/2^32 := by
  have hP : (b*2^32+a) * (d*2^32+c) = (b*d)*2^64 + (a*d + b*c)*2^32 + a*c := by grind
  rw [hP]
  generalize b*d = H
  generalize a*d = M1
  generalize b*c = M2
  generalize a*c = L
  omega

/-- What L's `mul_hi` computes: the high word of `x * y` from four 32×32-bit products. -/
def mulHiW (x y : UInt64) : UInt64 :=
  ((((x >>> (32 : UInt64)) * (y >>> (32 : UInt64))) + (((x &&& (0xFFFFFFFF : UInt64)) * (y >>> (32 : UInt64))) >>> (32 : UInt64))) +
    (((x >>> (32 : UInt64)) * (y &&& (0xFFFFFFFF : UInt64))) >>> (32 : UInt64))) +
    (((((x &&& (0xFFFFFFFF : UInt64)) * (y &&& (0xFFFFFFFF : UInt64))) >>> (32 : UInt64)) +
      (((x &&& (0xFFFFFFFF : UInt64)) * (y >>> (32 : UInt64))) &&& (0xFFFFFFFF : UInt64)) +
      (((x >>> (32 : UInt64)) * (y &&& (0xFFFFFFFF : UInt64))) &&& (0xFFFFFFFF : UInt64))) >>> (32 : UInt64))

theorem lo32 (x : UInt64) : (x &&& 0xFFFFFFFF).toNat = x.toNat % 2^32 := by
  rw [UInt64.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 32
theorem hi32 (x : UInt64) : (x >>> 32).toNat = x.toNat / 2^32 := by
  simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
theorem mul32 (x y : UInt64) (hx : x.toNat < 2^32) (hy : y.toNat < 2^32) :
    (x * y).toNat = x.toNat * y.toNat := by
  rw [UInt64.toNat_mul]; apply Nat.mod_eq_of_lt
  exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le hx (Nat.le_of_lt hy) (by omega)) (by decide)

theorem mulHiW_toNat (x y : UInt64) : (mulHiW x y).toNat = x.toNat * y.toNat / 2^64 := by
  have hk := mulHi_key (x.toNat % 2^32) (x.toNat / 2^32) (y.toNat % 2^32) (y.toNat / 2^32)
  rw [show x.toNat / 2^32 * 2^32 + x.toNat % 2^32 = x.toNat by omega,
      show y.toNat / 2^32 * 2^32 + y.toNat % 2^32 = y.toNat by omega] at hk
  have hxb := x.toNat_lt; have hyb := y.toNat_lt
  have bnd : x.toNat * y.toNat / 2^64 < 2^64 := by
    apply Nat.div_lt_of_lt_mul
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le hxb (Nat.le_of_lt hyb) (by omega)) (by decide)
  have t1 := mul32 (x >>> 32) (y >>> 32) (by rw [hi32]; omega) (by rw [hi32]; omega)
  have t2 := mul32 (x &&& (0xFFFFFFFF : UInt64)) (y >>> 32) (by rw [lo32]; omega) (by rw [hi32]; omega)
  have t3 := mul32 (x >>> 32) (y &&& (0xFFFFFFFF : UInt64)) (by rw [hi32]; omega) (by rw [lo32]; omega)
  have t4 := mul32 (x &&& (0xFFFFFFFF : UInt64)) (y &&& (0xFFFFFFFF : UInt64)) (by rw [lo32]; omega) (by rw [lo32]; omega)
  have b1 := ((x >>> 32) * (y >>> 32)).toNat_lt
  have b2 := ((x &&& (0xFFFFFFFF : UInt64)) * (y >>> 32)).toNat_lt
  have b3 := ((x >>> 32) * (y &&& (0xFFFFFFFF : UInt64))).toNat_lt
  have b4 := ((x &&& (0xFFFFFFFF : UInt64)) * (y &&& (0xFFFFFFFF : UInt64))).toNat_lt
  simp only [hi32, lo32] at t1 t2 t3 t4
  rw [t1] at b1; rw [t2] at b2; rw [t3] at b3; rw [t4] at b4
  simp only [mulHiW, UInt64.toNat_add, lo32, hi32, t1, t2, t3, t4]
  generalize x.toNat / 2^32 * (y.toNat / 2^32) = H at *
  generalize x.toNat % 2^32 * (y.toNat / 2^32) = M1 at *
  generalize x.toNat / 2^32 * (y.toNat % 2^32) = M2 at *
  generalize x.toNat % 2^32 * (y.toNat % 2^32) = L at *
  generalize x.toNat * y.toNat = P at *
  omega

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

theorem mulHiW_eq (x y : Word) : (mulHiW x y).toNat = mulHiN x y := mulHiW_toNat x y
grind_pattern [arena_grind] mulHiW_eq => mulHiW x y

/-- The high word of `x * y + t + c`, as a number. -/
def macHiN (x y t c : Word) : Nat := (x.toNat * y.toNat + t.toNat + c.toNat) / 2 ^ 64

theorem mac_split (x y t c : Word) :
    (x * y + t + c).toNat + macHiN x y t c * 2 ^ 64 = x.toNat * y.toNat + t.toNat + c.toNat := by
  have := mulHiN_le x y
  simp only [macHiN, UInt64.toNat_add, UInt64.toNat_mul]; omega
grind_pattern [arena_grind] mac_split => macHiN x y t c

theorem adc_split0 (x y : Word) : (x + y).toNat + adcHi x y 0 * 2 ^ 64 = x.toNat + y.toNat := by
  simp only [adcHi, UInt64.toNat_add]; simp; omega
grind_pattern [arena_grind] adc_split0 => adcHi x y 0

end L.Arena
