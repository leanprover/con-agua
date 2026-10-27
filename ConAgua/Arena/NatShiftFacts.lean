module

public import ConAgua.Arena.Pool
public import ConAgua.Arena.NatGrindAttr
import ConAgua.Arena.GrindAttr

@[expose] public section

/-!
# Word facts of the shifts

The word-level facts of `nat_shl` (`NatShl.lean`), apart from its program so that `NatShr` and
`NatDiv` can use them without waiting for it: the digit equation `shl_split` of one limb of a
left shift, the powers of two `sh`, and the split `shamt` of a shift amount into limbs and bits.
-/

namespace L.Arena

/-! ## Word facts -/

/-- `2^s`, as a named function: `grind`'s ring solver sees it as one atom. -/
def sh (s : Nat) : Nat := 2 ^ s

theorem shl_lo (x b : Word) (hb : b.toNat < 64) :
    (x <<< b).toNat = x.toNat * 2 ^ b.toNat % 2 ^ 64 := by
  rw [UInt64.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (a := b.toNat) hb]

theorem shl_hi (x b : Word) (hb : b.toNat < 64) :
    ((x >>> 1) >>> (63 - b)).toNat = x.toNat * 2 ^ b.toNat / 2 ^ 64 := by
  have h63 : (63 - b).toNat = 63 - b.toNat := by grind
  rw [UInt64.toNat_shiftRight, UInt64.toNat_shiftRight, h63]
  simp only [Nat.shiftRight_eq_div_pow, UInt64.toNat_one]
  rw [Nat.mod_eq_of_lt (by omega : 63 - b.toNat < 64), Nat.mod_eq_of_lt (by omega : 1 < 64)]
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  rw [show 1 + (63 - b.toNat) = 64 - b.toNat by omega]
  have : 2 ^ 64 = 2 ^ (64 - b.toNat) * 2 ^ b.toNat := by rw [← Nat.pow_add]; congr 1; omega
  rw [this, Nat.mul_comm (2 ^ (64 - b.toNat)), ← Nat.div_div_eq_div_mul,
    Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

theorem shl_split (x c b : Word) (hb : b.toNat < 64) (hc : c.toNat < 2 ^ b.toNat) :
    ((x <<< b) ||| c).toNat + ((x >>> 1) >>> (63 - b)).toNat * 2 ^ 64 =
      x.toNat * 2 ^ b.toNat + c.toNat := by
  rw [UInt64.toNat_or, shl_lo x b hb, shl_hi x b hb]
  have e : x.toNat * 2 ^ b.toNat % 2 ^ 64 = (x.toNat % 2 ^ (64 - b.toNat)) <<< b.toNat := by
    rw [Nat.shiftLeft_eq]
    have : 2 ^ 64 = 2 ^ (64 - b.toNat) * 2 ^ b.toNat := by rw [← Nat.pow_add]; congr 1; omega
    rw [this, Nat.mul_mod_mul_right]
  rw [e, ← Nat.shiftLeft_add_eq_or_of_lt hc, ← e]
  have := Nat.mod_add_div (x.toNat * 2 ^ b.toNat) (2 ^ 64)
  rw [Nat.mul_comm (x.toNat * 2 ^ b.toNat / 2 ^ 64)]
  omega

theorem shl_hi_lt (x b : Word) (hb : b.toNat < 64) :
    ((x >>> 1) >>> (63 - b)).toNat < 2 ^ b.toNat := by
  rw [shl_hi x b hb]
  apply Nat.div_lt_of_lt_mul
  have := x.toNat_lt
  have : 2 ^ 64 * 2 ^ b.toNat = 2 ^ (64 + b.toNat) := by rw [Nat.pow_add]
  calc x.toNat * 2 ^ b.toNat < 2 ^ 64 * 2 ^ b.toNat := Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos _)

/-- The digit equation of one limb of the shift, over `sh`, as `grind` uses it. -/
theorem shl_split' (x c b : Word) (hb : b.toNat < 64) (hc : c.toNat < sh b.toNat) :
    ((x <<< b) ||| c).toNat + ((x >>> 1) >>> (63 - b)).toNat * 2 ^ 64 =
      x.toNat * sh b.toNat + c.toNat := shl_split x c b hb hc
grind_pattern [arena_grind] shl_split' => (x <<< b) ||| c

theorem shl_hi_lt' (x b : Word) (hb : b.toNat < 64) :
    ((x >>> 1) >>> (63 - b)).toNat < sh b.toNat := shl_hi_lt x b hb
grind_pattern [arena_grind] shl_hi_lt' => (x >>> 1) >>> (63 - b)

theorem and63_lt (k : Word) : (k &&& 63).toNat < 64 := by
  rw [UInt64.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
grind_pattern [arena_grind] and63_lt => k &&& 63

@[arena_grind =] theorem sh_zero : sh 0 = 1 := rfl

theorem sh_pos (s : Nat) : 0 < sh s := Nat.two_pow_pos _
grind_pattern [arena_grind] sh_pos => sh s

/-- The amount `k` is `64 · (k >> 6) + (k & 63)`. -/
theorem shamt (k : Word) : 2 ^ k.toNat = sh (k &&& 63).toNat * wt (k >>> 6).toNat := by
  simp only [sh, wt, ← Nat.pow_add]
  congr 1
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight]
  simp only [Nat.shiftRight_eq_div_pow, show (63 : Word).toNat = 2 ^ 6 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, show (6 : Word).toNat % 64 = 6 from rfl]
  have := Nat.mod_add_div k.toNat (2 ^ 6)
  omega
grind_pattern [arena_grind] shamt => 2 ^ k.toNat

/-- A one-limb slice is its limb. -/
theorem pv_one (p : Array Word) (o : Nat) (h : o < p.size) : pv p o 1 = p[o].toNat := by
  simp [pv, h, wt]
grind_pattern [natop_grind] pv_one => pv p o 1, p[o]

end L.Arena
