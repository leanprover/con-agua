module

public import ConAgua.Arena.NatBits
public import ConAgua.Arena.NatShr
@[expose] public section

/-!
# The limb-wise bitwise ops are `Nat.land`/`Nat.lor`/`Nat.xor`

`nat_land`/`nat_lor`/`nat_xor` (`NatBits.lean`) are proved against `bv f`, the limb-wise combine
of the two slices. This file shows that `bv` is the `Nat` operation: splitting a number into
base-`2^64` digits commutes with a bitwise operation `op` (bit `i` of `op x y` is
`g (bit i of x) (bit i of y)`, `g false false = false`; `bitwise_split`, by `Nat.testBit`), so by
induction over the limbs (`bv_bitwise`) `op a b = bv f … k + wt k · op (a / wt k) (b / wt k)`, and
the high parts vanish at the loop's length (`land_bv`, `lor_bv`, `xor_bv`). The operation is a
parameter characterised by its bits, not `Nat.bitwise g`: in a `module`, `Nat.land`'s body is not
visible, only its `testBit` lemmas.
-/

namespace L.Arena

/-- A bitwise operation, given by what it does to each bit. -/
structure BitOp (op : Nat → Nat → Nat) (g : Bool → Bool → Bool) : Prop where
  ff : g false false = false
  bit : ∀ x y i, (op x y).testBit i = g (x.testBit i) (y.testBit i)

theorem BitOp.lt {op : Nat → Nat → Nat} {g : Bool → Bool → Bool} (h : BitOp op g) (x y n : Nat)
    (hx : x < 2 ^ n) (hy : y < 2 ^ n) : op x y < 2 ^ n := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [h.bit, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hi)),
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) hi)), h.ff]

theorem bitOp_and : BitOp (· &&& ·) and := ⟨rfl, Nat.testBit_and⟩
theorem bitOp_or : BitOp (· ||| ·) or := ⟨rfl, Nat.testBit_or⟩
theorem bitOp_xor : BitOp (· ^^^ ·) bne := ⟨rfl, Nat.testBit_xor⟩

theorem bitwise_split {op : Nat → Nat → Nat} {g : Bool → Bool → Bool} (h : BitOp op g)
    (x y X Y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    op (x + 2 ^ 64 * X) (y + 2 ^ 64 * Y) = op x y + 2 ^ 64 * op X Y := by
  have hb : op x y < 2 ^ 64 := h.lt x y 64 hx hy
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.add_comm (op x y), Nat.testBit_two_pow_mul_add _ hb, h.bit, Nat.add_comm x,
    Nat.add_comm y, Nat.testBit_two_pow_mul_add _ hx, Nat.testBit_two_pow_mul_add _ hy]
  split
  · rw [h.bit]
  · rw [h.bit]

theorem andF_toNat (a b : Word) : (andF a b).toNat = a.toNat &&& b.toNat := by
  simp [andF, UInt64.toNat_and]
theorem orF_toNat (a b : Word) : (orF a b).toNat = a.toNat ||| b.toNat := by
  simp [orF, UInt64.toNat_or]
theorem xorF_toNat (a b : Word) : (xorF a b).toNat = a.toNat ^^^ b.toNat := by
  simp [xorF, UInt64.toNat_xor]

theorem bv_bitwise (f : Word → Word → Word) {op : Nat → Nat → Nat} {g : Bool → Bool → Bool}
    (h : BitOp op g) (hf : ∀ a b, (f a b).toNat = op a.toNat b.toNat) (p : Array Word)
    (oa la ob lb : Nat) :
    ∀ k X Y, op (xv p oa la k + wt k * X) (xv p ob lb k + wt k * Y) =
      bv f p oa la ob lb k + wt k * op X Y := by
  intro k
  induction k with
  | zero =>
    intro X Y
    simp only [xv, bv, wt, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
  | succ k ih =>
    intro X Y
    have hw : wt (k + 1) = wt k * 2 ^ 64 := wt_succ k _ rfl
    have ha : lv p oa la k < 2 ^ 64 := by rw [← lvW_toNat]; exact UInt64.toNat_lt _
    have hb : lv p ob lb k < 2 ^ 64 := by rw [← lvW_toNat]; exact UInt64.toNat_lt _
    have e1 : xv p oa la (k + 1) + wt (k + 1) * X = xv p oa la k + wt k * (lv p oa la k + 2 ^ 64 * X) := by
      simp only [xv, hw]; grind
    have e2 : xv p ob lb (k + 1) + wt (k + 1) * Y = xv p ob lb k + wt k * (lv p ob lb k + 2 ^ 64 * Y) := by
      simp only [xv, hw]; grind
    rw [e1, e2, ih, bitwise_split h _ _ _ _ ha hb, ← lvW_toNat, ← lvW_toNat, ← hf]
    simp only [bv, hw]; grind

theorem xv_pv (p : Array Word) (o l k : Nat) (h : k ≤ l) : xv p o l k = pv p o k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [xv, pv, ih (by omega), lv, show k < l by omega, ite_true]

/-- A slice is its first `k` limbs (zero-extended) and the rest. -/
theorem pv_split_xv (p : Array Word) (o l k : Nat) :
    pv p o l = xv p o l k + wt k * pv p (o + k) (l - k) := by
  by_cases h : k ≤ l
  · rw [xv_pv p o l k h]
    have := pv_append p o k (l - k)
    rwa [show k + (l - k) = l by omega] at this
  · rw [xv_full p o l k (by omega), show l - k = 0 by omega]; simp [pv]

theorem bitwise_bv (f : Word → Word → Word) {op : Nat → Nat → Nat} {g : Bool → Bool → Bool}
    (h : BitOp op g) (hf : ∀ a b, (f a b).toNat = op a.toNat b.toNat) (p : Array Word)
    (oa la ob lb k : Nat) (hk : op (pv p (oa + k) (la - k)) (pv p (ob + k) (lb - k)) = 0) :
    op (pv p oa la) (pv p ob lb) = bv f p oa la ob lb k := by
  rw [pv_split_xv p oa la k, pv_split_xv p ob lb k, bv_bitwise f h hf, hk, Nat.mul_zero,
    Nat.add_zero]

/-- `Nat.land` of two slices is the limb-wise `&` over the shorter length. -/
theorem land_bv (p : Array Word) (oa la ob lb : Nat) :
    Nat.land (pv p oa la) (pv p ob lb) =
      bv andF p oa la ob lb (if lb < la then lb else la) := by
  rw [Nat.land_eq]
  apply bitwise_bv andF (op := (· &&& ·)) bitOp_and andF_toNat
  split
  · rw [show lb - lb = 0 by omega]; simp [pv]
  · rw [show la - la = 0 by omega]; simp [pv]

theorem lor_bv (p : Array Word) (oa la ob lb : Nat) :
    Nat.lor (pv p oa la) (pv p ob lb) =
      bv orF p oa la ob lb (if la < lb then lb else la) := by
  rw [Nat.lor_eq]
  apply bitwise_bv orF (op := (· ||| ·)) bitOp_or orF_toNat
  split
  · rw [show la - lb = 0 by omega, show lb - lb = 0 by omega]; simp [pv]
  · rw [show la - la = 0 by omega, show lb - la = 0 by omega]; simp [pv]

theorem xor_bv (p : Array Word) (oa la ob lb : Nat) :
    Nat.xor (pv p oa la) (pv p ob lb) =
      bv xorF p oa la ob lb (if la < lb then lb else la) := by
  rw [Nat.xor_eq]
  apply bitwise_bv xorF (op := (· ^^^ ·)) bitOp_xor xorF_toNat
  split
  · rw [show la - lb = 0 by omega, show lb - lb = 0 by omega]; simp [pv]
  · rw [show la - la = 0 by omega, show lb - la = 0 by omega]; simp [pv]

end L.Arena
