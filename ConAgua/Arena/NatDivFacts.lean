module

public import ConAgua.Arena.NatShiftFacts
public import ConAgua.Arena.Word

@[expose] public section

/-!
# The arithmetic of the limb-wise long division (lane `bigdiv`)

Pure `Nat` and word facts of `nat_divmod` (`NatDiv.lean`), apart from its program:

* `top2_div`: the top two words of a number shifted left by `s ≤ 63` bits, read from its top two
  limbs (`(w1 << s) + (w0 >> (64 - s))`), are the shifted number divided by the weight below them;
* `knuth_est`: con-ron's `knuth_estimate`: the estimate `⌊U / D⌋` from those top words is at least
  the true quotient digit;
* `mul_split`, `submul_step`: the word pair of a product (`mulhi`), and the digit equation of one
  limb of `div_submul`.
-/

namespace L.Arena

/-- `2^s` divides `2^64` for `s ≤ 63`, so the low word of `v · 2^s` leaves room for `2^s`. -/
theorem mod_shift_room (v s : Nat) (hs : s ≤ 63) : v * sh s % 2 ^ 64 + sh s ≤ 2 ^ 64 := by
  have hB : (2 : Nat) ^ 64 = sh s * 2 ^ (64 - s) := by
    simp only [sh, ← Nat.pow_add]; congr 1; omega
  rw [hB, Nat.mul_comm v, Nat.mul_mod_mul_left]
  have : v % 2 ^ (64 - s) < 2 ^ (64 - s) := Nat.mod_lt _ (Nat.two_pow_pos _)
  generalize v % 2 ^ (64 - s) = t at *
  generalize 2 ^ (64 - s) = M at *
  have : sh s * t + sh s = sh s * (t + 1) := by grind
  rw [this]; exact Nat.mul_le_mul_left _ (by omega)

/-- The top two words of `V · 2^s`, `V = L + wt k · (v0 + 2^64 · v1)` with `L < wt k`: the part of
`L` that the shift moves past `wt k` stays below the room the low word leaves. -/
theorem top2_div (L v0 v1 k s : Nat) (hL : L < wt k) (hs : s ≤ 63) :
    (L + wt k * (v0 + 2 ^ 64 * v1)) * sh s / wt (k + 1) = v1 * sh s + v0 * sh s / 2 ^ 64 := by
  have hw : wt (k + 1) = wt k * 2 ^ 64 := wt_succ k (k + 1) rfl
  have hwk : 0 < wt k := Nat.two_pow_pos _
  have hs0 : 0 < sh s := Nat.two_pow_pos _
  have hr := mod_shift_room v0 s hs
  generalize hB : (2:Nat) ^ 64 = B at *
  have hB0 : 0 < B := by subst hB; exact Nat.two_pow_pos _
  have e1 : (L + wt k * (v0 + B * v1)) * sh s =
      (L * sh s + wt k * (v0 * sh s)) + wt k * B * (v1 * sh s) := by grind
  rw [e1, hw, Nat.add_mul_div_left _ _ (Nat.mul_pos hwk hB0), Nat.add_comm]
  rw [Nat.add_left_cancel_iff]
  rw [← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hwk]
  have he : L * sh s / wt k < sh s := by
    apply Nat.div_lt_of_lt_mul
    exact Nat.mul_lt_mul_of_pos_right hL hs0
  have hdm := Nat.div_add_mod (v0 * sh s) B
  generalize L * sh s / wt k = e at *
  generalize v0 * sh s / B = d at *
  generalize v0 * sh s % B = m at *
  generalize v0 * sh s = V at *
  have : e + V = (m + e) + B * d := by omega
  rw [this, Nat.add_mul_div_left _ _ hB0, Nat.div_eq_of_lt (by omega)]
  simp

/-- con-ron's `knuth_estimate`: with `D` and `U` the divisor and the dividend shifted by `s` and
divided by the same weight, `⌊T / b⌋ ≤ ⌊U / D⌋`. -/
theorem knuth_est (T b s w : Nat) (hw : 0 < w) (hD : 0 < b * sh s / w) :
    T / b ≤ T * sh s / w / (b * sh s / w) := by
  rw [Nat.le_div_iff_mul_le hD, Nat.le_div_iff_mul_le hw]
  have h1 : T / b * b ≤ T := Nat.div_mul_le_self T b
  have h2 : b * sh s / w * w ≤ b * sh s := Nat.div_mul_le_self _ w
  generalize T / b = q at *
  generalize b * sh s / w = D at *
  calc q * D * w = q * (D * w) := by grind
    _ ≤ q * (b * sh s) := Nat.mul_le_mul_left _ h2
    _ = q * b * sh s := by grind
    _ ≤ T * sh s := Nat.mul_le_mul_right _ h1

/-- One limb of `div_submul`: the product `q · y` plus the carry `c` in, subtracted from `x`;
the new limb `x'` and the carry out (`mulhi` plus the two borrows) keep
`x' + q y + c = x + c' 2^64`, and the carry out does not wrap. -/
theorem submul_step (x y q c : Word) :
    (x - (q * y + c)).toNat + q.toNat * y.toNat + c.toNat =
      x.toNat + (UInt64.ofNat (q.toNat * y.toNat / 2 ^ 64) + (if q * y + c < c then 1 else 0) +
          (if x < q * y + c then 1 else 0)).toNat * 2 ^ 64 := by
  have hs := mul_split q y
  have hle := mulHiN_le q y
  have hx := x.toNat_lt; have hc := c.toNat_lt
  have hlo : (q * y + c).toNat = ((q * y).toNat + c.toNat) % 2 ^ 64 := UInt64.toNat_add _ _
  have hlt1 : (q * y + c < c) ↔ (q * y + c).toNat < c.toNat := UInt64.lt_iff_toNat_lt
  have hlt2 : (x < q * y + c) ↔ x.toNat < (q * y + c).toNat := UInt64.lt_iff_toNat_lt
  have hsub : (x - (q * y + c)).toNat = (2 ^ 64 - (q * y + c).toNat + x.toNat) % 2 ^ 64 :=
    UInt64.toNat_sub _ _
  have hlo' := (q * y + c).toNat_lt
  have hl := (q * y).toNat_lt
  rw [hsub]
  by_cases h1 : q * y + c < c <;> by_cases h2 : x < q * y + c <;>
    simp only [h1, h2, ite_true, ite_false] <;>
    simp only [UInt64.toNat_add, mulhi_toNat, UInt64.reduceToNat] <;>
    simp only [hlt1, hlt2] at h1 h2 <;>
    generalize (q * y + c).toNat = lo at * <;>
    generalize (q * y).toNat = L at * <;>
    generalize mulHiN q y = H at * <;>
    generalize q.toNat * y.toNat = P at * <;>
    omega

end L.Arena
