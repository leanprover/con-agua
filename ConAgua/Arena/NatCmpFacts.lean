module

public import ConAgua.Arena.Pool
public import ConAgua.Arena.NatGrindAttr
import ConAgua.Arena.GrindAttr

@[expose] public section

/-!
# Prefix values against weights, and the comparison code

The facts about pool prefixes that `nat_cmp` (`NatCmp.lean`) is built on, apart from its program
so that the other Nat ops (`NatSub`, `NatShr`, `NatDiv`) can use them without waiting for it:
a prefix is below its weight, the top limb decides, a longer normalised slice denotes more,
and the comparison code `cmpW`.
-/

namespace L.Arena

/-! ## The model -/

/-- The comparison code of con-ron's `Cmp`: `0` = `Lt`, `1` = `Eq`, `2` = `Gt`. -/
def cmpW (a b : Nat) : Word := if a < b then 0 else if a = b then 1 else 2

theorem cmpW_lt (a b : Nat) (h : a < b) : cmpW a b = 0 := by simp [cmpW, h]
theorem cmpW_eq (a b : Nat) (h : a = b) : cmpW a b = 1 := by simp [cmpW, h]
theorem cmpW_gt (a b : Nat) (h : b < a) : cmpW a b = 2 := by
  simp [cmpW, Nat.not_lt.mpr (Nat.le_of_lt h), Nat.ne_of_gt h]
grind_pattern [natcmp_grind] cmpW_lt => cmpW a b
grind_pattern [natcmp_grind] cmpW_eq => cmpW a b
grind_pattern [natcmp_grind] cmpW_gt => cmpW a b

/-! ## Prefix values below a weight -/

/-- A prefix of `k` limbs is below `wt k`. (`LitRefine.lean` has the same fact as `pv_lt`; that
file is not a `module`, so it cannot be imported here.) -/
theorem pv_lt_wt (p : Array Word) (o k : Nat) : pv p o k < wt k := by
  induction k with
  | zero => simp [pv, wt]
  | succ k ih =>
    simp only [pv]
    have hw : wt (k + 1) = wt k * 2 ^ 64 := wt_succ k (k + 1) rfl
    have hl := (p[o + k]?.getD 0).toNat_lt
    have : ((p[o + k]?.getD 0).toNat + 1) * wt k ≤ 2 ^ 64 * wt k :=
      Nat.mul_le_mul_right _ (by omega)
    rw [hw]; rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (2 ^ 64)] at this; omega
grind_pattern [natcmp_grind] pv_lt_wt => pv p o k

/-- The top limb decides: if limb `k - 1` of `a` is below limb `k - 1` of `b`, then the first `k`
limbs of `a` denote less than those of `b`. The pattern starts from the comparison the program
makes; its conclusion relates two terms already present, so it does not feed itself. -/
theorem pv_succ_lt (p : Array Word) (oa ob k ia ib : Nat) (ha : ia < p.size) (hb : ib < p.size)
    (hia : ia + 1 = oa + k) (hib : ib + 1 = ob + k) (hk : 0 < k) (hx : p[ia] < p[ib]) :
    pv p oa k < pv p ob k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h1 := pv_succ p oa j (j + 1) ia rfl (by omega) ha
  have h2 := pv_succ p ob j (j + 1) ib rfl (by omega) hb
  have h3 := pv_lt_wt p oa j
  have hx' : (p[ia]).toNat + 1 ≤ (p[ib]).toNat := hx
  have : ((p[ia]).toNat + 1) * wt j ≤ (p[ib]).toNat * wt j := Nat.mul_le_mul_right _ hx'
  rw [Nat.add_mul, Nat.one_mul] at this
  omega
grind_pattern [natcmp_grind] pv_succ_lt => p[ia] < p[ib], pv p oa k, pv p ob k

/-- A normalised slice with more limbs denotes more (the length test of `cmp`). -/
theorem pv_len_lt (p q : Array Word) (oa ob la lb : Nat) (hn : Norm q ob lb) (hl : la < lb) :
    pv p oa la < pv q ob lb := by
  have h1 := pv_lt_wt p oa la
  have h2 : wt (lb - 1) ≤ pv q ob lb := by
    obtain ⟨j, rfl⟩ : ∃ j, lb = j + 1 := ⟨lb - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pv]
    have : (q[ob + j]?.getD 0) ≠ 0 := hn (by omega)
    have : 1 ≤ (q[ob + j]?.getD 0).toNat := by
      rcases Nat.eq_zero_or_pos (q[ob + j]?.getD 0).toNat with h | h
      · exact absurd (UInt64.toNat_inj.mp (h.trans UInt64.toNat_zero.symm)) this
      · exact h
    have := Nat.mul_le_mul_right (wt j) this
    omega
  have h3 : wt la ≤ wt (lb - 1) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (by omega))
  omega

/-! ## Splitting a prefix -/

theorem pv_append (p : Array Word) (o w k : Nat) :
    pv p o (w + k) = pv p o w + wt w * pv p (o + w) k := by
  induction k with
  | zero => simp [pv]
  | succ k ih =>
    rw [← Nat.add_assoc, pv, ih, pv, wt_add w k (w + k) rfl,
      show o + (w + k) = o + w + k by omega]
    grind

theorem pv_ge_wt (p : Array Word) (o l : Nat) (hl : 0 < l) (hn : Norm p o l) :
    wt (l - 1) ≤ pv p o l := by
  obtain ⟨j, rfl⟩ : ∃ j, l = j + 1 := ⟨l - 1, by omega⟩
  simp only [Nat.add_sub_cancel, pv]
  have : (p[o + j]?.getD 0) ≠ 0 := hn (by omega)
  have : 1 ≤ (p[o + j]?.getD 0).toNat := by
    rcases Nat.eq_zero_or_pos (p[o + j]?.getD 0).toNat with h | h
    · exact absurd (UInt64.toNat_inj.mp (h.trans UInt64.toNat_zero.symm)) this
    · exact h
  have := Nat.mul_le_mul_right (wt j) this
  omega

end L.Arena
