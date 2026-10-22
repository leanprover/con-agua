module

public import ConAgua.Arena.Store

@[expose] public section

/-!
# The L side of the expression view: handle words and branch-free arithmetic

What every expression walk's L code shares: a handle word's tier bit and index (the tag is
`h >> 28`), the view's checks (`viewOK`: the scratch tier open for a scratch handle, the index
below the tier's count `CTL[c + t]`), and the branch-free `max`, truncating `z - 1` and the
saturating range arithmetic of the derived words (`satSuccW`, `satPredW`), which keep a walk's
bodies loop- and branch-free per tag (the house rule; `DESIGN.md`, lane `walk`).
-/

namespace L.Arena

/-- The larger of two words (branch-free in L: `x + (y - x) * u64(x < y)`). -/
def maxW (x y : Word) : Word := x + (y - x) * (if x < y then 1 else 0)

/-- Truncating `z - 1` (branch-free in L: `z - u64(0 < z)`). -/
def predW (z : Word) : Word := z - (if 0 < z then 1 else 0)

/-- The tier bit and the index of a handle word. -/
def tierW (h : Word) : Word := (h >>> 27) &&& 1
def idxW (h : Word) : Word := h &&& 134217727

/-- The view checks: a scratch handle needs the scratch tier open, and the index must be below
the tier's count `CTL[c + t]`. -/
def viewOK (m : Mem) (h c : Word) : Prop :=
  ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) ∧ idxW h < rdW (m.arr64 CTL) (c + tierW h)

/-- `min (x + 1) 32767` without wrapping (branch-free in L:
`(x + 1) * u64(x < 32767) + 32767 * u64(32767 <= x)`), con-leche's `satSucc`. -/
def satSuccW (x : Word) : Word :=
  (x + 1) * (if x < 32767 then 1 else 0) + 32767 * (if 32767 ≤ x then 1 else 0)

/-- con-leche's `satPred`: `32767` stays, `0` stays, else `x - 1` (branch-free in L:
`x - u64(0 < x) + u64(x == 32767)`). -/
def satPredW (x : Word) : Word := x - (if 0 < x then 1 else 0) + (if x = 32767 then 1 else 0)

/-- Pack two saturating 15-bit ranges into one word (`der_b`'s and `der_f`'s shared word, the
`DerR` compound columns, lane `exprops3`): `b` (`< 32768`) in bits 0‥14, `f` (`< 32768`) in bits
15‥29. Addition, not `|||`: the two fields are disjoint ranges, so `+` *is* the join, and the
arithmetic form is what makes the roundtrip lemmas `omega`-provable (con-leche's `packData` is the
same device, one level up). -/
def packBF (b f : Word) : Word := b + f * 32768

/-- `der_b`'s read of a packed word: `& 32767` recovers `b`. -/
theorem packBF_bvar (b f : Word) (hb : b.toNat < 32768) (_hf : f.toNat < 32768) :
    packBF b f &&& 32767 = b := by
  apply UInt64.toNat_inj.mp
  simp only [packBF, UInt64.toNat_and, UInt64.toNat_add, UInt64.toNat_mul]
  have e : (32767 : Word).toNat = 2 ^ 15 - 1 := rfl
  rw [e, Nat.and_two_pow_sub_one_eq_mod]
  have e2 : (32768 : Word).toNat = 2 ^ 15 := rfl
  rw [e2]
  omega

/-- `der_f`'s read of a packed word: `>> 15` recovers `f`. -/
theorem packBF_fvar (b f : Word) (hb : b.toNat < 32768) (hf : f.toNat < 32768) :
    packBF b f >>> 15 = f := by
  apply UInt64.toNat_inj.mp
  simp only [packBF, UInt64.toNat_shiftRight, UInt64.toNat_add, UInt64.toNat_mul,
    Nat.shiftRight_eq_div_pow]
  have e15 : (15 : Word).toNat % 64 = 15 := rfl
  have e32768 : (32768 : Word).toNat = 32768 := rfl
  have e2 : (2 : Nat) ^ 15 = 32768 := rfl
  rw [e15, e32768, e2]
  omega

end L.Arena
