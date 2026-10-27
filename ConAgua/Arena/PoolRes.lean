module

public import ConAgua.L.Logic
public import ConAgua.Arena.Pool
public import ConAgua.Arena.Reasons
meta import ConAgua.L.Semantics

@[expose] public section

/-!
# The limb pool: a slice resolved once (lane blkcopy2)

A reader of a slice `(o, l)` of the tiered pool (`Arena/Pool.lean`) that reads `POOL⦃o + i⦄` for
every limb decodes the tag every time (shift, mask, the tier's descriptor: ~20 instructions per
limb). `⟪sliceRes o l t x⟫` decodes it once, `t := ⦃o⦄.tier`, `x := ⦃o⦄.idx`, after which the
reader loads `POOL⟨t⟩[x + i]`. The block aborts unless the slice lies in one tier
(`x + l ≤ 2^40`; a slice of a well-formed pool always does, `SliceOK`), so the reader's spec needs
no hypothesis about the pool: an in-bounds load `POOL⟨t⟩[x + i]` with `i < l` is the tagged read
`prd m (o + i)` (`prd_res`), whatever the pool's sizes.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

open L

/-- `⟪sliceRes o l t x⟫`: the slice `(o, l)` resolved to its tier `t` and index `x`; aborts unless
`x + l ≤ 2^40`. -/
def sliceRes (o l t x : Var) : Stmt :=
  .seq (.set t (.bin .shr (.var o) (.const 40)))
    (.seq (.set x (.bin .and (.var o) (.const 0xFFFFFFFFFF)))
      (.ite (.cmp .ult (.bin .sub (.const 0x10000000000) (.var x)) (.var l)) (.abort (.const R_CAP_WORD)) .skip))

theorem sliceRes_spec (p : Prog) (k : Stmt → M Sig) (o l t x : Var) (hto : t ≠ o)
    (hlt : l ≠ t) (hlx : l ≠ x) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p k (sliceRes o l t x)
    ⦃fun r s' => r = .normal ∧
      s' = (s₀.setLoc t (s₀.loc o >>> 40)).setLoc x (s₀.loc o &&& 1099511627775) ∧
      (s₀.loc o &&& 1099511627775).toNat + (s₀.loc l).toNat ≤ 2 ^ 40; ⊤⦄ := by
  unfold sliceRes
  vcgen [step, evalE, evalC, setLoc]
  have hot : o ≠ t := Ne.symm hto
  all_goals (simp_all [St.setLoc, Cmp.eval, BinOp.eval])
  rename_i h
  rw [ite_eq_right (Ne.symm hto)] at h
  have hx := tag_idx_lt (s₀.loc o)
  have h1 := UInt64.le_iff_toNat_le.mp h
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp at hx ⊢; omega))] at h1
  simp at h1 hx ⊢; omega

/-- **The resolved read**: limb `i` of a slice in one tier is the tier's word at `x + i`. -/
theorem prd_res (m : Mem) (o i : Word) (h : (o &&& 1099511627775).toNat + i.toNat < 2 ^ 40) :
    prd m (o + i) =
      (m.arr64 (tierA 0 (o >>> 40)))[((o &&& 1099511627775) + i).toNat]?.getD 0 := by
  have ho := o.toNat_lt
  have h' := h; rw [tag_idx_toNat] at h'
  have hoi : (o + i).toNat = o.toNat + i.toNat := by
    rw [UInt64.toNat_add]; apply Nat.mod_eq_of_lt; omega
  have ht : (o + i) >>> 40 = o >>> 40 := by
    apply UInt64.toNat_inj.mp; simp only [tag_tier_toNat, hoi]; omega
  have hx' : (o + i) &&& 1099511627775 = (o &&& 1099511627775) + i := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
    simp only [tag_idx_toNat, hoi]; omega
  unfold prd; rw [ht, hx']

/-- `prd_res` for an in-bounds load. -/
theorem prd_res_get (m : Mem) (o i : Word) (h : (o &&& 1099511627775).toNat + i.toNat < 2 ^ 40)
    (hb : ((o &&& 1099511627775) + i).toNat < (m.arr64 (tierA 0 (o >>> 40))).size) :
    (m.arr64 (tierA 0 (o >>> 40)))[((o &&& 1099511627775) + i).toNat] = prd m (o + i) := by
  rw [prd_res m o i h, Array.getElem?_eq_getElem hb]; rfl

grind_pattern [arena_grind] prd_res_get =>
  (m.arr64 (tierA 0 (o >>> 40)))[((o &&& 1099511627775) + i).toNat]

/-- The bound-free pool `tpool` at a limb of a slice in one tier. -/
theorem tpool_res (m : Mem) (o i : Word) (h : (o &&& 1099511627775).toNat + i.toNat < 2 ^ 40) :
    (tpool m)[o.toNat + i.toNat]?.getD 0 = prd m (o + i) := by
  have ho := o.toNat_lt
  have h' := h; rw [tag_idx_toNat] at h'
  have hoi : (o + i).toNat = o.toNat + i.toNat := by
    rw [UInt64.toNat_add]; apply Nat.mod_eq_of_lt; omega
  rw [← hoi]; exact tpool_getD m (o + i)

end L.Arena
