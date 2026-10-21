import ConAgua.Arena.Pins
import ConAgua.Census.Attr

/-!
# The environment index in L: rows, `find?`, `push`, `popTemp`, `erase`

`Tiers.lean`'s `EnvR dn m vis fe` relates one view of the twin's `IFEnv` to the index arrays
`EIXA`/`EIXS`/`EIXN` (132‥134; rows addressed by the name handle), the constants array `ECON`
(135, `CTL[128]` entries) and the record pool `EREC` (136). This file has:

* `env_row_get(w)` / `env_row_set(w, c, p)`: the row of name handle `w` (abort on a tag above 2
  or an index past the end); their models `rowC`/`rowP` and `rowSet`, and the one fact the
  relation needs about a write: rows of other names do not move (`rowC_rowSet`).
* `env_find(w, vis)` refines `IFEnv.find?`, `env_push(vis, p)` refines `IFEnv.push`,
  `env_pop_temp(vis, w, c, p)` refines `IFEnv.popTemp`, `env_erase(w)` refines `HashMap.erase`
  on the index (one step of `eraseInstalled`), and `restrictTo` is the view word alone
  (`EnvR.restrictTo`). `mkIFEnv IEnv.empty` is all-zero memory (`EnvR.init`).

The twin's functions here are pure (`IFEnv → IFEnv`), so a refinement is: the L run ends in a
memory where `EnvR` holds of the twin's result.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## Row addresses -/

/-- `w`'s tag as an L expression computes it. -/
def tagW (w : Word) : Word := w >>> 28
/-- `w`'s row index as an L expression computes it: `4 (w mod 2^27) + 2 tier`. -/
def ixW (w : Word) : Word :=
  ((w - ((w >>> 27) <<< 27)) <<< 2) + (((w >>> 27) - ((w >>> 28) <<< 1)) <<< 1)

theorem tagW_toNat (w : Word) : (tagW w).toNat = rowTag w := by
  simp [tagW, rowTag, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]

theorem ixW_toNat (w : Word) (hw : w.toNat < 2 ^ 32) : (ixW w).toNat = rowIx w := by
  have h1 : (w >>> 27).toNat = w.toNat / 2 ^ 27 := by
    simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  have h2 : (w >>> 28).toNat = w.toNat / 2 ^ 28 := by
    simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  have h3 : ((w >>> 27) <<< 27).toNat = w.toNat / 2 ^ 27 * 2 ^ 27 := by
    rw [UInt64.toNat_shiftLeft, h1]; simp [Nat.shiftLeft_eq]; omega
  have h4 : ((w >>> 28) <<< 1).toNat = w.toNat / 2 ^ 28 * 2 := by
    rw [UInt64.toNat_shiftLeft, h2]; simp [Nat.shiftLeft_eq]; omega
  have h5 : (w - ((w >>> 27) <<< 27)).toNat = w.toNat % 2 ^ 27 := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)), h3]; omega
  have h6 : ((w >>> 27) - ((w >>> 28) <<< 1)).toNat = w.toNat / 2 ^ 27 % 2 := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)), h1, h4]; omega
  simp only [ixW, rowIx, UInt64.toNat_add, UInt64.toNat_shiftLeft, h5, h6]
  simp [Nat.shiftLeft_eq]; omega

theorem nat_split27 (a : Nat) :
    a = 2 ^ 28 * (a / 2 ^ 28) + 2 ^ 27 * (a / 2 ^ 27 % 2) + a % 2 ^ 27 := by
  have := Nat.div_add_mod a (2 ^ 27); have := Nat.div_add_mod (a / 2 ^ 27) 2
  rw [Nat.div_div_eq_div_mul] at this; omega

theorem nat_rowIx_inj (a b : Nat) (ht : a / 2 ^ 28 = b / 2 ^ 28)
    (hi : 4 * (a % 2 ^ 27) + 2 * (a / 2 ^ 27 % 2) = 4 * (b % 2 ^ 27) + 2 * (b / 2 ^ 27 % 2)) :
    a = b := by
  have e1 := nat_split27 a; have e2 := nat_split27 b
  have : a / 2 ^ 27 % 2 < 2 := Nat.mod_lt _ (by decide)
  have : b / 2 ^ 27 % 2 < 2 := Nat.mod_lt _ (by decide)
  generalize a / 2 ^ 28 = x1 at *; generalize a / 2 ^ 27 % 2 = y1 at *
  generalize a % 2 ^ 27 = z1 at *; generalize b / 2 ^ 28 = x2 at *
  generalize b / 2 ^ 27 % 2 = y2 at *; generalize b % 2 ^ 27 = z2 at *
  omega

/-- Two name words with the same tag and row index are equal. -/
theorem rowIx_inj {w w' : Word} (ht : rowTag w = rowTag w') (hi : rowIx w = rowIx w') : w = w' :=
  UInt64.toNat_inj.mp (nat_rowIx_inj _ _ ht hi)

/-! ## The models of a row write -/

/-- Word `k` of an array, `0` out of bounds. -/
def rdN (a : Array Word) (k : Nat) : Word := a[k]?.getD 0

theorem rdN_set64 (m : Mem) (a b : ArrId) (k v : Word) (j : Nat) :
    rdN ((m.set64 a k v).arr64 b) j =
      if b = a ∧ k.toNat = j ∧ j < (m.arr64 a).size then v else rdN (m.arr64 b) j := by
  by_cases h : b = a
  · subst h
    rw [Mem.arr64_set64_same]
    simp only [rdN, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    grind
  · rw [Mem.arr64_set64_ne _ _ _ _ _ h]; simp [h]

/-- The row's array. -/
def rowArr (w : Word) : ArrId := 132 + rowTag w

/-- The memory after `env_row_set(w, c, p)`. -/
def rowSet (m : Mem) (w c p : Word) : Mem :=
  (m.set64 (rowArr w) (ixW w) c).set64 (rowArr w) (ixW w + 1) p

theorem rowC_eq (m : Mem) (w : Word) (h : rowTag w ≤ 2) :
    rowC m w = rdN (m.arr64 (rowArr w)) (rowIx w) := by simp [rowC, h, rdN, rowArr]
theorem rowP_eq (m : Mem) (w : Word) (h : rowTag w ≤ 2) :
    rowP m w = rdN (m.arr64 (rowArr w)) (rowIx w + 1) := by simp [rowP, h, rdN, rowArr]

theorem ixW_succ (w : Word) (hw : w.toNat < 2 ^ 32) : (ixW w + 1).toNat = rowIx w + 1 := by
  rw [UInt64.toNat_add, ixW_toNat w hw]; simp [rowIx]; omega

section rowSet
variable {m : Mem} {w c p w' : Word} (hw : w.toNat < 2 ^ 32) (ht : rowTag w ≤ 2)
  (hb : rowIx w + 1 < (m.arr64 (rowArr w)).size)
include hw ht hb

theorem rowC_rowSet (ht' : rowTag w' ≤ 2) :
    rowC (rowSet m w c p) w' = if w' = w then c else rowC m w' := by
  have e1 : rowIx w % 2 = 0 := by simp only [rowIx]; omega
  have e2 : rowIx w' % 2 = 0 := by simp only [rowIx]; omega
  simp only [rowC_eq _ _ ht', rowSet, rdN_set64, Mem.size_arr64_set64, ixW_succ w hw, ixW_toNat w hw]
  by_cases he : w' = w
  · subst he; simp; omega
  · have hk : rowArr w' = rowArr w → rowIx w ≠ rowIx w' := fun h1 h2 =>
      he (rowIx_inj (by simp only [rowArr, ArrId] at h1; omega) h2.symm)
    simp only [he, ite_false]
    split
    · rename_i h1; exfalso; have := h1.2.1; omega
    · split
      · rename_i h2; exact absurd h2.2.1 (hk h2.1)
      · rfl

theorem rowP_rowSet (ht' : rowTag w' ≤ 2) :
    rowP (rowSet m w c p) w' = if w' = w then p else rowP m w' := by
  have e1 : rowIx w % 2 = 0 := by simp only [rowIx]; omega
  have e2 : rowIx w' % 2 = 0 := by simp only [rowIx]; omega
  simp only [rowP_eq _ _ ht', rowSet, rdN_set64, Mem.size_arr64_set64, ixW_succ w hw, ixW_toNat w hw]
  by_cases he : w' = w
  · subst he; simp; omega
  · have hk : rowArr w' = rowArr w → rowIx w ≠ rowIx w' := fun h1 h2 =>
      he (rowIx_inj (by simp only [rowArr, ArrId] at h1; omega) h2.symm)
    simp only [he, ite_false]
    split
    · rename_i h1; exact absurd (by have := h1.2.1; omega) (hk h1.1)
    · split
      · rename_i h2; exfalso; have := h2.2.1; omega
      · rfl

end rowSet

theorem rowSet_arr (m : Mem) (w c p : Word) (b : ArrId) (h : b ≠ rowArr w) :
    (rowSet m w c p).arr64 b = m.arr64 b := by
  simp [rowSet, Mem.arr64_set64_ne _ _ _ _ _ h]

/-! ## `env_row_get`, `env_row_set` -/

/-- `env_ix(w)`: the tag and the row index of name handle `w`. -/
def envIxL : FunDecl := lfn (w) locals () {
  return (w >> 28, ((w - ((w >> 27) << 27)) << 2) + (((w >> 27) - ((w >> 28) << 1)) << 1))
}

/-- `env_row_get(w)`: the row of name handle `w`, `(counter + 1, record)`. -/
def envRowGetL : FunDecl := lfn (w) locals (g, ix) {
  (g, ix) := call env_ix(w);
  if g == 0 { return (EIXA.u64[ix], EIXA.u64[ix + 1]) };
  if g == 1 { return (EIXS.u64[ix], EIXS.u64[ix + 1]) };
  if g == 2 { return (EIXN.u64[ix], EIXN.u64[ix + 1]) };
  abort
}

/-- `env_row_set(w, c, p)`: write the row of name handle `w`. -/
def envRowSetL : FunDecl := lfn (w, c, p) locals (g, ix) {
  (g, ix) := call env_ix(w);
  if 2 < g { abort };
  if g == 0 {
    EIXA.u64[ix] := c; EIXA.u64[ix + 1] := p; return 0
  };
  if g == 1 {
    EIXS.u64[ix] := c; EIXS.u64[ix + 1] := p; return 0
  };
  EIXN.u64[ix] := c; EIXN.u64[ix + 1] := p; return 0
}

section specs
variable (p : Prog)

theorem envIx_spec (hp : p.lookup "env_ix" = some envIxL) (n : Nat) (s₀ : St) (w : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "env_ix" [w]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ r.headD 0 = tagW w ∧ r.tail.headD 0 = ixW w; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, envIxL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs] <;>
      simp_all [tagW, ixW, LocEq, BinOp.eval, Sig.retVal, Sig.retOr, Locals.init]

theorem envRowGet_spec (hx : p.lookup "env_ix" = some envIxL)
    (hp : p.lookup "env_row_get" = some envRowGetL) (n : Nat) (s₀ : St)
    (w : Word) (hw : w.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "env_row_get" [w]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ rowTag w ≤ 2 ∧ r.headD 0 = rowC s₀.mem w ∧
      r.tail.headD 0 = rowP s₀.mem w; ⊤⦄ := by
  have ht := tagW_toNat w
  have hi := ixW_toNat w hw
  have hi1 := ixW_succ w hw
  have hc : ∀ k, rowTag w = k → k ≤ 2 → rowC s₀.mem w = rdN (s₀.mem.arr64 (132 + k)) (rowIx w) ∧
      rowP s₀.mem w = rdN (s₀.mem.arr64 (132 + k)) (rowIx w + 1) := by
    intro k hk hk2; subst hk; exact ⟨rowC_eq _ _ hk2, rowP_eq _ _ hk2⟩
  have hrd : ∀ (a : Array Word) (k : Nat) (h : k < a.size), rdN a k = a[k] := by
    intro a k h; simp [rdN, h]
  rw [invoke_eq _ hp]
  simp only [callFn, envRowGetL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, envIx_spec p hx n] <;>
      finish

theorem envRowSet_spec (hx : p.lookup "env_ix" = some envIxL)
    (hp : p.lookup "env_row_set" = some envRowSetL) (n : Nat) (s₀ : St)
    (w c q : Word) (hw : w.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "env_row_set" [w, c, q]
    ⦃fun _ s' => s'.mem = rowSet s₀.mem w c q ∧ LocEq s' s₀ ∧ rowTag w ≤ 2 ∧
      rowIx w + 1 < (s₀.mem.arr64 (rowArr w)).size; ⊤⦄ := by
  have ht := tagW_toNat w
  have hi := ixW_toNat w hw
  have hi1 := ixW_succ w hw
  rw [invoke_eq _ hp]
  simp only [callFn, envRowSetL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, envIx_spec p hx n] <;>
      finish [rowSet, rowArr]

end specs

end L.Arena
