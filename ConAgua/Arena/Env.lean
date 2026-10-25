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
set_option linter.unusedSimpArgs false

namespace L.Arena

/-! ## Row addresses -/

/-- `w`'s tag as an L expression computes it. -/
def tagW (w : Word) : Word := w >>> 28
theorem tagW_toNat (w : Word) : (tagW w).toNat = rowTag w := by
  simp [tagW, rowTag, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]

/-- `w`'s row array selector as an L expression computes it: `2 tag + tier` (`w >> 27`). -/
def rowSelW (w : Word) : Word := w >>> 27
/-- `w`'s row index as an L expression computes it: `2 (w mod 2^27)`. -/
def ixW (w : Word) : Word := (w &&& 134217727) <<< 1

theorem rowSelW_toNat (w : Word) : (rowSelW w).toNat = 2 * rowTag w + rowTier w := by
  have h0 : (w >>> 27).toNat = w.toNat / 2 ^ 27 := by
    simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  simp only [rowSelW, rowTag, rowTier, h0]
  have h1 := Nat.div_add_mod (w.toNat / 2 ^ 27) 2
  have h2 : w.toNat / 2 ^ 28 = w.toNat / 2 ^ 27 / 2 := by rw [Nat.div_div_eq_div_mul]
  omega

/-- The row array of selector `g` (`rowSelW`): tier 0's `EIXA`, `EIXS`, `EIXN` at `0, 2, 4`, tier 1's
at `1, 3, 5`. -/
def selArr (g : Word) : ArrId :=
  if g = 0 then EIXA else if g = 1 then EIXA1 else if g = 2 then EIXS
  else if g = 3 then EIXS1 else if g = 4 then EIXN else EIXN1

theorem selArr_rowSelW (w : Word) (ht : rowTag w ≤ 2) : selArr (rowSelW w) = rowArr w := by
  have h := rowSelW_toNat w
  have htr : rowTier w < 2 := Nat.mod_lt _ (by decide)
  have e : ∀ k : Nat, k < 6 → (rowSelW w).toNat = k → rowSelW w = UInt64.ofNat k := fun k hk e =>
    UInt64.toNat_inj.mp (by rw [e]; simp; omega)
  simp only [selArr, rowArr]
  rcases (by omega : rowTag w = 0 ∨ rowTag w = 1 ∨ rowTag w = 2) with h1 | h1 | h1 <;>
  rcases (by omega : rowTier w = 0 ∨ rowTier w = 1) with h2 | h2 <;>
  · rw [e (2 * rowTag w + rowTier w) (by omega) h]; simp [h1, h2]

theorem ixW_toNat (w : Word) (hw : w.toNat < 2 ^ 32) : (ixW w).toNat = rowIx w := by
  have h1 : (w &&& 134217727).toNat = w.toNat % 2 ^ 27 := by
    rw [UInt64.toNat_and]
    rw [show (134217727 : UInt64).toNat = 2 ^ 27 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
  rw [ixW, UInt64.toNat_shiftLeft, h1]; simp [Nat.shiftLeft_eq, rowIx]; omega

theorem nat_split27 (a : Nat) :
    a = 2 ^ 28 * (a / 2 ^ 28) + 2 ^ 27 * (a / 2 ^ 27 % 2) + a % 2 ^ 27 := by
  have := Nat.div_add_mod a (2 ^ 27); have := Nat.div_add_mod (a / 2 ^ 27) 2
  rw [Nat.div_div_eq_div_mul] at this; omega

theorem nat_rowIx_inj (a b : Nat) (ht : a / 2 ^ 28 = b / 2 ^ 28)
    (hr : a / 2 ^ 27 % 2 = b / 2 ^ 27 % 2) (hi : 2 * (a % 2 ^ 27) = 2 * (b % 2 ^ 27)) :
    a = b := by
  have e1 := nat_split27 a; have e2 := nat_split27 b
  omega

/-- Two name words (tags at most `2`) with the same row array and row index are equal. -/
theorem rowIx_inj {w w' : Word} (ht : rowTag w ≤ 2) (ht' : rowTag w' ≤ 2)
    (ha : rowArr w = rowArr w') (hi : rowIx w = rowIx w') : w = w' := by
  have h1 : rowTier w < 2 := Nat.mod_lt _ (by decide)
  have h2 : rowTier w' < 2 := Nat.mod_lt _ (by decide)
  simp only [rowArr, ArrId] at ha
  exact UInt64.toNat_inj.mp (nat_rowIx_inj _ _ (by simp only [rowTag] at *; omega)
    (by simp only [rowTier, rowTag] at *; omega) hi)

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

/-- The memory after `env_row_set(w, c, p)`. -/
def rowSet (m : Mem) (w c p : Word) : Mem :=
  (m.set64 (rowArr w) (ixW w) c).set64 (rowArr w) (ixW w + 1) p

theorem rowC_eq (m : Mem) (w : Word) (h : rowTag w ≤ 2) :
    rowC m w = rdN (m.arr64 (rowArr w)) (rowIx w) := by simp [rowC, h, rdN]
theorem rowP_eq (m : Mem) (w : Word) (h : rowTag w ≤ 2) :
    rowP m w = rdN (m.arr64 (rowArr w)) (rowIx w + 1) := by simp [rowP, h, rdN]

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
      he (rowIx_inj ht' ht h1 h2.symm)
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
      he (rowIx_inj ht' ht h1 h2.symm)
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

theorem ixW_lt (w : Word) (hw : w.toNat < 2 ^ 32) : (ixW w).toNat + 1 < 2 ^ 28 := by
  rw [ixW_toNat w hw]; simp only [rowIx]; omega

/-- **A row write leaves every word from `2^28` up** (the table rows, the tables list's words). -/
theorem rdN_rowSet_hi (m : Mem) (w c p : Word) (hw : w.toNat < 2 ^ 32) (b : ArrId) (j : Nat)
    (hj : 2 ^ 28 ≤ j) : rdN ((rowSet m w c p).arr64 b) j = rdN (m.arr64 b) j := by
  have h1 := ixW_lt w hw
  have h2 := ixW_succ w hw
  simp only [rowSet, rdN_set64]
  rw [if_neg (by rw [h2]; have := ixW_toNat w hw; omega), if_neg (by omega)]

theorem tblRow_eq (m : Mem) (w : Word) (h : rowTag w ≤ 2) :
    tblRow m w = rdN (m.arr64 (rowArr w)) (tblIx w) := by simp [tblRow, h, rdN]

theorem tblRow_rowSet (m : Mem) (w c p : Word) (hw : w.toNat < 2 ^ 32) (w' : Word) :
    tblRow (rowSet m w c p) w' = tblRow m w' := by
  unfold tblRow; split
  · have := rdN_rowSet_hi m w c p hw (rowArr w') (tblIx w') (by simp only [tblIx]; omega)
    simpa only [rdN] using this
  · rfl

theorem tblCnt_rowSet (m : Mem) (w c p : Word) (hw : w.toNat < 2 ^ 32) :
    tblCnt (rowSet m w c p) = tblCnt m := by
  have := rdN_rowSet_hi m w c p hw EIXA (2 ^ 29) (by omega)
  simp only [tblCnt]; simp only [rdN] at this; rw [this]

theorem tblHead_rowSet (m : Mem) (w c p : Word) (hw : w.toNat < 2 ^ 32) :
    tblHead (rowSet m w c p) = tblHead m := by
  have := rdN_rowSet_hi m w c p hw EIXA (2 ^ 29 + 1) (by omega)
  simp only [tblHead]; simp only [rdN] at this; rw [this]

/-! ## `env_row_get`, `env_row_set` -/

/-- `env_ix(w)`: the row array selector (`2 tag + tier`) and the row index of name handle `w`. -/
-- con-ron: none — row access of L's environment table (the twin's `IFEnv` map)
def envIxL : FunDecl := lfn (w) locals () {
  return (w >> 27, (w & 134217727) << 1)
}

/-- `env_row_get(w)`: the row of name handle `w`, `(counter + 1, record)`. -/
-- con-ron: none — row access of L's environment table (the twin's `IFEnv` map)
def envRowGetL : FunDecl := lfn (w) locals (g, ix) {
  (g, ix) := call env_ix(w);
  if g == 0 { return (EIXA.u64[ix], EIXA.u64[ix + 1]) };
  if g == 1 { return (EIXA1.u64[ix], EIXA1.u64[ix + 1]) };
  if g == 2 { return (EIXS.u64[ix], EIXS.u64[ix + 1]) };
  if g == 3 { return (EIXS1.u64[ix], EIXS1.u64[ix + 1]) };
  if g == 4 { return (EIXN.u64[ix], EIXN.u64[ix + 1]) };
  if g == 5 { return (EIXN1.u64[ix], EIXN1.u64[ix + 1]) };
  abort
}

/-- `env_row_set(w, c, p)`: write the row of name handle `w`. -/
-- con-ron: none — row access of L's environment table (the twin's `IFEnv` map)
def envRowSetL : FunDecl := lfn (w, c, p) locals (g, ix) {
  (g, ix) := call env_ix(w);
  if g == 0 { EIXA.u64[ix] := c; EIXA.u64[ix + 1] := p; return 0 };
  if g == 1 { EIXA1.u64[ix] := c; EIXA1.u64[ix + 1] := p; return 0 };
  if g == 2 { EIXS.u64[ix] := c; EIXS.u64[ix + 1] := p; return 0 };
  if g == 3 { EIXS1.u64[ix] := c; EIXS1.u64[ix + 1] := p; return 0 };
  if g == 4 { EIXN.u64[ix] := c; EIXN.u64[ix + 1] := p; return 0 };
  if g == 5 { EIXN1.u64[ix] := c; EIXN1.u64[ix + 1] := p; return 0 };
  abort
}

section specs
variable (p : Prog)

theorem envIx_spec (hp : p.lookup "env_ix" = some envIxL) (n : Nat) (s₀ : St) (w : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "env_ix" [w]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ r.headD 0 = rowSelW w ∧ r.tail.headD 0 = ixW w; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, envIxL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs] <;>
      simp_all [rowSelW, ixW, LocEq, BinOp.eval, Sig.retVal, Sig.retOr, Locals.init]

theorem envRowGet_spec (hx : p.lookup "env_ix" = some envIxL)
    (hp : p.lookup "env_row_get" = some envRowGetL) (n : Nat) (s₀ : St)
    (w : Word) (hw : w.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "env_row_get" [w]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ rowTag w ≤ 2 ∧ r.headD 0 = rowC s₀.mem w ∧
      r.tail.headD 0 = rowP s₀.mem w; ⊤⦄ := by
  have ht := rowSelW_toNat w
  have htr : rowTier w < 2 := Nat.mod_lt _ (by decide)
  have hi := ixW_toNat w hw
  have hi1 := ixW_succ w hw
  have hc : ∀ k, rowTag w + 8 * rowTier w = k → rowTag w ≤ 2 →
      rowC s₀.mem w = rdN (s₀.mem.arr64 (132 + k)) (rowIx w) ∧
      rowP s₀.mem w = rdN (s₀.mem.arr64 (132 + k)) (rowIx w + 1) := by
    intro k hk hk2; subst hk
    rw [rowC_eq _ _ hk2, rowP_eq _ _ hk2, rowArr, Nat.add_assoc]; exact ⟨rfl, rfl⟩
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
  have ht := rowSelW_toNat w
  have htr : rowTier w < 2 := Nat.mod_lt _ (by decide)
  have hi := ixW_toNat w hw
  have hi1 := ixW_succ w hw
  have ha : ∀ k, rowTag w + 8 * rowTier w = k → rowArr w = 132 + k := by
    intro k hk; simp only [rowArr, ArrId]; omega
  rw [invoke_eq _ hp]
  simp only [callFn, envRowSetL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, envIx_spec p hx n] <;>
      finish [rowSet]

end specs

/-! ## The relation's facts -/

theorem decI_word_self {k : IdxKind} (w : Word) (hw : w.toNat < 2 ^ 32) :
    (decI w : Idx k).word.toUInt64 = w := by
  apply UInt64.toNat_inj.mp; simp [decI]; omega

theorem decI_eq_iff {k : IdxKind} (w : Word) (hw : w.toNat < 2 ^ 32) (n : Idx k) :
    (decI w = n) ↔ (w = n.word.toUInt64) := by
  constructor
  · rintro rfl; exact (decI_word_self w hw).symm
  · rintro rfl; exact decI_word _

/-- What a found row decodes to: `(0, _)` is `none`, `(1, q)` the record at `q`. -/
def decFound (dn : NIdx → Option ConLeche.Name) (m : Mem) (f q : Word) : Option IConstantInfo :=
  if f = 0 then none else decCI (erecP m) dn q.toNat

section rel
variable {dn : NIdx → Option ConLeche.Name} {m : Mem} {vis : Word} {fe : IFEnv}

/-- **`find?` through the rows.** -/
theorem EnvR.find?_eq (h : EnvR dn m vis fe) (w : Word) (hw : w.toNat < 2 ^ 32)
    (ht : rowTag w ≤ 2) :
    fe.find? (decI w) = if rowC m w = 0 then none
      else if (rowC m w).toNat - 1 < vis.toNat then decCI (erecP m) dn (rowP m w).toNat
      else none := by
  have hk := h.keys (decI w) (by rwa [decI_word_self w hw])
  have hv := h.vals (decI w) (by rwa [decI_word_self w hw])
  rw [decI_word_self w hw] at hk hv
  simp only [IFEnv.find?, h.vis]
  by_cases h0 : rowC m w = 0
  · simp only [rowW, h0, ite_true, Option.map_none] at hk
    have : fe.idx[(decI w : NIdx)]? = none := by
      cases e : fe.idx[(decI w : NIdx)]? <;> simp_all
    simp [this, h0]
  · simp only [rowW, h0, ite_false, Option.map_some] at hk
    have hv := hv h0
    cases e : fe.idx[(decI w : NIdx)]? with
    | none => simp [e] at hk
    | some r =>
      obtain ⟨c, ci⟩ := r
      simp only [e, Option.map_some, Option.some.injEq] at hk hv
      simp [h0, hk, ← hv]

/-- A view of the same index: `restrictTo` is the view word alone (no L code). -/
@[refines ConRon.Arena.IFEnv.restrictTo]
theorem EnvR.restrictTo (h : EnvR dn m vis fe) (k : Word) :
    EnvR dn m k (fe.restrictTo k.toNat) :=
  ⟨rfl, h.keys, h.vals, h.consts, h.tkeys, h.tvals, h.tables⟩

end rel

/-! ## `env_find` -/

/-- `env_find(w, vis)`: `(1, record)` if name `w` has a row below the view `vis`, else `(0, 0)`. -/
-- con-ron: ConRon/Arena/Env.lean:254-259 ConRon.Arena.IFEnv.find?
@[l_impl ConRon.Arena.IFEnv.find?]
def envFindL : FunDecl := lfn (w, vis) locals (c, q) {
  (c, q) := call env_row_get(w);
  if c == 0 { return (0, 0) };
  if c - 1 < vis { return (1, q) };
  return (0, 0)
}

/-- **`env_find` refines `IFEnv.find?`**: the result decodes to the twin's lookup. -/
@[refines ConRon.Arena.IFEnv.find?]
theorem envFind_refines (p : Prog) (hx : p.lookup "env_ix" = some envIxL)
    (hg : p.lookup "env_row_get" = some envRowGetL) (hp : p.lookup "env_find" = some envFindL)
    (n : Nat) (s₀ : St) {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} (vis w : Word)
    (hE : EnvR dn s₀.mem vis fe) (hw : w.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "env_find" [w, vis]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧
      fe.find? (decI w) = decFound dn s₀.mem (r.headD 0) (r.tail.headD 0); ⊤⦄ := by
  have key := EnvR.find?_eq hE w hw
  rw [invoke_eq _ hp]
  simp only [callFn, envFindL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, envRowGet_spec p hx hg n] <;>
      finish [decFound]

/-! ## `env_push` -/

theorem hd?_some {k : IdxKind} {a : Array Word} {i : Nat} {x : Idx k} (h : hd? a i = some x) :
    ∃ w, a[i]? = some w ∧ w.toNat < 2 ^ 32 ∧ x = decI w := by
  cases e : a[i]? with
  | none => simp [hd?, e] at h
  | some w => simp [hd?, e] at h; exact ⟨w, rfl, h.1, h.2.symm⟩

theorem decCV_name {a : Array Word} {q : Nat} {cv : IConstantVal} (h : decCV a q = some cv) :
    ∃ w, a[q]? = some w ∧ w.toNat < 2 ^ 32 ∧ cv.name = decI w := by
  simp only [decCV, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨n, hn, _, _, _, _, h⟩ := h
  cases Option.some.inj h
  exact hd?_some hn

theorem decCI_name {a : Array Word} {dn : NIdx → Option ConLeche.Name} {p : Nat}
    {ci : IConstantInfo} (h : decCI a dn p = some ci) :
    ∃ w, a[p + 1]? = some w ∧ w.toNat < 2 ^ 32 ∧ ci.name = decI w := by
  simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, -, h⟩ := h
  split at h
  rotate_left 6
  · simp at h
  all_goals
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, h⟩ := h
    obtain ⟨w, h1, h2, h3⟩ := decCV_name hcv
    refine ⟨w, h1, h2, ?_⟩
    rw [← h3]
    repeat (obtain ⟨_, _, h⟩ := h)
    rfl

theorem triple_post {α : Type} {prog : M α} {P : St → Prop} {Q Q' : α → St → Prop}
    (h : ⦃fun s => P s⦄ prog ⦃fun r s => Q r s; ⊤⦄) (hq : ∀ r s, Q r s → Q' r s) :
    ⦃fun s => P s⦄ prog ⦃fun r s => Q' r s; ⊤⦄ :=
  M.triple_of_run fun _ _ _ hp hr => hq _ _ (M.of_run hp hr h)

theorem mapM_congr' {α β : Type} (f g : α → Option β) :
    ∀ l : List α, (∀ x ∈ l, f x = g x) → l.mapM f = l.mapM g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.mapM_cons, h x (by simp), mapM_congr' f g xs (fun y hy => h y (by simp [hy]))]

/-- The memory after `env_push(vis, q)`. -/
def envPushMem (m : Mem) (vis q : Word) : Mem :=
  let w := rdN (m.arr64 EREC) (q.toNat + 1)
  let m1 := rowSet m w (vis + 1) q
  let k := rdW (m1.arr64 CTL) 128
  (m1.set64 ECON k q).set64 CTL 128 (k + 1)

theorem EnvR.push {dn : NIdx → Option ConLeche.Name} {m : Mem} {vis : Word} {fe : IFEnv}
    (h : EnvR dn m vis fe) (q : Word) (ci : IConstantInfo)
    (hci : decCI (erecP m) dn q.toNat = some ci) (hv : vis + 1 ≠ 0)
    (ht : rowTag (rdN (m.arr64 EREC) (q.toNat + 1)) ≤ 2)
    (hb : rowIx (rdN (m.arr64 EREC) (q.toNat + 1)) + 1 <
      (m.arr64 (rowArr (rdN (m.arr64 EREC) (q.toNat + 1)))).size)
    (hk : (rdW (m.arr64 CTL) 128).toNat < (m.arr64 ECON).size)
    (hk1 : rdW (m.arr64 CTL) 128 + 1 ≠ 0) (hc : 128 < (m.arr64 CTL).size) :
    EnvR dn (envPushMem m vis q) (vis + 1) (fe.push ci) := by
  obtain ⟨w, hw1, hw2, hname⟩ := decCI_name hci
  have hw : rdN (m.arr64 EREC) (q.toNat + 1) = w := by simp [rdN, erecP_get hw1]
  rw [hw] at ht hb
  have hra : rowArr w ≠ CTL := by simp only [rowArr, CTL, ArrId]; omega
  have hre : rowArr w ≠ ECON := by simp only [rowArr, ECON, ArrId]; omega
  have hrr : rowArr w ≠ EREC := by simp only [rowArr, EREC, ArrId]; omega
  have hk0 : rdW ((rowSet m w (vis + 1) q).arr64 CTL) 128 = rdW (m.arr64 CTL) 128 := by
    rw [rowSet_arr _ _ _ _ _ (Ne.symm hra)]
  -- the arrays of the result
  have hA : ∀ b, b ≠ CTL → b ≠ ECON → (envPushMem m vis q).arr64 b = (rowSet m w (vis + 1) q).arr64 b := by
    intro b h1 h2; simp only [envPushMem, hw]
    rw [Mem.arr64_set64_ne _ _ _ _ _ h1, Mem.arr64_set64_ne _ _ _ _ _ h2]
  have hC : ∀ w', rowTag w' ≤ 2 → rowC (envPushMem m vis q) w' = rowC (rowSet m w (vis + 1) q) w' := by
    intro w' h'; simp only [rowC, h', ite_true]
    rw [hA _ (by simp only [CTL, ArrId, rowArr, rowTier]; omega) (by simp only [ECON, ArrId, rowArr, rowTier]; omega)]
  have hP : ∀ w', rowTag w' ≤ 2 → rowP (envPushMem m vis q) w' = rowP (rowSet m w (vis + 1) q) w' := by
    intro w' h'; simp only [rowP, h', ite_true]
    rw [hA _ (by simp only [CTL, ArrId, rowArr, rowTier]; omega) (by simp only [ECON, ArrId, rowArr, rowTier]; omega)]
  have hR : erecP (envPushMem m vis q) = erecP m := by
    apply erecP_congr
    · rw [hA _ (by decide) (by decide), rowSet_arr _ _ _ _ _ (Ne.symm hrr)]
    · simp only [envPushMem, hw, Mem.arr64_set64_same, rdW_set!,
        Mem.arr64_set64_ne _ _ _ _ _ (show CTL ≠ ECON by decide), rowSet_arr _ _ _ _ _ (Ne.symm hra)]
      simp
  have hW : ∀ n : NIdx, rowTag n.word.toUInt64 ≤ 2 →
      rowW (envPushMem m vis q) n.word.toUInt64 =
        if n.word.toUInt64 = w then some (vis.toNat, q) else rowW m n.word.toUInt64 := by
    intro n hn
    have e1 := rowC_rowSet (c := vis + 1) (p := q) (w' := n.word.toUInt64) hw2 ht hb hn
    have e2 := rowP_rowSet (c := vis + 1) (p := q) (w' := n.word.toUInt64) hw2 ht hb hn
    simp only [rowW, hC _ hn, hP _ hn, e1, e2]
    split
    · have : (vis + 1).toNat = vis.toNat + 1 := by
        rw [UInt64.toNat_add]; have := vis.toNat_lt; simp at hv ⊢
        have : vis.toNat + 1 ≠ 2 ^ 64 := fun h' => hv (UInt64.toNat_inj.mp (by simp; omega))
        omega
      simp [hv, this]
    · rfl
  have hname' : ∀ n : NIdx, (ci.name == n) = decide (n.word.toUInt64 = w) := by
    intro n; rw [hname]
    by_cases e : n.word.toUInt64 = w
    · subst e; simp [decI_word]
    · have : decI w ≠ n := fun h' => e ((decI_eq_iff w hw2 n).mp h').symm
      simp [e, this]
  have hvB : fe.visibleBelow = vis.toNat := h.vis
  have hT : ∀ w', tblRow (envPushMem m vis q) w' = tblRow m w' := by
    intro w'; unfold tblRow; split
    · rw [hA _ (by simp only [CTL, ArrId, rowArr, rowTier]; omega)
        (by simp only [ECON, ArrId, rowArr, rowTier]; omega)]
      have := tblRow_rowSet m w (vis + 1) q hw2 w'
      unfold tblRow at this; simp_all
    · rfl
  have hX : ∀ j, 2 ^ 28 ≤ j → ((envPushMem m vis q).arr64 EIXA)[j]?.getD 0 = (m.arr64 EIXA)[j]?.getD 0 := by
    intro j hj
    rw [hA _ (by decide) (by decide)]
    exact rdN_rowSet_hi m w (vis + 1) q hw2 EIXA j hj
  refine ⟨?_, ?_, ?_, ?_, fun n hn => by rw [hT]; exact h.tkeys n hn,
    fun n hn h0 => by rw [hT, hR] at *; exact h.tvals n hn h0, ?_⟩
  · simp only [IFEnv.push, hvB]
    rw [UInt64.toNat_add]; have := vis.toNat_lt; simp at hv ⊢
    have : vis.toNat + 1 ≠ 2 ^ 64 := fun h' => hv (UInt64.toNat_inj.mp (by simp; omega))
    omega
  · intro n hn
    simp only [IFEnv.push, Std.HashMap.getElem?_insert, hname', hW n hn]
    split <;> simp_all [h.keys n hn]
  · intro n hn h0
    have hW' := hW n hn
    simp only [IFEnv.push, Std.HashMap.getElem?_insert, hname', hR]
    by_cases e : n.word.toUInt64 = w
    · simp only [e, decide_true, ite_true, Option.map_some]
      have : rowP (envPushMem m vis q) w = q := by
        have := rowP_rowSet (c := vis + 1) (p := q) (w' := w) hw2 ht hb ht
        rw [hP _ ht, this]; simp
      rw [this, hci]
    · simp only [e, decide_false, ite_false]
      have hc0 : rowC m n.word.toUInt64 ≠ 0 := by
        intro hc0; apply h0
        have := rowC_rowSet (c := vis + 1) (p := q) (w' := n.word.toUInt64) hw2 ht hb hn
        rw [hC _ hn, this]; simp [e, hc0]
      have := rowP_rowSet (c := vis + 1) (p := q) (w' := n.word.toUInt64) hw2 ht hb hn
      rw [hP _ hn, this]; simp only [e, ite_false]
      exact h.vals n hn hc0
  · have hK : (rdW (m.arr64 CTL) 128 + 1).toNat = (rdW (m.arr64 CTL) 128).toNat + 1 := by
      rw [UInt64.toNat_add]; have := (rdW (m.arr64 CTL) 128).toNat_lt; simp at hk1 ⊢
      have : (rdW (m.arr64 CTL) 128).toNat + 1 ≠ 2 ^ 64 :=
        fun h' => hk1 (UInt64.toNat_inj.mp (by simp; omega))
      omega
    have hsz : 128 < ((rowSet m w (vis + 1) q).arr64 CTL).size := by
      rw [rowSet_arr _ _ _ _ _ (Ne.symm hra)]; exact hc
    have hL : envLen (envPushMem m vis q) = (rdW (m.arr64 CTL) 128).toNat + 1 := by
      simp only [envLen, envPushMem, hw, Mem.arr64_set64_same, rdW_set!,
        Mem.arr64_set64_ne _ _ _ _ _ (show CTL ≠ ECON by decide), hk0]
      simp [hsz, hK]
    have hN : (envPushMem m vis q).arr64 ECON = (m.arr64 ECON).set! (rdW (m.arr64 CTL) 128).toNat q := by
      simp only [envPushMem, hw, Mem.arr64_set64_ne _ _ _ _ _ (show ECON ≠ CTL by decide),
        Mem.arr64_set64_same, hk0, rowSet_arr _ _ _ _ _ (Ne.symm hre)]
    have hcs := h.consts
    simp only [envConsts] at hcs ⊢
    rw [hL, List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.mapM_cons, hR, hN]
    have hk' : nat? ((m.arr64 ECON).set! (rdW (m.arr64 CTL) 128).toNat q)
        (rdW (m.arr64 CTL) 128).toNat = some q.toNat := by
      simp [nat?, Array.set!_eq_setIfInBounds, hk]
    rw [mapM_congr' _ (fun c => do decCI (erecP m) dn (← nat? (m.arr64 ECON) c))]
    · simp only [Array.set!_eq_setIfInBounds] at hk'
      simp [hk', hci, envLen] at hcs ⊢; rw [hcs]; simp [IFEnv.push, Option.bind]
    · intro c hc'
      simp only [List.mem_reverse, List.mem_range] at hc'
      simp only [nat?, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
      simp [show (rdW (m.arr64 CTL) 128).toNat ≠ c by omega]
  · simp only [tblCnt, tblHead, hX _ (show 2 ^ 28 ≤ 2 ^ 29 by omega),
      hX _ (show 2 ^ 28 ≤ 2 ^ 29 + 1 by omega), hR]
    exact h.tables

/-- `env_push(vis, q)`: install the record at `q` (its name is word `q + 1`) at counter `vis`:
its row, its slot in `ECON`; returns the new view `vis + 1`. -/
-- con-ron: ConRon/Arena/Env.lean:266-271 ConRon.Arena.IFEnv.push
-- con-ron: CHANGED since 12752ca7 — `ConRon.Arena.IFEnv.push` changed; re-check the L code and its proofs, then delete this line
@[l_impl ConRon.Arena.IFEnv.push]
def envPushL : FunDecl := lfn (vis, q) locals (w, k, z) {
  if vis + 1 == 0 { abort };
  if 4294967295 < q { abort };
  w := EREC.u64[q + 1];
  z := call env_row_set(w, vis + 1, q);
  k := CTL.u64[128];
  if k + 1 == 0 { abort };
  ECON.u64[k] := q;
  CTL.u64[128] := k + 1;
  return vis + 1
}

/-- **`env_push` refines `IFEnv.push`**: on a return the new view `vis + 1` relates the pushed
environment. `q` must hold a record that decodes (the caller built it). -/
@[refines ConRon.Arena.IFEnv.push]
theorem envPush_refines (p : Prog) (hx : p.lookup "env_ix" = some envIxL)
    (hs : p.lookup "env_row_set" = some envRowSetL) (hp : p.lookup "env_push" = some envPushL)
    (n : Nat) (s₀ : St) {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} (vis q : Word)
    (ci : IConstantInfo) (hE : EnvR dn s₀.mem vis fe)
    (hci : decCI (erecP s₀.mem) dn q.toNat = some ci) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "env_push" [vis, q]
    ⦃fun r s' => LocEq s' s₀ ∧ EnvR dn s'.mem (r.headD 0) (fe.push ci); ⊤⦄ := by
  obtain ⟨w, hw1, hw2, -⟩ := decCI_name hci
  have hw1 := erecP_get hw1
  have hw : rdN (s₀.mem.arr64 EREC) (q.toNat + 1) = w := by simp [rdN, hw1]
  have key := fun (hv : vis + 1 ≠ 0) ht hb hk hk1 hc =>
    EnvR.push hE q ci hci hv ht hb hk hk1 hc
  simp only [hw] at key
  have hrc : ∀ (h : q.toNat + 1 < (s₀.mem.arr64 EREC).size), (s₀.mem.arr64 EREC)[q.toNat + 1] = w := by
    intro h; simpa [h] using hw1
  have hra : rowArr w ≠ CTL := by simp only [rowArr, CTL, ArrId]; omega
  have hctl : ∀ c p', (rowSet s₀.mem w c p').arr64 CTL = s₀.mem.arr64 CTL :=
    fun c p' => rowSet_arr _ _ _ _ _ (Ne.symm hra)
  have hcon : rowTag w ≤ 2 → ∀ c p', (rowSet s₀.mem w c p').arr64 ECON = s₀.mem.arr64 ECON :=
    fun ht c p' => rowSet_arr _ _ _ _ _ (by simp only [rowArr, ECON, ArrId]; omega)
  have hrd : ∀ (h : 128 < (s₀.mem.arr64 CTL).size), rdW (s₀.mem.arr64 CTL) 128 = (s₀.mem.arr64 CTL)[128] :=
    fun h => rdW_eq _ _ 128 rfl h
  simp only [envPushMem, hw, hctl] at key
  have hq1 : ¬ (4294967295 : Word) < q → (q + 1).toNat = q.toNat + 1 := by
    intro h; have : q.toNat ≤ 4294967295 := by
      have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp h); simpa using this
    rw [UInt64.toNat_add]; simp; omega
  rw [invoke_eq _ hp]
  simp only [callFn, envPushL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        envRowSet_spec p hx hs n] <;>
      finish

/-! ## A row write, in general; `env_erase`, `env_pop_temp` -/

/-- **A row write**: the rows of the other names stay, the written row is `R`. -/
theorem EnvR.setRow {dn : NIdx → Option ConLeche.Name} {m : Mem} {vis : Word} {fe : IFEnv}
    (h : EnvR dn m vis fe) (w c q : Word) (hw2 : w.toNat < 2 ^ 32) (ht : rowTag w ≤ 2)
    (hb : rowIx w + 1 < (m.arr64 (rowArr w)).size)
    (idx' : Std.HashMap NIdx (Nat × IConstantInfo)) (R : Option (Nat × IConstantInfo))
    (hidx : ∀ n : NIdx, idx'[n]? = if n.word.toUInt64 = w then R else fe.idx[n]?)
    (hR1 : R.map Prod.fst = if c = 0 then none else some (c.toNat - 1))
    (hR2 : c ≠ 0 → R.map Prod.snd = decCI (erecP m) dn q.toNat) :
    EnvR dn (rowSet m w c q) vis ⟨fe.env, idx', fe.visibleBelow, fe.tbls⟩ := by
  have hrr : rowArr w ≠ EREC := by simp only [rowArr, EREC, ArrId]; omega
  have hre : rowArr w ≠ ECON := by simp only [rowArr, ECON, ArrId]; omega
  have hra : rowArr w ≠ CTL := by simp only [rowArr, CTL, ArrId]; omega
  have hE' : erecP (rowSet m w c q) = erecP m :=
    erecP_congr (rowSet_arr _ _ _ _ _ (Ne.symm hrr)) (by rw [rowSet_arr _ _ _ _ _ (Ne.symm hra)])
  refine ⟨h.vis, ?_, ?_, ?_, fun n hn => by rw [tblRow_rowSet m w c q hw2]; exact h.tkeys n hn,
    fun n hn h0 => by rw [tblRow_rowSet m w c q hw2, hE'] at *; exact h.tvals n hn h0,
    by rw [tblCnt_rowSet m w c q hw2, tblHead_rowSet m w c q hw2, hE']; exact h.tables⟩
  · intro n hn
    have e1 := rowC_rowSet (c := c) (p := q) (w' := n.word.toUInt64) hw2 ht hb hn
    have e2 := rowP_rowSet (c := c) (p := q) (w' := n.word.toUInt64) hw2 ht hb hn
    simp only [hidx]
    by_cases e : n.word.toUInt64 = w
    · simp only [e, ite_true] at e1 e2 ⊢
      rw [hR1]; simp only [rowW, e1, e2]; split <;> simp
    · simp only [e, ite_false] at e1 e2 ⊢
      rw [h.keys n hn]; simp only [rowW, e1, e2]
  · intro n hn h0
    have e1 := rowC_rowSet (c := c) (p := q) (w' := n.word.toUInt64) hw2 ht hb hn
    have e2 := rowP_rowSet (c := c) (p := q) (w' := n.word.toUInt64) hw2 ht hb hn
    simp only [hidx, hE']
    by_cases e : n.word.toUInt64 = w
    · simp only [e, ite_true] at e1 e2 h0 ⊢
      rw [e2]; exact hR2 (by rwa [e1] at h0)
    · simp only [e, ite_false] at e1 e2 h0 ⊢
      rw [e2]; exact h.vals n hn (by rwa [e1] at h0)
  · rw [← h.consts]
    simp only [envConsts, envLen, hE',
      rowSet_arr _ _ _ _ _ (Ne.symm hre), rowSet_arr _ _ _ _ _ (Ne.symm hra)]

/-- `env_erase(w)`: drop the row of name `w` (one step of `eraseInstalled`). -/
-- con-ron: ConRon/Arena/Promote.lean:343-352 ConRon.Arena.eraseInstalled
def envEraseL : FunDecl := lfn (w) locals (z) {
  z := call env_row_set(w, 0, 0);
  return 0
}

/-- **`env_erase` erases the index row** (`HashMap.erase` at `decI w`). -/
theorem envErase_spec (p : Prog) (hx : p.lookup "env_ix" = some envIxL)
    (hs : p.lookup "env_row_set" = some envRowSetL) (hp : p.lookup "env_erase" = some envEraseL)
    (n : Nat) (s₀ : St) {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} (vis w : Word)
    (hE : EnvR dn s₀.mem vis fe) (hw : w.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "env_erase" [w]
    ⦃fun _ s' => LocEq s' s₀ ∧ EnvR dn s'.mem vis ⟨fe.env, fe.idx.erase (decI w), fe.visibleBelow, fe.tbls⟩; ⊤⦄ := by
  have key := fun ht hb => hE.setRow w 0 0 hw ht hb (fe.idx.erase (decI w)) none
    (fun n => by
      rw [Std.HashMap.getElem?_erase]
      by_cases e : n.word.toUInt64 = w
      · have : decI w = n := (decI_eq_iff w hw n).mpr e.symm
        simp [e, this]
      · have : ¬ decI w = n := fun h' => e ((decI_eq_iff w hw n).mp h').symm
        simp [e, this])
    (by simp) (by simp)
  rw [invoke_eq _ hp]
  simp only [callFn, envEraseL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, envRowSet_spec p hx hs n] <;>
      finish

/-- The memory after `env_pop_temp`'s count update: `CTL[128] - 1` (none at `0`). -/
def popLenMem (m : Mem) : Mem :=
  if rdW (m.arr64 CTL) 128 = 0 then m else m.set64 CTL 128 (rdW (m.arr64 CTL) 128 - 1)

/-- The view after a pop: `vis - 1`, `0` at `0`. -/
def popVis (vis : Word) : Word := if vis = 0 then 0 else vis - 1

/-- **The newest constant dropped and the view lowered** (the rest of `popTemp`). -/
theorem EnvR.popLen {dn : NIdx → Option ConLeche.Name} {m : Mem} {vis : Word}
    {env : IEnv} {idx : Std.HashMap NIdx (Nat × IConstantInfo)} {vb : Nat}
    {tbls : Std.HashMap NIdx IProjTable}
    (h : EnvR dn m vis ⟨env, idx, vb, tbls⟩) (hc : 128 < (m.arr64 CTL).size) :
    EnvR dn (popLenMem m) (popVis vis) ⟨⟨env.consts.tail, env.tables⟩, idx, vb - 1, tbls⟩ := by
  have hframe : ∀ b, b ≠ CTL → (popLenMem m).arr64 b = m.arr64 b := by
    intro b hb; simp only [popLenMem]; split
    · rfl
    · exact Mem.arr64_set64_ne _ _ _ _ _ hb
  have hv := h.vis
  simp only at hv
  have hC : ∀ w, rowC (popLenMem m) w = rowC m w := fun w => by
    unfold rowC; split
    · rw [hframe _ (by simp only [CTL, ArrId, rowArr, rowTier]; omega)]
    · rfl
  have hP : ∀ w, rowP (popLenMem m) w = rowP m w := fun w => by
    unfold rowP; split
    · rw [hframe _ (by simp only [CTL, ArrId, rowArr, rowTier]; omega)]
    · rfl
  have hW : ∀ w, rowW (popLenMem m) w = rowW m w := fun w => by simp only [rowW, hC, hP]
  have hR : erecP (popLenMem m) = erecP m := by
    apply erecP_congr (hframe _ (by decide))
    simp only [popLenMem]; split
    · rfl
    · rw [Mem.arr64_set64_same, rdW_set!]; simp
  have hN : (popLenMem m).arr64 ECON = m.arr64 ECON := hframe _ (by decide)
  have hT : ∀ w, tblRow (popLenMem m) w = tblRow m w := fun w => by
    unfold tblRow; split
    · rw [hframe _ (by simp only [CTL, ArrId, rowArr, rowTier]; omega)]
    · rfl
  have hX : (popLenMem m).arr64 EIXA = m.arr64 EIXA := hframe _ (by decide)
  refine ⟨?_, fun n hn => (hW _).symm ▸ h.keys n hn, fun n hn h0 => ?_, ?_,
    fun n hn => (hT _).symm ▸ h.tkeys n hn,
    fun n hn h0 => by rw [hT, hR] at *; exact h.tvals n hn h0,
    by simp only [tblCnt, tblHead, hX, hR]; exact h.tables⟩
  · simp only [popVis, hv]; split
    · simp_all
    · rename_i h0; rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr ?_)]
      · simp
      · have : vis.toNat ≠ 0 := fun h' => h0 (UInt64.toNat_inj.mp (by simpa using h'))
        simp; omega
  · rw [hP, hR]; exact h.vals n hn (by rwa [← hC])
  · have hcs := h.consts
    simp only [envConsts] at hcs ⊢
    rw [hR, hN]
    by_cases hk : rdW (m.arr64 CTL) 128 = 0
    · have hl : envLen m = 0 := by simp [envLen, hk]
      have hl' : envLen (popLenMem m) = 0 := by simp [popLenMem, hk, envLen]
      rw [hl] at hcs; rw [hl']
      simp at hcs ⊢; simp [hcs]
    · have hl' : envLen (popLenMem m) = envLen m - 1 := by
        have e : popLenMem m = m.set64 CTL 128 (rdW (m.arr64 CTL) 128 - 1) := by
          simp [popLenMem, hk]
        unfold envLen
        rw [e, Mem.arr64_set64_same, rdW_set!]
        simp only [show (128 : Word).toNat = 128 from rfl, hc, and_self, ite_true]
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr ?_)]
        · simp
        · have : (rdW (m.arr64 CTL) 128).toNat ≠ 0 :=
            fun h' => hk (UInt64.toNat_inj.mp (by simpa using h'))
          simp; omega
      have hpos : envLen m ≠ 0 := fun h' => hk (UInt64.toNat_inj.mp (by simpa [envLen] using h'))
      rw [hl']
      obtain ⟨j, hj⟩ : ∃ j, envLen m = j + 1 := ⟨envLen m - 1, by omega⟩
      rw [hj] at hcs; rw [hj, Nat.add_sub_cancel]
      rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.mapM_cons] at hcs
      simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at hcs
      obtain ⟨x, -, rest, hrest, hx⟩ := hcs
      simp only [Option.some.injEq] at hx
      rw [← hx]; simpa using hrest

/-- The previous row of a temporary push, as `env_pop_temp` gets it: `c = 0` is `none`, else
the counter `c - 1` and the record at `q`. -/
def prevD (dn : NIdx → Option ConLeche.Name) (m : Mem) (c q : Word) :
    Option (Option (Nat × IConstantInfo)) :=
  if c = 0 then some none else (decCI (erecP m) dn q.toNat).map fun ci => some (c.toNat - 1, ci)

/-- `env_pop_temp(vis, w, c, q)`: undo a temporary push of name `w`: its row put back to
`(c, q)` (`IFEnv.popTemp`'s `prev`), the newest constant dropped, the view lowered. -/
-- con-ron: ConRon/Arena/Env.lean:280-289 ConRon.Arena.IFEnv.popTemp
-- con-ron: CHANGED since 12752ca7 — `ConRon.Arena.IFEnv.popTemp` changed; re-check the L code and its proofs, then delete this line
@[l_impl ConRon.Arena.IFEnv.popTemp]
def envPopTempL : FunDecl := lfn (vis, w, c, q) locals (k, z) {
  z := call env_row_set(w, c, q);
  k := CTL.u64[128];
  if k != 0 { CTL.u64[128] := k - 1 };
  if vis == 0 { return 0 };
  return vis - 1
}

theorem popIdx_get (idx : Std.HashMap NIdx (Nat × IConstantInfo)) (n0 n : NIdx)
    (prev : Option (Nat × IConstantInfo)) :
    (match prev with
      | some r => idx.insert n0 r
      | none => idx.erase n0)[n]? = if n0 == n then prev else idx[n]? := by
  cases prev with
  | none => simp [Std.HashMap.getElem?_erase]
  | some r => simp [Std.HashMap.getElem?_insert]

/-- **`env_pop_temp` refines `IFEnv.popTemp`**, given the previous row as words that decode. -/
@[refines ConRon.Arena.IFEnv.popTemp]
theorem envPopTemp_refines (p : Prog) (hx : p.lookup "env_ix" = some envIxL)
    (hs : p.lookup "env_row_set" = some envRowSetL)
    (hp : p.lookup "env_pop_temp" = some envPopTempL)
    (n : Nat) (s₀ : St) {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} (vis w c q : Word)
    (prev : Option (Nat × IConstantInfo)) (hE : EnvR dn s₀.mem vis fe) (hw : w.toNat < 2 ^ 32)
    (hprev : prevD dn s₀.mem c q = some prev) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "env_pop_temp" [vis, w, c, q]
    ⦃fun r s' => LocEq s' s₀ ∧ EnvR dn s'.mem (r.headD 0) (fe.popTemp (decI w) prev); ⊤⦄ := by
  have hidx : ∀ n : NIdx, (match prev with
      | some r => fe.idx.insert (decI w) r
      | none => fe.idx.erase (decI w))[n]? = if n.word.toUInt64 = w then prev else fe.idx[n]? := by
    intro n; rw [popIdx_get]
    by_cases e : n.word.toUInt64 = w
    · have : decI w = n := (decI_eq_iff w hw n).mpr e.symm
      simp [e, this]
    · have : ¬ decI w = n := fun h' => e ((decI_eq_iff w hw n).mp h').symm
      simp [e, this]
  have hR1 : prev.map Prod.fst = if c = 0 then none else some (c.toNat - 1) := by
    simp only [prevD] at hprev; split at hprev
    · simp_all
    · rename_i h0
      cases e : decCI (erecP s₀.mem) dn q.toNat with
      | none => simp [e] at hprev
      | some ci =>
        simp only [e, Option.map_some, Option.some.injEq] at hprev; subst hprev; simp [h0]
  have hR2 : c ≠ 0 → prev.map Prod.snd = decCI (erecP s₀.mem) dn q.toNat := by
    intro h0; simp only [prevD, h0, ite_false] at hprev
    cases e : decCI (erecP s₀.mem) dn q.toNat with
    | none => simp [e] at hprev
    | some ci => simp only [e, Option.map_some, Option.some.injEq] at hprev; subst hprev; simp
  have key := fun ht hb hc =>
    (hE.setRow w c q hw ht hb _ prev hidx hR1 hR2).popLen hc
  have hra : rowArr w ≠ CTL := by simp only [rowArr, CTL, ArrId]; omega
  have hctl : (rowSet s₀.mem w c q).arr64 CTL = s₀.mem.arr64 CTL := rowSet_arr _ _ _ _ _ (Ne.symm hra)
  have hrd : ∀ (h : 128 < (s₀.mem.arr64 CTL).size),
      rdW (s₀.mem.arr64 CTL) 128 = (s₀.mem.arr64 CTL)[128] := fun h => rdW_eq _ _ 128 rfl h
  simp only [popLenMem, popVis, hctl] at key
  rw [invoke_eq _ hp]
  simp only [callFn, envPopTempL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        envRowSet_spec p hx hs n] <;>
      finish [IFEnv.popTemp]

/-- **The empty environment** (`mkIFEnv IEnv.empty`, the fold's start) is memory whose rows and
constant count are zero, at view `0` (all-zero memory in particular). -/
theorem EnvR.init {dn : NIdx → Option ConLeche.Name} {m : Mem}
    (hz : ∀ w, rowC m w = 0) (hl : rdW (m.arr64 CTL) 128 = 0) (hzt : ∀ w, tblRow m w = 0)
    (hlt : tblCnt m = 0) :
    EnvR dn m 0 (mkIFEnv IEnv.empty) := by
  refine ⟨rfl, fun n _ => ?_, fun n _ h0 => absurd (hz _) h0, ?_, fun n _ => ?_,
    fun n _ h0 => absurd (hzt _) h0, ?_⟩
  · simp [mkIFEnv, IEnv.empty, mkIFEnvGo, rowW, hz]
  · simp [envConsts, envLen, hl, mkIFEnv, IEnv.empty]
  · simp [mkIFEnv, IEnv.empty, mkIFEnvTblsGo, hzt]
  · simp [hlt, tblList, mkIFEnv, IEnv.empty]

/-! ## The table component: `tbl_row_get`, `tbl_row_set`, `find_table`, `env_push_table`

The table rows sit at word `2^28 + i` of the name's row array (`tblIx`); the tables list's length
and head at words `2^29` and `2^29 + 1` of `EIXA` (`Tiers.lean`, "The table component"). -/

/-- The table row's index as an L expression computes it: `2^28 + (w mod 2^27)`. -/
def tixW (w : Word) : Word := (w &&& 134217727) + 268435456

theorem tixW_toNat (w : Word) : (tixW w).toNat = tblIx w := by
  have h1 : (w &&& 134217727).toNat = w.toNat % 2 ^ 27 := by
    rw [UInt64.toNat_and]
    rw [show (134217727 : UInt64).toNat = 2 ^ 27 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
  rw [tixW, UInt64.toNat_add, h1]; simp [tblIx]; omega

/-- `tbl_ix(w)`: the row array selector (`2 tag + tier`) and the table row's index of `w`. -/
-- con-ron: none — row access of L's table map (the twin's `IFEnv.tbls`)
def tblIxL : FunDecl := lfn (w) locals () {
  return (w >> 27, (w & 134217727) + 268435456)
}

/-- `tbl_row_get(w)`: the table row of name handle `w` (the table record's pointer plus one, `0`
for none). -/
-- con-ron: none — row access of L's table map (the twin's `IFEnv.tbls`)
def tblRowGetL : FunDecl := lfn (w) locals (g, ix) {
  (g, ix) := call tbl_ix(w);
  if g == 0 { return EIXA.u64[ix] };
  if g == 1 { return EIXA1.u64[ix] };
  if g == 2 { return EIXS.u64[ix] };
  if g == 3 { return EIXS1.u64[ix] };
  if g == 4 { return EIXN.u64[ix] };
  if g == 5 { return EIXN1.u64[ix] };
  abort
}

/-- `tbl_row_set(w, v)`: write the table row of name handle `w`. -/
-- con-ron: none — row access of L's table map (the twin's `IFEnv.tbls`)
def tblRowSetL : FunDecl := lfn (w, v) locals (g, ix) {
  (g, ix) := call tbl_ix(w);
  if g == 0 { EIXA.u64[ix] := v; return 0 };
  if g == 1 { EIXA1.u64[ix] := v; return 0 };
  if g == 2 { EIXS.u64[ix] := v; return 0 };
  if g == 3 { EIXS1.u64[ix] := v; return 0 };
  if g == 4 { EIXN.u64[ix] := v; return 0 };
  if g == 5 { EIXN1.u64[ix] := v; return 0 };
  abort
}

/-- The memory after `tbl_row_set(w, v)`. -/
def tblSet (m : Mem) (w v : Word) : Mem := m.set64 (rowArr w) (tixW w) v

section specs
variable (p : Prog)

theorem tblIx_spec (hp : p.lookup "tbl_ix" = some tblIxL) (n : Nat) (s₀ : St) (w : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "tbl_ix" [w]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ r.headD 0 = rowSelW w ∧ r.tail.headD 0 = tixW w; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, tblIxL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs] <;>
      simp_all [rowSelW, tixW, LocEq, BinOp.eval, Sig.retVal, Sig.retOr, Locals.init]

theorem tblRowGet_spec (hx : p.lookup "tbl_ix" = some tblIxL)
    (hp : p.lookup "tbl_row_get" = some tblRowGetL) (n : Nat) (s₀ : St)
    (w : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "tbl_row_get" [w]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ rowTag w ≤ 2 ∧ r.headD 0 = tblRow s₀.mem w; ⊤⦄ := by
  have ht := rowSelW_toNat w
  have htr : rowTier w < 2 := Nat.mod_lt _ (by decide)
  have hi := tixW_toNat w
  have hc : ∀ k, rowTag w + 8 * rowTier w = k → rowTag w ≤ 2 →
      tblRow s₀.mem w = rdN (s₀.mem.arr64 (132 + k)) (tblIx w) := by
    intro k hk hk2; subst hk
    rw [tblRow_eq _ _ hk2, rowArr, Nat.add_assoc]
  have hrd : ∀ (a : Array Word) (k : Nat) (h : k < a.size), rdN a k = a[k] := by
    intro a k h; simp [rdN, h]
  rw [invoke_eq _ hp]
  simp only [callFn, tblRowGetL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, tblIx_spec p hx n] <;>
      finish

theorem tblRowSet_spec (hx : p.lookup "tbl_ix" = some tblIxL)
    (hp : p.lookup "tbl_row_set" = some tblRowSetL) (n : Nat) (s₀ : St)
    (w v : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "tbl_row_set" [w, v]
    ⦃fun _ s' => s'.mem = tblSet s₀.mem w v ∧ LocEq s' s₀ ∧ rowTag w ≤ 2 ∧
      tblIx w < (s₀.mem.arr64 (rowArr w)).size; ⊤⦄ := by
  have ht := rowSelW_toNat w
  have htr : rowTier w < 2 := Nat.mod_lt _ (by decide)
  have hi := tixW_toNat w
  have ha : ∀ k, rowTag w + 8 * rowTier w = k → rowArr w = 132 + k := by
    intro k hk; simp only [rowArr, ArrId]; omega
  rw [invoke_eq _ hp]
  simp only [callFn, tblRowSetL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, tblIx_spec p hx n] <;>
      finish [tblSet]

end specs

/-! ### The relation across table writes -/

theorem toNat_succ_of_ne' (x : Word) (h : x + 1 ≠ 0) : (x + 1).toNat = x.toNat + 1 := by
  have hl := x.toNat_lt
  have hx : x.toNat + 1 < 2 ^ 64 := by
    rcases Nat.lt_or_ge (x.toNat + 1) (2 ^ 64) with h' | h'
    · exact h'
    · exfalso; apply h; apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add]; simp; omega
  rw [UInt64.toNat_add]; simp; omega

theorem tblIx_inj {w w' : Word} (ht : rowTag w ≤ 2) (ht' : rowTag w' ≤ 2)
    (ha : rowArr w = rowArr w') (hi : tblIx w = tblIx w') : w = w' :=
  rowIx_inj ht ht' ha (by simp only [tblIx, rowIx] at hi ⊢; omega)

/-- A write at a word from `2^28` up leaves every constant row. -/
theorem rowC_set_hi (m : Mem) (a : ArrId) (k v : Word) (hk : 2 ^ 28 ≤ k.toNat) (w : Word) :
    rowC (m.set64 a k v) w = rowC m w := by
  unfold rowC; split
  · have := rdN_set64 m a (rowArr w) k v (rowIx w)
    simp only [rdN] at this; rw [this, if_neg (by simp only [rowIx]; omega)]
  · rfl

theorem rowP_set_hi (m : Mem) (a : ArrId) (k v : Word) (hk : 2 ^ 28 ≤ k.toNat) (w : Word) :
    rowP (m.set64 a k v) w = rowP m w := by
  unfold rowP; split
  · have := rdN_set64 m a (rowArr w) k v (rowIx w + 1)
    simp only [rdN] at this; rw [this, if_neg (by simp only [rowIx]; omega)]
  · rfl

/-- A write to a row array leaves `erecP`, `ECON` and `CTL`. -/
theorem erecP_set_row (m : Mem) (a : ArrId) (k v : Word) (ha : a = 132 ∨ a = 133 ∨ a = 134 ∨
    a = 140 ∨ a = 141 ∨ a = 142) : erecP (m.set64 a k v) = erecP m :=
  erecP_congr (Mem.arr64_set64_ne _ _ _ _ _ (by rcases ha with h | h | h | h | h | h <;> subst h <;> decide))
    (by rw [Mem.arr64_set64_ne _ _ _ _ _ (by rcases ha with h | h | h | h | h | h <;> subst h <;> decide)])

theorem rowArr_cases (w : Word) (ht : rowTag w ≤ 2) : rowArr w = 132 ∨ rowArr w = 133 ∨
    rowArr w = 134 ∨ rowArr w = 140 ∨ rowArr w = 141 ∨ rowArr w = 142 := by
  have : rowTier w < 2 := Nat.mod_lt _ (by decide)
  simp only [rowArr, ArrId]; omega

/-- The memory after `env_push_table(q)`: the table row of the record's structure name, then the
list's length and head. -/
def tblPushMem (m : Mem) (q : Word) : Mem :=
  let w := rdN (m.arr64 EREC) (q.toNat + 2)
  let m1 := tblSet m w (q + 1)
  let k := rdN (m1.arr64 EIXA) (2 ^ 29)
  (m1.set64 EIXA 536870912 (k + 1)).set64 EIXA 536870913 (q + 1)

theorem decTbl_name {a : Array Word} {p : Nat} {t : IProjTable} (h : decTbl a p = some t) :
    ∃ w, a[p + 2]? = some w ∧ w.toNat < 2 ^ 32 ∧ t.structName = decI w := by
  simp only [decTbl, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨n, hn, _, _, _, _, _, _, _, _, _, _, _, _, _, _, e⟩ := h
  cases e
  exact hd?_some hn

/-- **`pushTable`**: the record at `q` (which decodes to `t` and links the old head) becomes the
newest table, its structure's row points at it. -/
theorem EnvR.pushTable {dn : NIdx → Option ConLeche.Name} {m : Mem} {vis : Word} {fe : IFEnv}
    (h : EnvR dn m vis fe) (q : Word) (t : IProjTable) (hq : q.toNat < 2 ^ 32)
    (ht : decTbl (erecP m) q.toNat = some t)
    (hl : nat? (erecP m) (q.toNat + 1) = some (tblHead m))
    (hw : rowTag (rdN (m.arr64 EREC) (q.toNat + 2)) ≤ 2)
    (hb : tblIx (rdN (m.arr64 EREC) (q.toNat + 2)) <
      (m.arr64 (rowArr (rdN (m.arr64 EREC) (q.toNat + 2)))).size)
    (hk1 : rdN (m.arr64 EIXA) (2 ^ 29) + 1 ≠ 0) (hs : 2 ^ 29 + 1 < (m.arr64 EIXA).size) :
    EnvR dn (tblPushMem m q) vis (fe.pushTable t) := by
  obtain ⟨w, hw1, hw2, hname⟩ := decTbl_name ht
  have hwd : rdN (m.arr64 EREC) (q.toNat + 2) = w := by simp [rdN, erecP_get hw1]
  rw [hwd] at hw hb
  have hra := rowArr_cases w hw
  have hixw : (tixW w).toNat = tblIx w := tixW_toNat w
  have hhi : 2 ^ 28 ≤ (tixW w).toNat := by rw [hixw]; simp only [tblIx]; omega
  have h29 : (536870912 : Word).toNat = 2 ^ 29 := rfl
  have h29' : (536870913 : Word).toNat = 2 ^ 29 + 1 := rfl
  have hq1 : (q + 1).toNat = q.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  -- the three writes
  generalize hm1 : tblSet m w (q + 1) = m1
  have hk : rdN (m1.arr64 EIXA) (2 ^ 29) = rdN (m.arr64 EIXA) (2 ^ 29) := by
    rw [← hm1]; simp only [tblSet, rdN_set64]; rw [if_neg (by rw [hixw]; simp only [tblIx]; omega)]
  have hM : tblPushMem m q = (m1.set64 EIXA 536870912 (rdN (m.arr64 EIXA) (2 ^ 29) + 1)).set64 EIXA 536870913 (q + 1) := by
    simp only [tblPushMem, hwd, hm1, hk]
  rw [hM]
  have hC : ∀ w', rowC ((m1.set64 EIXA 536870912 (rdN (m.arr64 EIXA) (2 ^ 29) + 1)).set64 EIXA 536870913 (q + 1)) w' = rowC m w' := by
    intro w'
    rw [rowC_set_hi _ _ _ _ (by rw [h29']; omega), rowC_set_hi _ _ _ _ (by rw [h29]; omega),
      ← hm1, tblSet, rowC_set_hi _ _ _ _ hhi]
  have hP : ∀ w', rowP ((m1.set64 EIXA 536870912 (rdN (m.arr64 EIXA) (2 ^ 29) + 1)).set64 EIXA 536870913 (q + 1)) w' = rowP m w' := by
    intro w'
    rw [rowP_set_hi _ _ _ _ (by rw [h29']; omega), rowP_set_hi _ _ _ _ (by rw [h29]; omega),
      ← hm1, tblSet, rowP_set_hi _ _ _ _ hhi]
  have hW : ∀ w', rowW ((m1.set64 EIXA 536870912 (rdN (m.arr64 EIXA) (2 ^ 29) + 1)).set64 EIXA 536870913 (q + 1)) w' = rowW m w' :=
    fun w' => by simp only [rowW, hC, hP]
  have hR : erecP ((m1.set64 EIXA 536870912 (rdN (m.arr64 EIXA) (2 ^ 29) + 1)).set64 EIXA 536870913 (q + 1)) = erecP m := by
    rw [erecP_set_row _ _ _ _ (by decide), erecP_set_row _ _ _ _ (by decide), ← hm1, tblSet,
      erecP_set_row _ _ _ _ hra]
  have hN : ∀ b, b ≠ EIXA → b ≠ rowArr w →
      ((m1.set64 EIXA 536870912 (rdN (m.arr64 EIXA) (2 ^ 29) + 1)).set64 EIXA 536870913 (q + 1)).arr64 b = m.arr64 b := by
    intro b h1 h2
    rw [Mem.arr64_set64_ne _ _ _ _ _ h1, Mem.arr64_set64_ne _ _ _ _ _ h1, ← hm1, tblSet,
      Mem.arr64_set64_ne _ _ _ _ _ h2]
  have hT : ∀ w', rowTag w' ≤ 2 →
      tblRow ((m1.set64 EIXA 536870912 (rdN (m.arr64 EIXA) (2 ^ 29) + 1)).set64 EIXA 536870913 (q + 1)) w' =
        if w' = w then q + 1 else tblRow m w' := by
    intro w' ht'
    rw [tblRow_eq _ _ ht', tblRow_eq _ _ ht']
    rw [rdN_set64, if_neg (by rw [h29']; simp only [tblIx]; omega), rdN_set64,
      if_neg (by rw [h29]; simp only [tblIx]; omega), ← hm1, tblSet, rdN_set64, hixw]
    by_cases e : w' = w
    · subst e; simp [hb]
    · rw [if_neg e, if_neg]
      rintro ⟨h1, h2, -⟩
      exact e (tblIx_inj ht' hw h1 h2.symm)
  have hname' : ∀ n : NIdx, (t.structName == n) = decide (n.word.toUInt64 = w) := by
    intro n; rw [hname]
    by_cases e : n.word.toUInt64 = w
    · subst e; simp [decI_word]
    · have : decI w ≠ n := fun h' => e ((decI_eq_iff w hw2 n).mp h').symm
      simp [e, this]
  refine ⟨h.vis, fun n hn => (hW _).symm ▸ h.keys n hn, fun n hn h0 => ?_, ?_, fun n hn => ?_,
    fun n hn h0 => ?_, ?_⟩
  · rw [hP, hR]; exact h.vals n hn (by rwa [← hC])
  · simp only [IFEnv.pushTable]; rw [← h.consts]
    simp only [envConsts, envLen, hR, hN ECON (by decide) (by rcases hra with h | h | h | h | h | h <;> rw [h] <;> decide),
      hN CTL (by decide) (by rcases hra with h | h | h | h | h | h <;> rw [h] <;> decide)]
  · simp only [IFEnv.pushTable, Std.HashMap.getElem?_insert, hname', hT _ hn]
    by_cases e : n.word.toUInt64 = w
    · simp only [e, decide_true, ite_true, Option.isSome_some]
      have : q + 1 ≠ 0 := fun h' => by rw [h'] at hq1; simp at hq1
      simp [this]
    · simp only [e, decide_false, ite_false]; exact h.tkeys n hn
  · rw [hT _ hn] at h0 ⊢; rw [hR]
    simp only [IFEnv.pushTable, Std.HashMap.getElem?_insert, hname']
    by_cases e : n.word.toUInt64 = w
    · simp only [e, decide_true, ite_true, hq1, Nat.add_sub_cancel]; exact ht.symm
    · simp only [e, decide_false, ite_false] at h0 ⊢; exact h.tvals n hn h0
  · have hcnt : tblCnt ((m1.set64 EIXA 536870912 (rdN (m.arr64 EIXA) (2 ^ 29) + 1)).set64 EIXA 536870913 (q + 1)) = tblCnt m + 1 := by
      have hsz : 2 ^ 29 < (m1.arr64 EIXA).size := by
        rw [← hm1, tblSet, size_set64]; omega
      have hval := toNat_succ_of_ne' _ hk1
      have e : tblCnt ((m1.set64 EIXA 536870912 (rdN (m.arr64 EIXA) (2 ^ 29) + 1)).set64 EIXA 536870913 (q + 1)) =
          (rdN (((m1.set64 EIXA 536870912 (rdN (m.arr64 EIXA) (2 ^ 29) + 1)).set64 EIXA 536870913 (q + 1)).arr64 EIXA) (2 ^ 29)).toNat := rfl
      rw [e, rdN_set64, if_neg (fun h' => by rw [h29'] at h'; omega), rdN_set64,
        if_pos ⟨rfl, h29, hsz⟩, hval]
      rfl
    have hhead : tblHead ((m1.set64 EIXA 536870912 (rdN (m.arr64 EIXA) (2 ^ 29) + 1)).set64 EIXA 536870913 (q + 1)) = q.toNat + 1 := by
      have hsz : 2 ^ 29 + 1 < ((m1.set64 EIXA 536870912 (rdN (m.arr64 EIXA) (2 ^ 29) + 1)).arr64 EIXA).size := by
        rw [Mem.size_arr64_set64, ← hm1, tblSet, size_set64]; omega
      have e : tblHead ((m1.set64 EIXA 536870912 (rdN (m.arr64 EIXA) (2 ^ 29) + 1)).set64 EIXA 536870913 (q + 1)) =
          (rdN (((m1.set64 EIXA 536870912 (rdN (m.arr64 EIXA) (2 ^ 29) + 1)).set64 EIXA 536870913 (q + 1)).arr64 EIXA) (2 ^ 29 + 1)).toNat := rfl
      rw [e, rdN_set64, if_pos ⟨rfl, h29', hsz⟩, hq1]
    rw [hcnt, hhead, hR]
    simp only [tblList, Nat.add_sub_cancel, Option.bind_eq_bind, ht, hl, h.tables,
      show q.toNat + 1 ≠ 0 by omega, ite_false, Option.bind_some, IFEnv.pushTable]
    rfl

/-- A present row decodes. -/
theorem EnvR.decCI_isSome {dn : NIdx → Option ConLeche.Name} {m : Mem} {vis : Word} {fe : IFEnv}
    (h : EnvR dn m vis fe) (w : Word) (hw : w.toNat < 2 ^ 32) (ht : rowTag w ≤ 2)
    (h0 : rowC m w ≠ 0) : (decCI (erecP m) dn (rowP m w).toNat).isSome := by
  have hk := h.keys (decI w) (by rwa [decI_word_self w hw])
  have hv := h.vals (decI w) (by rwa [decI_word_self w hw])
  rw [decI_word_self w hw] at hk hv
  have hv := hv h0
  simp only [rowW, h0, ite_false, Option.map_some] at hk
  cases e : fe.idx[(decI w : NIdx)]? with
  | none => simp [e] at hk
  | some r => rw [e] at hv; rw [← hv]; simp

/-- What a table row word decodes to: `0` is `none`, else the record at the word minus one. -/
def tblOut (m : Mem) (r : Word) : Option IProjTable :=
  if r = 0 then none else decTbl (erecP m) (r.toNat - 1)

/-- A present table row decodes. -/
theorem EnvR.tblOut_isSome {dn : NIdx → Option ConLeche.Name} {m : Mem} {vis : Word} {fe : IFEnv}
    (h : EnvR dn m vis fe) (w : Word) (hw : w.toNat < 2 ^ 32) (ht : rowTag w ≤ 2)
    (h0 : tblRow m w ≠ 0) : (tblOut m (tblRow m w)).isSome := by
  have hk := h.tkeys (decI w) (by rwa [decI_word_self w hw])
  have hv := h.tvals (decI w) (by rwa [decI_word_self w hw])
  rw [decI_word_self w hw] at hk hv
  have hv := hv h0
  have hk' : (fe.tbls[(decI w : NIdx)]?).isSome = true := by rw [hk]; simpa using h0
  unfold tblOut; rw [if_neg h0, ← hv]; exact hk'

/-- **The table lookup** at view `vis`: the table row of `T` if the constant `T` is visible, else
`0` (a table is visible exactly where its structure is). -/
theorem EnvR.findTable?_eq {dn : NIdx → Option ConLeche.Name} {m : Mem} {vis : Word} {fe : IFEnv}
    (h : EnvR dn m vis fe) (w : Word) (hw : w.toNat < 2 ^ 32) (ht : rowTag w ≤ 2) :
    fe.findTable? (decI w) = if rowC m w = 0 then none
      else if (rowC m w).toNat - 1 < vis.toNat then tblOut m (tblRow m w) else none := by
  have hf := h.find?_eq w hw ht
  have hk := h.tkeys (decI w) (by rwa [decI_word_self w hw])
  have hv := h.tvals (decI w) (by rwa [decI_word_self w hw])
  rw [decI_word_self w hw] at hk hv
  have hraw : fe.rawTable? (decI w) = tblOut m (tblRow m w) := by
    simp only [IFEnv.rawTable?, tblOut]
    by_cases e0 : tblRow m w = 0
    · simp only [e0, bne_self_eq_false] at hk
      simp only [e0, ite_true]
      cases e : fe.tbls[(decI w : NIdx)]? <;> simp_all
    · simp only [e0, ite_false]; exact hv e0
  simp only [IFEnv.findTable?, hf, hraw]
  by_cases e0 : rowC m w = 0
  · simp [e0]
  · simp only [e0, ite_false]
    split
    · have := h.decCI_isSome w hw ht e0
      simp [this]
    · simp

/-- `find_table(vis, t)`: the table row of structure `t` if `t` is visible below `vis`, else `0`
(`IFEnv.findTable?`). -/
-- con-ron: ConRon/Arena/Env.lean:297-301 ConRon.Arena.IFEnv.findTable?
@[l_impl ConRon.Arena.IFEnv.findTable?]
def findTableL : FunDecl := lfn (vis, t) locals (c, q, r) {
  (c, q) := call env_row_get(t);
  if c == 0 { return 0 };
  if c - 1 < vis {
    r := call tbl_row_get(t);
    return r
  };
  return 0
}

/-- **`find_table` refines `IFEnv.findTable?`.** -/
@[refines ConRon.Arena.IFEnv.findTable?]
theorem findTable_refines (p : Prog) (hx : p.lookup "env_ix" = some envIxL)
    (hg : p.lookup "env_row_get" = some envRowGetL) (htx : p.lookup "tbl_ix" = some tblIxL)
    (htg : p.lookup "tbl_row_get" = some tblRowGetL) (hp : p.lookup "find_table" = some findTableL)
    (n : Nat) (s₀ : St) {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} (vis w : Word)
    (hE : EnvR dn s₀.mem vis fe) (hw : w.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "find_table" [vis, w]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧
      fe.findTable? (decI w) = tblOut s₀.mem (r.headD 0) ∧
      (r.headD 0 ≠ 0 → (tblOut s₀.mem (r.headD 0)).isSome); ⊤⦄ := by
  have key := EnvR.findTable?_eq hE w hw
  have key2 := EnvR.tblOut_isSome hE w hw
  have h0 : tblOut s₀.mem 0 = none := by simp [tblOut]
  rw [invoke_eq _ hp]
  simp only [callFn, findTableL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, envRowGet_spec p hx hg n,
        tblRowGet_spec p htx htg n] <;>
      finish

/-- `env_push_table(q)`: install the table record at `q` (its structure name is word `q + 2`,
its link word `q + 1` already holds the old head): its structure's table row, the list's length
and head (`IFEnv.pushTable`). -/
-- con-ron: ConRon/Arena/Env.lean:273-278 ConRon.Arena.IFEnv.pushTable
@[l_impl ConRon.Arena.IFEnv.pushTable]
def envPushTableL : FunDecl := lfn (q) locals (w, k, z) {
  if 4294967295 < q { abort };
  w := EREC.u64[q + 2];
  z := call tbl_row_set(w, q + 1);
  k := EIXA.u64[536870912];
  if k + 1 == 0 { abort };
  EIXA.u64[536870912] := k + 1;
  EIXA.u64[536870913] := q + 1;
  return 0
}

/-- **`env_push_table` refines `IFEnv.pushTable`**, for a record that decodes and links the old
head. -/
@[refines ConRon.Arena.IFEnv.pushTable]
theorem envPushTable_refines (p : Prog) (htx : p.lookup "tbl_ix" = some tblIxL)
    (hs : p.lookup "tbl_row_set" = some tblRowSetL)
    (hp : p.lookup "env_push_table" = some envPushTableL)
    (n : Nat) (s₀ : St) {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} (vis q : Word)
    (t : IProjTable) (hE : EnvR dn s₀.mem vis fe)
    (ht : decTbl (erecP s₀.mem) q.toNat = some t)
    (hl : nat? (erecP s₀.mem) (q.toNat + 1) = some (tblHead s₀.mem)) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "env_push_table" [q]
    ⦃fun _ s' => LocEq s' s₀ ∧ EnvR dn s'.mem vis (fe.pushTable t); ⊤⦄ := by
  obtain ⟨w, hw1, hw2, -⟩ := decTbl_name ht
  have hw1 := erecP_get hw1
  have hw : rdN (s₀.mem.arr64 EREC) (q.toNat + 2) = w := by simp [rdN, hw1]
  have key := fun (hq : q.toNat < 2 ^ 32) hrt hb hk1 hsz => EnvR.pushTable hE q t hq ht hl hrt hb hk1 hsz
  simp only [hw, tblPushMem, show (2 : Nat) ^ 29 = 536870912 from rfl,
    show (2 : Nat) ^ 29 + 1 = 536870913 from rfl] at key
  have hkk : ∀ v, rdN ((tblSet s₀.mem w v).arr64 EIXA) 536870912 = rdN (s₀.mem.arr64 EIXA) 536870912 := by
    intro v; simp only [tblSet, rdN_set64]
    rw [if_neg (by rw [tixW_toNat]; simp only [tblIx]; omega)]
  have hksz : ∀ v, ((tblSet s₀.mem w v).arr64 EIXA).size = (s₀.mem.arr64 EIXA).size := by
    intro v; simp only [tblSet, size_set64]
  simp only [hkk] at key
  have hq2 : ¬ (4294967295 : Word) < q → (q + 2).toNat = q.toNat + 2 := by
    intro h; have : q.toNat ≤ 4294967295 := by
      have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp h); simpa using this
    rw [UInt64.toNat_add]; simp; omega
  have hqlt : ¬ (4294967295 : Word) < q → q.toNat < 2 ^ 32 := by
    intro h; have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp h); simp at this; omega
  have hrc : ∀ (h : q.toNat + 2 < (s₀.mem.arr64 EREC).size), (s₀.mem.arr64 EREC)[q.toNat + 2] = w := by
    intro h; simpa [h] using hw1
  have hra : rowTag w ≤ 2 → rowArr w ≠ EREC := fun ht => by simp only [rowArr, EREC, ArrId]; omega
  have hsetE : ∀ v, rowTag w ≤ 2 → (tblSet s₀.mem w v).arr64 EREC = s₀.mem.arr64 EREC :=
    fun v ht => Mem.arr64_set64_ne _ _ _ _ _ (hra ht).symm
  have hrd : ∀ (a : Array Word) (k : Nat) (h : k < a.size), rdN a k = a[k] := by
    intro a k h; simp [rdN, h]
  rw [invoke_eq _ hp]
  simp only [callFn, envPushTableL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        tblRowSet_spec p htx hs n] <;>
      finish

/-! ### The tables list's length and head

The only access to the two words of `EIXA` that hold the tables list's length and head
(`tblCnt`, `tblHead`): the install (`check_struct_proj_table`) links the old head, the promotion
(`promote_new_tables`) and the fold's step (`install_step`) read the length and move the head. -/

/-- `tbl_cnt()`: the number of tables (`IEnv.tables.length`). -/
-- con-ron: none — the length of L's tables list (the twin's `IEnv.tables.length`)
def tblCntL : FunDecl := lfn () locals () {
  return EIXA.u64[536870912]
}

/-- `tbl_head()`: the tables list's head (the newest table's pointer plus one, `0` for none). -/
-- con-ron: none — the head of L's tables list (the twin's `IEnv.tables`)
def tblHeadL : FunDecl := lfn () locals () {
  return EIXA.u64[536870913]
}

/-- `tbl_head_set(h)`: the tables list's head set to `h`. -/
-- con-ron: none — the head of L's tables list (the twin's `IEnv.tables`)
def tblHeadSetL : FunDecl := lfn (h) locals () {
  EIXA.u64[536870913] := h;
  return 0
}

section specs
variable (p : Prog)

theorem tblCnt_spec (hp : p.lookup "tbl_cnt" = some tblCntL) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "tbl_cnt" []
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ 2 ^ 29 < (s₀.mem.arr64 EIXA).size ∧
      r.headD 0 = rdN (s₀.mem.arr64 EIXA) (2 ^ 29); ⊤⦄ := by
  have hrd : ∀ (a : Array Word) (k : Nat) (h : k < a.size), rdN a k = a[k] := by
    intro a k h; simp [rdN, h]
  rw [invoke_eq _ hp]
  simp only [callFn, tblCntL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish

theorem tblHead_spec (hp : p.lookup "tbl_head" = some tblHeadL) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "tbl_head" []
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ 2 ^ 29 + 1 < (s₀.mem.arr64 EIXA).size ∧
      r.headD 0 = rdN (s₀.mem.arr64 EIXA) (2 ^ 29 + 1); ⊤⦄ := by
  have hrd : ∀ (a : Array Word) (k : Nat) (h : k < a.size), rdN a k = a[k] := by
    intro a k h; simp [rdN, h]
  rw [invoke_eq _ hp]
  simp only [callFn, tblHeadL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish

theorem tblHeadSet_spec (hp : p.lookup "tbl_head_set" = some tblHeadSetL) (n : Nat) (s₀ : St)
    (h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "tbl_head_set" [h]
    ⦃fun _ s' => s'.mem = s₀.mem.set64 EIXA 536870913 h ∧ LocEq s' s₀ ∧
      2 ^ 29 + 1 < (s₀.mem.arr64 EIXA).size; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, tblHeadSetL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64] <;>
      finish

end specs

/-! ## The program and its write set -/

/-- The environment functions. -/
def envProg : Prog :=
  [("env_ix", envIxL), ("env_row_get", envRowGetL), ("env_row_set", envRowSetL),
   ("env_find", envFindL), ("env_push", envPushL), ("env_erase", envEraseL),
   ("env_pop_temp", envPopTempL), ("tbl_ix", tblIxL), ("tbl_row_get", tblRowGetL), ("tbl_row_set", tblRowSetL),
   ("find_table", findTableL), ("env_push_table", envPushTableL), ("tbl_cnt", tblCntL),
   ("tbl_head", tblHeadL), ("tbl_head_set", tblHeadSetL)]

/- Push the axiom record at `EREC[0]` (name `0x10000005`, a `str` name) at counter 0, then find
it in view 1 and miss it in view 0. -/
#guard
  let m : Mem := { words := (Array.replicate 132 (Array.replicate 140 0)) ++
    #[Array.replicate 8 0, Array.replicate 32 0, Array.replicate 8 0, Array.replicate 4 0,
      #[0, 0x10000005, 0, 0, 0, 0, 0, 0]] }
  match run envProg 100 "env_push" [0, 0] m with
  | .ok (r, m) =>
    r == [1] &&
    (match run envProg 100 "env_find" [0x10000005, 1] m, run envProg 100 "env_find" [0x10000005, 0] m with
      | .ok (r1, _), .ok (r0, _) => r1 == [1, 0] && r0 == [0, 0]
      | _, _ => false)
  | .error _ => false

end L.Arena
