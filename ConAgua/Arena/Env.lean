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
  if f = 0 then none else decCI (m.arr64 EREC) dn q.toNat

section rel
variable {dn : NIdx → Option ConLeche.Name} {m : Mem} {vis : Word} {fe : IFEnv}

/-- **`find?` through the rows.** -/
theorem EnvR.find?_eq (h : EnvR dn m vis fe) (w : Word) (hw : w.toNat < 2 ^ 32)
    (ht : rowTag w ≤ 2) :
    fe.find? (decI w) = if rowC m w = 0 then none
      else if (rowC m w).toNat - 1 < vis.toNat then decCI (m.arr64 EREC) dn (rowP m w).toNat
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

/-- A view of the same index: `restrictTo` is the view word alone. -/
theorem EnvR.restrictTo (h : EnvR dn m vis fe) (k : Word) :
    EnvR dn m k (fe.restrictTo k.toNat) :=
  ⟨rfl, h.keys, h.vals, h.consts⟩

end rel

/-! ## `env_find` -/

/-- `env_find(w, vis)`: `(1, record)` if name `w` has a row below the view `vis`, else `(0, 0)`. -/
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
  · simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨t, ht, h⟩ := h
    subst h
    simp only [decTbl, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at ht
    obtain ⟨n, hn, ht⟩ := ht
    repeat (obtain ⟨_, _, ht⟩ := ht)
    obtain ⟨w, h1, h2, h3⟩ := hd?_some hn
    exact ⟨w, h1, h2, h3⟩
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
    (hci : decCI (m.arr64 EREC) dn q.toNat = some ci) (hv : vis + 1 ≠ 0)
    (ht : rowTag (rdN (m.arr64 EREC) (q.toNat + 1)) ≤ 2)
    (hb : rowIx (rdN (m.arr64 EREC) (q.toNat + 1)) + 1 <
      (m.arr64 (rowArr (rdN (m.arr64 EREC) (q.toNat + 1)))).size)
    (hk : (rdW (m.arr64 CTL) 128).toNat < (m.arr64 ECON).size)
    (hk1 : rdW (m.arr64 CTL) 128 + 1 ≠ 0) (hc : 128 < (m.arr64 CTL).size) :
    EnvR dn (envPushMem m vis q) (vis + 1) (fe.push ci) := by
  obtain ⟨w, hw1, hw2, hname⟩ := decCI_name hci
  have hw : rdN (m.arr64 EREC) (q.toNat + 1) = w := by simp [rdN, hw1]
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
    rw [hA _ (by simp only [CTL, ArrId]; omega) (by simp only [ECON, ArrId]; omega)]
  have hP : ∀ w', rowTag w' ≤ 2 → rowP (envPushMem m vis q) w' = rowP (rowSet m w (vis + 1) q) w' := by
    intro w' h'; simp only [rowP, h', ite_true]
    rw [hA _ (by simp only [CTL, ArrId]; omega) (by simp only [ECON, ArrId]; omega)]
  have hR : (envPushMem m vis q).arr64 EREC = m.arr64 EREC := by
    rw [hA _ (by decide) (by decide), rowSet_arr _ _ _ _ _ (Ne.symm hrr)]
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
  refine ⟨?_, ?_, ?_, ?_⟩
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
    rw [mapM_congr' _ (fun c => do decCI (m.arr64 EREC) dn (← nat? (m.arr64 ECON) c))]
    · simp only [Array.set!_eq_setIfInBounds] at hk'
      simp [hk', hci, envLen] at hcs ⊢; rw [hcs]; simp [IFEnv.push, Option.bind]
    · intro c hc'
      simp only [List.mem_reverse, List.mem_range] at hc'
      simp only [nat?, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
      simp [show (rdW (m.arr64 CTL) 128).toNat ≠ c by omega]

/-- `env_push(vis, q)`: install the record at `q` (its name is word `q + 1`) at counter `vis`:
its row, its slot in `ECON`; returns the new view `vis + 1`. -/
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
    (hci : decCI (s₀.mem.arr64 EREC) dn q.toNat = some ci) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "env_push" [vis, q]
    ⦃fun r s' => LocEq s' s₀ ∧ EnvR dn s'.mem (r.headD 0) (fe.push ci); ⊤⦄ := by
  obtain ⟨w, hw1, hw2, -⟩ := decCI_name hci
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

end L.Arena
