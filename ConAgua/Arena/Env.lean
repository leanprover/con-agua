module

public import ConAgua.Arena.Tiers
public import ConAgua.Arena.RecLayout.CVDec
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
meta import ConAgua.Arena.Tiers
meta import ConAgua.Arena.GrindAttr
meta import ConAgua.L.GrindAttr
meta import Std.Tactic.BVDecide.Normalize.BitVec
meta import Std.Tactic.BVDecide.Normalize.Prop
meta import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import ConAgua.Arena.View

@[expose] public section

/-!
# The environment in L: the frozen stream index and a job's own layer

The twin's `IFEnv` (`ConRon/Arena/Env.lean`) is a job's **own layer** (`idx`, `tbls`: what the
job pushed) over the **frozen stream index** (`base : IFBase`, built once by `buildIndex`, read
at the view `below`/`belowRec` of the job's record). In L:

* **The stream index** (`EIXA`/`EIXS`/`EIXN`, `TIXA`/`TIXS`/`TIXN`, untiered: the stream's names
  are persistent, the index is built with the scratch tier off): directly addressed by the name
  handle's index `i`. Constant row: words `2 i`, `2 i + 1` = the counter plus one (`0`: no
  entry) and the record's address; table row: words `2 i`, `2 i + 1` = the record position plus
  one and the table record's address. Written by `build_index` only (a name's first entry
  wins, `insertIfNew`). The view of a job is two control words, `CTL[134]` (`below`, a counter) and
  `CTL[135]` (`belowRec`, a record position), set when the job starts.
* **The own layer** (`OIXA`/`OIXS`/`OIXN`, `OTXA`/`OTXS`/`OTXN`, tiered by the name's tier): the
  same addressing. Constant row: word `2 i` = `CTL[133] · 2^32 + c + 1` (`CTL[133]` the job's stamp) (`c` the push counter;
  `0` or another stamp: no row), word `2 i + 1` the record's address; table row: word `2 i` the
  stamp, `2 i + 1` the table record's address plus one. A job bumps the stamp, so the previous
  job's rows read as absent without being written (the twin's job starts from an empty layer).
  **One destructive layer, several views**: a view is the word `vis`, the number of pushes it
  sees (its own counter); a row with counter `≥ vis` belongs to a later environment. The twin's
  "an empty own index is not hashed into" is `vis = 0`.
* **The records** are `EREC`'s (`EnvRec.lean`): tier 0 the stream index's and the pins', tier 1
  a job's own (`erec_alloc` by the scratch flag).

These are control words rather than globals so that `MemFrame`'s `CTL` clause covers them.

`IEnv`'s two lists (`fe.env`) are not represented: nothing reads them.
-/

namespace L.Arena

/-! ## The own layer's constant rows -/

/-- `env_row_get(w)`: the own layer's raw row of name handle `w` (the twin's `idx[n]?`):
`(c + 1, record)` if the job pushed it at counter `c`, else `(0, 0)`. -/
-- con-ron: none — row access of L's environment table (the twin's `IFEnv.idx`)
@[no_expose] def envRowGetL : FunDecl := lfn (w) locals (g, t, ix, c) {
  g := ⟦w⟧.tag;
  t := ⟦w⟧.tier;
  ix := ⟦w⟧.idx << 1;
  if g == 0 { c := OIXA⟨t⟩[ix]; if c >> 32 != CTL.u64[133] { return (0, 0) };
    return (c & 4294967295, OIXA⟨t⟩[ix + 1]) };
  if g == 1 { c := OIXS⟨t⟩[ix]; if c >> 32 != CTL.u64[133] { return (0, 0) };
    return (c & 4294967295, OIXS⟨t⟩[ix + 1]) };
  if g == 2 { c := OIXN⟨t⟩[ix]; if c >> 32 != CTL.u64[133] { return (0, 0) };
    return (c & 4294967295, OIXN⟨t⟩[ix + 1]) };
  abort
}

/-- `env_row_set(w, c, p)`: the own layer's row of name handle `w` becomes `(c, p)` (`c = 0`:
no row). -/
-- con-ron: none — row access of L's environment table (the twin's `IFEnv.idx`)
@[no_expose] def envRowSetL : FunDecl := lfn (w, c, p) locals (g, t, ix, v) {
  g := ⟦w⟧.tag;
  t := ⟦w⟧.tier;
  ix := ⟦w⟧.idx << 1;
  v := 0;
  if c != 0 { v := (CTL.u64[133] << 32) + c };
  if g == 0 { OIXA⟨t⟩[ix] := v; OIXA⟨t⟩[ix + 1] := p; return 0 };
  if g == 1 { OIXS⟨t⟩[ix] := v; OIXS⟨t⟩[ix + 1] := p; return 0 };
  if g == 2 { OIXN⟨t⟩[ix] := v; OIXN⟨t⟩[ix + 1] := p; return 0 };
  abort
}

/-! ## The stream index's constant rows -/

/-- `base_row_get(w)`: the stream index's row of name handle `w`, `(counter + 1, record)`, or
`(0, 0)`; a scratch name has none. -/
-- con-ron: none — row access of L's stream index (the twin's `IFBase.idx`)
@[no_expose] def baseRowGetL : FunDecl := lfn (w) locals (g, ix) {
  if ⟦w⟧.tier != 0 { return (0, 0) };
  g := ⟦w⟧.tag;
  ix := ⟦w⟧.idx << 1;
  if g == 0 { return (EIXA.u64[ix], EIXA.u64[ix + 1]) };
  if g == 1 { return (EIXS.u64[ix], EIXS.u64[ix + 1]) };
  if g == 2 { return (EIXN.u64[ix], EIXN.u64[ix + 1]) };
  abort
}

/-- `base_row_set(w, c, p)`: the stream index's row of the persistent name handle `w`. -/
-- con-ron: none — row access of L's stream index (the twin's `IFBase.idx`)
@[no_expose] def baseRowSetL : FunDecl := lfn (w, c, p) locals (g, ix) {
  if ⟦w⟧.tier != 0 { abort };
  g := ⟦w⟧.tag;
  ix := ⟦w⟧.idx << 1;
  if g == 0 { EIXA.u64[ix] := c; EIXA.u64[ix + 1] := p; return 0 };
  if g == 1 { EIXS.u64[ix] := c; EIXS.u64[ix + 1] := p; return 0 };
  if g == 2 { EIXN.u64[ix] := c; EIXN.u64[ix + 1] := p; return 0 };
  abort
}

/-! ## Lookup, push, pop -/

/-- `env_find(w, vis)`: `(1, record)` if name `w` is in the view: the own layer's row below
`vis`, else the stream index's row below `CTL[134]`; `(0, 0)` otherwise. -/
-- con-ron: ConRon/Arena/Env.lean:313-317 ConRon.Arena.IFEnv.find?
@[no_expose, l_impl ConRon.Arena.IFEnv.find?]
def envFindL : FunDecl := lfn (w, vis) locals (c, q) {
  if vis != 0 {
    (c, q) := call env_row_get(w);
    if c != 0 { if c - 1 < vis { return (1, q) } }
  };
  (c, q) := call base_row_get(w);
  if c == 0 { return (0, 0) };
  if c - 1 < CTL.u64[134] { return (1, q) };
  return (0, 0)
}

/-- `env_push(vis, q)`: push the record at `q` (its name is word `q + CI.cv + CV.name`) into the own layer at
counter `vis`; returns the new view `vis + 1`. -/
-- con-ron: ConRon/Arena/Env.lean:350-362 ConRon.Arena.IFEnv.push
-- con-ron: CHANGED since 42a08640 — below `ConRon.Arena.IFEnv.push`, `ConRon.Arena.litNameAt` changed; re-check the L code and its proofs, then delete this line
-- con-ron: CHANGED since 42a08640 — `ConRon.Arena.IFEnv.push` changed; re-check the L code and its proofs, then delete this line
@[no_expose, l_impl ConRon.Arena.IFEnv.push]
def envPushL : FunDecl := lfn (vis, q) locals (w, z) {
  if 4294967294 <= vis { abort };
  w := EREC⦃q + ⟪CI.cv + CV.name⟫⦄;
  z := call env_row_set(w, vis + 1, q);
  return vis + 1
}

/-- `env_pop_temp(vis, w, c, q)`: undo a temporary push of name `w`: its own row put back to
`(c, q)` (`IFEnv.popTemp`'s `prev`), the view lowered. -/
-- con-ron: ConRon/Arena/Env.lean:371-381 ConRon.Arena.IFEnv.popTemp
-- con-ron: CHANGED since 42a08640 — `ConRon.Arena.IFEnv.popTemp` changed; re-check the L code and its proofs, then delete this line
@[no_expose, l_impl ConRon.Arena.IFEnv.popTemp]
def envPopTempL : FunDecl := lfn (vis, w, c, q) locals (z) {
  z := call env_row_set(w, c, q);
  if vis == 0 { return 0 };
  return vis - 1
}

/-! ## The table rows -/

/-- `tbl_own_get(w)`: the own layer's table row of name handle `w` (the record's address plus
one, `0` for none). -/
-- con-ron: none — row access of L's table map (the twin's `IFEnv.tbls`)
@[no_expose] def tblOwnGetL : FunDecl := lfn (w) locals (g, t, ix) {
  g := ⟦w⟧.tag;
  t := ⟦w⟧.tier;
  ix := ⟦w⟧.idx << 1;
  if g == 0 { if OTXA⟨t⟩[ix] != CTL.u64[133] { return 0 }; return OTXA⟨t⟩[ix + 1] };
  if g == 1 { if OTXS⟨t⟩[ix] != CTL.u64[133] { return 0 }; return OTXS⟨t⟩[ix + 1] };
  if g == 2 { if OTXN⟨t⟩[ix] != CTL.u64[133] { return 0 }; return OTXN⟨t⟩[ix + 1] };
  abort
}

/-- `tbl_own_set(w, v)`: the own layer's table row of name handle `w` becomes `v`. -/
-- con-ron: none — row access of L's table map (the twin's `IFEnv.tbls`)
@[no_expose] def tblOwnSetL : FunDecl := lfn (w, v) locals (g, t, ix) {
  g := ⟦w⟧.tag;
  t := ⟦w⟧.tier;
  ix := ⟦w⟧.idx << 1;
  if g == 0 { OTXA⟨t⟩[ix] := CTL.u64[133]; OTXA⟨t⟩[ix + 1] := v; return 0 };
  if g == 1 { OTXS⟨t⟩[ix] := CTL.u64[133]; OTXS⟨t⟩[ix + 1] := v; return 0 };
  if g == 2 { OTXN⟨t⟩[ix] := CTL.u64[133]; OTXN⟨t⟩[ix + 1] := v; return 0 };
  abort
}

/-- `tbl_base_get(w)`: the stream index's table row of name handle `w`, `(position + 1,
record)`, or `(0, 0)`; a scratch name has none. -/
-- con-ron: none — row access of L's stream index (the twin's `IFBase.tbls`)
@[no_expose] def tblBaseGetL : FunDecl := lfn (w) locals (g, ix) {
  if ⟦w⟧.tier != 0 { return (0, 0) };
  g := ⟦w⟧.tag;
  ix := ⟦w⟧.idx << 1;
  if g == 0 { return (TIXA.u64[ix], TIXA.u64[ix + 1]) };
  if g == 1 { return (TIXS.u64[ix], TIXS.u64[ix + 1]) };
  if g == 2 { return (TIXN.u64[ix], TIXN.u64[ix + 1]) };
  abort
}

/-- `tbl_base_set(w, r, p)`: the stream index's table row of the persistent name handle `w`. -/
-- con-ron: none — row access of L's stream index (the twin's `IFBase.tbls`)
@[no_expose] def tblBaseSetL : FunDecl := lfn (w, r, p) locals (g, ix) {
  if ⟦w⟧.tier != 0 { abort };
  g := ⟦w⟧.tag;
  ix := ⟦w⟧.idx << 1;
  if g == 0 { TIXA.u64[ix] := r; TIXA.u64[ix + 1] := p; return 0 };
  if g == 1 { TIXS.u64[ix] := r; TIXS.u64[ix + 1] := p; return 0 };
  if g == 2 { TIXN.u64[ix] := r; TIXN.u64[ix + 1] := p; return 0 };
  abort
}

/-- `raw_table(t)`: the table of structure `t`, ungated (`IFEnv.rawTable?`): the own layer's
row, else the stream index's row of a record below `CTL[135]`; the record's address plus one,
`0` for none. -/
-- con-ron: ConRon/Arena/Env.lean:389-394 ConRon.Arena.IFEnv.rawTable?
@[no_expose, l_impl ConRon.Arena.IFEnv.rawTable?]
def rawTableL : FunDecl := lfn (t) locals (r, q) {
  r := call tbl_own_get(t);
  if r != 0 { return r };
  (r, q) := call tbl_base_get(t);
  if r == 0 { return 0 };
  if r - 1 < CTL.u64[135] { return q + 1 };
  return 0
}

/-- `find_table(vis, t)`: the table of structure `t` if `t` is in the view, else `0`
(`IFEnv.findTable?`). -/
-- con-ron: ConRon/Arena/Env.lean:396-399 ConRon.Arena.IFEnv.findTable?
@[no_expose, l_impl ConRon.Arena.IFEnv.findTable?]
def findTableL : FunDecl := lfn (vis, t) locals (f, q, r) {
  (f, q) := call env_find(t, vis);
  if f == 0 { return 0 };
  r := call raw_table(t);
  return r
}

/-- `env_push_table(q)`: install the table record at `q` (its structure name is word `q + ProjTbl.structName`)
in the own layer (`IFEnv.pushTable`). -/
-- con-ron: ConRon/Arena/Env.lean:364-369 ConRon.Arena.IFEnv.pushTable
-- con-ron: CHANGED since 42a08640 — `ConRon.Arena.IFEnv.pushTable` changed; re-check the L code and its proofs, then delete this line
@[no_expose, l_impl ConRon.Arena.IFEnv.pushTable]
def envPushTableL : FunDecl := lfn (q) locals (w, z) {
  w := EREC⦃q + ⟪ProjTbl.structName⟫⦄;
  z := call tbl_own_set(w, q + 1);
  return 0
}

/-- The environment's L functions. -/
def envProg : Prog :=
  [("env_row_get", envRowGetL), ("env_row_set", envRowSetL), ("base_row_get", baseRowGetL),
   ("base_row_set", baseRowSetL), ("env_find", envFindL), ("env_push", envPushL),
   ("env_pop_temp", envPopTempL), ("tbl_own_get", tblOwnGetL), ("tbl_own_set", tblOwnSetL),
   ("tbl_base_get", tblBaseGetL), ("tbl_base_set", tblBaseSetL), ("raw_table", rawTableL),
   ("find_table", findTableL), ("env_push_table", envPushTableL)]

/-! ## Generic helpers (kept from the old `Env.lean`; their users are everywhere) -/

section helpers
open ConRon.Arena Std.WP
open scoped Lean.Order

theorem triple_post {α : Type} {prog : M α} {P : St → Prop} {Q Q' : α → St → Prop}
    (h : ⦃fun s => P s⦄ prog ⦃fun r s => Q r s; ⊤⦄) (hq : ∀ r s, Q r s → Q' r s) :
    ⦃fun s => P s⦄ prog ⦃fun r s => Q' r s; ⊤⦄ :=
  M.triple_of_run fun _ _ _ hp hr => hq _ _ (M.of_run hp hr h)

end helpers

/-! ## Row addresses and the row models -/

section rows
open ConRon.Arena Std.WP
open scoped Lean.Order

/-- `w`'s row index as an L expression computes it: `2 ⟦w⟧.idx`. -/
def ixW (w : Word) : Word := idxW w <<< 1

theorem ixW_toNat (w : Word) : (ixW w).toNat = rowIx w := by
  have h1 : (idxW w).toNat < 0x44000000 := UInt64.lt_iff_toNat_lt.mp (idxW_lt w)
  rw [ixW, UInt64.toNat_shiftLeft, Nat.shiftLeft_eq, show (1 : Word).toNat % 64 = 1 from rfl, rowIx]
  omega

theorem ixW_succ (w : Word) : (ixW w + 1).toNat = rowIx w + 1 := by
  have h1 : (idxW w).toNat < 0x44000000 := UInt64.lt_iff_toNat_lt.mp (idxW_lt w)
  rw [UInt64.toNat_add, ixW_toNat w]; simp [rowIx]; omega

/-- A narrow word below `2^32` is its tier, tag and index. -/
theorem nat_split27 (a : Nat) (ha : a < 2 ^ 32) (hn : a / 2 ^ 30 % 2 = 0) :
    a = 2 ^ 31 * (a / 2 ^ 31 % 2) + 2 ^ 26 * (a / 2 ^ 26 % 16) + a % 2 ^ 26 := by
  omega

/-- Two name words (below `2^32`, tags at most `2`) with the same tag, tier and row index are
equal. -/
theorem row_inj {w w' : Word} (hw : w.toNat < 2 ^ 32) (hw' : w'.toNat < 2 ^ 32)
    (ht : rowTag w ≤ 2) (ht' : rowTag w' ≤ 2) (hg : rowTag w = rowTag w')
    (hr : rowTier w = rowTier w') (hi : rowIx w = rowIx w') : w = w' := by
  have hn := rowTag_narrow ht; have hn' := rowTag_narrow ht'
  have e := rowTag_eq ht; have e' := rowTag_eq ht'
  simp only [rowIx, idxW_toNat_narrow w hn, idxW_toNat_narrow w' hn'] at hi
  simp only [rowTier] at hr
  have e1 := nat_split27 _ hw hn; have e2 := nat_split27 _ hw' hn'
  exact UInt64.toNat_inj.mp (by omega)

/-- Distinct names have distinct words. -/
theorem nidx_word_inj {n n' : NIdx} (h : n.word.toUInt64 = n'.word.toUInt64) : n = n' := by
  rw [← decI_word n, ← decI_word n', h]

theorem decTbl_name {a : Nat → Option Word} {p : Nat} {t : IProjTable} (h : decTbl a p = some t) :
    ∃ w, a (p + ProjTbl.structName.toNat) = some w ∧ w.toNat < 2 ^ 32 ∧ t.structName = decI w := by
  simp only [decTbl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨n, hn, -, -, -, -, -, -, -, -, -, -, rfl⟩ := h
  exact hd?_some hn

theorem rdN_eq (a : Array Word) (k : Nat) (h : k < a.size) : rdN a k = a[k] := by simp [rdN, h]

/-- The own row arrays by tag. -/
theorem oixArr_0 : oixArr 0 = OIXA := rfl
theorem oixArr_1 : oixArr 1 = OIXS := rfl
theorem oixArr_2 : oixArr 2 = OIXN := rfl

theorem rdN_ixW (a : Array Word) (w : Word) : rdN a (rowIx w) = rdW a (idxW w <<< 1) := by
  rw [← ixW_toNat w]; rfl

theorem rdN_ixW1 (a : Array Word) (w : Word) : rdN a (rowIx w + 1) = rdW a ((idxW w <<< 1) + 1) := by
  rw [← ixW_succ w]; rfl

/-- `ownRaw` at a name of tag `g` (`OIXA`, `OIXS`, `OIXN`): what `env_row_get` reads. -/
theorem ownRaw_tag {m : Mem} {w : Word} (A : ArrId) (g : Word) (hg : tagW w = g) (hg2 : g.toNat ≤ 2)
    (hA : oixArr g.toNat = A) :
    ownRaw m w =
      if rdW (m.arr64 (tierA A (tierW w))) (idxW w <<< 1) >>> 32 = rdW (m.arr64 CTL) 133 then
        (rdW (m.arr64 (tierA A (tierW w))) (idxW w <<< 1) &&& 4294967295,
         rdW (m.arr64 (tierA A (tierW w))) ((idxW w <<< 1) + 1))
      else (0, 0) := by
  have ht : rowTag w = g.toNat := by rw [rowTag, hg]
  simp only [ownRaw, ownRow, ht, hA, hg2, true_and, stampW, rdN_ixW, rdN_ixW1]

theorem ownRaw_0 {m : Mem} {w : Word} (hg : tagW w = 0) : ownRaw m w =
      if rdW (m.arr64 (tierA OIXA (tierW w))) (idxW w <<< 1) >>> 32 = rdW (m.arr64 CTL) 133 then
        (rdW (m.arr64 (tierA OIXA (tierW w))) (idxW w <<< 1) &&& 4294967295,
         rdW (m.arr64 (tierA OIXA (tierW w))) ((idxW w <<< 1) + 1))
      else (0, 0) := ownRaw_tag _ 0 hg (by decide) rfl
theorem ownRaw_1 {m : Mem} {w : Word} (hg : tagW w = 1) : ownRaw m w =
      if rdW (m.arr64 (tierA OIXS (tierW w))) (idxW w <<< 1) >>> 32 = rdW (m.arr64 CTL) 133 then
        (rdW (m.arr64 (tierA OIXS (tierW w))) (idxW w <<< 1) &&& 4294967295,
         rdW (m.arr64 (tierA OIXS (tierW w))) ((idxW w <<< 1) + 1))
      else (0, 0) := ownRaw_tag _ 1 hg (by decide) rfl
theorem ownRaw_2 {m : Mem} {w : Word} (hg : tagW w = 2) : ownRaw m w =
      if rdW (m.arr64 (tierA OIXN (tierW w))) (idxW w <<< 1) >>> 32 = rdW (m.arr64 CTL) 133 then
        (rdW (m.arr64 (tierA OIXN (tierW w))) (idxW w <<< 1) &&& 4294967295,
         rdW (m.arr64 (tierA OIXN (tierW w))) ((idxW w <<< 1) + 1))
      else (0, 0) := ownRaw_tag _ 2 hg (by decide) rfl

theorem rdN_set64 (m : Mem) (a b : TieredArray) (k v : Word) (j : Nat) :
    rdN ((m.set64 a k v).arr64 b) j =
      if b = a ∧ k.toNat = j ∧ j < (m.arr64 a).size then v else rdN (m.arr64 b) j := by
  by_cases h : b = a
  · subst h
    rw [Mem.arr64_set64_same]
    simp only [rdN, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    grind
  · rw [Mem.arr64_set64_ne _ _ _ _ _ h]; simp [h]

/-- The own row array of name handle `w`. -/
def ownArr (w : Word) : TieredArray := tierA (oixArr (rowTag w)) (tierW w)

/-- The own table-row array of name handle `w`. -/
def otxArrT (w : Word) : TieredArray := tierA (otxArr (rowTag w)) (tierW w)

theorem ownArr_arr (w : Word) : (ownArr w).arr = 140 ∨ (ownArr w).arr = 141 ∨ (ownArr w).arr = 142 := by
  unfold ownArr tierA oixArr; split <;> (try split) <;> simp [OIXA, OIXS, OIXN] <;> decide

theorem otxArrT_arr (w : Word) :
    (otxArrT w).arr = 146 ∨ (otxArrT w).arr = 147 ∨ (otxArrT w).arr = 148 := by
  unfold otxArrT tierA otxArr; split <;> (try split) <;> simp [OTXA, OTXS, OTXN] <;> decide

theorem ownArr_ne {w : Word} {b : TieredArray} (h : b.arr ≠ 140 ∧ b.arr ≠ 141 ∧ b.arr ≠ 142) :
    b ≠ ownArr w := fun e => by subst e; have := ownArr_arr w; omega

theorem otxArrT_ne {w : Word} {b : TieredArray} (h : b.arr ≠ 146 ∧ b.arr ≠ 147 ∧ b.arr ≠ 148) :
    b ≠ otxArrT w := fun e => by subst e; have := otxArrT_arr w; omega

theorem tierW_eq_of_bit {w w' : Word} (h : (tierW w &&& 1 != 0) = (tierW w' &&& 1 != 0)) :
    rowTier w = rowTier w' := by
  have a := tierW_lt w; have b := tierW_lt w'
  rw [← tierW_toNat_row, ← tierW_toNat_row]
  have ea : tierW w &&& 1 = tierW w := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_and]; simp; omega
  have eb : tierW w' &&& 1 = tierW w' := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_and]; simp; omega
  rw [ea, eb] at h
  have k : ∀ t : Word, ((t != 0) = true) ↔ t.toNat ≠ 0 := by
    intro t; simp only [bne_iff_ne, ne_eq]; exact not_congr ⟨fun e => by simp [e], fun e => UInt64.toNat_inj.mp (by simpa using e)⟩
  have h2 : ((tierW w != 0) = true) ↔ ((tierW w' != 0) = true) := by rw [h]
  rw [k, k] at h2
  omega

/-- Equal own row arrays (tags at most `2`) have equal tags and tiers. -/
theorem ownArr_inj {w w' : Word} (ht : rowTag w ≤ 2) (ht' : rowTag w' ≤ 2) (h : ownArr w = ownArr w') :
    rowTag w = rowTag w' ∧ rowTier w = rowTier w' := by
  simp only [ownArr, tierA, TieredArray.mk.injEq] at h
  refine ⟨?_, tierW_eq_of_bit h.2⟩
  have h1 := h.1
  unfold oixArr at h1
  rcases (by omega : rowTag w = 0 ∨ rowTag w = 1 ∨ rowTag w = 2) with a | a | a <;>
  rcases (by omega : rowTag w' = 0 ∨ rowTag w' = 1 ∨ rowTag w' = 2) with b | b | b <;>
  simp [a, b, OIXA, OIXS, OIXN] at h1 <;> omega

theorem otxArrT_inj {w w' : Word} (ht : rowTag w ≤ 2) (ht' : rowTag w' ≤ 2) (h : otxArrT w = otxArrT w') :
    rowTag w = rowTag w' ∧ rowTier w = rowTier w' := by
  simp only [otxArrT, tierA, TieredArray.mk.injEq] at h
  refine ⟨?_, tierW_eq_of_bit h.2⟩
  have h1 := h.1
  unfold otxArr at h1
  rcases (by omega : rowTag w = 0 ∨ rowTag w = 1 ∨ rowTag w = 2) with a | a | a <;>
  rcases (by omega : rowTag w' = 0 ∨ rowTag w' = 1 ∨ rowTag w' = 2) with b | b | b <;>
  simp [a, b, OTXA, OTXS, OTXN] at h1 <;> omega

/-- The own row's first word for counter `c` (`0`: no row). -/
def rowWord (m : Mem) (c : Word) : Word := if c = 0 then 0 else (rdW (m.arr64 CTL) 133 <<< 32) + c

/-- The memory after `env_row_set(w, c, p)`. -/
def ownSet (m : Mem) (w c p : Word) : Mem :=
  (m.set64 (ownArr w) (ixW w) (rowWord m c)).set64 (ownArr w) (ixW w + 1) p

/-- The memory after `tbl_own_set(w, v)`. -/
def tblSet (m : Mem) (w v : Word) : Mem :=
  (m.set64 (otxArrT w) (ixW w) (rdW (m.arr64 CTL) 133)).set64 (otxArrT w) (ixW w + 1) v

theorem ownSet_arr {m : Mem} {w c p : Word} {b : TieredArray} (h : b ≠ ownArr w) :
    (ownSet m w c p).arr64 b = m.arr64 b := by
  simp only [ownSet, Mem.arr64_set64_ne _ _ _ _ _ h]

theorem tblSet_arr {m : Mem} {w v : Word} {b : TieredArray} (h : b ≠ otxArrT w) :
    (tblSet m w v).arr64 b = m.arr64 b := by
  simp only [tblSet, Mem.arr64_set64_ne _ _ _ _ _ h]

theorem ctl_ne_ownArr (w : Word) : (CTL : TieredArray) ≠ ownArr w := ownArr_ne (by decide)
theorem ctl_ne_otxArrT (w : Word) : (CTL : TieredArray) ≠ otxArrT w := otxArrT_ne (by decide)

/-- The packed row word reads back. -/
theorem rowWord_read {m : Mem} {c : Word} (hc : c ≠ 0) (hc32 : c.toNat < 2 ^ 32)
    (hs : (rdW (m.arr64 CTL) 133).toNat < 2 ^ 32) :
    rowWord m c >>> 32 = rdW (m.arr64 CTL) 133 ∧ rowWord m c &&& 4294967295 = c := by
  simp only [rowWord, hc, ite_false]
  generalize rdW (m.arr64 CTL) 133 = st at hs ⊢
  have e : ((st <<< 32) + c).toNat = st.toNat * 2 ^ 32 + c.toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
  constructor
  · apply UInt64.toNat_inj.mp; rw [UInt64.toNat_shiftRight, e]; simp [Nat.shiftRight_eq_div_pow]; omega
  · apply UInt64.toNat_inj.mp; rw [UInt64.toNat_and, e]
    rw [show (4294967295 : Word).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega

theorem rowWord_zero (m : Mem) : rowWord m 0 = 0 := by simp [rowWord]

theorem rowIx_lt (w : Word) : rowIx w < 2 ^ 32 := by
  have h1 : (idxW w).toNat < 0x44000000 := UInt64.lt_iff_toNat_lt.mp (idxW_lt w)
  simp only [rowIx]; omega

theorem rowIx_mod (w : Word) : (rowIx w + 1) % 18446744073709551616 = rowIx w + 1 :=
  Nat.mod_eq_of_lt (by have := rowIx_lt w; omega)

theorem ownRow_eq (m : Mem) (w : Word) :
    ownRow m w = (rdN (m.arr64 (ownArr w)) (rowIx w), rdN (m.arr64 (ownArr w)) (rowIx w + 1)) := rfl

theorem stampW_ownSet (m : Mem) (w c p : Word) : stampW (ownSet m w c p) = stampW m := by
  simp only [stampW, ownSet_arr (ctl_ne_ownArr w)]

theorem rowIx_even (w : Word) : rowIx w % 2 = 0 := by simp [rowIx]

/-- Rows of distinct name words (below `2^32`) are distinct words of the own arrays. -/
theorem row_ne {w w' : Word} (hw : w.toNat < 2 ^ 32) (hw' : w'.toNat < 2 ^ 32)
    (ht : rowTag w ≤ 2) (ht' : rowTag w' ≤ 2) (hne : w' ≠ w) (ha : ownArr w' = ownArr w) :
    rowIx w' ≠ rowIx w := fun hi => by
  obtain ⟨h1, h2⟩ := ownArr_inj ht' ht ha
  exact hne (row_inj hw' hw ht' ht h1 h2 hi)

theorem ownRaw_ownSet_self {m : Mem} {w c p : Word} (ht : rowTag w ≤ 2)
    (hb : rowIx w + 1 < (m.arr64 (ownArr w)).size) (hc32 : c.toNat < 2 ^ 32)
    (hs : (stampW m).toNat < 2 ^ 32) :
    (ownRaw (ownSet m w c p) w).1 = c ∧ (c ≠ 0 → (ownRaw (ownSet m w c p) w).2 = p) := by
  have hr : ownRow (ownSet m w c p) w = (rowWord m c, p) := by
    rw [ownRow_eq]
    simp [ownSet, ixW_toNat, hb, Nat.lt_of_succ_lt hb, rowIx_mod, Mem.arr64_set64_same, rdN, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
  simp only [ownRaw, stampW_ownSet, hr, ht, true_and]
  by_cases hc : c = 0
  · subst hc; simp only [rowWord_zero]; split <;> simp
  · obtain ⟨e1, e2⟩ := rowWord_read (m := m) hc hc32 hs
    simp only [stampW] at *
    simp [e1, e2, hc]

theorem ownRaw_ownSet_other {m : Mem} {w c p w' : Word} (hw : w.toNat < 2 ^ 32)
    (hw' : w'.toNat < 2 ^ 32) (ht : rowTag w ≤ 2) (hne : w' ≠ w) :
    ownRaw (ownSet m w c p) w' = ownRaw m w' := by
  by_cases ht' : rowTag w' ≤ 2
  · have hr : ownRow (ownSet m w c p) w' = ownRow m w' := by
      rw [ownRow_eq, ownRow_eq]
      by_cases ha : ownArr w' = ownArr w
      · have := row_ne hw hw' ht ht' hne ha
        have e1 := rowIx_even w; have e2 := rowIx_even w'
        have n1 : rowIx w ≠ rowIx w' := Ne.symm this
        have n2 : rowIx w + 1 ≠ rowIx w' := by omega
        have n3 : rowIx w ≠ rowIx w' + 1 := by omega
        have n4 : rowIx w + 1 ≠ rowIx w' + 1 := by omega
        rw [ha]
        simp [ownSet, rdN, Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, ixW_toNat, rowIx_mod, n1, n2, n3]
      · simp [ownSet, Mem.arr64_set64_ne _ _ _ _ _ ha]
    simp only [ownRaw, stampW_ownSet, hr]
  · simp [ownRaw, ht']

theorem ownArr_tag {w : Word} (A : ArrId) (g : Word) (hg : tagW w = g) (hA : oixArr g.toNat = A) :
    ownArr w = tierA A (tierW w) := by rw [ownArr, rowTag, hg, hA]
theorem ownArr_0 {w : Word} (hg : tagW w = 0) : ownArr w = tierA OIXA (tierW w) := ownArr_tag _ 0 hg rfl
theorem ownArr_1 {w : Word} (hg : tagW w = 1) : ownArr w = tierA OIXS (tierW w) := ownArr_tag _ 1 hg rfl
theorem ownArr_2 {w : Word} (hg : tagW w = 2) : ownArr w = tierA OIXN (tierW w) := ownArr_tag _ 2 hg rfl
theorem otxArrT_tag {w : Word} (A : ArrId) (g : Word) (hg : tagW w = g) (hA : otxArr g.toNat = A) :
    otxArrT w = tierA A (tierW w) := by rw [otxArrT, rowTag, hg, hA]
theorem otxArrT_0 {w : Word} (hg : tagW w = 0) : otxArrT w = tierA OTXA (tierW w) := otxArrT_tag _ 0 hg rfl
theorem otxArrT_1 {w : Word} (hg : tagW w = 1) : otxArrT w = tierA OTXS (tierW w) := otxArrT_tag _ 1 hg rfl
theorem otxArrT_2 {w : Word} (hg : tagW w = 2) : otxArrT w = tierA OTXN (tierW w) := otxArrT_tag _ 2 hg rfl

theorem rowTag_of {w g : Word} (hg : tagW w = g) : rowTag w = g.toNat := by rw [rowTag, hg]
theorem eixArr_0 {w : Word} (hg : tagW w = 0) : (eixArr (rowTag w) : TieredArray) = EIXA := by
  rw [rowTag_of hg]; rfl
theorem tixArr_0 {w : Word} (hg : tagW w = 0) : (tixArr (rowTag w) : TieredArray) = TIXA := by
  rw [rowTag_of hg]; rfl
theorem eixArr_1 {w : Word} (hg : tagW w = 1) : (eixArr (rowTag w) : TieredArray) = EIXS := by
  rw [rowTag_of hg]; rfl
theorem tixArr_1 {w : Word} (hg : tagW w = 1) : (tixArr (rowTag w) : TieredArray) = TIXS := by
  rw [rowTag_of hg]; rfl
theorem eixArr_2 {w : Word} (hg : tagW w = 2) : (eixArr (rowTag w) : TieredArray) = EIXN := by
  rw [rowTag_of hg]; rfl
theorem tixArr_2 {w : Word} (hg : tagW w = 2) : (tixArr (rowTag w) : TieredArray) = TIXN := by
  rw [rowTag_of hg]; rfl
theorem rowTier_of {w : Word} (h : tierW w = 0) : rowTier w = 0 := by rw [← tierW_toNat_row, h]; rfl

theorem baseRow_t1 {m : Mem} {w : Word} (ht : tierW w ≠ 0) : baseRow m w = (0, 0) := by
  have h1 : rowTier w ≠ 0 := fun e => ht (UInt64.toNat_inj.mp (by rw [tierW_toNat_row, e]; rfl))
  simp [baseRow, h1]
theorem baseTbl_t1 {m : Mem} {w : Word} (ht : tierW w ≠ 0) : baseTbl m w = (0, 0) := by
  have h1 : rowTier w ≠ 0 := fun e => ht (UInt64.toNat_inj.mp (by rw [tierW_toNat_row, e]; rfl))
  simp [baseTbl, h1]
theorem baseRow_0 {m : Mem} {w : Word} (ht : tierW w = 0) (hg : tagW w = 0) :
    baseRow m w = (rdW (m.arr64 EIXA) (idxW w <<< 1), rdW (m.arr64 EIXA) ((idxW w <<< 1) + 1)) := by
  have h1 : rowTier w = 0 := by rw [← tierW_toNat_row, ht]; rfl
  simp only [baseRow, rowTag_of hg, h1, rdN_ixW, rdN_ixW1]; rfl
theorem baseTbl_0 {m : Mem} {w : Word} (ht : tierW w = 0) (hg : tagW w = 0) :
    baseTbl m w = (rdW (m.arr64 TIXA) (idxW w <<< 1), rdW (m.arr64 TIXA) ((idxW w <<< 1) + 1)) := by
  have h1 : rowTier w = 0 := by rw [← tierW_toNat_row, ht]; rfl
  simp only [baseTbl, rowTag_of hg, h1, rdN_ixW, rdN_ixW1]; rfl
theorem ownTbl_0 {m : Mem} {w : Word} (hg : tagW w = 0) :
    ownTbl m w = if rdW (m.arr64 (tierA OTXA (tierW w))) (idxW w <<< 1) = rdW (m.arr64 CTL) 133 then
      rdW (m.arr64 (tierA OTXA (tierW w))) ((idxW w <<< 1) + 1) else 0 := by
  simp [ownTbl, rowTag_of hg, rdN_ixW, rdN_ixW1, stampW, otxArr]
theorem baseRow_1 {m : Mem} {w : Word} (ht : tierW w = 0) (hg : tagW w = 1) :
    baseRow m w = (rdW (m.arr64 EIXS) (idxW w <<< 1), rdW (m.arr64 EIXS) ((idxW w <<< 1) + 1)) := by
  have h1 : rowTier w = 0 := by rw [← tierW_toNat_row, ht]; rfl
  simp only [baseRow, rowTag_of hg, h1, rdN_ixW, rdN_ixW1]; rfl
theorem baseTbl_1 {m : Mem} {w : Word} (ht : tierW w = 0) (hg : tagW w = 1) :
    baseTbl m w = (rdW (m.arr64 TIXS) (idxW w <<< 1), rdW (m.arr64 TIXS) ((idxW w <<< 1) + 1)) := by
  have h1 : rowTier w = 0 := by rw [← tierW_toNat_row, ht]; rfl
  simp only [baseTbl, rowTag_of hg, h1, rdN_ixW, rdN_ixW1]; rfl
theorem ownTbl_1 {m : Mem} {w : Word} (hg : tagW w = 1) :
    ownTbl m w = if rdW (m.arr64 (tierA OTXS (tierW w))) (idxW w <<< 1) = rdW (m.arr64 CTL) 133 then
      rdW (m.arr64 (tierA OTXS (tierW w))) ((idxW w <<< 1) + 1) else 0 := by
  simp [ownTbl, rowTag_of hg, rdN_ixW, rdN_ixW1, stampW, otxArr]
theorem baseRow_2 {m : Mem} {w : Word} (ht : tierW w = 0) (hg : tagW w = 2) :
    baseRow m w = (rdW (m.arr64 EIXN) (idxW w <<< 1), rdW (m.arr64 EIXN) ((idxW w <<< 1) + 1)) := by
  have h1 : rowTier w = 0 := by rw [← tierW_toNat_row, ht]; rfl
  simp only [baseRow, rowTag_of hg, h1, rdN_ixW, rdN_ixW1]; rfl
theorem baseTbl_2 {m : Mem} {w : Word} (ht : tierW w = 0) (hg : tagW w = 2) :
    baseTbl m w = (rdW (m.arr64 TIXN) (idxW w <<< 1), rdW (m.arr64 TIXN) ((idxW w <<< 1) + 1)) := by
  have h1 : rowTier w = 0 := by rw [← tierW_toNat_row, ht]; rfl
  simp only [baseTbl, rowTag_of hg, h1, rdN_ixW, rdN_ixW1]; rfl
theorem ownTbl_2 {m : Mem} {w : Word} (hg : tagW w = 2) :
    ownTbl m w = if rdW (m.arr64 (tierA OTXN (tierW w))) (idxW w <<< 1) = rdW (m.arr64 CTL) 133 then
      rdW (m.arr64 (tierA OTXN (tierW w))) ((idxW w <<< 1) + 1) else 0 := by
  simp [ownTbl, rowTag_of hg, rdN_ixW, rdN_ixW1, stampW, otxArr]

end rows

/-! ## The relation's facts -/

section rel
open ConRon.Arena

/-- What a found pair decodes to: `(0, _)` is `none`, `(f, q)` the record at `q`. -/
def envFound (m : Mem) (f q : Word) : Option IConstantInfo :=
  if f = 0 then none else decCI (erecP m) q.toNat

theorem sub1_lt_iff {c v : Word} (hc : c ≠ 0) : c - 1 < v ↔ c.toNat - 1 < v.toNat := by
  have : c.toNat ≠ 0 := fun e => hc (UInt64.toNat_inj.mp (by simpa using e))
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
  simp

theorem IFEnv.find?_eq_match (fe : IFEnv) (n : NIdx) :
    fe.find? n = match fe.idx[n]? with
      | some ci => some ci
      | none => fe.base.find? n := by
  simp only [IFEnv.find?, IFEnv.lookup]
  split
  · rename_i he
    rw [Std.HashMap.getElem?_of_isEmpty he]
  · rfl

variable {m : Mem} {vis : Word} {fe : IFEnv}

/-- The own row of `w` is in the view (the condition `env_find` tests). -/
def ownHit (m : Mem) (vis w : Word) : Prop := (ownRaw m w).1 ≠ 0 ∧ (ownRaw m w).1 - 1 < vis

/-- The base row of `w` is in the view `CTL[134]`. -/
def baseHit (m : Mem) (w : Word) : Prop :=
  (baseRow m w).1 ≠ 0 ∧ (baseRow m w).1 - 1 < rdW (m.arr64 CTL) 134

instance (m : Mem) (vis w : Word) : Decidable (ownHit m vis w) := by unfold ownHit; infer_instance
instance (m : Mem) (w : Word) : Decidable (baseHit m w) := by unfold baseHit; infer_instance

/-- **`find?` through the rows.** -/
theorem EnvR.find_eq (h : EnvR m vis fe) {w : Word} (hw : w.toNat < 2 ^ 32) :
    fe.find? (decI w) =
      if ownHit m vis w then decCI (erecP m) (ownRaw m w).2.toNat
      else if baseHit m w then decCI (erecP m) (baseRow m w).2.toNat else none := by
  have hn := decI_word_self (k := .name) w hw
  have ho := h.own (decI w); rw [hn] at ho
  have hd := h.own_dec (decI w); rw [hn] at hd
  have hb := h.base (decI w); rw [hn] at hb
  rw [IFEnv.find?_eq_match, ho]
  simp only [ownFind, ownHit, baseHit]
  by_cases c1 : (ownRaw m w).1 ≠ 0 ∧ (ownRaw m w).1.toNat - 1 < vis.toNat
  · obtain ⟨ci, hci⟩ := hd c1.1
    rw [ite_eq_left c1, ite_eq_left ⟨c1.1, (sub1_lt_iff c1.1).mpr c1.2⟩, hci]
  · rw [ite_eq_right c1, ite_eq_right (fun e => c1 ⟨e.1, (sub1_lt_iff e.1).mp e.2⟩)]
    simp only [IFBase.find?, h.below]
    cases e : fe.base.idx[(decI w : NIdx)]? with
    | none =>
      rw [e] at hb
      by_cases b0 : (baseRow m w).1 = 0
      · simp [b0]
      · simp [b0] at hb
    | some x =>
      obtain ⟨c, ci⟩ := x
      rw [e] at hb
      by_cases b0 : (baseRow m w).1 = 0
      · simp [b0] at hb
      · simp only [b0, ite_false, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨hc, hci⟩ := hb
        subst hc
        rw [← hci]
        dsimp only
        by_cases l : UInt64.toNat (baseRow m w).fst - 1 < UInt64.toNat (rdW (m.arr64 CTL) 134)
        · rw [ite_eq_left l, ite_eq_left ⟨b0, (sub1_lt_iff b0).mpr l⟩]
        · rw [ite_eq_right l, ite_eq_right (fun e => l ((sub1_lt_iff b0).mp e.2))]

/-- A hit decodes. -/
theorem EnvR.hit_dec (h : EnvR m vis fe) {w : Word} (hw : w.toNat < 2 ^ 32) :
    (ownHit m vis w → ∃ ci, decCI (erecP m) (ownRaw m w).2.toNat = some ci) ∧
    (baseHit m w → ∃ ci, decCI (erecP m) (baseRow m w).2.toNat = some ci) := by
  have hn := decI_word_self (k := .name) w hw
  have hd := h.own_dec (decI w); rw [hn] at hd
  have hb := h.base (decI w); rw [hn] at hb
  refine ⟨fun e => hd e.1, fun e => ?_⟩
  cases x : fe.base.idx[(decI w : NIdx)]? with
  | none => rw [x] at hb; simp [e.1] at hb
  | some y =>
    rw [x] at hb; simp only [e.1, ite_false, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb
    exact ⟨y.2, hb.2.symm⟩

/-- What a table result decodes to: `0` is `none`, `r` the table record at `r - 1`. -/
def tblFound (m : Mem) (r : Word) : Option IProjTable :=
  if r = 0 then none else decTbl (erecP m) (r.toNat - 1)

/-- The base table row of `t` is in the view `CTL[135]`. -/
def baseTblHit (m : Mem) (t : Word) : Prop :=
  (baseTbl m t).1 ≠ 0 ∧ (baseTbl m t).1 - 1 < rdW (m.arr64 CTL) 135

instance (m : Mem) (t : Word) : Decidable (baseTblHit m t) := by unfold baseTblHit; infer_instance

theorem erecP_lt64 {m : Mem} {i : Nat} {v : Word} (h : erecP m i = some v) : i < 2 ^ 64 := by
  unfold erecP at h; split at h
  · assumption
  · simp at h

/-- A decoded table record's handle (its address plus one) does not wrap. -/
theorem decTbl_lt {m : Mem} {p : Nat} {t : IProjTable} (h : decTbl (erecP m) p = some t) :
    p + 1 < 2 ^ 64 := by
  -- the level parameters' length word, at `p + ProjTbl.lpsOff + 1`
  simp only [decTbl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
  obtain ⟨-, -, l, hl, -⟩ := h
  simp only [hlist?, nat?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hl
  obtain ⟨-, -, c, ⟨w, hw, -⟩, -⟩ := hl
  have := erecP_lt64 hw
  omega

/-- **`rawTable?` through the rows.** -/
theorem EnvR.rawTable_eq (h : EnvR m vis fe) {t : Word} (ht : t.toNat < 2 ^ 32) :
    fe.rawTable? (decI t) =
      if ownTbl m t ≠ 0 then decTbl (erecP m) ((ownTbl m t).toNat - 1)
      else if baseTblHit m t then decTbl (erecP m) (baseTbl m t).2.toNat else none := by
  have hn := decI_word_self (k := .name) t ht
  have ho := h.otbl (decI t); rw [hn] at ho
  have hd := h.otbl_dec (decI t); rw [hn] at hd
  have hb := h.btbl (decI t); rw [hn] at hb
  simp only [IFEnv.rawTable?, ho]
  by_cases c1 : ownTbl m t = 0
  · simp only [c1, ite_true, ne_eq, not_true_eq_false, ite_false]
    simp only [IFBase.findTable?, h.belowRec, baseTblHit]
    cases e : fe.base.tbls[(decI t : NIdx)]? with
    | none =>
      rw [e] at hb
      by_cases b0 : (baseTbl m t).1 = 0
      · simp [b0]
      · simp [b0] at hb
    | some x =>
      obtain ⟨c, tb⟩ := x
      rw [e] at hb
      by_cases b0 : (baseTbl m t).1 = 0
      · simp [b0] at hb
      · simp only [b0, ite_false, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨hc, htb⟩ := hb
        subst hc
        rw [← htb]
        dsimp only
        by_cases l : UInt64.toNat (baseTbl m t).fst - 1 < UInt64.toNat (rdW (m.arr64 CTL) 135)
        · rw [ite_eq_left l, ite_eq_left ⟨b0, (sub1_lt_iff b0).mpr l⟩]
        · rw [ite_eq_right l, ite_eq_right (fun e => l ((sub1_lt_iff b0).mp e.2))]
  · obtain ⟨tb, htb⟩ := hd c1
    simp only [c1, ite_false, ne_eq, not_false_eq_true, ite_true, htb]

/-- A base table hit decodes. -/
theorem EnvR.tblHit_dec (h : EnvR m vis fe) {t : Word} (ht : t.toNat < 2 ^ 32) :
    (ownTbl m t ≠ 0 → ∃ tb, decTbl (erecP m) ((ownTbl m t).toNat - 1) = some tb) ∧
    (baseTblHit m t → ∃ tb, decTbl (erecP m) (baseTbl m t).2.toNat = some tb) := by
  have hn := decI_word_self (k := .name) t ht
  have hd := h.otbl_dec (decI t); rw [hn] at hd
  have hb := h.btbl (decI t); rw [hn] at hb
  refine ⟨hd, fun e => ?_⟩
  cases x : fe.base.tbls[(decI t : NIdx)]? with
  | none => rw [x] at hb; simp [e.1] at hb
  | some y =>
    rw [x] at hb; simp only [e.1, ite_false, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb
    exact ⟨y.2, hb.2.symm⟩

/-- The base table result `q + 1` decodes as the record at `q`. -/
theorem tblFound_succ {m : Mem} {q : Word} {tb : IProjTable} (h : decTbl (erecP m) q.toNat = some tb) :
    tblFound m (q + 1) = decTbl (erecP m) q.toNat ∧ q + 1 ≠ 0 := by
  have hl := decTbl_lt h
  have e : (q + 1).toNat = q.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  refine ⟨?_, fun h0 => by have := congrArg UInt64.toNat h0; simp only [e] at this; simp at this⟩
  have hne : q + 1 ≠ 0 := fun h0 => by have := congrArg UInt64.toNat h0; simp only [e] at this; simp at this
  simp only [tblFound, hne, ite_false, e, Nat.add_sub_cancel]

/-! ### Row writes and the relation -/

theorem ownSet_arr_of {m : Mem} {w c p : Word} {b : TieredArray}
    (h : b.arr ≠ 140 ∧ b.arr ≠ 141 ∧ b.arr ≠ 142) : (ownSet m w c p).arr64 b = m.arr64 b :=
  ownSet_arr (ownArr_ne h)

theorem ownSet_ctl (m : Mem) (w c p : Word) : (ownSet m w c p).arr64 CTL = m.arr64 CTL :=
  ownSet_arr_of (by decide)

theorem erecP_ownSet (m : Mem) (w c p : Word) : erecP (ownSet m w c p) = erecP m := by
  funext i
  simp only [erecP, erTop, erecTop1, ownSet_ctl, ownSet_arr_of (b := (EREC : TieredArray)) (by decide),
    ownSet_arr_of (b := tier1 EREC) (by decide)]
  rfl

theorem otxArrT_arr' (x : Word) : (tierA (otxArr (rowTag x)) (tierW x)).arr ≠ 140 ∧
    (tierA (otxArr (rowTag x)) (tierW x)).arr ≠ 141 ∧ (tierA (otxArr (rowTag x)) (tierW x)).arr ≠ 142 := by
  have := otxArrT_arr x; simp only [otxArrT] at this; omega

theorem ownTbl_ownSet (m : Mem) (w c p x : Word) : ownTbl (ownSet m w c p) x = ownTbl m x := by
  simp only [ownTbl, ownSet_arr_of (otxArrT_arr' x), stampW, ownSet_ctl]
  rfl

theorem eixArr_arr (g : Nat) : (eixArr g : TieredArray).arr = 132 ∨ (eixArr g : TieredArray).arr = 133 ∨
    (eixArr g : TieredArray).arr = 134 := by
  unfold eixArr; split <;> (try split) <;> simp [EIXA, EIXS, EIXN] <;> decide

theorem tixArr_arr (g : Nat) : (tixArr g : TieredArray).arr = 129 ∨ (tixArr g : TieredArray).arr = 130 ∨
    (tixArr g : TieredArray).arr = 131 := by
  unfold tixArr; split <;> (try split) <;> simp [TIXA, TIXS, TIXN] <;> decide

theorem baseRow_ownSet (m : Mem) (w c p x : Word) : baseRow (ownSet m w c p) x = baseRow m x := by
  have := eixArr_arr (rowTag x)
  simp only [baseRow, ownSet_arr_of (b := (eixArr (rowTag x) : TieredArray)) (by omega)]

theorem baseTbl_ownSet (m : Mem) (w c p x : Word) : baseTbl (ownSet m w c p) x = baseTbl m x := by
  have := tixArr_arr (rowTag x)
  simp only [baseTbl, ownSet_arr_of (b := (tixArr (rowTag x) : TieredArray)) (by omega)]

theorem nidx_beq (n n' : NIdx) : (n == n') = decide (n'.word.toUInt64 = n.word.toUInt64) := by
  by_cases e : n = n'
  · subst e; simp
  · have : n'.word.toUInt64 ≠ n.word.toUInt64 := fun h => e (nidx_word_inj h).symm
    simp [e, this]

theorem vis_toNat_succ {v : Word} (h : v.toNat < 2 ^ 32 - 2) : (v + 1).toNat = v.toNat + 1 := by
  rw [UInt64.toNat_add]; simp; omega

/-- **An own-row write keeps `OwnBelow`**: the row word carries the current stamp. -/
theorem OwnBelow.of_ownSet {m : Mem} {w c p : Word} (h : OwnBelow m) (hc32 : c.toNat < 2 ^ 32)
    (hs : (stampW m).toNat < 2 ^ 32) : OwnBelow (ownSet m w c p) := by
  intro x hx
  rw [stampW_ownSet]
  obtain ⟨h1, h2⟩ := h x hx
  refine ⟨?_, ?_⟩
  · rw [ownRow_eq] at h1 ⊢
    have e1 := rowIx_even w; have e2 := rowIx_even x
    simp only [ownSet, rdN_set64, ixW_succ, ixW_toNat]
    rw [ite_eq_right (fun hh => by omega)]
    split
    · by_cases hc : c = 0
      · subst hc; simp [rowWord_zero]
      · rw [(rowWord_read (m := m) hc hc32 hs).1]; exact Nat.le_refl _
    · exact h1
  · rw [ownSet_arr_of (otxArrT_arr' x)]; exact h2

/-- **The twin's push without the flags' recomputation**: the branch of `IFEnv.push` that keeps
the literal flags (a push of a name that is no literal name, or once string literals are
expandable). The recomputation is `IFEnv.setFlags` on top (`IFEnv.push_eq`). -/
def pushRows (fe : IFEnv) (ci : IConstantInfo) : IFEnv :=
  ⟨⟨ci :: fe.env.consts, fe.env.tables⟩, fe.idx.insert ci.name ci, fe.base, fe.tbls, fe.natLit,
    fe.strLit⟩

/-- **`IFEnv.push` as `pushRows` and the recomputation.** -/
theorem IFEnv.push_eq (fe : IFEnv) (ci : IConstantInfo) :
    fe.push ci = if (!fe.strLit && litNameAt fe.base.lits ci.name 0) = true then
      let fe2 := (pushRows fe ci).setFlags (pushRows fe ci).natLitStoredBy fe.strLit
      fe2.setFlags fe2.natLit fe2.strLitStoredBy
    else pushRows fe ci := by
  unfold IFEnv.push; rfl

/-- **`push`'s rows** (`pushRows`): the own row of the record's name becomes `(vis + 1, q)`; the
literal flags are left for `EnvR.setFlags`. -/
theorem EnvR.push (h : EnvR m vis fe) {q : Word} {ci : IConstantInfo}
    (hci : decCI (erecP m) q.toNat = some ci) {w : Word} (hw : erecP m (q.toNat + CI.cv.toNat) = some w)
    (hv : vis.toNat < 2 ^ 32 - 2) (ht : rowTag w ≤ 2)
    (hb : rowIx w + 1 < (m.arr64 (ownArr w)).size) :
    EnvR (ownSet m w (vis + 1) q) (vis + 1) (pushRows fe ci) := by
  obtain ⟨w', hw', hw32, hname⟩ := decCI_name hci
  rw [hw] at hw'; cases hw'
  have hv1 := vis_toNat_succ hv
  have hne : vis + 1 ≠ 0 := fun e => by have := congrArg UInt64.toNat e; simp only [hv1] at this; simp at this
  have hs := h.stamp
  obtain ⟨s1, s2⟩ := ownRaw_ownSet_self (m := m) (p := q) ht hb (by rw [hv1]; omega) hs
  have s2 := s2 hne
  have oth : ∀ n : NIdx, n.word.toUInt64 ≠ w →
      ownRaw (ownSet m w (vis + 1) q) n.word.toUInt64 = ownRaw m n.word.toUInt64 := fun n hn =>
    ownRaw_ownSet_other hw32 (L.Arena.idx_word_lt32 n) ht hn
  have hname' : ∀ n : NIdx, (ci.name == n) = decide (n.word.toUInt64 = w) := by
    intro n; rw [hname, nidx_beq, decI_word_self w hw32]
  have hP := erecP_ownSet m w (vis + 1) q
  refine ⟨fun n => ?_, fun n hn => ?_, fun n hn => ?_, fun n n' hn he => ?_, fun n => ?_, fun n hn => ?_,
    ?_, ?_, fun n => ?_, fun n => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [pushRows, Std.HashMap.getElem?_insert, hname']
    by_cases e : n.word.toUInt64 = w
    · simp only [e, decide_true, ite_true, ownFind, s1, s2, hP, hci, hv1]
      simp [hne]
    · simp only [e, decide_false, Bool.false_eq_true, ite_false, ownFind, oth n e, hP, h.own n, hv1]
      by_cases c0 : (ownRaw m n.word.toUInt64).1 = 0
      · simp [c0]
      · have := h.fresh n c0
        simp [c0, this, show (ownRaw m n.word.toUInt64).1.toNat - 1 < vis.toNat + 1 by omega]
  · by_cases e : n.word.toUInt64 = w
    · rw [e, s2, hP]; exact ⟨ci, hci⟩
    · rw [oth n e] at hn ⊢; rw [hP]; exact h.own_dec n hn
  · by_cases e : n.word.toUInt64 = w
    · rw [e, s1, hv1]; omega
    · rw [oth n e] at hn ⊢; have := h.fresh n hn; rw [hv1]; omega
  · by_cases e : n.word.toUInt64 = w <;> by_cases e' : n'.word.toUInt64 = w
    · exact nidx_word_inj (e.trans e'.symm)
    · exfalso; rw [e, s1, oth n' e'] at he
      have hn' : (ownRaw m n'.word.toUInt64).1 ≠ 0 := by rw [← he]; exact hne
      have := h.fresh n' hn'; rw [← he, hv1] at this; omega
    · exfalso; rw [e', s1, oth n e] at he
      rw [oth n e] at hn; have := h.fresh n hn; rw [he, hv1] at this; omega
    · rw [oth n e, oth n' e'] at he; rw [oth n e] at hn; exact h.uniq n n' hn he
  · simp only [pushRows, ownTbl_ownSet, hP]; exact h.otbl n
  · rw [ownTbl_ownSet] at hn ⊢; rw [hP]; exact h.otbl_dec n hn
  · simp only [pushRows, ownSet_ctl]; exact h.below
  · simp only [pushRows, ownSet_ctl]; exact h.belowRec
  · simp only [pushRows, baseRow_ownSet, hP]; exact h.base n
  · simp only [pushRows, baseTbl_ownSet, hP]; exact h.btbl n
  · simp only [stampW, ownSet_ctl]; exact hs
  · exact h.ownBelow.of_ownSet (by rw [hv1]; omega) hs
  · simp only [pushRows, ownSet_ctl]; exact h.natLit
  · simp only [pushRows, ownSet_ctl]; exact h.strLit
  · simp only [pushRows, litWords, ownSet_ctl]; exact h.lits

/-- **`popTemp`**: the own row of `w` (the newest push, counter `vis`) put back to `(c, q)`, the
row read before that push (`prev` its decoding), and the view lowered. -/
theorem EnvR.popTemp (h : EnvR m vis fe) {w c q : Word} (hw : w.toNat < 2 ^ 32) (ht : rowTag w ≤ 2)
    (hb : rowIx w + 1 < (m.arr64 (ownArr w)).size) (hv : vis ≠ 0) (htop : (ownRaw m w).1 = vis)
    (hc32 : c.toNat < 2 ^ 32) (hcv : c ≠ 0 → c.toNat - 1 < vis.toNat - 1)
    (hcd : c ≠ 0 → ∃ ci, decCI (erecP m) q.toNat = some ci)
    (hfree : c ≠ 0 → ∀ n : NIdx, n.word.toUInt64 ≠ w → (ownRaw m n.word.toUInt64).1 ≠ c) :
    EnvR (ownSet m w c q) (vis - 1)
      (fe.popTemp (decI w) (if c = 0 then none else decCI (erecP m) q.toNat)) := by
  have hs := h.stamp
  obtain ⟨s1, s2⟩ := ownRaw_ownSet_self (m := m) (p := q) ht hb hc32 hs
  have oth : ∀ n : NIdx, n.word.toUInt64 ≠ w →
      ownRaw (ownSet m w c q) n.word.toUInt64 = ownRaw m n.word.toUInt64 := fun n hn =>
    ownRaw_ownSet_other hw (L.Arena.idx_word_lt32 n) ht hn
  have hP := erecP_ownSet m w c q
  have hv1 : (vis - 1).toNat = vis.toNat - 1 := by
    have : vis.toNat ≠ 0 := fun e => hv (UInt64.toNat_inj.mp (by simpa using e))
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp
  have hwn := decI_word_self (k := .name) w hw
  -- the other rows are below the newest
  have below : ∀ n : NIdx, n.word.toUInt64 ≠ w → (ownRaw m n.word.toUInt64).1 ≠ 0 →
      (ownRaw m n.word.toUInt64).1.toNat - 1 < vis.toNat - 1 := by
    intro n hn h0
    have f := h.fresh n h0
    have : (ownRaw m n.word.toUInt64).1 ≠ vis := fun e => by
      have := h.uniq n (decI w) h0 (by rw [hwn, htop, e]); subst this; exact hn hwn
    have : (ownRaw m n.word.toUInt64).1.toNat ≠ vis.toNat := fun e => this (UInt64.toNat_inj.mp e)
    have : (ownRaw m n.word.toUInt64).1.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp (by simpa using e))
    omega
  have hkey : ∀ n : NIdx, ((decI w : NIdx) == n) = decide (n.word.toUInt64 = w) := by
    intro n; rw [nidx_beq, hwn]
  refine ⟨fun n => ?_, fun n hn => ?_, fun n hn => ?_, fun n n' hn he => ?_, fun n => ?_, fun n hn => ?_,
    ?_, ?_, fun n => ?_, fun n => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases e : n.word.toUInt64 = w
    · have e' : n = decI w := by rw [← e, decI_word]
      subst e'
      simp only [ownFind, hwn, s1, hP, hv1]
      by_cases c0 : c = 0
      · simp only [IFEnv.popTemp, c0, ite_true, Std.HashMap.getElem?_erase, beq_self_eq_true]; simp
      · obtain ⟨ci, hci⟩ := hcd c0
        simp only [IFEnv.popTemp, c0, ite_false, hci, Std.HashMap.getElem?_insert, beq_self_eq_true,
          ite_true, s2 c0, ne_eq, not_false_eq_true, true_and]
        rw [ite_eq_left (hcv c0)]
    · have hidx : (fe.popTemp (decI w) (if c = 0 then none else decCI (erecP m) q.toNat)).idx[n]? =
          fe.idx[n]? := by
        simp only [IFEnv.popTemp]; split <;> simp [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase, hkey, e]
      rw [hidx, h.own n]
      simp only [ownFind, oth n e, hP, hv1]
      by_cases c0 : (ownRaw m n.word.toUInt64).1 = 0
      · simp [c0]
      · have := below n e c0; have := h.fresh n c0
        simp [c0, this, show (ownRaw m n.word.toUInt64).1.toNat - 1 < vis.toNat - 1 by omega]
  · by_cases e : n.word.toUInt64 = w
    · rw [e, s1] at hn; rw [e, s2 hn, hP]; exact hcd hn
    · rw [oth n e] at hn ⊢; rw [hP]; exact h.own_dec n hn
  · rw [hv1]
    by_cases e : n.word.toUInt64 = w
    · rw [e, s1] at hn ⊢; exact hcv hn
    · rw [oth n e] at hn ⊢; exact below n e hn
  · by_cases e : n.word.toUInt64 = w <;> by_cases e' : n'.word.toUInt64 = w
    · exact nidx_word_inj (e.trans e'.symm)
    · exfalso; rw [e, s1] at hn he; rw [oth n' e'] at he; exact hfree hn n' e' he.symm
    · exfalso; rw [e', s1, oth n e] at he; rw [oth n e] at hn
      exact hfree (he ▸ hn) n e he
    · rw [oth n e, oth n' e'] at he; rw [oth n e] at hn; exact h.uniq n n' hn he
  · simp only [IFEnv.popTemp, ownTbl_ownSet, hP]; exact h.otbl n
  · rw [ownTbl_ownSet] at hn ⊢; rw [hP]; exact h.otbl_dec n hn
  · simp only [IFEnv.popTemp, ownSet_ctl]; exact h.below
  · simp only [IFEnv.popTemp, ownSet_ctl]; exact h.belowRec
  · simp only [IFEnv.popTemp, baseRow_ownSet, hP]; exact h.base n
  · simp only [IFEnv.popTemp, baseTbl_ownSet, hP]; exact h.btbl n
  · simp only [stampW, ownSet_ctl]; exact hs
  · exact h.ownBelow.of_ownSet hc32 hs
  · simp only [IFEnv.popTemp, ownSet_ctl]; exact h.natLit
  · simp only [IFEnv.popTemp, ownSet_ctl]; exact h.strLit
  · simp only [IFEnv.popTemp, litWords, ownSet_ctl]; exact h.lits

/-! ### Table-row writes and the relation -/

theorem tblSet_arr_of {m : Mem} {w v : Word} {b : TieredArray}
    (h : b.arr ≠ 146 ∧ b.arr ≠ 147 ∧ b.arr ≠ 148) : (tblSet m w v).arr64 b = m.arr64 b :=
  tblSet_arr (otxArrT_ne h)

theorem tblSet_ctl (m : Mem) (w v : Word) : (tblSet m w v).arr64 CTL = m.arr64 CTL :=
  tblSet_arr_of (by decide)

theorem erecP_tblSet (m : Mem) (w v : Word) : erecP (tblSet m w v) = erecP m := by
  funext i
  simp only [erecP, erTop, erecTop1, tblSet_ctl, tblSet_arr_of (b := (EREC : TieredArray)) (by decide),
    tblSet_arr_of (b := tier1 EREC) (by decide)]
  rfl

theorem ownRaw_tblSet (m : Mem) (w v x : Word) : ownRaw (tblSet m w v) x = ownRaw m x := by
  have := ownArr_arr x
  simp only [ownRaw, ownRow_eq, tblSet_arr_of (b := ownArr x) (by omega), stampW, tblSet_ctl]
  rfl

theorem baseRow_tblSet (m : Mem) (w v x : Word) : baseRow (tblSet m w v) x = baseRow m x := by
  have := eixArr_arr (rowTag x)
  simp only [baseRow, tblSet_arr_of (b := (eixArr (rowTag x) : TieredArray)) (by omega)]

theorem baseTbl_tblSet (m : Mem) (w v x : Word) : baseTbl (tblSet m w v) x = baseTbl m x := by
  have := tixArr_arr (rowTag x)
  simp only [baseTbl, tblSet_arr_of (b := (tixArr (rowTag x) : TieredArray)) (by omega)]

theorem ownTbl_eq (m : Mem) (w : Word) : ownTbl m w =
    if rowTag w ≤ 2 ∧ rdN (m.arr64 (otxArrT w)) (rowIx w) = stampW m then
      rdN (m.arr64 (otxArrT w)) (rowIx w + 1) else 0 := rfl

theorem ownTbl_tblSet_self {m : Mem} {w v : Word} (ht : rowTag w ≤ 2)
    (hb : rowIx w + 1 < (m.arr64 (otxArrT w)).size) : ownTbl (tblSet m w v) w = v := by
  rw [ownTbl_eq]
  simp [tblSet, stampW, ht, ixW_toNat, hb, Nat.lt_of_succ_lt hb, rowIx_mod,
    Mem.arr64_set64_same, Mem.arr64_set64_ne _ _ _ _ _ (ctl_ne_otxArrT w), rdN,
    Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

theorem ownTbl_tblSet_other {m : Mem} {w v x : Word} (hw : w.toNat < 2 ^ 32) (hx : x.toNat < 2 ^ 32)
    (ht : rowTag w ≤ 2) (hne : x ≠ w) : ownTbl (tblSet m w v) x = ownTbl m x := by
  by_cases ht' : rowTag x ≤ 2
  · rw [ownTbl_eq, ownTbl_eq]
    have hs : stampW (tblSet m w v) = stampW m := by simp only [stampW, tblSet_ctl]
    rw [hs]
    by_cases ha : otxArrT x = otxArrT w
    · obtain ⟨h1, h2⟩ := otxArrT_inj ht' ht ha
      have := fun hi => hne (row_inj hx hw ht' ht h1 h2 hi)
      have e1 := rowIx_even w; have e2 := rowIx_even x
      have n1 : rowIx w ≠ rowIx x := fun e => this e.symm
      have n2 : rowIx w + 1 ≠ rowIx x := by omega
      have n3 : rowIx w ≠ rowIx x + 1 := by omega
      have n4 : rowIx w + 1 ≠ rowIx x + 1 := by omega
      rw [ha]
      simp [tblSet, rdN, Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, ixW_toNat, rowIx_mod, n1, n2, n3]
      rfl
    · simp [tblSet, Mem.arr64_set64_ne _ _ _ _ _ ha]
  · simp [ownTbl, ht']

/-- **A table-row write keeps `OwnBelow`**: the table row carries the current stamp. -/
theorem OwnBelow.of_tblSet {m : Mem} {w v : Word} (h : OwnBelow m) : OwnBelow (tblSet m w v) := by
  intro x hx
  have hst : stampW (tblSet m w v) = stampW m := by simp only [stampW, tblSet_ctl]
  rw [hst]
  obtain ⟨h1, h2⟩ := h x hx
  refine ⟨?_, ?_⟩
  · have := ownArr_arr x
    rw [ownRow_eq] at h1 ⊢; rw [tblSet_arr_of (b := ownArr x) (by omega)]; exact h1
  · have e1 := rowIx_even w; have e2 := rowIx_even x
    show (rdN ((tblSet m w v).arr64 (otxArrT x)) (rowIx x)).toNat ≤ _
    simp only [tblSet, rdN_set64, ixW_succ, ixW_toNat]
    rw [ite_eq_right (fun hh => by omega)]
    split
    · exact Nat.le_refl _
    · exact h2

/-- **`pushTable`**: the own table row of the table's structure becomes the record. -/
theorem EnvR.pushTable (h : EnvR m vis fe) {q : Word} {tb : IProjTable}
    (htb : decTbl (erecP m) q.toNat = some tb) {w : Word} (hw : erecP m (q.toNat + ProjTbl.structName.toNat) = some w)
    (ht : rowTag w ≤ 2) (hb : rowIx w + 1 < (m.arr64 (otxArrT w)).size) :
    EnvR (tblSet m w (q + 1)) vis (fe.pushTable tb) := by
  obtain ⟨w', hw', hw32, hname⟩ := decTbl_name htb
  rw [hw] at hw'; cases hw'
  have hl := decTbl_lt htb
  have hq1 : (q + 1).toNat = q.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hne : q + 1 ≠ 0 := fun e => by have := congrArg UInt64.toNat e; simp only [hq1] at this; simp at this
  have s1 := ownTbl_tblSet_self (m := m) (v := q + 1) ht hb
  have oth : ∀ n : NIdx, n.word.toUInt64 ≠ w → ownTbl (tblSet m w (q + 1)) n.word.toUInt64 =
      ownTbl m n.word.toUInt64 := fun n hn => ownTbl_tblSet_other hw32 (L.Arena.idx_word_lt32 n) ht hn
  have hname' : ∀ n : NIdx, (tb.structName == n) = decide (n.word.toUInt64 = w) := by
    intro n; rw [hname, nidx_beq, decI_word_self w hw32]
  have hP := erecP_tblSet m w (q + 1)
  refine ⟨fun n => ?_, fun n hn => ?_, fun n hn => ?_, fun n n' hn he => ?_, fun n => ?_, fun n hn => ?_,
    ?_, ?_, fun n => ?_, fun n => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [IFEnv.pushTable, ownFind, ownRaw_tblSet, hP]; exact h.own n
  · rw [ownRaw_tblSet] at hn ⊢; rw [hP]; exact h.own_dec n hn
  · rw [ownRaw_tblSet] at hn ⊢; exact h.fresh n hn
  · rw [ownRaw_tblSet, ownRaw_tblSet] at he; rw [ownRaw_tblSet] at hn; exact h.uniq n n' hn he
  · simp only [IFEnv.pushTable, Std.HashMap.getElem?_insert, hname', hP]
    by_cases e : n.word.toUInt64 = w
    · simp [e, s1, hne, hq1, htb]
    · simp only [e, decide_false, Bool.false_eq_true, ite_false, oth n e]; exact h.otbl n
  · by_cases e : n.word.toUInt64 = w
    · rw [e, s1, hP, hq1, Nat.add_sub_cancel]; exact ⟨tb, htb⟩
    · rw [oth n e] at hn ⊢; rw [hP]; exact h.otbl_dec n hn
  · simp only [IFEnv.pushTable, tblSet_ctl]; exact h.below
  · simp only [IFEnv.pushTable, tblSet_ctl]; exact h.belowRec
  · simp only [IFEnv.pushTable, baseRow_tblSet, hP]; exact h.base n
  · simp only [IFEnv.pushTable, baseTbl_tblSet, hP]; exact h.btbl n
  · simp only [stampW, tblSet_ctl]; exact h.stamp
  · exact h.ownBelow.of_tblSet
  · simp only [IFEnv.pushTable, tblSet_ctl]; exact h.natLit
  · simp only [IFEnv.pushTable, tblSet_ctl]; exact h.strLit
  · simp only [IFEnv.pushTable, litWords, tblSet_ctl]; exact h.lits

/-! ### The literal flags -/

theorem rdW_set_ctl_160_161 (m : Mem) (a b x : Word) (hx : x ≠ 160) (hy : x ≠ 161) :
    rdW (((m.set64 CTL 160 a).set64 CTL 161 b).arr64 CTL) x = rdW (m.arr64 CTL) x := by
  simp only [rdW_set64]; simp [Ne.symm hx, Ne.symm hy]

/-- **The flag words written** (`IFEnv.setFlags`, and the recomputation of `IFEnv.push`): the
words `CTL[160]`, `CTL[161]` become `a`, `b`, the twin's flags `a ≠ 0`, `b ≠ 0`. -/
theorem EnvR.setFlags (h : EnvR m vis fe) (a b : Word) (hc : 161 < (m.arr64 CTL).size) :
    EnvR ((m.set64 CTL 160 a).set64 CTL 161 b) vis (fe.setFlags (a != 0) (b != 0)) := by
  have h' := h.congrF (m' := (m.set64 CTL 160 a).set64 CTL 161 b) (fun x hx => by
      have : x ≠ (CTL : TieredArray) := by intro e; subst e; revert hx; decide
      simp only [Mem.arr64_set64_ne _ _ _ _ _ this])
    (fun x _ h1 h2 => rdW_set_ctl_160_161 m a b x h1 h2)
  have e1 : rdW (((m.set64 CTL 160 a).set64 CTL 161 b).arr64 CTL) 160 = a := by
    simp [rdW_set64, Mem.size64_set64]; omega
  have e2 : rdW (((m.set64 CTL 160 a).set64 CTL 161 b).arr64 CTL) 161 = b := by
    simp [rdW_set64, Mem.size64_set64]; omega
  rw [e1, e2] at h'; exact h'

/-! ### Stream-index writes (`build_index`) -/

/-- The memory after `base_row_set(w, c, p)`. -/
def baseSet (m : Mem) (w c p : Word) : Mem :=
  (m.set64 (eixArr (rowTag w)) (ixW w) c).set64 (eixArr (rowTag w)) (ixW w + 1) p

/-- The memory after `tbl_base_set(w, r, p)`. -/
def baseTblSet (m : Mem) (w r p : Word) : Mem :=
  (m.set64 (tixArr (rowTag w)) (ixW w) r).set64 (tixArr (rowTag w)) (ixW w + 1) p

theorem eixArr_inj {g g' : Nat} (h : g ≤ 2) (h' : g' ≤ 2) (e : eixArr g = eixArr g') : g = g' := by
  unfold eixArr at e
  rcases (by omega : g = 0 ∨ g = 1 ∨ g = 2) with a | a | a <;>
  rcases (by omega : g' = 0 ∨ g' = 1 ∨ g' = 2) with b | b | b <;> simp [a, b, EIXA, EIXS, EIXN] at e <;> omega

theorem tixArr_inj {g g' : Nat} (h : g ≤ 2) (h' : g' ≤ 2) (e : tixArr g = tixArr g') : g = g' := by
  unfold tixArr at e
  rcases (by omega : g = 0 ∨ g = 1 ∨ g = 2) with a | a | a <;>
  rcases (by omega : g' = 0 ∨ g' = 1 ∨ g' = 2) with b | b | b <;> simp [a, b, TIXA, TIXS, TIXN] at e <;> omega

theorem baseRow_baseSet_self {m : Mem} {w c p : Word} (ht : rowTag w ≤ 2) (h0 : rowTier w = 0)
    (hb : rowIx w + 1 < (m.arr64 (eixArr (rowTag w))).size) : baseRow (baseSet m w c p) w = (c, p) := by
  simp [baseRow, baseSet, ht, h0, rdN, ixW_toNat, hb, Nat.lt_of_succ_lt hb, rowIx_mod,
    Mem.arr64_set64_same, Array.set!_eq_setIfInBounds,
    Array.size_setIfInBounds]

theorem baseRow_baseSet_other {m : Mem} {w c p x : Word} (hw : w.toNat < 2 ^ 32) (hx : x.toNat < 2 ^ 32)
    (ht : rowTag w ≤ 2) (h0 : rowTier w = 0) (hne : x ≠ w) : baseRow (baseSet m w c p) x = baseRow m x := by
  by_cases ht' : rowTag x ≤ 2 ∧ rowTier x = 0
  · simp only [baseRow, ht', and_self, ite_true]
    by_cases ha : (eixArr (rowTag x) : TieredArray) = eixArr (rowTag w)
    · have hg := eixArr_inj ht'.1 ht (TieredArray.t0_inj.mp ha)
      have := fun hi => hne (row_inj hx hw ht'.1 ht hg (by rw [ht'.2, h0]) hi)
      have e1 := rowIx_even w; have e2 := rowIx_even x
      have n1 : rowIx w ≠ rowIx x := fun e => this e.symm
      have n2 : rowIx w + 1 ≠ rowIx x := by omega
      have n3 : rowIx w ≠ rowIx x + 1 := by omega
      have n4 : rowIx w + 1 ≠ rowIx x + 1 := by omega
      rw [ha]
      simp [baseSet, rdN, Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, ixW_toNat, rowIx_mod, n1, n2, n3]
    · simp [baseSet, Mem.arr64_set64_ne _ _ _ _ _ ha]
  · simp only [baseRow, ht', ite_false]

theorem baseTbl_baseTblSet_self {m : Mem} {w r p : Word} (ht : rowTag w ≤ 2) (h0 : rowTier w = 0)
    (hb : rowIx w + 1 < (m.arr64 (tixArr (rowTag w))).size) :
    baseTbl (baseTblSet m w r p) w = (r, p) := by
  simp [baseTbl, baseTblSet, ht, h0, rdN, ixW_toNat, hb, Nat.lt_of_succ_lt hb, rowIx_mod,
    Mem.arr64_set64_same, Array.set!_eq_setIfInBounds,
    Array.size_setIfInBounds]

theorem baseTbl_baseTblSet_other {m : Mem} {w r p x : Word} (hw : w.toNat < 2 ^ 32)
    (hx : x.toNat < 2 ^ 32) (ht : rowTag w ≤ 2) (h0 : rowTier w = 0) (hne : x ≠ w) :
    baseTbl (baseTblSet m w r p) x = baseTbl m x := by
  by_cases ht' : rowTag x ≤ 2 ∧ rowTier x = 0
  · simp only [baseTbl, ht', and_self, ite_true]
    by_cases ha : (tixArr (rowTag x) : TieredArray) = tixArr (rowTag w)
    · have hg := tixArr_inj ht'.1 ht (TieredArray.t0_inj.mp ha)
      have := fun hi => hne (row_inj hx hw ht'.1 ht hg (by rw [ht'.2, h0]) hi)
      have e1 := rowIx_even w; have e2 := rowIx_even x
      have n1 : rowIx w ≠ rowIx x := fun e => this e.symm
      have n2 : rowIx w + 1 ≠ rowIx x := by omega
      have n3 : rowIx w ≠ rowIx x + 1 := by omega
      have n4 : rowIx w + 1 ≠ rowIx x + 1 := by omega
      rw [ha]
      simp [baseTblSet, rdN, Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, ixW_toNat, rowIx_mod, n1, n2, n3]
    · simp [baseTblSet, Mem.arr64_set64_ne _ _ _ _ _ ha]
  · simp only [baseTbl, ht', ite_false]

end rel

section specs
set_option linter.unusedSimpArgs false
open ConRon.Arena Std.WP
open scoped Lean.Order
set_option experimental.vcgen true
variable (p : Prog)

theorem envRowGet_spec (hp : p.lookup "env_row_get" = some envRowGetL) (n : Nat) (s₀ : St)
    (w : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "env_row_get" [w]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ r = [(ownRaw s₀.mem w).1, (ownRaw s₀.mem w).2]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, envRowGetL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, L.evalC_spec, L.evalE_spec, evalArgs, setLoc, setLocs]
    all_goals simp only [Cond.pval, Expr.pval, Expr.pval_tagE, Expr.pval_tierE, Expr.pval_idxE,
      St.setLoc_loc, L.St.setLoc_mem, Locals.init_cons_zero, Cmp.eval, BinOp.eval, rd64_rdWC,
      beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at *
    all_goals subst_vars
    all_goals simp_all [LocEq, Sig.retVal, Sig.retOr, ownRaw_0, ownRaw_1, ownRaw_2]

theorem envRowSet_spec (hp : p.lookup "env_row_set" = some envRowSetL) (n : Nat) (s₀ : St)
    (w c q : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "env_row_set" [w, c, q]
    ⦃fun _ s' => s'.mem = ownSet s₀.mem w c q ∧ LocEq s' s₀ ∧ rowTag w ≤ 2 ∧
      rowIx w + 1 < (s₀.mem.arr64 (ownArr w)).size; ⊤⦄ := by
  have h1 := ixW_succ w
  rw [invoke_eq _ hp]
  simp only [callFn, envRowSetL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, L.evalC_spec, L.evalE_spec, evalArgs, setLoc, setLocs, st64]
    all_goals simp only [Cond.pval, Expr.pval, Expr.pval_tagE, Expr.pval_tierE, Expr.pval_idxE,
      St.setLoc_loc, L.St.setLoc_mem, Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval,
      rd64_rdWC, beq_iff_eq, bne_iff_ne, ne_eq] at *
    all_goals subst_vars
    all_goals simp_all [LocEq, Sig.retVal, Sig.retOr, ownSet, ownArr_0, ownArr_1, ownArr_2, rowWord,
      rowTag_of, ixW, Mem.arr64_set64_same, Array.size_set!]

theorem baseRowGet_spec (hp : p.lookup "base_row_get" = some baseRowGetL) (n : Nat) (s₀ : St)
    (w : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "base_row_get" [w]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ r = [(baseRow s₀.mem w).1, (baseRow s₀.mem w).2]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, baseRowGetL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, L.evalC_spec, L.evalE_spec, evalArgs, setLoc, setLocs]
    all_goals simp only [Cond.pval, Expr.pval, Expr.pval_tagE, Expr.pval_tierE, Expr.pval_idxE,
      St.setLoc_loc, L.St.setLoc_mem, Locals.init_cons_zero, Cmp.eval, BinOp.eval, rd64_rdWC,
      beq_iff_eq, bne_iff_ne, ne_eq] at *
    all_goals subst_vars
    all_goals simp_all [LocEq, Sig.retVal, Sig.retOr, baseRow_t1, baseRow_0, baseRow_1, baseRow_2]

theorem tblBaseGet_spec (hp : p.lookup "tbl_base_get" = some tblBaseGetL) (n : Nat) (s₀ : St)
    (w : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "tbl_base_get" [w]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ r = [(baseTbl s₀.mem w).1, (baseTbl s₀.mem w).2]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, tblBaseGetL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, L.evalC_spec, L.evalE_spec, evalArgs, setLoc, setLocs]
    all_goals simp only [Cond.pval, Expr.pval, Expr.pval_tagE, Expr.pval_tierE, Expr.pval_idxE,
      St.setLoc_loc, L.St.setLoc_mem, Locals.init_cons_zero, Cmp.eval, BinOp.eval, rd64_rdWC,
      beq_iff_eq, bne_iff_ne, ne_eq] at *
    all_goals subst_vars
    all_goals simp_all [LocEq, Sig.retVal, Sig.retOr, baseTbl_t1, baseTbl_0, baseTbl_1, baseTbl_2]

theorem tblOwnGet_spec (hp : p.lookup "tbl_own_get" = some tblOwnGetL) (n : Nat) (s₀ : St)
    (w : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "tbl_own_get" [w]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ r = [ownTbl s₀.mem w]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, tblOwnGetL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, L.evalC_spec, L.evalE_spec, evalArgs, setLoc, setLocs]
    all_goals simp only [Cond.pval, Expr.pval, Expr.pval_tagE, Expr.pval_tierE, Expr.pval_idxE,
      St.setLoc_loc, L.St.setLoc_mem, Locals.init_cons_zero, Cmp.eval, BinOp.eval, rd64_rdWC,
      beq_iff_eq, bne_iff_ne, ne_eq] at *
    all_goals subst_vars
    all_goals simp_all [LocEq, Sig.retVal, Sig.retOr, ownTbl_0, ownTbl_1, ownTbl_2]

theorem tblOwnSet_spec (hp : p.lookup "tbl_own_set" = some tblOwnSetL) (n : Nat) (s₀ : St)
    (w v : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "tbl_own_set" [w, v]
    ⦃fun _ s' => s'.mem = tblSet s₀.mem w v ∧ LocEq s' s₀ ∧ rowTag w ≤ 2 ∧
      rowIx w + 1 < (s₀.mem.arr64 (otxArrT w)).size; ⊤⦄ := by
  have h1 := ixW_succ w
  rw [invoke_eq _ hp]
  simp only [callFn, tblOwnSetL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, L.evalC_spec, L.evalE_spec, evalArgs, setLoc, setLocs, st64]
    all_goals simp only [Cond.pval, Expr.pval, Expr.pval_tagE, Expr.pval_tierE, Expr.pval_idxE,
      St.setLoc_loc, L.St.setLoc_mem, Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval,
      rd64_rdWC, beq_iff_eq, bne_iff_ne, ne_eq] at *
    all_goals subst_vars
    all_goals simp_all [LocEq, Sig.retVal, Sig.retOr, tblSet, otxArrT_0, otxArrT_1, otxArrT_2,
      rowTag_of, ixW, Mem.arr64_set64_same, Array.size_set!]

/-- What `env_find(w, vis)` returns. -/
def findRes (m : Mem) (vis w : Word) : List Word :=
  if ownHit m vis w then [1, (ownRaw m w).2] else if baseHit m w then [1, (baseRow m w).2] else [0, 0]

/-- What `raw_table(t)` returns. -/
def rawRes (m : Mem) (t : Word) : Word :=
  if ownTbl m t ≠ 0 then ownTbl m t else if baseTblHit m t then (baseTbl m t).2 + 1 else 0

/-- What `find_table(vis, t)` returns. -/
def findTblRes (m : Mem) (vis t : Word) : Word :=
  if (findRes m vis t).headD 0 = 0 then 0 else rawRes m t

theorem envFind_spec (hg : p.lookup "env_row_get" = some envRowGetL)
    (hb : p.lookup "base_row_get" = some baseRowGetL) (hp : p.lookup "env_find" = some envFindL)
    (n : Nat) (s₀ : St) (vis w : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "env_find" [w, vis]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ r = findRes s₀.mem vis w; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, envFindL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, L.evalC_spec, L.evalE_spec, evalArgs, setLoc, setLocs,
      envRowGet_spec p hg n, baseRowGet_spec p hb n]
    all_goals simp only [Cond.pval, Expr.pval, St.setLoc_loc, L.St.setLoc_mem, St.setLocs_cons,
      St.setLocs_nil, Locals.init, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil,
      Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval, rd64_rdWC, beq_iff_eq,
      bne_iff_ne, ne_eq] at *
    all_goals subst_vars
    all_goals (simp_all [LocEq, Sig.retVal, Sig.retOr, findRes, ownHit, baseHit, ctl_t0, Locals.init,
      List.getD_cons_zero, List.getD_cons_succ, UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le] <;>
      first | omega | (split <;> (try split) <;> first | omega | rfl))

/-- `find?` from `env_find`'s result. -/
theorem EnvR.find_res {m : Mem} {vis : Word} {fe : IFEnv} (hE : EnvR m vis fe) {w : Word}
    (hw : w.toNat < 2 ^ 32) :
    fe.find? (decI w) = envFound m ((findRes m vis w).headD 0) ((findRes m vis w).tail.headD 0) ∧
      ((findRes m vis w).headD 0 ≠ 0 →
        ∃ ci, decCI (erecP m) ((findRes m vis w).tail.headD 0).toNat = some ci) := by
  have key := hE.find_eq hw
  have kd := hE.hit_dec hw
  unfold findRes
  by_cases h1 : ownHit m vis w
  · simp [h1, key, envFound, kd.1 h1]
  · by_cases h2 : baseHit m w
    · simp [h1, h2, key, envFound, kd.2 h2]
    · simp [h1, h2, key, envFound]

/-- **`env_find` refines `IFEnv.find?`**: the result decodes to the twin's lookup, and a found
record decodes. -/
@[refines ConRon.Arena.IFEnv.find?]
theorem envFind_refines (hg : p.lookup "env_row_get" = some envRowGetL)
    (hb : p.lookup "base_row_get" = some baseRowGetL) (hp : p.lookup "env_find" = some envFindL)
    (n : Nat) (s₀ : St) {fe : IFEnv} (vis w : Word)
    (hE : EnvR s₀.mem vis fe) (hw : w.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "env_find" [w, vis]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧
      fe.find? (decI w) = envFound s₀.mem (r.headD 0) (r.tail.headD 0) ∧
      (r.headD 0 ≠ 0 → ∃ ci, decCI (erecP s₀.mem) (r.tail.headD 0).toNat = some ci); ⊤⦄ :=
  triple_post (envFind_spec p hg hb hp n s₀ vis w) fun r s ⟨h1, h2, h3⟩ => by
    subst h3; exact ⟨h1, h2, hE.find_res hw⟩

theorem rawTable_spec (ho : p.lookup "tbl_own_get" = some tblOwnGetL)
    (hb : p.lookup "tbl_base_get" = some tblBaseGetL) (hp : p.lookup "raw_table" = some rawTableL)
    (n : Nat) (s₀ : St) (t : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "raw_table" [t]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ r = [rawRes s₀.mem t]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, rawTableL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, L.evalC_spec, L.evalE_spec, evalArgs, setLoc, setLocs,
      tblOwnGet_spec p ho n, tblBaseGet_spec p hb n]
    all_goals simp only [Cond.pval, Expr.pval, St.setLoc_loc, L.St.setLoc_mem, St.setLocs_cons,
      St.setLocs_nil, Locals.init, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil,
      Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval, rd64_rdWC, beq_iff_eq,
      bne_iff_ne, ne_eq] at *
    all_goals subst_vars
    all_goals (simp_all [LocEq, Sig.retVal, Sig.retOr, rawRes, baseTblHit, ctl_t0, Locals.init,
      List.getD_cons_zero, List.getD_cons_succ, UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le] <;>
      first | omega | (split <;> (try split) <;> first | omega | rfl))

/-- `rawTable?` from `raw_table`'s result. -/
theorem EnvR.rawTable_res {m : Mem} {vis : Word} {fe : IFEnv} (hE : EnvR m vis fe) {t : Word}
    (ht : t.toNat < 2 ^ 32) :
    fe.rawTable? (decI t) = tblFound m (rawRes m t) ∧
      (rawRes m t ≠ 0 → ∃ tb, decTbl (erecP m) ((rawRes m t).toNat - 1) = some tb) := by
  have key := hE.rawTable_eq ht
  have kd := hE.tblHit_dec ht
  unfold rawRes
  by_cases h1 : ownTbl m t ≠ 0
  · simp only [h1, ne_eq, not_false_eq_true, ite_true] at key ⊢
    exact ⟨by simp [key, tblFound, h1], fun _ => kd.1 h1⟩
  · simp only [h1, ite_false] at key ⊢
    by_cases h2 : baseTblHit m t
    · obtain ⟨tb, htb⟩ := kd.2 h2
      obtain ⟨e1, e2⟩ := tblFound_succ htb
      have := decTbl_lt htb
      have e3 : ((baseTbl m t).2 + 1).toNat - 1 = (baseTbl m t).2.toNat := by
        rw [UInt64.toNat_add]; simp; omega
      simp only [h2, ite_true] at key ⊢
      exact ⟨by rw [key, e1], fun _ => ⟨tb, by rw [e3]; exact htb⟩⟩
    · simp only [h2, ite_false] at key ⊢
      exact ⟨by simp [key, tblFound], fun h => absurd rfl h⟩

/-- **`raw_table` refines `IFEnv.rawTable?`**: the result decodes to the twin's table. -/
@[refines ConRon.Arena.IFEnv.rawTable?]
theorem rawTable_refines (ho : p.lookup "tbl_own_get" = some tblOwnGetL)
    (hb : p.lookup "tbl_base_get" = some tblBaseGetL) (hp : p.lookup "raw_table" = some rawTableL)
    (n : Nat) (s₀ : St) {fe : IFEnv} (vis t : Word)
    (hE : EnvR s₀.mem vis fe) (ht : t.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "raw_table" [t]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧
      fe.rawTable? (decI t) = tblFound s₀.mem (r.headD 0) ∧
      (r.headD 0 ≠ 0 → ∃ tb, decTbl (erecP s₀.mem) ((r.headD 0).toNat - 1) = some tb); ⊤⦄ :=
  triple_post (rawTable_spec p ho hb hp n s₀ t) fun r s ⟨h1, h2, h3⟩ => by
    subst h3; exact ⟨h1, h2, hE.rawTable_res ht⟩

/-- The `env_find`/`raw_table` lookups `find_table` makes. -/
structure FindTableProg (p : Prog) : Prop where
  rowGet : p.lookup "env_row_get" = some envRowGetL
  baseGet : p.lookup "base_row_get" = some baseRowGetL
  find : p.lookup "env_find" = some envFindL
  tblOwn : p.lookup "tbl_own_get" = some tblOwnGetL
  tblBase : p.lookup "tbl_base_get" = some tblBaseGetL
  raw : p.lookup "raw_table" = some rawTableL
  findTable : p.lookup "find_table" = some findTableL

theorem findTable_spec (hP : FindTableProg p) (n : Nat) (s₀ : St) (vis t : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "find_table" [vis, t]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ r = [findTblRes s₀.mem vis t]; ⊤⦄ := by
  rw [invoke_eq _ hP.findTable]
  simp only [callFn, findTableL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, L.evalC_spec, L.evalE_spec, evalArgs, setLoc, setLocs,
      envFind_spec p hP.rowGet hP.baseGet hP.find n, rawTable_spec p hP.tblOwn hP.tblBase hP.raw n]
    all_goals simp only [Cond.pval, Expr.pval, St.setLoc_loc, L.St.setLoc_mem, St.setLocs_cons,
      St.setLocs_nil, Locals.init, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil,
      Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval, rd64_rdWC, beq_iff_eq,
      bne_iff_ne, ne_eq] at *
    all_goals subst_vars
    all_goals simp_all [LocEq, Sig.retVal, Sig.retOr, findTblRes, Locals.init,
      List.getD_cons_zero, List.getD_cons_succ]

/-- **`find_table` refines `IFEnv.findTable?`**: the result decodes to the twin's table. -/
@[refines ConRon.Arena.IFEnv.findTable?]
theorem findTable_refines (hP : FindTableProg p) (n : Nat) (s₀ : St) {fe : IFEnv} (vis t : Word)
    (hE : EnvR s₀.mem vis fe) (ht : t.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "find_table" [vis, t]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧
      fe.findTable? (decI t) = tblFound s₀.mem (r.headD 0) ∧
      (r.headD 0 ≠ 0 → ∃ tb, decTbl (erecP s₀.mem) ((r.headD 0).toNat - 1) = some tb); ⊤⦄ :=
  triple_post (findTable_spec p hP n s₀ vis t) fun r s ⟨h1, h2, h3⟩ => by
    subst h3
    refine ⟨h1, h2, ?_⟩
    obtain ⟨f1, f2⟩ := hE.find_res ht
    obtain ⟨r1, r2⟩ := hE.rawTable_res ht
    simp only [List.headD_cons]
    rw [IFEnv.findTable?, f1]
    by_cases h0 : (findRes s₀.mem vis t).headD 0 = 0
    · simp only [envFound, findTblRes, h0, ite_true, Option.isSome_none]
      exact ⟨by simp [tblFound], fun h => absurd rfl h⟩
    · obtain ⟨ci, hci⟩ := f2 h0
      simp only [envFound, findTblRes, h0, ite_false, hci, Option.isSome_some, ite_true]
      exact ⟨r1, r2⟩

/-- The word L's tagged read `EREC⦃a⦄` reads. -/
def erecRd (m : Mem) (a : Word) : Word := rdW (m.arr64 (tierA EREC (a >>> 40))) (a &&& 1099511627775)

theorem erecRd_of {m : Mem} {a v : Word} (h : erecP m a.toNat = some v) : erecRd m a = v := by
  obtain ⟨h1, h2⟩ := erecP_tagRead h
  simp only [erecRd, rdW, h2]; rfl

theorem envPush_spec (hs : p.lookup "env_row_set" = some envRowSetL)
    (hp : p.lookup "env_push" = some envPushL) (n : Nat) (s₀ : St) (vis q : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "env_push" [vis, q]
    ⦃fun r s' => s'.mem = ownSet s₀.mem (erecRd s₀.mem (q + (CI.cv + CV.name))) (vis + 1) q ∧ LocEq s' s₀ ∧
      r = [vis + 1] ∧ vis.toNat < 4294967294 ∧ rowTag (erecRd s₀.mem (q + (CI.cv + CV.name))) ≤ 2 ∧
      rowIx (erecRd s₀.mem (q + (CI.cv + CV.name))) + 1 < (s₀.mem.arr64 (ownArr (erecRd s₀.mem (q + (CI.cv + CV.name))))).size; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, envPushL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, L.evalC_spec, L.evalE_spec, evalArgs, setLoc, setLocs, envRowSet_spec p hs n]
    all_goals simp only [Cond.pval, Expr.pval, St.setLoc_loc, L.St.setLoc_mem, St.setLocs_cons,
      St.setLocs_nil, Locals.init, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil,
      Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval, rd64_rdWC, beq_iff_eq,
      bne_iff_ne, ne_eq] at *
    all_goals subst_vars
    all_goals simp_all [LocEq, Sig.retVal, Sig.retOr, erecRd, Locals.init, List.getD_cons_zero,
      List.getD_cons_succ, UInt64.le_iff_toNat_le, St.setLoc_loc]

/-- **`env_push` refines `IFEnv.push`**: the new view `vis + 1` of the result relates the pushed
environment. -/
@[refines ConRon.Arena.IFEnv.push]
theorem envPush_refines (hs : p.lookup "env_row_set" = some envRowSetL)
    (hp : p.lookup "env_push" = some envPushL) (n : Nat) (s₀ : St) {fe : IFEnv} {ci : IConstantInfo}
    (vis q : Word) (hE : EnvR s₀.mem vis fe) (hci : decCI (erecP s₀.mem) q.toNat = some ci) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "env_push" [vis, q]
    ⦃fun r s' => LocEq s' s₀ ∧ r = [vis + 1] ∧ EnvR s'.mem (vis + 1) (fe.push ci) ∧
      s'.mem = ownSet s₀.mem (erecRd s₀.mem (q + (CI.cv + CV.name))) (vis + 1) q; ⊤⦄ := by
  sorry

theorem envPopTemp_spec (hs : p.lookup "env_row_set" = some envRowSetL)
    (hp : p.lookup "env_pop_temp" = some envPopTempL) (n : Nat) (s₀ : St) (vis w c q : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "env_pop_temp" [vis, w, c, q]
    ⦃fun r s' => s'.mem = ownSet s₀.mem w c q ∧ LocEq s' s₀ ∧
      r = [if vis = 0 then 0 else vis - 1] ∧ rowTag w ≤ 2 ∧
      rowIx w + 1 < (s₀.mem.arr64 (ownArr w)).size; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, envPopTempL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, L.evalC_spec, L.evalE_spec, evalArgs, setLoc, setLocs, envRowSet_spec p hs n]
    all_goals simp only [Cond.pval, Expr.pval, St.setLoc_loc, L.St.setLoc_mem, St.setLocs_cons,
      St.setLocs_nil, Locals.init, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil,
      Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval, rd64_rdWC, beq_iff_eq,
      bne_iff_ne, ne_eq] at *
    all_goals subst_vars
    all_goals simp_all [LocEq, Sig.retVal, Sig.retOr, Locals.init, List.getD_cons_zero,
      List.getD_cons_succ, St.setLoc_loc]

/-- **`env_pop_temp` refines `IFEnv.popTemp`** at the newest push of `w` (counter `vis`), with
`(c, q)` the row `env_row_get` read before that push (`prev` its decoding). -/
@[refines ConRon.Arena.IFEnv.popTemp]
theorem envPopTemp_refines (hs : p.lookup "env_row_set" = some envRowSetL)
    (hp : p.lookup "env_pop_temp" = some envPopTempL) (n : Nat) (s₀ : St) {fe : IFEnv}
    (vis w c q : Word) (hE : EnvR s₀.mem vis fe) (hw : w.toNat < 2 ^ 32) (hv : vis ≠ 0)
    (htop : (ownRaw s₀.mem w).1 = vis) (hc32 : c.toNat < 2 ^ 32)
    (hcv : c ≠ 0 → c.toNat - 1 < vis.toNat - 1)
    (hcd : c ≠ 0 → ∃ ci, decCI (erecP s₀.mem) q.toNat = some ci)
    (hfree : c ≠ 0 → ∀ n : NIdx, n.word.toUInt64 ≠ w → (ownRaw s₀.mem n.word.toUInt64).1 ≠ c) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "env_pop_temp" [vis, w, c, q]
    ⦃fun r s' => LocEq s' s₀ ∧ r = [vis - 1] ∧
      EnvR s'.mem (vis - 1) (fe.popTemp (decI w) (if c = 0 then none else decCI (erecP s₀.mem) q.toNat)) ∧
      s'.mem = ownSet s₀.mem w c q; ⊤⦄ :=
  triple_post (envPopTemp_spec p hs hp n s₀ vis w c q) fun r s ⟨h1, h2, h3, h4, h5⟩ => by
    refine ⟨h2, by rw [h3, ite_eq_right hv], ?_, h1⟩
    rw [h1]; exact hE.popTemp hw h4 h5 hv htop hc32 hcv hcd hfree

theorem envPushTable_spec (hs : p.lookup "tbl_own_set" = some tblOwnSetL)
    (hp : p.lookup "env_push_table" = some envPushTableL) (n : Nat) (s₀ : St) (q : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "env_push_table" [q]
    ⦃fun r s' => s'.mem = tblSet s₀.mem (erecRd s₀.mem (q + ProjTbl.structName)) (q + 1) ∧ LocEq s' s₀ ∧
      r = [0] ∧ rowTag (erecRd s₀.mem (q + ProjTbl.structName)) ≤ 2 ∧
      rowIx (erecRd s₀.mem (q + ProjTbl.structName)) + 1 < (s₀.mem.arr64 (otxArrT (erecRd s₀.mem (q + ProjTbl.structName)))).size; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, envPushTableL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, L.evalC_spec, L.evalE_spec, evalArgs, setLoc, setLocs, tblOwnSet_spec p hs n]
    all_goals simp only [Cond.pval, Expr.pval, St.setLoc_loc, L.St.setLoc_mem, St.setLocs_cons,
      St.setLocs_nil, Locals.init, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil,
      Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval, rd64_rdWC, beq_iff_eq,
      bne_iff_ne, ne_eq] at *
    all_goals subst_vars
    all_goals simp_all [LocEq, Sig.retVal, Sig.retOr, erecRd, Locals.init, List.getD_cons_zero,
      List.getD_cons_succ, St.setLoc_loc]

/-- **`env_push_table` refines `IFEnv.pushTable`**. -/
@[refines ConRon.Arena.IFEnv.pushTable]
theorem envPushTable_refines (hs : p.lookup "tbl_own_set" = some tblOwnSetL)
    (hp : p.lookup "env_push_table" = some envPushTableL) (n : Nat) (s₀ : St) {fe : IFEnv}
    {tb : IProjTable} (vis q : Word) (hE : EnvR s₀.mem vis fe)
    (htb : decTbl (erecP s₀.mem) q.toNat = some tb) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "env_push_table" [q]
    ⦃fun _ s' => LocEq s' s₀ ∧ EnvR s'.mem vis (fe.pushTable tb) ∧
      s'.mem = tblSet s₀.mem (erecRd s₀.mem (q + ProjTbl.structName)) (q + 1); ⊤⦄ :=
  triple_post (envPushTable_spec p hs hp n s₀ q) fun r s ⟨h1, h2, h3, h5, h6⟩ => by
    obtain ⟨w, hw, -, -⟩ := decTbl_name htb
    have hq : (q + ProjTbl.structName).toNat = q.toNat + ProjTbl.structName.toNat :=
      off_add_toNat rfl (erecP_lt64 hw)
    have hr : erecRd s₀.mem (q + ProjTbl.structName) = w := erecRd_of (by rw [hq]; exact hw)
    rw [hr] at h5 h6
    exact ⟨h2, by rw [h1, hr]; exact hE.pushTable htb hw h5 h6, h1⟩

theorem baseRowSet_spec (hp : p.lookup "base_row_set" = some baseRowSetL) (n : Nat) (s₀ : St)
    (w c q : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "base_row_set" [w, c, q]
    ⦃fun _ s' => s'.mem = baseSet s₀.mem w c q ∧ LocEq s' s₀ ∧ rowTag w ≤ 2 ∧ rowTier w = 0 ∧
      rowIx w + 1 < (s₀.mem.arr64 (eixArr (rowTag w))).size; ⊤⦄ := by
  have h1 := ixW_succ w
  rw [invoke_eq _ hp]
  simp only [callFn, baseRowSetL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, L.evalC_spec, L.evalE_spec, evalArgs, setLoc, setLocs, st64]
    all_goals simp only [Cond.pval, Expr.pval, Expr.pval_tagE, Expr.pval_tierE, Expr.pval_idxE,
      St.setLoc_loc, L.St.setLoc_mem, Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval,
      rd64_rdWC, beq_iff_eq, bne_iff_ne, ne_eq] at *
    all_goals subst_vars
    all_goals simp_all [LocEq, Sig.retVal, Sig.retOr, baseSet, eixArr_0, eixArr_1, eixArr_2,
      rowTag_of, rowTier_of, ixW, Mem.arr64_set64_same, Array.size_set!, eixArr, tixArr]

theorem tblBaseSet_spec (hp : p.lookup "tbl_base_set" = some tblBaseSetL) (n : Nat) (s₀ : St)
    (w r q : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "tbl_base_set" [w, r, q]
    ⦃fun _ s' => s'.mem = baseTblSet s₀.mem w r q ∧ LocEq s' s₀ ∧ rowTag w ≤ 2 ∧ rowTier w = 0 ∧
      rowIx w + 1 < (s₀.mem.arr64 (tixArr (rowTag w))).size; ⊤⦄ := by
  have h1 := ixW_succ w
  rw [invoke_eq _ hp]
  simp only [callFn, tblBaseSetL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, L.evalC_spec, L.evalE_spec, evalArgs, setLoc, setLocs, st64]
    all_goals simp only [Cond.pval, Expr.pval, Expr.pval_tagE, Expr.pval_tierE, Expr.pval_idxE,
      St.setLoc_loc, L.St.setLoc_mem, Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval,
      rd64_rdWC, beq_iff_eq, bne_iff_ne, ne_eq] at *
    all_goals subst_vars
    all_goals simp_all [LocEq, Sig.retVal, Sig.retOr, baseTblSet, tixArr_0, tixArr_1, tixArr_2,
      rowTag_of, rowTier_of, ixW, Mem.arr64_set64_same, Array.size_set!, eixArr, tixArr]

end specs

end L.Arena
