module

public import ConAgua.Arena.Tiers
public import ConAgua.L.Logic
import ConAgua.Census.Attr
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

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
-- con-ron: ConRon/Arena/Env.lean:272-275 ConRon.Arena.IFEnv.find?
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

/-- `env_push(vis, q)`: push the record at `q` (its name is word `q + 1`) into the own layer at
counter `vis`; returns the new view `vis + 1`. -/
-- con-ron: ConRon/Arena/Env.lean:277-280 ConRon.Arena.IFEnv.push
@[no_expose, l_impl ConRon.Arena.IFEnv.push]
def envPushL : FunDecl := lfn (vis, q) locals (w, z) {
  if 4294967294 <= vis { abort };
  w := EREC⦃q + 1⦄;
  z := call env_row_set(w, vis + 1, q);
  return vis + 1
}

/-- `env_pop_temp(vis, w, c, q)`: undo a temporary push of name `w`: its own row put back to
`(c, q)` (`IFEnv.popTemp`'s `prev`), the view lowered. -/
-- con-ron: ConRon/Arena/Env.lean:288-298 ConRon.Arena.IFEnv.popTemp
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
-- con-ron: ConRon/Arena/Env.lean:300-305 ConRon.Arena.IFEnv.rawTable?
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
-- con-ron: ConRon/Arena/Env.lean:307-310 ConRon.Arena.IFEnv.findTable?
@[no_expose, l_impl ConRon.Arena.IFEnv.findTable?]
def findTableL : FunDecl := lfn (vis, t) locals (f, q, r) {
  (f, q) := call env_find(t, vis);
  if f == 0 { return 0 };
  r := call raw_table(t);
  return r
}

/-- `env_push_table(q)`: install the table record at `q` (its structure name is word `q + 2`)
in the own layer (`IFEnv.pushTable`). -/
-- con-ron: ConRon/Arena/Env.lean:282-286 ConRon.Arena.IFEnv.pushTable
@[no_expose, l_impl ConRon.Arena.IFEnv.pushTable]
def envPushTableL : FunDecl := lfn (q) locals (w, z) {
  w := EREC⦃q + 2⦄;
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

theorem hd?_some {k : IdxKind} {a : Nat → Option Word} {i : Nat} {x : Idx k} (h : hd? a i = some x) :
    ∃ w, a i = some w ∧ w.toNat < 2 ^ 32 ∧ x = decI w := by
  cases e : a i with
  | none => simp [hd?, e] at h
  | some w => simp [hd?, e] at h; exact ⟨w, rfl, h.1, h.2.symm⟩

theorem decCV_name {a : Nat → Option Word} {q : Nat} {cv : IConstantVal} (h : decCV a q = some cv) :
    ∃ w, a q = some w ∧ w.toNat < 2 ^ 32 ∧ cv.name = decI w := by
  sorry

theorem decCI_name {a : Nat → Option Word} {p : Nat} {ci : IConstantInfo} (h : decCI a p = some ci) :
    ∃ w, a (p + 1) = some w ∧ w.toNat < 2 ^ 32 ∧ ci.name = decI w := by
  sorry

theorem triple_post {α : Type} {prog : M α} {P : St → Prop} {Q Q' : α → St → Prop}
    (h : ⦃fun s => P s⦄ prog ⦃fun r s => Q r s; ⊤⦄) (hq : ∀ r s, Q r s → Q' r s) :
    ⦃fun s => P s⦄ prog ⦃fun r s => Q' r s; ⊤⦄ :=
  M.triple_of_run fun _ _ _ hp hr => hq _ _ (M.of_run hp hr h)

end helpers

end L.Arena
