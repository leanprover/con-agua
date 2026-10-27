import ConAgua.Arena.WhnfBase

/-!
# `instantiateLevelParams` in L: `inst_lp`, its walk, its three memos

con-ron's `instLPFast fuel ks us e` (`Arena/ExprOps.lean:2254`) substitutes the level parameters
`ks` (names) by the universe arguments `us` (a level list) throughout `e`, as a memoized DAG walk
`instLPGo` with six arms, and the two level arms behind their own memos `substLMemoAt`
(`instLPLC`, a level handle) and `substLsMemoAt` (`instLPLsC`, a level-list handle). Every memo is
cleared at entry and exit (`instLPClear`). In L:

| twin | L | memo |
|---|---|---|
| `instLPFast` | `inst_lp_core(ko, kc, us, e)` (the keys on the spine stack) | clears all three |
| `instLPGo`, `instLPArm*` | `lp_go(h, ko, kc, vo, vc, fu)`, `lp_fvar`, `lp_app`, `lp_lam`, `lp_forall`, `lp_let`, `lp_proj` | `instLPC`: array 52, `CTL[54‥55]`, key `(h, 0)` |
| `substLMemoAt` | `sl_memo(u, ko, kc, vo, vc)`: probe, else `lv_sub_int` | `instLPLC`: array 53, `CTL[56‥57]`, key `(u, 0)` |
| `substLsMemoAt` | `sls_memo(vs, ko, kc, vo, vc)`: probe, else `sls_go` over the list's pool slice, `spn_ls` | `instLPLsC`: array 54, `CTL[58‥59]`, key `(vs, 0)` |
| `substLevelsAt`, `substParamLevels`, `recFireLevels` | `sle_go`, `slp_go`, `rec_fire_levels` | none (as the twin) |

The substitution's keys are copied onto the spine stack first (`keys_push`, `keys_push_iw`), so
that `inst_lp(po, pl, us, e)` (an `EREC` name slice, lane `whnf`'s callers) and lane `induct`'s
`inst_lp_fast(fuel, lo, ll, us, e)` (an `IW` slice) share one walk; the values are the list's pool
slice (`ls_node`). A list of interned results is built on the stack above its top and copied to
the pool top for `intern_ls` (`spn_ls`).

**The cut-off** (deviation D23, fixed by helper `whnf4-d23`): as the twin, `lp_go` returns `h`
at once when `h`'s derived word has no level parameter, and `inst_lp_core` returns `e` before any
readback (`ls_node(us)`) or memo clear when `e`'s has none; the bit is `der_b`'s third result
(`exprLPW`, `derLW_ok`: `lpOfData (derived h)`, `LpCol.lean`).

The depth counter `fu` is the twin's `fuel`: `lp_go` aborts at `0` and passes
`fu - 1` to the arms, which pass it to their children; the entry starts at `4000000000`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The three memos -/

/-- `instLPC`: array 52, stamp `CTL[54]`, count `CTL[55]`. -/
abbrev lpSch : MemoSch := ⟨LPMEMO, 54⟩
/-- `instLPLC`: array 53, stamp `CTL[56]`, count `CTL[57]`. -/
abbrev lplSch : MemoSch := ⟨LPLMEMO, 56⟩
/-- `instLPLsC`: array 54, stamp `CTL[58]`, count `CTL[59]`. -/
abbrev lplsSch : MemoSch := ⟨LPLSMEMO, 58⟩

/-! ## `keys_push_iw(lo, ll)`: an `IW` name slice onto the spine stack -/

/-- con-ron: none — the substitution's keys copied onto the spine stack (`lp_lookup`'s key array) -/
def ikCopy : FunDecl := lfn (s, d, l) locals (r) {
  if l == 0 { return 0 };
  SPN.u64[d] := LPIW.u64[s];
  r := call ik_copy(s + 1, d + 1, l - 1);
  return r
}

/-- con-ron: none — the substitution's keys copied onto the spine stack (`lp_lookup`'s key array) -/
def keysPushIW : FunDecl := lfn (lo, ll) locals (b, r) {
  b := CTL.u64[136];
  if len(SPN.u64) < b { abort };
  if len(SPN.u64) - b < ll { abort };
  r := call ik_copy(lo, b, ll);
  CTL.u64[136] := b + ll;
  return b
}

/-! ## Level lists: substitute each element, intern the list -/

/-- con-ron: ConRon/Arena/ExprOps.lean:2062-2069 ConRon.Arena.substLevelList
con-ron: ConRon/Arena/Monad.lean:525-531 ConRon.Arena.internLevelList -/
@[l_impl ConRon.Arena.substLevelList]
def slsGo : FunDecl := lfn (o, l, b, ko, kc, vo, vc) locals (h, r) {
  if l == 0 { return 0 };
  h := call lv_sub_int(POOL⦃o⦄, ko, kc, vo, vc);
  if h >= 4294967296 { abort };
  SPN.u64[b] := h;
  r := call sls_go(o + 1, l - 1, b + 1, ko, kc, vo, vc);
  return r
}

/-- con-ron: ConRon/Arena/Core.lean:1940-1950 ConRon.Arena.substLevelsAt -/
@[l_impl ConRon.Arena.substLevelsAt]
def sleGo : FunDecl := lfn (o, l, b, ko, kc, vo, vc) locals (h, r) {
  if l == 0 { return 0 };
  h := call lv_sub_int(EREC.u64[o], ko, kc, vo, vc);
  if h >= 4294967296 { abort };
  SPN.u64[b] := h;
  r := call sle_go(o + 1, l - 1, b + 1, ko, kc, vo, vc);
  return r
}

/-- con-ron: ConRon/Arena/Core.lean:1952-1962 ConRon.Arena.substParamLevels -/
@[l_impl ConRon.Arena.substParamLevels]
def slpGo : FunDecl := lfn (o, l, b, ko, kc, vo, vc) locals (f, v, h, r) {
  if l == 0 { return 0 };
  (f, v) := call lp_lookup(ko, kc, vo, vc, EREC.u64[o]);
  if f != 0 { h := call lv_intern(v) } else { h := call intern_param(EREC.u64[o]) };
  if h >= 4294967296 { abort };
  SPN.u64[b] := h;
  r := call slp_go(o + 1, l - 1, b + 1, ko, kc, vo, vc);
  return r
}

/-- con-ron: none — the stack slice copied to the pool top (the twin's list is a value) -/
def spnPool : FunDecl := lfn (b, d, l) locals (r, pt, pb) {
  if l == 0 { return 0 };
  pt := ⦃d⦄.tier;
  pb := ⦃d⦄.idx;
  POOL⟨pt⟩[pb] := SPN.u64[b];
  r := call spn_pool(b + 1, d + 1, l - 1);
  return r
}

/-- The stack slice `(b, l)` of level handles, copied to the pool top and interned as a list node.
con-ron: ConRon/Arena/Monad.lean:533-537 ConRon.Arena.internLevels -/
def spnLs : FunDecl := lfn (b, l) locals (top, r, h, pt, pb) {
  top := CTL.u64[0];
  pt := ⦃top⦄.tier;
  pb := ⦃top⦄.idx;
  if len(POOL⟨pt⟩) < pb { abort };
  if len(POOL⟨pt⟩) - pb < l { abort };
  r := call spn_pool(b, top, l);
  CTL.u64[0] := top + l;
  h := call intern_ls(top, l);
  if h >= 4294967296 { abort };
  return h
}

/-! ## The level memos -/

/-- con-ron: ConRon/Arena/ExprOps.lean:2071-2086 ConRon.Arena.substLMemoAt -/
@[l_impl ConRon.Arena.substLMemoAt]
def slMemo : FunDecl := lfn (u, ko, kc, vo, vc) locals (fd, j, e0, h, x) {
  (fd, j, e0) := call ilpl_find(u, 0);
  if fd != 0 { return LPLMEMO.u64[j * 4 + 3] };
  h := call lv_sub_int(u, ko, kc, vo, vc);
  if h >= 4294967296 { abort };
  (fd, j, e0) := call ilpl_find(u, 0);
  x := call ilpl_put(u, 0, h, fd, j);
  return h
}

/-- con-ron: ConRon/Arena/ExprOps.lean:2088-2098 ConRon.Arena.substLsMemoAt -/
@[l_impl ConRon.Arena.substLsMemoAt]
def slsMemo : FunDecl := lfn (vs, ko, kc, vo, vc) locals (fd, j, e0, o, l, b, r, x) {
  (fd, j, e0) := call ilpls_find(vs, 0);
  if fd != 0 { return LPLSMEMO.u64[j * 4 + 3] };
  (o, l) := call ls_node(vs);
  b := CTL.u64[136];
  if len(SPN.u64) < b { abort };
  if len(SPN.u64) - b < l { abort };
  x := call sls_go(o, l, b, ko, kc, vo, vc);
  r := call spn_ls(b, l);
  (fd, j, e0) := call ilpls_find(vs, 0);
  x := call ilpls_put(vs, 0, r, fd, j);
  return r
}

/-! ## The walk -/

/-- con-ron: ConRon/Arena/ExprOps.lean:2102-2134 ConRon.Arena.instLPGo -/
@[l_impl ConRon.Arena.instLPGo]
def lpGo : FunDecl := lfn (h, ko, kc, vo, vc, fu) locals (g, t, i, x, y, r) {
  if fu == 0 { abort };
  (x, y, r) := call der_b(h);
  if r == 0 { return h };
  g := h >> 28;
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if g == 0 { if BVAR⟨t⟩.count <= i { abort }; return h };
  if g == 8 { if LIT⟨t⟩.count <= i { abort }; return h };
  if g == 2 {
    if SORT⟨t⟩.count <= i { abort };
    x := SORT⟨t, i⟩.u;
    y := call sl_memo(x, ko, kc, vo, vc);
    if y == x { return h };
    r := call intern_sort(y);
    if r >= 4294967296 { abort };
    return r
  };
  if g == 3 {
    if CONST⟨t⟩.count <= i { abort };
    x := CONST⟨t, i⟩.us;
    r := CONST⟨t, i⟩.n;
    y := call sls_memo(x, ko, kc, vo, vc);
    if y == x { return h };
    r := call intern_const(r, y);
    if r >= 4294967296 { abort };
    return r
  };
  if g == 1 { if FVAR⟨t⟩.count <= i { abort }; r := call lp_fvar(h, ko, kc, vo, vc, fu - 1); return r };
  if g == 4 { if APP⟨t⟩.count <= i { abort }; r := call lp_app(h, ko, kc, vo, vc, fu - 1); return r };
  if g == 5 { if LAM⟨t⟩.count <= i { abort }; r := call lp_lam(h, ko, kc, vo, vc, fu - 1); return r };
  if g == 6 { if FORALL⟨t⟩.count <= i { abort }; r := call lp_forall(h, ko, kc, vo, vc, fu - 1); return r };
  if g == 7 { if LET⟨t⟩.count <= i { abort }; r := call lp_let(h, ko, kc, vo, vc, fu - 1); return r };
  if g == 9 { if PROJ⟨t⟩.count <= i { abort }; r := call lp_proj(h, ko, kc, vo, vc, fu - 1); return r };
  abort
}

/-- con-ron: ConRon/Arena/ExprOps.lean:2136-2147 ConRon.Arena.instLPArmFVar -/
@[l_impl ConRon.Arena.instLPArmFVar]
def lpFVar : FunDecl := lfn (h, ko, kc, vo, vc, fu) locals (fd, j, e0, t, i, ix, ty, x, r, u) {
  (fd, j, e0) := call ilp_find(h, 0);
  if fd != 0 { return LPMEMO.u64[j * 4 + 3] };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  ix := FVAR⟨t, i⟩.i;
  ty := FVAR⟨t, i⟩.ty;
  x := call lp_go(ty, ko, kc, vo, vc, fu);
  if x == ty { r := h } else { r := call intern_fvar(ix, x); if r >= 4294967296 { abort } };
  (fd, j, e0) := call ilp_find(h, 0);
  u := call ilp_put(h, 0, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:2149-2161 ConRon.Arena.instLPArmApp -/
@[l_impl ConRon.Arena.instLPArmApp]
def lpApp : FunDecl := lfn (h, ko, kc, vo, vc, fu) locals (fd, j, e0, t, i, f, a, x, y, r, u) {
  (fd, j, e0) := call ilp_find(h, 0);
  if fd != 0 { return LPMEMO.u64[j * 4 + 3] };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  f := APP⟨t, i⟩.f;
  a := APP⟨t, i⟩.a;
  x := call lp_go(f, ko, kc, vo, vc, fu);
  y := call lp_go(a, ko, kc, vo, vc, fu);
  if x == f && y == a { r := h } else { r := call mk_app(x, y); if r >= 4294967296 { abort } };
  (fd, j, e0) := call ilp_find(h, 0);
  u := call ilp_put(h, 0, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:2163-2175 ConRon.Arena.instLPArmLam -/
@[l_impl ConRon.Arena.instLPArmLam]
def lpLam : FunDecl := lfn (h, ko, kc, vo, vc, fu) locals (fd, j, e0, t, i, f, a, x, y, r, u) {
  (fd, j, e0) := call ilp_find(h, 0);
  if fd != 0 { return LPMEMO.u64[j * 4 + 3] };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  f := LAM⟨t, i⟩.ty;
  a := LAM⟨t, i⟩.b;
  x := call lp_go(f, ko, kc, vo, vc, fu);
  y := call lp_go(a, ko, kc, vo, vc, fu);
  if x == f && y == a { r := h } else { r := call mk_lam(x, y); if r >= 4294967296 { abort } };
  (fd, j, e0) := call ilp_find(h, 0);
  u := call ilp_put(h, 0, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:2177-2189 ConRon.Arena.instLPArmForallE -/
@[l_impl ConRon.Arena.instLPArmForallE]
def lpForall : FunDecl := lfn (h, ko, kc, vo, vc, fu) locals (fd, j, e0, t, i, f, a, x, y, r, u) {
  (fd, j, e0) := call ilp_find(h, 0);
  if fd != 0 { return LPMEMO.u64[j * 4 + 3] };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  f := FORALL⟨t, i⟩.ty;
  a := FORALL⟨t, i⟩.b;
  x := call lp_go(f, ko, kc, vo, vc, fu);
  y := call lp_go(a, ko, kc, vo, vc, fu);
  if x == f && y == a { r := h } else { r := call mk_forall(x, y); if r >= 4294967296 { abort } };
  (fd, j, e0) := call ilp_find(h, 0);
  u := call ilp_put(h, 0, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:2191-2204 ConRon.Arena.instLPArmLet -/
@[l_impl ConRon.Arena.instLPArmLet]
def lpLet : FunDecl := lfn (h, ko, kc, vo, vc, fu) locals (fd, j, e0, t, i, f, a, b, x, y, r, u) {
  (fd, j, e0) := call ilp_find(h, 0);
  if fd != 0 { return LPMEMO.u64[j * 4 + 3] };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  f := LET⟨t, i⟩.ty;
  a := LET⟨t, i⟩.v;
  b := LET⟨t, i⟩.b;
  x := call lp_go(f, ko, kc, vo, vc, fu);
  y := call lp_go(a, ko, kc, vo, vc, fu);
  r := call lp_let_tail(h, f, a, b, x, y, ko, kc, vo, vc, fu);
  (fd, j, e0) := call ilp_find(h, 0);
  u := call ilp_put(h, 0, r, fd, j);
  return r
}

/-- `lp_let`'s third child and rebuild (split out so that each function's spec stays small).
con-ron: none — the tail of `instLPArmLet` (ExprOps.lean:2191-2204), split out of `lp_let` -/
def lpLetTail : FunDecl := lfn (h, f, a, b, x, y, ko, kc, vo, vc, fu) locals (z, r) {
  z := call lp_go(b, ko, kc, vo, vc, fu);
  r := call lp_rb_let(h, f, a, b, x, y, z);
  return r
}

/-- `lp_let`'s rebuild: `h` when the three children came back equal, else `mk_let`.
con-ron: ConRon/Arena/ExprOps.lean:153-155 ConRon.Arena.internRebuiltLetE -/
def lpRbLet : FunDecl := lfn (h, f, a, b, x, y, z) locals (r) {
  if x == f && y == a { if z == b { return h } };
  r := call mk_let(x, y, z);
  if r >= 4294967296 { abort };
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:2206-2217 ConRon.Arena.instLPArmProj -/
@[l_impl ConRon.Arena.instLPArmProj]
def lpProj : FunDecl := lfn (h, ko, kc, vo, vc, fu) locals (fd, j, e0, t, i, nm, ix, e, x, r, u) {
  (fd, j, e0) := call ilp_find(h, 0);
  if fd != 0 { return LPMEMO.u64[j * 4 + 3] };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  nm := PROJ⟨t, i⟩.n;
  ix := PROJ⟨t, i⟩.i;
  e := PROJ⟨t, i⟩.e;
  x := call lp_go(e, ko, kc, vo, vc, fu);
  if x == e { r := h } else { r := call mk_proj(nm, ix, x); if r >= 4294967296 { abort } };
  (fd, j, e0) := call ilp_find(h, 0);
  u := call ilp_put(h, 0, r, fd, j);
  return r
}

/-! ## The entries -/

/-- con-ron: none — the substitution's keys checked to be stored names (the twin reads them back,
`readNamesM`, and fails on a handle that does not view; `keys_ok` aborts there instead) -/
def keysOk : FunDecl := lfn (o, l) locals (w, g, t, i, r, c) {
  if l == 0 { return 0 };
  w := SPN.u64[o];
  if w >= 4294967296 { abort };
  g := w >> 28;
  t := ⟦w⟧.tier;
  i := ⟦w⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if g >= 3 { abort };
  c := NANON⟨t⟩.count;
  if g == 1 { c := NSTR⟨t⟩.count };
  if g == 2 { c := NNUM⟨t⟩.count };
  if c <= i { abort };
  r := call keys_ok(o + 1, l - 1);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:2251-2268 ConRon.Arena.instLPFast -/
@[l_impl ConRon.Arena.instLPFast]
def instLPCore : FunDecl := lfn (ko, kc, us, e) locals (vo, vc, r, u) {
  (vo, vc, r) := call der_b(e);
  if r == 0 { return e & 4294967295 };
  (vo, vc) := call ls_node(us);
  u := call keys_ok(ko, kc);
  u := call ilp_clear();
  u := call ilpl_clear();
  u := call ilpls_clear();
  r := call lp_go(e, ko, kc, vo, vc, 4000000000);
  u := call ilp_clear();
  u := call ilpl_clear();
  u := call ilpls_clear();
  return r & 4294967295
}

/-- `inst_lp(po, pl, us, e)`: the keys an `EREC` name slice (lane `whnf`'s convention). -/
-- con-ron: ConRon/Arena/ExprOps.lean:2251-2268 ConRon.Arena.instLPFast
def instLPL : FunDecl := lfn (po, pl, us, e) locals (b, r) {
  b := call keys_push(po, pl);
  r := call inst_lp_core(b, pl, us, e);
  CTL.u64[136] := b;
  return r
}

/-- `inst_lp_fast(f, lo, ll, us, e)`: lane `induct`'s convention (the keys an `IW` slice, the
fuel explicit: anything but `coreWalkFuel` aborts, as `WhnfEntry.lean`'s `_f` adapters). -/
-- con-ron: ConRon/Arena/ExprOps.lean:2251-2268 ConRon.Arena.instLPFast
def instLPFastL : FunDecl := lfn (f, lo, ll, us, e) locals (b, r) {
  if f != 4000000000 { abort };
  b := call keys_push_iw(lo, ll);
  r := call inst_lp_core(b, ll, us, e);
  CTL.u64[136] := b;
  return r
}

/-- con-ron: ConRon/Arena/Core.lean:1976-1994 ConRon.Arena.recFireLevels -/
@[l_impl ConRon.Arena.recFireLevels]
def recFireLevelsL : FunDecl := lfn (fireKind, fvo, fvc, po, pc, us, qo, qc) locals (vo, vc, b, c, x, r) {
  (vo, vc) := call ls_node(us);
  b := call keys_push(po, pc);
  c := CTL.u64[136];
  if fireKind != 0 {
    if len(SPN.u64) < c { abort };
    if len(SPN.u64) - c < fvc { abort };
    x := call sle_go(fvo, fvc, c, b, pc, vo, vc);
    r := call spn_ls(c, fvc)
  } else {
    if len(SPN.u64) < c { abort };
    if len(SPN.u64) - c < qc { abort };
    x := call slp_go(qo, qc, c, b, pc, vo, vc);
    r := call spn_ls(c, qc)
  };
  CTL.u64[136] := b;
  return r
}

/-! ## The program -/

end L.Arena
