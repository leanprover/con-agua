import ConAgua.Arena.IndIface
import ConAgua.Census.Attr
import ConRon.Arena.Promote

/-!
# Promotion in L: the scratch → persistent copy (`Arena/Promote.lean` of the twin)

The twin's `promoteN`/`promoteL`/`promoteLs`/`promoteE` (a memoised structural copy of a handle
into the persistent tier), their lifts to lists and to the environment's records
(`promoteCV` … `promoteCI`, `promoteVG`), and `promoteNew` (the step's newly installed
constants, copied and re-indexed).

* **The memos.** The twin's `PMemo` (four `HashMap`s, handle → handle, per declaration) is four
  memos of the library (`MemoLib`): `pnSch` (names, array 146, `CTL[140]`), `plSch` (levels,
  147, `CTL[142]`), `plsSch` (level lists, 148, `CTL[144]`), `peSch` (expressions, 149,
  `CTL[146]`); keys are one handle word (second key word `0`), values handle words. Where the
  twin starts from `PMemo.empty` (`promote_vg`, `promote_new` with `fresh ≠ 0`) the four are
  cleared (an epoch bump).
* **The fuel** is the twin's: a word argument `f`, `CWF` (`coreWalkFuel`) at the entries,
  decremented where the twin decrements it (`promoteN`/`promoteL`/`promoteE`; `promoteLs` and the
  lists pass it on unchanged). Fuel `0` aborts (the twin fails).
* **Interning into the persistent tier** (`internPersistentE/N/L/Ls`): `pi_*` saves the scratch
  flag `CTL[1]`, clears it, calls the ordinary interner (`intern_*`, `mk_*`), and restores it.
  With the flag clear an interner probes and appends to tier 0 only, which is exactly
  `internPersistent` (the `else` branch of the twin's `intern`); see `PromoteTwin.lean` for the
  twin-side equation and DESIGN.md for the decision.
* **Lists.** A level list's promoted handles are written above the pool top, then the top is
  raised over them and `intern_ls` interns the slice. The handle lists of an environment record
  (`EREC` slices) are promoted into a fresh `EREC` slice (`erec_alloc`), element by element in
  the twin's order (the order fixes the persistent handles' numbers).
* **Records.** A promoted constant / value group is a fresh `EREC` record (`erec_alloc`), in
  `decCI`'s / `decVG`'s layout (`EnvRec.lean`).
-/

open ConRon.Arena

namespace L.Arena

open L.Ind (CWF)

/-! ## The four memos -/

abbrev PNM : ArrId := 146
abbrev PLM : ArrId := 147
abbrev PLSM : ArrId := 148
abbrev PEM : ArrId := 149

abbrev pnSch : MemoSch := ⟨PNM, 140⟩
abbrev plSch : MemoSch := ⟨PLM, 142⟩
abbrev plsSch : MemoSch := ⟨PLSM, 144⟩
abbrev peSch : MemoSch := ⟨PEM, 146⟩

/-! ## Interning into the persistent tier: the flag bracket -/

/-- `pi_bvar(i)`: `internPersistentE (.bvar i)`. -/
-- con-ron: ConRon/Arena/Monad.lean:627-645 ConRon.Arena.internPersistentE
def piBVar : FunDecl := lfn (i) locals (sc, r) {
  sc := CTL.u64[1]; CTL.u64[1] := 0; r := call intern_bvar(i); CTL.u64[1] := sc; return r
}
/-- `pi_fvar(i, ty)`. -/
-- con-ron: ConRon/Arena/Monad.lean:627-645 ConRon.Arena.internPersistentE
def piFVar : FunDecl := lfn (i, ty) locals (sc, r) {
  sc := CTL.u64[1]; CTL.u64[1] := 0; r := call intern_fvar(i, ty); CTL.u64[1] := sc; return r
}
/-- `pi_sort(u)`. -/
-- con-ron: ConRon/Arena/Monad.lean:627-645 ConRon.Arena.internPersistentE
def piSort : FunDecl := lfn (u) locals (sc, r) {
  sc := CTL.u64[1]; CTL.u64[1] := 0; r := call intern_sort(u); CTL.u64[1] := sc; return r
}
/-- `pi_const(n, us)`. -/
-- con-ron: ConRon/Arena/Monad.lean:627-645 ConRon.Arena.internPersistentE
def piConst : FunDecl := lfn (n, us) locals (sc, r) {
  sc := CTL.u64[1]; CTL.u64[1] := 0; r := call intern_const(n, us); CTL.u64[1] := sc; return r
}
/-- `pi_app(f, a)`. -/
-- con-ron: ConRon/Arena/Monad.lean:627-645 ConRon.Arena.internPersistentE
def piApp : FunDecl := lfn (f, a) locals (sc, r) {
  sc := CTL.u64[1]; CTL.u64[1] := 0; r := call mk_app(f, a); CTL.u64[1] := sc; return r
}
/-- `pi_lam(t, b)`. -/
-- con-ron: ConRon/Arena/Monad.lean:627-645 ConRon.Arena.internPersistentE
def piLam : FunDecl := lfn (t, b) locals (sc, r) {
  sc := CTL.u64[1]; CTL.u64[1] := 0; r := call mk_lam(t, b); CTL.u64[1] := sc; return r
}
/-- `pi_forall(t, b)`. -/
-- con-ron: ConRon/Arena/Monad.lean:627-645 ConRon.Arena.internPersistentE
def piForall : FunDecl := lfn (t, b) locals (sc, r) {
  sc := CTL.u64[1]; CTL.u64[1] := 0; r := call mk_forall(t, b); CTL.u64[1] := sc; return r
}
/-- `pi_let(t, v, b)`. -/
-- con-ron: ConRon/Arena/Monad.lean:627-645 ConRon.Arena.internPersistentE
def piLet : FunDecl := lfn (t, v, b) locals (sc, r) {
  sc := CTL.u64[1]; CTL.u64[1] := 0; r := call mk_let(t, v, b); CTL.u64[1] := sc; return r
}
/-- `pi_lit(o, l)` (a `natVal`). -/
-- con-ron: ConRon/Arena/Monad.lean:627-645 ConRon.Arena.internPersistentE
def piLit : FunDecl := lfn (o, l) locals (sc, r) {
  sc := CTL.u64[1]; CTL.u64[1] := 0; r := call intern_lit(o, l); CTL.u64[1] := sc; return r
}
/-- `pi_lit_str(o, l)` (a `strVal`). -/
-- con-ron: ConRon/Arena/Monad.lean:627-645 ConRon.Arena.internPersistentE
def piLitStr : FunDecl := lfn (o, l) locals (sc, r) {
  sc := CTL.u64[1]; CTL.u64[1] := 0; r := call intern_lit_str(o, l); CTL.u64[1] := sc; return r
}
/-- `pi_proj(n, i, e)`. -/
-- con-ron: ConRon/Arena/Monad.lean:627-645 ConRon.Arena.internPersistentE
def piProj : FunDecl := lfn (n, i, e) locals (sc, r) {
  sc := CTL.u64[1]; CTL.u64[1] := 0; r := call mk_proj(n, i, e); CTL.u64[1] := sc; return r
}
/-- `pi_nanon()`: `internPersistentN .anonymous`. -/
-- con-ron: ConRon/Arena/Monad.lean:647-661 ConRon.Arena.internPersistentN
def piNAnon : FunDecl := lfn () locals (sc, r) {
  sc := CTL.u64[1]; CTL.u64[1] := 0; r := call intern_nanon(); CTL.u64[1] := sc; return r
}
/-- `pi_nstr(q, o, l)`. -/
-- con-ron: ConRon/Arena/Monad.lean:647-661 ConRon.Arena.internPersistentN
def piNStr : FunDecl := lfn (q, o, l) locals (sc, r) {
  sc := CTL.u64[1]; CTL.u64[1] := 0; r := call intern_nstr(q, o, l); CTL.u64[1] := sc; return r
}
/-- `pi_nnum(q, u)`. -/
-- con-ron: ConRon/Arena/Monad.lean:647-661 ConRon.Arena.internPersistentN
def piNNum : FunDecl := lfn (q, u) locals (sc, r) {
  sc := CTL.u64[1]; CTL.u64[1] := 0; r := call intern_nnum(q, u); CTL.u64[1] := sc; return r
}
/-- `pi_zero()`: `internPersistentL .zero`. -/
-- con-ron: ConRon/Arena/Monad.lean:663-677 ConRon.Arena.internPersistentL
def piZero : FunDecl := lfn () locals (sc, r) {
  sc := CTL.u64[1]; CTL.u64[1] := 0; r := call intern_zero(); CTL.u64[1] := sc; return r
}
/-- `pi_succ(u)`. -/
-- con-ron: ConRon/Arena/Monad.lean:663-677 ConRon.Arena.internPersistentL
def piSucc : FunDecl := lfn (u) locals (sc, r) {
  sc := CTL.u64[1]; CTL.u64[1] := 0; r := call intern_succ(u); CTL.u64[1] := sc; return r
}
/-- `pi_max(u, v)`. -/
-- con-ron: ConRon/Arena/Monad.lean:663-677 ConRon.Arena.internPersistentL
def piMax : FunDecl := lfn (u, v) locals (sc, r) {
  sc := CTL.u64[1]; CTL.u64[1] := 0; r := call intern_max(u, v); CTL.u64[1] := sc; return r
}
/-- `pi_imax(u, v)`. -/
-- con-ron: ConRon/Arena/Monad.lean:663-677 ConRon.Arena.internPersistentL
def piImax : FunDecl := lfn (u, v) locals (sc, r) {
  sc := CTL.u64[1]; CTL.u64[1] := 0; r := call intern_imax(u, v); CTL.u64[1] := sc; return r
}
/-- `pi_param(n)`. -/
-- con-ron: ConRon/Arena/Monad.lean:663-677 ConRon.Arena.internPersistentL
def piParam : FunDecl := lfn (n) locals (sc, r) {
  sc := CTL.u64[1]; CTL.u64[1] := 0; r := call intern_param(n); CTL.u64[1] := sc; return r
}
/-- `pi_ls(o, l)`: `internPersistentLs` of the pool slice. -/
-- con-ron: ConRon/Arena/Monad.lean:679-693 ConRon.Arena.internPersistentLs
def piLs : FunDecl := lfn (o, l) locals (sc, r) {
  sc := CTL.u64[1]; CTL.u64[1] := 0; r := call intern_ls(o, l); CTL.u64[1] := sc; return r
}

/-! ## Names -/

/-- `pn_arm(f, h)`: view the scratch name `h`, promote its prefix at fuel `f`, intern the node
persistently (`promoteN`'s three view arms). -/
-- con-ron: ConRon/Arena/Promote.lean:80-101 ConRon.Arena.promoteN
@[l_impl ConRon.Arena.promoteN]
def pnArm : FunDecl := lfn (f, h) locals (g, t, i, k, q, o, l, r) {
  g := h >> 28;
  t := (h >> 27) & 1;
  i := h & 134217727;
  if 4294967295 < h { abort };
  if t != 0 && CTL.u64[1] == 0 { abort };
  if g == 0 {
    if CTL.u64[34 + t] <= i { abort };
    r := call pi_nanon();
    return r
  };
  if g == 1 {
    if CTL.u64[36 + t] <= i { abort };
    k := i * 8 + t * 4;
    q := NSREC.u64[k];
    o := NSREC.u64[k + 1];
    l := NSREC.u64[k + 2];
    q := call promote_n(f, q);
    r := call pi_nstr(q, o, l);
    return r
  };
  if g == 2 {
    if CTL.u64[38 + t] <= i { abort };
    k := i * 4 + t * 2;
    q := NNREC.u64[k];
    o := NNREC.u64[k + 1];
    q := call promote_n(f, q);
    r := call pi_nnum(q, o);
    return r
  };
  abort
}

/-- `promote_n(f, h)`: `promoteN` at fuel `f`. -/
-- con-ron: ConRon/Arena/Promote.lean:80-101 ConRon.Arena.promoteN
@[l_impl ConRon.Arena.promoteN]
def promoteNL : FunDecl := lfn (f, h) locals (fd, j, d, r, u) {
  if f == 0 { abort };
  if (h >> 27) & 1 == 0 { return h };
  (fd, j, d) := call pn_find(h, 0);
  if fd != 0 { return PNM.u64[j * 4 + 3] };
  r := call pn_arm(f - 1, h);
  (fd, j, d) := call pn_find(h, 0);
  u := call pn_put(h, 0, r, fd, j);
  return r
}

/-! ## Levels and level lists -/

/-- `pl_arm(f, h)`: view the scratch level `h`, promote its children at fuel `f`, intern the
node persistently (`promoteL`'s five view arms). -/
-- con-ron: ConRon/Arena/Promote.lean:103-129 ConRon.Arena.promoteL
@[l_impl ConRon.Arena.promoteL]
def plArm : FunDecl := lfn (f, h) locals (g, a, b, x, y, r) {
  if 4294967295 < h { abort };
  (g, a, b) := call lv_node(h);
  if g == 0 { r := call pi_zero(); return r };
  if g == 1 { x := call promote_l(f, a); r := call pi_succ(x); return r };
  if g == 2 {
    x := call promote_l(f, a); y := call promote_l(f, b); r := call pi_max(x, y); return r
  };
  if g == 3 {
    x := call promote_l(f, a); y := call promote_l(f, b); r := call pi_imax(x, y); return r
  };
  if g == 4 { x := call promote_n(f, a); r := call pi_param(x); return r };
  abort
}

/-- `promote_l(f, h)`: `promoteL` at fuel `f`. -/
-- con-ron: ConRon/Arena/Promote.lean:103-129 ConRon.Arena.promoteL
@[l_impl ConRon.Arena.promoteL]
def promoteLL : FunDecl := lfn (f, h) locals (fd, j, d, r, u) {
  if f == 0 { abort };
  if (h >> 27) & 1 == 0 { return h };
  (fd, j, d) := call pl_find(h, 0);
  if fd != 0 { return PLM.u64[j * 4 + 3] };
  r := call pl_arm(f - 1, h);
  (fd, j, d) := call pl_find(h, 0);
  u := call pl_put(h, 0, r, fd, j);
  return r
}

/-- `promote_l_pool(f, o, l, q)`: `POOL[q + j] := promote_l(f, POOL[o + j])` for `j < l`, in
order (`promoteLList` over a pool slice, the results above the pool top `q`). -/
-- con-ron: ConRon/Arena/Promote.lean:131-138 ConRon.Arena.promoteLList
@[l_impl ConRon.Arena.promoteLList]
def promoteLPool : FunDecl := lfn (f, o, l, q) locals (r, u) {
  if l == 0 { return 0 };
  r := call promote_l(f, POOL.u64[o]);
  POOL.u64[q] := r;
  u := call promote_l_pool(f, o + 1, l - 1, q + 1);
  return 0
}

/-- `pls_arm(f, h)`: the scratch level list `h` (a pool slice), promoted above the pool top,
the top raised over it, interned persistently. -/
-- con-ron: ConRon/Arena/Promote.lean:140-150 ConRon.Arena.promoteLs
@[l_impl ConRon.Arena.promoteLs]
def plsArm : FunDecl := lfn (f, h) locals (o, l, q, u, r) {
  if 4294967295 < h { abort };
  (o, l) := call ls_node(h);
  q := CTL.u64[0];
  if len(POOL.u64) < q { abort };
  if len(POOL.u64) - q < l { abort };
  u := call promote_l_pool(f, o, l, q);
  CTL.u64[0] := q + l;
  r := call pi_ls(q, l);
  return r
}

/-- `promote_ls(f, h)`: `promoteLs` at fuel `f` (not decremented). -/
-- con-ron: ConRon/Arena/Promote.lean:140-150 ConRon.Arena.promoteLs
@[l_impl ConRon.Arena.promoteLs]
def promoteLsL : FunDecl := lfn (f, h) locals (fd, j, d, r, u) {
  if (h >> 27) & 1 == 0 { return h };
  (fd, j, d) := call pls_find(h, 0);
  if fd != 0 { return PLSM.u64[j * 4 + 3] };
  r := call pls_arm(f, h);
  (fd, j, d) := call pls_find(h, 0);
  u := call pls_put(h, 0, r, fd, j);
  return r
}

/-! ## Expressions -/

/-- `pe_lit(h)`: the scratch literal `h` (its pool slice and kind) interned persistently. -/
-- con-ron: ConRon/Arena/Promote.lean:152-199 ConRon.Arena.promoteE
@[l_impl ConRon.Arena.promoteE]
def peLit : FunDecl := lfn (h) locals (t, i, k, r) {
  t := (h >> 27) & 1;
  i := h & 134217727;
  k := i * 8 + t * 4;
  if REC.u64[k] == 1 { r := call pi_lit_str(REC.u64[k + 1], REC.u64[k + 2]); return r };
  r := call pi_lit(REC.u64[k + 1], REC.u64[k + 2]);
  return r
}

/-- `pe_const(f, n, us)`. -/
-- con-ron: ConRon/Arena/Promote.lean:152-199 ConRon.Arena.promoteE
@[l_impl ConRon.Arena.promoteE]
def peConst : FunDecl := lfn (f, n, us) locals (x, y, r) {
  x := call promote_n(f, n); y := call promote_ls(f, us); r := call pi_const(x, y); return r
}

/-- `pe_app(f, a, b)`. -/
-- con-ron: ConRon/Arena/Promote.lean:152-199 ConRon.Arena.promoteE
@[l_impl ConRon.Arena.promoteE]
def peApp : FunDecl := lfn (f, a, b) locals (x, y, r) {
  x := call promote_e(f, a); y := call promote_e(f, b); r := call pi_app(x, y); return r
}

/-- `pe_lam(f, a, b)`. -/
-- con-ron: ConRon/Arena/Promote.lean:152-199 ConRon.Arena.promoteE
@[l_impl ConRon.Arena.promoteE]
def peLam : FunDecl := lfn (f, a, b) locals (x, y, r) {
  x := call promote_e(f, a); y := call promote_e(f, b); r := call pi_lam(x, y); return r
}

/-- `pe_forall(f, a, b)`. -/
-- con-ron: ConRon/Arena/Promote.lean:152-199 ConRon.Arena.promoteE
@[l_impl ConRon.Arena.promoteE]
def peForall : FunDecl := lfn (f, a, b) locals (x, y, r) {
  x := call promote_e(f, a); y := call promote_e(f, b); r := call pi_forall(x, y); return r
}

/-- `pe_let(f, a, b, c)`. -/
-- con-ron: ConRon/Arena/Promote.lean:152-199 ConRon.Arena.promoteE
@[l_impl ConRon.Arena.promoteE]
def peLet : FunDecl := lfn (f, a, b, c) locals (x, y, z, r) {
  x := call promote_e(f, a); y := call promote_e(f, b); z := call promote_e(f, c);
  r := call pi_let(x, y, z); return r
}

/-- `pe_proj(f, n, i, e)`. -/
-- con-ron: ConRon/Arena/Promote.lean:152-199 ConRon.Arena.promoteE
@[l_impl ConRon.Arena.promoteE]
def peProj : FunDecl := lfn (f, n, i, e) locals (x, y, r) {
  x := call promote_n(f, n); y := call promote_e(f, e); r := call pi_proj(x, i, y); return r
}

/-- `pe_arm(f, h)`: view the scratch expression `h` (`e_view`), promote its children at fuel
`f`, intern the node persistently (`promoteE`'s ten view arms). -/
-- con-ron: ConRon/Arena/Promote.lean:152-199 ConRon.Arena.promoteE
@[l_impl ConRon.Arena.promoteE]
def peArm : FunDecl := lfn (f, h) locals (g, a, b, c, r) {
  (g, a, b, c) := call e_view(h);
  if g == 0 { r := call pi_bvar(a); return r };
  if g == 1 { r := call promote_e(f, b); r := call pi_fvar(a, r); return r };
  if g == 2 { r := call promote_l(f, a); r := call pi_sort(r); return r };
  if g == 3 { r := call pe_const(f, a, b); return r };
  if g == 4 { r := call pe_app(f, a, b); return r };
  if g == 5 { r := call pe_lam(f, a, b); return r };
  if g == 6 { r := call pe_forall(f, a, b); return r };
  if g == 7 { r := call pe_let(f, a, b, c); return r };
  if g == 8 { r := call pe_lit(h); return r };
  r := call pe_proj(f, a, b, c);
  return r
}

/-- `promote_e(f, h)`: `promoteE` at fuel `f`. -/
-- con-ron: ConRon/Arena/Promote.lean:152-199 ConRon.Arena.promoteE
@[l_impl ConRon.Arena.promoteE]
def promoteEL : FunDecl := lfn (f, h) locals (fd, j, d, r, u) {
  if f == 0 { abort };
  if (h >> 27) & 1 == 0 { return h };
  (fd, j, d) := call pe_find(h, 0);
  if fd != 0 { return PEM.u64[j * 4 + 3] };
  r := call pe_arm(f - 1, h);
  (fd, j, d) := call pe_find(h, 0);
  u := call pe_put(h, 0, r, fd, j);
  return r
}

/-! ## Handle lists in `EREC` -/

/-- `promote_n_list(f, o, l, q)`: `EREC[q + j] := promote_n(f, EREC[o + j])`, in order. -/
-- con-ron: ConRon/Arena/Promote.lean:203-209 ConRon.Arena.promoteNList
@[l_impl ConRon.Arena.promoteNList]
def promoteNListL : FunDecl := lfn (f, o, l, q) locals (r, u) {
  if l == 0 { return 0 };
  r := call promote_n(f, EREC.u64[o]);
  EREC.u64[q] := r;
  u := call promote_n_list(f, o + 1, l - 1, q + 1);
  return 0
}

/-- `promote_l_list(f, o, l, q)`: the same for level handles (`promoteLList`). -/
-- con-ron: ConRon/Arena/Promote.lean:131-138 ConRon.Arena.promoteLList
@[l_impl ConRon.Arena.promoteLList]
def promoteLListL : FunDecl := lfn (f, o, l, q) locals (r, u) {
  if l == 0 { return 0 };
  r := call promote_l(f, EREC.u64[o]);
  EREC.u64[q] := r;
  u := call promote_l_list(f, o + 1, l - 1, q + 1);
  return 0
}

/-- `promote_e_list(f, o, l, q)`: the same for expression handles (`promoteEList`). -/
-- con-ron: ConRon/Arena/Promote.lean:211-218 ConRon.Arena.promoteEList
@[l_impl ConRon.Arena.promoteEList]
def promoteEListL : FunDecl := lfn (f, o, l, q) locals (r, u) {
  if l == 0 { return 0 };
  r := call promote_e(f, EREC.u64[o]);
  EREC.u64[q] := r;
  u := call promote_e_list(f, o + 1, l - 1, q + 1);
  return 0
}

/-- `promote_slice(k, f, o, l)`: a fresh `EREC` slice of the promoted handles of the slice
`(o, l)`; `k` the kind (`0` names, `1` levels, `2` expressions). Returns its offset. -/
-- con-ron: none — allocates the `EREC` slice the twin's list functions return as a value
def promoteSlice : FunDecl := lfn (k, f, o, l) locals (q, u) {
  q := call erec_alloc(l);
  if k == 0 { u := call promote_n_list(f, o, l, q); return q };
  if k == 1 { u := call promote_l_list(f, o, l, q); return q };
  u := call promote_e_list(f, o, l, q);
  return q
}

/-! ## Records -/

/-- `promote_cv(f, s, d)`: the constant value at `EREC[s‥s+4)` promoted into `EREC[d‥d+4)`
(name, level parameters, type, in that order). -/
-- con-ron: ConRon/Arena/Promote.lean:229-235 ConRon.Arena.promoteCV
@[l_impl ConRon.Arena.promoteCV]
def promoteCVL : FunDecl := lfn (f, s, d) locals (n, l, q, t) {
  n := call promote_n(f, EREC.u64[s]);
  l := EREC.u64[s + 2];
  q := call promote_slice(0, f, EREC.u64[s + 1], l);
  t := call promote_e(f, EREC.u64[s + 3]);
  EREC.u64[d] := n;
  EREC.u64[d + 1] := q;
  EREC.u64[d + 2] := l;
  EREC.u64[d + 3] := t;
  return 0
}

/-- `promote_fire(f, s, d)`: a rule's firing mode (words `3‥8` of the 11-word rule records at
`s` and `d`). -/
-- con-ron: ConRon/Arena/Promote.lean:237-244 ConRon.Arena.promoteFire
@[l_impl ConRon.Arena.promoteFire]
def promoteFireL : FunDecl := lfn (f, s, d) locals (q, r) {
  if EREC.u64[s + 3] != 1 {
    EREC.u64[d + 3] := EREC.u64[s + 3];
    EREC.u64[d + 4] := 0; EREC.u64[d + 5] := 0; EREC.u64[d + 6] := 0; EREC.u64[d + 7] := 0;
    return 0
  };
  q := call promote_slice(1, f, EREC.u64[s + 4], EREC.u64[s + 5]);
  r := call promote_slice(2, f, EREC.u64[s + 6], EREC.u64[s + 7]);
  EREC.u64[d + 3] := 1;
  EREC.u64[d + 4] := q; EREC.u64[d + 5] := EREC.u64[s + 5];
  EREC.u64[d + 6] := r; EREC.u64[d + 7] := EREC.u64[s + 7];
  return 0
}

/-- `promote_rule(f, s, d)`: the 11-word rule record at `s` promoted into `d` (constructor,
firing mode, right-hand side). -/
-- con-ron: ConRon/Arena/Promote.lean:246-252 ConRon.Arena.promoteRule
@[l_impl ConRon.Arena.promoteRule]
def promoteRuleL : FunDecl := lfn (f, s, d) locals (c, u, r) {
  c := call promote_n(f, EREC.u64[s]);
  u := call promote_fire(f, s, d);
  r := call promote_e(f, EREC.u64[s + 8]);
  EREC.u64[d] := c;
  EREC.u64[d + 1] := EREC.u64[s + 1];
  EREC.u64[d + 2] := EREC.u64[s + 2];
  EREC.u64[d + 8] := r;
  EREC.u64[d + 9] := EREC.u64[s + 9];
  EREC.u64[d + 10] := EREC.u64[s + 10];
  return 0
}

/-- `promote_rules(f, s, l, d)`: `l` rule records from `s` promoted into `d`, in order. -/
-- con-ron: ConRon/Arena/Promote.lean:254-261 ConRon.Arena.promoteRules
@[l_impl ConRon.Arena.promoteRules]
def promoteRulesL : FunDecl := lfn (f, s, l, d) locals (u) {
  if l == 0 { return 0 };
  u := call promote_rule(f, s, d);
  u := call promote_rules(f, s + 11, l - 1, d + 11);
  return 0
}

/-- `promote_caps(f, s, d)`: the 15-word capabilities record at `s` promoted into `d`
(`etaCtor`, `all`, `ctors`, in that order). `sortZ` is copied as the twin copies it: the twin's
`PropWhen` holds `ConLeche.Name` values, L's holds name handles read back by the fixed decoder
`dn`, so the copy decodes to the same value. -/
-- con-ron: ConRon/Arena/Promote.lean:263-271 ConRon.Arena.promoteCaps
@[l_impl ConRon.Arena.promoteCaps]
def promoteCapsL : FunDecl := lfn (f, s, d) locals (c, a, k) {
  c := call promote_n(f, EREC.u64[s + 1]);
  a := call promote_slice(0, f, EREC.u64[s + 10], EREC.u64[s + 11]);
  k := call promote_slice(0, f, EREC.u64[s + 13], EREC.u64[s + 14]);
  EREC.u64[d] := EREC.u64[s];
  EREC.u64[d + 1] := c;
  EREC.u64[d + 2] := EREC.u64[s + 2];
  EREC.u64[d + 3] := EREC.u64[s + 3];
  EREC.u64[d + 4] := EREC.u64[s + 4];
  EREC.u64[d + 5] := EREC.u64[s + 5];
  EREC.u64[d + 6] := EREC.u64[s + 6];
  EREC.u64[d + 7] := EREC.u64[s + 7];
  EREC.u64[d + 8] := EREC.u64[s + 8];
  EREC.u64[d + 9] := EREC.u64[s + 9];
  EREC.u64[d + 10] := a;
  EREC.u64[d + 11] := EREC.u64[s + 11];
  EREC.u64[d + 12] := EREC.u64[s + 12];
  EREC.u64[d + 13] := k;
  EREC.u64[d + 14] := EREC.u64[s + 14];
  return 0
}

/-- `promote_proj_table(f, p)`: the projection-table record at `p` (kind `6`, 14 words)
promoted into a fresh record, returned (`structName`, `tableName`, level parameters, `ctor`,
`structSort`, bodies, guards, in the twin's order). -/
-- con-ron: ConRon/Arena/Promote.lean:273-285 ConRon.Arena.promoteProjTable
@[l_impl ConRon.Arena.promoteProjTable]
def promoteProjTableL : FunDecl := lfn (f, p) locals (d, sn, tn, lp, c, ss, bs, gs) {
  d := call erec_alloc(14);
  sn := call promote_n(f, EREC.u64[p + 2]);
  tn := call promote_n(f, EREC.u64[p + 1]);
  lp := call promote_slice(0, f, EREC.u64[p + 3], EREC.u64[p + 4]);
  c := call promote_n(f, EREC.u64[p + 6]);
  ss := call promote_l(f, EREC.u64[p + 8]);
  bs := call promote_slice(2, f, EREC.u64[p + 9], EREC.u64[p + 10]);
  gs := call promote_slice(1, f, EREC.u64[p + 11], EREC.u64[p + 12]);
  EREC.u64[d] := 6;
  EREC.u64[d + 1] := tn;
  EREC.u64[d + 2] := sn;
  EREC.u64[d + 3] := lp;
  EREC.u64[d + 4] := EREC.u64[p + 4];
  EREC.u64[d + 5] := EREC.u64[p + 5];
  EREC.u64[d + 6] := c;
  EREC.u64[d + 7] := EREC.u64[p + 7];
  EREC.u64[d + 8] := ss;
  EREC.u64[d + 9] := bs;
  EREC.u64[d + 10] := EREC.u64[p + 10];
  EREC.u64[d + 11] := gs;
  EREC.u64[d + 12] := EREC.u64[p + 12];
  EREC.u64[d + 13] := EREC.u64[p + 13];
  return d
}

/-- `pci_cv(f, p, n)`: a fresh `n`-word record with `p`'s kind and `p`'s constant value
promoted (the arms `axiomInfo`, `thmInfo`, and the head of the others). -/
-- con-ron: ConRon/Arena/Promote.lean:287-315 ConRon.Arena.promoteCI
@[l_impl ConRon.Arena.promoteCI]
def pciCv : FunDecl := lfn (f, p, n) locals (d, u) {
  d := call erec_alloc(n);
  EREC.u64[d] := EREC.u64[p];
  u := call promote_cv(f, p + 1, d + 1);
  return d
}

/-- `pci_defn(f, p)`: `defnInfo cv value hint`. -/
-- con-ron: ConRon/Arena/Promote.lean:287-315 ConRon.Arena.promoteCI
@[l_impl ConRon.Arena.promoteCI]
def pciDefn : FunDecl := lfn (f, p) locals (d, x) {
  d := call pci_cv(f, p, 8);
  x := call promote_e(f, EREC.u64[p + 5]);
  EREC.u64[d + 5] := x;
  EREC.u64[d + 6] := EREC.u64[p + 6];
  EREC.u64[d + 7] := EREC.u64[p + 7];
  return d
}

/-- `pci_ind(f, p)`: `indInfo cv caps`. -/
-- con-ron: ConRon/Arena/Promote.lean:287-315 ConRon.Arena.promoteCI
@[l_impl ConRon.Arena.promoteCI]
def pciInd : FunDecl := lfn (f, p) locals (d, u) {
  d := call pci_cv(f, p, 20);
  u := call promote_caps(f, p + 5, d + 5);
  return d
}

/-- `pci_ctor(f, p)`: `ctorInfo cv nP nF`. -/
-- con-ron: ConRon/Arena/Promote.lean:287-315 ConRon.Arena.promoteCI
@[l_impl ConRon.Arena.promoteCI]
def pciCtor : FunDecl := lfn (f, p) locals (d) {
  d := call pci_cv(f, p, 7);
  EREC.u64[d + 5] := EREC.u64[p + 5];
  EREC.u64[d + 6] := EREC.u64[p + 6];
  return d
}

/-- `pci_rec(f, p)`: `recInfo cv major pre rules`. -/
-- con-ron: ConRon/Arena/Promote.lean:287-315 ConRon.Arena.promoteCI
@[l_impl ConRon.Arena.promoteCI]
def pciRec : FunDecl := lfn (f, p) locals (d, l, q, u) {
  d := call pci_cv(f, p, 9);
  l := EREC.u64[p + 8];
  if 1152921504606846976 <= l { abort };
  q := call erec_alloc(11 * l);
  u := call promote_rules(f, EREC.u64[p + 7], l, q);
  EREC.u64[d + 5] := EREC.u64[p + 5];
  EREC.u64[d + 6] := EREC.u64[p + 6];
  EREC.u64[d + 7] := q;
  EREC.u64[d + 8] := l;
  return d
}

/-- `promote_ci(f, p)`: the constant record at `p` promoted into a fresh record, returned
(`promoteCI`'s seven arms). -/
-- con-ron: ConRon/Arena/Promote.lean:287-315 ConRon.Arena.promoteCI
@[l_impl ConRon.Arena.promoteCI]
def promoteCIL : FunDecl := lfn (f, p) locals (k, d) {
  k := EREC.u64[p];
  if k == 0 || k == 2 { d := call pci_cv(f, p, 5); return d };
  if k == 1 { d := call pci_defn(f, p); return d };
  if k == 3 { d := call pci_ind(f, p); return d };
  if k == 4 { d := call pci_ctor(f, p); return d };
  if k == 5 { d := call pci_rec(f, p); return d };
  if k == 6 { d := call promote_proj_table(f, p); return d };
  abort
}

/-- `promote_ci_list(f, j, k)`: the constants at `ECON` positions `j, j - 1, …, j - k + 1`
(newest first, as `IEnv.consts`) promoted, each position overwritten with its new record. -/
-- con-ron: ConRon/Arena/Promote.lean:317-325 ConRon.Arena.promoteCIList
@[l_impl ConRon.Arena.promoteCIList]
def promoteCIListL : FunDecl := lfn (f, j, k) locals (d, u) {
  if k == 0 { return 0 };
  d := call promote_ci(f, ECON.u64[j]);
  ECON.u64[j] := d;
  u := call promote_ci_list(f, j - 1, k - 1);
  return 0
}

/-! ## The entries -/

/-- `promote_clear()`: the four memos emptied (`PMemo.empty`). -/
-- con-ron: ConRon/Arena/Promote.lean:72-74 ConRon.Arena.PMemo.empty
def promoteClear : FunDecl := lfn () locals (u) {
  u := call pn_clear(); u := call pl_clear(); u := call pls_clear(); u := call pe_clear();
  return 0
}

/-- `promote_vg(g, vis)`: `promoteVG PMemo.empty coreWalkFuel` on the value group record `g`;
returns the promoted record. -/
-- con-ron: ConRon/Arena/Promote.lean:327-335 ConRon.Arena.promoteVG
@[l_impl ConRon.Arena.promoteVG]
def promoteVGL : FunDecl := lfn (g, vis) locals (d, u, x) {
  u := call promote_clear();
  d := call erec_alloc(6);
  EREC.u64[d] := EREC.u64[g];
  u := call promote_cv(⟪CWF⟫, g + 1, d + 1);
  x := call promote_e(⟪CWF⟫, EREC.u64[g + 5]);
  EREC.u64[d + 5] := x;
  return d
}

/-- `erase_installed(j, k)`: the index rows of the constants at `ECON` positions `j, …,
j - k + 1` erased (`eraseInstalled`, newest first). -/
-- con-ron: ConRon/Arena/Promote.lean:339-348 ConRon.Arena.eraseInstalled
@[l_impl ConRon.Arena.eraseInstalled]
def eraseInstalledL : FunDecl := lfn (j, k) locals (u) {
  if k == 0 { return 0 };
  u := call env_erase(EREC.u64[ECON.u64[j] + 1]);
  u := call erase_installed(j - 1, k - 1);
  return 0
}

/-- `index_promoted(c, j, k)`: the constants at `ECON` positions `j, …, j - k + 1` indexed at
the counters `c - 1, c - 2, …` (`indexPromoted`; a row holds the counter plus one). -/
-- con-ron: ConRon/Arena/Promote.lean:350-356 ConRon.Arena.indexPromoted
@[l_impl ConRon.Arena.indexPromoted]
def indexPromotedL : FunDecl := lfn (c, j, k) locals (u, p) {
  if k == 0 { return 0 };
  p := ECON.u64[j];
  u := call env_row_set(EREC.u64[p + 1], c, p);
  u := call index_promoted(c - 1, j - 1, k - 1);
  return 0
}

/-- `promote_new(k, vis, fresh)`: `promoteNew pm coreWalkFuel k` at view `vis`, the memo
`PMemo.empty` when `fresh ≠ 0` and the one `promote_vg` left otherwise. The step's constants are
the `min k n` newest (`List.take`), `n = CTL[128]` the environment's length. -/
-- con-ron: ConRon/Arena/Promote.lean:358-378 ConRon.Arena.promoteNew
@[l_impl ConRon.Arena.promoteNew]
def promoteNewL : FunDecl := lfn (k, vis, fresh) locals (n, c, u) {
  if k == 0 { return 0 };
  if fresh != 0 { u := call promote_clear() };
  n := CTL.u64[128];
  c := k;
  if n < k { c := n };
  u := call erase_installed(n - 1, c);
  u := call promote_ci_list(⟪CWF⟫, n - 1, c);
  u := call index_promoted(vis, n - 1, c);
  return 0
}

/-! ## The program -/

/-- This module's functions, with the four memos' instances. -/
def promoteFns : Prog :=
  [("pi_bvar", piBVar), ("pi_fvar", piFVar), ("pi_sort", piSort), ("pi_const", piConst),
   ("pi_app", piApp), ("pi_lam", piLam), ("pi_forall", piForall), ("pi_let", piLet),
   ("pi_lit", piLit), ("pi_lit_str", piLitStr), ("pi_proj", piProj), ("pi_nanon", piNAnon),
   ("pi_nstr", piNStr), ("pi_nnum", piNNum), ("pi_zero", piZero), ("pi_succ", piSucc),
   ("pi_max", piMax), ("pi_imax", piImax), ("pi_param", piParam), ("pi_ls", piLs),
   ("pn_arm", pnArm), ("promote_n", promoteNL), ("pl_arm", plArm), ("promote_l", promoteLL),
   ("promote_l_pool", promoteLPool), ("pls_arm", plsArm), ("promote_ls", promoteLsL),
   ("pe_lit", peLit), ("pe_const", peConst), ("pe_app", peApp), ("pe_lam", peLam),
   ("pe_forall", peForall), ("pe_let", peLet), ("pe_proj", peProj), ("pe_arm", peArm),
   ("promote_e", promoteEL), ("promote_n_list", promoteNListL),
   ("promote_l_list", promoteLListL), ("promote_e_list", promoteEListL),
   ("promote_slice", promoteSlice), ("promote_cv", promoteCVL), ("promote_fire", promoteFireL),
   ("promote_rule", promoteRuleL), ("promote_rules", promoteRulesL),
   ("promote_caps", promoteCapsL), ("promote_proj_table", promoteProjTableL),
   ("pci_cv", pciCv), ("pci_defn", pciDefn), ("pci_ind", pciInd), ("pci_ctor", pciCtor),
   ("pci_rec", pciRec), ("promote_ci", promoteCIL), ("promote_ci_list", promoteCIListL),
   ("promote_clear", promoteClear), ("promote_vg", promoteVGL),
   ("erase_installed", eraseInstalledL), ("index_promoted", indexPromotedL),
   ("promote_new", promoteNewL),
   ("pn_find", memoFindG pnSch), ("pn_put", memoPutG pnSch), ("pn_clear", memoClearG pnSch),
   ("pl_find", memoFindG plSch), ("pl_put", memoPutG plSch), ("pl_clear", memoClearG plSch),
   ("pls_find", memoFindG plsSch), ("pls_put", memoPutG plsSch),
   ("pls_clear", memoClearG plsSch),
   ("pe_find", memoFindG peSch), ("pe_put", memoPutG peSch), ("pe_clear", memoClearG peSch)]

end L.Arena
