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
/-- `pool_alloc0(l)`: `l` words at the tier-0 pool top, which moves past them (`CTL[0]` outside
the scratch tier, the saved `PT0[0]` inside it): a persistent node's slice (lane tierpool). -/
-- con-ron: none — the limb pool's tiers (con-ron clones the promoted `Vec`)
def poolAlloc0 : FunDecl := lfn (l) locals (t, q) {
  t := CTL.u64[0];
  if t >> 40 == 0 { q := t } else { q := PT0.u64[0] };
  if len(POOL⟨0⟩) < q { abort };
  if len(POOL⟨0⟩) - q < l { abort };
  if t >> 40 == 0 { CTL.u64[0] := q + l } else { PT0.u64[0] := q + l };
  return q
}

/-- `pool_copy0`'s loop: the words `POOL⦃o + j‥o + l⦄` to `POOL⟨0⟩[q + j‥q + l]`. -/
def copy0Loop : Stmt := lblk (o, l, q, j) {
  while j < l {
    POOL⟨0⟩[q + j] := POOL⦃o + j⦄;
    j += 1
  }
}

/-- `pool_copy0(o, l)`: a tier-0 copy of the slice `(o, l)`, its address. -/
-- con-ron: none — the limb pool's tiers (con-ron clones the promoted `Vec`)
def poolCopy0 : FunDecl := lfn (o, l) locals (q, j) {
  q := call pool_alloc0(l);
  ⟪copy0Loop⟫;
  return q
}

/-- `pi_lit(o, l)` (a `natVal`). -/
-- con-ron: ConRon/Arena/Monad.lean:627-645 ConRon.Arena.internPersistentE
def piLit : FunDecl := lfn (o, l) locals (sc, r) {
  if o >> 40 != 0 { o := call pool_copy0(o, l) };
  sc := CTL.u64[1]; CTL.u64[1] := 0; r := call intern_lit(o, l); CTL.u64[1] := sc; return r
}
/-- `pi_lit_str(o, l)` (a `strVal`). -/
-- con-ron: ConRon/Arena/Monad.lean:627-645 ConRon.Arena.internPersistentE
def piLitStr : FunDecl := lfn (o, l) locals (sc, r) {
  if o >> 40 != 0 { o := call pool_copy0(o, l) };
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
  if o >> 40 != 0 { o := call pool_copy0(o, l) };
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
  if o >> 40 != 0 { o := call pool_copy0(o, l) };
  sc := CTL.u64[1]; CTL.u64[1] := 0; r := call intern_ls(o, l); CTL.u64[1] := sc; return r
}

/-! ## Names -/

/-- `pn_arm(f, h)`: view the scratch name `h`, promote its prefix at fuel `f`, intern the node
persistently (`promoteN`'s three view arms). -/
-- con-ron: ConRon/Arena/Promote.lean:80-101 ConRon.Arena.promoteN
@[l_impl ConRon.Arena.promoteN]
def pnArm : FunDecl := lfn (f, h) locals (g, t, i, q, o, l, r) {
  g := h >> 28;
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if 4294967295 < h { abort };
  if t != 0 && CTL.u64[1] == 0 { abort };
  if g == 0 {
    if NANON⟨t⟩.count <= i { abort };
    r := call pi_nanon();
    return r
  };
  if g == 1 {
    if NSTR⟨t⟩.count <= i { abort };
    q := NSTR⟨t, i⟩.p;
    o := NSTR⟨t, i⟩.o;
    l := NSTR⟨t, i⟩.l;
    q := call promote_n(f, q);
    r := call pi_nstr(q, o, l);
    return r
  };
  if g == 2 {
    if NNUM⟨t⟩.count <= i { abort };
    q := NNUM⟨t, i⟩.p;
    o := NNUM⟨t, i⟩.i;
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
  if ⟦h⟧.tier == 0 { return h };
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
  if ⟦h⟧.tier == 0 { return h };
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
def promoteLPool : FunDecl := lfn (f, o, l, q) locals (x, r, u, pt, pb) {
  if l == 0 { return 0 };
  pt := ⦃q⦄.tier;
  pb := ⦃q⦄.base;
  x := POOL⦃o⦄;
  r := call promote_l(f, x);
  POOL⟨pt⟩[q - pb] := r;
  u := call promote_l_pool(f, o + 1, l - 1, q + 1);
  return 0
}

/-- `pls_arm(f, h)`: the scratch level list `h` (a pool slice), promoted above the pool top (in
the top's tier), the top raised over it, interned persistently (`pi_ls` copies a tier-1 slice to
tier 0; lane tierpool). -/
-- con-ron: ConRon/Arena/Promote.lean:140-150 ConRon.Arena.promoteLs
@[l_impl ConRon.Arena.promoteLs]
def plsArm : FunDecl := lfn (f, h) locals (o, l, q, u, r, pt, pb) {
  if 4294967295 < h { abort };
  (o, l) := call ls_node(h);
  q := CTL.u64[0];
  pt := ⦃q⦄.tier;
  pb := ⦃q⦄.idx;
  if len(POOL⟨pt⟩) < pb { abort };
  if len(POOL⟨pt⟩) - pb < l { abort };
  u := call promote_l_pool(f, o, l, q);
  CTL.u64[0] := q + l;
  r := call pi_ls(q, l);
  return r
}

/-- `promote_ls(f, h)`: `promoteLs` at fuel `f` (not decremented). -/
-- con-ron: ConRon/Arena/Promote.lean:140-150 ConRon.Arena.promoteLs
@[l_impl ConRon.Arena.promoteLs]
def promoteLsL : FunDecl := lfn (f, h) locals (fd, j, d, r, u) {
  if ⟦h⟧.tier == 0 { return h };
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
def peLit : FunDecl := lfn (h) locals (t, i, o, l, r) {
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  o := LIT⟨t, i⟩.o;
  l := LIT⟨t, i⟩.l;
  if LIT⟨t, i⟩.kind == 1 { r := call pi_lit_str(o, l); return r };
  r := call pi_lit(o, l);
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
  if ⟦h⟧.tier == 0 { return h };
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
def promoteNListL : FunDecl := lfn (f, o, l, q) locals (x, r, u) {
  if l == 0 { return 0 };
  x := EREC.u64[o];
  r := call promote_n(f, x);
  EREC.u64[q] := r;
  u := call promote_n_list(f, o + 1, l - 1, q + 1);
  return 0
}

/-- `promote_l_list(f, o, l, q)`: the same for level handles (`promoteLList`). -/
-- con-ron: ConRon/Arena/Promote.lean:131-138 ConRon.Arena.promoteLList
@[l_impl ConRon.Arena.promoteLList]
def promoteLListL : FunDecl := lfn (f, o, l, q) locals (x, r, u) {
  if l == 0 { return 0 };
  x := EREC.u64[o];
  r := call promote_l(f, x);
  EREC.u64[q] := r;
  u := call promote_l_list(f, o + 1, l - 1, q + 1);
  return 0
}

/-- `promote_e_list(f, o, l, q)`: the same for expression handles (`promoteEList`). -/
-- con-ron: ConRon/Arena/Promote.lean:211-218 ConRon.Arena.promoteEList
@[l_impl ConRon.Arena.promoteEList]
def promoteEListL : FunDecl := lfn (f, o, l, q) locals (x, r, u) {
  if l == 0 { return 0 };
  x := EREC.u64[o];
  r := call promote_e(f, x);
  EREC.u64[q] := r;
  u := call promote_e_list(f, o + 1, l - 1, q + 1);
  return 0
}

/-- `erec_rd1(s)`: the 1 word(s) at `EREC[s‥s+1)`. -/
-- con-ron: none — reads/writes the words of an `EREC` record (the twin's records are values)
def erecRd1 : FunDecl := lfn (s) locals () {
  return EREC.u64[s]
}

/-- `erec_rd2(s)`: the 2 word(s) at `EREC[s‥s+2)`. -/
-- con-ron: none — reads/writes the words of an `EREC` record (the twin's records are values)
def erecRd2 : FunDecl := lfn (s) locals () {
  return (EREC.u64[s], EREC.u64[s + 1])
}

/-- `erec_rd3(s)`: the 3 word(s) at `EREC[s‥s+3)`. -/
-- con-ron: none — reads/writes the words of an `EREC` record (the twin's records are values)
def erecRd3 : FunDecl := lfn (s) locals () {
  return (EREC.u64[s], EREC.u64[s + 1], EREC.u64[s + 2])
}

/-- `erec_rd4(s)`: the 4 word(s) at `EREC[s‥s+4)`. -/
-- con-ron: none — reads/writes the words of an `EREC` record (the twin's records are values)
def erecRd4 : FunDecl := lfn (s) locals () {
  return (EREC.u64[s], EREC.u64[s + 1], EREC.u64[s + 2], EREC.u64[s + 3])
}

/-- `erec_rd5(s)`: the 5 word(s) at `EREC[s‥s+5)`. -/
-- con-ron: none — reads/writes the words of an `EREC` record (the twin's records are values)
def erecRd5 : FunDecl := lfn (s) locals () {
  return (EREC.u64[s], EREC.u64[s + 1], EREC.u64[s + 2], EREC.u64[s + 3], EREC.u64[s + 4])
}

/-- `erec_wr1(d, ..)`: 1 word(s) written at `EREC[d‥d+1)`. -/
-- con-ron: none — reads/writes the words of an `EREC` record (the twin's records are values)
def erecWr1 : FunDecl := lfn (d, a) locals () {
  EREC.u64[d] := a;
  return 0
}

/-- `erec_wr2(d, ..)`: 2 word(s) written at `EREC[d‥d+2)`. -/
-- con-ron: none — reads/writes the words of an `EREC` record (the twin's records are values)
def erecWr2 : FunDecl := lfn (d, a, b) locals () {
  EREC.u64[d] := a;
  EREC.u64[d + 1] := b;
  return 0
}

/-- `erec_wr3(d, ..)`: 3 word(s) written at `EREC[d‥d+3)`. -/
-- con-ron: none — reads/writes the words of an `EREC` record (the twin's records are values)
def erecWr3 : FunDecl := lfn (d, a, b, c) locals () {
  EREC.u64[d] := a;
  EREC.u64[d + 1] := b;
  EREC.u64[d + 2] := c;
  return 0
}

/-- `erec_wr4(d, ..)`: 4 word(s) written at `EREC[d‥d+4)`. -/
-- con-ron: none — reads/writes the words of an `EREC` record (the twin's records are values)
def erecWr4 : FunDecl := lfn (d, a, b, c, e) locals () {
  EREC.u64[d] := a;
  EREC.u64[d + 1] := b;
  EREC.u64[d + 2] := c;
  EREC.u64[d + 3] := e;
  return 0
}

/-- `erec_wr5(d, ..)`: 5 word(s) written at `EREC[d‥d+5)`. -/
-- con-ron: none — reads/writes the words of an `EREC` record (the twin's records are values)
def erecWr5 : FunDecl := lfn (d, a, b, c, e, g) locals () {
  EREC.u64[d] := a;
  EREC.u64[d + 1] := b;
  EREC.u64[d + 2] := c;
  EREC.u64[d + 3] := e;
  EREC.u64[d + 4] := g;
  return 0
}

/-- `erec_cp(d, s, n)`: `EREC[d + j] := EREC[s + j]` for `j < n`, in order. -/
-- con-ron: none — copies the words of an `EREC` record (the twin's records are values)
def erecCp : FunDecl := lfn (d, s, n) locals (x, u) {
  if n == 0 { return 0 };
  x := EREC.u64[s];
  EREC.u64[d] := x;
  u := call erec_cp(d + 1, s + 1, n - 1);
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

/-- `cv_rd(s)`: the four words of the constant value at `EREC[s‥s+4)`. -/
-- con-ron: none — reads an `EREC` record's words (the twin's `IConstantVal` is a value)
def cvRd : FunDecl := lfn (s) locals () {
  return (EREC.u64[s], EREC.u64[s + 1], EREC.u64[s + 2], EREC.u64[s + 3])
}

/-- `cv_wr(d, n, q, l, t)`: the four words of a constant value written at `EREC[d‥d+4)`. -/
-- con-ron: none — writes an `EREC` record's words (the twin's `IConstantVal` is a value)
def cvWr : FunDecl := lfn (d, n, q, l, t) locals () {
  EREC.u64[d] := n;
  EREC.u64[d + 1] := q;
  EREC.u64[d + 2] := l;
  EREC.u64[d + 3] := t;
  return 0
}

/-- `promote_cv(f, s)`: the constant value at `EREC[s‥s+4)` promoted (name, level parameters,
type, in that order); returns its four words `(name, lps.off, lps.len, type)`, the level
parameters a fresh `EREC` slice. The caller writes the record after every slice is allocated. -/
-- con-ron: ConRon/Arena/Promote.lean:229-235 ConRon.Arena.promoteCV
@[l_impl ConRon.Arena.promoteCV]
def promoteCVL : FunDecl := lfn (f, s) locals (n0, o, l, t0, n, q, t) {
  (n0, o, l, t0) := call cv_rd(s);
  n := call promote_n(f, n0);
  q := call promote_slice(0, f, o, l);
  t := call promote_e(f, t0);
  return (n, q, l, t)
}

/-- `promote_fire(f, s)`: a rule's firing mode (words `3‥8` of the 11-word rule record at `s`)
promoted; returns the five words of the promoted mode (`kind`, level slice offset and length,
pin slice offset and length). -/
-- con-ron: ConRon/Arena/Promote.lean:237-244 ConRon.Arena.promoteFire
@[l_impl ConRon.Arena.promoteFire]
def promoteFireL : FunDecl := lfn (f, s) locals (k, a, b, x, y, q, r) {
  (k, a, b, x, y) := call erec_rd5(s + 3);
  if k != 1 { return (k, 0, 0, 0, 0) };
  q := call promote_slice(1, f, a, b);
  r := call promote_slice(2, f, x, y);
  return (1, q, b, r, y)
}

/-- `pe_at(f, a)`: `promote_e` of the expression handle stored at `EREC[a]`. -/
-- con-ron: none — reads a handle of an `EREC` record (the twin's records are values)
def peAt : FunDecl := lfn (f, a) locals (w, r) {
  w := call erec_rd1(a);
  r := call promote_e(f, w);
  return r
}

/-- `rule_wr(d, s, c, r)`: the promoted constructor `c` and right-hand side `r` written into the
rule record `d`, the other words copied from the rule record `s`. -/
-- con-ron: none — writes the words of an `EREC` record (the twin's records are values)
def ruleWr : FunDecl := lfn (d, s, c, r) locals (w1, w2, w9, w10, u) {
  (w1, w2) := call erec_rd2(s + 1);
  (w9, w10) := call erec_rd2(s + 9);
  u := call erec_wr3(d, c, w1, w2);
  u := call erec_wr3(d + 8, r, w9, w10);
  return 0
}

/-- `promote_rule(f, s, d)`: the 11-word rule record at `s` promoted into `d` (constructor,
firing mode, right-hand side). -/
-- con-ron: ConRon/Arena/Promote.lean:246-252 ConRon.Arena.promoteRule
@[l_impl ConRon.Arena.promoteRule]
def promoteRuleL : FunDecl := lfn (f, s, d) locals (c, k, q, b, r2, y, r, u) {
  c := call pn_at(f, s);
  (k, q, b, r2, y) := call promote_fire(f, s);
  r := call pe_at(f, s + 8);
  u := call rule_wr(d, s, c, r);
  u := call erec_wr5(d + 3, k, q, b, r2, y);
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

/-- `pn_at(f, a)`: `promote_n` of the name handle stored at `EREC[a]`. -/
-- con-ron: none — reads a handle of an `EREC` record (the twin's records are values)
def pnAt : FunDecl := lfn (f, a) locals (w, r) {
  w := call erec_rd1(a);
  r := call promote_n(f, w);
  return r
}

/-- `pl_at(f, a)`: `promote_l` of the level handle stored at `EREC[a]`. -/
-- con-ron: none — reads a handle of an `EREC` record (the twin's records are values)
def plAt : FunDecl := lfn (f, a) locals (w, r) {
  w := call erec_rd1(a);
  r := call promote_l(f, w);
  return r
}

/-- `ps_at(k, f, a)`: `promote_slice(k, f, ..)` of the slice `(off, len)` stored at
`EREC[a], EREC[a + 1]`. -/
-- con-ron: none — reads a slice of an `EREC` record (the twin's records are values)
def psAt : FunDecl := lfn (k, f, a) locals (o, l, r) {
  (o, l) := call erec_rd2(a);
  r := call promote_slice(k, f, o, l);
  return r
}

/-- `caps_wr(d, c, a, k)`: the three promoted words of a capabilities record written. -/
-- con-ron: none — writes the words of an `EREC` record (the twin's records are values)
def capsWr : FunDecl := lfn (d, c, a, k) locals () {
  EREC.u64[d + 1] := c;
  EREC.u64[d + 10] := a;
  EREC.u64[d + 13] := k;
  return 0
}

/-- `proj_wr(d, sn, lp, c, ss, bs, gs)`: the six promoted words of a projection-table record
written. -/
-- con-ron: none — writes the words of an `EREC` record (the twin's records are values)
def projWr : FunDecl := lfn (d, sn, lp, c, ss, bs, gs) locals () {
  EREC.u64[d + 2] := sn;
  EREC.u64[d + 3] := lp;
  EREC.u64[d + 6] := c;
  EREC.u64[d + 8] := ss;
  EREC.u64[d + 9] := bs;
  EREC.u64[d + 11] := gs;
  return 0
}

/-- `caps_parts(f, s)`: the three promoted handles of the capabilities record at `s`
(`etaCtor`, `all`, `ctors`, in that order). -/
-- con-ron: ConRon/Arena/Promote.lean:263-271 ConRon.Arena.promoteCaps
@[l_impl ConRon.Arena.promoteCaps]
def capsParts : FunDecl := lfn (f, s) locals (c, a, k) {
  c := call pn_at(f, s + 1);
  a := call ps_at(0, f, s + 10);
  k := call ps_at(0, f, s + 13);
  return (c, a, k)
}

/-- `promote_caps(f, s, d)`: the 15-word capabilities record at `s` promoted into `d`
(`etaCtor`, `all`, `ctors`, in that order). `sortZ` is copied as the twin copies it: the twin's
`PropWhen` holds `ConLeche.Name` values, L's holds name handles read back by the fixed decoder
`dn`, so the copy decodes to the same value. -/
-- con-ron: ConRon/Arena/Promote.lean:263-271 ConRon.Arena.promoteCaps
@[l_impl ConRon.Arena.promoteCaps]
def promoteCapsL : FunDecl := lfn (f, s, d) locals (c, a, k, u) {
  (c, a, k) := call caps_parts(f, s);
  u := call erec_cp(d, s, 15);
  u := call caps_wr(d, c, a, k);
  return 0
}

/-- `proj_a(f, p)`: the first two promoted handles of the projection-table record at `p`
(`structName`, level parameters). -/
-- con-ron: ConRon/Arena/Promote.lean:273-282 ConRon.Arena.promoteProjTable
@[l_impl ConRon.Arena.promoteProjTable]
def projA : FunDecl := lfn (f, p) locals (sn, lp) {
  sn := call pn_at(f, p + 2);
  lp := call ps_at(0, f, p + 3);
  return (sn, lp)
}

/-- `proj_b(f, p)`: the other four promoted handles (`ctor`, `structSort`, bodies, guards). -/
-- con-ron: ConRon/Arena/Promote.lean:273-282 ConRon.Arena.promoteProjTable
@[l_impl ConRon.Arena.promoteProjTable]
def projB : FunDecl := lfn (f, p) locals (c, ss, bs, gs) {
  c := call pn_at(f, p + 6);
  ss := call pl_at(f, p + 8);
  bs := call ps_at(2, f, p + 9);
  gs := call ps_at(1, f, p + 11);
  return (c, ss, bs, gs)
}

/-- `promote_proj_table(f, p)`: the projection-table record at `p` (kind `6`, 13 words)
promoted into a fresh record, returned. Its link word (`p + 1`) is copied as it is: the list is
relinked by `promote_proj_tables`. -/
-- con-ron: ConRon/Arena/Promote.lean:273-282 ConRon.Arena.promoteProjTable
@[l_impl ConRon.Arena.promoteProjTable]
def promoteProjTableL : FunDecl := lfn (f, p) locals (d, sn, lp, c, ss, bs, gs, u) {
  d := call erec_alloc(13);
  (sn, lp) := call proj_a(f, p);
  (c, ss, bs, gs) := call proj_b(f, p);
  u := call erec_cp(d, p, 13);
  u := call proj_wr(d, sn, lp, c, ss, bs, gs);
  return d
}

/-- `pci_mk(p, n, nm, q, l, t)`: a fresh `n`-word record with `p`'s kind and the constant value
`(nm, q, l, t)` (the promoted one), allocated after the value's slice. -/
-- con-ron: ConRon/Arena/Promote.lean:284-309 ConRon.Arena.promoteCI
@[l_impl ConRon.Arena.promoteCI]
def pciMk : FunDecl := lfn (p, n, nm, q, l, t) locals (d, k, u) {
  d := call erec_alloc(n);
  k := call erec_rd1(p);
  u := call erec_wr1(d, k);
  u := call cv_wr(d + 1, nm, q, l, t);
  return d
}

/-- `pci_plain(f, p)`: `axiomInfo cv` and `thmInfo cv`. -/
-- con-ron: ConRon/Arena/Promote.lean:284-309 ConRon.Arena.promoteCI
@[l_impl ConRon.Arena.promoteCI]
def pciPlain : FunDecl := lfn (f, p) locals (nm, q, l, t, d) {
  (nm, q, l, t) := call promote_cv(f, p + 1);
  d := call pci_mk(p, 5, nm, q, l, t);
  return d
}

/-- `pci_defn(f, p)`: `defnInfo cv value hint`. -/
-- con-ron: ConRon/Arena/Promote.lean:284-309 ConRon.Arena.promoteCI
@[l_impl ConRon.Arena.promoteCI]
def pciDefn : FunDecl := lfn (f, p) locals (v, w6, w7, nm, q, l, t, x, d, u) {
  (v, w6, w7) := call erec_rd3(p + 5);
  (nm, q, l, t) := call promote_cv(f, p + 1);
  x := call promote_e(f, v);
  d := call pci_mk(p, 8, nm, q, l, t);
  u := call erec_wr3(d + 5, x, w6, w7);
  return d
}

/-- `pci_ind(f, p)`: `indInfo cv caps`. -/
-- con-ron: ConRon/Arena/Promote.lean:284-309 ConRon.Arena.promoteCI
@[l_impl ConRon.Arena.promoteCI]
def pciInd : FunDecl := lfn (f, p) locals (nm, q, l, t, d, u) {
  (nm, q, l, t) := call promote_cv(f, p + 1);
  d := call pci_mk(p, 20, nm, q, l, t);
  u := call promote_caps(f, p + 5, d + 5);
  return d
}

/-- `pci_ctor(f, p)`: `ctorInfo cv nP nF`. -/
-- con-ron: ConRon/Arena/Promote.lean:284-309 ConRon.Arena.promoteCI
@[l_impl ConRon.Arena.promoteCI]
def pciCtor : FunDecl := lfn (f, p) locals (w5, w6, nm, q, l, t, d, u) {
  (w5, w6) := call erec_rd2(p + 5);
  (nm, q, l, t) := call promote_cv(f, p + 1);
  d := call pci_mk(p, 7, nm, q, l, t);
  u := call erec_wr2(d + 5, w5, w6);
  return d
}

/-- `rec_block(d5, w5, w6, l)`: a fresh block of `11 l` words (the rules to come) and the four
words of the recursor record at `d5` (`majorIdx`, `rulePrefix`, the block, the count) written;
returns the block's offset. -/
-- con-ron: ConRon/Arena/Promote.lean:254-261 ConRon.Arena.promoteRules
@[l_impl ConRon.Arena.promoteRules]
def recBlock : FunDecl := lfn (d5, w5, w6, l) locals (b, u) {
  if 1152921504606846976 <= l { abort };
  b := call erec_alloc(11 * l);
  u := call erec_wr4(d5, w5, w6, b, l);
  return b
}

/-- `pci_rec(f, p)`: `recInfo cv major pre rules`. The record's words are written before the
rules are promoted into the block, so the promoted rules are the last thing written. -/
-- con-ron: ConRon/Arena/Promote.lean:284-309 ConRon.Arena.promoteCI
@[l_impl ConRon.Arena.promoteCI]
def pciRec : FunDecl := lfn (f, p) locals (w5, w6, w7, l, nm, q, cl, t, d, b, u) {
  (w5, w6, w7, l) := call erec_rd4(p + 5);
  (nm, q, cl, t) := call promote_cv(f, p + 1);
  d := call pci_mk(p, 9, nm, q, cl, t);
  b := call rec_block(d + 5, w5, w6, l);
  u := call promote_rules(f, w7, l, b);
  return d
}

/-- `promote_ci(f, p)`: the constant record at `p` promoted into a fresh record, returned
(`promoteCI`'s six arms). -/
-- con-ron: ConRon/Arena/Promote.lean:284-309 ConRon.Arena.promoteCI
@[l_impl ConRon.Arena.promoteCI]
def promoteCIL : FunDecl := lfn (f, p) locals (k, d) {
  k := call erec_rd1(p);
  if k == 0 || k == 2 { d := call pci_plain(f, p); return d };
  if k == 1 { d := call pci_defn(f, p); return d };
  if k == 3 { d := call pci_ind(f, p); return d };
  if k == 4 { d := call pci_ctor(f, p); return d };
  if k == 5 { d := call pci_rec(f, p); return d };
  abort
}

/-- `promote_ci_list(f, j, k)`: the constants at `ECON` positions `j, j - 1, …, j - k + 1`
(newest first, as `IEnv.consts`) promoted, each position overwritten with its new record. -/
-- con-ron: ConRon/Arena/Promote.lean:311-319 ConRon.Arena.promoteCIList
@[l_impl ConRon.Arena.promoteCIList]
def promoteCIListL : FunDecl := lfn (f, j, k) locals (d, u, p) {
  if k == 0 { return 0 };
  p := ECON.u64[j];
  d := call promote_ci(f, p);
  ECON.u64[j] := d;
  u := call promote_ci_list(f, j - 1, k - 1);
  return 0
}

/-- `promote_proj_tables(f, h, k)`: the `k` tables of the list from `h` (a record pointer plus
one; newest first, as `IEnv.tables`) promoted, each into a fresh record, in list order; the
promoted records are linked in the same order, the last one to what follows the `k` (`below`).
Returns the new list's head. -/
-- con-ron: ConRon/Arena/Promote.lean:321-329 ConRon.Arena.promoteProjTables
@[l_impl ConRon.Arena.promoteProjTables]
def promoteProjTablesL : FunDecl := lfn (f, h, k) locals (d, nx, r, u) {
  if k == 0 { return h };
  d := call promote_proj_table(f, h - 1);
  nx := call erec_rd1(h);
  r := call promote_proj_tables(f, nx, k - 1);
  u := call erec_wr1(d + 1, r);
  return d + 1
}

/-! ## The entries -/

/-- `promote_clear()`: the four memos emptied (`PMemo.empty`). -/
-- con-ron: ConRon/Arena/Promote.lean:72-74 ConRon.Arena.PMemo.empty
def promoteClear : FunDecl := lfn () locals (u) {
  u := call pn_clear(); u := call pl_clear(); u := call pls_clear(); u := call pe_clear();
  return 0
}

/-- `vg_rd(g)`: a value group's kind and value words. -/
-- con-ron: none — reads an `EREC` record's words (the twin's `ValueGroup` is a value)
def vgRd : FunDecl := lfn (g) locals () {
  return (EREC.u64[g], EREC.u64[g + 5])
}

/-- `vg_wr(d, k, n, q, l, t, x)`: a value group's six words written at `d`. -/
-- con-ron: none — writes an `EREC` record's words (the twin's `ValueGroup` is a value)
def vgWr : FunDecl := lfn (d, k, n, q, l, t, x) locals () {
  EREC.u64[d] := k;
  EREC.u64[d + 1] := n;
  EREC.u64[d + 2] := q;
  EREC.u64[d + 3] := l;
  EREC.u64[d + 4] := t;
  EREC.u64[d + 5] := x;
  return 0
}

/-- `promote_vg(g, vis)`: `promoteVG PMemo.empty coreWalkFuel` on the value group record `g`;
returns the promoted record, allocated after its parts. -/
-- con-ron: ConRon/Arena/Promote.lean:331-339 ConRon.Arena.promoteVG
@[l_impl ConRon.Arena.promoteVG]
def promoteVGL : FunDecl := lfn (g, vis) locals (k, j, n, q, l, t, x, d, u) {
  u := call promote_clear();
  (k, j) := call vg_rd(g);
  (n, q, l, t) := call promote_cv(⟪CWF⟫, g + 1);
  x := call promote_e(⟪CWF⟫, j);
  d := call erec_alloc(6);
  u := call vg_wr(d, k, n, q, l, t, x);
  return d
}

/-- `erase_installed(j, k)`: the index rows of the constants at `ECON` positions `j, …,
j - k + 1` erased (`eraseInstalled`, newest first). -/
-- con-ron: ConRon/Arena/Promote.lean:343-352 ConRon.Arena.eraseInstalled
@[l_impl ConRon.Arena.eraseInstalled]
def eraseInstalledL : FunDecl := lfn (j, k) locals (u, p, w) {
  if k == 0 { return 0 };
  p := ECON.u64[j];
  w := call erec_rd1(p + 1);
  u := call env_erase(w);
  u := call erase_installed(j - 1, k - 1);
  return 0
}

/-- `index_promoted(c, j, k)`: the constants at `ECON` positions `j, …, j - k + 1` indexed at
the counters `c - 1, c - 2, …` (`indexPromoted`; a row holds the counter plus one). -/
-- con-ron: ConRon/Arena/Promote.lean:354-360 ConRon.Arena.indexPromoted
@[l_impl ConRon.Arena.indexPromoted]
def indexPromotedL : FunDecl := lfn (c, j, k) locals (u, p, w) {
  if k == 0 { return 0 };
  p := ECON.u64[j];
  w := call erec_rd1(p + 1);
  u := call env_row_set(w, c, p);
  u := call index_promoted(c - 1, j - 1, k - 1);
  return 0
}

/-- `promote_new_consts(k, vis)`: `promoteNewConsts pm coreWalkFuel k` at view `vis` (the memo as
the caller left it). The step's constants are the `min k n` newest (`List.take`), `n = CTL[128]`
the environment's length. -/
-- con-ron: ConRon/Arena/Promote.lean:362-382 ConRon.Arena.promoteNewConsts
@[l_impl ConRon.Arena.promoteNewConsts]
def promoteNewConstsL : FunDecl := lfn (k, vis) locals (n, c, u) {
  if k == 0 { return 0 };
  n := CTL.u64[128];
  c := k;
  if n < k { c := n };
  u := call erase_installed(n - 1, c);
  u := call promote_ci_list(⟪CWF⟫, n - 1, c);
  u := call index_promoted(vis, n - 1, c);
  return 0
}

/-- `erase_installed_tables(h, k)`: the table rows of the `k` tables of the list from `h` erased
(`eraseInstalledTables`, newest first). -/
-- con-ron: ConRon/Arena/Promote.lean:384-391 ConRon.Arena.eraseInstalledTables
@[l_impl ConRon.Arena.eraseInstalledTables]
def eraseInstalledTablesL : FunDecl := lfn (h, k) locals (w, nx, u) {
  if k == 0 { return 0 };
  w := call erec_rd1(h + 1);
  u := call tbl_row_set(w, 0);
  nx := call erec_rd1(h);
  u := call erase_installed_tables(nx, k - 1);
  return 0
}

/-- `index_promoted_tables(h, k)`: the `k` tables of the list from `h` indexed under their
structures' names, the tail first (`indexPromotedTables`: the newest table of a name wins). -/
-- con-ron: ConRon/Arena/Promote.lean:393-400 ConRon.Arena.indexPromotedTables
@[l_impl ConRon.Arena.indexPromotedTables]
def indexPromotedTablesL : FunDecl := lfn (h, k) locals (w, nx, u) {
  if k == 0 { return 0 };
  nx := call erec_rd1(h);
  u := call index_promoted_tables(nx, k - 1);
  w := call erec_rd1(h + 1);
  u := call tbl_row_set(w, h);
  return 0
}

/-- `promote_new_tables(kt)`: `promoteNewTables pm coreWalkFuel kt` (the memo as the caller left
it). The step's tables are the `min kt n` newest, `n` the tables list's length; the list's head
moves to the promoted copies. -/
-- con-ron: ConRon/Arena/Promote.lean:402-415 ConRon.Arena.promoteNewTables
@[l_impl ConRon.Arena.promoteNewTables]
def promoteNewTablesL : FunDecl := lfn (kt) locals (n, c, h, h2, u) {
  if kt == 0 { return 0 };
  n := call tbl_cnt();
  c := kt;
  if n < kt { c := n };
  h := call tbl_head();
  u := call erase_installed_tables(h, c);
  h2 := call promote_proj_tables(⟪CWF⟫, h, c);
  u := call tbl_head_set(h2);
  u := call index_promoted_tables(h2, c);
  return 0
}

/-- `promote_new(k, kt, vis, fresh)`: `promoteNew pm coreWalkFuel k kt` at view `vis`, the memo
`PMemo.empty` when `fresh ≠ 0` and the one `promote_vg` left otherwise: the step's constants,
then its tables, at the one memo. -/
-- con-ron: ConRon/Arena/Promote.lean:417-423 ConRon.Arena.promoteNew
@[l_impl ConRon.Arena.promoteNew]
def promoteNewL : FunDecl := lfn (k, kt, vis, fresh) locals (u) {
  if fresh != 0 { u := call promote_clear() };
  u := call promote_new_consts(k, vis);
  u := call promote_new_tables(kt);
  return 0
}

/-! ## The program -/

end L.Arena
