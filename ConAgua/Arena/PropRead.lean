import ConAgua.Arena.LevelSubstL
import ConAgua.Arena.WhnfSpineRefine
import ConAgua.Arena.IndView
import ConAgua.Arena.Env
import ConAgua.Census.Attr

/-!
# The prop-ness readers `notProofFast` / `isProofFast` in L (lane `defeq2`, helper `defeq2-prop`)

con-ron's `Arena/PropRead.lean` (con-leche's `Kernel/PropRead.lean`): "is this term a proof?"
off the head symbol, the arity and the residual sorts of stored types, without inference.
`prop_irrel` (`DefEq.lean`) calls `not_proof_fast(vis, a)` and `is_proof_fast(vis, a)`.

**The datum.** The twin's `Option PropWhen` is three words `(k, o, c)`: `k = 0` is `none`, `k = 1`
`some .never`, `k = 2` `some (.ifAllZero ps)` with the parameter names `ps` the name words
`LH[o .. o + c)` on lane `levels`' scratch heap (array 192, top `CTL[192]`). `lv_zero` (the twin's
`Level.zeronessOf` on the read-back level) pushes them; `lv_spw` (`Level.substPW`'s `bindZ.go`)
reads them and pushes the substituted datum's. `not_proof_fast`/`is_proof_fast` reset the heap on
entry (as `lvl_eq`). The twin's `PropWhen.isProp` is `k = 2 ∧ c = 0`.

**Fuels.** The twin's `fuel` (`coreWalkFuel` at the entry) is an L argument `f`, decremented
exactly where the twin's `fuel + 1` patterns are: `proof_pw`'s and `type_sort_pw`'s loops,
`lam_proj`'s loop, and `app_count_at(e, f)` (`getAppFn fuel e` and `numArgs fuel e`: one walk,
the head and the count). `peelPisW`, `binderDom` and `unwrapIdDefs` are structural on their
counts (no fuel). `getAppArgs fuel e` runs only after `getAppFn fuel e` succeeded on the same `e`,
so the uncounted `get_app_args(e)` (at `coreWalkFuel`) has the same result.

**Readbacks.** The twin reads levels back (`readLevel`, `readNamesM`, `readLevelsM`) and runs
con-leche's algorithms on the trees; L runs lane `levels`' heap algorithms on the handles (keys:
the constant's level-parameter names, an `EREC` slice; values: the use's level list, a `POOL`
slice).

**Splits** (same semantics, for the proofs): `headTypePW` = `head_type_pw` (dispatch on the view)
+ `head_type_const` + `head_type_res` (`peelPisW` then `residualPW`); `headProofPW` =
`head_proof_pw` + `head_proof_const` + `head_proof_proj`; `unwrapIdDefs` = `unwrap_id_defs` (the
count) + `unwrap_step` (one δβ step); `typeSortPW`/`typeSortPWGo` = `type_sort_pw` (its loop a
named block). Every walk over a fixed chain of nodes (`binder_dom`, `lam_proj`, `type_sort_pw`,
`proof_pw`, `app_count_at`) is a named loop without calls.
-/

open ConRon.Arena


namespace L.Arena

/-! ## Syntactic telescope readers -/

/-- `binder_dom(k, e)`'s loop: `k` ∀ binders down, the domain at `k = 0`. -/
def binderDomLoop : Stmt := lblk (k, e, t, x) {
  while e >> 28 == 6 {
    t := ⟦e⟧.tier;
    x := ⟦e⟧.idx;
    if t != 0 && CTL.u64[1] == 0 { abort };
    if FORALL⟨t⟩.count <= x { abort };
    if k == 0 { return (1, FORALL⟨t, x⟩.ty) };
    e := FORALL⟨t, x⟩.b;
    k -= 1
  }
}

/-- con-ron: ConRon/Arena/PropRead.lean:59-74 ConRon.Arena.binderDom -/
@[l_impl ConRon.Arena.binderDom]
def binderDomL : FunDecl := lfn (k, e) locals (t, x) {
  ⟪binderDomLoop⟫;
  return (0, 0)
}

/-- `app_count_at(e, f)`'s loop: `get_app_fn`'s (`getAppFnLoop`), the start counter `f0` kept. -/
def appCountAtLoop : Stmt := lblk (e, f, t, x, f0) {
  while e >> 28 == 4 {
    if f == 0 { abort };
    f -= 1;
    t := ⟦e⟧.tier;
    x := ⟦e⟧.idx;
    if t != 0 && CTL.u64[1] == 0 { abort };
    if APP⟨t⟩.count <= x { abort };
    e := APP⟨t, x⟩.f
  }
}

/-- `app_count_at(e, f)`: `getAppFn f e` and `numArgs f e` in one walk at the counter `f`:
`(count, head)`. -/
-- con-ron: ConRon/Arena/PropRead.lean:76-89 ConRon.Arena.numArgs
-- con-ron: ConRon/Arena/ExprOps.lean:1281-1290 ConRon.Arena.getAppFn
@[l_impl ConRon.Arena.numArgs ConRon.Arena.getAppFn]
def appCountAtL : FunDecl := lfn (e, f) locals (t, x, f0) {
  f0 := f;
  ⟪appCountAtLoop⟫;
  if f == 0 { abort };
  return (f0 - f, e)
}

/-- con-ron: ConRon/Arena/PropRead.lean:91-105 ConRon.Arena.residualPW -/
@[l_impl ConRon.Arena.residualPW]
def residualPWL : FunDecl := lfn (fl, h) locals (t, x, t0, z) {
  if fl == 0 { return (0, 0, 0) };
  if h >> 28 != 2 { return (0, 0, 0) };
  t := ⟦h⟧.tier;
  x := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if SORT⟨t⟩.count <= x { abort };
  t0 := CTL.u64[192];
  z := call lv_zero(SORT⟨t, x⟩.u);
  if z != 0 { return (1, 0, 0) };
  return (2, t0, CTL.u64[192] - t0)
}

/-! ## Identity-like wrappers -/

/-- `lam_proj(f, k, e)`'s loop: down the λ chain, counting the binders. -/
def lamProjLoop : Stmt := lblk (f, k, e, t, x) {
  while e >> 28 == 5 {
    if f == 0 { abort };
    f -= 1;
    t := ⟦e⟧.tier;
    x := ⟦e⟧.idx;
    if t != 0 && CTL.u64[1] == 0 { abort };
    if LAM⟨t⟩.count <= x { abort };
    e := LAM⟨t, x⟩.b;
    k += 1
  }
}

/-- `lam_proj(f, k, e)`: `(1, k', j)` for `some (k', j)`, else `(0, 0, 0)`. -/
-- con-ron: ConRon/Arena/PropRead.lean:109-123 ConRon.Arena.lamProj?
@[l_impl ConRon.Arena.lamProj?]
def lamProjL : FunDecl := lfn (f, k, e) locals (t, x, j) {
  ⟪lamProjLoop⟫;
  if f == 0 { abort };
  if e >> 28 != 0 { return (0, 0, 0) };
  t := ⟦e⟧.tier;
  x := ⟦e⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if BVAR⟨t⟩.count <= x { abort };
  j := BVAR⟨t, x⟩.i;
  if j < k { return (1, k, j) };
  return (0, 0, 0)
}

/-- `unwrap_step(vis, f, e)`: one step of `unwrapIdDefs` (`(1, e')`), or `(0, 0)` where the twin
answers `e` itself. The argument slice `get_app_args` pushes is dropped (the top put back). -/
-- con-ron: ConRon/Arena/PropRead.lean:125-148 ConRon.Arena.unwrapIdDefs
@[l_impl ConRon.Arena.unwrapIdDefs]
def unwrapStepL : FunDecl :=
    lfn (vis, f, e) locals (cnt, hh, t, x, fd, p, lf, k, j, top, ao, an, r) {
  (cnt, hh) := call app_count_at(e, f);
  if hh >> 28 != 3 { return (0, 0) };
  t := ⟦hh⟧.tier;
  x := ⟦hh⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CONST⟨t⟩.count <= x { abort };
  (fd, p) := call env_find(CONST⟨t, x⟩.n, vis);
  if fd == 0 { return (0, 0) };
  if EREC.u64[p] != 1 { return (0, 0) };
  (lf, k, j) := call lam_proj(f, 0, EREC.u64[p + 5]);
  if lf == 0 { return (0, 0) };
  top := CTL.u64[136];
  (ao, an) := call get_app_args(e);
  if an != k { CTL.u64[136] := top; return (0, 0) };
  r := SPN.u64[ao + (k - 1 - j)];
  CTL.u64[136] := top;
  return (1, r)
}

/-- `unwrap_id_defs(vis, f, n, e)`: at most `n` steps. -/
-- con-ron: ConRon/Arena/PropRead.lean:125-148 ConRon.Arena.unwrapIdDefs
@[l_impl ConRon.Arena.unwrapIdDefs]
def unwrapIdDefsL : FunDecl := lfn (vis, f, n, e) locals (fl, e2, r) {
  if n == 0 { return e };
  (fl, e2) := call unwrap_step(vis, f, e);
  if fl == 0 { return e };
  r := call unwrap_id_defs(vis, f, n - 1, e2);
  return r
}

/-- `peel_pis_w(vis, f, k, e)`: `(1, e')` for `some e'`, `(0, 0)` for `none`. -/
-- con-ron: ConRon/Arena/PropRead.lean:150-168 ConRon.Arena.peelPisW
@[l_impl ConRon.Arena.peelPisW]
def peelPisWL : FunDecl := lfn (vis, f, k, e) locals (u, t, x, r1, r2) {
  if k == 0 {
    u := call unwrap_id_defs(vis, f, 4, e);
    return (1, u)
  };
  u := e;
  if e >> 28 != 6 {
    u := call unwrap_id_defs(vis, f, 4, e);
    if u >> 28 != 6 { return (0, 0) }
  };
  t := ⟦u⟧.tier;
  x := ⟦u⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if FORALL⟨t⟩.count <= x { abort };
  (r1, r2) := call peel_pis_w(vis, f, k - 1, FORALL⟨t, x⟩.b);
  return (r1, r2)
}

/-! ## The head readers -/

/-- `subst_pw_at(lo, lc, us, k, o, c)`: `Level.substPW` at a constant's level parameters (the
`EREC` slice `(lo, lc)`) and a use's level list `us`, only at a datum `ifAllZero (_ :: _)`. -/
-- con-ron: ConRon/Arena/PropRead.lean:172-184 ConRon.Arena.substPWAt
@[l_impl ConRon.Arena.substPWAt]
def substPWAtL : FunDecl := lfn (lo, lc, us, k, o, c) locals (vo, vc, t0, x) {
  if k != 2 { return (k, o, c) };
  if c == 0 { return (k, o, c) };
  (vo, vc) := call ls_node(us);
  t0 := CTL.u64[192];
  x := call lv_spw(o, c, lo, lc, vo, vc);
  if x != 0 { return (1, 0, 0) };
  return (2, t0, CTL.u64[192] - t0)
}

/-- `head_type_res(vis, f, n, ty)`: the residual's datum after `n` binders (`peelPisW`, then
`residualPW`). -/
-- con-ron: ConRon/Arena/PropRead.lean:186-219 ConRon.Arena.headTypePW
@[l_impl ConRon.Arena.headTypePW]
def headTypeResL : FunDecl := lfn (vis, f, n, ty) locals (pf, pv, k, o, c) {
  (pf, pv) := call peel_pis_w(vis, f, n, ty);
  (k, o, c) := call residual_pw(pf, pv);
  return (k, o, c)
}

/-- `head_type_const(vis, f, n, cn, us)`: `headTypePW`'s `.const` arm. -/
-- con-ron: ConRon/Arena/PropRead.lean:186-219 ConRon.Arena.headTypePW
@[l_impl ConRon.Arena.headTypePW]
def headTypeConstL : FunDecl := lfn (vis, f, n, cn, us) locals (fd, p, lo, l, k, o, c) {
  (fd, p) := call env_find(cn, vis);
  if fd == 0 { return (0, 0, 0) };
  (lo, l) := call ls_node(us);
  if l != EREC.u64[p + 3] { return (0, 0, 0) };
  (k, o, c) := call head_type_res(vis, f, n, EREC.u64[p + 4]);
  if k == 0 { return (0, 0, 0) };
  (k, o, c) := call subst_pw_at(EREC.u64[p + 2], EREC.u64[p + 3], us, k, o, c);
  return (k, o, c)
}

/-- `head_type_pw(vis, f, root, d, h, n)`: the dispatch on the head's view. -/
-- con-ron: ConRon/Arena/PropRead.lean:186-219 ConRon.Arena.headTypePW
@[l_impl ConRon.Arena.headTypePW]
def headTypePWL : FunDecl :=
    lfn (vis, f, root, d, h, n) locals (g, x1, x2, x3, bf, bd, k, o, c) {
  (g, x1, x2, x3) := call e_view(h);
  if g == 3 {
    (k, o, c) := call head_type_const(vis, f, n, x1, x2);
    return (k, o, c)
  };
  if g == 1 {
    (k, o, c) := call head_type_res(vis, f, n, x2);
    return (k, o, c)
  };
  if g == 0 && x1 < d {
    (bf, bd) := call binder_dom(d - 1 - x1, root);
    if bf == 0 { return (0, 0, 0) };
    (k, o, c) := call head_type_res(vis, f, n, bd);
    return (k, o, c)
  };
  return (0, 0, 0)
}

/-- `type_sort_pw`'s loop: down the ∀ telescope, counting the binders. -/
def typeSortPWLoop : Stmt := lblk (vis, f, rt, r, d, t, x) {
  while r >> 28 == 6 {
    if f == 0 { abort };
    f -= 1;
    t := ⟦r⟧.tier;
    x := ⟦r⟧.idx;
    if t != 0 && CTL.u64[1] == 0 { abort };
    if FORALL⟨t⟩.count <= x { abort };
    r := FORALL⟨t, x⟩.b;
    d += 1
  }
}

/-- `type_sort_pw(vis, f, rt)`: `typeSortPW` (`typeSortPWGo` from the root `rt`, depth `0`). -/
-- con-ron: ConRon/Arena/PropRead.lean:221-237 ConRon.Arena.typeSortPWGo
-- con-ron: ConRon/Arena/PropRead.lean:239-242 ConRon.Arena.typeSortPW
@[l_impl ConRon.Arena.typeSortPWGo ConRon.Arena.typeSortPW]
def typeSortPWL : FunDecl := lfn (vis, f, rt) locals (r, d, t, x, cnt, fn, k, o, c) {
  r := rt;
  d := 0;
  ⟪typeSortPWLoop⟫;
  if f == 0 { abort };
  f -= 1;
  if r >> 28 == 2 { return (1, 0, 0) };
  (cnt, fn) := call app_count_at(r, f);
  (k, o, c) := call head_type_pw(vis, f, rt, d, fn, cnt);
  return (k, o, c)
}

/-- `head_proof_const(vis, f, cn, us)`: `headProofPW`'s `.const` arm. -/
-- con-ron: ConRon/Arena/PropRead.lean:244-275 ConRon.Arena.headProofPW
@[l_impl ConRon.Arena.headProofPW]
def headProofConstL : FunDecl := lfn (vis, f, cn, us) locals (fd, p, lo, l, k, o, c) {
  (fd, p) := call env_find(cn, vis);
  if fd == 0 { return (0, 0, 0) };
  (lo, l) := call ls_node(us);
  if l != EREC.u64[p + 3] { return (0, 0, 0) };
  (k, o, c) := call type_sort_pw(vis, f, EREC.u64[p + 4]);
  if k == 0 { return (0, 0, 0) };
  (k, o, c) := call subst_pw_at(EREC.u64[p + 2], EREC.u64[p + 3], us, k, o, c);
  return (k, o, c)
}

/-- `head_proof_proj(vis, f, sn, i)`: `headProofPW`'s `.proj` arm (the table's body at field `i`,
the `Inhabited` handle `0` past the bodies, as `Array.getD`). -/
-- con-ron: ConRon/Arena/PropRead.lean:244-275 ConRon.Arena.headProofPW
@[l_impl ConRon.Arena.headProofPW]
def headProofProjL : FunDecl := lfn (vis, f, sn, i) locals (fd, q, b, k, o, c) {
  (fd, q) := call find_proj(vis, sn, i);
  if fd == 0 { return (0, 0, 0) };
  b := 0;
  if i < EREC.u64[q + 10] { b := EREC.u64[EREC.u64[q + 9] + i] };
  (k, o, c) := call type_sort_pw(vis, f, b);
  if k == 1 { return (1, 0, 0) };
  return (0, 0, 0)
}

/-- `head_proof_pw(vis, f, h)`: the dispatch on the head's view. -/
-- con-ron: ConRon/Arena/PropRead.lean:244-275 ConRon.Arena.headProofPW
@[l_impl ConRon.Arena.headProofPW]
def headProofPWL : FunDecl := lfn (vis, f, h) locals (g, x1, x2, x3, k, o, c) {
  (g, x1, x2, x3) := call e_view(h);
  if g == 3 {
    (k, o, c) := call head_proof_const(vis, f, x1, x2);
    return (k, o, c)
  };
  if g == 1 {
    (k, o, c) := call type_sort_pw(vis, f, x2);
    return (k, o, c)
  };
  if g == 2 { return (1, 0, 0) };
  if g == 6 { return (1, 0, 0) };
  if g == 8 { return (1, 0, 0) };
  if g == 9 {
    (k, o, c) := call head_proof_proj(vis, f, x1, x2);
    return (k, o, c)
  };
  return (0, 0, 0)
}

/-- `proof_pw`'s loop: through λ bodies, `let` bodies and application heads. -/
def proofPWLoop : Stmt := lblk (vis, f, e, t, x) {
  while e >> 28 == 5 || e >> 28 == 7 || e >> 28 == 4 {
    if f == 0 { abort };
    f -= 1;
    t := ⟦e⟧.tier;
    x := ⟦e⟧.idx;
    if t != 0 && CTL.u64[1] == 0 { abort };
    if e >> 28 == 5 {
      if LAM⟨t⟩.count <= x { abort };
      e := LAM⟨t, x⟩.b
    } else {
      if e >> 28 == 7 {
        if LET⟨t⟩.count <= x { abort };
        e := LET⟨t, x⟩.b
      } else {
        if APP⟨t⟩.count <= x { abort };
        e := APP⟨t, x⟩.f
      }
    }
  }
}

/-- con-ron: ConRon/Arena/PropRead.lean:277-298 ConRon.Arena.proofPW -/
@[l_impl ConRon.Arena.proofPW]
def proofPWL : FunDecl := lfn (vis, f, e) locals (t, x, k, o, c) {
  ⟪proofPWLoop⟫;
  if f == 0 { abort };
  f -= 1;
  (k, o, c) := call head_proof_pw(vis, f, e);
  return (k, o, c)
}

/-! ## The two arms -/

/-- `not_proof_fast(vis, a)`: the heap reset, then `proof_pw` at `coreWalkFuel`. -/
-- con-ron: ConRon/Arena/PropRead.lean:302-308 ConRon.Arena.notProofFast
@[l_impl ConRon.Arena.notProofFast]
def notProofFastL : FunDecl := lfn (vis, a) locals (k, o, c) {
  CTL.u64[192] := 0;
  (k, o, c) := call proof_pw(vis, 4000000000, a);
  if k == 0 { return 0 };
  if k == 2 && c == 0 { return 0 };
  return 1
}

/-- `is_proof_fast(vis, a)`. -/
-- con-ron: ConRon/Arena/PropRead.lean:310-316 ConRon.Arena.isProofFast
@[l_impl ConRon.Arena.isProofFast]
def isProofFastL : FunDecl := lfn (vis, a) locals (k, o, c) {
  CTL.u64[192] := 0;
  (k, o, c) := call proof_pw(vis, 4000000000, a);
  if k == 2 && c == 0 { return 1 };
  return 0
}

end L.Arena
