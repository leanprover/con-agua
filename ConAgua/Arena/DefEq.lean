import ConAgua.Arena.WhnfIota
import ConAgua.Arena.WhnfDelta
import ConAgua.Arena.CoreLevels
import ConAgua.Census.Attr

/-!
# Definitional equality: `defeqBody` and everything below it (phase 6, lane `defeq`)

con-ron's `Arena/Core.lean:2880-3535` (`defeqBody`, `quickDefEq`, the batched ∀ descent
`defeqPeel`, the λ-telescope `defeqLams`, offsets, the lazy-delta loop and its step, the
projection pair, the stuck comparison) and the helpers it reaches in `:240-460`, `:838-875`,
`:1360-1640` (`isBoolTrue`, `isEagerReduce`, `unfoldableHead`, `headHint`, `sameConstHeads`,
`ioNeutral`, `propIrrel`, `etaCert`, `stuckIrrel` and the structure-η / unit-like certificates),
in L, written top down. The knot's slots (`defeq`, `defeq_e`, `infer`, `infer_io`) are in
`Knot.lean`, the inference bodies in `Infer.lean`.

**Conventions** (lane `whnf`'s, `WhnfBase.lean`): the mode word (bit 0 trusted, bit 1 eager;
`verifiedChecks` is `mode & 1 == 0`, `eager` is `(mode >> 1) & 1 != 0`), the view word `vis`,
the depth word `d`; the knot record is the program (`r.defeq` is `call defeq(mode, …)`,
`r.defeqE` is `call defeq_e(mode, …)`, `r.whnfCore c` is `call whnf_core(mode, c, …)`, …). Lists
are slices of the spine stack `SPN` (array 144, top `CTL[136]`); a function that pushes puts the
top back before it returns. Every twin `fail` is an `abort` (ROADMAP §3 (c)); the twin's
`2^62` loop fuels (`defeqLoopFuel`, `lamsFuel`) are uncounted `while` loops (§3 (b)), `peelFuel`
(`2^24`) is an exact counter.

**Results.** `Bool`: `0`/`1`. `Option Bool` (`quick_defeq`, `defeq_offset`): `(flag, v)`.
`DeltaStepA` (`lazy_delta_step`, `delta_quick`): `(k, a, b)` with `k` = `0` `.cont a b`, `1`
`.eq`, `2` `.diff`, `3` `.unknown`. `LazyResA` (`lazy_delta_reduction`): `(k, a, b)` with `k` =
`0` `.verdict false`, `1` `.verdict true`, `2` `.unknown a b`. A reducibility hint (`head_hint`)
is `(kind, height)`, `kind` `0` opaque, `1` abbrev, `2` regular (`decHint`'s layout).

**Lean's `do` lifts every `(← …)` of a statement in front of it**: `(← isBoolTrue b) && (… ||
!(← hasFvarFast a))` runs both callees before the test, and so does L (`defeq_body`,
`defeq_offset`, `prop_irrel`, `stuck_str`, `lazy_delta_step`'s two unfolds).

**Callees not written yet** (stubs, `DefeqCallees` in `Knot.lean`): `has_fvar(e)`
(`hasFvarFast coreWalkFuel`), `not_proof_fast(vis, a)`, `is_proof_fast(vis, a)` (`PropRead.lean`,
phase 2); from lane `whnf`: `inst_list`, `inst1`, `find_proj`, `str_lit_supported`,
`str_lit_ctor`.
-/

open ConRon.Arena

set_option linter.unusedVariables false

namespace L.Arena

/-! ## Small readers -/

/-- con-ron: ConRon/Arena/Core.lean:840-852 ConRon.Arena.isBoolTrue -/
@[l_impl ConRon.Arena.isBoolTrue]
def isBoolTrueL : FunDecl := lfn (h) locals (t, i, el, bt) {
  if h >> 28 != 3 { return 0 };
  t := (h >> 27) & 1;
  i := h & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[18 + t] <= i { abort };
  el := call pin_word(52);
  if CREC.u64[i * 4 + t * 2 + 1] != el { return 0 };
  bt := call pin_at(30);
  return u64(CREC.u64[i * 4 + t * 2] == bt)
}

/-- con-ron: ConRon/Arena/Core.lean:854-874 ConRon.Arena.isEagerReduce -/
@[l_impl ConRon.Arena.isEagerReduce]
def isEagerReduceL : FunDecl := lfn (h) locals (t, i, f, g, er) {
  if h >> 28 != 4 { return 0 };
  t := (h >> 27) & 1;
  i := h & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[4 + t] <= i { abort };
  f := AREC.u64[i * 4 + t * 2];
  if f >> 28 != 4 { return 0 };
  t := (f >> 27) & 1;
  i := f & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[4 + t] <= i { abort };
  g := AREC.u64[i * 4 + t * 2];
  if g >> 28 != 3 { return 0 };
  t := (g >> 27) & 1;
  i := g & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[18 + t] <= i { abort };
  er := call pin_at(50);
  return u64(CREC.u64[i * 4 + t * 2] == er)
}

/-- `lit_eq(a, b)`: two literal handles hold equal literals (the twin's `l₁ == l₂` on the two
views): the same kind, the same length, the same limbs/bytes (`limbs_eq` on the pool slices;
`Nat` literals are trimmed, so equal values have equal slices). -/
-- con-ron: ConRon/Arena/Core.lean:3072-3098 ConRon.Arena.quickDefEq
@[l_impl ConRon.Arena.quickDefEq]
def litEqL : FunDecl := lfn (a, b) locals (ta, xa, tb, xb, la, lb, r) {
  ta := (a >> 27) & 1;
  xa := a & 134217727;
  if ta != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[2 + ta] <= xa { abort };
  tb := (b >> 27) & 1;
  xb := b & 134217727;
  if tb != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[2 + tb] <= xb { abort };
  if REC.u64[xa * 8 + ta * 4] != REC.u64[xb * 8 + tb * 4] { return 0 };
  la := REC.u64[xa * 8 + ta * 4 + 2];
  lb := REC.u64[xb * 8 + tb * 4 + 2];
  if la != lb { return 0 };
  r := call limbs_eq(REC.u64[xa * 8 + ta * 4 + 1], REC.u64[xb * 8 + tb * 4 + 1], la);
  return r
}

/-- con-ron: ConRon/Arena/Core.lean:316-325 ConRon.Arena.ioNeutral -/
@[l_impl ConRon.Arena.ioNeutral]
def ioNeutralL : FunDecl := lfn (e) locals (h, t) {
  h := call get_app_fn(e);
  t := h >> 28;
  if t == 5 || t == 7 || t == 0 { return 0 };
  return 1
}

/-- con-ron: ConRon/Arena/Core.lean:400-416 ConRon.Arena.unfoldableHead -/
@[l_impl ConRon.Arena.unfoldableHead]
def unfoldableHeadL : FunDecl := lfn (vis, e) locals (hh, t, i, f, p, lo, l) {
  hh := call get_app_fn(e);
  if hh >> 28 != 3 { return 0 };
  t := (hh >> 27) & 1;
  i := hh & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[18 + t] <= i { abort };
  (f, p) := call env_find(CREC.u64[i * 4 + t * 2], vis);
  if f == 0 { return 0 };
  if EREC.u64[p] != 1 { return 0 };
  (lo, l) := call ls_node(CREC.u64[i * 4 + t * 2 + 1]);
  return u64(l == EREC.u64[p + 3])
}

/-- con-ron: ConRon/Arena/Core.lean:418-429 ConRon.Arena.headHint -/
@[l_impl ConRon.Arena.headHint]
def headHintL : FunDecl := lfn (vis, e) locals (hh, t, i, f, p) {
  hh := call get_app_fn(e);
  if hh >> 28 != 3 { return (0, 0) };
  t := (hh >> 27) & 1;
  i := hh & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[18 + t] <= i { abort };
  (f, p) := call env_find(CREC.u64[i * 4 + t * 2], vis);
  if f == 0 { return (0, 0) };
  if EREC.u64[p] != 1 { return (0, 0) };
  return (EREC.u64[p + 6], EREC.u64[p + 7])
}

/-- `hint_lt(k1, h1, k2, h2)`: `ReducibilityHint.lt` on two `(kind, height)` hints (con-leche's
`Env.lean:206-211`, a pure function: `opaque < regular h < abbrev`). -/
-- con-ron: ConRon/Arena/Core.lean:3195-3252 ConRon.Arena.lazyDeltaStep
@[l_impl ConRon.Arena.lazyDeltaStep]
def hintLtL : FunDecl := lfn (k1, h1, k2, h2) locals () {
  if k2 == 0 { return 0 };
  if k1 == 1 { return 0 };
  if k1 == 0 { return 1 };
  if k2 == 1 { return 1 };
  return u64(h1 < h2)
}

/-- con-ron: ConRon/Arena/Core.lean:431-456 ConRon.Arena.sameConstHeads -/
@[l_impl ConRon.Arena.sameConstHeads]
def sameConstHeadsL : FunDecl := lfn (a, b) locals (t, i, f1, f2, hh, n1) {
  if a >> 28 != 4 { return 0 };
  t := (a >> 27) & 1;
  i := a & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[4 + t] <= i { abort };
  f1 := AREC.u64[i * 4 + t * 2];
  if b >> 28 != 4 { return 0 };
  t := (b >> 27) & 1;
  i := b & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[4 + t] <= i { abort };
  f2 := AREC.u64[i * 4 + t * 2];
  hh := call get_app_fn(f1);
  if hh >> 28 != 3 { return 0 };
  t := (hh >> 27) & 1;
  i := hh & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[18 + t] <= i { abort };
  n1 := CREC.u64[i * 4 + t * 2];
  hh := call get_app_fn(f2);
  if hh >> 28 != 3 { return 0 };
  t := (hh >> 27) & 1;
  i := hh & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[18 + t] <= i { abort };
  return u64(n1 == CREC.u64[i * 4 + t * 2])
}

/-- `er_slice_eq`'s loop (named, for its spec). -/
def erSliceEqLoop : Stmt := lblk (o1, n1, o2, n2, i) {
  while i < n1 {
    if EREC.u64[o1 + i] != EREC.u64[o2 + i] { return 0 };
    i += 1
  }
}

/-- `er_slice_eq(o1, n1, o2, n2)`: two `EREC` slices of handles are the same list (the twin's
`cvc.levelParams = cvT.levelParams`). -/
-- con-ron: ConRon/Arena/Core.lean:1492-1538 ConRon.Arena.structEtaCertWith
@[l_impl ConRon.Arena.structEtaCertWith]
def erSliceEqL : FunDecl := lfn (o1, n1, o2, n2) locals (i) {
  if n1 != n2 { return 0 };
  i := 0;
  ⟪erSliceEqLoop⟫;
  return 1
}

/-! ## Spines compared pairwise -/

/-- `defeq_lst(mode, vis, d, ao, an, bo, bn)`: the twin's `defEqList` on two stack slices, pair by
pair from the front **until either list ends** (a length mismatch is `false` only after the
common prefix compared equal, as the twin's list recursion). -/
-- con-ron: ConRon/Arena/Core.lean:1339-1346 ConRon.Arena.defEqList
@[l_impl ConRon.Arena.defEqList]
def defeqLstL : FunDecl := lfn (mode, vis, d, ao, an, bo, bn) locals (i, ok) {
  i := 0;
  while i < an && i < bn {
    ok := call defeq(mode, vis, d, SPN.u64[ao + i], SPN.u64[bo + i]);
    if ok == 0 { return 0 };
    i += 1
  };
  return u64(an == bn)
}

/-- `defeq_list_rev(mode, vis, d, ao, an, bo, bn)`: `defEqList` on the two REVERSED slices (from
the last pair to the first), `defeqSpine`'s order. -/
-- con-ron: ConRon/Arena/Core.lean:2887-2913 ConRon.Arena.defeqSpine
@[l_impl ConRon.Arena.defeqSpine]
def defeqListRevL : FunDecl := lfn (mode, vis, d, ao, an, bo, bn) locals (i, j, ok) {
  i := an;
  j := bn;
  while i != 0 && j != 0 {
    i -= 1;
    j -= 1;
    ok := call defeq(mode, vis, d, SPN.u64[ao + i], SPN.u64[bo + j]);
    if ok == 0 { return 0 }
  };
  return u64(an == bn)
}

/-- con-ron: ConRon/Arena/Core.lean:2880-2885 ConRon.Arena.boolTrueShortcut -/
@[l_impl ConRon.Arena.boolTrueShortcut]
def boolTrueShortcutL : FunDecl := lfn (mode, vis, d, a) locals (w, r) {
  w := call whnf(mode, vis, d, a);
  r := call is_bool_true(w);
  return r
}

/-- con-ron: ConRon/Arena/Core.lean:2887-2913 ConRon.Arena.defeqSpine -/
@[l_impl ConRon.Arena.defeqSpine]
def defeqSpineL : FunDecl :=
    lfn (mode, vis, d, a, b) locals (top, hh, t, i, n, us, n2, us2, ao, an, bo, bn, z, r) {
  hh := call get_app_fn(a);
  if hh >> 28 != 3 { return 0 };
  t := (hh >> 27) & 1;
  i := hh & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[18 + t] <= i { abort };
  n := CREC.u64[i * 4 + t * 2];
  us := CREC.u64[i * 4 + t * 2 + 1];
  hh := call get_app_fn(b);
  if hh >> 28 != 3 { return 0 };
  t := (hh >> 27) & 1;
  i := hh & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[18 + t] <= i { abort };
  n2 := CREC.u64[i * 4 + t * 2];
  us2 := CREC.u64[i * 4 + t * 2 + 1];
  top := CTL.u64[136];
  (ao, an) := call get_app_args(a);
  (bo, bn) := call get_app_args(b);
  if n == n2 && an == bn {
    z := call lvls_eq_c(us, us2);
    if z == 2 {
      r := call defeq_list_rev(mode, vis, d, ao, an, bo, bn);
      CTL.u64[136] := top;
      return r
    }
  };
  CTL.u64[136] := top;
  return 0
}

/-- con-ron: ConRon/Arena/Core.lean:2915-2923 ConRon.Arena.defeqNoFvars -/
@[l_impl ConRon.Arena.defeqNoFvars]
def defeqNoFvarsL : FunDecl := lfn (a, b) locals (x, y) {
  x := call has_fvar(a);
  if x != 0 { return 0 };
  y := call has_fvar(b);
  return u64(y == 0)
}

/-- con-ron: ConRon/Arena/Core.lean:2925-2931 ConRon.Arena.lazyFoldOk -/
@[l_impl ConRon.Arena.lazyFoldOk]
def lazyFoldOkL : FunDecl := lfn (mode, a, b) locals (r) {
  if (mode >> 1) & 1 != 0 { return 1 };
  r := call defeq_no_fvars(a, b);
  return r
}

/-! ## The binder descents -/

/-- The batched ∀ descent: `fvs` is the stack slice `(fo, k)` (`CTL[136] = fo + k`). -/
-- con-ron: ConRon/Arena/Core.lean:2952-3017 ConRon.Arena.defeqPeel
-- con-ron: ConRon/Arena/Core.lean:2943-2950 ConRon.Arena.defeqPeelLeaf
@[l_impl ConRon.Arena.defeqPeel ConRon.Arena.defeqPeelLeaf]
def defeqPeelL : FunDecl :=
    lfn (mode, vis, d, peel, a, b, k, fo) locals (o1, o2, t, i, da, ba, db, bb, t1, t2, dq, fv) {
  while 0 == 0 {
    if a == b { return 1 };
    if peel == 0 || a >> 28 != 6 || b >> 28 != 6 {
      o1 := call inst_list(a, fo, k, 0);
      o2 := call inst_list(b, fo, k, 0);
      dq := call defeq(mode, vis, d + k, o1, o2);
      return dq
    };
    t := (a >> 27) & 1;
    i := a & 134217727;
    if t != 0 && CTL.u64[1] == 0 { abort };
    if CTL.u64[30 + t] <= i { abort };
    da := FAREC.u64[i * 4 + t * 2];
    ba := FAREC.u64[i * 4 + t * 2 + 1];
    t := (b >> 27) & 1;
    i := b & 134217727;
    if t != 0 && CTL.u64[1] == 0 { abort };
    if CTL.u64[30 + t] <= i { abort };
    db := FAREC.u64[i * 4 + t * 2];
    bb := FAREC.u64[i * 4 + t * 2 + 1];
    t1 := call inst_list(da, fo, k, 0);
    if da == db {
      t2 := t1;
      dq := 1
    } else {
      t2 := call inst_list(db, fo, k, 0);
      dq := call defeq(mode, vis, d + k, t1, t2)
    };
    if dq == 0 { return 0 };
    fv := call intern_fvar(d + k, t2);
    if len(SPN.u64) <= fo + k { abort };
    SPN.u64[fo + k] := fv;
    k += 1;
    CTL.u64[136] := fo + k;
    peel -= 1;
    a := ba;
    b := bb
  };
  abort
}

/-- con-ron: ConRon/Arena/Core.lean:3019-3028 ConRon.Arena.defeqBinders -/
@[l_impl ConRon.Arena.defeqBinders]
def defeqBindersL : FunDecl := lfn (mode, vis, d, ty1, body1, ty2, body2) locals (ok, fv, so, r) {
  ok := call defeq(mode, vis, d, ty1, ty2);
  if ok == 0 { return 0 };
  fv := call intern_fvar(d, ty2);
  so := CTL.u64[136];
  if len(SPN.u64) <= so { abort };
  SPN.u64[so] := fv;
  CTL.u64[136] := so + 1;
  r := call defeq_peel(mode, vis, d, 16777216, body1, body2, 1, so);
  CTL.u64[136] := so;
  return r
}

/-- con-ron: ConRon/Arena/Core.lean:3036-3047 ConRon.Arena.defeqLamsInner -/
@[l_impl ConRon.Arena.defeqLamsInner]
def defeqLamsInnerL : FunDecl := lfn (mode, vis, d, b1, b2) locals (ok, t1, t2, r) {
  ok := call defeq(mode, vis, d + 1, b1, b2);
  if ok == 0 { return 0 };
  if mode & 1 == 0 {
    t1 := call infer(mode, vis, d + 1, b1);
    t2 := call infer(mode, vis, d + 1, b2);
    r := call defeq(mode, vis, d + 1, t1, t2);
    return r
  };
  return 1
}

/-- The λ-telescope congruence; the twin's `lamsFuel` (`2^62`) is not counted (ROADMAP §3 (b)):
an uncounted loop over the λ pairs. `lamPair?` is the tag test and the two binder reads. -/
-- con-ron: ConRon/Arena/Core.lean:3049-3070 ConRon.Arena.defeqLams
-- con-ron: ConRon/Arena/ExprOps.lean:1266-1277 ConRon.Arena.lamPair?
@[l_impl ConRon.Arena.defeqLams ConRon.Arena.lamPair?]
def defeqLamsL : FunDecl :=
    lfn (mode, vis, d, ty1, body1, ty2, body2) locals (ok, fv, b1, b2, t, i, r) {
  while 0 == 0 {
    ok := call defeq(mode, vis, d, ty1, ty2);
    if ok == 0 { return 0 };
    fv := call intern_fvar(d, ty2);
    b1 := call inst1(body1, fv, 0);
    b2 := call inst1(body2, fv, 0);
    if b1 >> 28 != 5 || b2 >> 28 != 5 {
      r := call defeq_lams_inner(mode, vis, d, b1, b2);
      return r
    };
    t := (b1 >> 27) & 1;
    i := b1 & 134217727;
    if t != 0 && CTL.u64[1] == 0 { abort };
    if CTL.u64[28 + t] <= i { abort };
    ty1 := LAREC.u64[i * 4 + t * 2];
    body1 := LAREC.u64[i * 4 + t * 2 + 1];
    t := (b2 >> 27) & 1;
    i := b2 & 134217727;
    if t != 0 && CTL.u64[1] == 0 { abort };
    if CTL.u64[28 + t] <= i { abort };
    ty2 := LAREC.u64[i * 4 + t * 2];
    body2 := LAREC.u64[i * 4 + t * 2 + 1];
    if b1 == b2 { return 1 };
    d += 1
  };
  abort
}

/-! ## The easy cases, offsets -/

/-- con-ron: ConRon/Arena/Core.lean:3072-3098 ConRon.Arena.quickDefEq -/
@[l_impl ConRon.Arena.quickDefEq]
def quickDefeqL : FunDecl :=
    lfn (mode, vis, d, a, b) locals (g, t, i, s, x1, y1, x2, y2, z, r) {
  if a == b { return (1, 1) };
  g := a >> 28;
  if g != b >> 28 { return (0, 0) };
  if g != 2 && g != 8 && g != 6 && g != 5 { return (0, 0) };
  t := (a >> 27) & 1;
  i := a & 134217727;
  s := (b >> 27) & 1;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if s != 0 && CTL.u64[1] == 0 { abort };
  if g == 2 {
    if CTL.u64[16 + t] <= i { abort };
    x1 := SOREC.u64[i * 2 + t];
    i := b & 134217727;
    if CTL.u64[16 + s] <= i { abort };
    z := call lvl_eq_c(x1, SOREC.u64[i * 2 + s]);
    if z == 0 { abort };
    return (1, z - 1)
  };
  if g == 8 {
    r := call lit_eq(a, b);
    return (1, r)
  };
  if g == 6 {
    if CTL.u64[30 + t] <= i { abort };
    x1 := FAREC.u64[i * 4 + t * 2];
    y1 := FAREC.u64[i * 4 + t * 2 + 1];
    i := b & 134217727;
    if CTL.u64[30 + s] <= i { abort };
    x2 := FAREC.u64[i * 4 + s * 2];
    y2 := FAREC.u64[i * 4 + s * 2 + 1];
    r := call defeq_binders(mode, vis, d, x1, y1, x2, y2);
    return (1, r)
  };
  if CTL.u64[28 + t] <= i { abort };
  x1 := LAREC.u64[i * 4 + t * 2];
  y1 := LAREC.u64[i * 4 + t * 2 + 1];
  i := b & 134217727;
  if CTL.u64[28 + s] <= i { abort };
  x2 := LAREC.u64[i * 4 + s * 2];
  y2 := LAREC.u64[i * 4 + s * 2 + 1];
  r := call defeq_lams(mode, vis, d, x1, y1, x2, y2);
  return (1, r)
}

/-- con-ron: ConRon/Arena/Core.lean:3100-3114 ConRon.Arena.isNatZero -/
@[l_impl ConRon.Arena.isNatZero]
def isNatZeroL : FunDecl := lfn (e) locals (t, i, el, nz) {
  t := (e >> 27) & 1;
  i := e & 134217727;
  if e >> 28 == 8 {
    if t != 0 && CTL.u64[1] == 0 { abort };
    if CTL.u64[2 + t] <= i { abort };
    if REC.u64[i * 8 + t * 4] != 0 { return 0 };
    return u64(REC.u64[i * 8 + t * 4 + 2] == 0)
  };
  if e >> 28 == 3 {
    if t != 0 && CTL.u64[1] == 0 { abort };
    if CTL.u64[18 + t] <= i { abort };
    el := call pin_word(52);
    nz := call pin_at(2);
    if CREC.u64[i * 4 + t * 2] == nz && CREC.u64[i * 4 + t * 2 + 1] == el { return 1 };
    return 0
  };
  return 0
}

/-- `nat_pred(e)`: `(1, x)` when `natPred? e = some x`, else `(0, 0)`. -/
-- con-ron: ConRon/Arena/Core.lean:3116-3138 ConRon.Arena.natPred?
@[l_impl ConRon.Arena.natPred?]
def natPredL : FunDecl := lfn (e) locals (t, i, l, f, x, el, ns) {
  t := (e >> 27) & 1;
  i := e & 134217727;
  if e >> 28 == 8 {
    if t != 0 && CTL.u64[1] == 0 { abort };
    if CTL.u64[2 + t] <= i { abort };
    if REC.u64[i * 8 + t * 4] != 0 { return (0, 0) };
    if REC.u64[i * 8 + t * 4 + 2] == 0 { return (0, 0) };
    l := call nat_pred_lit(REC.u64[i * 8 + t * 4 + 1], REC.u64[i * 8 + t * 4 + 2]);
    return (1, l)
  };
  if e >> 28 == 4 {
    if t != 0 && CTL.u64[1] == 0 { abort };
    if CTL.u64[4 + t] <= i { abort };
    f := AREC.u64[i * 4 + t * 2];
    x := AREC.u64[i * 4 + t * 2 + 1];
    if f >> 28 != 3 { return (0, 0) };
    t := (f >> 27) & 1;
    i := f & 134217727;
    if t != 0 && CTL.u64[1] == 0 { abort };
    if CTL.u64[18 + t] <= i { abort };
    el := call pin_word(52);
    ns := call pin_at(3);
    if CREC.u64[i * 4 + t * 2] == ns && CREC.u64[i * 4 + t * 2 + 1] == el { return (1, x) };
    return (0, 0)
  };
  return (0, 0)
}

/-- con-ron: ConRon/Arena/Core.lean:3140-3158 ConRon.Arena.defeqOffset -/
@[l_impl ConRon.Arena.defeqOffset]
def defeqOffsetL : FunDecl := lfn (mode, vis, d, a, b) locals (za, zb, fa, x, fb, y, ok) {
  za := call is_nat_zero(a);
  zb := call is_nat_zero(b);
  if za != 0 && zb != 0 { return (1, 1) };
  if a >> 28 == 8 && b >> 28 == 8 { return (0, 0) };
  (fa, x) := call nat_pred(a);
  if fa == 0 { return (0, 0) };
  (fb, y) := call nat_pred(b);
  if fb == 0 { return (0, 0) };
  ok := call defeq(mode, vis, d, x, y);
  return (1, ok)
}

/-! ## Lazy delta -/

/-- con-ron: ConRon/Arena/Core.lean:3160-3164 ConRon.Arena.headIsProj -/
@[l_impl ConRon.Arena.headIsProj]
def headIsProjL : FunDecl := lfn (e) locals (h) {
  h := call get_app_fn(e);
  return u64(h >> 28 == 9)
}

/-- `try_unfold_proj_app(mode, vis, d, e)`: `(1, e')` when `tryUnfoldProjApp` is `some e'`. -/
-- con-ron: ConRon/Arena/Core.lean:3166-3175 ConRon.Arena.tryUnfoldProjApp
@[l_impl ConRon.Arena.tryUnfoldProjApp]
def tryUnfoldProjAppL : FunDecl := lfn (mode, vis, d, e) locals (p, e2) {
  p := call head_is_proj(e);
  if p == 0 { return (0, 0) };
  e2 := call whnf_core(mode, 0, vis, d, e);
  if e2 == e { return (0, 0) };
  return (1, e2)
}

/-- con-ron: ConRon/Arena/Core.lean:3185-3193 ConRon.Arena.deltaQuick -/
@[l_impl ConRon.Arena.deltaQuick]
def deltaQuickL : FunDecl := lfn (mode, vis, d, a, b) locals (f, v) {
  (f, v) := call quick_defeq(mode, vis, d, a, b);
  if f == 0 { return (0, a, b) };
  if v != 0 { return (1, 0, 0) };
  return (2, 0, 0)
}

/-- One unfolding of the LEFT side: `unfoldDefinition`, the cheap `whnfCore`, `deltaQuick`
(`.unknown` when nothing unfolds). -/
-- con-ron: ConRon/Arena/Core.lean:3195-3252 ConRon.Arena.lazyDeltaStep
@[l_impl ConRon.Arena.lazyDeltaStep]
def ldsLeftL : FunDecl := lfn (mode, vis, d, a, b) locals (f, a2, a3, k, x, y) {
  (f, a2) := call unfold_definition(vis, a);
  if f == 0 { return (3, 0, 0) };
  a3 := call whnf_core(mode, 1, vis, d, a2);
  (k, x, y) := call delta_quick(mode, vis, d, a3, b);
  return (k, x, y)
}

/-- One unfolding of the RIGHT side. -/
-- con-ron: ConRon/Arena/Core.lean:3195-3252 ConRon.Arena.lazyDeltaStep
@[l_impl ConRon.Arena.lazyDeltaStep]
def ldsRightL : FunDecl := lfn (mode, vis, d, a, b) locals (f, b2, b3, k, x, y) {
  (f, b2) := call unfold_definition(vis, b);
  if f == 0 { return (3, 0, 0) };
  b3 := call whnf_core(mode, 1, vis, d, b2);
  (k, x, y) := call delta_quick(mode, vis, d, a, b3);
  return (k, x, y)
}

/-- The `true, true` arm of `lazyDeltaStep`: the hints, the same-head shortcut, both unfolds. -/
-- con-ron: ConRon/Arena/Core.lean:3195-3252 ConRon.Arena.lazyDeltaStep
@[l_impl ConRon.Arena.lazyDeltaStep]
def ldsBothL : FunDecl :=
    lfn (mode, vis, d, a, b) locals (ka, ha, kb, hb, lt, sch, sp, fa, a2, fb, b2, a3, b3, k, x, y) {
  (ka, ha) := call head_hint(vis, a);
  (kb, hb) := call head_hint(vis, b);
  lt := call hint_lt(kb, hb, ka, ha);
  if lt != 0 {
    (k, x, y) := call lds_left(mode, vis, d, a, b);
    return (k, x, y)
  };
  lt := call hint_lt(ka, ha, kb, hb);
  if lt != 0 {
    (k, x, y) := call lds_right(mode, vis, d, a, b);
    return (k, x, y)
  };
  sch := call same_const_heads(a, b);
  sp := 0;
  if ka == 2 && kb == 2 && ha == hb && sch != 0 { sp := call defeq_spine(mode, vis, d, a, b) };
  if sp != 0 { return (1, 0, 0) };
  (fa, a2) := call unfold_definition(vis, a);
  (fb, b2) := call unfold_definition(vis, b);
  if fa == 0 || fb == 0 { return (3, 0, 0) };
  a3 := call whnf_core(mode, 1, vis, d, a2);
  b3 := call whnf_core(mode, 1, vis, d, b2);
  (k, x, y) := call delta_quick(mode, vis, d, a3, b3);
  return (k, x, y)
}

/-- con-ron: ConRon/Arena/Core.lean:3195-3252 ConRon.Arena.lazyDeltaStep -/
@[l_impl ConRon.Arena.lazyDeltaStep]
def lazyDeltaStepL : FunDecl := lfn (mode, vis, d, a, b) locals (ua, ub, f, e2, k, x, y) {
  ua := call unfoldable_head(vis, a);
  ub := call unfoldable_head(vis, b);
  if ua == 0 && ub == 0 { return (3, 0, 0) };
  if ub == 0 {
    (f, e2) := call try_unfold_proj_app(mode, vis, d, b);
    if f != 0 {
      (k, x, y) := call delta_quick(mode, vis, d, a, e2);
      return (k, x, y)
    };
    (k, x, y) := call lds_left(mode, vis, d, a, b);
    return (k, x, y)
  };
  if ua == 0 {
    (f, e2) := call try_unfold_proj_app(mode, vis, d, a);
    if f != 0 {
      (k, x, y) := call delta_quick(mode, vis, d, e2, b);
      return (k, x, y)
    };
    (k, x, y) := call lds_right(mode, vis, d, a, b);
    return (k, x, y)
  };
  (k, x, y) := call lds_both(mode, vis, d, a, b);
  return (k, x, y)
}

/-- The lazy-delta loop on its uncounted `2^62` budget (`defeqLoopFuel`, ROADMAP §3 (b)). -/
-- con-ron: ConRon/Arena/Core.lean:3265-3293 ConRon.Arena.lazyDeltaReduction
@[l_impl ConRon.Arena.lazyDeltaReduction]
def lazyDeltaReductionL : FunDecl :=
    lfn (mode, vis, d, a, b) locals (of, ov, nf, fa, a2, fb, b2, v, k, x, y) {
  while 0 == 0 {
    (of, ov) := call defeq_offset(mode, vis, d, a, b);
    if of != 0 { return (ov, 0, 0) };
    nf := call lazy_fold_ok(mode, a, b);
    if nf != 0 {
      (fa, a2) := call reduce_nat(mode, vis, d, a);
      if fa != 0 {
        v := call defeq(mode, vis, d, a2, b);
        return (v, 0, 0)
      };
      (fb, b2) := call reduce_nat(mode, vis, d, b);
      if fb != 0 {
        v := call defeq(mode, vis, d, a, b2);
        return (v, 0, 0)
      }
    };
    (k, x, y) := call lazy_delta_step(mode, vis, d, a, b);
    if k == 1 { return (1, 0, 0) };
    if k == 2 { return (0, 0, 0) };
    if k == 3 { return (2, a, b) };
    a := x;
    b := y
  };
  abort
}

/-- The projection loop on its uncounted budget. -/
-- con-ron: ConRon/Arena/Core.lean:3295-3315 ConRon.Arena.lazyDeltaProjReduction
@[l_impl ConRon.Arena.lazyDeltaProjReduction]
def lazyDeltaProjReductionL : FunDecl :=
    lfn (mode, vis, d, sn, i, a, b) locals (k, x, y, fx, px, fy, py, r) {
  while 0 == 0 {
    (k, x, y) := call lazy_delta_step(mode, vis, d, a, b);
    if k != 0 {
      if k == 1 { return 1 };
      (fx, px) := call reduce_proj_core(mode, vis, d, sn, i, a);
      if fx != 0 {
        (fy, py) := call reduce_proj_core(mode, vis, d, sn, i, b);
        if fy != 0 {
          r := call defeq(mode, vis, d, px, py);
          return r
        }
      };
      r := call defeq(mode, vis, d, a, b);
      return r
    };
    a := x;
    b := y
  };
  abort
}

/-- con-ron: ConRon/Arena/Core.lean:3317-3330 ConRon.Arena.defeqProjPair -/
@[l_impl ConRon.Arena.defeqProjPair]
def defeqProjPairL : FunDecl := lfn (mode, vis, d, a, b) locals (t, i, s, x1, x2, x3, r) {
  if a >> 28 != 9 || b >> 28 != 9 { return 0 };
  t := (a >> 27) & 1;
  i := a & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[32 + t] <= i { abort };
  x1 := PJREC.u64[i * 6 + t * 3];
  x2 := PJREC.u64[i * 6 + t * 3 + 1];
  x3 := PJREC.u64[i * 6 + t * 3 + 2];
  s := (b >> 27) & 1;
  i := b & 134217727;
  if s != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[32 + s] <= i { abort };
  if x1 == PJREC.u64[i * 6 + s * 3] && x2 == PJREC.u64[i * 6 + s * 3 + 1] {
    r := call lazy_delta_proj_reduction(mode, vis, d, x1, x2, x3, PJREC.u64[i * 6 + s * 3 + 2]);
    return r
  };
  return 0
}

/-! ## Proof irrelevance, η, the stuck fallbacks -/

/-- con-ron: ConRon/Arena/Core.lean:1387-1418 ConRon.Arena.propIrrel -/
@[l_impl ConRon.Arena.propIrrel]
def propIrrelL : FunDecl := lfn (mode, vis, d, a, b) locals (na, nb, ia, ib, r) {
  na := call not_proof_fast(vis, a);
  nb := call not_proof_fast(vis, b);
  if na != 0 || nb != 0 { return 0 };
  ia := call is_proof_fast(vis, a);
  ib := call is_proof_fast(vis, b);
  if ia != 0 && ib != 0 { return 1 };
  r := call proof_irrel(mode, vis, d, a, b);
  return r
}

/-- `etaCert`'s verified-mode check: the λ body's full-grade type against the ∀'s codomain at
the fresh variable `fv` (split off for the proofs). -/
-- con-ron: ConRon/Arena/Core.lean:1599-1625 ConRon.Arena.etaCert
@[l_impl ConRon.Arena.etaCert]
def etaCertTyL : FunDecl := lfn (mode, vis, d, lhs, cod2, fv) locals (t1, t2, ok) {
  t1 := call infer(mode, vis, d + 1, lhs);
  t2 := call inst1(cod2, fv, 0);
  ok := call defeq(mode, vis, d + 1, t1, t2);
  return ok
}

/-- `etaCert` once the domains agree: the bodies at a fresh variable (split off for the
proofs). The depth capacity: the word `d + 1` must not wrap where the twin's `Nat` does not. -/
-- con-ron: ConRon/Arena/Core.lean:1599-1625 ConRon.Arena.etaCert
@[l_impl ConRon.Arena.etaCert]
def etaCertBodyL : FunDecl := lfn (mode, vis, d, ty1, body1, b, cod2) locals (fv, lhs, rhs, ok) {
  if d + 1 == 0 { abort };
  fv := call intern_fvar(d, ty1);
  lhs := call inst1(body1, fv, 0);
  rhs := call mk_app(b, fv);
  ok := call defeq(mode, vis, d + 1, lhs, rhs);
  if ok == 0 { return 0 };
  if mode & 1 == 0 {
    ok := call eta_cert_ty(mode, vis, d, lhs, cod2, fv);
    return ok
  };
  return 1
}

/-- con-ron: ConRon/Arena/Core.lean:1599-1625 ConRon.Arena.etaCert -/
@[l_impl ConRon.Arena.etaCert]
def etaCertL : FunDecl :=
    lfn (mode, vis, d, ty1, body1, b) locals (nt, tb, hh, t, i, ty2, cod2, ok) {
  nt := call io_neutral(b);
  if nt == 0 { return 0 };
  tb := call infer_io(mode, vis, d, b);
  hh := call whnf(mode, vis, d, tb);
  if hh >> 28 != 6 { return 0 };
  t := (hh >> 27) & 1;
  i := hh & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[30 + t] <= i { abort };
  ty2 := FAREC.u64[i * 4 + t * 2];
  cod2 := FAREC.u64[i * 4 + t * 2 + 1];
  ok := call defeq(mode, vis, d, ty2, ty1);
  if ok == 0 { return 0 };
  ok := call eta_cert_body(mode, vis, d, ty1, body1, b, cod2);
  return ok
}

/-- con-ron: ConRon/Arena/Core.lean:1540-1555 ConRon.Arena.etaCtorShape -/
@[l_impl ConRon.Arena.etaCtorShape]
def etaCtorShapeL : FunDecl := lfn (vis, a) locals (top, hh, t, i, f, p, ao, an, nf) {
  hh := call get_app_fn(a);
  if hh >> 28 != 3 { return 0 };
  t := (hh >> 27) & 1;
  i := hh & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[18 + t] <= i { abort };
  (f, p) := call env_find(CREC.u64[i * 4 + t * 2], vis);
  if f == 0 { return 0 };
  if EREC.u64[p] != 4 { return 0 };
  top := CTL.u64[136];
  (ao, an) := call get_app_args(a);
  CTL.u64[136] := top;
  nf := EREC.u64[p + 6];
  if an < nf { return 0 };
  return u64(an - nf == EREC.u64[p + 5])
}

/-- The η certificate's checks after the two heads are found (`c` the constructor's record `p`,
`T` the type's record `q`, the spines `(ao, an)`, `(to, tn)` on the stack). -/
-- con-ron: ConRon/Arena/Core.lean:1492-1538 ConRon.Arena.structEtaCertWith
@[l_impl ConRon.Arena.structEtaCertWith]
def structEtaCertGoL : FunDecl :=
    lfn (mode, vis, d, b, us, c, p, T, q, us2, ao, an, to, tn)
    locals (lo, uslen, slots, r1, r2, lpe, z, ok, ep, tk, po, pn) {
  (lo, uslen) := call ls_node(us2);
  slots := call tower_slots_all(vis, T, EREC.u64[q + 8]);
  if EREC.u64[q + 5] == 0 { return 0 };
  if EREC.u64[q + 6] != c { return 0 };
  r1 := call reserved_contains(T);
  if r1 != 0 { return 0 };
  r2 := call reserved_contains(c);
  if r2 != 0 { return 0 };
  ep := EREC.u64[q + 7];
  if tn != ep { return 0 };
  if uslen != EREC.u64[q + 3] { return 0 };
  lpe := call er_slice_eq(EREC.u64[p + 2], EREC.u64[p + 3], EREC.u64[q + 2], EREC.u64[q + 3]);
  if lpe == 0 { return 0 };
  if slots == 0 { return 0 };
  z := call lvls_eq_c(us, us2);
  if z == 0 { abort };
  if z == 1 { return 0 };
  tk := ep;
  if an < tk { tk := an };
  ok := call defeq_lst(mode, vis, d, ao, tk, to, tn);
  if ok == 0 { return 0 };
  (po, pn) := call eta_projs(T, b, EREC.u64[q + 8]);
  ok := call defeq_lst(mode, vis, d, ao + tk, an - tk, po, pn);
  return ok
}

/-- con-ron: ConRon/Arena/Core.lean:1492-1538 ConRon.Arena.structEtaCertWith -/
@[l_impl ConRon.Arena.structEtaCertWith]
def structEtaCertWithL : FunDecl :=
    lfn (mode, vis, d, a, b, wtb) locals (top, hh, t, i, c, us, f, p, ao, an, nf, T, us2, q, to, tn, r) {
  hh := call get_app_fn(a);
  if hh >> 28 != 3 { return 0 };
  t := (hh >> 27) & 1;
  i := hh & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[18 + t] <= i { abort };
  c := CREC.u64[i * 4 + t * 2];
  us := CREC.u64[i * 4 + t * 2 + 1];
  (f, p) := call env_find(c, vis);
  if f == 0 { return 0 };
  if EREC.u64[p] != 4 { return 0 };
  top := CTL.u64[136];
  (ao, an) := call get_app_args(a);
  nf := EREC.u64[p + 6];
  if an < nf || an - nf != EREC.u64[p + 5] {
    CTL.u64[136] := top;
    return 0
  };
  hh := call get_app_fn(wtb);
  if hh >> 28 != 3 {
    CTL.u64[136] := top;
    return 0
  };
  t := (hh >> 27) & 1;
  i := hh & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[18 + t] <= i { abort };
  T := CREC.u64[i * 4 + t * 2];
  us2 := CREC.u64[i * 4 + t * 2 + 1];
  (f, q) := call env_find(T, vis);
  if f == 0 || EREC.u64[q] != 3 {
    CTL.u64[136] := top;
    return 0
  };
  (to, tn) := call get_app_args(wtb);
  r := call struct_eta_cert_go(mode, vis, d, b, us, c, p, T, q, us2, ao, an, to, tn);
  CTL.u64[136] := top;
  return r
}

/-- con-ron: ConRon/Arena/Core.lean:1557-1566 ConRon.Arena.structEtaCert -/
@[l_impl ConRon.Arena.structEtaCert]
def structEtaCertL : FunDecl := lfn (mode, vis, d, a, b) locals (s, tb, wtb, r) {
  s := call eta_ctor_shape(vis, a);
  if s == 0 { return 0 };
  tb := call infer_io(mode, vis, d, b);
  wtb := call whnf(mode, vis, d, tb);
  r := call struct_eta_cert_with(mode, vis, d, a, b, wtb);
  return r
}

/-- con-ron: ConRon/Arena/Core.lean:1568-1597 ConRon.Arena.structUnitCert -/
@[l_impl ConRon.Arena.structUnitCert]
def structUnitCertL : FunDecl :=
    lfn (mode, vis, d, a, b) locals (top, ta, wta, hh, t, i, T, us2, f, q, to, tn, lo, uslen, rc, tb, wtb, r) {
  ta := call infer_io(mode, vis, d, a);
  wta := call whnf(mode, vis, d, ta);
  hh := call get_app_fn(wta);
  if hh >> 28 != 3 { return 0 };
  t := (hh >> 27) & 1;
  i := hh & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[18 + t] <= i { abort };
  T := CREC.u64[i * 4 + t * 2];
  us2 := CREC.u64[i * 4 + t * 2 + 1];
  (f, q) := call env_find(T, vis);
  if f == 0 { return 0 };
  if EREC.u64[q] != 3 { return 0 };
  top := CTL.u64[136];
  (to, tn) := call get_app_args(wta);
  CTL.u64[136] := top;
  (lo, uslen) := call ls_node(us2);
  rc := call reserved_contains(T);
  if EREC.u64[q + 9] != 0 && rc == 0 && tn == EREC.u64[q + 10] && uslen == EREC.u64[q + 3] {
    tb := call infer_io(mode, vis, d, b);
    wtb := call whnf(mode, vis, d, tb);
    if wtb >> 28 == 6 { return 0 };
    r := call defeq(mode, vis, d, wta, wtb);
    return r
  };
  return 0
}

/-- con-ron: ConRon/Arena/Core.lean:1627-1635 ConRon.Arena.stuckIrrel -/
@[l_impl ConRon.Arena.stuckIrrel]
def stuckIrrelL : FunDecl := lfn (mode, vis, d, a, b) locals (r) {
  r := call struct_eta_cert(mode, vis, d, a, b);
  if r != 0 { return 1 };
  r := call struct_eta_cert(mode, vis, d, b, a);
  if r != 0 { return 1 };
  r := call struct_unit_cert(mode, vis, d, a, b);
  if r != 0 { return 1 };
  r := call proof_irrel(mode, vis, d, a, b);
  return r
}

/-! ## The stuck comparison, the body -/

/-- `defeqStuck`'s two string-literal arms: the literal `lt` against an application with head
`fo`; `side` `0` when the literal is on the left (`a`). -/
-- con-ron: ConRon/Arena/Core.lean:3332-3401 ConRon.Arena.defeqStuck
@[l_impl ConRon.Arena.defeqStuck]
def stuckStrL : FunDecl :=
    lfn (mode, vis, d, a, b, side, lt, fo) locals (t, i, el, sl, ss, c, r) {
  t := (lt >> 27) & 1;
  i := lt & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[2 + t] <= i { abort };
  if REC.u64[i * 8 + t * 4] == 1 && fo >> 28 == 3 {
    t := (fo >> 27) & 1;
    i := fo & 134217727;
    if t != 0 && CTL.u64[1] == 0 { abort };
    if CTL.u64[18 + t] <= i { abort };
    el := call pin_word(52);
    sl := call pin_at(6);
    ss := call str_lit_supported(vis);
    if CREC.u64[i * 4 + t * 2] == sl && CREC.u64[i * 4 + t * 2 + 1] == el && ss != 0 {
      c := call str_lit_ctor(lt);
      if side == 0 { r := call defeq(mode, vis, d, c, b) } else { r := call defeq(mode, vis, d, a, c) };
      return r
    }
  };
  r := call stuck_irrel(mode, vis, d, a, b);
  return r
}

/-- `defeqStuck`'s application arm: spine-wise congruence. -/
-- con-ron: ConRon/Arena/Core.lean:3332-3401 ConRon.Arena.defeqStuck
@[l_impl ConRon.Arena.defeqStuck]
def stuckAppL : FunDecl := lfn (mode, vis, d, a, b) locals (top, ao, an, bo, bn, fa, fb, ok, r) {
  top := CTL.u64[136];
  (ao, an) := call get_app_args(a);
  (bo, bn) := call get_app_args(b);
  if an == bn {
    fa := call get_app_fn(a);
    fb := call get_app_fn(b);
    ok := call defeq(mode, vis, d, fa, fb);
    if ok != 0 {
      ok := call defeq_lst(mode, vis, d, ao, an, bo, bn);
      if ok != 0 {
        CTL.u64[136] := top;
        return 1
      }
    }
  };
  CTL.u64[136] := top;
  r := call stuck_irrel(mode, vis, d, a, b);
  return r
}

/-- con-ron: ConRon/Arena/Core.lean:3332-3401 ConRon.Arena.defeqStuck -/
@[l_impl ConRon.Arena.defeqStuck]
def defeqStuckL : FunDecl :=
    lfn (mode, vis, d, a, b) locals (ga, a1, a2, a3, gb, b1, b2, b3, z, ok, r) {
  (ga, a1, a2, a3) := call e_view(a);
  (gb, b1, b2, b3) := call e_view(b);
  if ga == 8 && gb == 4 {
    r := call stuck_str(mode, vis, d, a, b, 0, a, b1);
    return r
  };
  if ga == 4 && gb == 8 {
    r := call stuck_str(mode, vis, d, a, b, 1, b, a1);
    return r
  };
  if ga == 1 && gb == 1 {
    if a1 == b1 { return 1 };
    r := call stuck_irrel(mode, vis, d, a, b);
    return r
  };
  if ga == 3 && gb == 3 {
    if a1 == b1 {
      z := call lvls_eq_c(a2, b2);
      if z == 0 { abort };
      if z == 2 { return 1 }
    };
    r := call stuck_irrel(mode, vis, d, a, b);
    return r
  };
  if ga == 4 && gb == 4 {
    r := call stuck_app(mode, vis, d, a, b);
    return r
  };
  if ga == 5 {
    ok := call eta_cert(mode, vis, d, a1, a2, b);
    if ok != 0 { return 1 };
    r := call stuck_irrel(mode, vis, d, a, b);
    return r
  };
  if gb == 5 {
    ok := call eta_cert(mode, vis, d, b1, b2, a);
    if ok != 0 { return 1 };
    r := call stuck_irrel(mode, vis, d, a, b);
    return r
  };
  r := call stuck_irrel(mode, vis, d, a, b);
  return r
}

/-- The second half of `defeqBody`, from the lazy-delta loop's `.unknown` pair on. -/
-- con-ron: ConRon/Arena/Core.lean:3403-3441 ConRon.Arena.defeqBody
@[l_impl ConRon.Arena.defeqBody]
def defeqTailL : FunDecl := lfn (mode, vis, d, a1, b1) locals (pp, pa, pb, a2, b2, r) {
  pp := call defeq_proj_pair(mode, vis, d, a1, b1);
  if pp != 0 { return 1 };
  pa := call head_is_proj(a1);
  pb := call head_is_proj(b1);
  if pa == 0 && pb == 0 {
    r := call defeq_stuck(mode, vis, d, a1, b1);
    return r
  };
  a2 := call whnf_core(mode, 0, vis, d, a1);
  b2 := call whnf_core(mode, 0, vis, d, b1);
  if a2 == a1 && b2 == b1 {
    r := call defeq_stuck(mode, vis, d, a1, b1);
    return r
  };
  r := call defeq(mode, vis, d, a2, b2);
  return r
}

/-- con-ron: ConRon/Arena/Core.lean:3403-3441 ConRon.Arena.defeqBody -/
@[l_impl ConRon.Arena.defeqBody]
def defeqBodyL : FunDecl :=
    lfn (mode, vis, d, a, b) locals (bt, hf, sc, qf, qv, pi, a1, b1, lk, la, lb, r) {
  if a == b { return 1 };
  bt := call is_bool_true(b);
  hf := call has_fvar(a);
  sc := 0;
  if bt != 0 {
    if (mode >> 1) & 1 != 0 || hf == 0 { sc := call bool_true_shortcut(mode, vis, d, a) }
  };
  if sc != 0 { return 1 };
  (qf, qv) := call quick_defeq(mode, vis, d, a, b);
  if qf != 0 { return qv };
  pi := call prop_irrel(mode, vis, d, a, b);
  if pi != 0 { return 1 };
  a1 := call whnf_core(mode, 1, vis, d, a);
  b1 := call whnf_core(mode, 1, vis, d, b);
  (qf, qv) := call quick_defeq(mode, vis, d, a1, b1);
  if qf != 0 { return qv };
  (lk, la, lb) := call lazy_delta_reduction(mode, vis, d, a1, b1);
  if lk != 2 { return lk };
  r := call defeq_tail(mode, vis, d, la, lb);
  return r
}

/-- The functions of this file. -/
def defeqFns : Prog :=
  [("is_bool_true", isBoolTrueL), ("is_eager_reduce", isEagerReduceL), ("lit_eq", litEqL),
   ("io_neutral", ioNeutralL), ("unfoldable_head", unfoldableHeadL), ("head_hint", headHintL),
   ("hint_lt", hintLtL), ("same_const_heads", sameConstHeadsL), ("er_slice_eq", erSliceEqL),
   ("defeq_lst", defeqLstL), ("defeq_list_rev", defeqListRevL),
   ("bool_true_shortcut", boolTrueShortcutL), ("defeq_spine", defeqSpineL),
   ("defeq_no_fvars", defeqNoFvarsL), ("lazy_fold_ok", lazyFoldOkL), ("defeq_peel", defeqPeelL),
   ("defeq_binders", defeqBindersL), ("defeq_lams_inner", defeqLamsInnerL),
   ("defeq_lams", defeqLamsL), ("quick_defeq", quickDefeqL), ("is_nat_zero", isNatZeroL),
   ("nat_pred", natPredL), ("defeq_offset", defeqOffsetL), ("head_is_proj", headIsProjL),
   ("try_unfold_proj_app", tryUnfoldProjAppL), ("delta_quick", deltaQuickL),
   ("lds_left", ldsLeftL), ("lds_right", ldsRightL), ("lds_both", ldsBothL),
   ("lazy_delta_step", lazyDeltaStepL), ("lazy_delta_reduction", lazyDeltaReductionL),
   ("lazy_delta_proj_reduction", lazyDeltaProjReductionL), ("defeq_proj_pair", defeqProjPairL),
   ("prop_irrel", propIrrelL), ("eta_cert_ty", etaCertTyL), ("eta_cert_body", etaCertBodyL),
   ("eta_cert", etaCertL), ("eta_ctor_shape", etaCtorShapeL),
   ("struct_eta_cert_go", structEtaCertGoL), ("struct_eta_cert_with", structEtaCertWithL),
   ("struct_eta_cert", structEtaCertL), ("struct_unit_cert", structUnitCertL),
   ("stuck_irrel", stuckIrrelL), ("stuck_str", stuckStrL), ("stuck_app", stuckAppL),
   ("defeq_stuck", defeqStuckL), ("defeq_tail", defeqTailL), ("defeq_body", defeqBodyL)]

end L.Arena
