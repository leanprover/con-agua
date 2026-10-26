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
top back before it returns. Every twin `fail` is an `abort` (`fail R` where the twin
rejects or declines, `Arena/Reasons.lean`); the twin's
`2^62` loop fuels (`defeqLoopFuel`, `lamsFuel`) are uncounted `while` loops (each step costs L a
unit of its own fuel, which is below `2^62`), `peelFuel`
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

/-- Defaults for the twin's step results (the refinements' `AM.res`). -/
instance : Inhabited DeltaStepA := ⟨.unknown⟩
instance : Inhabited LazyResA := ⟨.verdict false⟩

/-! ## Small readers -/

/-- con-ron: ConRon/Arena/Core.lean:840-852 ConRon.Arena.isBoolTrue -/
@[l_impl ConRon.Arena.isBoolTrue]
def isBoolTrueL : FunDecl := lfn (h) locals (t, i, el, bt) {
  if h >> 28 != 3 { return 0 };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CONST⟨t⟩.count <= i { abort };
  el := call pin_word(52);
  if CONST⟨t, i⟩.us != el { return 0 };
  bt := call pin_at(30);
  return u64(CONST⟨t, i⟩.n == bt)
}

/-- con-ron: ConRon/Arena/Core.lean:854-874 ConRon.Arena.isEagerReduce -/
@[l_impl ConRon.Arena.isEagerReduce]
def isEagerReduceL : FunDecl := lfn (h) locals (t, i, f, g, er) {
  if h >> 28 != 4 { return 0 };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if APP⟨t⟩.count <= i { abort };
  f := APP⟨t, i⟩.f;
  if f >> 28 != 4 { return 0 };
  t := ⟦f⟧.tier;
  i := ⟦f⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if APP⟨t⟩.count <= i { abort };
  g := APP⟨t, i⟩.f;
  if g >> 28 != 3 { return 0 };
  t := ⟦g⟧.tier;
  i := ⟦g⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CONST⟨t⟩.count <= i { abort };
  er := call pin_at(50);
  return u64(CONST⟨t, i⟩.n == er)
}

/-- `lit_eq(a, b)`: two literal handles hold equal literals (the twin's `l₁ == l₂` on the two
views): the same kind, the same length, the same limbs/bytes (`limbs_eq` on the pool slices;
`Nat` literals are trimmed, so equal values have equal slices). -/
-- con-ron: ConRon/Arena/Core.lean:3064-3090 ConRon.Arena.quickDefEq
@[l_impl ConRon.Arena.quickDefEq]
def litEqL : FunDecl := lfn (a, b) locals (ta, xa, tb, xb, la, lb, r) {
  ta := ⟦a⟧.tier;
  xa := ⟦a⟧.idx;
  if ta != 0 && CTL.u64[1] == 0 { abort };
  if LIT⟨ta⟩.count <= xa { abort };
  tb := ⟦b⟧.tier;
  xb := ⟦b⟧.idx;
  if tb != 0 && CTL.u64[1] == 0 { abort };
  if LIT⟨tb⟩.count <= xb { abort };
  if LIT⟨ta, xa⟩.kind != LIT⟨tb, xb⟩.kind { return 0 };
  la := LIT⟨ta, xa⟩.l;
  lb := LIT⟨tb, xb⟩.l;
  if la != lb { return 0 };
  r := call limbs_eq(LIT⟨ta, xa⟩.o, LIT⟨tb, xb⟩.o, la);
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
  t := ⟦hh⟧.tier;
  i := ⟦hh⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CONST⟨t⟩.count <= i { abort };
  (f, p) := call env_find(CONST⟨t, i⟩.n, vis);
  if f == 0 { return 0 };
  if EREC.u64[p] != 1 { return 0 };
  (lo, l) := call ls_node(CONST⟨t, i⟩.us);
  return u64(l == EREC.u64[p + 3])
}

/-- con-ron: ConRon/Arena/Core.lean:418-429 ConRon.Arena.headHint -/
@[l_impl ConRon.Arena.headHint]
def headHintL : FunDecl := lfn (vis, e) locals (hh, t, i, f, p) {
  hh := call get_app_fn(e);
  if hh >> 28 != 3 { return (0, 0) };
  t := ⟦hh⟧.tier;
  i := ⟦hh⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CONST⟨t⟩.count <= i { abort };
  (f, p) := call env_find(CONST⟨t, i⟩.n, vis);
  if f == 0 { return (0, 0) };
  if EREC.u64[p] != 1 { return (0, 0) };
  return (EREC.u64[p + 6], EREC.u64[p + 7])
}

/-- `hint_lt(k1, h1, k2, h2)`: `ReducibilityHint.lt` on two `(kind, height)` hints (con-leche's
`Env.lean:206-211`, a pure function: `opaque < regular h < abbrev`). -/
-- con-ron: ConRon/Arena/Core.lean:3187-3244 ConRon.Arena.lazyDeltaStep
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
  t := ⟦a⟧.tier;
  i := ⟦a⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if APP⟨t⟩.count <= i { abort };
  f1 := APP⟨t, i⟩.f;
  if b >> 28 != 4 { return 0 };
  t := ⟦b⟧.tier;
  i := ⟦b⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if APP⟨t⟩.count <= i { abort };
  f2 := APP⟨t, i⟩.f;
  hh := call get_app_fn(f1);
  if hh >> 28 != 3 { return 0 };
  t := ⟦hh⟧.tier;
  i := ⟦hh⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CONST⟨t⟩.count <= i { abort };
  n1 := CONST⟨t, i⟩.n;
  hh := call get_app_fn(f2);
  if hh >> 28 != 3 { return 0 };
  t := ⟦hh⟧.tier;
  i := ⟦hh⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CONST⟨t⟩.count <= i { abort };
  return u64(n1 == CONST⟨t, i⟩.n)
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
-- con-ron: ConRon/Arena/Core.lean:1493-1539 ConRon.Arena.structEtaCertWith
@[l_impl ConRon.Arena.structEtaCertWith]
def erSliceEqL : FunDecl := lfn (o1, n1, o2, n2) locals (i) {
  if n1 != n2 { return 0 };
  i := 0;
  ⟪erSliceEqLoop⟫;
  return 1
}

/-! ## Spines compared pairwise -/

/-- `defeq_lst`'s loop (named, for its spec). -/
def defeqLstLoop : Stmt := lblk (mode, vis, d, ao, an, bo, bn, i, ok) {
  while 0 == 0 {
    if an <= i || bn <= i { return u64(an == bn) };
    ok := call defeq(mode, vis, d, SPN.u64[ao + i], SPN.u64[bo + i]);
    if ok == 0 { return 0 };
    i += 1
  }
}

/-- `defeq_lst(mode, vis, d, ao, an, bo, bn)`: the twin's `defEqList` on two stack slices, pair by
pair from the front **until either list ends** (a length mismatch is `false` only after the
common prefix compared equal, as the twin's list recursion). -/
-- con-ron: ConRon/Arena/Core.lean:1339-1346 ConRon.Arena.defEqList
@[l_impl ConRon.Arena.defEqList]
def defeqLstL : FunDecl := lfn (mode, vis, d, ao, an, bo, bn) locals (i, ok) {
  i := 0;
  ⟪defeqLstLoop⟫;
  abort
}

/-- `defeq_list_rev`'s loop (named, for its spec). -/
def defeqListRevLoop : Stmt := lblk (mode, vis, d, ao, an, bo, bn, i, j, ok) {
  while 0 == 0 {
    if i == 0 || j == 0 { return u64(an == bn) };
    i -= 1;
    j -= 1;
    ok := call defeq(mode, vis, d, SPN.u64[ao + i], SPN.u64[bo + j]);
    if ok == 0 { return 0 }
  }
}

/-- `defeq_list_rev(mode, vis, d, ao, an, bo, bn)`: `defEqList` on the two REVERSED slices (from
the last pair to the first), `defeqSpine`'s order. -/
-- con-ron: ConRon/Arena/Core.lean:2879-2905 ConRon.Arena.defeqSpine
@[l_impl ConRon.Arena.defeqSpine]
def defeqListRevL : FunDecl := lfn (mode, vis, d, ao, an, bo, bn) locals (i, j, ok) {
  i := an;
  j := bn;
  ⟪defeqListRevLoop⟫;
  abort
}

/-- con-ron: ConRon/Arena/Core.lean:2872-2877 ConRon.Arena.boolTrueShortcut -/
@[l_impl ConRon.Arena.boolTrueShortcut]
def boolTrueShortcutL : FunDecl := lfn (mode, vis, d, a) locals (w, r) {
  w := call whnf(mode, vis, d, a);
  r := call is_bool_true(w);
  return r
}

/-- The constant head of a spine: `(1, n, us)`, or `(0, 0, 0)` when the head is not a constant. -/
-- con-ron: ConRon/Arena/Core.lean:2879-2905 ConRon.Arena.defeqSpine
@[l_impl ConRon.Arena.defeqSpine]
def spineHeadL : FunDecl := lfn (e) locals (hh, g, n, us, x) {
  hh := call get_app_fn(e);
  if hh >> 28 != 3 { return (0, 0, 0) };
  (g, n, us, x) := call e_view(hh);
  return (1, n, us)
}

/-- `defeqSpine` past the two heads: the arguments, the names and lengths, the levels, the
reversed argument lists. -/
-- con-ron: ConRon/Arena/Core.lean:2879-2905 ConRon.Arena.defeqSpine
@[l_impl ConRon.Arena.defeqSpine]
def defeqSpine2L : FunDecl :=
    lfn (mode, vis, d, a, b, n, us, n2, us2) locals (top, ao, an, bo, bn, r) {
  top := CTL.u64[136];
  (ao, an) := call get_app_args(a);
  (bo, bn) := call get_app_args(b);
  r := call spine_cmp(mode, vis, d, n, us, n2, us2, ao, an, bo, bn);
  CTL.u64[136] := top;
  return r
}

/-- `defeqSpine`'s comparison on the argument slices (`some true` is any answer word `≥ 2`, as
`decO` reads it). -/
-- con-ron: ConRon/Arena/Core.lean:2879-2905 ConRon.Arena.defeqSpine
@[l_impl ConRon.Arena.defeqSpine]
def spineCmpL : FunDecl :=
    lfn (mode, vis, d, n, us, n2, us2, ao, an, bo, bn) locals (z, r) {
  if n == n2 && an == bn {
    z := call lvls_eq_c(us, us2);
    if 2 <= z {
      r := call defeq_list_rev(mode, vis, d, ao, an, bo, bn);
      return r
    }
  };
  return 0
}

/-- con-ron: ConRon/Arena/Core.lean:2879-2905 ConRon.Arena.defeqSpine -/
@[l_impl ConRon.Arena.defeqSpine]
def defeqSpineL : FunDecl :=
    lfn (mode, vis, d, a, b) locals (fa, n, us, fb, n2, us2, r) {
  (fa, n, us) := call spine_head(a);
  if fa == 0 { return 0 };
  (fb, n2, us2) := call spine_head(b);
  if fb == 0 { return 0 };
  r := call defeq_spine2(mode, vis, d, a, b, n, us, n2, us2);
  return r
}

/-- con-ron: ConRon/Arena/Core.lean:2907-2915 ConRon.Arena.defeqNoFvars -/
@[l_impl ConRon.Arena.defeqNoFvars]
def defeqNoFvarsL : FunDecl := lfn (a, b) locals (x, y) {
  x := call has_fvar(a);
  if x != 0 { return 0 };
  y := call has_fvar(b);
  return u64(y == 0)
}

/-- con-ron: ConRon/Arena/Core.lean:2917-2923 ConRon.Arena.lazyFoldOk -/
@[l_impl ConRon.Arena.lazyFoldOk]
def lazyFoldOkL : FunDecl := lfn (mode, a, b) locals (r) {
  if (mode >> 1) & 1 != 0 { return 1 };
  r := call defeq_no_fvars(a, b);
  return r
}

/-! ## The binder descents -/

/-- The batched descent's leaf: both residuals opened against the slice `(fo, k)`, compared at
depth `d + k`. -/
-- con-ron: ConRon/Arena/Core.lean:2935-2942 ConRon.Arena.defeqPeelLeaf
@[l_impl ConRon.Arena.defeqPeelLeaf]
def peelLeafL : FunDecl := lfn (mode, vis, d, a, b, k, fo) locals (o1, o2, dq) {
  o1 := call inst_list(a, fo, k, 0);
  o2 := call inst_list(b, fo, k, 0);
  dq := call defeq(mode, vis, d + k, o1, o2);
  return dq
}

/-- One peeled level's domains: `(dq, t2)`, the verdict and the opened second domain (the first,
when the raw domains are the same handle). -/
-- con-ron: ConRon/Arena/Core.lean:2944-3009 ConRon.Arena.defeqPeel
@[l_impl ConRon.Arena.defeqPeel]
def peelDomL : FunDecl := lfn (mode, vis, d, da, db, k, fo) locals (t1, t2, dq) {
  t1 := call inst_list(da, fo, k, 0);
  if da == db { return (1, t1) };
  t2 := call inst_list(db, fo, k, 0);
  dq := call defeq(mode, vis, d + k, t1, t2);
  return (dq, t2)
}

/-- One peeled level, the second binder's view and the domains: `(dq, t2, bb)`. -/
-- con-ron: ConRon/Arena/Core.lean:2944-3009 ConRon.Arena.defeqPeel
@[l_impl ConRon.Arena.defeqPeel]
def peelStep2L : FunDecl := lfn (mode, vis, d, da, b, k, fo) locals (g, db, bb, x, dq, t2) {
  (g, db, bb, x) := call e_view(b);
  (dq, t2) := call peel_dom(mode, vis, d, da, db, k, fo);
  return (dq, t2, bb)
}

/-- One peeled level: the two binders' views, then the domains: `(dq, t2, ba, bb)`. -/
-- con-ron: ConRon/Arena/Core.lean:2944-3009 ConRon.Arena.defeqPeel
@[l_impl ConRon.Arena.defeqPeel]
def peelStepL : FunDecl := lfn (mode, vis, d, a, b, k, fo) locals (g, da, ba, x, dq, t2, bb) {
  (g, da, ba, x) := call e_view(a);
  (dq, t2, bb) := call peel_step2(mode, vis, d, da, b, k, fo);
  return (dq, t2, ba, bb)
}

/-- The fresh free variable of a peeled level, pushed on the stack at `fo + k` (the top). -/
-- con-ron: ConRon/Arena/Core.lean:2944-3009 ConRon.Arena.defeqPeel
@[l_impl ConRon.Arena.defeqPeel]
def peelPushL : FunDecl := lfn (d, k, fo, t2) locals (fv) {
  fv := call intern_fvar(d + k, t2);
  if len(SPN.u64) <= fo + k { abort };
  SPN.u64[fo + k] := fv;
  CTL.u64[136] := fo + k + 1;
  return fv
}

/-- `defeq_peel`'s loop (named, for its spec). -/
def defeqPeelLoop : Stmt := lblk (mode, vis, d, peel, a, b, k, fo, dq, t2, ba, bb, fv) {
  while 0 == 0 {
    if a == b { return 1 };
    if peel == 0 || a >> 28 != 6 || b >> 28 != 6 {
      dq := call peel_leaf(mode, vis, d, a, b, k, fo);
      return dq
    };
    (dq, t2, ba, bb) := call peel_step(mode, vis, d, a, b, k, fo);
    if dq == 0 { return 0 };
    fv := call peel_push(d, k, fo, t2);
    k += 1;
    peel -= 1;
    a := ba;
    b := bb
  }
}

/-- The batched ∀ descent: `fvs` is the stack slice `(fo, k)` (`CTL[136] = fo + k`). -/
-- con-ron: ConRon/Arena/Core.lean:2944-3009 ConRon.Arena.defeqPeel
@[l_impl ConRon.Arena.defeqPeel]
def defeqPeelL : FunDecl :=
    lfn (mode, vis, d, peel, a, b, k, fo) locals (dq, t2, ba, bb, fv) {
  ⟪defeqPeelLoop⟫;
  abort
}

/-- con-ron: ConRon/Arena/Core.lean:3011-3020 ConRon.Arena.defeqBinders -/
@[l_impl ConRon.Arena.defeqBinders]
def defeqBindersL : FunDecl := lfn (mode, vis, d, ty1, body1, ty2, body2) locals (ok, fv, so, r) {
  ok := call defeq(mode, vis, d, ty1, ty2);
  if ok == 0 { return 0 };
  so := CTL.u64[136];
  fv := call peel_push(d, 0, so, ty2);
  r := call defeq_peel(mode, vis, d, 16777216, body1, body2, 1, so);
  CTL.u64[136] := so;
  return r
}

/-- con-ron: ConRon/Arena/Core.lean:3028-3039 ConRon.Arena.defeqLamsInner -/
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

/-- One λ level opened: the domains compared, the fresh free variable, both bodies instantiated:
`(ok, b1, b2)` (`(0, 0, 0)` when the domains differ). -/
-- con-ron: ConRon/Arena/Core.lean:3041-3062 ConRon.Arena.defeqLams
@[l_impl ConRon.Arena.defeqLams]
def lamsOpenL : FunDecl := lfn (mode, vis, d, ty1, body1, ty2, body2) locals (ok, b1, b2) {
  ok := call defeq(mode, vis, d, ty1, ty2);
  if ok == 0 { return (0, 0, 0) };
  (b1, b2) := call lams_inst(d, ty2, body1, body2);
  return (1, b1, b2)
}

/-- The fresh free variable `fvar d ty2`, both bodies instantiated with it: `(b1, b2)`. -/
-- con-ron: ConRon/Arena/Core.lean:3041-3062 ConRon.Arena.defeqLams
@[l_impl ConRon.Arena.defeqLams]
def lamsInstL : FunDecl := lfn (d, ty2, body1, body2) locals (fv, b1, b2) {
  fv := call intern_fvar(d, ty2);
  b1 := call inst1(body1, fv, 0);
  b2 := call inst1(body2, fv, 0);
  return (b1, b2)
}

/-- `lamPair?`: `(1, ty1, body1, ty2, body2)` when both handles are λs, else `(0, 0, 0, 0, 0)`. -/
-- con-ron: ConRon/Arena/ExprOps.lean:1266-1277 ConRon.Arena.lamPair?
@[l_impl ConRon.Arena.lamPair?]
def lamPairL : FunDecl := lfn (a, b) locals (g, x1, y1, x2, y2, z) {
  if a >> 28 != 5 || b >> 28 != 5 { return (0, 0, 0, 0, 0) };
  (g, x1, y1, z) := call e_view(a);
  (g, x2, y2, z) := call e_view(b);
  return (1, x1, y1, x2, y2)
}

/-- `defeq_lams`'s loop (named, for its spec). -/
def defeqLamsLoop : Stmt := lblk (mode, vis, d, ty1, body1, ty2, body2, ok, b1, b2, f, r) {
  while 0 == 0 {
    (ok, b1, b2) := call lams_open(mode, vis, d, ty1, body1, ty2, body2);
    if ok == 0 { return 0 };
    (f, ty1, body1, ty2, body2) := call lam_pair(b1, b2);
    if f == 0 {
      r := call defeq_lams_inner(mode, vis, d, b1, b2);
      return r
    };
    if b1 == b2 { return 1 };
    d += 1
  }
}

/-- The λ-telescope congruence; the twin's `lamsFuel` (`2^62`) is not counted (each pair costs L a unit
of its own fuel, which is below `2^62`):
an uncounted loop over the λ pairs. -/
-- con-ron: ConRon/Arena/Core.lean:3041-3062 ConRon.Arena.defeqLams
@[l_impl ConRon.Arena.defeqLams]
def defeqLamsL : FunDecl :=
    lfn (mode, vis, d, ty1, body1, ty2, body2) locals (ok, b1, b2, f, r) {
  ⟪defeqLamsLoop⟫;
  abort
}

/-! ## The easy cases, offsets -/

/-- `quickDefEq`'s sort pair: the two levels compared (`lvl_eq_c`; `none` aborts). -/
-- con-ron: ConRon/Arena/Core.lean:3064-3090 ConRon.Arena.quickDefEq
@[l_impl ConRon.Arena.quickDefEq]
def quickSortL : FunDecl := lfn (a, b) locals (g, u, v, x, y, z) {
  (g, u, x, y) := call e_view(a);
  (g, v, x, y) := call e_view(b);
  z := call lvl_eq_c(u, v);
  if z == 0 { fail R_RESOURCE_LIMIT_FUEL };
  return z - 1
}

/-- `quickDefEq`'s `∀` pair: binder congruence (`defeq_binders`). -/
-- con-ron: ConRon/Arena/Core.lean:3064-3090 ConRon.Arena.quickDefEq
@[l_impl ConRon.Arena.quickDefEq]
def quickForallL : FunDecl := lfn (mode, vis, d, a, b) locals (g, x1, y1, x2, y2, z, r) {
  (g, x1, y1, z) := call e_view(a);
  (g, x2, y2, z) := call e_view(b);
  r := call defeq_binders(mode, vis, d, x1, y1, x2, y2);
  return r
}

/-- `quickDefEq`'s `λ` pair: the telescope (`defeq_lams`). -/
-- con-ron: ConRon/Arena/Core.lean:3064-3090 ConRon.Arena.quickDefEq
@[l_impl ConRon.Arena.quickDefEq]
def quickLamL : FunDecl := lfn (mode, vis, d, a, b) locals (g, x1, y1, x2, y2, z, r) {
  (g, x1, y1, z) := call e_view(a);
  (g, x2, y2, z) := call e_view(b);
  r := call defeq_lams(mode, vis, d, x1, y1, x2, y2);
  return r
}

/-- con-ron: ConRon/Arena/Core.lean:3064-3090 ConRon.Arena.quickDefEq -/
@[l_impl ConRon.Arena.quickDefEq]
def quickDefeqL : FunDecl := lfn (mode, vis, d, a, b) locals (g, r) {
  if a == b { return (1, 1) };
  g := a >> 28;
  if g != b >> 28 { return (0, 0) };
  if g == 2 {
    r := call quick_sort(a, b);
    return (1, r)
  };
  if g == 8 {
    r := call lit_eq(a, b);
    return (1, r)
  };
  if g == 6 {
    r := call quick_forall(mode, vis, d, a, b);
    return (1, r)
  };
  if g == 5 {
    r := call quick_lam(mode, vis, d, a, b);
    return (1, r)
  };
  return (0, 0)
}

/-- con-ron: ConRon/Arena/Core.lean:3092-3106 ConRon.Arena.isNatZero -/
@[l_impl ConRon.Arena.isNatZero]
def isNatZeroL : FunDecl := lfn (e) locals (t, i, el, nz) {
  t := ⟦e⟧.tier;
  i := ⟦e⟧.idx;
  if e >> 28 == 8 {
    if t != 0 && CTL.u64[1] == 0 { abort };
    if LIT⟨t⟩.count <= i { abort };
    if LIT⟨t, i⟩.kind != 0 { return 0 };
    return u64(LIT⟨t, i⟩.l == 0)
  };
  if e >> 28 == 3 {
    if t != 0 && CTL.u64[1] == 0 { abort };
    if CONST⟨t⟩.count <= i { abort };
    el := call pin_word(52);
    nz := call pin_at(2);
    if CONST⟨t, i⟩.n == nz && CONST⟨t, i⟩.us == el { return 1 };
    return 0
  };
  return 0
}

/-- `nat_pred(e)`: `(1, x)` when `natPred? e = some x`, else `(0, 0)`. -/
-- con-ron: ConRon/Arena/Core.lean:3108-3130 ConRon.Arena.natPred?
@[l_impl ConRon.Arena.natPred?]
def natPredL : FunDecl := lfn (e) locals (t, i, l, f, x, el, ns) {
  t := ⟦e⟧.tier;
  i := ⟦e⟧.idx;
  if e >> 28 == 8 {
    if t != 0 && CTL.u64[1] == 0 { abort };
    if LIT⟨t⟩.count <= i { abort };
    if LIT⟨t, i⟩.kind != 0 { return (0, 0) };
    if LIT⟨t, i⟩.l == 0 { return (0, 0) };
    l := call nat_pred_lit(LIT⟨t, i⟩.o, LIT⟨t, i⟩.l);
    return (1, l)
  };
  if e >> 28 == 4 {
    if t != 0 && CTL.u64[1] == 0 { abort };
    if APP⟨t⟩.count <= i { abort };
    f := APP⟨t, i⟩.f;
    x := APP⟨t, i⟩.a;
    if f >> 28 != 3 { return (0, 0) };
    t := ⟦f⟧.tier;
    i := ⟦f⟧.idx;
    if t != 0 && CTL.u64[1] == 0 { abort };
    if CONST⟨t⟩.count <= i { abort };
    el := call pin_word(52);
    ns := call pin_at(3);
    if CONST⟨t, i⟩.n == ns && CONST⟨t, i⟩.us == el { return (1, x) };
    return (0, 0)
  };
  return (0, 0)
}

/-- con-ron: ConRon/Arena/Core.lean:3132-3150 ConRon.Arena.defeqOffset -/
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

/-- con-ron: ConRon/Arena/Core.lean:3152-3156 ConRon.Arena.headIsProj -/
@[l_impl ConRon.Arena.headIsProj]
def headIsProjL : FunDecl := lfn (e) locals (h) {
  h := call get_app_fn(e);
  return u64(h >> 28 == 9)
}

/-- `try_unfold_proj_app(mode, vis, d, e)`: `(1, e')` when `tryUnfoldProjApp` is `some e'`. -/
-- con-ron: ConRon/Arena/Core.lean:3158-3167 ConRon.Arena.tryUnfoldProjApp
@[l_impl ConRon.Arena.tryUnfoldProjApp]
def tryUnfoldProjAppL : FunDecl := lfn (mode, vis, d, e) locals (p, e2) {
  p := call head_is_proj(e);
  if p == 0 { return (0, 0) };
  e2 := call whnf_core(mode, 0, vis, d, e);
  if e2 == e { return (0, 0) };
  return (1, e2)
}

/-- con-ron: ConRon/Arena/Core.lean:3177-3185 ConRon.Arena.deltaQuick -/
@[l_impl ConRon.Arena.deltaQuick]
def deltaQuickL : FunDecl := lfn (mode, vis, d, a, b) locals (f, v) {
  (f, v) := call quick_defeq(mode, vis, d, a, b);
  if f == 0 { return (0, a, b) };
  if v != 0 { return (1, 0, 0) };
  return (2, 0, 0)
}

/-- One unfolding of the LEFT side: `unfoldDefinition`, the cheap `whnfCore`, `deltaQuick`
(`.unknown` when nothing unfolds). -/
-- con-ron: ConRon/Arena/Core.lean:3187-3244 ConRon.Arena.lazyDeltaStep
@[l_impl ConRon.Arena.lazyDeltaStep]
def ldsLeftL : FunDecl := lfn (mode, vis, d, a, b) locals (f, a2, a3, k, x, y) {
  (f, a2) := call unfold_definition(vis, a);
  if f == 0 { return (3, 0, 0) };
  a3 := call whnf_core(mode, 1, vis, d, a2);
  (k, x, y) := call delta_quick(mode, vis, d, a3, b);
  return (k, x, y)
}

/-- One unfolding of the RIGHT side. -/
-- con-ron: ConRon/Arena/Core.lean:3187-3244 ConRon.Arena.lazyDeltaStep
@[l_impl ConRon.Arena.lazyDeltaStep]
def ldsRightL : FunDecl := lfn (mode, vis, d, a, b) locals (f, b2, b3, k, x, y) {
  (f, b2) := call unfold_definition(vis, b);
  if f == 0 { return (3, 0, 0) };
  b3 := call whnf_core(mode, 1, vis, d, b2);
  (k, x, y) := call delta_quick(mode, vis, d, a, b3);
  return (k, x, y)
}

/-- Both sides unfolded, through the cheap `whnfCore`, then `deltaQuick` (`.unknown` unless both
unfold). -/
-- con-ron: ConRon/Arena/Core.lean:3187-3244 ConRon.Arena.lazyDeltaStep
@[l_impl ConRon.Arena.lazyDeltaStep]
def ldsUnfold2L : FunDecl := lfn (mode, vis, d, a, b) locals (fa, a2, fb, b2, a3, b3, k, x, y) {
  (fa, a2) := call unfold_definition(vis, a);
  (fb, b2) := call unfold_definition(vis, b);
  if fa == 0 || fb == 0 { return (3, 0, 0) };
  a3 := call whnf_core(mode, 1, vis, d, a2);
  b3 := call whnf_core(mode, 1, vis, d, b2);
  (k, x, y) := call delta_quick(mode, vis, d, a3, b3);
  return (k, x, y)
}

/-- Equal hints: the same-head shortcut at equal regular hints (a kind word `≥ 2` is regular, as
`head_hint`'s decoding reads it), else both unfolds. -/
-- con-ron: ConRon/Arena/Core.lean:3187-3244 ConRon.Arena.lazyDeltaStep
@[l_impl ConRon.Arena.lazyDeltaStep]
def ldsSameL : FunDecl := lfn (mode, vis, d, a, b, ka, ha, kb, hb) locals (sch, sp, k, x, y) {
  sch := call same_const_heads(a, b);
  sp := 0;
  if 2 <= ka && 2 <= kb && ha == hb && sch != 0 { sp := call defeq_spine(mode, vis, d, a, b) };
  if sp != 0 { return (1, 0, 0) };
  (k, x, y) := call lds_unfold2(mode, vis, d, a, b);
  return (k, x, y)
}

/-- The `true, true` arm of `lazyDeltaStep`: the hints, the greater side unfolded, else
`lds_same`. -/
-- con-ron: ConRon/Arena/Core.lean:3187-3244 ConRon.Arena.lazyDeltaStep
@[l_impl ConRon.Arena.lazyDeltaStep]
def ldsBothL : FunDecl := lfn (mode, vis, d, a, b) locals (ka, ha, kb, hb, lt, k, x, y) {
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
  (k, x, y) := call lds_same(mode, vis, d, a, b, ka, ha, kb, hb);
  return (k, x, y)
}

/-- con-ron: ConRon/Arena/Core.lean:3187-3244 ConRon.Arena.lazyDeltaStep -/
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

/-- The literal acceleration of one lazy-delta iteration: `(v, 0, 0)` when either side reduces
(the comparison restarted on the reduct; `v` normalised to `0`/`1`), `(3, 0, 0)` when neither
does. -/
-- con-ron: ConRon/Arena/Core.lean:3257-3285 ConRon.Arena.lazyDeltaReduction
@[l_impl ConRon.Arena.lazyDeltaReduction]
def lazyNatL : FunDecl := lfn (mode, vis, d, a, b) locals (fa, a2, fb, b2, v) {
  (fa, a2) := call reduce_nat(mode, vis, d, a);
  if fa != 0 {
    v := call defeq(mode, vis, d, a2, b);
    return (u64(v != 0), 0, 0)
  };
  (fb, b2) := call reduce_nat(mode, vis, d, b);
  if fb != 0 {
    v := call defeq(mode, vis, d, a, b2);
    return (u64(v != 0), 0, 0)
  };
  return (3, 0, 0)
}

/-- One lazy-delta iteration: `(k, x, y)` with `k` = `0` `.verdict false`, `1` `.verdict true`, `2`
`.unknown a b`, `3` continue with `(x, y)`. -/
-- con-ron: ConRon/Arena/Core.lean:3257-3285 ConRon.Arena.lazyDeltaReduction
@[l_impl ConRon.Arena.lazyDeltaReduction]
def lazyIterL : FunDecl := lfn (mode, vis, d, a, b) locals (of, ov, nf, k, x, y) {
  (of, ov) := call defeq_offset(mode, vis, d, a, b);
  if of != 0 { return (u64(ov != 0), 0, 0) };
  nf := call lazy_fold_ok(mode, a, b);
  if nf != 0 {
    (k, x, y) := call lazy_nat(mode, vis, d, a, b);
    if k != 3 { return (k, 0, 0) }
  };
  (k, x, y) := call lazy_delta_step(mode, vis, d, a, b);
  if k == 0 { return (3, x, y) };
  if k == 1 { return (1, 0, 0) };
  if k == 2 { return (0, 0, 0) };
  return (2, a, b)
}

/-- `lazy_delta_reduction`'s loop (named, for its spec). -/
def lazyDeltaLoop : Stmt := lblk (mode, vis, d, a, b, k, x, y) {
  while 0 == 0 {
    (k, x, y) := call lazy_iter(mode, vis, d, a, b);
    if k != 3 { return (k, x, y) };
    a := x;
    b := y
  }
}

/-- The lazy-delta loop on its uncounted `2^62` budget (`defeqLoopFuel`; each step costs L a unit of its own fuel, which
is below `2^62`). -/
-- con-ron: ConRon/Arena/Core.lean:3257-3285 ConRon.Arena.lazyDeltaReduction
@[l_impl ConRon.Arena.lazyDeltaReduction]
def lazyDeltaReductionL : FunDecl := lfn (mode, vis, d, a, b) locals (k, x, y) {
  ⟪lazyDeltaLoop⟫;
  abort
}

/-- The projection loop's exit on a verdict `k` (`1` equal, else the projections tried on both
sides; split off for the proofs). -/
-- con-ron: ConRon/Arena/Core.lean:3287-3307 ConRon.Arena.lazyDeltaProjReduction
@[l_impl ConRon.Arena.lazyDeltaProjReduction]
def ldprExitL : FunDecl := lfn (mode, vis, d, sn, i, a, b, k) locals (fx, px, fy, py, r) {
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
}

/-- The projection loop, named for its spec. -/
def ldprLoopB : Stmt := lblk (mode, vis, d, sn, i, a, b, k, x, y, r) {
  while 0 == 0 {
    (k, x, y) := call lazy_delta_step(mode, vis, d, a, b);
    if k != 0 {
      r := call ldpr_exit(mode, vis, d, sn, i, a, b, k);
      return r
    };
    a := x;
    b := y
  }
}

/-- The projection loop on its uncounted budget. -/
-- con-ron: ConRon/Arena/Core.lean:3287-3307 ConRon.Arena.lazyDeltaProjReduction
@[l_impl ConRon.Arena.lazyDeltaProjReduction]
def lazyDeltaProjReductionL : FunDecl :=
    lfn (mode, vis, d, sn, i, a, b) locals (k, x, y, r) {
  ⟪ldprLoopB⟫;
  abort
}

/-- Each test its own `if`, the second record's words loaded before the tests (the proof's
paths).
con-ron: ConRon/Arena/Core.lean:3309-3322 ConRon.Arena.defeqProjPair -/
@[l_impl ConRon.Arena.defeqProjPair]
def defeqProjPairL : FunDecl := lfn (mode, vis, d, a, b) locals (t, i, s, x1, x2, x3, y1, y2, y3, r) {
  if a >> 28 != 9 { return 0 };
  if b >> 28 != 9 { return 0 };
  t := ⟦a⟧.tier;
  i := ⟦a⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if PROJ⟨t⟩.count <= i { abort };
  x1 := PROJ⟨t, i⟩.n;
  x2 := PROJ⟨t, i⟩.i;
  x3 := PROJ⟨t, i⟩.e;
  s := ⟦b⟧.tier;
  i := ⟦b⟧.idx;
  if s != 0 && CTL.u64[1] == 0 { abort };
  if PROJ⟨s⟩.count <= i { abort };
  y1 := PROJ⟨s, i⟩.n;
  y2 := PROJ⟨s, i⟩.i;
  y3 := PROJ⟨s, i⟩.e;
  if x1 != y1 { return 0 };
  if x2 != y2 { return 0 };
  r := call lazy_delta_proj_reduction(mode, vis, d, x1, x2, x3, y3);
  return r
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
-- con-ron: ConRon/Arena/Core.lean:1600-1626 ConRon.Arena.etaCert
@[l_impl ConRon.Arena.etaCert]
def etaCertTyL : FunDecl := lfn (mode, vis, d, lhs, cod2, fv) locals (t1, t2, ok) {
  t1 := call infer(mode, vis, d + 1, lhs);
  t2 := call inst1(cod2, fv, 0);
  ok := call defeq(mode, vis, d + 1, t1, t2);
  return ok
}

/-- `etaCert` once the domains agree: the bodies at a fresh variable (split off for the
proofs). The depth capacity: the word `d + 1` must not wrap where the twin's `Nat` does not. -/
-- con-ron: ConRon/Arena/Core.lean:1600-1626 ConRon.Arena.etaCert
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

/-- con-ron: ConRon/Arena/Core.lean:1600-1626 ConRon.Arena.etaCert -/
@[l_impl ConRon.Arena.etaCert]
def etaCertL : FunDecl :=
    lfn (mode, vis, d, ty1, body1, b) locals (nt, tb, hh, t, i, ty2, cod2, ok) {
  nt := call io_neutral(b);
  if nt == 0 { return 0 };
  tb := call infer_io(mode, vis, d, b);
  hh := call whnf(mode, vis, d, tb);
  if hh >> 28 != 6 { return 0 };
  t := ⟦hh⟧.tier;
  i := ⟦hh⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if FORALL⟨t⟩.count <= i { abort };
  ty2 := FORALL⟨t, i⟩.ty;
  cod2 := FORALL⟨t, i⟩.b;
  ok := call defeq(mode, vis, d, ty2, ty1);
  if ok == 0 { return 0 };
  ok := call eta_cert_body(mode, vis, d, ty1, body1, b, cod2);
  return ok
}

/-- con-ron: ConRon/Arena/Core.lean:1541-1556 ConRon.Arena.etaCtorShape -/
@[l_impl ConRon.Arena.etaCtorShape]
def etaCtorShapeL : FunDecl := lfn (vis, a) locals (top, hh, t, i, f, p, ao, an, nf) {
  hh := call get_app_fn(a);
  if hh >> 28 != 3 { return 0 };
  t := ⟦hh⟧.tier;
  i := ⟦hh⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CONST⟨t⟩.count <= i { abort };
  (f, p) := call env_find(CONST⟨t, i⟩.n, vis);
  if f == 0 { return 0 };
  if EREC.u64[p] != 4 { return 0 };
  top := CTL.u64[136];
  (ao, an) := call get_app_args(a);
  CTL.u64[136] := top;
  nf := EREC.u64[p + 6];
  if an < nf { return 0 };
  return u64(an - nf == EREC.u64[p + 5])
}

/-- The η certificate's level comparison and the two spine comparisons (`ep` the parameters, `nf`
the fields; split off for the proofs). Leaves the projections' slice on the stack. -/
-- con-ron: ConRon/Arena/Core.lean:1493-1539 ConRon.Arena.structEtaCertWith
@[l_impl ConRon.Arena.structEtaCertWith]
def structEtaCertTailL : FunDecl :=
    lfn (mode, vis, d, b, us, T, us2, ao, an, to, tn, ep, nf) locals (z, tk, ok, po, pn) {
  z := call lvls_eq_c(us, us2);
  if z == 0 { fail R_RESOURCE_LIMIT_FUEL };
  if z == 1 { return 0 };
  tk := ep;
  if an < tk { tk := an };
  ok := call defeq_lst(mode, vis, d, ao, tk, to, tn);
  if ok == 0 { return 0 };
  (po, pn) := call eta_projs(T, b, nf);
  ok := call defeq_lst(mode, vis, d, ao + tk, an - tk, po, pn);
  return ok
}

/-- The η certificate's checks after the two heads are found (`c` the constructor's record `p`,
`T` the type's record `q`, the spines `(ao, an)`, `(to, tn)` on the stack). Every record word is
read before the first call, and the twin's pure tests (`er_slice_eq`, `reserved_contains`, the
level list's length) run before `tower_slots_all`: the twin's condition has no effect, so nothing
moves across an effect. -/
-- con-ron: ConRon/Arena/Core.lean:1493-1539 ConRon.Arena.structEtaCertWith
@[l_impl ConRon.Arena.structEtaCertWith]
def structEtaCertGoL : FunDecl :=
    lfn (mode, vis, d, b, us, c, p, T, q, us2, ao, an, to, tn)
    locals (eta, ec, ep, nf, lpn, lpo, cpo, cpn, lpe, r1, r2, lo, uslen, slots, r) {
  eta := EREC.u64[q + 5];
  ec := EREC.u64[q + 6];
  ep := EREC.u64[q + 7];
  nf := EREC.u64[q + 8];
  lpo := EREC.u64[q + 2];
  lpn := EREC.u64[q + 3];
  cpo := EREC.u64[p + 2];
  cpn := EREC.u64[p + 3];
  lpe := call er_slice_eq(cpo, cpn, lpo, lpn);
  r1 := call reserved_contains_w(T);
  r2 := call reserved_contains_w(c);
  (lo, uslen) := call ls_node(us2);
  slots := call tower_slots_all(vis, T, nf);
  if eta == 0 { return 0 };
  if ec != c { return 0 };
  if r1 != 0 { return 0 };
  if r2 != 0 { return 0 };
  if tn != ep { return 0 };
  if uslen != lpn { return 0 };
  if lpe == 0 { return 0 };
  if slots == 0 { return 0 };
  r := call struct_eta_cert_tail(mode, vis, d, b, us, T, us2, ao, an, to, tn, ep, nf);
  return r
}

/-- `structEtaCertWith` past the constructor's spine: the type's head and spine, then the keys
(split off for the proofs). Leaves its slices on the stack. -/
-- con-ron: ConRon/Arena/Core.lean:1493-1539 ConRon.Arena.structEtaCertWith
@[l_impl ConRon.Arena.structEtaCertWith]
def structEtaCertWtbL : FunDecl :=
    lfn (mode, vis, d, b, us, c, p, ao, an, wtb) locals (hh, t, i, T, us2, f, q, to, tn, r) {
  hh := call get_app_fn(wtb);
  if hh >> 28 != 3 { return 0 };
  t := ⟦hh⟧.tier;
  i := ⟦hh⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CONST⟨t⟩.count <= i { abort };
  T := CONST⟨t, i⟩.n;
  us2 := CONST⟨t, i⟩.us;
  (f, q) := call env_find(T, vis);
  if f == 0 { return 0 };
  if EREC.u64[q] != 3 { return 0 };
  (to, tn) := call get_app_args(wtb);
  r := call struct_eta_cert_go(mode, vis, d, b, us, c, p, T, q, us2, ao, an, to, tn);
  return r
}

/-- con-ron: ConRon/Arena/Core.lean:1493-1539 ConRon.Arena.structEtaCertWith -/
@[l_impl ConRon.Arena.structEtaCertWith]
def structEtaCertWithL : FunDecl :=
    lfn (mode, vis, d, a, b, wtb) locals (top, hh, t, i, c, us, f, p, ao, an, nf, r) {
  hh := call get_app_fn(a);
  if hh >> 28 != 3 { return 0 };
  t := ⟦hh⟧.tier;
  i := ⟦hh⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CONST⟨t⟩.count <= i { abort };
  c := CONST⟨t, i⟩.n;
  us := CONST⟨t, i⟩.us;
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
  r := call struct_eta_cert_wtb(mode, vis, d, b, us, c, p, ao, an, wtb);
  CTL.u64[136] := top;
  return r
}

/-- con-ron: ConRon/Arena/Core.lean:1558-1567 ConRon.Arena.structEtaCert -/
@[l_impl ConRon.Arena.structEtaCert]
def structEtaCertL : FunDecl := lfn (mode, vis, d, a, b) locals (s, tb, wtb, r) {
  s := call eta_ctor_shape(vis, a);
  if s == 0 { return 0 };
  tb := call infer_io(mode, vis, d, b);
  wtb := call whnf(mode, vis, d, tb);
  r := call struct_eta_cert_with(mode, vis, d, a, b, wtb);
  return r
}

/-- `structUnitCert` once the family is certified: `b`'s type against `wta` (split off for the
proofs). -/
-- con-ron: ConRon/Arena/Core.lean:1569-1598 ConRon.Arena.structUnitCert
@[l_impl ConRon.Arena.structUnitCert]
def structUnitTailL : FunDecl := lfn (mode, vis, d, b, wta) locals (tb, wtb, r) {
  tb := call infer_io(mode, vis, d, b);
  wtb := call whnf(mode, vis, d, tb);
  if wtb >> 28 == 6 { return 0 };
  r := call defeq(mode, vis, d, wta, wtb);
  return r
}

/-- `structUnitCert` past `a`'s type `wta`: its head, family and spine (split off for the proofs).
The record words are read before the first call after `env_find`, and the twin's pure tests
(`ls_node`, `reserved_contains`) run before the tests. -/
-- con-ron: ConRon/Arena/Core.lean:1569-1598 ConRon.Arena.structUnitCert
@[l_impl ConRon.Arena.structUnitCert]
def structUnitHeadL : FunDecl :=
    lfn (mode, vis, d, b, wta) locals (top, hh, t, i, T, us2, f, q, ul, up, lpn, to, tn, lo, uslen, rc, r) {
  hh := call get_app_fn(wta);
  if hh >> 28 != 3 { return 0 };
  t := ⟦hh⟧.tier;
  i := ⟦hh⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CONST⟨t⟩.count <= i { abort };
  T := CONST⟨t, i⟩.n;
  us2 := CONST⟨t, i⟩.us;
  (f, q) := call env_find(T, vis);
  if f == 0 { return 0 };
  if EREC.u64[q] != 3 { return 0 };
  ul := EREC.u64[q + 9];
  up := EREC.u64[q + 10];
  lpn := EREC.u64[q + 3];
  top := CTL.u64[136];
  (to, tn) := call get_app_args(wta);
  CTL.u64[136] := top;
  (lo, uslen) := call ls_node(us2);
  rc := call reserved_contains_w(T);
  if ul == 0 { return 0 };
  if rc != 0 { return 0 };
  if tn != up { return 0 };
  if uslen != lpn { return 0 };
  r := call struct_unit_tail(mode, vis, d, b, wta);
  return r
}

/-- con-ron: ConRon/Arena/Core.lean:1569-1598 ConRon.Arena.structUnitCert -/
@[l_impl ConRon.Arena.structUnitCert]
def structUnitCertL : FunDecl := lfn (mode, vis, d, a, b) locals (ta, wta, r) {
  ta := call infer_io(mode, vis, d, a);
  wta := call whnf(mode, vis, d, ta);
  r := call struct_unit_head(mode, vis, d, b, wta);
  return r
}

/-- con-ron: ConRon/Arena/Core.lean:1628-1636 ConRon.Arena.stuckIrrel -/
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
`fo`; `side` `0` when the literal is on the left (`a`). The head's record words are read before
the first call. -/
-- con-ron: ConRon/Arena/Core.lean:3324-3393 ConRon.Arena.defeqStuck
@[l_impl ConRon.Arena.defeqStuck]
def stuckStrL : FunDecl :=
    lfn (mode, vis, d, a, b, side, lt, fo) locals (t, i, co, uo, el, sl, ss, c, r) {
  t := ⟦lt⟧.tier;
  i := ⟦lt⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if LIT⟨t⟩.count <= i { abort };
  if LIT⟨t, i⟩.kind == 1 && fo >> 28 == 3 {
    t := ⟦fo⟧.tier;
    i := ⟦fo⟧.idx;
    if t != 0 && CTL.u64[1] == 0 { abort };
    if CONST⟨t⟩.count <= i { abort };
    co := CONST⟨t, i⟩.n;
    uo := CONST⟨t, i⟩.us;
    el := call pin_word(52);
    sl := call pin_at(6);
    ss := call str_lit_supported(vis);
    if co == sl && uo == el && ss != 0 {
      c := call str_lit_ctor(lt);
      if side == 0 { r := call defeq(mode, vis, d, c, b) } else { r := call defeq(mode, vis, d, a, c) };
      return r
    }
  };
  r := call stuck_irrel(mode, vis, d, a, b);
  return r
}

/-- `defeqStuck`'s application arm, its congruence (split off for the proofs): `1` when the heads
and the spines agree pairwise; the top put back. -/
-- con-ron: ConRon/Arena/Core.lean:3324-3393 ConRon.Arena.defeqStuck
@[l_impl ConRon.Arena.defeqStuck]
def stuckAppCongL : FunDecl := lfn (mode, vis, d, a, b) locals (top, ao, an, bo, bn, fa, fb, ok) {
  top := CTL.u64[136];
  (ao, an) := call get_app_args(a);
  (bo, bn) := call get_app_args(b);
  ok := 0;
  if an == bn {
    fa := call get_app_fn(a);
    fb := call get_app_fn(b);
    ok := call defeq(mode, vis, d, fa, fb);
    if ok != 0 { ok := call defeq_lst(mode, vis, d, ao, an, bo, bn) }
  };
  CTL.u64[136] := top;
  return ok
}

/-- `defeqStuck`'s application arm: spine-wise congruence, else the stuck fallbacks. -/
-- con-ron: ConRon/Arena/Core.lean:3324-3393 ConRon.Arena.defeqStuck
@[l_impl ConRon.Arena.defeqStuck]
def stuckAppL : FunDecl := lfn (mode, vis, d, a, b) locals (ok, r) {
  ok := call stuck_app_cong(mode, vis, d, a, b);
  if ok != 0 { return 1 };
  r := call stuck_irrel(mode, vis, d, a, b);
  return r
}

/-- `defeqStuck`'s free-variable, constant and λ arms and the fallback, by the two views' words
(split off for the proofs). -/
-- con-ron: ConRon/Arena/Core.lean:3324-3393 ConRon.Arena.defeqStuck
@[l_impl ConRon.Arena.defeqStuck]
def stuckRestL : FunDecl :=
    lfn (mode, vis, d, a, b, ga, a1, a2, gb, b1, b2) locals (z, ok, r) {
  if ga == 1 {
    if gb == 1 {
      if a1 == b1 { return 1 };
      r := call stuck_irrel(mode, vis, d, a, b);
      return r
    }
  };
  if ga == 3 {
    if gb == 3 {
      if a1 == b1 {
        z := call lvls_eq_c(a2, b2);
        if z == 0 { fail R_RESOURCE_LIMIT_FUEL };
        if z != 1 { return 1 }
      };
      r := call stuck_irrel(mode, vis, d, a, b);
      return r
    }
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

/-- The tags tested one at a time (no `&&` chains: the proof's paths); the twin's pairs are
disjoint, so grouping by `a`'s tag keeps its match order.
con-ron: ConRon/Arena/Core.lean:3324-3393 ConRon.Arena.defeqStuck -/
@[l_impl ConRon.Arena.defeqStuck]
def defeqStuckL : FunDecl :=
    lfn (mode, vis, d, a, b) locals (ga, a1, a2, a3, gb, b1, b2, b3, r) {
  (ga, a1, a2, a3) := call e_view(a);
  (gb, b1, b2, b3) := call e_view(b);
  if ga == 8 {
    if gb == 4 {
      r := call stuck_str(mode, vis, d, a, b, 0, a, b1);
      return r
    }
  };
  if ga == 4 {
    if gb == 8 {
      r := call stuck_str(mode, vis, d, a, b, 1, b, a1);
      return r
    };
    if gb == 4 {
      r := call stuck_app(mode, vis, d, a, b);
      return r
    }
  };
  r := call stuck_rest(mode, vis, d, a, b, ga, a1, a2, gb, b1, b2);
  return r
}

/-- The second half of `defeqBody`, from the lazy-delta loop's `.unknown` pair on. -/
-- con-ron: ConRon/Arena/Core.lean:3395-3433 ConRon.Arena.defeqBody
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

/-- A depth word `≥ 2^63` aborts (the binder descents below add to it, the twin's `Nat` does not
wrap); the lazy loop's verdict words `0`/`1` are tested one by one (`decLR`: any other is `.unknown`).
con-ron: ConRon/Arena/Core.lean:3395-3433 ConRon.Arena.defeqBody -/
@[l_impl ConRon.Arena.defeqBody]
def defeqBodyL : FunDecl :=
    lfn (mode, vis, d, a, b) locals (bt, hf, sc, qf, qv, pi, a1, b1, lk, la, lb, r) {
  if a == b { return 1 };
  if d >> 63 != 0 { abort };
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
  if lk == 0 { return 0 };
  if lk == 1 { return 1 };
  r := call defeq_tail(mode, vis, d, la, lb);
  return r
}

end L.Arena
