module

public import ConAgua.Arena.WhnfBase
public import ConAgua.Arena.Env

@[expose] public section

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
phase 2); from lane `whnf`: `inst_list`, `inst1`, `find_proj`, `str_lit_stored`,
`str_lit_ctor`.
-/

open ConRon.Arena


namespace L.Arena

/-- Defaults for the twin's step results (the refinements' `AM.res`). -/
instance : Inhabited DeltaStepA := ⟨.unknown⟩
instance : Inhabited LazyResA := ⟨.verdict false⟩

/-! ## Small readers -/

/-- con-ron: ConRon/Arena/Core.lean:884-896 ConRon.Arena.isBoolTrue -/
@[no_expose, l_impl ConRon.Arena.isBoolTrue]
def isBoolTrueL : FunDecl := lfn (h) locals (t, i, el, bt) {
  if ⟦h⟧.tag != 3 { return 0 };
  (t, i) := node CONST⟦h⟧;
  el := call pin_word(52);
  if CONST⟨t, i⟩.us != el { return 0 };
  bt := call pin_at(30);
  return u64(CONST⟨t, i⟩.n == bt)
}

/-- con-ron: ConRon/Arena/Core.lean:898-918 ConRon.Arena.isEagerReduce -/
@[no_expose, l_impl ConRon.Arena.isEagerReduce]
def isEagerReduceL : FunDecl := lfn (h) locals (t, i, f, g, er) {
  if ⟦h⟧.tag != 4 { return 0 };
  (t, i) := node APP⟦h⟧;
  f := APP⟨t, i⟩.f;
  if ⟦f⟧.tag != 4 { return 0 };
  (t, i) := node APP⟦f⟧;
  g := APP⟨t, i⟩.f;
  if ⟦g⟧.tag != 3 { return 0 };
  (t, i) := node CONST⟦g⟧;
  er := call pin_at(50);
  return u64(CONST⟨t, i⟩.n == er)
}

/-- `lit_eq(a, b)`: two literal handles hold equal literals (the twin's `l₁ == l₂` on the two
views): the same kind, the same length, the same limbs/bytes (`limbs_eq` on the pool slices;
`Nat` literals are trimmed, so equal values have equal slices). -/
-- con-ron: ConRon/Arena/Core.lean:3867-3893 ConRon.Arena.quickDefEq
@[no_expose, l_impl ConRon.Arena.quickDefEq]
def litEqL : FunDecl := lfn (a, b) locals (ta, xa, tb, xb, la, lb, r) {
  (ta, xa) := node LIT⟦a⟧;
  (tb, xb) := node LIT⟦b⟧;
  if LIT⟨ta, xa⟩.kind != LIT⟨tb, xb⟩.kind { return 0 };
  la := LIT⟨ta, xa⟩.l;
  lb := LIT⟨tb, xb⟩.l;
  if la != lb { return 0 };
  r := call limbs_eq(LIT⟨ta, xa⟩.o, LIT⟨tb, xb⟩.o, la);
  return r
}

/-- con-ron: ConRon/Arena/Core.lean:321-330 ConRon.Arena.ioNeutral -/
@[no_expose, l_impl ConRon.Arena.ioNeutral]
def ioNeutralL : FunDecl := lfn (e) locals (h, t) {
  h := call get_app_fn(e);
  t := ⟦h⟧.tag;
  if t == 5 || t == 7 || t == 0 { return 0 };
  return 1
}

/-- con-ron: ConRon/Arena/Core.lean:414-430 ConRon.Arena.unfoldableHead -/
@[no_expose, l_impl ConRon.Arena.unfoldableHead]
def unfoldableHeadL : FunDecl := lfn (vis, e) locals (hh, t, i, f, p, lo, l) {
  hh := call get_app_fn(e);
  if ⟦hh⟧.tag != 3 { return 0 };
  (t, i) := node CONST⟦hh⟧;
  (f, p) := call env_find(CONST⟨t, i⟩.n, vis);
  if f == 0 { return 0 };
  if EREC⦃p⦄ != 1 { return 0 };
  (lo, l) := call ls_node(CONST⟨t, i⟩.us);
  return u64(l == EREC⦃p + ⟪CI.cv + CV.lpsLen⟫⦄)
}

/-- con-ron: ConRon/Arena/Core.lean:432-443 ConRon.Arena.headHint -/
@[no_expose, l_impl ConRon.Arena.headHint]
def headHintL : FunDecl := lfn (vis, e) locals (hh, t, i, f, p) {
  hh := call get_app_fn(e);
  if ⟦hh⟧.tag != 3 { return (0, 0) };
  (t, i) := node CONST⟦hh⟧;
  (f, p) := call env_find(CONST⟨t, i⟩.n, vis);
  if f == 0 { return (0, 0) };
  if EREC⦃p⦄ != 1 { return (0, 0) };
  return (EREC⦃p + ⟪CI.defnHint⟫⦄, EREC⦃p + ⟪CI.defnHint + Hint.height⟫⦄)
}

/-- `hint_lt(k1, h1, k2, h2)`: `ReducibilityHint.lt` on two `(kind, height)` hints (con-leche's
`Env.lean:206-211`, a pure function: `opaque < regular h < abbrev`). -/
-- con-ron: ConRon/Arena/Core.lean:3990-4047 ConRon.Arena.lazyDeltaStep
@[no_expose, l_impl ConRon.Arena.lazyDeltaStep]
def hintLtL : FunDecl := lfn (k1, h1, k2, h2) locals () {
  if k2 == 0 { return 0 };
  if k1 == 1 { return 0 };
  if k1 == 0 { return 1 };
  if k2 == 1 { return 1 };
  return u64(h1 < h2)
}

/-- con-ron: ConRon/Arena/Core.lean:445-470 ConRon.Arena.sameConstHeads -/
@[no_expose, l_impl ConRon.Arena.sameConstHeads]
def sameConstHeadsL : FunDecl := lfn (a, b) locals (t, i, f1, f2, hh, n1) {
  if ⟦a⟧.tag != 4 { return 0 };
  (t, i) := node APP⟦a⟧;
  f1 := APP⟨t, i⟩.f;
  if ⟦b⟧.tag != 4 { return 0 };
  (t, i) := node APP⟦b⟧;
  f2 := APP⟨t, i⟩.f;
  hh := call get_app_fn(f1);
  if ⟦hh⟧.tag != 3 { return 0 };
  (t, i) := node CONST⟦hh⟧;
  n1 := CONST⟨t, i⟩.n;
  hh := call get_app_fn(f2);
  if ⟦hh⟧.tag != 3 { return 0 };
  (t, i) := node CONST⟦hh⟧;
  return u64(n1 == CONST⟨t, i⟩.n)
}

/-- `er_slice_eq`'s loop (named, for its spec). -/
def erSliceEqLoop : Stmt := lblk (o1, n1, o2, n2, i) {
  for i < n1 { if EREC⦃o1 + i⦄ != EREC⦃o2 + i⦄ { return 0 } }
}

/-- `er_slice_eq(o1, n1, o2, n2)`: two `EREC` slices of handles are the same list (the twin's
`cvc.levelParams = cvT.levelParams`). -/
-- con-ron: ConRon/Arena/Core.lean:1584-1633 ConRon.Arena.structEtaCertWith
@[no_expose, l_impl ConRon.Arena.structEtaCertWith]
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
-- con-ron: ConRon/Arena/Core.lean:1434-1441 ConRon.Arena.defEqList
@[no_expose, l_impl ConRon.Arena.defEqList]
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
-- con-ron: ConRon/Arena/Core.lean:3756-3782 ConRon.Arena.defeqSpine
@[no_expose, l_impl ConRon.Arena.defeqSpine]
def defeqListRevL : FunDecl := lfn (mode, vis, d, ao, an, bo, bn) locals (i, j, ok) {
  i := an;
  j := bn;
  ⟪defeqListRevLoop⟫;
  abort
}

/-- con-ron: ConRon/Arena/Core.lean:3749-3754 ConRon.Arena.boolTrueShortcut -/
@[no_expose, l_impl ConRon.Arena.boolTrueShortcut]
def boolTrueShortcutL : FunDecl := lfn (mode, vis, d, a) locals (w, r) {
  w := call whnf(mode, vis, d, a);
  r := call is_bool_true(w);
  return r
}

/-- The constant head of a spine: `(1, n, us)`, or `(0, 0, 0)` when the head is not a constant. -/
-- con-ron: ConRon/Arena/Core.lean:3756-3782 ConRon.Arena.defeqSpine
@[no_expose, l_impl ConRon.Arena.defeqSpine]
def spineHeadL : FunDecl := lfn (e) locals (hh, g, n, us, x) {
  hh := call get_app_fn(e);
  if ⟦hh⟧.tag != 3 { return (0, 0, 0) };
  (g, n, us, x) := call e_view(hh);
  return (1, n, us)
}

/-- `defeqSpine` past the two heads: the arguments, the names and lengths, the levels, the
reversed argument lists. -/
-- con-ron: ConRon/Arena/Core.lean:3756-3782 ConRon.Arena.defeqSpine
@[no_expose, l_impl ConRon.Arena.defeqSpine]
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
-- con-ron: ConRon/Arena/Core.lean:3756-3782 ConRon.Arena.defeqSpine
@[no_expose, l_impl ConRon.Arena.defeqSpine]
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

/-- con-ron: ConRon/Arena/Core.lean:3756-3782 ConRon.Arena.defeqSpine -/
@[no_expose, l_impl ConRon.Arena.defeqSpine]
def defeqSpineL : FunDecl :=
    lfn (mode, vis, d, a, b) locals (fa, n, us, fb, n2, us2, r) {
  (fa, n, us) := call spine_head(a);
  if fa == 0 { return 0 };
  (fb, n2, us2) := call spine_head(b);
  if fb == 0 { return 0 };
  r := call defeq_spine2(mode, vis, d, a, b, n, us, n2, us2);
  return r
}

/-- con-ron: ConRon/Arena/Core.lean:3784-3792 ConRon.Arena.defeqNoFvars -/
@[no_expose, l_impl ConRon.Arena.defeqNoFvars]
def defeqNoFvarsL : FunDecl := lfn (a, b) locals (x, y) {
  x := call has_fvar(a);
  if x != 0 { return 0 };
  y := call has_fvar(b);
  return u64(y == 0)
}

/-- con-ron: ConRon/Arena/Core.lean:3794-3800 ConRon.Arena.lazyFoldOk -/
@[no_expose, l_impl ConRon.Arena.lazyFoldOk]
def lazyFoldOkL : FunDecl := lfn (mode, a, b) locals (r) {
  if (mode >> 1) & 1 != 0 { return 1 };
  r := call defeq_no_fvars(a, b);
  return r
}

/-! ## The binder-telescope congruence -/

/-- One level's domains in `defeq_binders`: the same RAW domain handle is `1`; otherwise the left
domain, opened over the variables so far (the stack slice `(fo, k)`, push order) in one
`inst_list`, against the opened right one `dom2`. -/
-- con-ron: ConRon/Arena/Core.lean:3823-3833 ConRon.Arena.defeqDomain
@[no_expose, l_impl ConRon.Arena.defeqDomain]
def defeqDomainL : FunDecl := lfn (mode, vis, d, fo, k, ty1, ty2, dom2) locals (dom1, r) {
  if ty1 == ty2 { return 1 };
  dom1 := call inst_list(ty1, fo, k, 0);
  r := call defeq(mode, vis, d, dom1, dom2);
  return r
}

/-- The innermost level of `defeq_binders`: the opened bodies, and for two λ-telescopes (`lam`)
at the verified mode their FULL-grade types. -/
-- con-ron: ConRon/Arena/Core.lean:3810-3821 ConRon.Arena.defeqBindersInner
@[no_expose, l_impl ConRon.Arena.defeqBindersInner]
def defeqBindersInnerL : FunDecl := lfn (mode, vis, lam, d, b1, b2) locals (ok, t1, t2, r) {
  ok := call defeq(mode, vis, d + 1, b1, b2);
  if ok == 0 { return 0 };
  if lam != 0 && mode & 1 == 0 {
    t1 := call infer(mode, vis, d + 1, b1);
    t2 := call infer(mode, vis, d + 1, b2);
    r := call defeq(mode, vis, d + 1, t1, t2);
    return r
  };
  return 1
}

/-- `binderPair?`: `(1, ty1, body1, ty2, body2)` when both handles are λs (`lam ≠ 0`) or both ∀s
(`lam = 0`), else `(0, 0, 0, 0, 0)`. -/
-- con-ron: ConRon/Arena/ExprOps.lean:1271-1284 ConRon.Arena.binderPair?
@[no_expose, l_impl ConRon.Arena.binderPair?]
def binderPairL : FunDecl := lfn (lam, a, b) locals (t, g, x1, y1, x2, y2, z) {
  if lam != 0 { t := 5 } else { t := 6 };
  if ⟦a⟧.tag != t || ⟦b⟧.tag != t { return (0, 0, 0, 0, 0) };
  (g, x1, y1, z) := call e_view(a);
  (g, x2, y2, z) := call e_view(b);
  return (1, x1, y1, x2, y2)
}

/-- **Binder-telescope congruence**: two ∀-telescopes (`lam = 0`) or two λ-telescopes peeled
together while both bodies are binders of that kind, at the budget `fuel`. The bodies stay RAW:
the variables of the levels above are the stack slice `(fo, k)` in push order (the twin's `fvs`,
`CTL[136] = fo + k`), and every opening is one `inst_list` over it. Per level the right domain is
opened (`dom2`), the domains compared (`defeq_domain`), the variable `fvar d dom2` pushed; at the
innermost level both bodies are opened and compared (`defeq_binders_inner`). The depth capacity:
the word `d + 1` must not wrap where the twin's `Nat` does not. -/
-- con-ron: ConRon/Arena/Core.lean:3835-3865 ConRon.Arena.defeqBinders
@[no_expose, l_impl ConRon.Arena.defeqBinders]
def defeqBindersL : FunDecl := lfn (mode, vis, lam, fuel, d, fo, k, ty1, body1, ty2, body2)
    locals (dom2, ok, fv, f, x1, y1, x2, y2, b1, b2, r) {
  dom2 := call inst_list(ty2, fo, k, 0);
  ok := call defeq_domain(mode, vis, d, fo, k, ty1, ty2, dom2);
  if ok == 0 { return 0 };
  fv := call intern_fvar(d, dom2);
  if len(SPN.u64) <= fo + k { abort };
  SPN.u64[fo + k] := fv;
  CTL.u64[136] := fo + k + 1;
  if fuel != 0 {
    (f, x1, y1, x2, y2) := call binder_pair(lam, body1, body2);
    if f != 0 {
      if d + 1 == 0 { abort };
      r := call defeq_binders(mode, vis, lam, fuel - 1, d + 1, fo, k + 1, x1, y1, x2, y2);
      return r
    }
  };
  b1 := call inst_list(body1, fo, k + 1, 0);
  b2 := call inst_list(body2, fo, k + 1, 0);
  r := call defeq_binders_inner(mode, vis, lam, d, b1, b2);
  return r
}

/-! ## The easy cases, offsets -/

/-- `quickDefEq`'s sort pair: the two levels compared (`lvl_eq_c`; `none` aborts). -/
-- con-ron: ConRon/Arena/Core.lean:3867-3893 ConRon.Arena.quickDefEq
@[no_expose, l_impl ConRon.Arena.quickDefEq]
def quickSortL : FunDecl := lfn (a, b) locals (g, u, v, x, y, z) {
  (g, u, x, y) := call e_view(a);
  (g, v, x, y) := call e_view(b);
  z := call lvl_eq_c(u, v);
  if z == 0 { fail R_RESOURCE_LIMIT_FUEL };
  return z - 1
}

/-- `quickDefEq`'s `∀` (`lam = 0`) and `λ` (`lam = 1`) pairs: binder-telescope congruence
(`defeq_binders` at `bindersFuel`, `2^62`, from an empty variable slice at the stack top; the top
put back; a top beyond the stack array aborts, a defensive check). -/
-- con-ron: ConRon/Arena/Core.lean:3867-3893 ConRon.Arena.quickDefEq
@[no_expose, l_impl ConRon.Arena.quickDefEq]
def quickBindersL : FunDecl := lfn (mode, vis, lam, d, a, b) locals (g, x1, y1, x2, y2, z, so, r) {
  (g, x1, y1, z) := call e_view(a);
  (g, x2, y2, z) := call e_view(b);
  so := CTL.u64[136];
  if len(SPN.u64) < so { abort };
  r := call defeq_binders(mode, vis, lam, 4611686018427387904, d, so, 0, x1, y1, x2, y2);
  CTL.u64[136] := so;
  return r
}

/-- con-ron: ConRon/Arena/Core.lean:3867-3893 ConRon.Arena.quickDefEq -/
@[no_expose, l_impl ConRon.Arena.quickDefEq]
def quickDefeqL : FunDecl := lfn (mode, vis, d, a, b) locals (g, r) {
  if a == b { return (1, 1) };
  g := ⟦a⟧.tag;
  if g != ⟦b⟧.tag { return (0, 0) };
  if g == 2 {
    r := call quick_sort(a, b);
    return (1, r)
  };
  if g == 8 {
    r := call lit_eq(a, b);
    return (1, r)
  };
  if g == 6 {
    r := call quick_binders(mode, vis, 0, d, a, b);
    return (1, r)
  };
  if g == 5 {
    r := call quick_binders(mode, vis, 1, d, a, b);
    return (1, r)
  };
  return (0, 0)
}

/-- con-ron: ConRon/Arena/Core.lean:3895-3909 ConRon.Arena.isNatZero -/
@[no_expose, l_impl ConRon.Arena.isNatZero]
def isNatZeroL : FunDecl := lfn (e) locals (t, i, el, nz) {
  t := ⟦e⟧.tier;
  i := ⟦e⟧.idx;
  if ⟦e⟧.tag == 8 {
    if t != 0 && CTL.u64[1] == 0 { abort };
    if LIT⟨t⟩.count <= i { abort };
    if LIT⟨t, i⟩.kind != 0 { return 0 };
    return u64(LIT⟨t, i⟩.l == 0)
  };
  if ⟦e⟧.tag == 3 {
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
-- con-ron: ConRon/Arena/Core.lean:3911-3933 ConRon.Arena.natPred?
@[no_expose, l_impl ConRon.Arena.natPred?]
def natPredL : FunDecl := lfn (e) locals (t, i, l, f, x, el, ns) {
  t := ⟦e⟧.tier;
  i := ⟦e⟧.idx;
  if ⟦e⟧.tag == 8 {
    if t != 0 && CTL.u64[1] == 0 { abort };
    if LIT⟨t⟩.count <= i { abort };
    if LIT⟨t, i⟩.kind != 0 { return (0, 0) };
    if LIT⟨t, i⟩.l == 0 { return (0, 0) };
    l := call nat_pred_lit(LIT⟨t, i⟩.o, LIT⟨t, i⟩.l);
    return (1, l)
  };
  if ⟦e⟧.tag == 4 {
    if t != 0 && CTL.u64[1] == 0 { abort };
    i := ⟦e⟧.aidx;
    if APP⟨t⟩.count <= i { abort };
    f := APP⟨t, i⟩.f;
    x := APP⟨t, i⟩.a;
    if ⟦f⟧.tag != 3 { return (0, 0) };
    (t, i) := node CONST⟦f⟧;
    el := call pin_word(52);
    ns := call pin_at(3);
    if CONST⟨t, i⟩.n == ns && CONST⟨t, i⟩.us == el { return (1, x) };
    return (0, 0)
  };
  return (0, 0)
}

/-- con-ron: ConRon/Arena/Core.lean:3935-3953 ConRon.Arena.defeqOffset -/
@[no_expose, l_impl ConRon.Arena.defeqOffset]
def defeqOffsetL : FunDecl := lfn (mode, vis, d, a, b) locals (za, zb, fa, x, fb, y, ok) {
  za := call is_nat_zero(a);
  zb := call is_nat_zero(b);
  if za != 0 && zb != 0 { return (1, 1) };
  if ⟦a⟧.tag == 8 && ⟦b⟧.tag == 8 { return (0, 0) };
  (fa, x) := call nat_pred(a);
  if fa == 0 { return (0, 0) };
  (fb, y) := call nat_pred(b);
  if fb == 0 { return (0, 0) };
  ok := call defeq(mode, vis, d, x, y);
  return (1, ok)
}

/-! ## Lazy delta -/

/-- con-ron: ConRon/Arena/Core.lean:3955-3959 ConRon.Arena.headIsProj -/
@[no_expose, l_impl ConRon.Arena.headIsProj]
def headIsProjL : FunDecl := lfn (e) locals (h) {
  h := call get_app_fn(e);
  return u64(⟦h⟧.tag == 9)
}

/-- `try_unfold_proj_app(mode, vis, d, e)`: `(1, e')` when `tryUnfoldProjApp` is `some e'`. -/
-- con-ron: ConRon/Arena/Core.lean:3961-3970 ConRon.Arena.tryUnfoldProjApp
@[no_expose, l_impl ConRon.Arena.tryUnfoldProjApp]
def tryUnfoldProjAppL : FunDecl := lfn (mode, vis, d, e) locals (p, e2) {
  p := call head_is_proj(e);
  if p == 0 { return (0, 0) };
  e2 := call whnf_core(mode, 0, vis, d, e);
  if e2 == e { return (0, 0) };
  return (1, e2)
}

/-- con-ron: ConRon/Arena/Core.lean:3980-3988 ConRon.Arena.deltaQuick -/
@[no_expose, l_impl ConRon.Arena.deltaQuick]
def deltaQuickL : FunDecl := lfn (mode, vis, d, a, b) locals (f, v) {
  (f, v) := call quick_defeq(mode, vis, d, a, b);
  if f == 0 { return (0, a, b) };
  if v != 0 { return (1, 0, 0) };
  return (2, 0, 0)
}

/-- One unfolding of the LEFT side: `unfoldDefinition`, the cheap `whnfCore`, `deltaQuick`
(`.unknown` when nothing unfolds). -/
-- con-ron: ConRon/Arena/Core.lean:3990-4047 ConRon.Arena.lazyDeltaStep
@[no_expose, l_impl ConRon.Arena.lazyDeltaStep]
def ldsLeftL : FunDecl := lfn (mode, vis, d, a, b) locals (f, a2, a3, k, x, y) {
  (f, a2) := call unfold_definition(vis, a);
  if f == 0 { return (3, 0, 0) };
  a3 := call whnf_core(mode, 1, vis, d, a2);
  (k, x, y) := call delta_quick(mode, vis, d, a3, b);
  return (k, x, y)
}

/-- One unfolding of the RIGHT side. -/
-- con-ron: ConRon/Arena/Core.lean:3990-4047 ConRon.Arena.lazyDeltaStep
@[no_expose, l_impl ConRon.Arena.lazyDeltaStep]
def ldsRightL : FunDecl := lfn (mode, vis, d, a, b) locals (f, b2, b3, k, x, y) {
  (f, b2) := call unfold_definition(vis, b);
  if f == 0 { return (3, 0, 0) };
  b3 := call whnf_core(mode, 1, vis, d, b2);
  (k, x, y) := call delta_quick(mode, vis, d, a, b3);
  return (k, x, y)
}

/-- Both sides unfolded, through the cheap `whnfCore`, then `deltaQuick` (`.unknown` unless both
unfold). -/
-- con-ron: ConRon/Arena/Core.lean:3990-4047 ConRon.Arena.lazyDeltaStep
@[no_expose, l_impl ConRon.Arena.lazyDeltaStep]
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
-- con-ron: ConRon/Arena/Core.lean:3990-4047 ConRon.Arena.lazyDeltaStep
@[no_expose, l_impl ConRon.Arena.lazyDeltaStep]
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
-- con-ron: ConRon/Arena/Core.lean:3990-4047 ConRon.Arena.lazyDeltaStep
@[no_expose, l_impl ConRon.Arena.lazyDeltaStep]
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

/-- con-ron: ConRon/Arena/Core.lean:3990-4047 ConRon.Arena.lazyDeltaStep -/
@[no_expose, l_impl ConRon.Arena.lazyDeltaStep]
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
-- con-ron: ConRon/Arena/Core.lean:4060-4088 ConRon.Arena.lazyDeltaReduction
@[no_expose, l_impl ConRon.Arena.lazyDeltaReduction]
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
-- con-ron: ConRon/Arena/Core.lean:4060-4088 ConRon.Arena.lazyDeltaReduction
@[no_expose, l_impl ConRon.Arena.lazyDeltaReduction]
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
-- con-ron: ConRon/Arena/Core.lean:4060-4088 ConRon.Arena.lazyDeltaReduction
@[no_expose, l_impl ConRon.Arena.lazyDeltaReduction]
def lazyDeltaReductionL : FunDecl := lfn (mode, vis, d, a, b) locals (k, x, y) {
  ⟪lazyDeltaLoop⟫;
  abort
}

/-- The projection loop's exit on a verdict `k` (`1` equal, else the projections tried on both
sides; split off for the proofs). -/
-- con-ron: ConRon/Arena/Core.lean:4090-4110 ConRon.Arena.lazyDeltaProjReduction
@[no_expose, l_impl ConRon.Arena.lazyDeltaProjReduction]
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
-- con-ron: ConRon/Arena/Core.lean:4090-4110 ConRon.Arena.lazyDeltaProjReduction
@[no_expose, l_impl ConRon.Arena.lazyDeltaProjReduction]
def lazyDeltaProjReductionL : FunDecl :=
    lfn (mode, vis, d, sn, i, a, b) locals (k, x, y, r) {
  ⟪ldprLoopB⟫;
  abort
}

/-- Each test its own `if`, the second record's words loaded before the tests (the proof's
paths).
con-ron: ConRon/Arena/Core.lean:4112-4125 ConRon.Arena.defeqProjPair -/
@[no_expose, l_impl ConRon.Arena.defeqProjPair]
def defeqProjPairL : FunDecl := lfn (mode, vis, d, a, b) locals (t, i, s, x1, x2, x3, y1, y2, y3, r) {
  if ⟦a⟧.tag != 9 { return 0 };
  if ⟦b⟧.tag != 9 { return 0 };
  (t, i) := node PROJ⟦a⟧;
  x1 := PROJ⟨t, i⟩.n;
  x2 := PROJ⟨t, i⟩.i;
  x3 := PROJ⟨t, i⟩.e;
  (s, i) := node PROJ⟦b⟧;
  y1 := PROJ⟨s, i⟩.n;
  y2 := PROJ⟨s, i⟩.i;
  y3 := PROJ⟨s, i⟩.e;
  if x1 != y1 { return 0 };
  if x2 != y2 { return 0 };
  r := call lazy_delta_proj_reduction(mode, vis, d, x1, x2, x3, y3);
  return r
}

/-! ## Proof irrelevance, η, the stuck fallbacks -/

/-- con-ron: ConRon/Arena/Core.lean:1482-1513 ConRon.Arena.propIrrel -/
@[no_expose, l_impl ConRon.Arena.propIrrel]
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
-- con-ron: ConRon/Arena/Core.lean:1897-1923 ConRon.Arena.etaCert
@[no_expose, l_impl ConRon.Arena.etaCert]
def etaCertTyL : FunDecl := lfn (mode, vis, d, lhs, cod2, fv) locals (t1, t2, ok) {
  t1 := call infer(mode, vis, d + 1, lhs);
  t2 := call inst1(cod2, fv, 0);
  ok := call defeq(mode, vis, d + 1, t1, t2);
  return ok
}

/-- `etaCert` once the domains agree: the bodies at a fresh variable (split off for the
proofs). The depth capacity: the word `d + 1` must not wrap where the twin's `Nat` does not. -/
-- con-ron: ConRon/Arena/Core.lean:1897-1923 ConRon.Arena.etaCert
@[no_expose, l_impl ConRon.Arena.etaCert]
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

/-- con-ron: ConRon/Arena/Core.lean:1897-1923 ConRon.Arena.etaCert -/
@[no_expose, l_impl ConRon.Arena.etaCert]
def etaCertL : FunDecl :=
    lfn (mode, vis, d, ty1, body1, b) locals (nt, tb, hh, t, i, ty2, cod2, ok) {
  nt := call io_neutral(b);
  if nt == 0 { return 0 };
  tb := call infer_io(mode, vis, d, b);
  hh := call whnf(mode, vis, d, tb);
  if ⟦hh⟧.tag != 6 { return 0 };
  (t, i) := node FORALL⟦hh⟧;
  ty2 := FORALL⟨t, i⟩.ty;
  cod2 := FORALL⟨t, i⟩.b;
  ok := call defeq(mode, vis, d, ty2, ty1);
  if ok == 0 { return 0 };
  ok := call eta_cert_body(mode, vis, d, ty1, body1, b, cod2);
  return ok
}

/-- con-ron: ConRon/Arena/Core.lean:1635-1650 ConRon.Arena.etaCtorShape -/
@[no_expose, l_impl ConRon.Arena.etaCtorShape]
def etaCtorShapeL : FunDecl := lfn (vis, a) locals (top, hh, t, i, f, p, ao, an, nf) {
  hh := call get_app_fn(a);
  if ⟦hh⟧.tag != 3 { return 0 };
  (t, i) := node CONST⟦hh⟧;
  (f, p) := call env_find(CONST⟨t, i⟩.n, vis);
  if f == 0 { return 0 };
  if EREC⦃p⦄ != 4 { return 0 };
  top := CTL.u64[136];
  (ao, an) := call get_app_args(a);
  CTL.u64[136] := top;
  nf := EREC⦃p + ⟪CI.ctorNfields⟫⦄;
  if an < nf { return 0 };
  return u64(an - nf == EREC⦃p + ⟪CI.ctorNparams⟫⦄)
}

/-- The η certificate's level comparison and the two spine comparisons (`ep` the parameters, `nf`
the fields; split off for the proofs). Leaves the projections' slice on the stack. -/
-- con-ron: ConRon/Arena/Core.lean:1584-1633 ConRon.Arena.structEtaCertWith
@[no_expose, l_impl ConRon.Arena.structEtaCertWith]
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

/-- The η certificate's checks after the two heads and the family's projection table are found
(`c` the constructor's record `p`, `T` the type's record `q`, `tq` its table plus one, the spines
`(ao, an)`, `(to, tn)` on the stack): the table's constructor and parameter count, the level
list's length, the level parameters. Every record word is read before the first call, and the
twin's pure tests (`er_slice_eq`, the level list's length) run before the tests. -/
-- con-ron: ConRon/Arena/Core.lean:1584-1633 ConRon.Arena.structEtaCertWith
@[no_expose, l_impl ConRon.Arena.structEtaCertWith]
def structEtaCertGoL : FunDecl :=
    lfn (mode, vis, d, b, us, c, p, T, q, tq, us2, ao, an, to, tn)
    locals (eta, ec, ep, nf, lpn, lpo, cpo, cpn, lpe, lo, uslen, r) {
  eta := EREC⦃q + ⟪CI.indCaps + Caps.eta⟫⦄;
  ec := EREC⦃tq + ⟪ProjTbl.ctor - 1⟫⦄;
  ep := EREC⦃tq + ⟪ProjTbl.numParams - 1⟫⦄;
  nf := EREC⦃tq + ⟪ProjTbl.numFields - 1⟫⦄;
  lpo := EREC⦃q + ⟪CI.cv + CV.lpsOff⟫⦄;
  lpn := EREC⦃q + ⟪CI.cv + CV.lpsLen⟫⦄;
  cpo := EREC⦃p + ⟪CI.cv + CV.lpsOff⟫⦄;
  cpn := EREC⦃p + ⟪CI.cv + CV.lpsLen⟫⦄;
  lpe := call er_slice_eq(cpo, cpn, lpo, lpn);
  (lo, uslen) := call ls_node(us2);
  if eta == 0 { return 0 };
  if ec != c { return 0 };
  if tn != ep { return 0 };
  if uslen != lpn { return 0 };
  if lpe == 0 { return 0 };
  r := call struct_eta_cert_tail(mode, vis, d, b, us, T, us2, ao, an, to, tn, ep, nf);
  return r
}

/-- `structEtaCertWith` past the constructor's spine: the type's head, its family's projection
table (none: `false`) and spine, then the keys (split off for the proofs). Leaves its slices on
the stack. -/
-- con-ron: ConRon/Arena/Core.lean:1584-1633 ConRon.Arena.structEtaCertWith
@[no_expose, l_impl ConRon.Arena.structEtaCertWith]
def structEtaCertWtbL : FunDecl :=
    lfn (mode, vis, d, b, us, c, p, ao, an, wtb) locals (hh, t, i, T, us2, f, q, tq, to, tn, r) {
  hh := call get_app_fn(wtb);
  if ⟦hh⟧.tag != 3 { return 0 };
  (t, i) := node CONST⟦hh⟧;
  T := CONST⟨t, i⟩.n;
  us2 := CONST⟨t, i⟩.us;
  (f, q) := call env_find(T, vis);
  if f == 0 { return 0 };
  if EREC⦃q⦄ != 3 { return 0 };
  tq := call find_table(vis, T);
  if tq == 0 { return 0 };
  (to, tn) := call get_app_args(wtb);
  r := call struct_eta_cert_go(mode, vis, d, b, us, c, p, T, q, tq, us2, ao, an, to, tn);
  return r
}

/-- con-ron: ConRon/Arena/Core.lean:1584-1633 ConRon.Arena.structEtaCertWith -/
@[no_expose, l_impl ConRon.Arena.structEtaCertWith]
def structEtaCertWithL : FunDecl :=
    lfn (mode, vis, d, a, b, wtb) locals (top, hh, t, i, c, us, f, p, ao, an, nf, r) {
  hh := call get_app_fn(a);
  if ⟦hh⟧.tag != 3 { return 0 };
  (t, i) := node CONST⟦hh⟧;
  c := CONST⟨t, i⟩.n;
  us := CONST⟨t, i⟩.us;
  (f, p) := call env_find(c, vis);
  if f == 0 { return 0 };
  if EREC⦃p⦄ != 4 { return 0 };
  top := CTL.u64[136];
  (ao, an) := call get_app_args(a);
  nf := EREC⦃p + ⟪CI.ctorNfields⟫⦄;
  if an < nf || an - nf != EREC⦃p + ⟪CI.ctorNparams⟫⦄ {
    CTL.u64[136] := top;
    return 0
  };
  r := call struct_eta_cert_wtb(mode, vis, d, b, us, c, p, ao, an, wtb);
  CTL.u64[136] := top;
  return r
}

/-- The family half of `etaCtorPartial`: the constructor's family (its record's `induct`, `T`) is a
stored η family whose projection table's constructor is `c`. One lookup, no walk; the `eta` word
is read before `find_table`. -/
-- con-ron: ConRon/Arena/Core.lean:1652-1663 ConRon.Arena.etaCtorPartialFam
@[no_expose, l_impl ConRon.Arena.etaCtorPartialFam]
def etaCtorPartialFamL : FunDecl := lfn (vis, c, T) locals (f, q, eta, tq) {
  (f, q) := call env_find(T, vis);
  if f == 0 { return 0 };
  if EREC⦃q⦄ != 3 { return 0 };
  eta := EREC⦃q + ⟪CI.indCaps + Caps.eta⟫⦄;
  tq := call find_table(vis, T);
  if tq == 0 { return 0 };
  if eta == 0 { return 0 };
  return u64(EREC⦃tq + ⟪ProjTbl.ctor - 1⟫⦄ == c)
}

/-- **A partially applied η constructor**: `(1, k)`, `k > 0` the arguments `a`'s constructor head
lacks, or `(0, 0)`. The record words are read before the first call after `env_find`; the stack
top is put back after the spine is counted. The sum of the constructor's counts must fit a word
(a capacity). -/
-- con-ron: ConRon/Arena/Core.lean:1665-1686 ConRon.Arena.etaCtorPartial
@[no_expose, l_impl ConRon.Arena.etaCtorPartial]
def etaCtorPartialL : FunDecl := lfn (vis, a) locals (hh, t, i, c, f, p, np, nf, T, top, ao, an, ok) {
  hh := call get_app_fn(a);
  if ⟦hh⟧.tag != 3 { return (0, 0) };
  (t, i) := node CONST⟦hh⟧;
  c := CONST⟨t, i⟩.n;
  (f, p) := call env_find(c, vis);
  if f == 0 { return (0, 0) };
  if EREC⦃p⦄ != 4 { return (0, 0) };
  np := EREC⦃p + ⟪CI.ctorNparams⟫⦄;
  nf := EREC⦃p + ⟪CI.ctorNfields⟫⦄;
  T := EREC⦃p + ⟪CI.ctorInduct⟫⦄;
  if np + nf < np { abort };
  top := CTL.u64[136];
  (ao, an) := call get_app_args(a);
  CTL.u64[136] := top;
  if np + nf <= an { return (0, 0) };
  ok := call eta_ctor_partial_fam(vis, c, T);
  if ok == 0 { return (0, 0) };
  return (1, np + nf - an)
}

/-- The body of structure η at a fully applied constructor, past the shape gate: `b`'s io-inferred
type, head-normalised, and the certificate against it. -/
-- con-ron: ConRon/Arena/Core.lean:1688-1697 ConRon.Arena.structEtaFullAt
@[no_expose, l_impl ConRon.Arena.structEtaFullAt]
def structEtaFullAtL : FunDecl := lfn (mode, vis, d, a, b) locals (tb, wtb, r) {
  tb := call infer_io(mode, vis, d, b);
  wtb := call whnf(mode, vis, d, tb);
  r := call struct_eta_cert_with(mode, vis, d, a, b, wtb);
  return r
}

/-- Structure η at a fully applied constructor: the shape gate first. -/
-- con-ron: ConRon/Arena/Core.lean:1699-1706 ConRon.Arena.structEtaFull
@[no_expose, l_impl ConRon.Arena.structEtaFull]
def structEtaFullL : FunDecl := lfn (mode, vis, d, a, b) locals (s, r) {
  s := call eta_ctor_shape(vis, a);
  if s == 0 { return 0 };
  r := call struct_eta_full_at(mode, vis, d, a, b);
  return r
}

/-- **The η-expansion of a partially applied constructor**: both sides applied to a fresh variable
per missing argument along `ta` (read syntactically), then `struct_eta_full`. The depth capacity:
the word `d + 1` must not wrap where the twin's `Nat` does not. -/
-- con-ron: ConRon/Arena/Core.lean:1708-1726 ConRon.Arena.structEtaExpand
@[no_expose, l_impl ConRon.Arena.structEtaExpand]
def structEtaExpandL : FunDecl := lfn (mode, vis, k, d, a, b, ta)
    locals (t, i, dom, body, fv, a2, b2, body2, r) {
  if k == 0 {
    r := call struct_eta_full(mode, vis, d, a, b);
    return r
  };
  if ⟦ta⟧.tag != 6 { return 0 };
  if d + 1 == 0 { abort };
  (t, i) := node FORALL⟦ta⟧;
  dom := FORALL⟨t, i⟩.ty;
  body := FORALL⟨t, i⟩.b;
  fv := call intern_fvar(d, dom);
  a2 := call mk_app(a, fv);
  b2 := call mk_app(b, fv);
  body2 := call inst1(body, fv, 0);
  r := call struct_eta_expand(mode, vis, k - 1, d + 1, a2, b2, body2);
  return r
}

/-- The partial-constructor arm of `structEtaCert`, at `k` missing arguments: `b` neutral, the two
io-inferred types compared, then both sides η-expanded. -/
-- con-ron: ConRon/Arena/Core.lean:1728-1740 ConRon.Arena.structEtaCertPartial
@[no_expose, l_impl ConRon.Arena.structEtaCertPartial]
def structEtaCertPartialL : FunDecl := lfn (mode, vis, d, k, a, b) locals (nt, ta, tb, ok, r) {
  nt := call io_neutral(b);
  if nt == 0 { return 0 };
  ta := call infer_io(mode, vis, d, a);
  tb := call infer_io(mode, vis, d, b);
  ok := call defeq(mode, vis, d, tb, ta);
  if ok == 0 { return 0 };
  r := call struct_eta_expand(mode, vis, k, d, a, b, ta);
  return r
}

/-- Structural η: `a` a fully applied constructor of an η family (the shape gate read once) or a
partially applied one (`eta_ctor_partial`). -/
-- con-ron: ConRon/Arena/Core.lean:1742-1753 ConRon.Arena.structEtaCert
@[no_expose, l_impl ConRon.Arena.structEtaCert]
def structEtaCertL : FunDecl := lfn (mode, vis, d, a, b) locals (s, f, k, r) {
  s := call eta_ctor_shape(vis, a);
  if s != 0 {
    r := call struct_eta_full_at(mode, vis, d, a, b);
    return r
  };
  (f, k) := call eta_ctor_partial(vis, a);
  if f == 0 { return 0 };
  r := call struct_eta_cert_partial(mode, vis, d, k, a, b);
  return r
}

/-- **Is a proposition**: `T`'s io-inferred type head-normalises to a sort equivalent to `Prop`
(the zero level is pin word 53; `lvl_eq_c`'s `0` is the twin's fuel failure). -/
-- con-ron: ConRon/Arena/Core.lean:1755-1768 ConRon.Arena.isPropType
@[no_expose, l_impl ConRon.Arena.isPropType]
def isPropTypeL : FunDecl := lfn (mode, vis, d, T) locals (tt, w, g, u, x, y, z, e) {
  tt := call infer_io(mode, vis, d, T);
  w := call whnf(mode, vis, d, tt);
  if ⟦w⟧.tag != 2 { return 0 };
  (g, u, x, y) := call e_view(w);
  z := call pin_word(53);
  e := call lvl_eq_c(u, z);
  if e == 0 { fail R_RESOURCE_LIMIT_FUEL };
  return e - 1
}

/-- **The field loop of `is_unit_like`**: each of the `n` field binders of `tele` has a
proposition or a unit-like type (`unit_like_loop` at the budget `ulf`, the twin's `ul`), the field
opened at a fresh variable before the next. -/
-- con-ron: ConRon/Arena/Core.lean:1770-1793 ConRon.Arena.unitLikeFields
@[no_expose, l_impl ConRon.Arena.unitLikeFields]
def unitLikeFieldsL : FunDecl := lfn (mode, vis, ulf, n, d, tele)
    locals (t, i, dom, body, pr, u, fv, body2, r) {
  if n == 0 { return 1 };
  if ⟦tele⟧.tag != 6 { return 0 };
  if d + 1 == 0 { abort };
  (t, i) := node FORALL⟦tele⟧;
  dom := FORALL⟨t, i⟩.ty;
  body := FORALL⟨t, i⟩.b;
  pr := call is_prop_type(mode, vis, d, dom);
  if pr == 0 {
    u := call unit_like_loop(mode, vis, ulf, d, dom);
    if u == 0 { return 0 }
  };
  fv := call intern_fvar(d, dom);
  body2 := call inst1(body, fv, 0);
  r := call unit_like_fields(mode, vis, ulf, n - 1, d + 1, body2);
  return r
}

/-- The field telescope of an instance at its family's table: the table's constructor `tctor`,
stored, its type at the levels `us`, its `nP` parameter binders dropped and instantiated with the
slice `(to, tn)`: `(1, tele, nF)`, or `(0, 0, 0)`. -/
-- con-ron: ConRon/Arena/Core.lean:1800-1816 ConRon.Arena.unitLikeShapeAt
@[no_expose, l_impl ConRon.Arena.unitLikeShapeAt]
def unitLikeShapeAtL : FunDecl := lfn (vis, us, to, tn, tctor, nP, nF) locals (f, p, cty, ok, body, tele) {
  (f, p) := call env_find(tctor, vis);
  if f == 0 { return (0, 0, 0) };
  if EREC⦃p⦄ != 4 { return (0, 0, 0) };
  cty := call inst_lp(EREC⦃p + ⟪CI.cv + CV.lpsOff⟫⦄, EREC⦃p + ⟪CI.cv + CV.lpsLen⟫⦄, us, EREC⦃p + ⟪CI.cv + CV.type⟫⦄);
  (ok, body) := call peel_pis(nP, cty);
  if ok == 0 { return (0, 0, 0) };
  tele := call inst_list(body, to, tn, 0);
  return (1, tele, nF)
}

/-- **The shape of an instance in `is_unit_like`**: `w` an instance of a stored η family at the
family's level count and its table's parameter count: `(1, tele, n)` its constructor's field
telescope and field count, or `(0, 0, 0)`. The stack top is put back. -/
-- con-ron: ConRon/Arena/Core.lean:1818-1845 ConRon.Arena.unitLikeShape
@[no_expose, l_impl ConRon.Arena.unitLikeShape]
def unitLikeShapeL : FunDecl := lfn (vis, w)
    locals (hh, t, i, S, us, f, q, eta, lpn, lo, usl, tq, np, tc, nf, top, to, tn, g, tele, n) {
  hh := call get_app_fn(w);
  if ⟦hh⟧.tag != 3 { return (0, 0, 0) };
  (t, i) := node CONST⟦hh⟧;
  S := CONST⟨t, i⟩.n;
  us := CONST⟨t, i⟩.us;
  (f, q) := call env_find(S, vis);
  if f == 0 { return (0, 0, 0) };
  if EREC⦃q⦄ != 3 { return (0, 0, 0) };
  eta := EREC⦃q + ⟪CI.indCaps + Caps.eta⟫⦄;
  lpn := EREC⦃q + ⟪CI.cv + CV.lpsLen⟫⦄;
  (lo, usl) := call ls_node(us);
  if eta == 0 { return (0, 0, 0) };
  if usl != lpn { return (0, 0, 0) };
  tq := call find_table(vis, S);
  if tq == 0 { return (0, 0, 0) };
  np := EREC⦃tq + ⟪ProjTbl.numParams - 1⟫⦄;
  tc := EREC⦃tq + ⟪ProjTbl.ctor - 1⟫⦄;
  nf := EREC⦃tq + ⟪ProjTbl.numFields - 1⟫⦄;
  top := CTL.u64[136];
  (to, tn) := call get_app_args(w);
  if tn != np {
    CTL.u64[136] := top;
    return (0, 0, 0)
  };
  (g, tele, n) := call unit_like_shape_at(vis, us, to, tn, tc, np, nf);
  CTL.u64[136] := top;
  return (g, tele, n)
}

/-- **The structure arm of `is_unit_like`**: `w` an instance of an η family every field of whose
constructor is a proposition or unit-like (`unit_like_loop` at `ulf`). -/
-- con-ron: ConRon/Arena/Core.lean:1847-1856 ConRon.Arena.unitLikeStruct
@[no_expose, l_impl ConRon.Arena.unitLikeStruct]
def unitLikeStructL : FunDecl := lfn (mode, vis, ulf, d, w) locals (f, tele, n, r) {
  (f, tele, n) := call unit_like_shape(vis, w);
  if f == 0 { return 0 };
  r := call unit_like_fields(mode, vis, ulf, n, d, tele);
  return r
}

/-- **Is a type unit-like** (`is_unit_like`), at the budget `fuel` (`unitLikeFuel`, `2^62`):
its head normal form a ∀ whose codomain, opened at a fresh variable, is unit-like, or an instance
of an η family (`unit_like_struct`). -/
-- con-ron: ConRon/Arena/Core.lean:1858-1875 ConRon.Arena.unitLikeLoop
@[no_expose, l_impl ConRon.Arena.unitLikeLoop]
def unitLikeLoopL : FunDecl := lfn (mode, vis, fuel, d, T) locals (w, t, i, dom, body, fv, body2, r) {
  if fuel == 0 { return 0 };
  w := call whnf(mode, vis, d, T);
  if ⟦w⟧.tag == 6 {
    if d + 1 == 0 { abort };
    (t, i) := node FORALL⟦w⟧;
    dom := FORALL⟨t, i⟩.ty;
    body := FORALL⟨t, i⟩.b;
    fv := call intern_fvar(d, dom);
    body2 := call inst1(body, fv, 0);
    r := call unit_like_loop(mode, vis, fuel - 1, d + 1, body2);
    return r
  };
  r := call unit_like_struct(mode, vis, fuel - 1, d, w);
  return r
}

/-- `structUnitCert` once `a`'s type `wta` is unit-like: `b`'s type against it (a side whose type
is a ∀ must be neutral; split off for the proofs). -/
-- con-ron: ConRon/Arena/Core.lean:1877-1895 ConRon.Arena.structUnitCert
@[no_expose, l_impl ConRon.Arena.structUnitCert]
def structUnitTailL : FunDecl := lfn (mode, vis, d, b, wta) locals (tb, wtb, gb, r) {
  tb := call infer_io(mode, vis, d, b);
  wtb := call whnf(mode, vis, d, tb);
  if ⟦wtb⟧.tag == 6 {
    gb := call io_neutral(b);
    if gb == 0 { return 0 }
  };
  r := call defeq(mode, vis, d, wta, wtb);
  return r
}

/-- **Unit-likeness** (`is_def_eq_unit_like`): `a`'s type, head-normalised, unit-like at
`unitLikeFuel` (`2^62`), and `b`'s type definitionally equal to it. -/
-- con-ron: ConRon/Arena/Core.lean:1877-1895 ConRon.Arena.structUnitCert
@[no_expose, l_impl ConRon.Arena.structUnitCert]
def structUnitCertL : FunDecl := lfn (mode, vis, d, a, b) locals (ta, wta, ga, u, r) {
  ta := call infer_io(mode, vis, d, a);
  wta := call whnf(mode, vis, d, ta);
  if ⟦wta⟧.tag == 6 {
    ga := call io_neutral(a);
    if ga == 0 { return 0 }
  };
  u := call unit_like_loop(mode, vis, 4611686018427387904, d, wta);
  if u == 0 { return 0 };
  r := call struct_unit_tail(mode, vis, d, b, wta);
  return r
}

/-- con-ron: ConRon/Arena/Core.lean:1925-1933 ConRon.Arena.stuckIrrel -/
@[no_expose, l_impl ConRon.Arena.stuckIrrel]
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
-- con-ron: ConRon/Arena/Core.lean:4127-4196 ConRon.Arena.defeqStuck
@[no_expose, l_impl ConRon.Arena.defeqStuck]
def stuckStrL : FunDecl :=
    lfn (mode, vis, d, a, b, side, lt, fo) locals (t, i, co, uo, el, sl, ss, c, r) {
  (t, i) := node LIT⟦lt⟧;
  if LIT⟨t, i⟩.kind == 1 && ⟦fo⟧.tag == 3 {
    (t, i) := node CONST⟦fo⟧;
    co := CONST⟨t, i⟩.n;
    uo := CONST⟨t, i⟩.us;
    el := call pin_word(52);
    sl := call pin_at(6);
    ss := call str_lit_stored(vis);
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
-- con-ron: ConRon/Arena/Core.lean:4127-4196 ConRon.Arena.defeqStuck
@[no_expose, l_impl ConRon.Arena.defeqStuck]
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
-- con-ron: ConRon/Arena/Core.lean:4127-4196 ConRon.Arena.defeqStuck
@[no_expose, l_impl ConRon.Arena.defeqStuck]
def stuckAppL : FunDecl := lfn (mode, vis, d, a, b) locals (ok, r) {
  ok := call stuck_app_cong(mode, vis, d, a, b);
  if ok != 0 { return 1 };
  r := call stuck_irrel(mode, vis, d, a, b);
  return r
}

/-- `defeqStuck`'s free-variable, constant and λ arms and the fallback, by the two views' words
(split off for the proofs). -/
-- con-ron: ConRon/Arena/Core.lean:4127-4196 ConRon.Arena.defeqStuck
@[no_expose, l_impl ConRon.Arena.defeqStuck]
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
con-ron: ConRon/Arena/Core.lean:4127-4196 ConRon.Arena.defeqStuck -/
@[no_expose, l_impl ConRon.Arena.defeqStuck]
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
-- con-ron: ConRon/Arena/Core.lean:4198-4236 ConRon.Arena.defeqBody
@[no_expose, l_impl ConRon.Arena.defeqBody]
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
con-ron: ConRon/Arena/Core.lean:4198-4236 ConRon.Arena.defeqBody -/
@[no_expose, l_impl ConRon.Arena.defeqBody]
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

/-- The structure-η and unit-like certificates' functions, at their names (`stuck_irrel`'s first
three arms). -/
structure CertProg (p : Prog) : Prop where
  setTail : p.lookup "struct_eta_cert_tail" = some structEtaCertTailL
  setGo : p.lookup "struct_eta_cert_go" = some structEtaCertGoL
  setWtb : p.lookup "struct_eta_cert_wtb" = some structEtaCertWtbL
  setWith : p.lookup "struct_eta_cert_with" = some structEtaCertWithL
  ecpFam : p.lookup "eta_ctor_partial_fam" = some etaCtorPartialFamL
  ecp : p.lookup "eta_ctor_partial" = some etaCtorPartialL
  sefAt : p.lookup "struct_eta_full_at" = some structEtaFullAtL
  sef : p.lookup "struct_eta_full" = some structEtaFullL
  see : p.lookup "struct_eta_expand" = some structEtaExpandL
  secp : p.lookup "struct_eta_cert_partial" = some structEtaCertPartialL
  setCert : p.lookup "struct_eta_cert" = some structEtaCertL
  ipt : p.lookup "is_prop_type" = some isPropTypeL
  ulFields : p.lookup "unit_like_fields" = some unitLikeFieldsL
  ulShapeAt : p.lookup "unit_like_shape_at" = some unitLikeShapeAtL
  ulShape : p.lookup "unit_like_shape" = some unitLikeShapeL
  ulStruct : p.lookup "unit_like_struct" = some unitLikeStructL
  ulLoop : p.lookup "unit_like_loop" = some unitLikeLoopL
  suTail : p.lookup "struct_unit_tail" = some structUnitTailL
  sunit : p.lookup "struct_unit_cert" = some structUnitCertL
  findTable : FindTableProg p

end L.Arena
