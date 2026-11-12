module

public import ConAgua.Arena.WhnfBase

@[expose] public section

/-!
# Type inference: `inferBody`, `inferBodyIO` and their clauses (phase 7, lane `defeq`)

con-ron's `Arena/Core.lean:2439-2878` in L, written top down: `ensureSort`, the batched binder
telescopes (`inferLams`, `inferPis` with their leaves and outward rebuilds), the batched
application spine at both grades (`inferSpine`, `inferSpineIO`), the projection clause
(`inferProj`, shared by both grades), the two bodies.

**The two grades.** The twin hands `inferBodyIO` the record's io view (`CoreFnsA.ioView`: its
`infer` slot is `inferIO`), so every `r.infer` inside the io body and its clauses is the knot's
`infer_io` slot. `infer_proj` is shared and takes the grade as a word (`io`: `0` full, `1` io).

**Stacks.** `fvs` (the free variables a telescope has introduced) and a spine's accumulator are
slices of the spine stack `SPN` (array 144, top `CTL[136]`). The telescopes' second stack
(`stk`: the opened domains of `inferLams`, the domain sorts of `inferPis`) grows in step with
`fvs` while knot calls run in between, so it cannot share `SPN`: it is a slice of the **binder
stack `BSTK`** (array 145, top `CTL[137]`, lane `defeq`; outside every tier of `CoreS`, which
`CoreS.frame` already allows). Both tops are put back before a function returns.

**Callees not written yet** (stubs, `DefeqCallees` in `Knot.lean`): `abs_entry(e, d, k)`
(`abstract1Fast coreWalkFuel`), `ar_entry(e, d, k, c)` (`abstractRangeFast coreWalkFuel`); from lane `whnf`: `inst_list`,
`inst1`, `inst_lp`, `find_proj`, `str_lit_stored`.
-/

open ConRon.Arena
open L.Ind (IW)


namespace L.Arena

/-! ## Sorts, constants, literals -/

/-- con-ron: ConRon/Arena/Core.lean:2789-2798 ConRon.Arena.ensureSort -/
@[no_expose, l_impl ConRon.Arena.ensureSort]
def ensureSortL : FunDecl := lfn (mode, vis, d, e) locals (hh, t, i) {
  hh := call whnf(mode, vis, d, e);
  if ⟦hh⟧.tag != 2 { fail R_EXPECTED_A_SORT };
  (t, i) := node SORT⟦hh⟧;
  return SORT⟨t, i⟩.u
}

/-- The `.const n us` clause of both bodies: the stored constant, the level count, `constTyAt` (`const_ty_at`, lane `whnf`, with its cache) at the record's own name
(word `p + 1`, the twin's `cv.name`; the cache key). -/
-- con-ron: ConRon/Arena/Core.lean:3404-3467 ConRon.Arena.inferBody
-- con-ron: CHANGED since 01ecb31c — below `ConRon.Arena.inferBody`, `ConRon.Arena.natSizeRefused` changed; re-check the L code and its proofs, then delete this line
-- con-ron: CHANGED since 01ecb31c — `ConRon.Arena.inferBody` changed; re-check the L code and its proofs, then delete this line
-- con-ron: CHANGED since 01ecb31c — below `ConRon.Arena.inferBodyIO`, `ConRon.Arena.natSizeRefused` changed; re-check the L code and its proofs, then delete this line
-- con-ron: ConRon/Arena/Core.lean:3469-3542 ConRon.Arena.inferBodyIO
-- con-ron: CHANGED since 01ecb31c — `ConRon.Arena.inferBodyIO` changed; re-check the L code and its proofs, then delete this line
-- con-ron: ConRon/Arena/Core.lean:232-246 ConRon.Arena.unknownConstError
@[no_expose, l_impl ConRon.Arena.inferBody ConRon.Arena.inferBodyIO ConRon.Arena.unknownConstError]
def inferConstL : FunDecl := lfn (vis, n, us) locals (f, p, lo, l, r) {
  (f, p) := call env_find(n, vis);
  if f == 0 {
    -- `unknownConstError`: `sorryAx` (pin 13) declines, any other name rejects
    l := call pin_at(13);
    if n == l { fail R_USE_OF_THE };
    fail R_UNKNOWN_CONSTANT_2
  };
  (lo, l) := call ls_node(us);
  if l != EREC⦃p + 3⦄ { fail R_INCORRECT_NUMBER_OF };
  r := call const_ty_at(EREC⦃p + 1⦄, EREC⦃p + 2⦄, EREC⦃p + 3⦄, EREC⦃p + 4⦄, us);
  return r
}

/-- The two `.lit` clauses of both bodies: `Nat` (`pinNat`) or `String` (`pinString`), each
behind its basis guard. -/
-- con-ron: ConRon/Arena/Core.lean:3404-3467 ConRon.Arena.inferBody
-- con-ron: CHANGED since 01ecb31c — below `ConRon.Arena.inferBodyIO`, `ConRon.Arena.natSizeRefused` changed; re-check the L code and its proofs, then delete this line
-- con-ron: CHANGED since 01ecb31c — below `ConRon.Arena.inferBody`, `ConRon.Arena.natSizeRefused` changed; re-check the L code and its proofs, then delete this line
-- con-ron: CHANGED since 01ecb31c — `ConRon.Arena.inferBody` changed; re-check the L code and its proofs, then delete this line
-- con-ron: ConRon/Arena/Core.lean:3469-3542 ConRon.Arena.inferBodyIO
-- con-ron: CHANGED since 01ecb31c — `ConRon.Arena.inferBodyIO` changed; re-check the L code and its proofs, then delete this line
@[no_expose, l_impl ConRon.Arena.inferBody ConRon.Arena.inferBodyIO]
def inferLitL : FunDecl := lfn (vis, e) locals (t, i, s, c, r) {
  (t, i) := node LIT⟦e⟧;
  if LIT⟨t, i⟩.kind == 0 {
    s := call nat_lit_stored(vis);
    if s == 0 { fail R_NAT_LITERAL_WITHOUT };
    c := call pin_at(1);
    r := call const_e(c);
    return r
  };
  s := call str_lit_stored(vis);
  if s == 0 { fail R_STRING_LITERALS_BEFORE };
  c := call pin_at(5);
  r := call const_e(c);
  return r
}

/-- con-ron: ConRon/Arena/Core.lean:3123-3129 ConRon.Arena.inferLamResult -/
@[no_expose, l_impl ConRon.Arena.inferLamResult]
def inferLamResultL : FunDecl := lfn (ty, bt, d) locals (ab, r) {
  ab := call abs_entry(bt, d, 0);
  r := call mk_forall(ty, ab);
  return r
}

/-! ## The binder telescopes

`fvs` is the stack slice `(fo, k)` (`CTL[136] = fo + k`), `stk` the binder-stack slice `(lo, k)`
(`CTL[137] = lo + k`); `d + k` is the depth of the next binder (the depth capacity: `infer_lam`
and `infer_forall` abort at `d ≥ 2^63`, so `d + k` does not wrap). The twin's `peelFuel` (`2^24`)
is the exact counter `peel`. -/

/-- The λ loop's leaf and its outward rebuild. -/
-- con-ron: ConRon/Arena/Core.lean:3168-3176 ConRon.Arena.inferLamsLeaf
-- con-ron: ConRon/Arena/Core.lean:3155-3166 ConRon.Arena.inferLamsOut
@[no_expose, l_impl ConRon.Arena.inferLamsLeaf ConRon.Arena.inferLamsOut]
def inferLamsLeafL : FunDecl := lfn (mode, vis, d, t, k, fo, lo) locals (ob, bt, cur, n, ta) {
  ob := call inst_list(t, fo, k, 0);
  bt := call infer(mode, vis, d + k, ob);
  cur := call ar_entry(bt, d, k, 0);
  n := k;
  while n != 0 {
    n -= 1;
    ta := call ar_entry(BSTK.u64[lo + n], d, n, 0);
    cur := call mk_forall(ta, cur)
  };
  return cur
}

/-- con-ron: ConRon/Arena/Core.lean:3178-3202 ConRon.Arena.inferLams -/
@[no_expose, l_impl ConRon.Arena.inferLams]
def inferLamsL : FunDecl :=
    lfn (mode, vis, d, peel, t, k, fo, lo) locals (s, i, ty, body, tyo, tty, w, fv, r) {
  while peel != 0 && ⟦t⟧.tag == 5 {
    (s, i) := node LAM⟦t⟧;
    ty := LAM⟨s, i⟩.ty;
    body := LAM⟨s, i⟩.b;
    tyo := call inst_list(ty, fo, k, 0);
    tty := call infer(mode, vis, d + k, tyo);
    w := call whnf(mode, vis, d + k, tty);
    if ⟦w⟧.tag != 2 { fail R_EXPECTED_A_SORT };
    fv := call intern_fvar(d + k, tyo);
    if len(SPN.u64) <= fo + k { abort };
    if len(BSTK.u64) <= lo + k { abort };
    SPN.u64[fo + k] := fv;
    BSTK.u64[lo + k] := tyo;
    k += 1;
    CTL.u64[136] := fo + k;
    CTL.u64[137] := lo + k;
    peel -= 1;
    t := body
  };
  r := call infer_lams_leaf(mode, vis, d, t, k, fo, lo);
  return r
}

/-- The ∀ loop's leaf and its outward `imax` fold. -/
-- con-ron: ConRon/Arena/Core.lean:3215-3225 ConRon.Arena.inferPisLeaf
-- con-ron: ConRon/Arena/Core.lean:3204-3213 ConRon.Arena.inferPisOut
@[no_expose, l_impl ConRon.Arena.inferPisLeaf ConRon.Arena.inferPisOut]
def inferPisLeafL : FunDecl := lfn (mode, vis, d, t, k, fo, lo) locals (ob, bt, v, n, r) {
  ob := call inst_list(t, fo, k, 0);
  bt := call infer(mode, vis, d + k, ob);
  v := call ensure_sort(mode, vis, d + k, bt);
  n := k;
  while n != 0 {
    n -= 1;
    v := call intern_imax(BSTK.u64[lo + n], v)
  };
  r := call intern_sort(v);
  return r
}

/-- con-ron: ConRon/Arena/Core.lean:3227-3248 ConRon.Arena.inferPis -/
@[no_expose, l_impl ConRon.Arena.inferPis]
def inferPisL : FunDecl :=
    lfn (mode, vis, d, peel, t, k, fo, lo) locals (s, i, ty, body, tyo, tty, w, u, fv, r) {
  while peel != 0 && ⟦t⟧.tag == 6 {
    (s, i) := node FORALL⟦t⟧;
    ty := FORALL⟨s, i⟩.ty;
    body := FORALL⟨s, i⟩.b;
    tyo := call inst_list(ty, fo, k, 0);
    tty := call infer(mode, vis, d + k, tyo);
    w := call whnf(mode, vis, d + k, tty);
    if ⟦w⟧.tag != 2 { fail R_EXPECTED_A_SORT };
    (s, i) := node SORT⟦w⟧;
    u := SORT⟨s, i⟩.u;
    fv := call intern_fvar(d + k, tyo);
    if len(SPN.u64) <= fo + k { abort };
    if len(BSTK.u64) <= lo + k { abort };
    SPN.u64[fo + k] := fv;
    BSTK.u64[lo + k] := u;
    k += 1;
    CTL.u64[136] := fo + k;
    CTL.u64[137] := lo + k;
    peel -= 1;
    t := body
  };
  r := call infer_pis_leaf(mode, vis, d, t, k, fo, lo);
  return r
}

/-- con-ron: ConRon/Arena/Core.lean:3250-3260 ConRon.Arena.inferLam -/
@[no_expose, l_impl ConRon.Arena.inferLam]
def inferLamL : FunDecl := lfn (mode, vis, d, ty, body) locals (tty, w, fv, so, lo, r) {
  if d >> 63 != 0 { abort };
  tty := call infer(mode, vis, d, ty);
  w := call whnf(mode, vis, d, tty);
  if ⟦w⟧.tag != 2 { fail R_EXPECTED_A_SORT };
  fv := call intern_fvar(d, ty);
  so := CTL.u64[136];
  lo := CTL.u64[137];
  if len(SPN.u64) <= so { abort };
  if len(BSTK.u64) <= lo { abort };
  SPN.u64[so] := fv;
  BSTK.u64[lo] := ty;
  CTL.u64[136] := so + 1;
  CTL.u64[137] := lo + 1;
  r := call infer_lams(mode, vis, d, 16777216, body, 1, so, lo);
  CTL.u64[136] := so;
  CTL.u64[137] := lo;
  return r
}

/-- con-ron: ConRon/Arena/Core.lean:3262-3274 ConRon.Arena.inferForall -/
@[no_expose, l_impl ConRon.Arena.inferForall]
def inferForallL : FunDecl := lfn (mode, vis, d, ty, body) locals (tty, w, t, i, u, fv, so, lo, r) {
  if d >> 63 != 0 { abort };
  tty := call infer(mode, vis, d, ty);
  w := call whnf(mode, vis, d, tty);
  if ⟦w⟧.tag != 2 { fail R_EXPECTED_A_SORT };
  (t, i) := node SORT⟦w⟧;
  u := SORT⟨t, i⟩.u;
  fv := call intern_fvar(d, ty);
  so := CTL.u64[136];
  lo := CTL.u64[137];
  if len(SPN.u64) <= so { abort };
  if len(BSTK.u64) <= lo { abort };
  SPN.u64[so] := fv;
  BSTK.u64[lo] := u;
  CTL.u64[136] := so + 1;
  CTL.u64[137] := lo + 1;
  r := call infer_pis(mode, vis, d, 16777216, body, 1, so, lo);
  CTL.u64[136] := so;
  CTL.u64[137] := lo;
  return r
}

/-! ## The application spine

The arguments are the slice `(ao, an)` `head_and_args` left on the stack; the accumulator is the
slice `(co, cn)` above it (`co` the top on entry; a top past the stack's end is a capacity
abort, so that the empty accumulator is a slice). The `whnf` re-entry resets it to `#[a]`. -/

/-- con-ron: ConRon/Arena/Core.lean:3290-3296 ConRon.Arena.defeqArg -/
@[no_expose, l_impl ConRon.Arena.defeqArg]
def defeqArgL : FunDecl := lfn (mode, vis, d, a, ta, ty) locals (er, r) {
  er := call is_eager_reduce(a);
  if er != 0 {
    r := call defeq_e(mode, vis, d, ta, ty);
    return r
  };
  r := call defeq(mode, vis, d, ta, ty);
  return r
}

/-- One argument of the full-grade spine at a `∀` type `(dom, body)`, its domain already opened
(`dom2`): infer the argument, compare its type, push it. -/
-- con-ron: ConRon/Arena/Core.lean:3298-3326 ConRon.Arena.inferSpine
@[no_expose, l_impl ConRon.Arena.inferSpine]
def inferSpineArgL : FunDecl := lfn (mode, vis, d, a, dom2) locals (ta, ok) {
  ta := call infer(mode, vis, d, a);
  ok := call defeq_arg(mode, vis, d, a, ta, dom2);
  if ok == 0 { fail R_APPLICATION_TYPE_MISMATCH };
  return 0
}

/-- con-ron: ConRon/Arena/Core.lean:3298-3326 ConRon.Arena.inferSpine -/
@[no_expose, l_impl ConRon.Arena.inferSpine]
def inferSpineL : FunDecl :=
    lfn (mode, vis, d, ty, ao, an) locals (co, cn, i, a, t, x, dom, dom2, ty2, w, z, r) {
  co := CTL.u64[136];
  if len(SPN.u64) < co { abort };
  cn := 0;
  i := 0;
  for i < an {
    a := SPN.u64[ao + i];
    if ⟦ty⟧.tag == 6 {
      (t, x) := node FORALL⟦ty⟧;
      dom := FORALL⟨t, x⟩.ty;
      ty := FORALL⟨t, x⟩.b;
      dom2 := call inst_list(dom, co, cn, 0);
      z := call infer_spine_arg(mode, vis, d, a, dom2);
      if len(SPN.u64) <= co + cn { abort };
      SPN.u64[co + cn] := a;
      cn += 1;
      CTL.u64[136] := co + cn
    } else {
      ty2 := call inst_list(ty, co, cn, 0);
      w := call whnf(mode, vis, d, ty2);
      if ⟦w⟧.tag != 6 { fail R_FUNCTION_EXPECTED_2 };
      (t, x) := node FORALL⟦w⟧;
      dom := FORALL⟨t, x⟩.ty;
      ty := FORALL⟨t, x⟩.b;
      z := call infer_spine_arg(mode, vis, d, a, dom);
      if len(SPN.u64) <= co { abort };
      SPN.u64[co] := a;
      cn := 1;
      CTL.u64[136] := co + 1
    }
  };
  r := call inst_list(ty, co, cn, 0);
  CTL.u64[136] := co;
  return r
}

/-- con-ron: ConRon/Arena/Core.lean:3328-3335 ConRon.Arena.inferApp -/
@[no_expose, l_impl ConRon.Arena.inferApp]
def inferAppL : FunDecl := lfn (mode, vis, d, e) locals (top, hd, ao, an, tf, r) {
  top := CTL.u64[136];
  (hd, ao, an) := call head_and_args(e);
  tf := call infer(mode, vis, d, hd);
  r := call infer_spine(mode, vis, d, tf, ao, an);
  CTL.u64[136] := top;
  return r
}

/-- con-ron: ConRon/Arena/Core.lean:3337-3358 ConRon.Arena.inferSpineIO -/
@[no_expose, l_impl ConRon.Arena.inferSpineIO]
def inferSpineIOL : FunDecl :=
    lfn (mode, vis, d, ty, ao, an) locals (co, cn, i, a, t, x, ty2, w, r) {
  co := CTL.u64[136];
  if len(SPN.u64) < co { abort };
  cn := 0;
  i := 0;
  for i < an {
    a := SPN.u64[ao + i];
    if ⟦ty⟧.tag == 6 {
      (t, x) := node FORALL⟦ty⟧;
      if len(SPN.u64) <= co + cn { abort };
      SPN.u64[co + cn] := a;
      cn += 1;
      CTL.u64[136] := co + cn;
      ty := FORALL⟨t, x⟩.b
    } else {
      ty2 := call inst_list(ty, co, cn, 0);
      w := call whnf(mode, vis, d, ty2);
      if ⟦w⟧.tag != 6 { fail R_FUNCTION_EXPECTED_2 };
      (t, x) := node FORALL⟦w⟧;
      if len(SPN.u64) <= co { abort };
      SPN.u64[co] := a;
      cn := 1;
      CTL.u64[136] := co + 1;
      ty := FORALL⟨t, x⟩.b
    }
  };
  r := call inst_list(ty, co, cn, 0);
  CTL.u64[136] := co;
  return r
}

/-- con-ron: ConRon/Arena/Core.lean:3360-3366 ConRon.Arena.inferAppIOAt -/
@[no_expose, l_impl ConRon.Arena.inferAppIOAt]
def inferAppIOL : FunDecl := lfn (mode, vis, d, e) locals (top, hd, ao, an, tf, r) {
  top := CTL.u64[136];
  (hd, ao, an) := call head_and_args(e);
  tf := call infer_io(mode, vis, d, hd);
  r := call infer_spine_io(mode, vis, d, tf, ao, an);
  CTL.u64[136] := top;
  return r
}

/-! ## Projections -/

/-- The entry's type at the subject's levels and arguments: `instLPFast` of the entry's body,
then ONE `instantiateList` against `targs ++ [pe]` (the arguments' slice `(to, tn)` is at the
stack top, so `pe` is pushed right after it). `q` is the table record, `i` the field. -/
-- con-ron: ConRon/Arena/Core.lean:2611-2622 ConRon.Arena.IProjEntry.typeAt
@[no_expose, l_impl ConRon.Arena.IProjEntry.typeAt]
def projTypeAtL : FunDecl := lfn (q, i, us, to, tn, pe) locals (body, b, r) {
  body := 0;
  if i < EREC⦃q + 10⦄ { body := EREC⦃EREC⦃q + 9⦄ + i⦄ };
  b := call inst_lp(EREC⦃q + 3⦄, EREC⦃q + 4⦄, us, body);
  if len(SPN.u64) <= to + tn { abort };
  SPN.u64[to + tn] := pe;
  CTL.u64[136] := to + tn + 1;
  r := call inst_list(b, to, tn + 1, 0);
  CTL.u64[136] := to + tn;
  return r
}

/-! ## The projection's guard at the use (`checkProjGuard`, con-leche task #480)

Nothing about the guard is stored: the structure's sort is read off its type or walked to at the
use's levels (`proj_guard_sort`), the rows are read off the constructor's telescope opened at the
use's levels (`proj_guard_rows`), and each row's term must be a proposition wherever the guard sort
is zero (`check_guard_rows`). The rows are pairs `(depth, term)` on the spine stack `SPN` (two words
each, at `ro`), above the top while they are checked. -/

/-- `check_guard_rows(mode, vis, ro, rn, i, gs)`: rows `i, …, rn - 1` of the slice at `ro`: each
row's term, inferred at the io grade at its own depth and head-normalized, has a sort that is zero
wherever `gs` is (`lv_zero_where_zero`). -/
-- con-ron: ConRon/Arena/Core.lean:2800-2822 ConRon.Arena.checkGuardRows
@[no_expose, l_impl ConRon.Arena.checkGuardRows]
def checkGuardRowsL : FunDecl := lfn (mode, vis, ro, rn, i, gs) locals (d, dom, t, w, tg, x, u, ok, r) {
  if rn <= i { return 0 };
  d := SPN.u64[ro + 2 * i];
  dom := SPN.u64[ro + 2 * i + 1];
  t := call infer_io(mode, vis, d, dom);
  w := call whnf(mode, vis, d, t);
  if ⟦w⟧.tag != 2 { fail R_EXPECTED_A_SORT };
  (tg, x) := node SORT⟦w⟧;
  u := SORT⟨tg, x⟩.u;
  ok := call lv_zero_where_zero(gs, u);
  if ok == 0 { fail R_PROJECTION_FROM_A };
  r := call check_guard_rows(mode, vis, ro, rn, i + 1, gs);
  return r
}

/-- `proj_guard_sort(mode, vis, p, us)`: the sort the rows answer to at this use, `(1, gs)`, or
`(0, 0)` where the guard asks nothing (`p` the structure's inductive record). A stored type that
ends in a sort answers at once (`Prop` asks for propositions: the zero level, pin word 53); else the
sort is walked to (`former_sort_loop`, from depth `0`): never zero asks nothing, no sort rejects. -/
-- con-ron: ConRon/Arena/Core.lean:2824-2844 ConRon.Arena.projGuardSort
@[no_expose, l_impl ConRon.Arena.projGuardSort]
def projGuardSortL : FunDecl := lfn (mode, vis, p, us) locals (po, pc, ty, n, f, u, a, z, ity, nv) {
  po := EREC⦃p + 2⦄;
  pc := EREC⦃p + 3⦄;
  ty := EREC⦃p + 4⦄;
  n := EREC⦃p + 17⦄ + EREC⦃p + 11⦄;
  if n < EREC⦃p + 17⦄ { abort };
  (f, u) := call former_res_sort(ty);
  if f != 0 {
    a := call lv_always_zero(u);
    if a != 0 { z := call pin_word(53); return (1, z) };
    return (0, 0)
  };
  ity := call inst_lp(po, pc, us, ty);
  (f, u) := call former_sort_loop(mode, vis, 0, n, ity);
  if f == 0 { fail R_PROJECTION_FROM_A_STRUCTURE };
  nv := call lv_never(u);
  if nv != 0 { return (0, 0) };
  return (1, u)
}

/-- `proj_guard_rows_at(cty, nP, idx, fo, fn, j, ro, rn)`: the rows of fields `j, …, idx` read off
the opened telescope's free variables (the `IW` slice `(fo, fn)`): field `idx`, and every earlier
field a later one uses (`struct_used_later`), as `(nP + j, its variable's type)`, appended at row
`rn` of the slice at `ro` (the top raised past each); the row count after. -/
-- con-ron: ConRon/Arena/Core.lean:3066-3077 ConRon.Arena.projGuardRowsAt
-- con-ron: CHANGED since 01ecb31c — `ConRon.Arena.projGuardRowsAt` changed; re-check the L code and its proofs, then delete this line
-- con-ron: CHANGED since 01ecb31c — below `ConRon.Arena.projGuardRowsAt`, `ConRon.Arena.projGuardFast`, `ConRon.Arena.projGuardRowsGo` changed; re-check the L code and its proofs, then delete this line
@[no_expose, l_impl ConRon.Arena.projGuardRowsAt]
def projGuardRowsAtL : FunDecl := lfn (cty, nP, idx, fo, fn, j, ro, rn) locals (used, ty, r) {
  if idx < j { return rn };
  if j == idx { used := 1 } else { used := call struct_used_later(cty, nP, j) };
  if used != 0 && nP + j < fn {
    ty := call fvar_type_d(IW.u64[fo + nP + j]);
    if len(SPN.u64) <= ro + 2 * rn + 1 { abort };
    SPN.u64[ro + 2 * rn] := nP + j;
    SPN.u64[ro + 2 * rn + 1] := ty;
    CTL.u64[136] := ro + 2 * rn + 2;
    r := call proj_guard_rows_at(cty, nP, idx, fo, fn, j + 1, ro, rn + 1);
    return r
  };
  r := call proj_guard_rows_at(cty, nP, idx, fo, fn, j + 1, ro, rn);
  return r
}

/-- `proj_guard_rows(vis, q, i, us)`: what a `.proj` use of field `i` of the table record `q` must
show: `(1, ro, rn)` the rows at `ro` on the stack (left above the top), or `(0, 0, 0)` where the
stored constructor does not bind what the entry says. The constructor's type at the use's levels
(`const_ty_at`), opened in one pass (`open_pis_at_fvars_f`). -/
-- con-ron: ConRon/Arena/Core.lean:3079-3102 ConRon.Arena.projGuardRows
-- con-ron: CHANGED since 01ecb31c — below `ConRon.Arena.projGuardRows`, `ConRon.Arena.openPisRawGo` changed; re-check the L code and its proofs, then delete this line
-- con-ron: CHANGED since 01ecb31c — `ConRon.Arena.projGuardRows` changed; re-check the L code and its proofs, then delete this line
@[no_expose, l_impl ConRon.Arena.projGuardRows]
def projGuardRowsL : FunDecl := lfn (vis, q, i, us) locals (np, f, c, cty, ok, fo, fn, b, ro, rn, k) {
  np := EREC⦃q + 5⦄;
  (f, c) := call env_find(EREC⦃q + 6⦄, vis);
  if f == 0 { return (0, 0, 0) };
  cty := call const_ty_at(EREC⦃c + 1⦄, EREC⦃c + 2⦄, EREC⦃c + 3⦄, EREC⦃c + 4⦄, us);
  k := np + i + 1;
  if k <= np { abort };
  (ok, fo, fn, b) := call open_pis_at_fvars_f(k, cty, 0);
  if ok == 0 { return (0, 0, 0) };
  ro := CTL.u64[136];
  rn := call proj_guard_rows_at(EREC⦃c + 4⦄, np, i, fo, fn, 0, ro, 0);
  return (1, ro, rn)
}

/-- `check_proj_guard(mode, vis, q, i, us)`: the official `infer_proj` restriction at this use of
field `i` of the table record `q` (the structure's name at `q + 2`); the stack top put back. -/
-- con-ron: ConRon/Arena/Core.lean:3104-3121 ConRon.Arena.checkProjGuard
@[no_expose, l_impl ConRon.Arena.checkProjGuard]
def checkProjGuardL : FunDecl := lfn (mode, vis, q, i, us) locals (top, f, p, g, gs, ok, ro, rn, u) {
  top := CTL.u64[136];
  (f, p) := call env_find(EREC⦃q + 2⦄, vis);
  if f == 0 { fail R_PROJECTION_FROM_A };
  if EREC⦃p⦄ != 3 { fail R_PROJECTION_FROM_A };
  (g, gs) := call proj_guard_sort(mode, vis, p, us);
  if g == 0 { return 0 };
  (ok, ro, rn) := call proj_guard_rows(vis, q, i, us);
  if ok == 0 { fail R_PROJECTION_FROM_A };
  u := call check_guard_rows(mode, vis, ro, rn, 0, gs);
  CTL.u64[136] := top;
  return 0
}

/-- `inferProj` from the subject type's head constant `T.{us}` on (`te` the head-normal subject
type, `q` the table record of field `i`). -/
-- con-ron: ConRon/Arena/Core.lean:3368-3402 ConRon.Arena.inferProj
@[no_expose, l_impl ConRon.Arena.inferProj]
def inferProjAtL : FunDecl :=
    lfn (mode, vis, sn, i, pe, te, T, us, q) locals (top, to, tn, lo, usl, u, r) {
  top := CTL.u64[136];
  (to, tn) := call get_app_args(te);
  if T != sn { fail R_INVALID_PROJECTION_THE };
  if tn != EREC⦃q + 5⦄ { fail R_PROJECTION_PARAMETER_MISMATCH };
  (lo, usl) := call ls_node(us);
  if usl != EREC⦃q + 4⦄ { fail R_PROJECTION_WITHOUT_A };
  u := call check_proj_guard(mode, vis, q, i, us);
  r := call proj_type_at(q, i, us, to, tn, pe);
  CTL.u64[136] := top;
  return r
}

/-- con-ron: ConRon/Arena/Core.lean:3368-3402 ConRon.Arena.inferProj
con-ron: ConRon/Arena/Core.lean:300-311 ConRon.Arena.projMissError -/
@[no_expose, l_impl ConRon.Arena.inferProj ConRon.Arena.projMissError]
def inferProjL : FunDecl :=
    lfn (mode, io, vis, d, sn, i, pe) locals (it, te, hh, t, x, f, q, r, cT, cu, to, tn) {
  if io != 0 { it := call infer_io(mode, vis, d, pe) } else { it := call infer(mode, vis, d, pe) };
  te := call whnf(mode, vis, d, it);
  hh := call get_app_fn(te);
  if ⟦hh⟧.tag != 3 { fail R_INVALID_PROJECTION_NOT };
  (t, x) := node CONST⟦hh⟧;
  cT := CONST⟨t, x⟩.n;
  cu := CONST⟨t, x⟩.us;
  (f, q) := call find_proj(vis, cT, i);
  if f == 0 {
    -- `projMissError`: a table means the index is out of range; an indexed structure-like type
    -- (`projIndexedStructLike`: `T` is `sn`, an inductive with one constructor, more arguments
    -- than parameters, and `i` below the constructor's field count) declines; else reject
    f := call find_table(vis, cT);
    if f != 0 { fail R_PROJECTION_INDEX_OUT };
    if cT == sn {
      (to, tn) := call get_app_args(te);
      (f, q) := call env_find(cT, vis);
      if f != 0 && EREC⦃q⦄ == 3 && EREC⦃q + 19⦄ == 1 && EREC⦃q + 17⦄ < tn {
        (f, q) := call env_find(EREC⦃EREC⦃q + 18⦄⦄, vis);
        if f != 0 && EREC⦃q⦄ == 4 && i < EREC⦃q + 6⦄ { fail R_PROJECTION_ON_AN }
      }
    };
    fail R_INVALID_PROJECTION_NOT
  };
  r := call infer_proj_at(mode, vis, sn, i, pe, te, cT, cu, q);
  return r
}

/-! ## The bodies -/

/-- The full body's `.letE` clause (official `infer_let`). -/
-- con-ron: ConRon/Arena/Core.lean:3404-3467 ConRon.Arena.inferBody
-- con-ron: CHANGED since 01ecb31c — below `ConRon.Arena.inferBody`, `ConRon.Arena.natSizeRefused` changed; re-check the L code and its proofs, then delete this line
-- con-ron: CHANGED since 01ecb31c — `ConRon.Arena.inferBody` changed; re-check the L code and its proofs, then delete this line
@[no_expose, l_impl ConRon.Arena.inferBody]
def inferLetL : FunDecl := lfn (mode, vis, d, ty, v, b) locals (tty, u, tv, ok, ob, r) {
  tty := call infer(mode, vis, d, ty);
  u := call ensure_sort(mode, vis, d, tty);
  tv := call infer(mode, vis, d, v);
  ok := call defeq(mode, vis, d, tv, ty);
  if ok == 0 { fail R_LET_VALUE_TYPE };
  ob := call inst1(b, v, 0);
  r := call infer(mode, vis, d, ob);
  return r
}

/-- con-ron: ConRon/Arena/Core.lean:3404-3467 ConRon.Arena.inferBody -/
-- con-ron: CHANGED since 01ecb31c — `ConRon.Arena.inferBody` changed; re-check the L code and its proofs, then delete this line
-- con-ron: CHANGED since 01ecb31c — below `ConRon.Arena.inferBody`, `ConRon.Arena.natSizeRefused` changed; re-check the L code and its proofs, then delete this line
@[no_expose, l_impl ConRon.Arena.inferBody]
def inferBodyL : FunDecl := lfn (mode, vis, d, e) locals (g, x1, x2, x3, su, r) {
  (g, x1, x2, x3) := call e_view(e);
  if g == 2 {
    su := call intern_succ(x1);
    r := call intern_sort(su);
    return r
  };
  if g == 1 {
    if x1 < d { return x2 };
    fail R_FREE_VARIABLE_OUT
  };
  if g == 3 {
    r := call infer_const(vis, x1, x2);
    return r
  };
  if g == 8 {
    r := call infer_lit(vis, e);
    return r
  };
  if g == 6 {
    r := call infer_forall(mode, vis, d, x1, x2);
    return r
  };
  if g == 5 {
    r := call infer_lam(mode, vis, d, x1, x2);
    return r
  };
  if g == 4 {
    r := call infer_app(mode, vis, d, e);
    return r
  };
  if g == 9 {
    r := call infer_proj(mode, 0, vis, d, x1, x2, x3);
    return r
  };
  if g == 7 {
    r := call infer_let(mode, vis, d, x1, x2, x3);
    return r
  };
  fail R_INFERTYPE_BEYOND_THE
}

/-- The io body's `.forallE` clause (chained, one binder). The depth capacity: the body runs at
`d + 1`, which must not wrap (the twin's depth is a `Nat`). -/
-- con-ron: ConRon/Arena/Core.lean:3469-3542 ConRon.Arena.inferBodyIO
-- con-ron: CHANGED since 01ecb31c — below `ConRon.Arena.inferBodyIO`, `ConRon.Arena.natSizeRefused` changed; re-check the L code and its proofs, then delete this line
-- con-ron: CHANGED since 01ecb31c — `ConRon.Arena.inferBodyIO` changed; re-check the L code and its proofs, then delete this line
@[no_expose, l_impl ConRon.Arena.inferBodyIO]
def inferForallIOL : FunDecl := lfn (mode, vis, d, ty, body) locals (tt, hh, t, i, u, fv, ob, bt, v, iu, r) {
  if d + 1 == 0 { abort };
  tt := call infer_io(mode, vis, d, ty);
  hh := call whnf(mode, vis, d, tt);
  if ⟦hh⟧.tag != 2 { fail R_EXPECTED_A_SORT };
  (t, i) := node SORT⟦hh⟧;
  u := SORT⟨t, i⟩.u;
  fv := call intern_fvar(d, ty);
  ob := call inst1(body, fv, 0);
  bt := call infer_io(mode, vis, d + 1, ob);
  v := call ensure_sort(mode, vis, d + 1, bt);
  iu := call intern_imax(u, v);
  r := call intern_sort(iu);
  return r
}

/-- The io body's `.lam` clause (no domain-sort run; the depth capacity as `infer_forall_io`'s). -/
-- con-ron: ConRon/Arena/Core.lean:3469-3542 ConRon.Arena.inferBodyIO
-- con-ron: CHANGED since 01ecb31c — below `ConRon.Arena.inferBodyIO`, `ConRon.Arena.natSizeRefused` changed; re-check the L code and its proofs, then delete this line
-- con-ron: CHANGED since 01ecb31c — `ConRon.Arena.inferBodyIO` changed; re-check the L code and its proofs, then delete this line
@[no_expose, l_impl ConRon.Arena.inferBodyIO]
def inferLamIOL : FunDecl := lfn (mode, vis, d, ty, body) locals (fv, ob, bt, r) {
  if d + 1 == 0 { abort };
  fv := call intern_fvar(d, ty);
  ob := call inst1(body, fv, 0);
  bt := call infer_io(mode, vis, d + 1, ob);
  r := call infer_lam_result(ty, bt, d);
  return r
}

/-- con-ron: ConRon/Arena/Core.lean:3469-3542 ConRon.Arena.inferBodyIO -/
-- con-ron: CHANGED since 01ecb31c — `ConRon.Arena.inferBodyIO` changed; re-check the L code and its proofs, then delete this line
-- con-ron: CHANGED since 01ecb31c — below `ConRon.Arena.inferBodyIO`, `ConRon.Arena.natSizeRefused` changed; re-check the L code and its proofs, then delete this line
@[no_expose, l_impl ConRon.Arena.inferBodyIO]
def inferBodyIOL : FunDecl := lfn (mode, vis, d, e) locals (g, x1, x2, x3, su, ob, r) {
  (g, x1, x2, x3) := call e_view(e);
  if g == 2 {
    su := call intern_succ(x1);
    r := call intern_sort(su);
    return r
  };
  if g == 1 {
    if x1 < d { return x2 };
    fail R_FREE_VARIABLE_OUT
  };
  if g == 3 {
    r := call infer_const(vis, x1, x2);
    return r
  };
  if g == 8 {
    r := call infer_lit(vis, e);
    return r
  };
  if g == 6 {
    r := call infer_forall_io(mode, vis, d, x1, x2);
    return r
  };
  if g == 5 {
    r := call infer_lam_io(mode, vis, d, x1, x2);
    return r
  };
  if g == 4 {
    r := call infer_app_io(mode, vis, d, e);
    return r
  };
  if g == 9 {
    r := call infer_proj(mode, 1, vis, d, x1, x2, x3);
    return r
  };
  if g == 7 {
    ob := call inst1(x3, x2, 0);
    r := call infer_io(mode, vis, d, ob);
    return r
  };
  fail R_INFERTYPE_BEYOND_THE
}

end L.Arena
