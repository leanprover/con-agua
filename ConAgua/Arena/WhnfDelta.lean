import ConAgua.Arena.WhnfSpine
import ConAgua.Arena.Env
import ConAgua.Arena.LsStore
import ConAgua.Arena.ConstStore
import ConAgua.Arena.ExprMk
import ConAgua.Arena.PinsNatOp

/-!
# The `whnf` half of the whnf family: `whnf`, its loop, the literal/delta step, and their helpers

Twin: `vendor/con-ron/ConRon/Arena/Core.lean`. L names and their twins:

| L | twin | notes |
|---|---|---|
| `whnf(mode, vis, d, e)` | the knot's `whnf` slot (`coreKnot`'s `whnf :=` field) | `whnfStuckTag`, the `whnfC` memo (`wh_find`/`wh_put`, array 98) |
| `whnf_loop(mode, vis, d, e)` | `whnfBody`/`whnfLoop` | an uncounted `while` (the `2^62` loop fuel is not counted in L) |
| `whnf_step(mode, vis, d, e)` | `whnfStep` | `(0, e)` done, `(1, e)` cont; `r.whnfCore false depth e` is `call whnf_core(mode, 0, vis, d, e)` |
| `reduce_nat(mode, vis, d, e)` | `reduceNat` | literal acceleration; the "native Nat computation on literals" arm is an `abort` |
| `nat_bin_op_name(c)` | `natBinOpName` | `pin_at` comparisons |
| `nat_op_stored(vis, c)` | `natOpStored` | `env_find`, kind `== 1` |
| `raw_nat_lit(h)` | `rawNatLit?` | `(flag, off, cnt)`: the literal's POOL slice |
| `nat_lit_supported(vis)` | `natLitSupported` | three `env_find` + the `nat_*_ok` triple |
| `nat_ind_ok(found, q)`, `nat_zero_ok(found, q)`, `nat_succ_ok(found, q)` | `natIndOk`, `natZeroOk`, `natSuccOk` | `(found, q)` is `find?`'s result |
| `const_e(n)` | `constE` | `intern_const(n, pin_word(52))` |
| `nat_lit_to_ctor(o, cnt)` | `natLitToConstructor` | `k = n - 1` via `nat_sub` with a pushed one-limb `1` |
| `lit_to_ctor_if_nat(vis, h)` | `litToCtorIfNat` | |
| `unfold_definition(vis, e)` | `unfoldDefinition` | `get_app_fn`/`get_app_args`/`mk_app_n`; the level list's length read off `LSREC` directly (no `view_ls` L function exists) |
| `const_val_at(n, po, pl, value, us)` | `constValAt` | the `constValC` memo (`cv_find`/`cv_put`, array 103); a miss calls the stub `inst_lp` |

**Two deviations from the twin's clause order**, both harmless simplifications (same aborts, same
order of externally visible side effects):

1. `view h`'s scratch check (`t != 0 && CTL.u64[1] == 0`) is identical for every tag, so `raw_nat_lit`
   and `reduce_nat`'s inner `view f` hoist it once before branching on the tag, instead of repeating
   it in each of the ten arms.
2. `natOpWfNames` is not given its own L function (it is not one of the assigned names): its eight
   pin reads are inlined at `reduce_nat`'s one call site.

**The two kinds of `view h` the twin uses here** (DESIGN's "exactness", `WhnfSpine.lean`'s note):
`get_app_fn`/`unfold_definition`'s `hh.tag == ETag.const` tests the tag BEFORE viewing, so only the
matching arm's bound check is needed; `raw_nat_lit` and `reduce_nat`'s `view f` do not, so the L code
must perform the one bound check that the handle's OWN tag selects, for all ten tags (the other nine
arms only check and return `none`/fall through, as the twin's `_ => pure none` does).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedVariables false

namespace L.Arena

/-! ## Two more cache arrays, read directly on a memo hit -/

/-- `whnfC`'s array (`whSch.arr`): the `whnf` memo, hit value at `WH.u64[j * 4 + 3]`. -/
abbrev WH : ArrId := 98
/-- `constValC`'s array (`cvSch.arr`): the `const_val_at` memo, hit value at `CV.u64[j * 4 + 3]`. -/
abbrev CV : ArrId := 103

/-! ## The L code -/

/-- `const_e(n)`: `intern_const(n, pin_word(52))` (the empty level list). -/
@[l_impl ConRon.Arena.constE]
def constEL : FunDecl := lfn (n) locals (us, r) {
  us := call pin_word(52);
  r := call intern_const(n, us);
  return r
}

/-- `nat_lit_to_ctor(o, cnt)`: the literal `n` (the POOL slice `(o, cnt)`) as a `Nat` constructor,
one layer: `Nat.zero` at `cnt == 0`, else `Nat.succ (lit (n - 1))` with `n - 1` computed as
`natPredLit` does (push a one-limb `1` at the pool top, `nat_sub`, `intern_lit`). -/
@[l_impl ConRon.Arena.natLitToConstructor]
def natLitToCtorL : FunDecl := lfn (o, cnt) locals (z, r, s, sc, oo, ll, lh) {
  if cnt == 0 {
    z := call pin_at(2);
    r := call const_e(z);
    return r
  };
  s := call pin_at(3);
  sc := call const_e(s);
  oo := CTL.u64[0];
  if len(POOL.u64) <= oo { abort };
  POOL.u64[oo] := 1;
  CTL.u64[0] := oo + 1;
  ll := call nat_sub(o, cnt, oo, 1);
  lh := call intern_lit(oo + 1, ll);
  r := call mk_app(sc, lh);
  return r
}

/-- `nat_ind_ok(found, p)`: the stored `Nat` declaration at record `p` (`found == 0` is `none`) has
the expected shape: an `indInfo`, no level parameters, type `Sort 1`. -/
@[l_impl ConRon.Arena.natIndOk]
def natIndOkL : FunDecl := lfn (found, p) locals (s1) {
  if found == 0 { return 0 };
  if EREC.u64[p] != 3 { return 0 };
  if EREC.u64[p + 3] != 0 { return 0 };
  s1 := call pin_word(54);
  return u64(EREC.u64[p + 4] == s1)
}

/-- `nat_zero_ok(found, p)`: the stored `Nat.zero` declaration has the expected shape: a `ctorInfo`,
no level parameters, type `Nat`. -/
@[l_impl ConRon.Arena.natZeroOk]
def natZeroOkL : FunDecl := lfn (found, p) locals (nt, nc) {
  if found == 0 { return 0 };
  if EREC.u64[p] != 4 { return 0 };
  if EREC.u64[p + 3] != 0 { return 0 };
  nt := call pin_at(1);
  nc := call const_e(nt);
  return u64(EREC.u64[p + 4] == nc)
}

/-- `nat_succ_ok(found, p)`: the stored `Nat.succ` declaration has the expected (annotated) shape: a
`ctorInfo`, no level parameters, type `Nat → Nat`. -/
@[l_impl ConRon.Arena.natSuccOk]
def natSuccOkL : FunDecl := lfn (found, p) locals (nt, nc, ty, t, i, dom, body) {
  if found == 0 { return 0 };
  if EREC.u64[p] != 4 { return 0 };
  if EREC.u64[p + 3] != 0 { return 0 };
  nt := call pin_at(1);
  nc := call const_e(nt);
  ty := EREC.u64[p + 4];
  if ty >> 28 != 6 { return 0 };
  t := (ty >> 27) & 1;
  i := ty & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[30 + t] <= i { abort };
  dom := FAREC.u64[i * 4 + t * 2];
  body := FAREC.u64[i * 4 + t * 2 + 1];
  if dom == nc && body == nc { return 1 };
  return 0
}

/-- `nat_lit_supported(vis)`: `Nat`/`Nat.zero`/`Nat.succ` are all stored with the expected shape. -/
@[l_impl ConRon.Arena.natLitSupported]
def natLitSupportedL : FunDecl :=
  lfn (vis) locals (nt, f, p, r, nz, f2, p2, r2, ns, f3, p3, r3) {
  nt := call pin_at(1);
  (f, p) := call env_find(nt, vis);
  r := call nat_ind_ok(f, p);
  if r == 0 { return 0 };
  nz := call pin_at(2);
  (f2, p2) := call env_find(nz, vis);
  r2 := call nat_zero_ok(f2, p2);
  if r2 == 0 { return 0 };
  ns := call pin_at(3);
  (f3, p3) := call env_find(ns, vis);
  r3 := call nat_succ_ok(f3, p3);
  return r3
}

/-- `lit_to_ctor_if_nat(vis, h)`: a `Nat`-literal major premise, converted to constructor form one
layer (`lit_to_ctor_if_nat`'s cheap tag test, as the twin's does, so no bound check is paid for a
non-`lit` handle). -/
@[l_impl ConRon.Arena.litToCtorIfNat]
def litToCtorIfNatL : FunDecl :=
  lfn (vis, h) locals (tag, t, i, k, sup, o, cnt, r) {
  tag := h >> 28;
  if tag != 8 { return h };
  t := (h >> 27) & 1;
  i := h & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[2 + t] <= i { abort };
  k := REC.u64[i * 8 + t * 4];
  if k != 0 { return h };
  sup := call nat_lit_supported(vis);
  if sup == 0 { return h };
  o := REC.u64[i * 8 + t * 4 + 1];
  cnt := REC.u64[i * 8 + t * 4 + 2];
  r := call nat_lit_to_ctor(o, cnt);
  return r
}

/-- `raw_nat_lit(h)`: a `Nat` literal reading of `h`, as a POOL slice `(flag, off, cnt)`:
`.lit (.natVal _)`'s own slice, or the empty slice (flag set) at `Nat.zero` (`pinNatZero` under
`emptyLevels`), else no match (flag clear). `h` is not tag-tested first (the twin's `view h` is
unconditional), so every one of the ten tags gets its own bound check; only `lit`/`const` read
further. -/
@[l_impl ConRon.Arena.rawNatLit?]
def rawNatLitL : FunDecl := lfn (h) locals (tag, t, i, k, nz, el) {
  tag := h >> 28;
  t := (h >> 27) & 1;
  i := h & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if tag == 0 { if CTL.u64[22 + t] <= i { abort }; return (0, 0, 0) };
  if tag == 1 { if CTL.u64[26 + t] <= i { abort }; return (0, 0, 0) };
  if tag == 2 { if CTL.u64[16 + t] <= i { abort }; return (0, 0, 0) };
  if tag == 3 {
    if CTL.u64[18 + t] <= i { abort };
    nz := call pin_at(2);
    el := call pin_word(52);
    if CREC.u64[i * 4 + t * 2] == nz && CREC.u64[i * 4 + t * 2 + 1] == el {
      return (1, CTL.u64[0], 0)
    };
    return (0, 0, 0)
  };
  if tag == 4 { if CTL.u64[4 + t] <= i { abort }; return (0, 0, 0) };
  if tag == 5 { if CTL.u64[28 + t] <= i { abort }; return (0, 0, 0) };
  if tag == 6 { if CTL.u64[30 + t] <= i { abort }; return (0, 0, 0) };
  if tag == 7 { if CTL.u64[20 + t] <= i { abort }; return (0, 0, 0) };
  if tag == 8 {
    if CTL.u64[2 + t] <= i { abort };
    k := REC.u64[i * 8 + t * 4];
    if k == 0 { return (1, REC.u64[i * 8 + t * 4 + 1], REC.u64[i * 8 + t * 4 + 2]) };
    return (0, 0, 0)
  };
  if CTL.u64[32 + t] <= i { abort };
  return (0, 0, 0)
}

/-- `nat_bin_op_name(c)`: is `c` one of the fourteen pinned binary `Nat` operations (the fifteenth,
`pred`, is unary and not tested here)? The pin table read inline (`PINS.u64[1 + k]`), as
`nat_op_result`'s own dispatch does (`NatArms.lean`), rather than fourteen `pin_at` calls: the
same values, one bound check instead of fourteen. -/
@[l_impl ConRon.Arena.natBinOpName]
def natBinOpNameL : FunDecl := lfn (c) locals () {
  if PINS.u64[0] == 0 { abort };
  if c == PINS.u64[16] || c == PINS.u64[17] || c == PINS.u64[18] || c == PINS.u64[19] ||
    c == PINS.u64[20] || c == PINS.u64[21] || c == PINS.u64[22] || c == PINS.u64[23] ||
    c == PINS.u64[24] || c == PINS.u64[25] || c == PINS.u64[26] || c == PINS.u64[27] ||
    c == PINS.u64[28] || c == PINS.u64[29] { return 1 };
  return 0
}

/-- `nat_op_stored(vis, c)`: is `c` stored as a definition at all (the reduction-time half of
`natOpGuard`)? -/
@[l_impl ConRon.Arena.natOpStored]
def natOpStoredL : FunDecl := lfn (vis, c) locals (f, p) {
  (f, p) := call env_find(c, vis);
  if f == 0 { return 0 };
  return u64(EREC.u64[p] == 1)
}

/-- `const_val_at(n, po, pl, value, us)`: a stored definition's value at the universe instantiation
`us`, memoized on `(n, us)` (`cv_find`/`cv_put`, array 103); a miss calls the stub `inst_lp(po, pl,
us, value)` (the level parameters `(po, pl)` the slice of name handles at the constant's record). -/
@[l_impl ConRon.Arena.constValAt]
def constValAtL : FunDecl := lfn (n, po, pl, value, us) locals (fd, j, dd, r, z) {
  (fd, j, dd) := call cv_find(n, us);
  if fd != 0 { return CV.u64[j * 4 + 3] };
  r := call inst_lp(po, pl, us, value);
  (fd, j, dd) := call cv_find(n, us);
  z := call cv_put(n, us, r, fd, j);
  return r
}

/-- `unfold_definition(vis, e)`: unfold the application of a definition at the head, one step, its
value instantiated through `const_val_at`. The level-argument list's length is read directly off
`LSREC` (no `view_ls`/`view_ls_len` L function exists yet). -/
@[l_impl ConRon.Arena.unfoldDefinition]
def unfoldDefinitionL : FunDecl :=
  lfn (vis, e) locals (hh, t, i, n, us, found, p, tu, iu, usl, lpl, po, value, v, ao, an, r) {
  hh := call get_app_fn(e);
  if hh >> 28 != 3 { return (0, 0) };
  t := (hh >> 27) & 1;
  i := hh & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[18 + t] <= i { abort };
  n := CREC.u64[i * 4 + t * 2];
  us := CREC.u64[i * 4 + t * 2 + 1];
  (found, p) := call env_find(n, vis);
  if found == 0 { return (0, 0) };
  if EREC.u64[p] != 1 { return (0, 0) };
  tu := (us >> 27) & 1;
  iu := us & 134217727;
  if tu != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[40 + tu] <= iu { abort };
  usl := LSREC.u64[iu * 6 + tu * 3 + 1];
  lpl := EREC.u64[p + 3];
  if usl != lpl { return (0, 0) };
  po := EREC.u64[p + 2];
  value := EREC.u64[p + 5];
  v := call const_val_at(n, po, lpl, value, us);
  (ao, an) := call get_app_args(e);
  r := call mk_app_n(v, ao, an);
  return (1, r)
}

/-- `reduce_nat(mode, vis, d, e)`: the binary literal acceleration run in the `whnf` loop before
delta-unfolding (`Nat.succ` on a literal, then the certified binary operations, then the pinned
"safety net" ops whose native computation declines: an `abort`). `view f` (the application's head)
is not tag-tested first, so all ten tags get their bound check; only `const`/`app` do more. -/
@[l_impl ConRon.Arena.reduceNat]
def reduceNatL : FunDecl :=
  lfn (mode, vis, d, e) locals
    (t, i, f, b, tag2, t2, i2, c, us, el, ns, sup, wb, fl1, o1, cnt1, oo, xh, g, a, t3, i3, isbin,
     stored, di2, mo2, gc2, la2, lo2, xo2, sl2, sr2, iswf, sup2, wa, fl2, o2, cnt2, rf, rh) {
  if e >> 28 != 4 { return (0, 0) };
  t := (e >> 27) & 1;
  i := e & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[4 + t] <= i { abort };
  f := AREC.u64[i * 4 + t * 2];
  b := AREC.u64[i * 4 + t * 2 + 1];
  tag2 := f >> 28;
  t2 := (f >> 27) & 1;
  i2 := f & 134217727;
  if t2 != 0 && CTL.u64[1] == 0 { abort };
  if tag2 == 3 {
    if CTL.u64[18 + t2] <= i2 { abort };
    c := CREC.u64[i2 * 4 + t2 * 2];
    us := CREC.u64[i2 * 4 + t2 * 2 + 1];
    el := call pin_word(52);
    if us != el { return (0, 0) };
    ns := call pin_at(3);
    if c != ns { return (0, 0) };
    sup := call nat_lit_supported(vis);
    if sup == 0 { return (0, 0) };
    wb := call whnf(mode, vis, d, b);
    (fl1, o1, cnt1) := call raw_nat_lit(wb);
    if fl1 == 0 { return (0, 0) };
    oo := CTL.u64[0];
    if len(POOL.u64) <= oo { abort };
    POOL.u64[oo] := 1;
    CTL.u64[0] := oo + 1;
    xh := call nat_add_lit(o1, cnt1, oo, 1);
    return (1, xh)
  };
  if tag2 == 4 {
    if CTL.u64[4 + t2] <= i2 { abort };
    g := AREC.u64[i2 * 4 + t2 * 2];
    a := AREC.u64[i2 * 4 + t2 * 2 + 1];
    if g >> 28 != 3 { return (0, 0) };
    t3 := (g >> 27) & 1;
    i3 := g & 134217727;
    if t3 != 0 && CTL.u64[1] == 0 { abort };
    if CTL.u64[18 + t3] <= i3 { abort };
    c := CREC.u64[i3 * 4 + t3 * 2];
    us := CREC.u64[i3 * 4 + t3 * 2 + 1];
    el := call pin_word(52);
    if us != el { return (0, 0) };
    isbin := call nat_bin_op_name(c);
    stored := call nat_op_stored(vis, c);
    if isbin != 0 && stored != 0 {
      wa := call whnf(mode, vis, d, a);
      (fl1, o1, cnt1) := call raw_nat_lit(wa);
      if fl1 == 0 { return (0, 0) };
      wb := call whnf(mode, vis, d, b);
      (fl2, o2, cnt2) := call raw_nat_lit(wb);
      if fl2 == 0 { return (0, 0) };
      (rf, rh) := call nat_op_result(c, o1, cnt1, o2, cnt2);
      return (rf, rh)
    };
    di2 := call pin_at(21);
    mo2 := call pin_at(22);
    gc2 := call pin_at(23);
    la2 := call pin_at(24);
    lo2 := call pin_at(25);
    xo2 := call pin_at(26);
    sl2 := call pin_at(27);
    sr2 := call pin_at(28);
    iswf := 0;
    if c == di2 || c == mo2 || c == gc2 || c == la2 || c == lo2 || c == xo2 || c == sl2 ||
      c == sr2 { iswf := 1 };
    if iswf != 0 {
      sup2 := call nat_lit_supported(vis);
      if sup2 != 0 {
        wa := call whnf(mode, vis, d, a);
        (fl1, o1, cnt1) := call raw_nat_lit(wa);
        if fl1 != 0 {
          wb := call whnf(mode, vis, d, b);
          (fl2, o2, cnt2) := call raw_nat_lit(wb);
          if fl2 != 0 { abort }
        }
      }
    };
    return (0, 0)
  };
  if tag2 == 0 { if CTL.u64[22 + t2] <= i2 { abort }; return (0, 0) };
  if tag2 == 1 { if CTL.u64[26 + t2] <= i2 { abort }; return (0, 0) };
  if tag2 == 2 { if CTL.u64[16 + t2] <= i2 { abort }; return (0, 0) };
  if tag2 == 5 { if CTL.u64[28 + t2] <= i2 { abort }; return (0, 0) };
  if tag2 == 6 { if CTL.u64[30 + t2] <= i2 { abort }; return (0, 0) };
  if tag2 == 7 { if CTL.u64[20 + t2] <= i2 { abort }; return (0, 0) };
  if tag2 == 8 { if CTL.u64[2 + t2] <= i2 { abort }; return (0, 0) };
  if CTL.u64[32 + t2] <= i2 { abort };
  return (0, 0)
}

/-- `whnf_step(mode, vis, d, e)`: one iteration of the reduction loop (`decStep`): head-normalize
without delta, try literal acceleration, unfold one definition. -/
@[l_impl ConRon.Arena.whnfStep]
def whnfStepL : FunDecl := lfn (mode, vis, d, e) locals (e1, fl, e2, fl2, e3) {
  e1 := call whnf_core(mode, 0, vis, d, e);
  (fl, e2) := call reduce_nat(mode, vis, d, e1);
  if fl != 0 { return (1, e2) };
  (fl2, e3) := call unfold_definition(vis, e1);
  if fl2 != 0 { return (1, e3) };
  return (0, e1)
}

/-- `whnf_loop(mode, vis, d, e)`: the reduction loop, iterating `whnf_step` on its own (effectively
unbounded, `2^62`) step budget — an uncounted L `while` (the convention: the twin's loop fuels are
not counted in L, since an L `while` already costs L fuel per iteration). -/
@[l_impl ConRon.Arena.whnfBody]
def whnfLoopL : FunDecl := lfn (mode, vis, d, e) locals (fl, x) {
  while 0 == 0 {
    (fl, x) := call whnf_step(mode, vis, d, e);
    if fl == 0 { return x };
    e := x
  }
}

/-- `whnf(mode, vis, d, e)`: the knot's `whnf` slot. The six stuck tags (`sort`, `fvar`, `lam`,
`forallE`, `lit`; `whnfStuckTag`) return `e` untouched; else the `whnfC` memo at the current
generation (`CTL.u64[115]`, array 98): a hit returns the stored handle, a miss runs `whnf_loop`,
probes again (the loop may have changed the table) and inserts. -/
@[l_impl ConRon.Arena.coreKnot]
def whnfL : FunDecl := lfn (mode, vis, d, e) locals (t, fd, j, dd, x, z) {
  t := e >> 28;
  if t == 2 || t == 1 || t == 5 || t == 6 || t == 8 { return e };
  (fd, j, dd) := call wh_find(e, CTL.u64[115] << 32);
  if fd != 0 { return WH.u64[j * 4 + 3] };
  x := call whnf_loop(mode, vis, d, e);
  (fd, j, dd) := call wh_find(e, CTL.u64[115] << 32);
  z := call wh_put(e, CTL.u64[115] << 32, x, fd, j);
  return x
}

/-! ## The program -/

/-- The functions this file writes. -/
def whnfDeltaProg : Prog :=
  [("const_e", constEL), ("nat_lit_to_ctor", natLitToCtorL), ("nat_ind_ok", natIndOkL),
   ("nat_zero_ok", natZeroOkL), ("nat_succ_ok", natSuccOkL), ("nat_lit_supported", natLitSupportedL),
   ("lit_to_ctor_if_nat", litToCtorIfNatL), ("raw_nat_lit", rawNatLitL),
   ("nat_bin_op_name", natBinOpNameL), ("nat_op_stored", natOpStoredL),
   ("const_val_at", constValAtL), ("unfold_definition", unfoldDefinitionL),
   ("reduce_nat", reduceNatL), ("whnf_step", whnfStepL), ("whnf_loop", whnfLoopL), ("whnf", whnfL)]

/-- What the specs in this file need of a program: this file's own sixteen functions, and the
external functions they call by name (`whnf_core` is the one callee covered instead by `KnotOK`,
since it is the knot's own slot and its L code is another agent's). -/
structure WhnfDeltaProg (p : Prog) : Prop where
  whnf : p.lookup "whnf" = some whnfL
  whnfLoop : p.lookup "whnf_loop" = some whnfLoopL
  whnfStep : p.lookup "whnf_step" = some whnfStepL
  reduceNat : p.lookup "reduce_nat" = some reduceNatL
  natBinOpName : p.lookup "nat_bin_op_name" = some natBinOpNameL
  natOpStored : p.lookup "nat_op_stored" = some natOpStoredL
  rawNatLit : p.lookup "raw_nat_lit" = some rawNatLitL
  natLitSupported : p.lookup "nat_lit_supported" = some natLitSupportedL
  natIndOk : p.lookup "nat_ind_ok" = some natIndOkL
  natZeroOk : p.lookup "nat_zero_ok" = some natZeroOkL
  natSuccOk : p.lookup "nat_succ_ok" = some natSuccOkL
  constE : p.lookup "const_e" = some constEL
  natLitToCtor : p.lookup "nat_lit_to_ctor" = some natLitToCtorL
  litToCtorIfNat : p.lookup "lit_to_ctor_if_nat" = some litToCtorIfNatL
  unfoldDefinition : p.lookup "unfold_definition" = some unfoldDefinitionL
  constValAt : p.lookup "const_val_at" = some constValAtL
  pinAt : p.lookup "pin_at" = some pinAtL
  pinWord : p.lookup "pin_word" = some pinWordL
  envFind : p.lookup "env_find" = some envFindL
  getAppFn : p.lookup "get_app_fn" = some getAppFnL
  getAppArgs : p.lookup "get_app_args" = some getAppArgsL
  mkAppN : p.lookup "mk_app_n" = some mkAppNL
  mkApp : p.lookup "mk_app" = some mkApp
  internConst : p.lookup "intern_const" = some internConst
  internLit : p.lookup "intern_lit" = some internLit
  natSub : p.lookup "nat_sub" = some natSub
  natAddLit : p.lookup "nat_add_lit" = some natAddLit
  natOpResult : p.lookup "nat_op_result" = some natOpResultL
  whFind : p.lookup "wh_find" = some (memoFindG whSch)
  whPut : p.lookup "wh_put" = some (memoPutG whSch)
  cvFind : p.lookup "cv_find" = some (memoFindG cvSch)
  cvPut : p.lookup "cv_put" = some (memoPutG cvSch)

/-! ## Lifting a read-only, memory-unchanged triple into `CoreSpec`

For a function whose twin action neither changes `AState` nor the L code's memory, `CoreAfter`'s
existential is witnessed by the very same maps (`KeptAll.refl`, `StackKept.refl`): the recipe
`flushCaches_refinesC` (`CoreRefine.lean`) uses for a state-changing function, specialised to one
that does not change anything. -/
theorem CoreSpec.of_pure {α : Type} [Inhabited α] (p : Prog) (n : Nat) (f : FnName)
    (args : List Word) (T : AM α) (dec : List Word → α) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (G g : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM G g) (hok : AM.ok T a₀) (hst : AM.st T a₀ = a₀)
    (htrip : ⦃fun s => s = s₀⦄
      invoke p (exec p n) f args
      ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ AM.res T a₀ = dec r; ⊤⦄) :
    CoreSpec p n f args T dec s₀ a₀ dn vis fe MM G g := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hmem, hres⟩ := M.of_run (P := fun s => s = s₀) hs hrun htrip
  subst hs
  refine ⟨hloc, hok, ⟨MM, G, ?_, KeptAll.refl _ _ _, ?_⟩, hres⟩
  · rw [hst, hmem]; exact hC
  · rw [hmem]; exact StackKept.refl _

/-! ## The specs

Plain `CoreSpec` for every function that neither calls the knot nor loops; a named, `F`-quantified
(and, for `whnf_loop`, additionally loop-fuel-`K`-quantified) `Prop` for the three that call
`whnf`/`whnf_core`, in `WhnfCoreSlot`/`WhnfSlot`'s own shape; `whnf` itself is `WhnfSlot` (already
in `WhnfBase.lean`). All `sorry` except `nat_bin_op_name` (proved: `CoreSpec.of_pure` plus the
`natOpResult_sel` recipe of `PinsNatOp.lean`, run on the fourteen binary-op pins instead of the
fifteen `natOpResult` reads). -/

section specs
variable (p : Prog) (hp : WhnfDeltaProg p)

/-- **`const_e` refines `constE`.** -/
@[refines ConRon.Arena.constE]
theorem constE_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (MM : ModeMaps) (G g nm : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM G g) (hnm : HW nm) :
    CoreSpec p n "const_e" [nm] (constE (decI nm)) decH s₀ a₀ dn vis fe MM G g := sorry

/-- **`nat_lit_to_ctor` refines `natLitToConstructor`** at the literal `n` the slice `(o, cnt)`
denotes. -/
@[refines ConRon.Arena.natLitToConstructor]
theorem natLitToCtor_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (MM : ModeMaps) (G g o cnt : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM G g) (hs : SliceOK s₀.mem o cnt)
    (hnorm : Norm (s₀.mem.arr64 POOL) o.toNat cnt.toNat) :
    CoreSpec p n "nat_lit_to_ctor" [o, cnt]
      (natLitToConstructor (pv (s₀.mem.arr64 POOL) o.toNat cnt.toNat)) decH s₀ a₀ dn vis fe MM G g :=
  sorry

/-- **`nat_ind_ok` refines `natIndOk`** at the `find?` result `(found, q)` decodes to. -/
@[refines ConRon.Arena.natIndOk]
theorem natIndOk_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (MM : ModeMaps) (G g found q : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM G g) (hq : HW q) :
    CoreSpec p n "nat_ind_ok" [found, q] (natIndOk (decFound dn s₀.mem found q)) decBool s₀ a₀ dn
      vis fe MM G g := sorry

/-- **`nat_zero_ok` refines `natZeroOk`.** -/
@[refines ConRon.Arena.natZeroOk]
theorem natZeroOk_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (MM : ModeMaps) (G g found q : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM G g) (hq : HW q) :
    CoreSpec p n "nat_zero_ok" [found, q] (natZeroOk (decFound dn s₀.mem found q)) decBool s₀ a₀ dn
      vis fe MM G g := sorry

/-- **`nat_succ_ok` refines `natSuccOk`.** -/
@[refines ConRon.Arena.natSuccOk]
theorem natSuccOk_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (MM : ModeMaps) (G g found q : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM G g) (hq : HW q) :
    CoreSpec p n "nat_succ_ok" [found, q] (natSuccOk (decFound dn s₀.mem found q)) decBool s₀ a₀ dn
      vis fe MM G g := sorry

/-- **`nat_lit_supported` refines `natLitSupported`.** -/
@[refines ConRon.Arena.natLitSupported]
theorem natLitSupported_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (MM : ModeMaps) (G g : Word) (hC : CoreS dn s₀.mem a₀ vis fe MM G g) :
    CoreSpec p n "nat_lit_supported" [vis] (natLitSupported fe) decBool s₀ a₀ dn vis fe MM G g :=
  sorry

/-- **`lit_to_ctor_if_nat` refines `litToCtorIfNat`.** -/
@[refines ConRon.Arena.litToCtorIfNat]
theorem litToCtorIfNat_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (MM : ModeMaps) (G g h : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM G g) (hh : HW h) :
    CoreSpec p n "lit_to_ctor_if_nat" [vis, h] (litToCtorIfNat fe (decE h)) decH s₀ a₀ dn vis fe MM
      G g := sorry

/-- **`raw_nat_lit` refines `rawNatLit?`**: the result is a flag and the literal's POOL slice
(`pv`), read-only. -/
@[refines ConRon.Arena.rawNatLit?]
theorem rawNatLit_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (MM : ModeMaps) (G g h : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM G g) (hh : HW h) :
    CoreSpec p n "raw_nat_lit" [h] (rawNatLit? (decE h))
      (fun r => if r.headD 0 = 0 then none
        else some (pv (s₀.mem.arr64 POOL) (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat))
      s₀ a₀ dn vis fe MM G g := sorry

/-- `natBinOpName` with its pins read: word `w k` is the absolute `PINS` word `k`, `natOpSel`'s own
convention (`PinsNatOp.lean`): the fourteen binary ops, `pred` excluded. -/
def natBinOpSel (w : Nat → Word) (c : Word) : Bool :=
  decide (c = w 16) || decide (c = w 17) || decide (c = w 18) || decide (c = w 19) ||
  decide (c = w 20) || decide (c = w 21) || decide (c = w 22) || decide (c = w 23) ||
  decide (c = w 24) || decide (c = w 25) || decide (c = w 26) || decide (c = w 27) ||
  decide (c = w 28) || decide (c = w 29)

/-- **`natBinOpName`'s pins read**, as `natOpResult_sel` reads `natOpResult`'s. -/
theorem natBinOpName_run {m : Mem} {a : AState} (h : PinsFull m a.pins) (c : Word)
    (hc : c.toNat < 2 ^ 32) :
    (natBinOpName (decI c)).run a = .ok (natBinOpSel (pinW m) c, a) := by
  have hb : ∀ i, i < 51 →
      ((decI c : NIdx) == decI (pinW m (1 + i))) = decide (c = pinW m (1 + i)) :=
    fun i hi => decI_beq _ _ hc (h.names_lt i hi)
  simp only [natBinOpName, natAddName, natSubName, natMulName, natPowName, natBeqName,
    natBleName, natDivName, natModName, natGcdName, natLandName, natLorName, natXorName,
    natShiftLeftName, natShiftRightName, pinNatAdd, pinNatSub, pinNatMul, pinNatPow, pinNatBeq,
    pinNatBle, pinNatDiv, pinNatMod, pinNatGcd, pinNatLand, pinNatLor, pinNatXor,
    pinNatShiftLeft, pinNatShiftRight, PIN_NAT_ADD, PIN_NAT_SUB, PIN_NAT_MUL, PIN_NAT_POW,
    PIN_NAT_BEQ, PIN_NAT_BLE, PIN_NAT_DIV, PIN_NAT_MOD, PIN_NAT_GCD, PIN_NAT_LAND, PIN_NAT_LOR,
    PIN_NAT_XOR, PIN_NAT_SHIFT_LEFT, PIN_NAT_SHIFT_RIGHT, pinAt_bind_run h, Nat.reduceAdd,
    Nat.reduceLT]
  have e16 : (decI c == (decI (pinW m 16) : NIdx)) = decide (c = pinW m 16) := hb 15 (by decide)
  have e17 : (decI c == (decI (pinW m 17) : NIdx)) = decide (c = pinW m 17) := hb 16 (by decide)
  have e18 : (decI c == (decI (pinW m 18) : NIdx)) = decide (c = pinW m 18) := hb 17 (by decide)
  have e19 : (decI c == (decI (pinW m 19) : NIdx)) = decide (c = pinW m 19) := hb 18 (by decide)
  have e20 : (decI c == (decI (pinW m 20) : NIdx)) = decide (c = pinW m 20) := hb 19 (by decide)
  have e21 : (decI c == (decI (pinW m 21) : NIdx)) = decide (c = pinW m 21) := hb 20 (by decide)
  have e22 : (decI c == (decI (pinW m 22) : NIdx)) = decide (c = pinW m 22) := hb 21 (by decide)
  have e23 : (decI c == (decI (pinW m 23) : NIdx)) = decide (c = pinW m 23) := hb 22 (by decide)
  have e24 : (decI c == (decI (pinW m 24) : NIdx)) = decide (c = pinW m 24) := hb 23 (by decide)
  have e25 : (decI c == (decI (pinW m 25) : NIdx)) = decide (c = pinW m 25) := hb 24 (by decide)
  have e26 : (decI c == (decI (pinW m 26) : NIdx)) = decide (c = pinW m 26) := hb 25 (by decide)
  have e27 : (decI c == (decI (pinW m 27) : NIdx)) = decide (c = pinW m 27) := hb 26 (by decide)
  have e28 : (decI c == (decI (pinW m 28) : NIdx)) = decide (c = pinW m 28) := hb 27 (by decide)
  have e29 : (decI c == (decI (pinW m 29) : NIdx)) = decide (c = pinW m 29) := hb 28 (by decide)
  simp only [e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29]
  rfl

/-- **`nat_bin_op_name`'s L-side triple**: memory unchanged, the result word decodes to
`natBinOpSel`, read inline off `PINS` (no callee: `natBinOpNameL` has none), exactly as
`natOpResultL_refines` reads its fifteen. `hflag` is the pin table's filled flag (`PinsR.full`'s
own premise): a core function runs only once the driver has filled the pins, so it is available
wherever `CoreS`/`PinsFull` is (`natBinOpName_refines` gets it from `hC.pins.size` and the array's
own zeroth word, which the L code's own `abort` branch would otherwise have to witness). -/
theorem natBinOpNameL_spec (p : Prog) (hp : p.lookup "nat_bin_op_name" = some natBinOpNameL)
    (n : Nat) (s₀ : St) (hflag : pinW s₀.mem 0 ≠ 0) (c : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_bin_op_name" [c]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧
      (r.headD 0 != 0) = natBinOpSel (pinW s₀.mem) c; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, natBinOpNameL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [natBinOpSel, pinW_eq]

/-- **`nat_bin_op_name` refines `natBinOpName`.** `hflag` (the pin table's filled flag) is not
literally one of `PinsFull`'s own fields (`Tiers.lean`'s `PinsR.full : pinW m 0 ≠ 0 → PinsFull m
p` is the unlock, not a consequence), so it is taken here as a hypothesis; a core driver fills the
pins once, before any core function runs, so every real call site has it (`pinsReady`). -/
@[refines ConRon.Arena.natBinOpName]
theorem natBinOpName_refines (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (G g c : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM G g) (hc : HW c) (hflag : pinW s₀.mem 0 ≠ 0) :
    CoreSpec p n "nat_bin_op_name" [c] (natBinOpName (decI c)) decBool s₀ a₀ dn vis fe MM G g := by
  have hrun := natBinOpName_run hC.pins c hc
  apply CoreSpec.of_pure p n "nat_bin_op_name" [c] (natBinOpName (decI c)) decBool s₀ a₀ dn vis fe
    MM G g hC
  · simp [AM.ok, hrun]
  · simp [AM.st, hrun]
  · apply M.triple_of_run
    intro s r s' hs hrun'
    obtain ⟨hmem, hloc, heq⟩ := M.of_run (P := fun s => s = s₀) hs hrun'
      (natBinOpNameL_spec p hp.natBinOpName n s₀ hflag c)
    subst hs
    refine ⟨hloc, hmem, ?_⟩
    simp only [AM.res, hrun, decBool]
    rw [← heq]

/-- **`nat_op_stored` refines `natOpStored`.** -/
@[refines ConRon.Arena.natOpStored]
theorem natOpStored_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (MM : ModeMaps) (G g c : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM G g) (hc : HW c) :
    CoreSpec p n "nat_op_stored" [vis, c] (natOpStored fe (decI c)) decBool s₀ a₀ dn vis fe MM G
      g := sorry

/-- **`const_val_at` refines `constValAt`**, given the level parameters `lps` the slice `(po, pl)`
of the constant's record holds, and the stub `inst_lp`'s spec (`WhnfCallees`, phase 4). -/
@[refines ConRon.Arena.constValAt]
theorem constValAt_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (MM : ModeMaps) (G g nm po pl value us : Word) (lps : List NIdx)
    (hC : CoreS dn s₀.mem a₀ vis fe MM G g) (hnm : HW nm) (hv : HW value) (hu : HW us)
    (hwc : WhnfCallees p) (hlps : hslice? (s₀.mem.arr64 EREC) po.toNat pl.toNat = some lps) :
    CoreSpec p n "const_val_at" [nm, po, pl, value, us]
      (constValAt (decI nm) lps (decE value) (decI us)) decH s₀ a₀ dn vis fe MM G g := sorry

-- TODO(merge with the `whnf` branch): the lead's `CoreSpec`/`CoreRef` gained a trailing
-- `(ok : List Word → Prop := ResH)` argument (result words must be valid handles); this
-- `decOptR`-returning statement should pass `ResW` (`ResW r := HW (r.headD 0) ∧ HW (r.tail.headD
-- 0)`) explicitly once this file is rebased onto that `WhnfBase.lean`.
/-- **`unfold_definition` refines `unfoldDefinition`**, given the stub `inst_lp`'s spec. -/
@[refines ConRon.Arena.unfoldDefinition]
theorem unfoldDefinition_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (MM : ModeMaps) (G g e : Word) (hC : CoreS dn s₀.mem a₀ vis fe MM G g)
    (he : HW e) (hwc : WhnfCallees p) :
    CoreSpec p n "unfold_definition" [vis, e] (unfoldDefinition fe (decE e)) decOptR s₀ a₀ dn vis fe
      MM G g := sorry

-- TODO(merge with the `whnf` branch): pass `ResW` explicitly here too (`decOptR`), once rebased.
/-- `reduce_nat(mode, vis, d, e)` refines `reduceNat` at every knot fuel `F ≥ n`, given the knot's
`whnf` slot at L-fuel `n` (`KnotOK`). -/
def ReduceNatSpec (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (G g mode d e : Word), n ≤ F → SlotPre s₀ a₀ dn vis fe MM G g mode → HW e →
    KnotOK p n →
    CoreSpec p n "reduce_nat" [mode, vis, d, e]
      (reduceNat (coreKnot (decMode mode) fe id F) fe d.toNat (decE e)) decOptR s₀ a₀ dn vis fe MM G
      g

/-- **`reduce_nat` refines `reduceNat`.** -/
@[refines ConRon.Arena.reduceNat]
theorem reduceNat_refines (n : Nat) (hwd : WhnfDeltaProg p) : ReduceNatSpec p n := sorry

-- TODO(merge with the `whnf` branch): pass `ResW` explicitly here too (`decStep`), once rebased.
/-- `whnf_step(mode, vis, d, e)` refines `whnfStep` at every knot fuel `F ≥ n`, given `KnotOK p n`
(its `r.whnfCore false depth e` is `call whnf_core(mode, 0, vis, d, e)`, its `r.whnf` calls are
`reduce_nat`'s). -/
def WhnfStepSpec (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (G g mode d e : Word), n ≤ F → SlotPre s₀ a₀ dn vis fe MM G g mode → HW e →
    KnotOK p n →
    CoreSpec p n "whnf_step" [mode, vis, d, e]
      (whnfStep (coreKnot (decMode mode) fe id F) fe d.toNat (decE e)) decStep s₀ a₀ dn vis fe MM G
      g

/-- **`whnf_step` refines `whnfStep`.** -/
@[refines ConRon.Arena.whnfStep]
theorem whnfStep_refines (n : Nat) (hwd : WhnfDeltaProg p) (hrn : ReduceNatSpec p n) :
    WhnfStepSpec p n := sorry

/-- `whnf_loop(mode, vis, d, e)` refines `whnfLoop` at every knot fuel `F ≥ n` and every loop fuel
`K ≥ n` (the lead's shape for the `2 ^ 62` loop fuels: `whnf_loop` refines `whnfLoop` directly,
generalized over the loop-fuel argument, so that `whnf`'s own theorem can instantiate it at
`K = whnfLoopFuel` under `n ≤ 2 ^ 62`). -/
def WhnfLoopSpec (p : Prog) (n : Nat) : Prop :=
  ∀ (F K : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (G g mode d e : Word), n ≤ F → n ≤ K → SlotPre s₀ a₀ dn vis fe MM G g mode →
    HW e → KnotOK p n →
    CoreSpec p n "whnf_loop" [mode, vis, d, e]
      (whnfLoop (coreKnot (decMode mode) fe id F) fe d.toNat K (decE e)) decH s₀ a₀ dn vis fe MM G g

/-- **`whnf_loop` refines `whnfLoop`.** -/
@[refines ConRon.Arena.whnfBody]
theorem whnfLoop_refines (n : Nat) (hwd : WhnfDeltaProg p) (hws : WhnfStepSpec p n) :
    WhnfLoopSpec p n := sorry

/-- **`whnf` refines the knot's `whnf` slot**: `WhnfSlot p (n + 1)` (`WhnfBase.lean`), from
`whnf_loop`'s spec at L-fuel `n` and `n ≤ 2 ^ 62` (so that `whnfBody`'s fixed loop fuel `whnfLoopFuel
= 2 ^ 62` instantiates `WhnfLoopSpec`'s `K`). Priority: proved only if time permits. -/
@[refines ConRon.Arena.coreKnot]
theorem whnf_refines (n : Nat) (hn : n ≤ 2 ^ 62) (hwd : WhnfDeltaProg p) (hk : KnotOK p n)
    (hloop : WhnfLoopSpec p n) : WhnfSlot p (n + 1) := sorry

end specs

end L.Arena
