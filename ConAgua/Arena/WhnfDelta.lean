import ConAgua.Arena.Reasons
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
-- con-ron: ConRon/Arena/Core.lean:120-124 ConRon.Arena.constE
@[l_impl ConRon.Arena.constE]
def constEL : FunDecl := lfn (n) locals (us, r) {
  us := call pin_word(52);
  r := call intern_const(n, us);
  return r
}

/-- `nat_lit_to_ctor(o, cnt)`: the literal `n` (the POOL slice `(o, cnt)`) as a `Nat` constructor,
one layer: `Nat.zero` at `cnt == 0`, else `Nat.succ (lit (n - 1))` with `n - 1` computed by
`nat_pred_lit` (`NatArms.lean`: push a one-limb `1` at the pool top, `nat_sub`, `intern_lit`; this
function had those three steps inline, whnf-delta2 replaced them by the call, a behaviour-preserving
split that reuses `natPredLit`'s proof). -/
-- con-ron: ConRon/Arena/Core.lean:458-469 ConRon.Arena.natLitToConstructor
@[l_impl ConRon.Arena.natLitToConstructor]
def natLitToCtorL : FunDecl := lfn (o, cnt) locals (z, r, s, sc, lh) {
  if cnt == 0 {
    z := call pin_at(2);
    r := call const_e(z);
    return r
  };
  s := call pin_at(3);
  sc := call const_e(s);
  lh := call nat_pred_lit(o, cnt);
  r := call mk_app(sc, lh);
  return r
}

/-- `nat_ind_ok(found, p)`: the stored `Nat` declaration at record `p` (`found == 0` is `none`) has
the expected shape: an `indInfo`, no level parameters, type `Sort 1`. -/
-- con-ron: ConRon/Arena/Core.lean:471-477 ConRon.Arena.natIndOk
@[l_impl ConRon.Arena.natIndOk]
def natIndOkL : FunDecl := lfn (found, p) locals (s1) {
  if found == 0 { return 0 };
  if EREC.u64[p] != 3 { return 0 };
  if EREC.u64[p + 3] != 0 { return 0 };
  s1 := call pin_word(54);
  return u64(EREC.u64[p + 4] == s1)
}

/-- `nat_zero_ok(found, p)`: the stored `Nat.zero` declaration has the expected shape: a `ctorInfo`,
no level parameters, type `Nat`. The twin interns `Nat` (`constE`) BEFORE it tests the level
parameters, so `const_e` is called before that test (an earlier version tested first and skipped the
interning, a divergence of the arena from the twin's state; whnf-delta2 reordered it). -/
-- con-ron: ConRon/Arena/Core.lean:479-486 ConRon.Arena.natZeroOk
@[l_impl ConRon.Arena.natZeroOk]
def natZeroOkL : FunDecl := lfn (found, p) locals (nt, nc) {
  if found == 0 { return 0 };
  if EREC.u64[p] != 4 { return 0 };
  nt := call pin_at(1);
  nc := call const_e(nt);
  if EREC.u64[p + 3] != 0 { return 0 };
  return u64(EREC.u64[p + 4] == nc)
}

/-- `nat_succ_ok(found, p)`: the stored `Nat.succ` declaration has the expected (annotated) shape: a
`ctorInfo`, no level parameters, type `Nat → Nat`. -/
-- con-ron: ConRon/Arena/Core.lean:488-500 ConRon.Arena.natSuccOk
@[l_impl ConRon.Arena.natSuccOk]
def natSuccOkL : FunDecl := lfn (found, p) locals (nt, nc, ty, t, i, dom, body) {
  if found == 0 { return 0 };
  if EREC.u64[p] != 4 { return 0 };
  if EREC.u64[p + 3] != 0 { return 0 };
  nt := call pin_at(1);
  nc := call const_e(nt);
  ty := EREC.u64[p + 4];
  if ty >> 28 != 6 { return 0 };
  t := ⟦ty⟧.tier;
  i := ⟦ty⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if FORALL⟨t⟩.count <= i { abort };
  dom := FORALL⟨t, i⟩.ty;
  body := FORALL⟨t, i⟩.b;
  if dom == nc && body == nc { return 1 };
  return 0
}

/-- `nat_lit_supported(vis)`: `Nat`/`Nat.zero`/`Nat.succ` are all stored with the expected shape. -/
-- con-ron: ConRon/Arena/Core.lean:502-512 ConRon.Arena.natLitSupported
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
-- con-ron: ConRon/Arena/Core.lean:562-570 ConRon.Arena.litToCtorIfNat
@[l_impl ConRon.Arena.litToCtorIfNat]
def litToCtorIfNatL : FunDecl :=
  lfn (vis, h) locals (tag, t, i, k, sup, o, cnt, r) {
  tag := h >> 28;
  if tag != 8 { return h };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if LIT⟨t⟩.count <= i { abort };
  k := LIT⟨t, i⟩.kind;
  if k != 0 { return h };
  sup := call nat_lit_supported(vis);
  if sup == 0 { return h };
  o := LIT⟨t, i⟩.o;
  cnt := LIT⟨t, i⟩.l;
  r := call nat_lit_to_ctor(o, cnt);
  return r
}

/-- `raw_nat_lit(h)`: a `Nat` literal reading of `h`, as a POOL slice `(flag, off, cnt)`:
`.lit (.natVal _)`'s own slice, or the empty slice (flag set) at `Nat.zero` (`pinNatZero` under
`emptyLevels`), else no match (flag clear). `h` is not tag-tested first (the twin's `view h` is
unconditional), so every one of the ten tags gets its own bound check; only `lit`/`const` read
further. A handle with a tag above `9` is no node (the twin's `view` fails on it): the last arm is
`proj` only, `abort` otherwise (whnf-delta2: added, so that the L code refines the twin on every
handle word; before, the last arm answered "no match" for the tags `10`‥`15` too). -/
-- con-ron: ConRon/Arena/Core.lean:572-582 ConRon.Arena.rawNatLit?
@[l_impl ConRon.Arena.rawNatLit?]
def rawNatLitL : FunDecl := lfn (h) locals (tag, t, i, k, nz, el) {
  tag := h >> 28;
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if tag == 0 { if BVAR⟨t⟩.count <= i { abort }; return (0, 0, 0) };
  if tag == 1 { if FVAR⟨t⟩.count <= i { abort }; return (0, 0, 0) };
  if tag == 2 { if SORT⟨t⟩.count <= i { abort }; return (0, 0, 0) };
  if tag == 3 {
    if CONST⟨t⟩.count <= i { abort };
    nz := call pin_at(2);
    el := call pin_word(52);
    if CONST⟨t, i⟩.n == nz && CONST⟨t, i⟩.us == el {
      return (1, CTL.u64[0], 0)
    };
    return (0, 0, 0)
  };
  if tag == 4 { if APP⟨t⟩.count <= i { abort }; return (0, 0, 0) };
  if tag == 5 { if LAM⟨t⟩.count <= i { abort }; return (0, 0, 0) };
  if tag == 6 { if FORALL⟨t⟩.count <= i { abort }; return (0, 0, 0) };
  if tag == 7 { if LET⟨t⟩.count <= i { abort }; return (0, 0, 0) };
  if tag == 8 {
    if LIT⟨t⟩.count <= i { abort };
    k := LIT⟨t, i⟩.kind;
    if k == 0 { return (1, LIT⟨t, i⟩.o, LIT⟨t, i⟩.l) };
    return (0, 0, 0)
  };
  if tag != 9 { abort };
  if PROJ⟨t⟩.count <= i { abort };
  return (0, 0, 0)
}

/-- `nat_bin_op_name(c)`: is `c` one of the fourteen pinned binary `Nat` operations (the fifteenth,
`pred`, is unary and not tested here)? The pin table read inline (`PINS.u64[1 + k]`), as
`nat_op_result`'s own dispatch does (`NatArms.lean`), rather than fourteen `pin_at` calls: the
same values, one bound check instead of fourteen. -/
-- con-ron: ConRon/Arena/Core.lean:1209-1221 ConRon.Arena.natBinOpName
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
-- con-ron: ConRon/Arena/Core.lean:1199-1207 ConRon.Arena.natOpStored
@[l_impl ConRon.Arena.natOpStored]
def natOpStoredL : FunDecl := lfn (vis, c) locals (f, p) {
  (f, p) := call env_find(c, vis);
  if f == 0 { return 0 };
  return u64(EREC.u64[p] == 1)
}

/-- `const_val_at(n, po, pl, value, us)`: a stored definition's value at the universe instantiation
`us`, memoized on `(n, us)` (`cv_find`/`cv_put`, array 103); a miss calls the stub `inst_lp(po, pl,
us, value)` (the level parameters `(po, pl)` the slice of name handles at the constant's record). -/
-- con-ron: ConRon/Arena/Core.lean:193-207 ConRon.Arena.constValAt
@[l_impl ConRon.Arena.constValAt]
def constValAtL : FunDecl := lfn (n, po, pl, value, us) locals (fd, j, dd, r, z) {
  (fd, j, dd) := call cv_find(n, us);
  if fd != 0 { return CV.u64[j * 4 + 3] };
  r := call inst_lp(po, pl, us, value);
  (fd, j, dd) := call cv_find(n, us);
  z := call cv_put(n, us, r, fd, j);
  return r
}

/-- `unfold_defn_at(e, n, us, p)`: the second half of `unfold_definition`, once the head constant
`n` (at levels `us`) has a `defnInfo` record at `p`: the level count must agree, then the value
(through `const_val_at`) is applied to the spine. The level-argument list's length is read directly
off `LSREC` (no `view_ls`/`view_ls_len` L function exists yet), after `ls_node`'s own tag test (a
level-list handle has tag `0`; the twin's `viewLs` fails on any other tag, so the L code aborts
there: whnf-delta2 added the `us >> 28` test). The argument slice `get_app_args` pushes is dropped
again before returning (`CTL[136]` put back, the `StackKept` contract of a core function; before,
every unfolding leaked its spine onto the stack: whnf-delta2). -/
-- con-ron: ConRon/Arena/Core.lean:378-398 ConRon.Arena.unfoldDefinition
def unfoldDefnAtL : FunDecl :=
  lfn (e, n, us, p) locals (tu, iu, usl, lpl, po, value, v, top, ao, an, r) {
  if us >> 28 != 0 { abort };
  tu := ⟦us⟧.tier;
  iu := ⟦us⟧.idx;
  if tu != 0 && CTL.u64[1] == 0 { abort };
  if LVLS⟨tu⟩.count <= iu { abort };
  usl := LVLS⟨tu, iu⟩.l;
  lpl := EREC.u64[p + 3];
  if usl != lpl { return (0, 0) };
  po := EREC.u64[p + 2];
  value := EREC.u64[p + 5];
  v := call const_val_at(n, po, lpl, value, us);
  top := CTL.u64[136];
  (ao, an) := call get_app_args(e);
  r := call mk_app_n(v, ao, an);
  CTL.u64[136] := top;
  return (1, r)
}

/-- `unfold_definition(vis, e)`: unfold the application of a definition at the head, one step, its
value instantiated through `const_val_at` (the second half is `unfold_defn_at`, a
behaviour-preserving split, whnf-delta2). -/
-- con-ron: ConRon/Arena/Core.lean:378-398 ConRon.Arena.unfoldDefinition
@[l_impl ConRon.Arena.unfoldDefinition]
def unfoldDefinitionL : FunDecl :=
  lfn (vis, e) locals (hh, t, i, n, us, found, p, fl, r) {
  hh := call get_app_fn(e);
  if hh >> 28 != 3 { return (0, 0) };
  t := ⟦hh⟧.tier;
  i := ⟦hh⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CONST⟨t⟩.count <= i { abort };
  n := CONST⟨t, i⟩.n;
  us := CONST⟨t, i⟩.us;
  (found, p) := call env_find(n, vis);
  if found == 0 { return (0, 0) };
  if EREC.u64[p] != 1 { return (0, 0) };
  (fl, r) := call unfold_defn_at(e, n, us, p);
  return (fl, r)
}

/-- `nat_succ_lit(o, cnt)`: the literal `n + 1`, for the POOL slice `(o, cnt)` of `n`: push a
one-limb `1` at the pool top, `nat_add_lit`. (`reduce_nat`'s `Nat.succ` arm, as its own function:
a behaviour-preserving split, whnf-delta2.) -/
-- con-ron: ConRon/Arena/Core.lean:1223-1277 ConRon.Arena.reduceNat
def natSuccLitL : FunDecl := lfn (o, cnt) locals (oo, xh, pt, pb) {
  oo := CTL.u64[0];
  pt := ⦃oo⦄.tier;
  pb := ⦃oo⦄.idx;
  if len(POOL⟨pt⟩) <= pb { abort };
  POOL⟨pt⟩[pb] := 1;
  CTL.u64[0] := oo + 1;
  xh := call nat_add_lit(o, cnt, oo, 1);
  return xh
}

/-- `reduce_nat_succ(mode, vis, d, c, b)`: the `Nat.succ` arm of `reduce_nat`, once the head constant
`c` (at the empty levels) of `c b` is known: `c` must be `Nat.succ` and the literals supported, then
`b` is head-normalised and, if a literal `n`, answered by the literal `n + 1`. (A behaviour-preserving
split of `reduce_nat`, whnf-delta2.) -/
-- con-ron: ConRon/Arena/Core.lean:1223-1277 ConRon.Arena.reduceNat
def reduceNatSuccL : FunDecl :=
  lfn (mode, vis, d, c, b) locals (sup, ns, wb, fl1, o1, cnt1, xh) {
  sup := call nat_lit_supported(vis);
  ns := call pin_at(3);
  if c != ns { return (0, 0) };
  if sup == 0 { return (0, 0) };
  wb := call whnf(mode, vis, d, b);
  (fl1, o1, cnt1) := call raw_nat_lit(wb);
  if fl1 == 0 { return (0, 0) };
  xh := call nat_succ_lit(o1, cnt1);
  return (1, xh)
}

/-- `reduce_nat_op(mode, vis, d, c, a, b)`: the certified binary operation `c a b` on two literals
(`a`, then `b`, head-normalised; the second only if the first is a literal). (A split of
`reduce_nat`, whnf-delta2.) The result is normalised to a flag word `0`/`1` and a 32-bit handle
word (`decOpt` reads the same value): `nat_op_result`'s refinement says nothing about its words'
high bits, and the callers compute with them (lane `whnf2`). -/
-- con-ron: ConRon/Arena/Core.lean:1223-1277 ConRon.Arena.reduceNat
def reduceNatOpL : FunDecl :=
  lfn (mode, vis, d, c, a, b) locals (wa, fl1, o1, cnt1, wb, fl2, o2, cnt2, rf, rh) {
  wa := call whnf(mode, vis, d, a);
  (fl1, o1, cnt1) := call raw_nat_lit(wa);
  if fl1 == 0 { return (0, 0) };
  wb := call whnf(mode, vis, d, b);
  (fl2, o2, cnt2) := call raw_nat_lit(wb);
  if fl2 == 0 { return (0, 0) };
  (rf, rh) := call nat_op_result(c, o1, cnt1, o2, cnt2);
  return (u64(rf != 0), rh & 4294967295)
}

/-- `nat_op_is_wf(c)`: is `c` one of the eight pinned WF-recursive `Nat` operations (`natOpWfNames`:
`div`, `mod`, `gcd`, `land`, `lor`, `xor`, `shiftLeft`, `shiftRight`, the pin words `22‥29`)? The pin
table read inline as `nat_bin_op_name` does, instead of eight `pin_at` calls. (Written for the proof,
whnf-delta2: the eight `pin_at` reads and the comparison chain were inline in `reduce_nat_wf`.) -/
-- con-ron: ConRon/Arena/Core.lean:1086-1092 ConRon.Arena.natOpWfNames
def natOpIsWfL : FunDecl := lfn (c) locals () {
  if PINS.u64[0] == 0 { abort };
  if c == PINS.u64[22] || c == PINS.u64[23] || c == PINS.u64[24] || c == PINS.u64[25] ||
    c == PINS.u64[26] || c == PINS.u64[27] || c == PINS.u64[28] || c == PINS.u64[29] { return 1 };
  return 0
}

/-- `reduce_nat_wf(mode, vis, d, c, a, b)`: the pinned "safety net" operations (division, `mod`, …)
whose native computation declines: on two literals, an `abort`, else no match. (A split of
`reduce_nat`, whnf-delta2.) -/
-- con-ron: ConRon/Arena/Core.lean:1223-1277 ConRon.Arena.reduceNat
def reduceNatWfL : FunDecl :=
  lfn (mode, vis, d, c, a, b) locals
    (iswf, sup2, wa, fl1, o1, cnt1, wb, fl2, o2, cnt2) {
  iswf := call nat_op_is_wf(c);
  sup2 := call nat_lit_supported(vis);
  if iswf != 0 {
    if sup2 != 0 {
      wa := call whnf(mode, vis, d, a);
      (fl1, o1, cnt1) := call raw_nat_lit(wa);
      if fl1 != 0 {
        wb := call whnf(mode, vis, d, b);
        (fl2, o2, cnt2) := call raw_nat_lit(wb);
        if fl2 != 0 { fail R_NATIVE_NAT_COMPUTATION }
      }
    }
  };
  return (0, 0)
}

/-- `reduce_nat_k(mode, vis, d, f, b)`: `reduce_nat`'s arm for an application `f b` whose head `f` is a
constant: at the empty levels, `reduce_nat_succ`. (A split of `reduce_nat`, whnf-delta2.) -/
-- con-ron: ConRon/Arena/Core.lean:1223-1277 ConRon.Arena.reduceNat
def reduceNatKL : FunDecl :=
  lfn (mode, vis, d, f, b) locals (t2, i2, c, us, el, rf, rh) {
  t2 := ⟦f⟧.tier;
  i2 := ⟦f⟧.idx;
  if CONST⟨t2⟩.count <= i2 { abort };
  c := CONST⟨t2, i2⟩.n;
  us := CONST⟨t2, i2⟩.us;
  el := call pin_word(52);
  if us != el { return (0, 0) };
  (rf, rh) := call reduce_nat_succ(mode, vis, d, c, b);
  return (rf, rh)
}

/-- `reduce_nat_ap(mode, vis, d, f, b)`: `reduce_nat`'s arm for an application `f b` whose head `f`
is itself an application `g a`: for a constant `g` at the empty levels, `reduce_nat_op` (a certified
binary operation) or `reduce_nat_wf`. (A split of `reduce_nat`, whnf-delta2.) -/
-- con-ron: ConRon/Arena/Core.lean:1223-1277 ConRon.Arena.reduceNat
def reduceNatApL : FunDecl :=
  lfn (mode, vis, d, f, b) locals (t2, i2, g, a, t3, i3, c, us, el, isbin, stored, rf, rh) {
  t2 := ⟦f⟧.tier;
  i2 := ⟦f⟧.idx;
  if APP⟨t2⟩.count <= i2 { abort };
  g := APP⟨t2, i2⟩.f;
  a := APP⟨t2, i2⟩.a;
  if g >> 28 != 3 { return (0, 0) };
  t3 := ⟦g⟧.tier;
  i3 := ⟦g⟧.idx;
  if t3 != 0 && CTL.u64[1] == 0 { abort };
  if CONST⟨t3⟩.count <= i3 { abort };
  c := CONST⟨t3, i3⟩.n;
  us := CONST⟨t3, i3⟩.us;
  el := call pin_word(52);
  if us != el { return (0, 0) };
  isbin := call nat_bin_op_name(c);
  stored := call nat_op_stored(vis, c);
  if isbin != 0 && stored != 0 {
    (rf, rh) := call reduce_nat_op(mode, vis, d, c, a, b);
    return (rf, rh)
  };
  (rf, rh) := call reduce_nat_wf(mode, vis, d, c, a, b);
  return (rf, rh)
}

/-- `reduce_nat_head(mode, vis, d, f, b)`: `reduce_nat` on the application `f b`, by the tag of its
head `f` (`view f` is not tag-tested first, so all ten tags get their bound check; only `const` and
`app` do more). A handle with a tag above `9` is no node: `abort`. (A split of `reduce_nat`,
whnf-delta2.) -/
-- con-ron: ConRon/Arena/Core.lean:1223-1277 ConRon.Arena.reduceNat
def reduceNatHeadL : FunDecl :=
  lfn (mode, vis, d, f, b) locals (tag2, t2, i2, rf, rh) {
  tag2 := f >> 28;
  t2 := ⟦f⟧.tier;
  i2 := ⟦f⟧.idx;
  if t2 != 0 && CTL.u64[1] == 0 { abort };
  if tag2 == 3 {
    (rf, rh) := call reduce_nat_k(mode, vis, d, f, b);
    return (rf, rh)
  };
  if tag2 == 4 {
    (rf, rh) := call reduce_nat_ap(mode, vis, d, f, b);
    return (rf, rh)
  };
  if tag2 == 0 { if BVAR⟨t2⟩.count <= i2 { abort }; return (0, 0) };
  if tag2 == 1 { if FVAR⟨t2⟩.count <= i2 { abort }; return (0, 0) };
  if tag2 == 2 { if SORT⟨t2⟩.count <= i2 { abort }; return (0, 0) };
  if tag2 == 5 { if LAM⟨t2⟩.count <= i2 { abort }; return (0, 0) };
  if tag2 == 6 { if FORALL⟨t2⟩.count <= i2 { abort }; return (0, 0) };
  if tag2 == 7 { if LET⟨t2⟩.count <= i2 { abort }; return (0, 0) };
  if tag2 == 8 { if LIT⟨t2⟩.count <= i2 { abort }; return (0, 0) };
  if tag2 != 9 { abort };
  if PROJ⟨t2⟩.count <= i2 { abort };
  return (0, 0)
}

/-- `reduce_nat(mode, vis, d, e)`: the binary literal acceleration run in the `whnf` loop before
delta-unfolding (`Nat.succ` on a literal, then the certified binary operations, then the pinned
"safety net" ops whose native computation declines: an `abort`). `view f` (the application's head)
is not tag-tested first, so all ten tags get their bound check; only `const`/`app` do more.
`nat_lit_supported` runs wherever the twin's does: the twin writes `c == ns && (← natLitSupported fe)`
(and `wf.contains c && (← natLitSupported fe)`), and `do`-notation hoists the `(← …)` out of the
`&&`, so the twin runs `natLitSupported` (which may intern the type `Nat`) whether or not the name
test succeeds; the L code used to skip it (whnf-delta2: it now calls it first, to keep the arena
equal to the twin's; the cost is three `env_find`s per level-less constant application). The body
after the application test is `reduce_nat_head`, whose arms are `reduce_nat_k` / `reduce_nat_ap`, and
those `reduce_nat_succ`, `reduce_nat_op`, `reduce_nat_wf` (behaviour-preserving splits,
whnf-delta2). -/
-- con-ron: ConRon/Arena/Core.lean:1223-1277 ConRon.Arena.reduceNat
@[l_impl ConRon.Arena.reduceNat]
def reduceNatL : FunDecl :=
  lfn (mode, vis, d, e) locals (t, i, f, b, rf, rh) {
  if e >> 28 != 4 { return (0, 0) };
  t := ⟦e⟧.tier;
  i := ⟦e⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if APP⟨t⟩.count <= i { abort };
  f := APP⟨t, i⟩.f;
  b := APP⟨t, i⟩.a;
  (rf, rh) := call reduce_nat_head(mode, vis, d, f, b);
  return (rf, rh)
}

/-- `whnf_step(mode, vis, d, e)`: one iteration of the reduction loop (`decStep`): head-normalize
without delta, try literal acceleration, unfold one definition. -/
-- con-ron: ConRon/Arena/Core.lean:2405-2420 ConRon.Arena.whnfStep
@[l_impl ConRon.Arena.whnfStep]
def whnfStepL : FunDecl := lfn (mode, vis, d, e) locals (e1, fl, e2, fl2, e3) {
  e1 := call whnf_core(mode, 0, vis, d, e);
  (fl, e2) := call reduce_nat(mode, vis, d, e1);
  if fl != 0 { return (1, e2) };
  (fl2, e3) := call unfold_definition(vis, e1);
  if fl2 != 0 { return (1, e3) };
  return (0, e1)
}

/-- The loop of `whnf_loop`, named for its spec (`WhnfDeltaSlot.lean`). -/
def whnfLoopB : Stmt := lblk (mode, vis, d, e, fl, x) {
  while 0 == 0 {
    (fl, x) := call whnf_step(mode, vis, d, e);
    if fl == 0 { return x };
    e := x
  }
}

/-- `whnf_loop(mode, vis, d, e)`: the reduction loop, iterating `whnf_step` on its own (effectively
unbounded, `2^62`) step budget — an uncounted L `while` (the convention: the twin's loop fuels are
not counted in L, since an L `while` already costs L fuel per iteration). -/
-- con-ron: ConRon/Arena/Core.lean:2433-2436 ConRon.Arena.whnfBody
@[l_impl ConRon.Arena.whnfBody]
def whnfLoopL : FunDecl := lfn (mode, vis, d, e) locals (fl, x) {
  ⟪whnfLoopB⟫;
  abort
}

/-- `whnf(mode, vis, d, e)`: the knot's `whnf` slot. The six stuck tags (`sort`, `fvar`, `lam`,
`forallE`, `lit`; `whnfStuckTag`) return `e` untouched; else the `whnfC` memo at the current
eager bit (the mode's, `((mode >> 1) & 1) << 32`, array 98): a hit returns the stored handle, a miss runs `whnf_loop`,
probes again (the loop may have changed the table) and inserts. -/
-- con-ron: ConRon/Arena/Core.lean:2155-2167 ConRon.Arena.whnfStuckTag
@[l_impl ConRon.Arena.whnfStuckTag]
def whnfL : FunDecl := lfn (mode, vis, d, e) locals (t, fd, j, dd, x, z) {
  t := e >> 28;
  if t == 2 || t == 1 || t == 5 || t == 6 || t == 8 { return e };
  (fd, j, dd) := call wh_find(e, ((mode >> 1) & 1) << 32);
  if fd != 0 { return WH.u64[j * 4 + 3] };
  x := call whnf_loop(mode, vis, d, e);
  (fd, j, dd) := call wh_find(e, ((mode >> 1) & 1) << 32);
  z := call wh_put(e, ((mode >> 1) & 1) << 32, x, fd, j);
  return x
}

/-! ## The program -/

/-- What the specs in this file need of a program: this file's own sixteen functions, and the
external functions they call by name (`whnf_core` is the one callee covered instead by `KnotOK`,
since it is the knot's own slot and its L code is another agent's). -/
structure WhnfDeltaProg (p : Prog) : Prop where
  whnf : p.lookup "whnf" = some whnfL
  whnfLoop : p.lookup "whnf_loop" = some whnfLoopL
  whnfStep : p.lookup "whnf_step" = some whnfStepL
  reduceNat : p.lookup "reduce_nat" = some reduceNatL
  reduceNatHead : p.lookup "reduce_nat_head" = some reduceNatHeadL
  reduceNatK : p.lookup "reduce_nat_k" = some reduceNatKL
  reduceNatAp : p.lookup "reduce_nat_ap" = some reduceNatApL
  reduceNatSucc : p.lookup "reduce_nat_succ" = some reduceNatSuccL
  reduceNatOp : p.lookup "reduce_nat_op" = some reduceNatOpL
  reduceNatWf : p.lookup "reduce_nat_wf" = some reduceNatWfL
  natOpIsWf : p.lookup "nat_op_is_wf" = some natOpIsWfL
  natBinOpName : p.lookup "nat_bin_op_name" = some natBinOpNameL
  natOpStored : p.lookup "nat_op_stored" = some natOpStoredL
  rawNatLit : p.lookup "raw_nat_lit" = some rawNatLitL
  natLitSupported : p.lookup "nat_lit_supported" = some natLitSupportedL
  natIndOk : p.lookup "nat_ind_ok" = some natIndOkL
  natZeroOk : p.lookup "nat_zero_ok" = some natZeroOkL
  natSuccOk : p.lookup "nat_succ_ok" = some natSuccOkL
  constE : p.lookup "const_e" = some constEL
  natLitToCtor : p.lookup "nat_lit_to_ctor" = some natLitToCtorL
  natSuccLit : p.lookup "nat_succ_lit" = some natSuccLitL
  litToCtorIfNat : p.lookup "lit_to_ctor_if_nat" = some litToCtorIfNatL
  unfoldDefinition : p.lookup "unfold_definition" = some unfoldDefinitionL
  unfoldDefnAt : p.lookup "unfold_defn_at" = some unfoldDefnAtL
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
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb : Word)
    (ok : List Word → Prop)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (hok : AM.ok T a₀) (hst : AM.st T a₀ = a₀)
    (htrip : ⦃fun s => s = s₀⦄
      invoke p (exec p n) f args
      ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ AM.res T a₀ = dec r ∧ ok r; ⊤⦄) :
    CoreSpec p n f args T dec s₀ a₀ dn vis fe MM eb ok := by
  apply L.M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hmem, hres, hokr⟩ := L.M.of_run (P := fun s => s = s₀) hs hrun htrip
  subst hs
  refine ⟨hloc, hok, ⟨MM, ?_, KeptAll.refl _ _, ?_⟩, hres, hokr⟩
  · rw [hst, hmem]; exact hC
  · rw [hmem]; exact StackKept.refl _

/-! ## The specs

Plain `CoreSpec` for every function that neither calls the knot nor loops; a named, `F`-quantified
(and, for `whnf_loop`, additionally loop-fuel-`K`-quantified) `Prop` for the three that call
`whnf`/`whnf_core`, in `WhnfCoreSlot`/`WhnfSlot`'s own shape; `whnf` itself is `WhnfSlot` (already
in `WhnfBase.lean`). `nat_bin_op_name` is proved here (`CoreSpec.of_pure` plus the
`natOpResult_sel` recipe of `PinsNatOp.lean`); the others in `WhnfDeltaRefine*.lean`. -/

section specs
variable (p : Prog) (hp : WhnfDeltaProg p)

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
      (r.headD 0 != 0) = natBinOpSel (pinW s₀.mem) c ∧ HW (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, natBinOpNameL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [natBinOpSel, pinW_eq, HW]

/-- **`nat_bin_op_name` refines `natBinOpName`.** `hflag` (the pin table's filled flag) is not
literally one of `PinsFull`'s own fields (`Tiers.lean`'s `PinsR.full : pinW m 0 ≠ 0 → PinsFull m
p` is the unlock, not a consequence), so it is taken here as a hypothesis; a core driver fills the
pins once, before any core function runs, so every real call site has it (`pinsReady`). -/
@[refines ConRon.Arena.natBinOpName]
theorem natBinOpName_refines (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb c : Word)
    (hC : CoreS dn s₀.mem a₀ vis fe MM eb) (hc : HW c) (hflag : pinW s₀.mem 0 ≠ 0) :
    CoreSpec p n "nat_bin_op_name" [c] (natBinOpName (decI c)) decBool s₀ a₀ dn vis fe MM eb := by
  have hrun := natBinOpName_run hC.pins c hc
  apply CoreSpec.of_pure p n "nat_bin_op_name" [c] (natBinOpName (decI c)) decBool s₀ a₀ dn vis fe
    MM eb ResH hC
  · simp [AM.ok, hrun]
  · simp [AM.st, hrun]
  · apply M.triple_of_run
    intro s r s' hs hrun'
    obtain ⟨hmem, hloc, heq, hhw⟩ := L.M.of_run (P := fun s => s = s₀) hs hrun'
      (natBinOpNameL_spec p hp.natBinOpName n s₀ hflag c)
    subst hs
    refine ⟨hloc, hmem, ?_, hhw⟩
    simp only [AM.res, hrun, decBool]
    rw [← heq]

/-- `reduce_nat(mode, vis, d, e)` refines `reduceNat` at every knot fuel `F ≥ n`, given the knot's
`whnf` slot at L-fuel `n` (`KnotOK`). -/
def ReduceNatSpec (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d e : Word), n ≤ F → SlotPre s₀ a₀ dn vis fe MM eb mode → HW e →
    KnotUpTo p n →
    CoreSpec p n "reduce_nat" [mode, vis, d, e]
      (reduceNat (coreKnot (decMode mode) fe id F) fe d.toNat (decE e)) decOptR s₀ a₀ dn vis fe MM eb
      ResW

/-- `whnf_step(mode, vis, d, e)` refines `whnfStep` at every knot fuel `F ≥ n`, given `KnotUpTo p n`
(its `r.whnfCore false depth e` is `call whnf_core(mode, 0, vis, d, e)`, its `r.whnf` calls are
`reduce_nat`'s). -/
def WhnfStepSpec (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d e : Word), n ≤ F → SlotPre s₀ a₀ dn vis fe MM eb mode → HW e →
    KnotUpTo p n →
    CoreSpec p n "whnf_step" [mode, vis, d, e]
      (whnfStep (coreKnot (decMode mode) fe id F) fe d.toNat (decE e)) decStep s₀ a₀ dn vis fe MM eb
      ResW

/-- `whnf_loop(mode, vis, d, e)` refines `whnfLoop` at every knot fuel `F ≥ n` and every loop fuel
`K ≥ n` (the lead's shape for the `2 ^ 62` loop fuels: `whnf_loop` refines `whnfLoop` directly,
generalized over the loop-fuel argument, so that `whnf`'s own theorem can instantiate it at
`K = whnfLoopFuel` under `n ≤ 2 ^ 62`). -/
def WhnfLoopSpec (p : Prog) (n : Nat) : Prop :=
  ∀ (F K : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d e : Word), n ≤ F → n ≤ K → SlotPre s₀ a₀ dn vis fe MM eb mode →
    HW e → KnotUpTo p n →
    CoreSpec p n "whnf_loop" [mode, vis, d, e]
      (whnfLoop (coreKnot (decMode mode) fe id F) fe d.toNat K (decE e)) decH s₀ a₀ dn vis fe MM eb

/- `whnf_loop` refines `whnfLoop` and `whnf` refines the knot's `whnf` slot: proved in
`WhnfDeltaSlot.lean` (imports this file and `WhnfCoreSlot.lean`), exactly as `WhnfCoreSlot.lean`
proves `whnf_core`/`whnf_core_loop`. -/

end specs

end L.Arena
