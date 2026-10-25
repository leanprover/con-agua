import ConAgua.Arena.Reasons
import ConAgua.Arena.DeclArmsCanon
import ConAgua.Arena.Globals

/-!
# `checkDecl`'s one-constant arms in L, part 2: the certified `Nat` operations (lane `decls2`)

The twin's structural-`Nat` gate (`Core.lean`: `natOpNames`, `natDivModNames`, `natOpDeps`,
`natOpGuard`, `natOpStoredOk`, `natOpEquations`, `substConst0`, `substConstAll`;
`DeclCheck.lean`: `natOpStoredOkAll`, `substConst0Pairs`, `certifyNatEqs`) and the
`Nat.div`-family pin gate (`DeclCheck.lean`: `divModCertStmts` and its eleven pieces,
`divModCertApplied`, the guards, `checkDivModCerts`, `checkDivModPinAt`, `checkDivModPinLoop`,
`checkDivModPin`), on lane `induct`'s conventions.

* The pinned names are `pin_at` reads (`PIN_*` slots of `vendor/con-ron/ConRon/Arena/Pins.lean`);
  the name lists (`natOpNames`, …) are `IW` slices built from them, so a pin read fails where the
  twin's does.
* `List (EIdx × EIdx)` (the recurrence equations) is an `IW` slice of pointers to 2-word records
  `[lhs, rhs]`; `List (List EIdx × EIdx)` (the certificate statements) of pointers to 3-word
  records `[hyps.off, hyps.len, eq]`.
* `CertCtxA` is a 21-word `IW` record, the fields in the twin's order: `natTy, x, y, one, bleN,
  boolTy, bT, bF, z, two, modN, divN, addN, mulN, subN, gcdN, slN, srN, landN, lorN, xorN`.
* **A pin variant** (`INatOpPinSet`, the ROM's, lane lead) is an `EREC` record of 24 words: the
  eight pins `divPin, modPin, gcdPin, landPin, lorPin, xorPin, shiftLeftPin, shiftRightPin`, then
  the eight proof lists as `EREC` slices `(off, len)` in the same order (`toolchain` is only in
  the decline message, not kept). The variant list is the `IW` slice `rom_pin_sets()` returns.
* **No recovery** (L recovers nowhere): the twin's `orElseAttempt` resumes after an error inside one
  variant's attempt (`checkDivModPinAt`) and tries the next variant; L aborts there, with the class
  bits of a reject or decline cleared (`ATT`, `Arena/Globals.lean`). That is an error where the twin may still accept through a later variant: a completeness loss, never a
  soundness one. With the ROM's empty variant list (`romPins = []`) the loop declines at once in
  both.
-/

namespace L.Ind

open L.Arena

/-! ## The name lists -/

/-- `nat_op_names()`: `natOpNames` (`pred, add, sub, mul, pow, beq, ble`), an `IW` slice. -/
-- con-ron: ConRon/Arena/Core.lean:876-882 ConRon.Arena.natOpNames
@[l_impl ConRon.Arena.natOpNames]
def natOpNamesL : FunDecl := lfn () locals (a, b, c, d, e, f, g, q) {
  a := call pin_at(14); b := call pin_at(15); c := call pin_at(16); d := call pin_at(17);
  e := call pin_at(18); f := call pin_at(19); g := call pin_at(20);
  q := call iw_alloc(7);
  IW.u64[q] := a; IW.u64[q + 1] := b; IW.u64[q + 2] := c; IW.u64[q + 3] := d;
  IW.u64[q + 4] := e; IW.u64[q + 5] := f; IW.u64[q + 6] := g;
  return (q, 7)
}

/-- `nat_div_mod_names()`: `natDivModNames` (`div, mod, gcd, land, lor, xor, shiftLeft,
shiftRight`), an `IW` slice. -/
-- con-ron: ConRon/Arena/Core.lean:884-890 ConRon.Arena.natDivModNames
@[l_impl ConRon.Arena.natDivModNames]
def natDivModNamesL : FunDecl := lfn () locals (a, b, c, d, e, f, g, h, q) {
  a := call pin_at(21); b := call pin_at(22); c := call pin_at(23); d := call pin_at(24);
  e := call pin_at(25); f := call pin_at(26); g := call pin_at(27); h := call pin_at(28);
  q := call iw_alloc(8);
  IW.u64[q] := a; IW.u64[q + 1] := b; IW.u64[q + 2] := c; IW.u64[q + 3] := d;
  IW.u64[q + 4] := e; IW.u64[q + 5] := f; IW.u64[q + 6] := g; IW.u64[q + 7] := h;
  return (q, 8)
}

/-- `nat_op_pins_a(q)`: the pin slots `14‥21` (`pred, add, sub, mul, pow, beq, ble, div`) into
`IW[q‥q+7]`. -/
-- con-ron: ConRon/Arena/Core.lean:892-915 ConRon.Arena.natOpDeps
def natOpPinsAL : FunDecl := lfn (q) locals (a, b, c, d, e, f, g, h) {
  a := call pin_at(14); b := call pin_at(15); c := call pin_at(16); d := call pin_at(17);
  e := call pin_at(18); f := call pin_at(19); g := call pin_at(20); h := call pin_at(21);
  IW.u64[q] := a; IW.u64[q + 1] := b; IW.u64[q + 2] := c; IW.u64[q + 3] := d;
  IW.u64[q + 4] := e; IW.u64[q + 5] := f; IW.u64[q + 6] := g; IW.u64[q + 7] := h;
  return 0
}

/-- `nat_op_pins_b(q)`: the pin slots `22‥28` (`mod, gcd, land, lor, xor, shiftLeft,
shiftRight`) into `IW[q‥q+6]`. -/
-- con-ron: ConRon/Arena/Core.lean:892-915 ConRon.Arena.natOpDeps
def natOpPinsBL : FunDecl := lfn (q) locals (a, b, c, d, e, f, g) {
  a := call pin_at(22); b := call pin_at(23); c := call pin_at(24); d := call pin_at(25);
  e := call pin_at(26); f := call pin_at(27); g := call pin_at(28);
  IW.u64[q] := a; IW.u64[q + 1] := b; IW.u64[q + 2] := c; IW.u64[q + 3] := d;
  IW.u64[q + 4] := e; IW.u64[q + 5] := f; IW.u64[q + 6] := g;
  return 0
}

/-- `nat_op_pins_c(q)`: the pin slots `1, 2, 3, 30, 31, 29` (`Nat, Nat.zero, Nat.succ,
Bool.true, Bool.false, Bool`) into `IW[q‥q+5]`. -/
-- con-ron: ConRon/Arena/Core.lean:929-992 ConRon.Arena.natOpEquations
def natOpPinsCL : FunDecl := lfn (q) locals (a, b, c, d, e, f) {
  a := call pin_at(1); b := call pin_at(2); c := call pin_at(3); d := call pin_at(30);
  e := call pin_at(31); f := call pin_at(29);
  IW.u64[q] := a; IW.u64[q + 1] := b; IW.u64[q + 2] := c; IW.u64[q + 3] := d;
  IW.u64[q + 4] := e; IW.u64[q + 5] := f;
  return 0
}

/-- `nat_op_pins()`: the names the structural-`Nat` gate reads (the twin reads all fifteen
operation pins at once, `natOpDeps`' and `natOpEquations`' opening lines), as a 21-word `IW`
record: words `0‥14` the slots `14‥28`, then `Nat`, `Nat.zero`, `Nat.succ`, `Bool.true`,
`Bool.false`, `Bool` (words `15‥20`). A pin read changes no state and cannot fail once one has
succeeded, so reading them up front is the twin's behaviour; the split keeps each proof small. -/
-- con-ron: ConRon/Arena/Core.lean:892-915 ConRon.Arena.natOpDeps
def natOpPinsL : FunDecl := lfn () locals (q, u) {
  q := call iw_alloc(21);
  u := call nat_op_pins_a(q);
  u := call nat_op_pins_b(q + 8);
  u := call nat_op_pins_c(q + 15);
  return q
}

/-- `nat_op_deps(c)`: `natOpDeps c`, an `IW` slice. -/
-- con-ron: ConRon/Arena/Core.lean:892-915 ConRon.Arena.natOpDeps
@[l_impl ConRon.Arena.natOpDeps]
def natOpDepsL : FunDecl :=
    lfn (c) locals (pi, pr, ad, su, mu, po, be, bl, di, mo, gc, la, lo, xo, sl, sr, q) {
  pi := call nat_op_pins();
  pr := IW.u64[pi + 0]; ad := IW.u64[pi + 1]; su := IW.u64[pi + 2]; mu := IW.u64[pi + 3]; po := IW.u64[pi + 4]; be := IW.u64[pi + 5]; bl := IW.u64[pi + 6]; di := IW.u64[pi + 7]; mo := IW.u64[pi + 8]; gc := IW.u64[pi + 9]; la := IW.u64[pi + 10]; lo := IW.u64[pi + 11]; xo := IW.u64[pi + 12]; sl := IW.u64[pi + 13]; sr := IW.u64[pi + 14];
  if c == pr {
    q := call iw_alloc(1); IW.u64[q + 0] := pr;
    return (q, 1)
  };
  if c == ad {
    q := call iw_alloc(1); IW.u64[q + 0] := ad;
    return (q, 1)
  };
  if c == su {
    q := call iw_alloc(2); IW.u64[q + 0] := pr; IW.u64[q + 1] := su;
    return (q, 2)
  };
  if c == mu {
    q := call iw_alloc(2); IW.u64[q + 0] := ad; IW.u64[q + 1] := mu;
    return (q, 2)
  };
  if c == po {
    q := call iw_alloc(3); IW.u64[q + 0] := ad; IW.u64[q + 1] := mu; IW.u64[q + 2] := po;
    return (q, 3)
  };
  if c == be {
    q := call iw_alloc(1); IW.u64[q + 0] := be;
    return (q, 1)
  };
  if c == bl {
    q := call iw_alloc(1); IW.u64[q + 0] := bl;
    return (q, 1)
  };
  if c == di {
    q := call iw_alloc(4); IW.u64[q + 0] := pr; IW.u64[q + 1] := su; IW.u64[q + 2] := bl; IW.u64[q + 3] := di;
    return (q, 4)
  };
  if c == mo {
    q := call iw_alloc(4); IW.u64[q + 0] := pr; IW.u64[q + 1] := su; IW.u64[q + 2] := bl; IW.u64[q + 3] := mo;
    return (q, 4)
  };
  if c == gc {
    q := call iw_alloc(3); IW.u64[q + 0] := bl; IW.u64[q + 1] := mo; IW.u64[q + 2] := gc;
    return (q, 3)
  };
  if c == la {
    q := call iw_alloc(6); IW.u64[q + 0] := ad; IW.u64[q + 1] := mu; IW.u64[q + 2] := bl; IW.u64[q + 3] := di; IW.u64[q + 4] := mo; IW.u64[q + 5] := la;
    return (q, 6)
  };
  if c == lo {
    q := call iw_alloc(7); IW.u64[q + 0] := ad; IW.u64[q + 1] := su; IW.u64[q + 2] := mu; IW.u64[q + 3] := bl; IW.u64[q + 4] := di; IW.u64[q + 5] := mo; IW.u64[q + 6] := lo;
    return (q, 7)
  };
  if c == xo {
    q := call iw_alloc(6); IW.u64[q + 0] := ad; IW.u64[q + 1] := mu; IW.u64[q + 2] := bl; IW.u64[q + 3] := di; IW.u64[q + 4] := mo; IW.u64[q + 5] := xo;
    return (q, 6)
  };
  if c == sl {
    q := call iw_alloc(4); IW.u64[q + 0] := su; IW.u64[q + 1] := mu; IW.u64[q + 2] := bl; IW.u64[q + 3] := sl;
    return (q, 4)
  };
  if c == sr {
    q := call iw_alloc(4); IW.u64[q + 0] := su; IW.u64[q + 1] := bl; IW.u64[q + 2] := di; IW.u64[q + 3] := sr;
    return (q, 4)
  };
  return (0, 0)
}

/-! ## The structural gate -/

/-- `nat_op_deps_stored(vis, o, l)`: every name of the slice is stored as a level-monomorphic
definition. -/
-- con-ron: ConRon/Arena/Core.lean:1037-1046 ConRon.Arena.natOpDepsStored
@[l_impl ConRon.Arena.natOpDepsStored]
def natOpDepsStoredL : FunDecl := lfn (vis, o, l) locals (f, r, e) {
  if l == 0 { return 1 };
  (f, r) := call env_find(IW.u64[o], vis);
  if f == 0 { return 0 };
  if EREC.u64[r] != 1 { return 0 };
  if EREC.u64[r + 3] != 0 { return 0 };
  e := call nat_op_deps_stored(vis, o + 1, l - 1);
  return e
}

/-- `bool_ctor_ok(p)`: the stored `Bool` constructor `p` is level-free, at the type `Bool`. -/
-- con-ron: ConRon/Arena/Core.lean:1048-1058 ConRon.Arena.boolCtorOk
-- con-ron: CHANGED since 12752ca7 — `ConRon.Arena.boolCtorOk` changed; re-check the L code and its proofs, then delete this line
@[l_impl ConRon.Arena.boolCtorOk]
def boolCtorOkL : FunDecl := lfn (p) locals (q, n, b) {
  q := call ci_to_cv(p);
  if EREC.u64[q + 2] != 0 { return 0 };
  n := call pin_at(29);
  b := call const_e(n);
  return u64(EREC.u64[q + 3] == b)
}

/-- `nat_op_bool_ctors(vis)`: the `Bool` constructors' conjunct of `natOpGuard`: `Bool.true` then
`Bool.false` stored, level-free, at the type `Bool` (`boolCtorOk`). -/
-- con-ron: ConRon/Arena/Core.lean:1060-1084 ConRon.Arena.natOpGuard
def natOpBoolCtorsL : FunDecl := lfn (vis) locals (bt, f, r, ok, bf) {
  bt := call pin_at(30);
  (f, r) := call env_find(bt, vis);
  if f == 0 { return 0 };
  ok := call bool_ctor_ok(r);
  if ok == 0 { return 0 };
  bf := call pin_at(31);
  (f, r) := call env_find(bf, vis);
  if f == 0 { return 0 };
  ok := call bool_ctor_ok(r);
  return ok
}

/-- `nat_op_guard(vis, c)`: `natOpGuard fe c`. -/
-- con-ron: ConRon/Arena/Core.lean:1060-1084 ConRon.Arena.natOpGuard
@[l_impl ConRon.Arena.natOpGuard]
def natOpGuardL : FunDecl := lfn (vis, c) locals (s, o, l, d, be, bl, mo, ml, m, ok) {
  s := call nat_lit_supported(vis);
  if s == 0 { return 0 };
  (o, l) := call nat_op_deps(c);
  d := call nat_op_deps_stored(vis, o, l);
  if d == 0 { return 0 };
  be := call pin_at(19);
  bl := call pin_at(20);
  (mo, ml) := call nat_div_mod_names();
  m := call sl_contains(mo, ml, c);
  if c == be || c == bl || m != 0 {
    ok := call nat_op_bool_ctors(vis);
    return ok
  };
  return 1
}

/-- `nat_op_cod(vis, c, e)`: `natOpCod`: `Bool` (stored at `Sort 1`) for the comparisons, `Nat`
otherwise. -/
-- con-ron: ConRon/Arena/Core.lean:1142-1161 ConRon.Arena.natOpCod
-- con-ron: CHANGED since 12752ca7 — `ConRon.Arena.natOpCod` changed; re-check the L code and its proofs, then delete this line
@[l_impl ConRon.Arena.natOpCod]
def natOpCodL : FunDecl := lfn (vis, c, e) locals (be, bl, bn, bc, f, r, q, s1, nn, nc) {
  be := call pin_at(19);
  bl := call pin_at(20);
  if c == be || c == bl {
    bn := call pin_at(29);
    bc := call const_e(bn);
    if e != bc { return 0 };
    (f, r) := call env_find(bn, vis);
    if f == 0 { return 0 };
    q := call ci_to_cv(r);
    s1 := call pin_word(54);
    if EREC.u64[q + 2] != 0 { return 0 };
    return u64(EREC.u64[q + 3] == s1)
  };
  nn := call pin_at(1);
  nc := call const_e(nn);
  return u64(e == nc)
}

/-- `nat_op_ty_pinned(vis, c, ty)`: `natOpTyPinned`: `Nat → cod` for `pred`, `Nat → Nat → cod`
otherwise (the tag tested on the handle before the view, as the twin does). -/
-- con-ron: ConRon/Arena/Core.lean:1163-1189 ConRon.Arena.natOpTyPinned
@[l_impl ConRon.Arena.natOpTyPinned]
def natOpTyPinnedL : FunDecl :=
    lfn (vis, c, ty) locals (nn, nc, pr, t, d, b, z, t2, d2, b2, z2, r) {
  nn := call pin_at(1);
  nc := call const_e(nn);
  pr := call pin_at(14);
  if ty >> 28 != 6 { return 0 };
  (t, d, b, z) := call e_view(ty);
  if t != 6 { return 0 };
  if c == pr {
    if d != nc { return 0 };
    r := call nat_op_cod(vis, c, b);
    return r
  };
  if b >> 28 != 6 { return 0 };
  (t2, d2, b2, z2) := call e_view(b);
  if t2 != 6 { return 0 };
  if d != nc || d2 != nc { return 0 };
  r := call nat_op_cod(vis, c, b2);
  return r
}

/-- `nat_op_stored_ok(vis, n)`: `n` is stored as a level-monomorphic definition of the pinned
type. -/
-- con-ron: ConRon/Arena/Core.lean:1191-1197 ConRon.Arena.natOpStoredOk
@[l_impl ConRon.Arena.natOpStoredOk]
def natOpStoredOkL : FunDecl := lfn (vis, n) locals (f, r, e) {
  (f, r) := call env_find(n, vis);
  if f == 0 { return 0 };
  if EREC.u64[r] != 1 { return 0 };
  if EREC.u64[r + 3] != 0 { return 0 };
  e := call nat_op_ty_pinned(vis, n, EREC.u64[r + 4]);
  return e
}

/-- `nat_op_stored_ok_all(vis, o, l)`. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:146-154 ConRon.Arena.natOpStoredOkAll
@[l_impl ConRon.Arena.natOpStoredOkAll]
def natOpStoredOkAllL : FunDecl := lfn (vis, o, l) locals (e) {
  if l == 0 { return 1 };
  e := call nat_op_stored_ok(vis, IW.u64[o]);
  if e == 0 { return 0 };
  e := call nat_op_stored_ok_all(vis, o + 1, l - 1);
  return e
}

/-! ## The recurrence equations -/

/-- `nat_ap1(n, a)`: `const n [] a`. -/
-- con-ron: ConRon/Arena/Core.lean:917-922 ConRon.Arena.natAp1
@[l_impl ConRon.Arena.natAp1]
def natAp1L : FunDecl := lfn (n, a) locals (f, r) {
  f := call const_e(n);
  r := call mk_app(f, a);
  return r
}

/-- `nat_ap2(n, a, b)`: `const n [] a b`. -/
-- con-ron: ConRon/Arena/Core.lean:924-927 ConRon.Arena.natAp2
@[l_impl ConRon.Arena.natAp2]
def natAp2L : FunDecl := lfn (n, a, b) locals (f, r) {
  f := call nat_ap1(n, a);
  r := call mk_app(f, b);
  return r
}

/-- `nat_eq_list2(a1, b1, a2, b2)`: the two-equation list `[(a1, b1), (a2, b2)]`. -/
-- con-ron: ConRon/Arena/Core.lean:929-992 ConRon.Arena.natOpEquations
def natEqList2 : FunDecl := lfn (a1, b1, a2, b2) locals (q, p1, p2) {
  p1 := call rec2(a1, b1);
  p2 := call rec2(a2, b2);
  q := call iw_alloc(2);
  IW.u64[q] := p1;
  IW.u64[q + 1] := p2;
  return (q, 2)
}

/-- `nat_eq_list3(a1, b1, a2, b2, a3, b3)`: the three-equation list. -/
-- con-ron: ConRon/Arena/Core.lean:929-992 ConRon.Arena.natOpEquations
def natEqList3 : FunDecl := lfn (a1, b1, a2, b2, a3, b3) locals (q, p1, p2, p3) {
  p1 := call rec2(a1, b1);
  p2 := call rec2(a2, b2);
  p3 := call rec2(a3, b3);
  q := call iw_alloc(3);
  IW.u64[q] := p1; IW.u64[q + 1] := p2; IW.u64[q + 2] := p3;
  return (q, 3)
}

/-- `nat_eq_list4(a1, b1, a2, b2, a3, b3, a4, b4)`: the four-equation list. -/
-- con-ron: ConRon/Arena/Core.lean:929-992 ConRon.Arena.natOpEquations
def natEqList4 : FunDecl :=
    lfn (a1, b1, a2, b2, a3, b3, a4, b4) locals (q, p1, p2, p3, p4) {
  p1 := call rec2(a1, b1);
  p2 := call rec2(a2, b2);
  p3 := call rec2(a3, b3);
  p4 := call rec2(a4, b4);
  q := call iw_alloc(4);
  IW.u64[q] := p1; IW.u64[q + 1] := p2; IW.u64[q + 2] := p3; IW.u64[q + 3] := p4;
  return (q, 4)
}

/-- `nat_eq_pr(c, z, x, sx)`: `Nat.pred`'s equations `pred 0 = 0`, `pred (succ x) = x`. -/
-- con-ron: ConRon/Arena/Core.lean:929-992 ConRon.Arena.natOpEquations
def natEqPr : FunDecl := lfn (c, z, x, sx) locals (l1, l2, q, u) {
  l1 := call nat_ap1(c, z);
  l2 := call nat_ap1(c, sx);
  (q, u) := call nat_eq_list2(l1, z, l2, x);
  return (q, 2)
}

/-- `nat_eq_un(c, x, y, z, sy, w)`: `add`'s and `sub`'s equations: `c x 0 = x`,
`c x (succ y) = w (c x y)` (`w` the successor for `add`, the predecessor for `sub`). -/
-- con-ron: ConRon/Arena/Core.lean:929-992 ConRon.Arena.natOpEquations
def natEqUn : FunDecl := lfn (c, x, y, z, sy, w) locals (l1, l2, r3, r2, q, u) {
  l1 := call nat_ap2(c, x, z);
  l2 := call nat_ap2(c, x, sy);
  r3 := call nat_ap2(c, x, y);
  r2 := call nat_ap1(w, r3);
  (q, u) := call nat_eq_list2(l1, x, l2, r2);
  return (q, 2)
}

/-- `nat_eq_mu(c, x, y, z, sy, ad)`: `mul`'s equations. -/
-- con-ron: ConRon/Arena/Core.lean:929-992 ConRon.Arena.natOpEquations
def natEqMu : FunDecl := lfn (c, x, y, z, sy, ad) locals (l1, l2, r3, r2, q, u) {
  l1 := call nat_ap2(c, x, z);
  l2 := call nat_ap2(c, x, sy);
  r3 := call nat_ap2(c, x, y);
  r2 := call nat_ap2(ad, r3, x);
  (q, u) := call nat_eq_list2(l1, z, l2, r2);
  return (q, 2)
}

/-- `nat_eq_po(c, x, y, z, sy, sN, mu)`: `pow`'s equations. -/
-- con-ron: ConRon/Arena/Core.lean:929-992 ConRon.Arena.natOpEquations
def natEqPo : FunDecl := lfn (c, x, y, z, sy, sN, mu) locals (l1, sz, l2, r3, r2, q, u) {
  l1 := call nat_ap2(c, x, z);
  sz := call nat_ap1(sN, z);
  l2 := call nat_ap2(c, x, sy);
  r3 := call nat_ap2(c, x, y);
  r2 := call nat_ap2(mu, r3, x);
  (q, u) := call nat_eq_list2(l1, sz, l2, r2);
  return (q, 2)
}

/-- `nat_eq_be(c, x, y, z, sx, sy, bT, bF)`: `Nat.beq`'s four equations. -/
-- con-ron: ConRon/Arena/Core.lean:929-992 ConRon.Arena.natOpEquations
def natEqBe : FunDecl := lfn (c, x, y, z, sx, sy, bT, bF) locals (l1, l2, l3, l4, r4, q, u) {
  l1 := call nat_ap2(c, z, z);
  l2 := call nat_ap2(c, z, sy);
  l3 := call nat_ap2(c, sx, z);
  l4 := call nat_ap2(c, sx, sy);
  r4 := call nat_ap2(c, x, y);
  (q, u) := call nat_eq_list4(l1, bT, l2, bF, l3, bF, l4, r4);
  return (q, 4)
}

/-- `nat_eq_bl(c, x, y, z, sx, sy, bT, bF)`: `Nat.ble`'s three equations. -/
-- con-ron: ConRon/Arena/Core.lean:929-992 ConRon.Arena.natOpEquations
def natEqBl : FunDecl := lfn (c, x, y, z, sx, sy, bT, bF) locals (l1, l2, l3, r3, q, u) {
  l1 := call nat_ap2(c, z, y);
  l2 := call nat_ap2(c, sx, z);
  l3 := call nat_ap2(c, sx, sy);
  r3 := call nat_ap2(c, x, y);
  (q, u) := call nat_eq_list3(l1, bT, l2, bF, l3, r3);
  return (q, 3)
}

/-- `nat_eq_ctx(pi, d)`: the terms `natOpEquations` builds before it dispatches, in its order: `x :=
fvar d`, `y := fvar (d + 1)` at `Nat`, `Nat.zero`, `Nat.succ`'s name, `succ x`, `succ y`,
`Bool.true`, `Bool.false`, as an 8-word `IW` record `[x, y, z, sN, sx, sy, bT, bF]`. -/
-- con-ron: ConRon/Arena/Core.lean:929-992 ConRon.Arena.natOpEquations
def natEqCtx : FunDecl := lfn (pi, d) locals (nN, natTy, x, y, zN, z, sN, sx, sy, u, bT, bF, q) {
  nN := IW.u64[pi + 15];
  natTy := call const_e(nN);
  x := call intern_fvar(d, natTy);
  y := call intern_fvar(d + 1, natTy);
  zN := IW.u64[pi + 16];
  z := call const_e(zN);
  sN := IW.u64[pi + 17];
  sx := call nat_ap1(sN, x);
  sy := call nat_ap1(sN, y);
  u := IW.u64[pi + 18];
  bT := call const_e(u);
  u := IW.u64[pi + 19];
  bF := call const_e(u);
  q := call iw_alloc(8);
  IW.u64[q] := x; IW.u64[q + 1] := y; IW.u64[q + 2] := z; IW.u64[q + 3] := sN;
  IW.u64[q + 4] := sx; IW.u64[q + 5] := sy; IW.u64[q + 6] := bT; IW.u64[q + 7] := bF;
  return q
}

/-- `nat_eq_disp(c, pi, cx)`: the dispatch of `natOpEquations` over the seven operations, from the
pin record `pi` and the term record `cx`. -/
-- con-ron: ConRon/Arena/Core.lean:929-992 ConRon.Arena.natOpEquations
def natEqDisp : FunDecl := lfn (c, pi, cx) locals (q, l) {
  if c == IW.u64[pi] { (q, l) := call nat_eq_pr(c, IW.u64[cx + 2], IW.u64[cx], IW.u64[cx + 4]); return (q, l) };
  if c == IW.u64[pi + 1] { (q, l) := call nat_eq_un(c, IW.u64[cx], IW.u64[cx + 1], IW.u64[cx + 2], IW.u64[cx + 5], IW.u64[cx + 3]); return (q, l) };
  if c == IW.u64[pi + 2] { (q, l) := call nat_eq_un(c, IW.u64[cx], IW.u64[cx + 1], IW.u64[cx + 2], IW.u64[cx + 5], IW.u64[pi]); return (q, l) };
  if c == IW.u64[pi + 3] { (q, l) := call nat_eq_mu(c, IW.u64[cx], IW.u64[cx + 1], IW.u64[cx + 2], IW.u64[cx + 5], IW.u64[pi + 1]); return (q, l) };
  if c == IW.u64[pi + 4] { (q, l) := call nat_eq_po(c, IW.u64[cx], IW.u64[cx + 1], IW.u64[cx + 2], IW.u64[cx + 5], IW.u64[cx + 3], IW.u64[pi + 3]); return (q, l) };
  if c == IW.u64[pi + 5] { (q, l) := call nat_eq_be(c, IW.u64[cx], IW.u64[cx + 1], IW.u64[cx + 2], IW.u64[cx + 4], IW.u64[cx + 5], IW.u64[cx + 6], IW.u64[cx + 7]); return (q, l) };
  if c == IW.u64[pi + 6] { (q, l) := call nat_eq_bl(c, IW.u64[cx], IW.u64[cx + 1], IW.u64[cx + 2], IW.u64[cx + 4], IW.u64[cx + 5], IW.u64[cx + 6], IW.u64[cx + 7]); return (q, l) };
  return (0, 0)
}

/-- `nat_op_equations(d, c)`: `natOpEquations d c`, the equations of the seven structural
operations over `x := fvar d`, `y := fvar (d + 1)` (every pin read first, as the twin does). -/
-- con-ron: ConRon/Arena/Core.lean:929-992 ConRon.Arena.natOpEquations
@[l_impl ConRon.Arena.natOpEquations]
def natOpEquationsL : FunDecl :=
    lfn (d, c) locals (pi, cx, q, l) {
  pi := call nat_op_pins();
  cx := call nat_eq_ctx(pi, d);
  (q, l) := call nat_eq_disp(c, pi, cx);
  return (q, l)
}

/-- `defn_nat_cert(vis, w, n)`: the stored value of `n` at the extended view `w` (a definition),
its recurrences (`nat_op_equations 0 n`) with `n` replaced by the value, certified at the
pre-insertion view `vis`. Returns `0`. -/
-- con-ron: ConRon/Arena/CheckDecl.lean:82-214 ConRon.Arena.checkDecl
def defnNatCert : FunDecl :=
    lfn (vis, w, n) locals (f, r, eo, el, so, sl, ok) {
  (f, r) := call env_find(n, w);
  if f == 0 { abort };
  if EREC.u64[r] != 1 { abort };
  (eo, el) := call nat_op_equations(0, n);
  (so, sl) := call subst_const0_pairs(n, EREC.u64[r + 5], eo, el);
  ok := call certify_nat_eqs(vis, so, sl);
  if ok == 0 { fail R_NONSTANDARD_STRUCTURAL_NAT };
  return 0
}

/-- `subst_const0(n, r, fuel, h)`: `Expr.substConst0`: `.const n []` replaced by `r` through an
application spine. -/
-- con-ron: ConRon/Arena/Core.lean:1094-1108 ConRon.Arena.substConst0
@[l_impl ConRon.Arena.substConst0]
def substConst0L : FunDecl := lfn (n, r, fuel, h) locals (t, x, y, z, el, f2, a2, e) {
  if fuel == 0 { abort };
  (t, x, y, z) := call e_view(h);
  if t == 3 {
    el := call pin_word(52);
    if x == n && y == el { return r };
    return h
  };
  if t == 4 {
    f2 := call subst_const0(n, r, fuel - 1, x);
    a2 := call subst_const0(n, r, fuel - 1, y);
    e := call mk_app(f2, a2);
    return e
  };
  return h
}

/-- `subst_const_all(n, r, fuel, h)`: `Expr.substConstAll`: everywhere, under binders too
(`fvar` annotations not entered). -/
-- con-ron: ConRon/Arena/Core.lean:1110-1140 ConRon.Arena.substConstAll
@[l_impl ConRon.Arena.substConstAll]
def substConstAllL : FunDecl := lfn (n, r, fuel, h) locals (t, x, y, z, el, a, b, c, e) {
  if fuel == 0 { abort };
  (t, x, y, z) := call e_view(h);
  if t == 3 {
    el := call pin_word(52);
    if x == n && y == el { return r };
    return h
  };
  if t == 4 {
    a := call subst_const_all(n, r, fuel - 1, x);
    b := call subst_const_all(n, r, fuel - 1, y);
    e := call mk_app(a, b);
    return e
  };
  if t == 5 {
    a := call subst_const_all(n, r, fuel - 1, x);
    b := call subst_const_all(n, r, fuel - 1, y);
    e := call mk_lam(a, b);
    return e
  };
  if t == 6 {
    a := call subst_const_all(n, r, fuel - 1, x);
    b := call subst_const_all(n, r, fuel - 1, y);
    e := call mk_forall(a, b);
    return e
  };
  if t == 7 {
    a := call subst_const_all(n, r, fuel - 1, x);
    b := call subst_const_all(n, r, fuel - 1, y);
    c := call subst_const_all(n, r, fuel - 1, z);
    e := call mk_let(a, b, c);
    return e
  };
  if t == 9 {
    c := call subst_const_all(n, r, fuel - 1, z);
    e := call mk_proj(x, y, c);
    return e
  };
  return h
}

/-- `subst_const0_pairs(n, r, o, l)`: both sides of every equation, then the rest. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:771-779 ConRon.Arena.substConst0Pairs
@[l_impl ConRon.Arena.substConst0Pairs]
def substConst0PairsL : FunDecl := lfn (n, r, o, l) locals (p, a, b, q, ro, rl, so, sl) {
  if l == 0 { return (0, 0) };
  p := IW.u64[o];
  a := call subst_const0(n, r, 4000000000, IW.u64[p]);
  b := call subst_const0(n, r, 4000000000, IW.u64[p + 1]);
  (ro, rl) := call subst_const0_pairs(n, r, o + 1, l - 1);
  q := call rec2(a, b);
  (so, sl) := call sl_cons(q, ro, rl);
  return (so, sl)
}

/-- `certify_nat_eqs(vis, o, l)`: every equation by definitional equality at depth 2. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:760-769 ConRon.Arena.certifyNatEqs
@[l_impl ConRon.Arena.certifyNatEqs]
def certifyNatEqsL : FunDecl := lfn (vis, o, l) locals (p, e) {
  if l == 0 { return 1 };
  p := IW.u64[o];
  e := call is_def_eq_core(vis, 2, IW.u64[p], IW.u64[p + 1]);
  if e == 0 { return 0 };
  e := call certify_nat_eqs(vis, o + 1, l - 1);
  return e
}

/-! ## The `Nat.div` family: a pin variant's fields -/

/-- `div_mod_slot(c)`: the field index of op `c` in a pin variant (`div 0`, `mod 1`, `gcd 2`,
`land 3`, `lor 4`, `xor 5`, `shiftLeft 6`, `shiftRight 7`; anything else `mod`), the names read
in the twin's order and only as far as the twin reads them. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:167-178 ConRon.Arena.divModDeclPin
def divModSlot : FunDecl := lfn (c) locals (x) {
  x := call pin_at(21); if c == x { return 0 };
  x := call pin_at(23); if c == x { return 2 };
  x := call pin_at(24); if c == x { return 3 };
  x := call pin_at(25); if c == x { return 4 };
  x := call pin_at(26); if c == x { return 5 };
  x := call pin_at(27); if c == x { return 6 };
  x := call pin_at(28); if c == x { return 7 };
  return 1
}

/-- `div_mod_decl_pin(ps, c)`: the variant's pinned defining expression of op `c`. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:167-178 ConRon.Arena.divModDeclPin
@[l_impl ConRon.Arena.divModDeclPin]
def divModDeclPinL : FunDecl := lfn (ps, c) locals (j) {
  j := call div_mod_slot(c);
  return EREC.u64[ps + j]
}

/-- `div_mod_cert_proofs(ps, c)`: the variant's certificate proofs of op `c`, copied into `IW`. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:180-191 ConRon.Arena.divModCertProofs
@[l_impl ConRon.Arena.divModCertProofs]
def divModCertProofsL : FunDecl := lfn (ps, c) locals (j, o, l) {
  j := call div_mod_slot(c);
  (o, l) := call er_to_iw(EREC.u64[ps + 8 + 2 * j], EREC.u64[ps + 9 + 2 * j]);
  return (o, l)
}

/-! ## The pinned characterization statements -/

/-- `eq_at1(ty, a, b)`: `Eq.{1} ty a b`. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:225-235 ConRon.Arena.eqAt1
@[l_impl ConRon.Arena.eqAt1]
def eqAt1L : FunDecl := lfn (ty, a, b) locals (z, one, o, l, us, en, e, e1, e2, r) {
  z := call pin_word(53);
  one := call intern_succ(z);
  (o, l) := call sl_new1(one);
  us := call intern_ls_iw(o, l);
  en := call pin_at(0);
  e := call intern_const(en, us);
  e1 := call mk_app(e, ty);
  e2 := call mk_app(e1, a);
  r := call mk_app(e2, b);
  return r
}

/-- `nat_one()`: `Nat.succ Nat.zero`. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:237-242 ConRon.Arena.natOne
@[l_impl ConRon.Arena.natOne]
def natOneL : FunDecl := lfn () locals (s, z, cz, r) {
  s := call pin_at(3);
  z := call pin_at(2);
  cz := call const_e(z);
  r := call nat_ap1(s, cz);
  return r
}

/-- `nat_var(i)`: `fvar i Nat`. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:244-248 ConRon.Arena.natVar
@[l_impl ConRon.Arena.natVar]
def natVarL : FunDecl := lfn (i) locals (nt, c, r) {
  nt := call pin_at(1);
  c := call const_e(nt);
  r := call intern_fvar(i, c);
  return r
}

/-- `cert_ctx_pins(q, pi)`: the eleven operation names of the `nat_op_pins` record `pi` (words
`1‥3`, `7‥14`) into `IW[q + 10 ‥ q + 20]`, the last eleven words of the context record. All eleven are
read before any is written (lane `decls3-divmod`: the refinement proof then needs no aliasing facts
between the two records, and `cert_ctx` stays short enough for one `vcgen` run). -/
-- con-ron: ConRon/Arena/DeclCheck.lean:278-305 ConRon.Arena.certCtx
def certCtxPinsL : FunDecl :=
    lfn (q, pi) locals (w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20) {
  w10 := IW.u64[pi + 8]; w11 := IW.u64[pi + 7]; w12 := IW.u64[pi + 1]; w13 := IW.u64[pi + 3];
  w14 := IW.u64[pi + 2]; w15 := IW.u64[pi + 9]; w16 := IW.u64[pi + 13]; w17 := IW.u64[pi + 14];
  w18 := IW.u64[pi + 10]; w19 := IW.u64[pi + 11]; w20 := IW.u64[pi + 12];
  IW.u64[q + 10] := w10; IW.u64[q + 11] := w11; IW.u64[q + 12] := w12; IW.u64[q + 13] := w13;
  IW.u64[q + 14] := w14; IW.u64[q + 15] := w15; IW.u64[q + 16] := w16; IW.u64[q + 17] := w17;
  IW.u64[q + 18] := w18; IW.u64[q + 19] := w19; IW.u64[q + 20] := w20;
  return 0
}

/-- `cert_ctx_main(q, natTy, x, y, one, bleN, boolTy, bT, bF, z, two)`: the first ten words of the
context record at `q`. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:278-305 ConRon.Arena.certCtx
def certCtxMainL : FunDecl :=
    lfn (q, natTy, x, y, one, bleN, boolTy, bT, bF, z, two) {
  IW.u64[q] := natTy; IW.u64[q + 1] := x; IW.u64[q + 2] := y; IW.u64[q + 3] := one;
  IW.u64[q + 4] := bleN; IW.u64[q + 5] := boolTy; IW.u64[q + 6] := bT; IW.u64[q + 7] := bF;
  IW.u64[q + 8] := z; IW.u64[q + 9] := two;
  return 0
}

/-- `cert_ctx()`: the 21 pinned handles, a fresh `IW` record (the module doc's layout), built in
the twin's order (the first ten words are written by `cert_ctx_main`, the last eleven, the
operation names, copied by `cert_ctx_pins`). -/
-- con-ron: ConRon/Arena/DeclCheck.lean:278-305 ConRon.Arena.certCtx
@[l_impl ConRon.Arena.certCtx]
def certCtxL : FunDecl :=
    lfn () locals (pi, nt, natTy, x, y, one, bleN, bn, boolTy, u, bT, bF, z, s, two, q) {
  pi := call nat_op_pins();
  nt := IW.u64[pi + 15];
  natTy := call const_e(nt);
  x := call nat_var(0);
  y := call nat_var(1);
  one := call nat_one();
  bleN := IW.u64[pi + 6];
  bn := IW.u64[pi + 20];
  boolTy := call const_e(bn);
  u := IW.u64[pi + 18];
  bT := call const_e(u);
  u := IW.u64[pi + 19];
  bF := call const_e(u);
  u := IW.u64[pi + 16];
  z := call const_e(u);
  s := IW.u64[pi + 17];
  two := call nat_ap1(s, one);
  q := call iw_alloc(21);
  u := call cert_ctx_pins(q, pi);
  u := call cert_ctx_main(q, natTy, x, y, one, bleN, boolTy, bT, bF, z, two);
  return q
}

/-- `cert_guard(cx, a, b, r)`: `Nat.ble a b = r`. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:307-310 ConRon.Arena.certGuard
@[l_impl ConRon.Arena.certGuard]
def certGuardL : FunDecl := lfn (cx, a, b, r) locals (t, e) {
  t := call nat_ap2(IW.u64[cx + 4], a, b);
  e := call eq_at1(IW.u64[cx + 5], t, r);
  return e
}

/-- `cert_eq(cx, c, rhs)`: `c x y = rhs` (the left side interned after the right one). -/
-- con-ron: ConRon/Arena/DeclCheck.lean:312-316 ConRon.Arena.certEq
@[l_impl ConRon.Arena.certEq]
def certEqL : FunDecl := lfn (cx, c, rhs) locals (t, e) {
  t := call nat_ap2(c, IW.u64[cx + 1], IW.u64[cx + 2]);
  e := call eq_at1(IW.u64[cx], t, rhs);
  return e
}

/-- `cert_halves(cx, c)`: `c (x / 2) (y / 2)`. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:318-323 ConRon.Arena.certHalves
@[l_impl ConRon.Arena.certHalves]
def certHalvesL : FunDecl := lfn (cx, c) locals (hx, hy, r) {
  hx := call nat_ap2(IW.u64[cx + 11], IW.u64[cx + 1], IW.u64[cx + 9]);
  hy := call nat_ap2(IW.u64[cx + 11], IW.u64[cx + 2], IW.u64[cx + 9]);
  r := call nat_ap2(c, hx, hy);
  return r
}

/-- `stmt1(h, e)`: the statement record `[[h], e]` (one hypothesis). -/
-- con-ron: ConRon/Arena/DeclCheck.lean:325-331 ConRon.Arena.certTwoEqs
def stmt1 : FunDecl := lfn (h, e) locals (o, l, s) {
  (o, l) := call sl_new1(h);
  s := call rec3(o, l, e);
  return s
}

/-- `cert_two_eqs(cx, c, h1, h2, r1, r2)`: `[([h1], c x y = r1), ([h2], c x y = r2)]`. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:325-331 ConRon.Arena.certTwoEqs
@[l_impl ConRon.Arena.certTwoEqs]
def certTwoEqsL : FunDecl := lfn (cx, c, h1, h2, r1, r2) locals (e1, e2, s1, s2, q) {
  e1 := call cert_eq(cx, c, r1);
  e2 := call cert_eq(cx, c, r2);
  s1 := call stmt1(h1, e1);
  s2 := call stmt1(h2, e2);
  q := call rec2(s1, s2);
  return (q, 2)
}

/-- `cert_gcd(cx, c)`. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:333-339 ConRon.Arena.certGcd
@[l_impl ConRon.Arena.certGcd]
def certGcdL : FunDecl := lfn (cx, c) locals (h1, h2, m, r1, o, l) {
  h1 := call cert_guard(cx, IW.u64[cx + 3], IW.u64[cx + 1], IW.u64[cx + 6]);
  h2 := call cert_guard(cx, IW.u64[cx + 3], IW.u64[cx + 1], IW.u64[cx + 7]);
  m := call nat_ap2(IW.u64[cx + 10], IW.u64[cx + 2], IW.u64[cx + 1]);
  r1 := call nat_ap2(c, m, IW.u64[cx + 1]);
  (o, l) := call cert_two_eqs(cx, c, h1, h2, r1, IW.u64[cx + 2]);
  return (o, l)
}

/-- `cert_shift_left(cx, c)`. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:341-347 ConRon.Arena.certShiftLeft
@[l_impl ConRon.Arena.certShiftLeft]
def certShiftLeftL : FunDecl := lfn (cx, c) locals (h1, h2, a, b, r1, o, l) {
  h1 := call cert_guard(cx, IW.u64[cx + 3], IW.u64[cx + 2], IW.u64[cx + 6]);
  h2 := call cert_guard(cx, IW.u64[cx + 3], IW.u64[cx + 2], IW.u64[cx + 7]);
  a := call nat_ap2(IW.u64[cx + 13], IW.u64[cx + 9], IW.u64[cx + 1]);
  b := call nat_ap2(IW.u64[cx + 14], IW.u64[cx + 2], IW.u64[cx + 3]);
  r1 := call nat_ap2(c, a, b);
  (o, l) := call cert_two_eqs(cx, c, h1, h2, r1, IW.u64[cx + 1]);
  return (o, l)
}

/-- `cert_shift_right(cx, c)`. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:349-355 ConRon.Arena.certShiftRight
@[l_impl ConRon.Arena.certShiftRight]
def certShiftRightL : FunDecl := lfn (cx, c) locals (h1, h2, a, b, r1, o, l) {
  h1 := call cert_guard(cx, IW.u64[cx + 3], IW.u64[cx + 2], IW.u64[cx + 6]);
  h2 := call cert_guard(cx, IW.u64[cx + 3], IW.u64[cx + 2], IW.u64[cx + 7]);
  a := call nat_ap2(IW.u64[cx + 14], IW.u64[cx + 2], IW.u64[cx + 3]);
  b := call nat_ap2(c, IW.u64[cx + 1], a);
  r1 := call nat_ap2(IW.u64[cx + 11], b, IW.u64[cx + 9]);
  (o, l) := call cert_two_eqs(cx, c, h1, h2, r1, IW.u64[cx + 1]);
  return (o, l)
}

/-- `cert_land(cx, c)`. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:357-366 ConRon.Arena.certLand
@[l_impl ConRon.Arena.certLand]
def certLandL : FunDecl := lfn (cx, c) locals (h1, h2, rc, a, mx, my, b, r1, o, l) {
  h1 := call cert_guard(cx, IW.u64[cx + 3], IW.u64[cx + 1], IW.u64[cx + 6]);
  h2 := call cert_guard(cx, IW.u64[cx + 3], IW.u64[cx + 1], IW.u64[cx + 7]);
  rc := call cert_halves(cx, c);
  a := call nat_ap2(IW.u64[cx + 13], IW.u64[cx + 9], rc);
  mx := call nat_ap2(IW.u64[cx + 10], IW.u64[cx + 1], IW.u64[cx + 9]);
  my := call nat_ap2(IW.u64[cx + 10], IW.u64[cx + 2], IW.u64[cx + 9]);
  b := call nat_ap2(IW.u64[cx + 13], mx, my);
  r1 := call nat_ap2(IW.u64[cx + 12], a, b);
  (o, l) := call cert_two_eqs(cx, c, h1, h2, r1, IW.u64[cx + 8]);
  return (o, l)
}

/-- `cert_lor_rhs(cx, c)`: `2*((x/2) ||| (y/2)) + (x%2 + y%2 - (x%2)*(y%2))`. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:368-376 ConRon.Arena.certLorRhs
@[l_impl ConRon.Arena.certLorRhs]
def certLorRhsL : FunDecl := lfn (cx, c) locals (rc, t2, mx, my, a, b, d, r) {
  rc := call cert_halves(cx, c);
  t2 := call nat_ap2(IW.u64[cx + 13], IW.u64[cx + 9], rc);
  mx := call nat_ap2(IW.u64[cx + 10], IW.u64[cx + 1], IW.u64[cx + 9]);
  my := call nat_ap2(IW.u64[cx + 10], IW.u64[cx + 2], IW.u64[cx + 9]);
  a := call nat_ap2(IW.u64[cx + 12], mx, my);
  b := call nat_ap2(IW.u64[cx + 13], mx, my);
  d := call nat_ap2(IW.u64[cx + 14], a, b);
  r := call nat_ap2(IW.u64[cx + 12], t2, d);
  return r
}

/-- `cert_lor(cx, c)`. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:378-384 ConRon.Arena.certLor
@[l_impl ConRon.Arena.certLor]
def certLorL : FunDecl := lfn (cx, c) locals (h1, h2, r1, o, l) {
  h1 := call cert_guard(cx, IW.u64[cx + 3], IW.u64[cx + 1], IW.u64[cx + 6]);
  h2 := call cert_guard(cx, IW.u64[cx + 3], IW.u64[cx + 1], IW.u64[cx + 7]);
  r1 := call cert_lor_rhs(cx, c);
  (o, l) := call cert_two_eqs(cx, c, h1, h2, r1, IW.u64[cx + 2]);
  return (o, l)
}

/-- `cert_xor_rhs(cx, c)`: `2*((x/2) ^^^ (y/2)) + (x%2 + y%2) % 2`. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:386-393 ConRon.Arena.certXorRhs
@[l_impl ConRon.Arena.certXorRhs]
def certXorRhsL : FunDecl := lfn (cx, c) locals (rc, t2, mx, my, a, d, r) {
  rc := call cert_halves(cx, c);
  t2 := call nat_ap2(IW.u64[cx + 13], IW.u64[cx + 9], rc);
  mx := call nat_ap2(IW.u64[cx + 10], IW.u64[cx + 1], IW.u64[cx + 9]);
  my := call nat_ap2(IW.u64[cx + 10], IW.u64[cx + 2], IW.u64[cx + 9]);
  a := call nat_ap2(IW.u64[cx + 12], mx, my);
  d := call nat_ap2(IW.u64[cx + 10], a, IW.u64[cx + 9]);
  r := call nat_ap2(IW.u64[cx + 12], t2, d);
  return r
}

/-- `cert_xor(cx, c)`. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:395-401 ConRon.Arena.certXor
@[l_impl ConRon.Arena.certXor]
def certXorL : FunDecl := lfn (cx, c) locals (h1, h2, r1, o, l) {
  h1 := call cert_guard(cx, IW.u64[cx + 3], IW.u64[cx + 1], IW.u64[cx + 6]);
  h2 := call cert_guard(cx, IW.u64[cx + 3], IW.u64[cx + 1], IW.u64[cx + 7]);
  r1 := call cert_xor_rhs(cx, c);
  (o, l) := call cert_two_eqs(cx, c, h1, h2, r1, IW.u64[cx + 2]);
  return (o, l)
}

/-- `cert_rec_rhs(cx, c)`: `c (x - y) y`, under `Nat.succ` for `div`. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:403-410 ConRon.Arena.certRecRhs
@[l_impl ConRon.Arena.certRecRhs]
def certRecRhsL : FunDecl := lfn (cx, c) locals (d, st, s, r) {
  d := call nat_ap2(IW.u64[cx + 14], IW.u64[cx + 1], IW.u64[cx + 2]);
  st := call nat_ap2(c, d, IW.u64[cx + 2]);
  if c == IW.u64[cx + 11] {
    s := call pin_at(3);
    r := call nat_ap1(s, st);
    return r
  };
  return st
}

/-- `cert_div_mod_eqs(cx, c, h1, h2, h3, h4, recRhs, baseRhs)`:
`[([h1, h2], c x y = recRhs), ([h3], c x y = baseRhs), ([h4], c x y = baseRhs)]`. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:412-418 ConRon.Arena.certDivModEqs
@[l_impl ConRon.Arena.certDivModEqs]
def certDivModEqsL : FunDecl :=
    lfn (cx, c, h1, h2, h3, h4, recRhs, baseRhs) locals (e1, e2, o, s1, s2, s3, q) {
  e1 := call cert_eq(cx, c, recRhs);
  e2 := call cert_eq(cx, c, baseRhs);
  o := call rec2(h1, h2);
  s1 := call rec3(o, 2, e1);
  s2 := call stmt1(h3, e2);
  s3 := call stmt1(h4, e2);
  q := call rec3(s1, s2, s3);
  return (q, 3)
}

/-- `cert_div_mod_guards(cx, c, recRhs, baseRhs)`: the four guards, then the three statements. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:420-428 ConRon.Arena.certDivModGuards
@[l_impl ConRon.Arena.certDivModGuards]
def certDivModGuardsL : FunDecl := lfn (cx, c, recRhs, baseRhs) locals (h1, h2, h3, h4, o, l) {
  h1 := call cert_guard(cx, IW.u64[cx + 2], IW.u64[cx + 1], IW.u64[cx + 6]);
  h2 := call cert_guard(cx, IW.u64[cx + 3], IW.u64[cx + 2], IW.u64[cx + 6]);
  h3 := call cert_guard(cx, IW.u64[cx + 2], IW.u64[cx + 1], IW.u64[cx + 7]);
  h4 := call cert_guard(cx, IW.u64[cx + 3], IW.u64[cx + 2], IW.u64[cx + 7]);
  (o, l) := call cert_div_mod_eqs(cx, c, h1, h2, h3, h4, recRhs, baseRhs);
  return (o, l)
}

/-- `cert_div_mod(cx, c)`. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:430-435 ConRon.Arena.certDivMod
@[l_impl ConRon.Arena.certDivMod]
def certDivModL : FunDecl := lfn (cx, c) locals (rr, b, o, l) {
  rr := call cert_rec_rhs(cx, c);
  b := IW.u64[cx + 1];
  if c == IW.u64[cx + 11] { b := IW.u64[cx + 8] };
  (o, l) := call cert_div_mod_guards(cx, c, rr, b);
  return (o, l)
}

/-- `div_mod_cert_stmts_at(cx, c)`: the seven-way dispatch. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:437-447 ConRon.Arena.divModCertStmtsAt
@[l_impl ConRon.Arena.divModCertStmtsAt]
def divModCertStmtsAtL : FunDecl := lfn (cx, c) locals (o, l) {
  if c == IW.u64[cx + 15] { (o, l) := call cert_gcd(cx, c); return (o, l) };
  if c == IW.u64[cx + 16] { (o, l) := call cert_shift_left(cx, c); return (o, l) };
  if c == IW.u64[cx + 17] { (o, l) := call cert_shift_right(cx, c); return (o, l) };
  if c == IW.u64[cx + 18] { (o, l) := call cert_land(cx, c); return (o, l) };
  if c == IW.u64[cx + 19] { (o, l) := call cert_lor(cx, c); return (o, l) };
  if c == IW.u64[cx + 20] { (o, l) := call cert_xor(cx, c); return (o, l) };
  (o, l) := call cert_div_mod(cx, c);
  return (o, l)
}

/-- `div_mod_cert_stmts(c)`. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:449-461 ConRon.Arena.divModCertStmts
@[l_impl ConRon.Arena.divModCertStmts]
def divModCertStmtsL : FunDecl := lfn (c) locals (cx, o, l) {
  cx := call cert_ctx();
  (o, l) := call div_mod_cert_stmts_at(cx, c);
  return (o, l)
}

/-- `div_mod_cert_applied(proofS, ho, hl)`: the proof applied to `x`, `y` and one `fvar` per
hypothesis (at most two; a longer list stays `proof x y`, as the twin's `_` clause). -/
-- con-ron: ConRon/Arena/DeclCheck.lean:463-481 ConRon.Arena.divModCertApplied
@[l_impl ConRon.Arena.divModCertApplied]
def divModCertAppliedL : FunDecl := lfn (proofS, ho, hl) locals (x, y, b1, base, f2, a1, f3, r) {
  x := call nat_var(0);
  y := call nat_var(1);
  b1 := call mk_app(proofS, x);
  base := call mk_app(b1, y);
  if hl == 1 {
    f2 := call intern_fvar(2, IW.u64[ho]);
    r := call mk_app(base, f2);
    return r
  };
  if hl == 2 {
    f2 := call intern_fvar(2, IW.u64[ho]);
    a1 := call mk_app(base, f2);
    f3 := call intern_fvar(3, IW.u64[ho + 1]);
    r := call mk_app(a1, f3);
    return r
  };
  return base
}

/-- `subst_const0_list(n, r, o, l)`. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:483-490 ConRon.Arena.substConst0List
@[l_impl ConRon.Arena.substConst0List]
def substConst0ListL : FunDecl := lfn (n, r, o, l) locals (h, ro, rl, so, sl) {
  if l == 0 { return (0, 0) };
  h := call subst_const0(n, r, 4000000000, IW.u64[o]);
  (ro, rl) := call subst_const0_list(n, r, o + 1, l - 1);
  (so, sl) := call sl_cons(h, ro, rl);
  return (so, sl)
}

/-- `consts_resolve_all(vis, o, l)`. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:492-497 ConRon.Arena.constsResolveAll
@[l_impl ConRon.Arena.constsResolveAll]
def constsResolveAllL : FunDecl := lfn (vis, o, l) locals (e) {
  if l == 0 { return 1 };
  e := call consts_resolve_ffast(vis, IW.u64[o]);
  if e == 0 { return 0 };
  e := call consts_resolve_all(vis, o + 1, l - 1);
  return e
}

/-! ## The guards -/

/-- `div_mod_cert_guard(vis, c, annVal, ho, hl, eqE, proof)`: the syntactic guards of one
certificate. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:499-513 ConRon.Arena.divModCertGuard
@[l_impl ConRon.Arena.divModCertGuard]
def divModCertGuardL : FunDecl := lfn (vis, c, annVal, ho, hl, eqE, proof) locals (p, b, so, sl, e) {
  p := call subst_const_all(c, annVal, 4000000000, proof);
  b := call loose_bvars_bounded_fast(4000000000, 0, p);
  if b == 0 { return 0 };
  b := call has_fvar_fast(4000000000, p);
  if b != 0 { return 0 };
  b := call all_level_params_defined(0, 0, p);
  if b == 0 { return 0 };
  b := call consts_resolve_ffast(vis, p);
  if b == 0 { return 0 };
  (so, sl) := call subst_const0_list(c, annVal, ho, hl);
  b := call consts_resolve_all(vis, so, sl);
  if b == 0 { return 0 };
  e := call subst_const0(c, annVal, 4000000000, eqE);
  b := call consts_resolve_ffast(vis, e);
  return b
}

/-- `bool_ctor_typed(vis2, n)`: `n` is stored at the type `Bool` itself (the lookup, then the
stored type, then `Bool` interned). -/
-- con-ron: ConRon/Arena/DeclCheck.lean:515-528 ConRon.Arena.boolCtorTyped
-- con-ron: CHANGED since 12752ca7 — `ConRon.Arena.boolCtorTyped` changed; re-check the L code and its proofs, then delete this line
@[l_impl ConRon.Arena.boolCtorTyped]
def boolCtorTypedL : FunDecl := lfn (vis2, n) locals (f, r, q, bn, bt) {
  (f, r) := call env_find(n, vis2);
  if f == 0 { return 0 };
  q := call ci_to_cv(r);
  bn := call pin_at(29);
  bt := call const_e(bn);
  return u64(EREC.u64[q + 3] == bt)
}

/-- `div_mod_env_guard(vis2, c)`: the dependency guard, the pinned dependencies, the pinned `Eq`
basis, the `Bool` constructors at `Bool`. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:530-542 ConRon.Arena.divModEnvGuard
@[l_impl ConRon.Arena.divModEnvGuard]
def divModEnvGuardL : FunDecl := lfn (vis2, c) locals (g, o, l, en, ea, e, n) {
  g := call nat_op_guard(vis2, c);
  if g == 0 { return 0 };
  (o, l) := call nat_op_deps(c);
  g := call nat_op_stored_ok_all(vis2, o, l);
  if g == 0 { return 0 };
  en := call pin_at(0);
  ea := call rom_ci(0);
  e := call find_is(vis2, en, ea);
  if e == 0 { return 0 };
  n := call pin_at(30);
  e := call bool_ctor_typed(vis2, n);
  if e == 0 { return 0 };
  n := call pin_at(31);
  e := call bool_ctor_typed(vis2, n);
  return e
}

/-- `div_mod_pin_guard(ps, vis, c)`: the syntactic guards on the variant's pin. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:577-586 ConRon.Arena.divModPinGuard
-- con-ron: CHANGED since 12752ca7 — below `ConRon.Arena.divModPinGuard`, `ConRon.Arena.divModTypePins`, `ConRon.Arena.groundGuards`, `ConRon.Arena.typePinsGuard` changed; re-check the L code and its proofs, then delete this line
-- con-ron: CHANGED since 12752ca7 — `ConRon.Arena.divModPinGuard` changed; re-check the L code and its proofs, then delete this line
@[l_impl ConRon.Arena.divModPinGuard]
def divModPinGuardL : FunDecl := lfn (ps, vis, c) locals (p, b) {
  p := call div_mod_decl_pin(ps, c);
  b := call loose_bvars_bounded_fast(4000000000, 0, p);
  if b == 0 { return 0 };
  b := call has_fvar_fast(4000000000, p);
  if b != 0 { return 0 };
  b := call all_level_params_defined(0, 0, p);
  if b == 0 { return 0 };
  b := call consts_resolve_ffast(vis, p);
  return b
}

/-- `div_mod_certs_guard_go(vis, c, annVal, so, sl, po, pl)`: the statements zipped with the
proofs (the shorter list ends it, `true`). -/
-- con-ron: ConRon/Arena/DeclCheck.lean:588-600 ConRon.Arena.divModCertsGuardGo
@[l_impl ConRon.Arena.divModCertsGuardGo]
def divModCertsGuardGoL : FunDecl := lfn (vis, c, annVal, so, sl, po, pl) locals (s, e) {
  if sl == 0 || pl == 0 { return 1 };
  s := IW.u64[so];
  e := call div_mod_cert_guard(vis, c, annVal, IW.u64[s], IW.u64[s + 1], IW.u64[s + 2],
    IW.u64[po]);
  if e == 0 { return 0 };
  e := call div_mod_certs_guard_go(vis, c, annVal, so + 1, sl - 1, po + 1, pl - 1);
  return e
}

/-- `div_mod_certs_guard(ps, vis, c, annVal)`: the statements, then the proofs, then the zip. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:602-608 ConRon.Arena.divModCertsGuard
@[l_impl ConRon.Arena.divModCertsGuard]
def divModCertsGuardL : FunDecl := lfn (ps, vis, c, annVal) locals (so, sl, po, pl, e) {
  (so, sl) := call div_mod_cert_stmts(c);
  (po, pl) := call div_mod_cert_proofs(ps, c);
  e := call div_mod_certs_guard_go(vis, c, annVal, so, sl, po, pl);
  return e
}

/-! ## The certificates, one variant, the loop -/

/-- `check_div_mod_certs(vis, c, annVal, so, sl, po, pl)`: per certificate, the guards, the
substituted proof applied, its type inferred and compared with the substituted equation (depth
`4`); the two lists must end together. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:610-631 ConRon.Arena.checkDivModCerts
@[l_impl ConRon.Arena.checkDivModCerts]
def checkDivModCertsL : FunDecl :=
    lfn (vis, c, annVal, so, sl, po, pl) locals (s, g, p, ho, hl, ap, tp, rhs, d) {
  if sl == 0 && pl == 0 { return 1 };
  if sl == 0 || pl == 0 { return 0 };
  s := IW.u64[so];
  g := call div_mod_cert_guard(vis, c, annVal, IW.u64[s], IW.u64[s + 1], IW.u64[s + 2],
    IW.u64[po]);
  if g == 0 { return 0 };
  p := call subst_const_all(c, annVal, 4000000000, IW.u64[po]);
  (ho, hl) := call subst_const0_list(c, annVal, IW.u64[s], IW.u64[s + 1]);
  ap := call div_mod_cert_applied(p, ho, hl);
  tp := call infer_type_core(vis, 4, ap);
  rhs := call subst_const0(c, annVal, 4000000000, IW.u64[s + 2]);
  d := call is_def_eq_core(vis, 4, tp, rhs);
  if d == 0 { return 0 };
  d := call check_div_mod_certs(vis, c, annVal, so + 1, sl - 1, po + 1, pl - 1);
  return d
}

/-- `check_div_mod_pin_at(vis, c, value, ps)`: one variant's attempt: the stored value against
the variant's pin, then (on a match) its certificates. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:657-668 ConRon.Arena.checkDivModPinAt
-- con-ron: CHANGED since 12752ca7 — `ConRon.Arena.checkDivModPinAt` changed; re-check the L code and its proofs, then delete this line
-- con-ron: CHANGED since 12752ca7 — below `ConRon.Arena.checkDivModPinAt`, `ConRon.Arena.checkDivModPinValue`, `ConRon.Arena.checkTypePins`, `ConRon.Arena.divModTypePins` changed; re-check the L code and its proofs, then delete this line
@[l_impl ConRon.Arena.checkDivModPinAt]
def checkDivModPinAtL : FunDecl := lfn (vis, c, value, ps) locals (pa, ok, so, sl, po, pl, r) {
  pa := call div_mod_decl_pin(ps, c);
  ok := call is_def_eq_core(vis, 0, value, pa);
  if ok == 0 { return 0 };
  (so, sl) := call div_mod_cert_stmts(c);
  (po, pl) := call div_mod_cert_proofs(ps, c);
  r := call check_div_mod_certs(vis, c, value, so, sl, po, pl);
  return r
}

/-- `check_div_mod_pin_loop(vis, c, value, po, pl)`: the variant loop over the `IW` slice of
variant records; no variant left declines. **No recovery**: an error inside an attempt aborts
here, where the twin's `orElseAttempt` restores the state and tries the next variant (the
module doc); `ATT` is `3` during the attempt, so such an abort claims no class (`fail R`,
`Arena/Globals.lean`). The `tried` list only feeds the message and is not kept. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:676-704 ConRon.Arena.checkDivModPinLoop
-- con-ron: CHANGED since 12752ca7 — `ConRon.Arena.checkDivModPinLoop` changed; re-check the L code and its proofs, then delete this line
@[l_impl ConRon.Arena.checkDivModPinLoop]
def checkDivModPinLoopL : FunDecl := lfn (vis, c, value, po, pl) locals (ps, g1, g2, r) {
  if pl == 0 { fail R_UNSUPPORTED_NAT_DIV_MOD };
  ps := IW.u64[po];
  g1 := call div_mod_pin_guard(ps, vis, c);
  g2 := call div_mod_certs_guard(ps, vis, c, value);
  if g1 != 0 && g2 != 0 {
    L.Arena.ATT := 3;
    r := call check_div_mod_pin_at(vis, c, value, ps);
    L.Arena.ATT := 0;
    if r != 0 { return 0 }
  };
  r := call check_div_mod_pin_loop(vis, c, value, po + 1, pl - 1);
  return r
}

/-- `check_div_mod_pin(po, pl, vis, vis2, c)`: the gate after the definition check (`vis2` the
extended view, `vis` the pre-insertion one every check runs at). -/
-- con-ron: ConRon/Arena/DeclCheck.lean:706-720 ConRon.Arena.checkDivModPin
@[l_impl ConRon.Arena.checkDivModPin]
def checkDivModPinL : FunDecl := lfn (po, pl, vis, vis2, c) locals (g, f, r, z) {
  g := call div_mod_env_guard(vis2, c);
  if g == 0 { fail R_UNSUPPORTED_NAT_DIV };
  (f, r) := call env_find(c, vis2);
  if f == 0 { abort };
  if EREC.u64[r] != 1 { abort };
  z := call check_div_mod_pin_loop(vis, c, EREC.u64[r + 5], po, pl);
  return 0
}

/-! ## The module's program -/

/-- This module's functions. -/
def declArmsNatFns : Prog :=
  [("nat_op_names", natOpNamesL), ("nat_div_mod_names", natDivModNamesL),
   ("nat_op_pins_a", natOpPinsAL), ("nat_op_pins_b", natOpPinsBL), ("nat_op_pins_c", natOpPinsCL),
   ("nat_op_pins", natOpPinsL), ("nat_op_deps", natOpDepsL), ("nat_op_deps_stored", natOpDepsStoredL),
   ("bool_ctor_ok", boolCtorOkL), ("nat_op_bool_ctors", natOpBoolCtorsL),
   ("nat_op_guard", natOpGuardL), ("nat_op_cod", natOpCodL),
   ("nat_op_ty_pinned", natOpTyPinnedL), ("nat_op_stored_ok", natOpStoredOkL),
   ("nat_op_stored_ok_all", natOpStoredOkAllL), ("nat_ap1", natAp1L), ("nat_ap2", natAp2L),
   ("nat_eq_list2", natEqList2), ("nat_eq_list3", natEqList3), ("nat_eq_list4", natEqList4),
   ("nat_eq_pr", natEqPr), ("nat_eq_un", natEqUn), ("nat_eq_mu", natEqMu), ("nat_eq_po", natEqPo),
   ("nat_eq_be", natEqBe), ("nat_eq_bl", natEqBl), ("nat_eq_ctx", natEqCtx), ("nat_eq_disp", natEqDisp), ("nat_op_equations", natOpEquationsL), ("defn_nat_cert", defnNatCert),
   ("subst_const0", substConst0L), ("subst_const_all", substConstAllL),
   ("subst_const0_pairs", substConst0PairsL), ("certify_nat_eqs", certifyNatEqsL),
   ("div_mod_slot", divModSlot), ("div_mod_decl_pin", divModDeclPinL),
   ("div_mod_cert_proofs", divModCertProofsL), ("eq_at1", eqAt1L), ("nat_one", natOneL),
   ("nat_var", natVarL), ("cert_ctx_pins", certCtxPinsL), ("cert_ctx_main", certCtxMainL),
   ("cert_ctx", certCtxL), ("cert_guard", certGuardL),
   ("cert_eq", certEqL), ("cert_halves", certHalvesL), ("stmt1", stmt1),
   ("cert_two_eqs", certTwoEqsL), ("cert_gcd", certGcdL), ("cert_shift_left", certShiftLeftL),
   ("cert_shift_right", certShiftRightL), ("cert_land", certLandL),
   ("cert_lor_rhs", certLorRhsL), ("cert_lor", certLorL), ("cert_xor_rhs", certXorRhsL),
   ("cert_xor", certXorL), ("cert_rec_rhs", certRecRhsL), ("cert_div_mod_eqs", certDivModEqsL),
   ("cert_div_mod_guards", certDivModGuardsL), ("cert_div_mod", certDivModL),
   ("div_mod_cert_stmts_at", divModCertStmtsAtL), ("div_mod_cert_stmts", divModCertStmtsL),
   ("div_mod_cert_applied", divModCertAppliedL), ("subst_const0_list", substConst0ListL),
   ("consts_resolve_all", constsResolveAllL), ("div_mod_cert_guard", divModCertGuardL),
   ("bool_ctor_typed", boolCtorTypedL), ("div_mod_env_guard", divModEnvGuardL),
   ("div_mod_pin_guard", divModPinGuardL), ("div_mod_certs_guard_go", divModCertsGuardGoL),
   ("div_mod_certs_guard", divModCertsGuardL), ("check_div_mod_certs", checkDivModCertsL),
   ("check_div_mod_pin_at", checkDivModPinAtL), ("check_div_mod_pin_loop", checkDivModPinLoopL),
   ("check_div_mod_pin", checkDivModPinL)]

/-- **The ROM stubs** (lane lead: the con-leche values the twin interns, read from the ROM). Each
call stands for the twin's intern of the value (its store effect included) and returns where the
value now lives:

* `rom_basis_decls(kind)` → `(off, len)`: `BasisKind.decls kind` (the RAW block), an `IW` slice
  of `EREC` pointers to constant records (`decCI`); `kind` `0` `eqK`, `1` `natK`, `2` `emptyK`,
  `3` `falseK`, `4` `quotK` (con-leche's constructor order).
* `rom_basis_decls_a(kind)` → `(off, len)`: `BasisKind.declsA kind` (the ANNOTATED block), the
  same shape.
* `rom_ci(id)` → an `EREC` pointer to a constant record: `0` `eqA`, `1` `natA`, `2` `iffA`, `3`
  `iffIntroA`, `4` `iffRecA`, `5` `nonemptyA`, `6` `nonemptyIntroA`, `7` `nonemptyRecA`.
* `rom_cv(id)` → an `EREC` pointer to a constant value (`decCV`, 4 words): `0` `propextA`, `1`
  `choiceA`, `2` `trueCvA`, `3` `trueIntroCvA`, `4` `trustCompilerA`, `5` `boolCvA`, `6`
  `reduceNatCvA`, `7` `reduceBoolCvA`, `8` `ofReduceNatA`, `9` `ofReduceBoolA`.
* `rom_expr_pin(id)` → an expression handle: `0` `reduceNatDeclPin`, `1` `reduceBoolDeclPin`.
* `rom_pin_sets()` → `(off, len)`: the `Nat`-operation pin variants (`checkDecl`'s `pins`), an
  `IW` slice of `EREC` pointers to 24-word variant records (this module's doc). Empty for the
  program's ROM today (`romPins = []`). -/
def romStubs : Prog :=
  [("rom_basis_decls", stub 1), ("rom_basis_decls_a", stub 1), ("rom_ci", stub 1),
   ("rom_cv", stub 1), ("rom_expr_pin", stub 1), ("rom_pin_sets", stub 0), ("rom_and_pin", stub 0)]

/-! ## Runs on stub-free paths -/

/-- The test memory with a filled pin table: flag `1`, slot `i` holding the name `100 + i`. -/
def pinsTestMem : Mem :=
  let p := (List.range 71).foldl (fun a i => a.set! (1 + i) (UInt64.ofNat (100 + i)))
    ((Array.replicate 72 (0 : Word)).set! 0 1)
  { armsTestMem with words := armsTestMem.words.set! PINS p }

/-- The real pin readers in place of `masterFns`' stubs (for the runs below). -/
def withPins (p : Prog) : Prog :=
  p.map fun e => if e.1 == "pin_at" then ("pin_at", pinAtL)
    else if e.1 == "pin_word" then ("pin_word", pinWordL) else e

/-- The program the runs below use. -/
def natTestProg : Prog :=
  withPins (declArmsNatFns ++ declArmsCanonFns ++ libFns ++ stubFns ++ masterFns ++
    armsMasterFns ++ romStubs)

-- `natOpDeps Nat.lor` is `[add, sub, mul, ble, div, mod, lor]`; `Nat.shiftRight`'s variant slot
-- is `7`; a name that is no operation has no dependencies.
#guard
  (match run natTestProg 1000 "nat_op_deps" [125] pinsTestMem with
   | .ok ([o, 7], m) =>
     (List.range 7).map (fun j => rdW (m.arr64 IW) (o + UInt64.ofNat j)) ==
       [115, 116, 117, 120, 121, 122, 125]
   | _ => false) &&
  (match run natTestProg 1000 "div_mod_slot" [128] pinsTestMem with
   | .ok ([7], _) => true | _ => false) &&
  (match run natTestProg 1000 "nat_op_deps" [5] pinsTestMem with
   | .ok ([_, 0], _) => true | _ => false)

end L.Ind
