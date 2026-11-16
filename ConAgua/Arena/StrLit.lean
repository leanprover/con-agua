module

public import ConAgua.Arena.Tiers
import ConAgua.Census.Attr

@[expose] public section

/-!
# String literals in L: `lit_shape_ok`, `str_lit_ctor` (lane `defeq2`, helper `defeq2-str`)

Twin: `vendor/con-ron/ConRon/Arena/Core.lean` ("String literals"). L names and their twins:

| L | twin | notes |
|---|---|---|
| `str_cv(p)` | `IConstantInfo.toConstantVal` | `(lo, ll, ty)`: the level parameters' `EREC` slice and the type; a projection table interns `Sort 1` |
| `string_ty_ok`, `char_ty_ok` | `stringTyOk`, `charTyOk` | one body (the twins are the same) |
| `str_param_sort(pn)` | none | `internLNode (.param p)`, `.succ`, `internE (.sort ·)`: the prefix of the three `List` tests |
| `str_ls1(u)` | `internLsNode [u]` | the one-element list at the pool top |
| `list_ty_ok`, `list_nil_ty_ok`, `list_cons_ty_ok`, `char_of_nat_ty_ok`, `string_of_list_ty_ok` | the `…TyOk` tests | `(found, q)` is `find?`'s result, as `nat_ind_ok` |
| `lit_shape_ok(p)` | `litShapeOk` | the `…TyOk` test of the name's pin, `1` elsewhere |
| `str_utf8_char(k, n)` | none | `utf8_char` (`Scan/Utf8.lean`) on the pool's byte words: one code point of `s.toList` |
| `str_cons_spine(cons, ofNat, nilE, k, n)` | `strLitConsSpine` | the bytes `[k, n)` of the pool; recursion over the characters as the twin's |
| `str_ctor_pre()` | none | the literal-independent prefix of `strLitToConstructor` |
| `str_lit_ctor(h)` | `strLitToConstructor` | the literal's record gives the byte slice |

A character's `Nat` literal is interned by `rom_lit` (`RomExpr.lean`: its one limb at the pool
top). Every view is the twin's: a tag test, then `e_view`.
-/


namespace L.Arena

/-- `str_cv(p)`: the constant value of the record at `p` (`IConstantInfo.toConstantVal`, inline at
`p + CI.cv`) as `(lo, ll, ty)`: the level parameters `EREC[lo‥lo+ll)` and the type. -/
-- con-ron: ConRon/Arena/Env.lean:168-172 ConRon.Arena.IConstantInfo.toConstantVal
@[no_expose] def strCvL : FunDecl := lfn (p) locals () {
  return (EREC⦃p + ⟪CI.cv + CV.lpsOff⟫⦄, EREC⦃p + ⟪CI.cv + CV.lpsLen⟫⦄, EREC⦃p + ⟪CI.cv + CV.type⟫⦄)
}

/-- `string_ty_ok(found, p)`: no level parameters, type `Sort 1`. -/
-- con-ron: ConRon/Arena/Core.lean:714-721 ConRon.Arena.stringTyOk
@[no_expose, l_impl ConRon.Arena.stringTyOk]
def stringTyOkL : FunDecl := lfn (found, p) locals (lo, ll, ty, s1) {
  if found == 0 { return 0 };
  (lo, ll, ty) := call str_cv(p);
  s1 := call pin_word(54);
  if ll == 0 && ty == s1 { return 1 };
  return 0
}

/-- `char_ty_ok(found, p)`: `string_ty_ok`'s body (the twins are the same). -/
-- con-ron: ConRon/Arena/Core.lean:723-730 ConRon.Arena.charTyOk
@[no_expose, l_impl ConRon.Arena.charTyOk]
def charTyOkL : FunDecl := stringTyOkL

/-- `str_param_sort(pn)`: `(pl, so)` with `pl` the level `param pn` and `so` the expression
`Sort (succ pl)`, interned in the twin's order. -/
-- con-ron: none — the shared prefix of `listTyOk`, `listNilTyOk`, `listConsTyOk` (no twin function)
@[no_expose] def strParamSortL : FunDecl := lfn (pn) locals (pl, sp, so) {
  pl := call intern_param(pn);
  sp := call intern_succ(pl);
  so := call intern_sort(sp);
  return (pl, so)
}

/-- `str_ls1(u)`: the level list `[u]`, its one handle word at the pool top. -/
-- con-ron: ConRon/Arena/Monad.lean:502-518 ConRon.Arena.internLsNode
@[no_expose] def strLs1L : FunDecl := lfn (u) locals (o, h, pt, pb) {
  o := CTL.u64[0];
  pt := ⦃o⦄.tier;
  pb := ⦃o⦄.base;
  if len(POOL⟨pt⟩) <= o - pb { abort };
  POOL⟨pt⟩[o - pb] := u;
  CTL.u64[0] := o + 1;
  h := call intern_ls(o, 1);
  return h
}

/-- `list_ty_ok(found, p)`: one level parameter `u`, type `Sort (u+1) → Sort (u+1)`. -/
-- con-ron: ConRon/Arena/Core.lean:732-749 ConRon.Arena.listTyOk
@[no_expose, l_impl ConRon.Arena.listTyOk]
def listTyOkL : FunDecl := lfn (found, p) locals (lo, ll, ty, pl, so, g, d, b, z) {
  if found == 0 { return 0 };
  (lo, ll, ty) := call str_cv(p);
  if ll != 1 { return 0 };
  (pl, so) := call str_param_sort(EREC⦃lo⦄);
  if ⟦ty⟧.tag != 6 { return 0 };
  (g, d, b, z) := call e_view(ty);
  if d == so && b == so { return 1 };
  return 0
}

/-- `list_nil_ty_ok(found, p)`: one level parameter `u`, type `Sort (u+1) → List.{u} #0`. -/
-- con-ron: ConRon/Arena/Core.lean:751-785 ConRon.Arena.listNilTyOk
@[no_expose, l_impl ConRon.Arena.listNilTyOk]
def listNilTyOkL : FunDecl :=
  lfn (found, p) locals (lo, ll, ty, pl, so, ps, li, g, d, b, z, f, x, l1, u1, i, y, w) {
  if found == 0 { return 0 };
  (lo, ll, ty) := call str_cv(p);
  if ll != 1 { return 0 };
  (pl, so) := call str_param_sort(EREC⦃lo⦄);
  ps := call str_ls1(pl);
  li := call pin_at(7);
  if ⟦ty⟧.tag != 6 { return 0 };
  (g, d, b, z) := call e_view(ty);
  if d != so { return 0 };
  if ⟦b⟧.tag != 4 { return 0 };
  (g, f, x, z) := call e_view(b);
  if ⟦f⟧.tag != 3 { return 0 };
  (g, l1, u1, z) := call e_view(f);
  if ⟦x⟧.tag != 0 { return 0 };
  (g, i, y, w) := call e_view(x);
  if i != 0 { return 0 };
  if l1 == li && u1 == ps { return 1 };
  return 0
}

/-- `list_cons_ty_ok(found, p)`: one level parameter `u`, type
`(α : Sort (u+1)) → α → List.{u} α → List.{u} α` (in de Bruijn indices). -/
-- con-ron: ConRon/Arena/Core.lean:787-823 ConRon.Arena.listConsTyOk
@[no_expose, l_impl ConRon.Arena.listConsTyOk]
def listConsTyOkL : FunDecl :=
  lfn (found, p) locals (lo, ll, ty, pl, so, ps, li, b0, b1, b2, l1, dom3, cod3, g, d, r, z,
    d2, r2, d3, c3) {
  if found == 0 { return 0 };
  (lo, ll, ty) := call str_cv(p);
  if ll != 1 { return 0 };
  (pl, so) := call str_param_sort(EREC⦃lo⦄);
  ps := call str_ls1(pl);
  li := call pin_at(7);
  b0 := call intern_bvar(0);
  b1 := call intern_bvar(1);
  b2 := call intern_bvar(2);
  l1 := call intern_const(li, ps);
  dom3 := call mk_app(l1, b1);
  cod3 := call mk_app(l1, b2);
  if ⟦ty⟧.tag != 6 { return 0 };
  (g, d, r, z) := call e_view(ty);
  if d != so { return 0 };
  if ⟦r⟧.tag != 6 { return 0 };
  (g, d2, r2, z) := call e_view(r);
  if d2 != b0 { return 0 };
  if ⟦r2⟧.tag != 6 { return 0 };
  (g, d3, c3, z) := call e_view(r2);
  if d3 == dom3 && c3 == cod3 { return 1 };
  return 0
}

/-- `char_of_nat_ty_ok(found, p)`: no level parameters, type `Nat → Char`. -/
-- con-ron: ConRon/Arena/Core.lean:825-840 ConRon.Arena.charOfNatTyOk
@[no_expose, l_impl ConRon.Arena.charOfNatTyOk]
def charOfNatTyOkL : FunDecl := lfn (found, p) locals (lo, ll, ty, nt, nc, ch, cc, g, d, b, z) {
  if found == 0 { return 0 };
  (lo, ll, ty) := call str_cv(p);
  if ll != 0 { return 0 };
  nt := call pin_at(1);
  nc := call const_e(nt);
  ch := call pin_at(10);
  cc := call const_e(ch);
  if ⟦ty⟧.tag != 6 { return 0 };
  (g, d, b, z) := call e_view(ty);
  if d == nc && b == cc { return 1 };
  return 0
}

/-- `string_of_list_ty_ok(found, p)`: no level parameters, type `List.{0} Char → String`. -/
-- con-ron: ConRon/Arena/Core.lean:842-863 ConRon.Arena.stringOfListTyOk
@[no_expose, l_impl ConRon.Arena.stringOfListTyOk]
def stringOfListTyOkL : FunDecl :=
  lfn (found, p) locals (lo, ll, ty, zl, zs, li, lc, ch, cc, dom, st, sc, g, d, b, z) {
  if found == 0 { return 0 };
  (lo, ll, ty) := call str_cv(p);
  if ll != 0 { return 0 };
  zl := call pin_word(53);
  zs := call str_ls1(zl);
  li := call pin_at(7);
  lc := call intern_const(li, zs);
  ch := call pin_at(10);
  cc := call const_e(ch);
  dom := call mk_app(lc, cc);
  st := call pin_at(5);
  sc := call const_e(st);
  if ⟦ty⟧.tag != 6 { return 0 };
  (g, d, b, z) := call e_view(ty);
  if d == dom && b == sc { return 1 };
  return 0
}

/-! ## `lit_shape_ok` -/

/-- `nat_ind_at_cv(q)`: `natIndOk (some (.indInfo cv {}))` at the constant value `q` (no level
parameters, type `Sort 1`): `nat_ind_ok` at a record of the kind `litShapeOk` builds. -/
-- con-ron: ConRon/Arena/Core.lean:564-570 ConRon.Arena.natIndOk
@[no_expose, l_impl ConRon.Arena.natIndOk]
def natIndAtCvL : FunDecl := lfn (q) locals (s1) {
  if EREC⦃q + ⟪CV.lpsLen⟫⦄ != 0 { return 0 };
  s1 := call pin_word(54);
  return u64(EREC⦃q + ⟪CV.type⟫⦄ == s1)
}

/-- `nat_zero_at_cv(q)`: `natZeroOk (some (.ctorInfo cv 0 0))` at the constant value `q` (no level
parameters, type `Nat`; `Nat` interned first, as the twin does). -/
-- con-ron: ConRon/Arena/Core.lean:572-579 ConRon.Arena.natZeroOk
@[no_expose, l_impl ConRon.Arena.natZeroOk]
def natZeroAtCvL : FunDecl := lfn (q) locals (nt, nc) {
  nt := call pin_at(1);
  nc := call const_e(nt);
  if EREC⦃q + ⟪CV.lpsLen⟫⦄ != 0 { return 0 };
  return u64(EREC⦃q + ⟪CV.type⟫⦄ == nc)
}

/-- `nat_succ_at_cv(q)`: `natSuccOk (some (.ctorInfo cv 0 1))` at the constant value `q` (no level
parameters, type `Nat → Nat`). -/
-- con-ron: ConRon/Arena/Core.lean:581-593 ConRon.Arena.natSuccOk
@[no_expose, l_impl ConRon.Arena.natSuccOk]
def natSuccAtCvL : FunDecl := lfn (q) locals (nt, nc, ty, t, i, dom, body) {
  if EREC⦃q + ⟪CV.lpsLen⟫⦄ != 0 { return 0 };
  nt := call pin_at(1);
  nc := call const_e(nt);
  ty := EREC⦃q + ⟪CV.type⟫⦄;
  if ⟦ty⟧.tag != 6 { return 0 };
  (t, i) := node FORALL⟦ty⟧;
  dom := FORALL⟨t, i⟩.ty;
  body := FORALL⟨t, i⟩.b;
  if dom == nc && body == nc { return 1 };
  return 0
}

/-- `lit_shape_ok(p)`: the shape a declaration (the record at `p`, its name at `p + CI.cv`) at a
literal's name must have; any other name passes. The three `Nat` names are read at the kinds their
guards ask for (`nat_ind_at_cv`, `nat_zero_at_cv`, `nat_succ_at_cv` at the record's constant value
`p + CI.cv`). The cited `if`-chain, each name pinned only when the chain reaches it. -/
-- con-ron: ConRon/Arena/Core.lean:865-883 ConRon.Arena.litShapeOk
@[no_expose, l_impl ConRon.Arena.litShapeOk]
def litShapeOkL : FunDecl := lfn (p) locals (n, x, r) {
  n := EREC⦃p + ⟪CI.cv + CV.name⟫⦄;
  x := call pin_at(1);
  if n == x { r := call nat_ind_at_cv(p + ⟪CI.cv⟫); return r };
  x := call pin_at(2);
  if n == x { r := call nat_zero_at_cv(p + ⟪CI.cv⟫); return r };
  x := call pin_at(3);
  if n == x { r := call nat_succ_at_cv(p + ⟪CI.cv⟫); return r };
  x := call pin_at(5);
  if n == x { r := call string_ty_ok(1, p); return r };
  x := call pin_at(6);
  if n == x { r := call string_of_list_ty_ok(1, p); return r };
  x := call pin_at(7);
  if n == x { r := call list_ty_ok(1, p); return r };
  x := call pin_at(8);
  if n == x { r := call list_nil_ty_ok(1, p); return r };
  x := call pin_at(9);
  if n == x { r := call list_cons_ty_ok(1, p); return r };
  x := call pin_at(10);
  if n == x { r := call char_ty_ok(1, p); return r };
  x := call pin_at(12);
  if n == x { r := call char_of_nat_ty_ok(1, p); return r };
  return 1
}

/-! ## `str_lit_ctor` -/

/-- `str_utf8_char(k, n)`: `utf8_char` on the pool's byte words `[k, n)` (each masked to a byte):
the code point at `k` and its length, `(0, 0)` for invalid bytes. -/
-- con-ron: none — `s.toList`'s decoding of the literal's UTF-8 bytes (`utf8_char` on the pool)
@[no_expose] def strUtf8CharL : FunDecl := lfn (k, n) locals (c0, c1, c2, c3, v) {
  c0 := POOL⦃k⦄ & 255;
  if c0 < 0x80 { return (c0, 1) };
  if c0 < 0xC2 { return (0, 0) };
  if c0 < 0xE0 {
    if n <= k + 1 { return (0, 0) };
    c1 := POOL⦃k + 1⦄ & 255;
    if c1 < 0x80 || 0xC0 <= c1 { return (0, 0) };
    return (((c0 & 0x1F) << 6) | (c1 & 0x3F), 2)
  };
  if c0 < 0xF0 {
    if n <= k + 2 { return (0, 0) };
    c1 := POOL⦃k + 1⦄ & 255;
    c2 := POOL⦃k + 2⦄ & 255;
    if c1 < 0x80 || 0xC0 <= c1 || c2 < 0x80 || 0xC0 <= c2 { return (0, 0) };
    v := ((c0 & 0x0F) << 12) | ((c1 & 0x3F) << 6) | (c2 & 0x3F);
    if v < 0x800 || (0xD800 <= v && v < 0xE000) { return (0, 0) };
    return (v, 3)
  };
  if c0 < 0xF5 {
    if n <= k + 3 { return (0, 0) };
    c1 := POOL⦃k + 1⦄ & 255;
    c2 := POOL⦃k + 2⦄ & 255;
    c3 := POOL⦃k + 3⦄ & 255;
    if c1 < 0x80 || 0xC0 <= c1 || c2 < 0x80 || 0xC0 <= c2 || c3 < 0x80 || 0xC0 <= c3 {
      return (0, 0)
    };
    v := ((c0 & 0x07) << 18) | ((c1 & 0x3F) << 12) | ((c2 & 0x3F) << 6) | (c3 & 0x3F);
    if v < 0x10000 || 0x10FFFF < v { return (0, 0) };
    return (v, 4)
  };
  return (0, 0)
}

/-- `str_cons_spine(cons, ofNat, nilE, k, n)`: the `List.cons` spine of the characters whose UTF-8
bytes are the pool words `[k, n)`; the rest of the spine first, then the character's nodes, as the
twin's recursion interns them. -/
-- con-ron: ConRon/Arena/Core.lean:679-691 ConRon.Arena.strLitConsSpine
@[no_expose, l_impl ConRon.Arena.strLitConsSpine]
def strConsSpineL : FunDecl := lfn (cons, ofNat, nilE, k, n) locals (c, l, rest, lit, ch, f, r) {
  if n <= k { return nilE };
  (c, l) := call str_utf8_char(k, n);
  if l == 0 { abort };
  rest := call str_cons_spine(cons, ofNat, nilE, k + l, n);
  lit := call rom_lit(c);
  ch := call mk_app(ofNat, lit);
  f := call mk_app(cons, ch);
  r := call mk_app(f, rest);
  return r
}

/-- `str_ctor_pre()`: `(cons, ofNat, nilE)`, the three nodes every string literal's constructor
form uses (`List.cons.{0} Char`, `Char.ofNat`, `List.nil.{0} Char`), interned in the twin's order. -/
-- con-ron: none — the literal-independent prefix of `strLitToConstructor` (no twin function)
@[no_expose] def strCtorPreL : FunDecl :=
  lfn () locals (zl, zs, chN, chC, lnN, ln, nilE, lcN, lc, cons, coN, ofNat) {
  zl := call pin_word(53);
  zs := call str_ls1(zl);
  chN := call pin_at(10);
  chC := call const_e(chN);
  lnN := call pin_at(8);
  ln := call intern_const(lnN, zs);
  nilE := call mk_app(ln, chC);
  lcN := call pin_at(9);
  lc := call intern_const(lcN, zs);
  cons := call mk_app(lc, chC);
  coN := call pin_at(12);
  ofNat := call const_e(coN);
  return (cons, ofNat, nilE)
}

/-- `str_lit_ctor(h)`: the constructor form `String.ofList (List.cons.{0} Char (Char.ofNat c₁) …
(List.nil.{0} Char))` of the string literal `h`: the prefix, then the literal's record (read
after the prefix, so at the memory the spine reads) gives the bytes' pool slice. -/
-- con-ron: ConRon/Arena/Core.lean:693-712 ConRon.Arena.strLitToConstructor
@[no_expose, l_impl ConRon.Arena.strLitToConstructor]
def strLitCtorL : FunDecl :=
  lfn (h) locals (cons, ofNat, nilE, t, i, o, cnt, spine, slN, sl, r) {
  (cons, ofNat, nilE) := call str_ctor_pre();
  if ⟦h⟧.tag != 8 { abort };
  (t, i) := node LIT⟦h⟧;
  if LIT⟨t, i⟩.kind != 1 { abort };
  o := LIT⟨t, i⟩.o;
  cnt := LIT⟨t, i⟩.l;
  spine := call str_cons_spine(cons, ofNat, nilE, o, o + cnt);
  slN := call pin_at(6);
  sl := call const_e(slN);
  r := call mk_app(sl, spine);
  return r
}

end L.Arena
