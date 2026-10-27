import ConAgua.Arena.Tiers

/-!
# String literals in L: `str_lit_supported`, `str_lit_ctor` (lane `defeq2`, helper `defeq2-str`)

Twin: `vendor/con-ron/ConRon/Arena/Core.lean` ("String literals"). L names and their twins:

| L | twin | notes |
|---|---|---|
| `str_cv(p)` | `IConstantInfo.toConstantVal` | `(lo, ll, ty)`: the level parameters' `EREC` slice and the type; a projection table interns `Sort 1` |
| `string_ty_ok`, `char_ty_ok` | `stringTyOk`, `charTyOk` | one body (the twins are the same) |
| `str_param_sort(pn)` | none | `internLNode (.param p)`, `.succ`, `internE (.sort ·)`: the prefix of the three `List` tests |
| `str_ls1(u)` | `internLsNode [u]` | the one-element list at the pool top |
| `list_ty_ok`, `list_nil_ty_ok`, `list_cons_ty_ok`, `char_of_nat_ty_ok`, `string_of_list_ty_ok` | the `…TyOk` tests | `(found, q)` is `find?`'s result, as `nat_ind_ok` |
| `str_lit_supported(vis)`, `str_sup_1` … `str_sup_7` | `strLitSupported` | one function per tested declaration (the suffixes of the twin's chain) |
| `str_utf8_char(k, n)` | none | `utf8_char` (`Scan/Utf8.lean`) on the pool's byte words: one code point of `s.toList` |
| `str_cons_spine(cons, ofNat, nilE, k, n)` | `strLitConsSpine` | the bytes `[k, n)` of the pool; recursion over the characters as the twin's |
| `str_ctor_pre()` | none | the literal-independent prefix of `strLitToConstructor` |
| `str_lit_ctor(h)` | `strLitToConstructor` | the literal's record gives the byte slice |

A character's `Nat` literal is interned by `rom_lit` (`RomExpr.lean`: its one limb at the pool
top). Every view is the twin's: a tag test, then `e_view`.
-/


namespace L.Arena

/-- `str_cv(p)`: the constant value of the record at `p` (`IConstantInfo.toConstantVal`, inline at
`p + 1`) as `(lo, ll, ty)`: the level parameters `EREC[lo‥lo+ll)` and the type. -/
-- con-ron: ConRon/Arena/Env.lean:176-180 ConRon.Arena.IConstantInfo.toConstantVal
def strCvL : FunDecl := lfn (p) locals () {
  return (EREC.u64[p + 2], EREC.u64[p + 3], EREC.u64[p + 4])
}

/-- `string_ty_ok(found, p)`: no level parameters, type `Sort 1`. -/
-- con-ron: ConRon/Arena/Core.lean:621-628 ConRon.Arena.stringTyOk
@[l_impl ConRon.Arena.stringTyOk]
def stringTyOkL : FunDecl := lfn (found, p) locals (lo, ll, ty, s1) {
  if found == 0 { return 0 };
  (lo, ll, ty) := call str_cv(p);
  s1 := call pin_word(54);
  if ll == 0 && ty == s1 { return 1 };
  return 0
}

/-- `char_ty_ok(found, p)`: `string_ty_ok`'s body (the twins are the same). -/
-- con-ron: ConRon/Arena/Core.lean:630-637 ConRon.Arena.charTyOk
@[l_impl ConRon.Arena.charTyOk]
def charTyOkL : FunDecl := stringTyOkL

/-- `str_param_sort(pn)`: `(pl, so)` with `pl` the level `param pn` and `so` the expression
`Sort (succ pl)`, interned in the twin's order. -/
-- con-ron: none — the shared prefix of `listTyOk`, `listNilTyOk`, `listConsTyOk` (no twin function)
def strParamSortL : FunDecl := lfn (pn) locals (pl, sp, so) {
  pl := call intern_param(pn);
  sp := call intern_succ(pl);
  so := call intern_sort(sp);
  return (pl, so)
}

/-- `str_ls1(u)`: the level list `[u]`, its one handle word at the pool top. -/
-- con-ron: ConRon/Arena/Monad.lean:499-515 ConRon.Arena.internLsNode
def strLs1L : FunDecl := lfn (u) locals (o, h, pt, pb) {
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
-- con-ron: ConRon/Arena/Core.lean:639-656 ConRon.Arena.listTyOk
@[l_impl ConRon.Arena.listTyOk]
def listTyOkL : FunDecl := lfn (found, p) locals (lo, ll, ty, pl, so, g, d, b, z) {
  if found == 0 { return 0 };
  (lo, ll, ty) := call str_cv(p);
  if ll != 1 { return 0 };
  (pl, so) := call str_param_sort(EREC.u64[lo]);
  if ty >> 28 != 6 { return 0 };
  (g, d, b, z) := call e_view(ty);
  if d == so && b == so { return 1 };
  return 0
}

/-- `list_nil_ty_ok(found, p)`: one level parameter `u`, type `Sort (u+1) → List.{u} #0`. -/
-- con-ron: ConRon/Arena/Core.lean:658-692 ConRon.Arena.listNilTyOk
@[l_impl ConRon.Arena.listNilTyOk]
def listNilTyOkL : FunDecl :=
  lfn (found, p) locals (lo, ll, ty, pl, so, ps, li, g, d, b, z, f, x, l1, u1, i, y, w) {
  if found == 0 { return 0 };
  (lo, ll, ty) := call str_cv(p);
  if ll != 1 { return 0 };
  (pl, so) := call str_param_sort(EREC.u64[lo]);
  ps := call str_ls1(pl);
  li := call pin_at(7);
  if ty >> 28 != 6 { return 0 };
  (g, d, b, z) := call e_view(ty);
  if d != so { return 0 };
  if b >> 28 != 4 { return 0 };
  (g, f, x, z) := call e_view(b);
  if f >> 28 != 3 { return 0 };
  (g, l1, u1, z) := call e_view(f);
  if x >> 28 != 0 { return 0 };
  (g, i, y, w) := call e_view(x);
  if i != 0 { return 0 };
  if l1 == li && u1 == ps { return 1 };
  return 0
}

/-- `list_cons_ty_ok(found, p)`: one level parameter `u`, type
`(α : Sort (u+1)) → α → List.{u} α → List.{u} α` (in de Bruijn indices). -/
-- con-ron: ConRon/Arena/Core.lean:694-730 ConRon.Arena.listConsTyOk
@[l_impl ConRon.Arena.listConsTyOk]
def listConsTyOkL : FunDecl :=
  lfn (found, p) locals (lo, ll, ty, pl, so, ps, li, b0, b1, b2, l1, dom3, cod3, g, d, r, z,
    d2, r2, d3, c3) {
  if found == 0 { return 0 };
  (lo, ll, ty) := call str_cv(p);
  if ll != 1 { return 0 };
  (pl, so) := call str_param_sort(EREC.u64[lo]);
  ps := call str_ls1(pl);
  li := call pin_at(7);
  b0 := call intern_bvar(0);
  b1 := call intern_bvar(1);
  b2 := call intern_bvar(2);
  l1 := call intern_const(li, ps);
  dom3 := call mk_app(l1, b1);
  cod3 := call mk_app(l1, b2);
  if ty >> 28 != 6 { return 0 };
  (g, d, r, z) := call e_view(ty);
  if d != so { return 0 };
  if r >> 28 != 6 { return 0 };
  (g, d2, r2, z) := call e_view(r);
  if d2 != b0 { return 0 };
  if r2 >> 28 != 6 { return 0 };
  (g, d3, c3, z) := call e_view(r2);
  if d3 == dom3 && c3 == cod3 { return 1 };
  return 0
}

/-- `char_of_nat_ty_ok(found, p)`: no level parameters, type `Nat → Char`. -/
-- con-ron: ConRon/Arena/Core.lean:732-747 ConRon.Arena.charOfNatTyOk
@[l_impl ConRon.Arena.charOfNatTyOk]
def charOfNatTyOkL : FunDecl := lfn (found, p) locals (lo, ll, ty, nt, nc, ch, cc, g, d, b, z) {
  if found == 0 { return 0 };
  (lo, ll, ty) := call str_cv(p);
  if ll != 0 { return 0 };
  nt := call pin_at(1);
  nc := call const_e(nt);
  ch := call pin_at(10);
  cc := call const_e(ch);
  if ty >> 28 != 6 { return 0 };
  (g, d, b, z) := call e_view(ty);
  if d == nc && b == cc { return 1 };
  return 0
}

/-- `string_of_list_ty_ok(found, p)`: no level parameters, type `List.{0} Char → String`. -/
-- con-ron: ConRon/Arena/Core.lean:749-770 ConRon.Arena.stringOfListTyOk
@[l_impl ConRon.Arena.stringOfListTyOk]
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
  if ty >> 28 != 6 { return 0 };
  (g, d, b, z) := call e_view(ty);
  if d == dom && b == sc { return 1 };
  return 0
}

/-! ## `str_lit_supported`: one function per tested declaration -/

/-- `str_sup_7(vis)`: `Char.ofNat`. -/
-- con-ron: ConRon/Arena/Core.lean:772-791 ConRon.Arena.strLitSupported
def strSup7L : FunDecl := lfn (vis) locals (x, f, q, r) {
  x := call pin_at(12);
  (f, q) := call env_find(x, vis);
  r := call char_of_nat_ty_ok(f, q);
  return r
}

/-- `str_sup_6(vis)`: `Char`, then `str_sup_7`. -/
-- con-ron: ConRon/Arena/Core.lean:772-791 ConRon.Arena.strLitSupported
def strSup6L : FunDecl := lfn (vis) locals (x, f, q, r) {
  x := call pin_at(10);
  (f, q) := call env_find(x, vis);
  r := call char_ty_ok(f, q);
  if r == 0 { return 0 };
  r := call str_sup_7(vis);
  return r
}

/-- `str_sup_5(vis)`: `List.cons`, then `str_sup_6`. -/
-- con-ron: ConRon/Arena/Core.lean:772-791 ConRon.Arena.strLitSupported
def strSup5L : FunDecl := lfn (vis) locals (x, f, q, r) {
  x := call pin_at(9);
  (f, q) := call env_find(x, vis);
  r := call list_cons_ty_ok(f, q);
  if r == 0 { return 0 };
  r := call str_sup_6(vis);
  return r
}

/-- `str_sup_4(vis)`: `List.nil`, then `str_sup_5`. -/
-- con-ron: ConRon/Arena/Core.lean:772-791 ConRon.Arena.strLitSupported
def strSup4L : FunDecl := lfn (vis) locals (x, f, q, r) {
  x := call pin_at(8);
  (f, q) := call env_find(x, vis);
  r := call list_nil_ty_ok(f, q);
  if r == 0 { return 0 };
  r := call str_sup_5(vis);
  return r
}

/-- `str_sup_3(vis)`: `List`, then `str_sup_4`. -/
-- con-ron: ConRon/Arena/Core.lean:772-791 ConRon.Arena.strLitSupported
def strSup3L : FunDecl := lfn (vis) locals (x, f, q, r) {
  x := call pin_at(7);
  (f, q) := call env_find(x, vis);
  r := call list_ty_ok(f, q);
  if r == 0 { return 0 };
  r := call str_sup_4(vis);
  return r
}

/-- `str_sup_2(vis)`: `String.ofList`, then `str_sup_3`. -/
-- con-ron: ConRon/Arena/Core.lean:772-791 ConRon.Arena.strLitSupported
def strSup2L : FunDecl := lfn (vis) locals (x, f, q, r) {
  x := call pin_at(6);
  (f, q) := call env_find(x, vis);
  r := call string_of_list_ty_ok(f, q);
  if r == 0 { return 0 };
  r := call str_sup_3(vis);
  return r
}

/-- `str_sup_1(vis)`: `String`, then `str_sup_2`. -/
-- con-ron: ConRon/Arena/Core.lean:772-791 ConRon.Arena.strLitSupported
def strSup1L : FunDecl := lfn (vis) locals (x, f, q, r) {
  x := call pin_at(5);
  (f, q) := call env_find(x, vis);
  r := call string_ty_ok(f, q);
  if r == 0 { return 0 };
  r := call str_sup_2(vis);
  return r
}

/-- `str_lit_supported(vis)`: the `Nat` literal guard, then the seven declarations. -/
-- con-ron: ConRon/Arena/Core.lean:772-791 ConRon.Arena.strLitSupported
@[l_impl ConRon.Arena.strLitSupported]
def strLitSupportedL : FunDecl := lfn (vis) locals (r) {
  r := call nat_lit_supported(vis);
  if r == 0 { return 0 };
  r := call str_sup_1(vis);
  return r
}

/-! ## `str_lit_ctor` -/

/-- `str_utf8_char(k, n)`: `utf8_char` on the pool's byte words `[k, n)` (each masked to a byte):
the code point at `k` and its length, `(0, 0)` for invalid bytes. -/
-- con-ron: none — `s.toList`'s decoding of the literal's UTF-8 bytes (`utf8_char` on the pool)
def strUtf8CharL : FunDecl := lfn (k, n) locals (c0, c1, c2, c3, v) {
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
-- con-ron: ConRon/Arena/Core.lean:586-598 ConRon.Arena.strLitConsSpine
@[l_impl ConRon.Arena.strLitConsSpine]
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
def strCtorPreL : FunDecl :=
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
-- con-ron: ConRon/Arena/Core.lean:600-619 ConRon.Arena.strLitToConstructor
@[l_impl ConRon.Arena.strLitToConstructor]
def strLitCtorL : FunDecl :=
  lfn (h) locals (cons, ofNat, nilE, t, i, o, cnt, spine, slN, sl, r) {
  (cons, ofNat, nilE) := call str_ctor_pre();
  if h >> 28 != 8 { abort };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if LIT⟨t⟩.count <= i { abort };
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
