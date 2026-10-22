import ConAgua.Arena.WhnfDelta

/-!
# String literals: `str_lit_supported`, `str_lit_ctor` and their helpers (lane `whnf3`)

con-ron's `Arena/Core.lean:585-788`, in L:

| L | twin |
|---|---|
| `ci_lp_ty(p)` | `IConstantInfo.toConstantVal` at record `p`, read as `(lp offset, lp count, type)`: kinds 0‥5 read the stored value; a `projInfo` interns `Sort 1` (as the twin) |
| `ls_one(x)` | `internLsNode [x]`: `x` pushed at the pool top, `intern_ls` over the one-word slice |
| `string_ty_ok`, `char_ty_ok`, `list_ty_ok`, `list_nil_ty_ok`, `list_cons_ty_ok`, `char_of_nat_ty_ok`, `string_of_list_ty_ok` `(found, p)` | the seven `*TyOk` at `fe.find?`'s answer `(found, p)` (`env_find`) |
| `str_lit_supported(vis)` | `strLitSupported fe` |
| `lit_char(c)` | `internE (.lit (.natVal c))` for a code point `c` (one limb at the pool top, none for `0`) |
| `str_lit_spine(cons, ofNat, nilE, so, k)` | `strLitConsSpine cons ofNat nilE cs`, the code points a stack slice `(so, k)`, interned from the last |
| `str_lit_ctor(h)` | `strLitToConstructor s` at the `strVal` literal `h`: its UTF-8 bytes (`REC` kind `1`, a pool slice) decoded into code points on the spine stack above its top |

The twin's `internLsNode`/`internE` of a literal allocate nothing when the node exists; L writes
the list's word or the limb at the pool top first (the store's refinements need the slice below
the top), on every call (`docs/deviations.md`, D20).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- `ci_lp_ty(p)`: `(lp offset, lp count, type)` of the constant record `p` (`toConstantVal`). -/
-- con-ron: ConRon/Arena/Env.lean:203-214 ConRon.Arena.IConstantInfo.toConstantVal
@[l_impl ConRon.Arena.IConstantInfo.toConstantVal]
def ciLpTyL : FunDecl := lfn (p) locals (k, z, o, t) {
  k := EREC.u64[p];
  if k <= 5 { return (EREC.u64[p + 2], EREC.u64[p + 3], EREC.u64[p + 4]) };
  if k != 6 { abort };
  z := call intern_zero();
  if 4294967296 <= z { abort };
  o := call intern_succ(z);
  if 4294967296 <= o { abort };
  t := call intern_sort(o);
  if 4294967296 <= t { abort };
  return (EREC.u64[p + 3], EREC.u64[p + 4], t)
}

/-- `ls_one(x)`: the level list `[x]`. -/
-- con-ron: ConRon/Arena/Monad.lean:499-515 ConRon.Arena.internLsNode
@[l_impl ConRon.Arena.internLsNode]
def lsOneL : FunDecl := lfn (x) locals (o, h) {
  o := CTL.u64[0];
  if len(POOL.u64) <= o { abort };
  POOL.u64[o] := x;
  CTL.u64[0] := o + 1;
  h := call intern_ls(o, 1);
  if 4294967296 <= h { abort };
  return h
}

/-- `string_ty_ok(found, p)`. -/
-- con-ron: ConRon/Arena/Core.lean:621-628 ConRon.Arena.stringTyOk
@[l_impl ConRon.Arena.stringTyOk]
def stringTyOkL : FunDecl := lfn (found, p) locals (lo, ll, ty, s1) {
  if found == 0 { return 0 };
  (lo, ll, ty) := call ci_lp_ty(p);
  s1 := call pin_word(54);
  if ll == 0 && ty == s1 { return 1 };
  return 0
}

/-- `char_ty_ok(found, p)`. -/
-- con-ron: ConRon/Arena/Core.lean:630-637 ConRon.Arena.charTyOk
@[l_impl ConRon.Arena.charTyOk]
def charTyOkL : FunDecl := lfn (found, p) locals (lo, ll, ty, s1) {
  if found == 0 { return 0 };
  (lo, ll, ty) := call ci_lp_ty(p);
  s1 := call pin_word(54);
  if ll == 0 && ty == s1 { return 1 };
  return 0
}

/-- `list_ty_ok(found, p)`: `List.{p} : Type p → Type p`. -/
-- con-ron: ConRon/Arena/Core.lean:639-656 ConRon.Arena.listTyOk
@[l_impl ConRon.Arena.listTyOk]
def listTyOkL : FunDecl := lfn (found, p) locals (lo, ll, ty, pl, sp, srt, t, i, d, b) {
  if found == 0 { return 0 };
  (lo, ll, ty) := call ci_lp_ty(p);
  if ll != 1 { return 0 };
  pl := call intern_param(EREC.u64[lo]);
  if 4294967296 <= pl { abort };
  sp := call intern_succ(pl);
  if 4294967296 <= sp { abort };
  srt := call intern_sort(sp);
  if 4294967296 <= srt { abort };
  if ty >> 28 != 6 { return 0 };
  t := (ty >> 27) & 1;
  i := ty & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[30 + t] <= i { abort };
  d := FAREC.u64[i * 4 + t * 2];
  b := FAREC.u64[i * 4 + t * 2 + 1];
  if d == srt && b == srt { return 1 };
  return 0
}

/-- `list_nil_ty_ok(found, p)`: `List.nil.{p} : (α : Type p) → List.{p} α`. -/
-- con-ron: ConRon/Arena/Core.lean:658-692 ConRon.Arena.listNilTyOk
@[l_impl ConRon.Arena.listNilTyOk]
def listNilTyOkL : FunDecl :=
    lfn (found, p) locals (lo, ll, ty, pl, sp, srt, ps, li, t, i, d, b, f, a, l1, us1) {
  if found == 0 { return 0 };
  (lo, ll, ty) := call ci_lp_ty(p);
  if ll != 1 { return 0 };
  pl := call intern_param(EREC.u64[lo]);
  if 4294967296 <= pl { abort };
  sp := call intern_succ(pl);
  if 4294967296 <= sp { abort };
  srt := call intern_sort(sp);
  if 4294967296 <= srt { abort };
  ps := call ls_one(pl);
  li := call pin_at(7);
  if ty >> 28 != 6 { return 0 };
  t := (ty >> 27) & 1;
  i := ty & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[30 + t] <= i { abort };
  d := FAREC.u64[i * 4 + t * 2];
  b := FAREC.u64[i * 4 + t * 2 + 1];
  if d != srt { return 0 };
  if b >> 28 != 4 { return 0 };
  t := (b >> 27) & 1;
  i := b & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[4 + t] <= i { abort };
  f := AREC.u64[i * 4 + t * 2];
  a := AREC.u64[i * 4 + t * 2 + 1];
  if f >> 28 != 3 { return 0 };
  t := (f >> 27) & 1;
  i := f & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[18 + t] <= i { abort };
  l1 := CREC.u64[i * 4 + t * 2];
  us1 := CREC.u64[i * 4 + t * 2 + 1];
  if a >> 28 != 0 { return 0 };
  t := (a >> 27) & 1;
  i := a & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[22 + t] <= i { abort };
  if BREC.u64[i * 2 + t] != 0 { return 0 };
  if l1 == li && us1 == ps { return 1 };
  return 0
}

/-- `list_cons_ty_ok(found, p)`: `List.cons.{p} : (α : Type p) → α → List.{p} α → List.{p} α`. -/
-- con-ron: ConRon/Arena/Core.lean:694-730 ConRon.Arena.listConsTyOk
@[l_impl ConRon.Arena.listConsTyOk]
def listConsTyOkL : FunDecl :=
    lfn (found, p) locals (lo, ll, ty, pl, sp, srt, ps, li, b0, b1, b2, l1, dom3, cod3, t, i, d, r) {
  if found == 0 { return 0 };
  (lo, ll, ty) := call ci_lp_ty(p);
  if ll != 1 { return 0 };
  pl := call intern_param(EREC.u64[lo]);
  if 4294967296 <= pl { abort };
  sp := call intern_succ(pl);
  if 4294967296 <= sp { abort };
  srt := call intern_sort(sp);
  if 4294967296 <= srt { abort };
  ps := call ls_one(pl);
  li := call pin_at(7);
  b0 := call intern_bvar(0);
  b1 := call intern_bvar(1);
  b2 := call intern_bvar(2);
  l1 := call intern_const(li, ps);
  dom3 := call mk_app(l1, b1);
  cod3 := call mk_app(l1, b2);
  if ty >> 28 != 6 { return 0 };
  t := (ty >> 27) & 1;
  i := ty & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[30 + t] <= i { abort };
  d := FAREC.u64[i * 4 + t * 2];
  r := FAREC.u64[i * 4 + t * 2 + 1];
  if d != srt { return 0 };
  if r >> 28 != 6 { return 0 };
  t := (r >> 27) & 1;
  i := r & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[30 + t] <= i { abort };
  d := FAREC.u64[i * 4 + t * 2];
  r := FAREC.u64[i * 4 + t * 2 + 1];
  if d != b0 { return 0 };
  if r >> 28 != 6 { return 0 };
  t := (r >> 27) & 1;
  i := r & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[30 + t] <= i { abort };
  d := FAREC.u64[i * 4 + t * 2];
  r := FAREC.u64[i * 4 + t * 2 + 1];
  if d == dom3 && r == cod3 { return 1 };
  return 0
}

/-- `char_of_nat_ty_ok(found, p)`: `Char.ofNat : Nat → Char`. -/
-- con-ron: ConRon/Arena/Core.lean:732-747 ConRon.Arena.charOfNatTyOk
@[l_impl ConRon.Arena.charOfNatTyOk]
def charOfNatTyOkL : FunDecl := lfn (found, p) locals (lo, ll, ty, nt, nc, ch, cc, t, i, d, b) {
  if found == 0 { return 0 };
  (lo, ll, ty) := call ci_lp_ty(p);
  if ll != 0 { return 0 };
  nt := call pin_at(1);
  nc := call const_e(nt);
  ch := call pin_at(10);
  cc := call const_e(ch);
  if ty >> 28 != 6 { return 0 };
  t := (ty >> 27) & 1;
  i := ty & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[30 + t] <= i { abort };
  d := FAREC.u64[i * 4 + t * 2];
  b := FAREC.u64[i * 4 + t * 2 + 1];
  if d == nc && b == cc { return 1 };
  return 0
}

/-- `string_of_list_ty_ok(found, p)`: `String.ofList : List.{0} Char → String`. -/
-- con-ron: ConRon/Arena/Core.lean:749-770 ConRon.Arena.stringOfListTyOk
@[l_impl ConRon.Arena.stringOfListTyOk]
def stringOfListTyOkL : FunDecl :=
    lfn (found, p) locals (lo, ll, ty, z, zs, li, lc, ch, cc, dom, st, sc, t, i, d, b) {
  if found == 0 { return 0 };
  (lo, ll, ty) := call ci_lp_ty(p);
  if ll != 0 { return 0 };
  z := call pin_word(53);
  zs := call ls_one(z);
  li := call pin_at(7);
  lc := call intern_const(li, zs);
  ch := call pin_at(10);
  cc := call const_e(ch);
  dom := call mk_app(lc, cc);
  st := call pin_at(5);
  sc := call const_e(st);
  if ty >> 28 != 6 { return 0 };
  t := (ty >> 27) & 1;
  i := ty & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[30 + t] <= i { abort };
  d := FAREC.u64[i * 4 + t * 2];
  b := FAREC.u64[i * 4 + t * 2 + 1];
  if d == dom && b == sc { return 1 };
  return 0
}

/-- `str_lit_supported(vis)`: the `Nat` literal guard and the seven string declarations. -/
-- con-ron: ConRon/Arena/Core.lean:772-791 ConRon.Arena.strLitSupported
@[l_impl ConRon.Arena.strLitSupported]
def strLitSupportedL : FunDecl := lfn (vis) locals (r, n, f, p) {
  r := call nat_lit_supported(vis);
  if r == 0 { return 0 };
  n := call pin_at(5);
  (f, p) := call env_find(n, vis);
  r := call string_ty_ok(f, p);
  if r == 0 { return 0 };
  n := call pin_at(6);
  (f, p) := call env_find(n, vis);
  r := call string_of_list_ty_ok(f, p);
  if r == 0 { return 0 };
  n := call pin_at(7);
  (f, p) := call env_find(n, vis);
  r := call list_ty_ok(f, p);
  if r == 0 { return 0 };
  n := call pin_at(8);
  (f, p) := call env_find(n, vis);
  r := call list_nil_ty_ok(f, p);
  if r == 0 { return 0 };
  n := call pin_at(9);
  (f, p) := call env_find(n, vis);
  r := call list_cons_ty_ok(f, p);
  if r == 0 { return 0 };
  n := call pin_at(10);
  (f, p) := call env_find(n, vis);
  r := call char_ty_ok(f, p);
  if r == 0 { return 0 };
  n := call pin_at(12);
  (f, p) := call env_find(n, vis);
  r := call char_of_nat_ty_ok(f, p);
  return r
}

/-! ## The constructor form -/

/-- `lit_char(c)`: the `Nat` literal `c` (zero limbs at `0`, else the one limb `c`). -/
-- con-ron: ConRon/Arena/Monad.lean:246-264 ConRon.Arena.internE
def litCharL : FunDecl := lfn (c) locals (o, h) {
  o := CTL.u64[0];
  if c == 0 {
    h := call intern_lit(o, 0);
    return h
  };
  if len(POOL.u64) <= o { abort };
  POOL.u64[o] := c;
  CTL.u64[0] := o + 1;
  h := call intern_lit(o, 1);
  return h
}

/-- `str_lit_spine(cons, ofNat, nilE, so, k)`: the `List.cons` spine of the code points
`SPN[so]`, …, `SPN[so + k - 1]`, interned from the last (the twin's recursion interns the rest
first). -/
-- con-ron: ConRon/Arena/Core.lean:586-598 ConRon.Arena.strLitConsSpine
@[l_impl ConRon.Arena.strLitConsSpine]
def strLitSpineL : FunDecl := lfn (cons, ofNat, nilE, so, k) locals (sp, c, lit, ch, f) {
  sp := nilE;
  while 0 < k {
    k := k - 1;
    c := SPN.u64[so + k];
    lit := call lit_char(c);
    if 4294967296 <= lit { abort };
    ch := call mk_app(ofNat, lit);
    f := call mk_app(cons, ch);
    sp := call mk_app(f, sp)
  };
  return sp
}

/-- `str_cps(o, l, so)`: the code points of the UTF-8 bytes `POOL[o]`, …, `POOL[o + l - 1]`
(one byte per word, well formed: the bytes of a `String`) written at `SPN[so]`, …; their count. -/
-- con-ron: none — `String.toList` of a `strVal` literal, whose characters L keeps as UTF-8 bytes
def strCpsL : FunDecl := lfn (o, l, so) locals (j, k, b, c) {
  j := 0;
  k := 0;
  while j < l {
    if len(SPN.u64) <= so + k { abort };
    b := POOL.u64[o + j];
    if b < 128 {
      c := b;
      j := j + 1
    } else {
      if b < 224 {
        c := ((b & 31) << 6) | (POOL.u64[o + j + 1] & 63);
        j := j + 2
      } else {
        if b < 240 {
          c := (((b & 15) << 12) | ((POOL.u64[o + j + 1] & 63) << 6)) | (POOL.u64[o + j + 2] & 63);
          j := j + 3
        } else {
          c := ((((b & 7) << 18) | ((POOL.u64[o + j + 1] & 63) << 12)) |
            ((POOL.u64[o + j + 2] & 63) << 6)) | (POOL.u64[o + j + 3] & 63);
          j := j + 4
        }
      }
    };
    SPN.u64[so + k] := c;
    k := k + 1
  };
  return k
}

/-- `str_lit_ctor(h)`: the constructor form of the `String` literal `h`. -/
-- con-ron: ConRon/Arena/Core.lean:600-619 ConRon.Arena.strLitToConstructor
@[l_impl ConRon.Arena.strLitToConstructor]
def strLitCtorL : FunDecl :=
    lfn (h) locals (t, i, o, l, z, zs, chN, chC, lnN, ln, nilE, lcN, lc, cons, coN, ofNat, so, k,
      sp, slN, sl, r) {
  if 4294967295 < h { abort };
  if h >> 28 != 8 { abort };
  t := (h >> 27) & 1;
  i := h & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[2 + t] <= i { abort };
  if REC.u64[i * 8 + t * 4] != 1 { abort };
  o := REC.u64[i * 8 + t * 4 + 1];
  l := REC.u64[i * 8 + t * 4 + 2];
  z := call pin_word(53);
  zs := call ls_one(z);
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
  so := CTL.u64[136];
  k := call str_cps(o, l, so);
  sp := call str_lit_spine(cons, ofNat, nilE, so, k);
  slN := call pin_at(6);
  sl := call const_e(slN);
  r := call mk_app(sl, sp);
  return r
}

/-- **The lookups of this file's functions.** -/
structure StrLitProg (p : Prog) : Prop where
  ciLpTy : p.lookup "ci_lp_ty" = some ciLpTyL
  lsOne : p.lookup "ls_one" = some lsOneL
  stringTyOk : p.lookup "string_ty_ok" = some stringTyOkL
  charTyOk : p.lookup "char_ty_ok" = some charTyOkL
  listTyOk : p.lookup "list_ty_ok" = some listTyOkL
  listNilTyOk : p.lookup "list_nil_ty_ok" = some listNilTyOkL
  listConsTyOk : p.lookup "list_cons_ty_ok" = some listConsTyOkL
  charOfNatTyOk : p.lookup "char_of_nat_ty_ok" = some charOfNatTyOkL
  stringOfListTyOk : p.lookup "string_of_list_ty_ok" = some stringOfListTyOkL
  strLitSupported : p.lookup "str_lit_supported" = some strLitSupportedL
  litChar : p.lookup "lit_char" = some litCharL
  strLitSpine : p.lookup "str_lit_spine" = some strLitSpineL
  strCps : p.lookup "str_cps" = some strCpsL
  strLitCtor : p.lookup "str_lit_ctor" = some strLitCtorL

end L.Arena
