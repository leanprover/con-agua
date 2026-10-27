import ConAgua.Arena.IndIface
import ConAgua.Census.Attr

/-!
# `checkDecl`'s one-constant arms in L, part 1: comparisons of constants (lane `decls2`)

The twin's `Canon.lean` (the lockstep canonical-form comparisons `IConstantInfo.canonEq`,
`canonEqList`, …), `IConstantInfo.toConstantVal`, and the derived equalities the arms test
(`fe.find? n == some eqA`: `IConstantInfo`'s `DecidableEq`), on lane `induct`'s conventions
(`IndIface.lean`).

* Constant records and constant values are `EREC` pointers (`decCI`/`decCV`, `EnvRec.lean`).
  A constant's level parameters are an `EREC` slice; the canonical comparisons take them as `IW`
  slices (`cv_lps`), as every list argument is. Recursor rules stay `EREC` slices of 11-word
  records (`decRules`): `canon_rules_eq` and `rules_eq` take the `EREC` slice `(off, cnt)`.
* **Equality of decoded records is word equality**, except where the decoder forgets: a `Bool`
  word (`bool?`: any nonzero word is `true`, `b_eq`), the height of a non-regular hint
  (`hint_eq`), the fire slices of a plain rule. Handles compare as words: the stores intern each
  value once (`denoteE`/`denoteN`/`denoteL` injective), so handle equality is value equality —
  also for a literal (`canon_expr_eq`'s `.lit` clause compares handles) and for `PropWhen`'s
  names (`dn` injective).
* `canon_names(n)`: the numbered names `⟨0⟩ … ⟨n-1⟩` as an `IW` slice. The renaming context of a
  comparison is three `IW` slices, flattened: the two parameter lists `ps`, `ps'` and the
  numerals `cs` (`po, pl, qo, ql, co, cl`), then the fuel (a word, `coreWalkFuel` = `4·10^9` at
  the entry points), then the two handles.
-/

namespace L.Ind

open L.Arena

/-! ## Equalities of records (the twin's derived `BEq`/`DecidableEq`) -/

/-- `er_sl_eq(o1, l1, o2, l2)`: two `EREC` slices hold the same words. -/
-- con-ron: none — the derived list equality, over two `EREC` slices
def erSlEq : FunDecl := lfn (o1, l1, o2, l2) locals (r) {
  if l1 != l2 { return 0 };
  if l1 == 0 { return 1 };
  if EREC.u64[o1] != EREC.u64[o2] { return 0 };
  r := call er_sl_eq(o1 + 1, l1 - 1, o2 + 1, l2 - 1);
  return r
}

/-- `b_eq(a, b)`: the two words decode to the same `Bool` (`bool?`). -/
-- con-ron: none — the derived `Bool` equality, at `bool?`'s decoding
def bEq : FunDecl := lfn (a, b) locals () {
  if a == 0 { return u64(b == 0) };
  return u64(b != 0)
}

/-- `cv_eq(q, q')`: the derived equality of two constant values (name, level parameters, type). -/
-- con-ron: none — the derived `IConstantVal` equality
def cvEq : FunDecl := lfn (q, r) locals (e, o1, l1, o2, l2) {
  if EREC.u64[q] != EREC.u64[r] { return 0 };
  o1 := EREC.u64[q + 1];
  l1 := EREC.u64[q + 2];
  o2 := EREC.u64[r + 1];
  l2 := EREC.u64[r + 2];
  e := call er_sl_eq(o1, l1, o2, l2);
  if e == 0 { return 0 };
  return u64(EREC.u64[q + 3] == EREC.u64[r + 3])
}

/-- `hint_eq(h, h')`: the hints at `EREC[h]`, `EREC[h + 1]` (kind, height) are equal; the height
counts only for a regular hint (kind `2`). -/
-- con-ron: none — the derived `ReducibilityHint` equality, at `decHint`'s decoding
def hintEq : FunDecl := lfn (h, g) locals () {
  if EREC.u64[h] != EREC.u64[g] { return 0 };
  if EREC.u64[h] == 2 { return u64(EREC.u64[h + 1] == EREC.u64[g + 1]) };
  return 1
}

/-- `pw_eq(q, q')`: two `PropWhen` records (`decPW`) are equal. -/
-- con-ron: none — the derived `PropWhen` equality, at `decPW`'s decoding
def pwEq : FunDecl := lfn (q, r) locals (e, o1, l1, o2, l2) {
  if EREC.u64[q] != EREC.u64[r] { return 0 };
  if EREC.u64[q] != 1 { return 1 };
  o1 := EREC.u64[q + 1];
  l1 := EREC.u64[q + 2];
  o2 := EREC.u64[r + 1];
  l2 := EREC.u64[r + 2];
  e := call er_sl_eq(o1, l1, o2, l2);
  return e
}

/-- `er_sl_at(p, q, i)`: the `EREC` slices at words `(p + i, p + i + 1)` and `(q + i, q + i + 1)` agree
(the words are loaded into locals before the call). -/
-- con-ron: none — plumbing of the derived record equalities
def erSlAt : FunDecl := lfn (p, q, i) locals (o1, l1, o2, l2, e) {
  o1 := EREC.u64[p + i];
  l1 := EREC.u64[p + i + 1];
  o2 := EREC.u64[q + i];
  l2 := EREC.u64[q + i + 1];
  e := call er_sl_eq(o1, l1, o2, l2);
  return e
}

/-- `caps_eq_a(q, q')`: `eta`, `etaCtor`, `etaParams`, `etaFields`, `unitlike` (words `0‥4`). -/
-- con-ron: none — the derived `IIndCaps` equality, at `decCaps`' decoding
def capsEqA : FunDecl := lfn (q, r) locals (e) {
  e := call b_eq(EREC.u64[q], EREC.u64[r]);
  if e == 0 { return 0 };
  if EREC.u64[q + 1] != EREC.u64[r + 1] { return 0 };
  if EREC.u64[q + 2] != EREC.u64[r + 2] { return 0 };
  if EREC.u64[q + 3] != EREC.u64[r + 3] { return 0 };
  e := call b_eq(EREC.u64[q + 4], EREC.u64[r + 4]);
  return e
}

/-- `caps_eq_b(q, q')`: `unitParams`, `ruleK`, `sortZ` (words `5‥9`). -/
-- con-ron: none — the derived `IIndCaps` equality, at `decCaps`' decoding
def capsEqB : FunDecl := lfn (q, r) locals (e) {
  if EREC.u64[q + 5] != EREC.u64[r + 5] { return 0 };
  e := call b_eq(EREC.u64[q + 6], EREC.u64[r + 6]);
  if e == 0 { return 0 };
  e := call pw_eq(q + 7, r + 7);
  return e
}

/-- `caps_eq_c(q, q')`: `all`, `nparams`, `ctors` (words `10‥14`). -/
-- con-ron: none — the derived `IIndCaps` equality, at `decCaps`' decoding
def capsEqC : FunDecl := lfn (q, r) locals (e) {
  e := call er_sl_at(q, r, 10);
  if e == 0 { return 0 };
  if EREC.u64[q + 12] != EREC.u64[r + 12] { return 0 };
  e := call er_sl_at(q, r, 13);
  return e
}

/-- `caps_eq(q, q')`: two `IIndCaps` records (`decCaps`, 15 words) are equal. -/
-- con-ron: none — the derived `IIndCaps` equality, at `decCaps`' decoding
def capsEq : FunDecl := lfn (q, r) locals (e) {
  e := call caps_eq_a(q, r);
  if e == 0 { return 0 };
  e := call caps_eq_b(q, r);
  if e == 0 { return 0 };
  e := call caps_eq_c(q, r);
  return e
}

/-- `rule_eq_a(q, q')`: `ctor`, `nfields`, `ctorParams`, the fire kind (words `0‥3`). -/
-- con-ron: ConRon/Arena/Canon.lean:176-190 ConRon.Arena.canonRulesEq
def ruleEqA : FunDecl := lfn (q, r) locals () {
  if EREC.u64[q] != EREC.u64[r] { return 0 };
  if EREC.u64[q + 1] != EREC.u64[r + 1] { return 0 };
  if EREC.u64[q + 2] != EREC.u64[r + 2] { return 0 };
  return u64(EREC.u64[q + 3] == EREC.u64[r + 3])
}

/-- `rule_eq_b(q, q')`: a nested fire's two slices (words `4‥7`); a plain fire has none. -/
-- con-ron: ConRon/Arena/Canon.lean:176-190 ConRon.Arena.canonRulesEq
def ruleEqB : FunDecl := lfn (q, r) locals (e) {
  if EREC.u64[q + 3] == 1 {
    e := call er_sl_at(q, r, 4);
    if e == 0 { return 0 };
    e := call er_sl_at(q, r, 6);
    return e
  };
  return 1
}

/-- `rule_eq_but_rhs(q, q')`: two recursor rules (`decRule`, 11 words) agree on every field but
`rhs` (the twin's `{ r with rhs := default } == { r' with rhs := default }`). -/
-- con-ron: ConRon/Arena/Canon.lean:176-190 ConRon.Arena.canonRulesEq
def ruleEqButRhs : FunDecl := lfn (q, r) locals (e) {
  e := call rule_eq_a(q, r);
  if e == 0 { return 0 };
  e := call rule_eq_b(q, r);
  if e == 0 { return 0 };
  e := call b_eq(EREC.u64[q + 9], EREC.u64[r + 9]);
  if e == 0 { return 0 };
  e := call b_eq(EREC.u64[q + 10], EREC.u64[r + 10]);
  return e
}

/-- `rules_eq(o, l, o', l')`: two `EREC` rule slices (11-word records) are equal. -/
-- con-ron: none — the derived `List IRecRule` equality
def rulesEq : FunDecl := lfn (o1, l1, o2, l2) locals (e) {
  if l1 != l2 { return 0 };
  if l1 == 0 { return 1 };
  e := call rule_eq_but_rhs(o1, o2);
  if e == 0 { return 0 };
  if EREC.u64[o1 + 8] != EREC.u64[o2 + 8] { return 0 };
  e := call rules_eq(o1 + 11, l1 - 1, o2 + 11, l2 - 1);
  return e
}

/-- `ci_eq_rest(p, p', k)`: the equality of two records of the same kind `k ≤ 5` whose constant
values agree. -/
-- con-ron: none — the derived `IConstantInfo` equality (`fe.find? n == some pin`)
def ciEqRest : FunDecl := lfn (p, q, k) locals (e, o1, l1, o2, l2) {
  if k == 1 {
    if EREC.u64[p + 5] != EREC.u64[q + 5] { return 0 };
    e := call hint_eq(p + 6, q + 6);
    return e
  };
  if k == 3 { e := call caps_eq(p + 5, q + 5); return e };
  if k == 4 {
    if EREC.u64[p + 5] != EREC.u64[q + 5] { return 0 };
    return u64(EREC.u64[p + 6] == EREC.u64[q + 6])
  };
  if k == 5 {
    if EREC.u64[p + 5] != EREC.u64[q + 5] { return 0 };
    if EREC.u64[p + 6] != EREC.u64[q + 6] { return 0 };
    o1 := EREC.u64[p + 7];
    l1 := EREC.u64[p + 8];
    o2 := EREC.u64[q + 7];
    l2 := EREC.u64[q + 8];
    e := call rules_eq(o1, l1, o2, l2);
    return e
  };
  return 1
}

/-- `ci_eq(p, p')`: the derived equality of two constant records (`decCI`), kind by kind. -/
-- con-ron: none — the derived `IConstantInfo` equality (`fe.find? n == some pin`)
def ciEq : FunDecl := lfn (p, q) locals (k, e) {
  k := EREC.u64[p];
  if k != EREC.u64[q] { return 0 };
  if 5 < k { abort };
  e := call cv_eq(p + 1, q + 1);
  if e == 0 { return 0 };
  e := call ci_eq_rest(p, q, k);
  return e
}

/-- `find_is(vis, n, pin)`: `fe.find? n == some pin` (`pin` a constant record). -/
-- con-ron: none — `fe.find? n == some ci`, the lookup and the derived equality
def findIs : FunDecl := lfn (vis, n, pin) locals (f, r, e) {
  (f, r) := call env_find(n, vis);
  if f == 0 { return 0 };
  e := call ci_eq(r, pin);
  return e
}

/-! ## `toConstantVal` -/

/-- `ci_to_cv(p)`: `IConstantInfo.toConstantVal` → the constant value pointer: the inline one at
`p + 1` (every constant record has it there). -/
-- con-ron: ConRon/Arena/Env.lean:176-180 ConRon.Arena.IConstantInfo.toConstantVal
@[l_impl ConRon.Arena.IConstantInfo.toConstantVal]
def ciToCv : FunDecl := lfn (p) locals () {
  return p + 1
}

/-! ## The renaming -/

/-- `canon_names_go(i, n)`: the numbered names `⟨i⟩ … ⟨i + n - 1⟩`, interned, as an `IW` slice. -/
-- con-ron: ConRon/Arena/Canon.lean:48-59 ConRon.Arena.canonNamesGo
@[l_impl ConRon.Arena.canonNamesGo]
def canonNamesGo : FunDecl := lfn (i, n) locals (a, h, o, l, q, m) {
  if n == 0 { return (0, 0) };
  a := call intern_nanon();
  if 4294967296 <= a { abort };
  h := call intern_nnum(a, i);
  if 4294967296 <= h { abort };
  (o, l) := call canon_names_go(i + 1, n - 1);
  (q, m) := call sl_cons(h, o, l);
  return (q, m)
}

/-- `canon_names(n)`. -/
-- con-ron: ConRon/Arena/Canon.lean:61-63 ConRon.Arena.canonNames
@[l_impl ConRon.Arena.canonNames]
def canonNames : FunDecl := lfn (n) locals (o, l) {
  (o, l) := call canon_names_go(0, n);
  return (o, l)
}

/-- `canon_name_map(po, pl, co, cl, n)`: the `i`-th parameter of `ps` becomes `cs[i]` (or stays,
past `cs`), anything else stays. -/
-- con-ron: ConRon/Arena/Canon.lean:65-73 ConRon.Arena.canonNameMap
@[l_impl ConRon.Arena.canonNameMap]
def canonNameMap : FunDecl := lfn (po, pl, co, cl, n) locals (f, i, r) {
  (f, i) := call sl_find(po, pl, n);
  if f == 0 { return n };
  r := call sl_getd(co, cl, i, n);
  return r
}

/-! ## Levels -/

/-- `canon_level_eq(po, pl, qo, ql, co, cl, fuel, u, v)`: `canonLevelEq`, in lockstep on the two
level handles (`lv_node`'s tags: `0` zero, `1` succ, `2` max, `3` imax, `4` param). -/
-- con-ron: ConRon/Arena/Canon.lean:77-99 ConRon.Arena.canonLevelEq
@[l_impl ConRon.Arena.canonLevelEq]
def canonLevelEq : FunDecl :=
    lfn (po, pl, qo, ql, co, cl, fuel, u, v) locals (ta, a1, a2, tb, b1, b2, r, x, y) {
  if fuel == 0 { abort };
  (ta, a1, a2) := call lv_node(u);
  (tb, b1, b2) := call lv_node(v);
  if ta != tb { return 0 };
  if ta == 0 { return 1 };
  if ta == 1 {
    r := call canon_level_eq(po, pl, qo, ql, co, cl, fuel - 1, a1, b1);
    return r
  };
  if ta == 2 || ta == 3 {
    r := call canon_level_eq(po, pl, qo, ql, co, cl, fuel - 1, a1, b1);
    if r == 0 { return 0 };
    r := call canon_level_eq(po, pl, qo, ql, co, cl, fuel - 1, a2, b2);
    return r
  };
  if ta == 4 {
    x := call canon_name_map(po, pl, co, cl, a1);
    y := call canon_name_map(qo, ql, co, cl, b1);
    return u64(x == y)
  };
  return 0
}

/-- `canon_level_list_eq(po, pl, qo, ql, co, cl, fuel, ao, al, bo, bl)`: two `IW` slices of level
handles, pairwise. -/
-- con-ron: ConRon/Arena/Canon.lean:101-111 ConRon.Arena.canonLevelListEq
@[l_impl ConRon.Arena.canonLevelListEq]
def canonLevelListEq : FunDecl :=
    lfn (po, pl, qo, ql, co, cl, fuel, ao, al, bo, bl) locals (r, u, v) {
  if al == 0 && bl == 0 { return 1 };
  if al == 0 || bl == 0 { return 0 };
  u := IW.u64[ao];
  v := IW.u64[bo];
  r := call canon_level_eq(po, pl, qo, ql, co, cl, fuel, u, v);
  if r == 0 { return 0 };
  r := call canon_level_list_eq(po, pl, qo, ql, co, cl, fuel, ao + 1, al - 1, bo + 1, bl - 1);
  return r
}

/-- `canon_levels_eq(po, pl, qo, ql, co, cl, fuel, us, vs)`: at two level-list handles. -/
-- con-ron: ConRon/Arena/Canon.lean:113-117 ConRon.Arena.canonLevelsEq
@[l_impl ConRon.Arena.canonLevelsEq]
def canonLevelsEq : FunDecl :=
    lfn (po, pl, qo, ql, co, cl, fuel, us, vs) locals (ao, al, bo, bl, r) {
  (ao, al) := call view_ls(us);
  (bo, bl) := call view_ls(vs);
  r := call canon_level_list_eq(po, pl, qo, ql, co, cl, fuel, ao, al, bo, bl);
  return r
}

/-! ## Terms -/

/-- `canon_expr_eq(po, pl, qo, ql, co, cl, fuel, a, b)`: `canonExprEq`, both views first. -/
-- con-ron: ConRon/Arena/Canon.lean:121-159 ConRon.Arena.canonExprEq
@[l_impl ConRon.Arena.canonExprEq]
def canonExprEq : FunDecl :=
    lfn (po, pl, qo, ql, co, cl, fuel, a, b) locals (t, x, y, z, s, x2, y2, z2, r) {
  if fuel == 0 { abort };
  (t, x, y, z) := call e_view(a);
  (s, x2, y2, z2) := call e_view(b);
  if t != s { return 0 };
  if t == 0 { return u64(x == x2) };
  if t == 1 {
    if x != x2 { return 0 };
    r := call canon_expr_eq(po, pl, qo, ql, co, cl, fuel - 1, y, y2);
    return r
  };
  if t == 2 {
    r := call canon_level_eq(po, pl, qo, ql, co, cl, fuel - 1, x, x2);
    return r
  };
  if t == 3 {
    if x != x2 { return 0 };
    r := call canon_levels_eq(po, pl, qo, ql, co, cl, fuel - 1, y, y2);
    return r
  };
  if t == 4 || t == 5 || t == 6 {
    r := call canon_expr_eq(po, pl, qo, ql, co, cl, fuel - 1, x, x2);
    if r == 0 { return 0 };
    r := call canon_expr_eq(po, pl, qo, ql, co, cl, fuel - 1, y, y2);
    return r
  };
  if t == 7 {
    r := call canon_expr_eq(po, pl, qo, ql, co, cl, fuel - 1, x, x2);
    if r == 0 { return 0 };
    r := call canon_expr_eq(po, pl, qo, ql, co, cl, fuel - 1, y, y2);
    if r == 0 { return 0 };
    r := call canon_expr_eq(po, pl, qo, ql, co, cl, fuel - 1, z, z2);
    return r
  };
  if t == 8 { return u64(a == b) };
  if x != x2 || y != y2 { return 0 };
  r := call canon_expr_eq(po, pl, qo, ql, co, cl, fuel - 1, z, z2);
  return r
}

/-! ## Constants -/

/-- `canon_ctx(cp, cq)`: the renaming context of two constant values: the interned numerals for
`cp`'s parameter count, then both parameter lists, as `(po, pl, qo, ql, co, cl)`. -/
-- con-ron: ConRon/Arena/Canon.lean:48-59 ConRon.Arena.canonNamesGo
def canonCtx : FunDecl := lfn (cp, cq) locals (n, co, cl, po, pl, qo, ql) {
  n := EREC.u64[cp + 2];
  (co, cl) := call canon_names(n);
  (po, pl) := call cv_lps(cp);
  (qo, ql) := call cv_lps(cq);
  return (po, pl, qo, ql, co, cl)
}

/-- `cv_canon_eq(q, q')`: `IConstantVal.canonEq`: the names and the parameter counts first, then
the types under the renaming. -/
-- con-ron: ConRon/Arena/Canon.lean:163-174 ConRon.Arena.IConstantVal.canonEq
@[l_impl ConRon.Arena.IConstantVal.canonEq]
def cvCanonEq : FunDecl := lfn (q, r) locals (co, cl, po, pl, qo, ql, e, a, b) {
  if EREC.u64[q] != EREC.u64[r] || EREC.u64[q + 2] != EREC.u64[r + 2] { return 0 };
  (po, pl, qo, ql, co, cl) := call canon_ctx(q, r);
  a := EREC.u64[q + 3];
  b := EREC.u64[r + 3];
  e := call canon_expr_eq(po, pl, qo, ql, co, cl, 4000000000, a, b);
  return e
}

/-- `canon_rules_eq(po, pl, qo, ql, co, cl, fuel, o, l, o', l')`: two `EREC` rule slices, every
field but the right-hand side compared as it stands, the right-hand sides canonically. -/
-- con-ron: ConRon/Arena/Canon.lean:176-190 ConRon.Arena.canonRulesEq
@[l_impl ConRon.Arena.canonRulesEq]
def canonRulesEq : FunDecl :=
    lfn (po, pl, qo, ql, co, cl, fuel, o1, l1, o2, l2) locals (e, a, b) {
  if l1 == 0 && l2 == 0 { return 1 };
  if l1 == 0 || l2 == 0 { return 0 };
  e := call rule_eq_but_rhs(o1, o2);
  if e == 0 { return 0 };
  a := EREC.u64[o1 + 8];
  b := EREC.u64[o2 + 8];
  e := call canon_expr_eq(po, pl, qo, ql, co, cl, fuel, a, b);
  if e == 0 { return 0 };
  e := call canon_rules_eq(po, pl, qo, ql, co, cl, fuel, o1 + 11, l1 - 1, o2 + 11, l2 - 1);
  return e
}

/-- `ci_canon_defn(p, p')`: two definitions, hints first, then the common data, then the values. -/
-- con-ron: ConRon/Arena/Canon.lean:192-217 ConRon.Arena.IConstantInfo.canonEq
def ciCanonDefn : FunDecl := lfn (p, q) locals (e, co, cl, po, pl, qo, ql, a, b) {
  e := call hint_eq(p + 6, q + 6);
  if e == 0 { return 0 };
  e := call cv_canon_eq(p + 1, q + 1);
  if e == 0 { return 0 };
  (po, pl, qo, ql, co, cl) := call canon_ctx(p + 1, q + 1);
  a := EREC.u64[p + 5];
  b := EREC.u64[q + 5];
  e := call canon_expr_eq(po, pl, qo, ql, co, cl, 4000000000, a, b);
  return e
}

/-- `ci_canon_rec(p, p')`: two recursors, the two counts first, then the common data, then the
rules. -/
-- con-ron: ConRon/Arena/Canon.lean:192-217 ConRon.Arena.IConstantInfo.canonEq
def ciCanonRec : FunDecl := lfn (p, q) locals (e, co, cl, po, pl, qo, ql, o1, l1, o2, l2) {
  if EREC.u64[p + 5] != EREC.u64[q + 5] || EREC.u64[p + 6] != EREC.u64[q + 6] { return 0 };
  e := call cv_canon_eq(p + 1, q + 1);
  if e == 0 { return 0 };
  (po, pl, qo, ql, co, cl) := call canon_ctx(p + 1, q + 1);
  o1 := EREC.u64[p + 7];
  l1 := EREC.u64[p + 8];
  o2 := EREC.u64[q + 7];
  l2 := EREC.u64[q + 8];
  e := call canon_rules_eq(po, pl, qo, ql, co, cl, 4000000000, o1, l1, o2, l2);
  return e
}

/-- `ci_canon_eq(p, p')`: `IConstantInfo.canonEq`, kind by kind (a definition's hints first, a
recursor's two counts first; an inductive's capabilities are not compared). -/
-- con-ron: ConRon/Arena/Canon.lean:192-217 ConRon.Arena.IConstantInfo.canonEq
@[l_impl ConRon.Arena.IConstantInfo.canonEq]
def ciCanonEq : FunDecl := lfn (p, q) locals (k, e) {
  k := EREC.u64[p];
  if k != EREC.u64[q] { return 0 };
  if 5 < k { abort };
  if k == 1 { e := call ci_canon_defn(p, q); return e };
  if k == 4 {
    if EREC.u64[p + 5] != EREC.u64[q + 5] || EREC.u64[p + 6] != EREC.u64[q + 6] { return 0 }
  };
  if k == 5 { e := call ci_canon_rec(p, q); return e };
  e := call cv_canon_eq(p + 1, q + 1);
  return e
}

/-- `canon_eq_list(o, l, o', l')`: two `IW` slices of constant records, member for member. -/
-- con-ron: ConRon/Arena/Canon.lean:219-226 ConRon.Arena.canonEqList
@[l_impl ConRon.Arena.canonEqList]
def canonEqListL : FunDecl := lfn (o1, l1, o2, l2) locals (e, a, b) {
  if l1 == 0 && l2 == 0 { return 1 };
  if l1 == 0 || l2 == 0 { return 0 };
  a := IW.u64[o1];
  b := IW.u64[o2];
  e := call ci_canon_eq(a, b);
  if e == 0 { return 0 };
  e := call canon_eq_list(o1 + 1, l1 - 1, o2 + 1, l2 - 1);
  return e
}

/-! ## The module's program -/

/-- This module's functions. -/
def declArmsCanonFns : Prog :=
  [("er_sl_eq", erSlEq), ("b_eq", bEq), ("cv_eq", cvEq), ("hint_eq", hintEq), ("pw_eq", pwEq),
   ("caps_eq", capsEq), ("rule_eq_but_rhs", ruleEqButRhs), ("rules_eq", rulesEq),
   ("ci_eq", ciEq), ("er_sl_at", erSlAt), ("caps_eq_a", capsEqA),
   ("caps_eq_b", capsEqB), ("caps_eq_c", capsEqC), ("rule_eq_a", ruleEqA), ("rule_eq_b", ruleEqB),
   ("ci_eq_rest", ciEqRest), ("canon_ctx", canonCtx),
   ("ci_canon_defn", ciCanonDefn), ("ci_canon_rec", ciCanonRec), ("find_is", findIs), ("ci_to_cv", ciToCv),
   ("canon_names_go", canonNamesGo), ("canon_names", canonNames),
   ("canon_name_map", canonNameMap), ("canon_level_eq", canonLevelEq),
   ("canon_level_list_eq", canonLevelListEq), ("canon_levels_eq", canonLevelsEq),
   ("canon_expr_eq", canonExprEq), ("cv_canon_eq", cvCanonEq), ("canon_rules_eq", canonRulesEq),
   ("ci_canon_eq", ciCanonEq), ("canon_eq_list", canonEqListL)]

/-- Functions of master the arms call that lane `induct`'s program does not carry (as stubs here;
the whole program uses the real ones): `intern_succ(u)` (`LevelStore.lean`), `intern_nnum(pre,
i)` (`NNumStore.lean`), `const_e(n)` (`WhnfDelta.lean`, `constE`), `nat_lit_supported(vis)`
(`WhnfDelta.lean`, `natLitSupported`). -/
def armsMasterFns : Prog :=
  [("intern_succ", stub 1), ("intern_nnum", stub 2), ("const_e", stub 1),
   ("nat_lit_supported", stub 1)]

/-! ## Runs on stub-free paths -/

/-- Two constant records in a test memory: `EREC[0‥]` an `axiomInfo` (name `7`, parameters the
slice `[3, 4]` at `20`, type `9`), `EREC[8‥]` the same, `EREC[16‥]` one with type `10`. -/
def armsTestMem : Mem :=
  let e := (Array.replicate 64 (0 : Word))
    |>.set! 0 0 |>.set! 1 7 |>.set! 2 20 |>.set! 3 2 |>.set! 4 9
    |>.set! 8 0 |>.set! 9 7 |>.set! 10 22 |>.set! 11 2 |>.set! 12 9
    |>.set! 16 0 |>.set! 17 7 |>.set! 18 20 |>.set! 19 2 |>.set! 20 3 |>.set! 21 4
    |>.set! 22 3 |>.set! 23 4
  { testMem with words := testMem.words.set! EREC e }

-- `ci_eq` of two equal axiom records (their parameter slices at different places), and of two
-- that differ in the type (`EREC[16‥]`'s type word is `EREC[20] = 3`).
#guard
  (match run (declArmsCanonFns ++ libFns ++ stubFns ++ masterFns ++ armsMasterFns) 1000 "ci_eq"
      [0, 8] armsTestMem with
   | .ok ([1], _) => true | _ => false) &&
  (match run (declArmsCanonFns ++ libFns ++ stubFns ++ masterFns ++ armsMasterFns) 1000 "ci_eq"
      [0, 16] armsTestMem with
   | .ok ([0], _) => true | _ => false)

end L.Ind
