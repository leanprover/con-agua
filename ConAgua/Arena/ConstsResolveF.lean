import ConAgua.Arena.IndIface
import ConAgua.Census.Attr

/-!
# `consts_resolve_ffast(vis, e)`: the twin's memoized `constsResolve` (lane `stubs`)

The twin (`ConRon/Arena/CheckerBase.lean`, `constsResolveFFast fe e`): do all constants of `e`
(through `fvar` annotations and `proj` structure names) resolve in `fe`? One DAG walk with a
walk-local memo keyed on the node (fresh per call), at `coreWalkFuel`. The four leaf views
(`bvar`, `sort`, `lit`, `const`) are answered by the pure walk `constsResolve` at that node, without
the memo; every other node is probed first. In L:

* the memo is the memo library's table `CRM` (word array 155, `CTL[158]` stamp − 1, `CTL[159]`
  live count), key `(h, 0)`, value `0`/`1`, cleared at the entry;
* `cr_leaf(vis, g, h)` is `constsResolve` at a leaf (`g` the view's tag): `bvar`/`sort` resolve; a
  `Nat` literal needs the pins `Nat`, `Nat.zero`, `Nat.succ` in the environment, a `String` literal
  also `String`, `String.ofList`, `List`, `List.nil`, `List.cons`, `Char`, `Char.ofNat` (all read
  off the pin table first, as the twin does); a `const` its name;
* the arms evaluate every child (the twin's `&&` comes after both recursive calls), the `proj` arm
  looks its structure name up after the child;
* the fuel is the twin's: one unit per level of recursion, `0` aborts (the twin's `.internal`).

`crf_go` re-probes before its put: the recursive calls may have filled the slot the first probe
returned (as `alpd_go`).
-/

namespace L.Stubs

open L.Arena L.Ind

/-- The walk's memo table. -/
abbrev CRM : ArrId := 155

/-- Its schema: array 155, `CTL[158]`, `CTL[159]`. -/
abbrev crSch : MemoSch := ⟨CRM, 158⟩

/-- `pin_found(vis, k)`: pin `k`'s name has a row below `vis`. -/
-- con-ron: ConRon/Arena/Core.lean:514-560 ConRon.Arena.constsResolve
def pinFound : FunDecl := lfn (vis, k) locals (n, f, q) {
  n := call pin_at(k);
  (f, q) := call env_find(n, vis);
  return f
}

/-- `cr_lit_pins(vis, s)`: the literal's pins resolve (`s ≠ 0`: a `String` literal's ten,
else a `Nat` literal's three). -/
-- con-ron: ConRon/Arena/Core.lean:514-560 ConRon.Arena.constsResolve
def crLitPins : FunDecl := lfn (vis, s) locals (a, b, c, d, f, g, h, i, j, k) {
  a := call pin_found(vis, 1); b := call pin_found(vis, 2); c := call pin_found(vis, 3);
  if s == 0 {
    if a != 0 && b != 0 && c != 0 { return 1 };
    return 0
  };
  d := call pin_found(vis, 5); f := call pin_found(vis, 6); g := call pin_found(vis, 7);
  h := call pin_found(vis, 8); i := call pin_found(vis, 9); j := call pin_found(vis, 10);
  k := call pin_found(vis, 12);
  if a != 0 && b != 0 && c != 0 && d != 0 && f != 0 && g != 0 && h != 0 && i != 0 &&
    j != 0 && k != 0 { return 1 };
  return 0
}

/-- `cr_leaf(vis, g, x, h)`: `constsResolve` at a leaf of tag `g` (`x` the view's first field). -/
-- con-ron: ConRon/Arena/Core.lean:514-560 ConRon.Arena.constsResolve
def crLeaf : FunDecl := lfn (vis, g, x, h) locals (s, f, q, r) {
  if g == 8 {
    s := call is_str_lit(h);
    r := call cr_lit_pins(vis, s);
    return r
  };
  if g == 3 { (f, q) := call env_find(x, vis); return f };
  return 1
}

/-- `crf_go(vis, f, h)`: the memoized walk at fuel `f`. -/
-- con-ron: ConRon/Arena/CheckerBase.lean:111-149 ConRon.Arena.constsResolveFGo
@[l_impl ConRon.Arena.constsResolveFGo]
def crfGo : FunDecl := lfn (vis, f, h) locals (fd, j, d, g, x, y, w, r, a, b, q) {
  if f == 0 { abort };
  (g, x, y, w) := call e_view(h);
  if g == 0 || g == 2 || g == 3 || g == 8 { r := call cr_leaf(vis, g, x, h); return r };
  (fd, j, d) := call crm_find(h, 0);
  if fd != 0 { return CRM.u64[j * 4 + 3] };
  if g == 1 { r := call crf_go(vis, f - 1, y) }
  else if g == 4 || g == 5 || g == 6 {
    a := call crf_go(vis, f - 1, x);
    b := call crf_go(vis, f - 1, y);
    if a != 0 && b != 0 { r := 1 } else { r := 0 }
  }
  else if g == 7 {
    a := call crf_go(vis, f - 1, x);
    b := call crf_go(vis, f - 1, y);
    r := call crf_go(vis, f - 1, w);
    if a != 0 && b != 0 && r != 0 { r := 1 } else { r := 0 }
  }
  else {
    r := call crf_go(vis, f - 1, w);
    (a, q) := call env_find(x, vis);
    if a != 0 && r != 0 { r := 1 } else { r := 0 }
  };
  (fd, j, d) := call crm_find(h, 0);
  d := call crm_put(h, 0, r, fd, j);
  return r
}

/-- `consts_resolve_ffast(vis, e)`: `constsResolveFFast fe e`, `1`/`0`. -/
-- con-ron: ConRon/Arena/CheckerBase.lean:151-155 ConRon.Arena.constsResolveFFast
@[l_impl ConRon.Arena.constsResolveFFast]
def constsResolveFFastL : FunDecl := lfn (vis, e) locals (z, r) {
  z := call crm_clear();
  r := call crf_go(vis, 4000000000, e);
  return r
}

/-- This module's functions, with the memo's three library functions. -/
def crfProg : Prog :=
  [("consts_resolve_ffast", constsResolveFFastL), ("crf_go", crfGo), ("cr_leaf", crLeaf),
   ("cr_lit_pins", crLitPins), ("pin_found", pinFound),
   ("crm_find", memoFindG crSch), ("crm_put", memoPutG crSch), ("crm_clear", memoClearG crSch)]

/-! ## `CheckerBase.lean`: the verdict at a term whose constants do not all resolve

These walks run only on the error path, right after `consts_resolve_ffast` failed; the run aborts
after them. They write nothing (no memo: the twin's `hasStrLitGo` visited set and
`mentionsConst`'s memo are dropped, `docs/deviations.md` D16), so the error path stays inside every
write set its callers' frames are checked against (the parallel mode's owned arrays, the loops'
and the inductive arm's memo frames). -/

/-- `has_str_lit_go(f, h)`: does `h` contain a string literal? The twin's fuel `f` (abort at `0`,
the twin's `.internal`; the children at `f - 1`), the node viewed first and the leaves decided off
the view (a literal of kind `≠ 0` is a string), short-circuiting. The twin's visited set is
dropped: a node it has visited and finished answered `false` (a `true` ends the walk), which is
what a second walk of it answers too. -/
-- con-ron: ConRon/Arena/CheckerBase.lean:188-221 ConRon.Arena.hasStrLitGo
@[l_impl ConRon.Arena.hasStrLitGo]
def hasStrLitGoL : FunDecl := lfn (f, h) locals (g, x, y, z, t, i, r) {
  if f == 0 { abort };
  (g, x, y, z) := call e_view(h);
  if g == 8 {
    t := ⟦h⟧.tier;
    i := ⟦h⟧.idx;
    return u64(LIT⟨t, i⟩.kind != 0)
  };
  if g == 0 || g == 2 || g == 3 { return 0 };
  if g == 1 { r := call has_str_lit_go(f - 1, y); return r };
  if g == 4 || g == 5 || g == 6 {
    r := call has_str_lit_go(f - 1, x);
    if r != 0 { return 1 };
    r := call has_str_lit_go(f - 1, y);
    return r
  };
  if g == 7 {
    r := call has_str_lit_go(f - 1, x);
    if r != 0 { return 1 };
    r := call has_str_lit_go(f - 1, y);
    if r != 0 { return 1 };
    r := call has_str_lit_go(f - 1, z);
    return r
  };
  r := call has_str_lit_go(f - 1, z);
  return r
}

/-- `ue_mentions_go(f, T, h)`: `mentions_const_go` (the twin's `mentionsConstGo`, the same walk)
without its memo. -/
-- con-ron: ConRon/Arena/Inductives/StructParts.lean:263-304 ConRon.Arena.mentionsConstGo
@[l_impl ConRon.Arena.mentionsConstGo]
def ueMentionsGoL : FunDecl := lfn (f, T, h) locals (g, x, y, z, r, b1, b2, b3) {
  if f == 0 { abort };
  (g, x, y, z) := call e_view(h);
  if g == 0 || g == 2 || g == 8 { return 0 };
  if g == 3 { return u64(x == T) };
  if g == 1 { r := call ue_mentions_go(f - 1, T, y) }
  else if g == 4 || g == 5 || g == 6 {
    b1 := call ue_mentions_go(f - 1, T, x);
    b2 := call ue_mentions_go(f - 1, T, y);
    r := b1 | b2
  } else if g == 7 {
    b1 := call ue_mentions_go(f - 1, T, x);
    b2 := call ue_mentions_go(f - 1, T, y);
    b3 := call ue_mentions_go(f - 1, T, z);
    r := b1 | b2 | b3
  } else {
    b1 := call ue_mentions_go(f - 1, T, z);
    r := u64(x == T) | b1
  };
  return r
}

/-- `unresolved_consts_error(vis, e, w)`: the twin's `fail (← unresolvedConstsErrorL (←
strLitSupported fe) where_ e)` (`w ≤ 1`) and `fail (← unresolvedConstsError where_ e)` (`w ≥ 2`):
always aborts. `w` names the twin's `where_` (`0` "type", `1` "value", `2` "type of", `3`
"generated rule of", `4` "the domains of a generated rule of"; the reason of each message). For
`w ≤ 1`: without the String support declarations, a string literal in `e` (`has_str_lit_go`)
declines. Then a term mentioning `sorryAx` (pin 13, `ue_mentions_go`: the twin's `mentionsConst`)
declines, anything else rejects. -/
-- con-ron: ConRon/Arena/CheckerBase.lean:176-186 ConRon.Arena.unresolvedConstsError
-- con-ron: ConRon/Arena/CheckerBase.lean:223-235 ConRon.Arena.unresolvedConstsErrorL
@[l_impl ConRon.Arena.unresolvedConstsError ConRon.Arena.unresolvedConstsErrorL]
def unresolvedConstsErrL : FunDecl := lfn (vis, e, w) locals (s, r, sa, m) {
  if w <= 1 {
    s := call str_lit_supported(vis);
    if s == 0 {
      r := call has_str_lit_go(⟪CWF⟫, e);
      if r != 0 { fail R_STRING_LITERALS_BEFORE }
    }
  };
  sa := call pin_at(13);
  m := call ue_mentions_go(⟪CWF⟫, sa, e);
  if m != 0 {
    if w == 0 { fail R_USE_OF_THE_SORRYAX_IN_TYPE };
    if w == 1 { fail R_USE_OF_THE_SORRYAX_IN_VALUE };
    if w == 2 { fail R_USE_OF_THE_SORRYAX_IN_TYPE_OF };
    if w == 3 { fail R_USE_OF_THE_SORRYAX_IN_GENERATED };
    fail R_USE_OF_THE_SORRYAX_IN_THE
  };
  if w == 0 { fail R_UNKNOWN_CONSTANT_IN_TYPE };
  if w == 1 { fail R_UNKNOWN_CONSTANT_IN_VALUE };
  if w == 2 { fail R_UNKNOWN_CONSTANT_IN_TYPE_OF };
  if w == 3 { fail R_UNKNOWN_CONSTANT_IN_GENERATED };
  fail R_UNKNOWN_CONSTANT_IN_THE
}

/-- The error path's functions (outside `crfProg`, whose callers' proofs never reach them). -/
def unresolvedFns : Prog :=
  [("has_str_lit_go", hasStrLitGoL), ("ue_mentions_go", ueMentionsGoL),
   ("unresolved_consts_error", unresolvedConstsErrL)]

end L.Stubs
