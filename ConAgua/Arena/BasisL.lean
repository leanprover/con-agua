module

public import ConAgua.Arena.DeclArmsCanon
meta import ConAgua.Arena.DeclArmsCanon

@[expose] public section

/-!
# The pinned basis blocks in L: a pin at a stream's names, the block's comparison, the quotient

The twin's `Basis.lean` (`vendor/con-ron/ConRon/Arena/Basis.lean`) but for `andPinOk`
(`DeclAndPin.lean`) and `BasisKind.decls`/`natA` (the ROM's `rom_basis_decls`, `rom_ci`): a pin at
a stream's level-parameter names (`IConstantInfo.atLps`), the block's comparison with its pin
(`pinListOk`), the name test that says a record is a pinned block's (`basisNameHit`), what such a
block and a quotient record store (`BasisKind.atBlock`, `quotAt`), the quotient record's tests
(`quotPinHit`, `quotPredsOk`). On lane `induct`'s conventions (`IndIface.lean`):

* A constant record is an `EREC` pointer (`decCI`, `EnvRec.lean`); a list of them an `IW` slice
  of pointers (the ROM's blocks, `rom_basis_decls(kind)`). The block of a stream record arrives
  as an `EREC` slice of pointers (`ind_block_to_erec`): the three entry points that take it
  (`basis_name_hit`, `basis_at_block`, `check_basis_block`, `DeclArms.lean`) copy it into `IW`
  (`er_to_iw`) first.
* A list of level-parameter names `ps` is an `EREC` slice (a record's own, `(p + 2, p + 3)`);
  `atLps` shares it with the record it builds. The read-back names and levels of the twin
  (`readNamesM`, `Level.subst`) are the name handles themselves (`denoteN` injective):
  `pinLinkOk`'s `Level.subst rp (r.map .param) (.param p)` is `canon_name_map`'s lookup.
* A pin at new names is a fresh record (`ci_at_lps`): the cv inline (`cv_at_lps` writes 4 words),
  a definition's value, a recursor's rules (`rules_at_lps`, a fresh 11-word rule slice) renamed,
  every other word copied.
-/

namespace L.Ind

open L.Arena

/-! ## A pin at a stream's level-parameter names -/

/-- `cv_at_lps(d, q, po, pl)`: `IConstantVal.atLps cv ps` (`q` the constant value, `ps` the
`EREC` name slice `(po, pl)`), written as the 4 words at `d`: the name, `ps`, the type with `cv`'s
names replaced positionally by `ps.map .param`. Returns `0`. -/
-- con-ron: ConRon/Arena/Basis.lean:51-57 ConRon.Arena.IConstantVal.atLps
@[no_expose, l_impl ConRon.Arena.IConstantVal.atLps]
def cvAtLps : FunDecl := lfn (d, q, po, pl) locals (io, il, us, ty, ez) {
  (io, il) := call er_to_iw(po, pl);
  us := call param_levels(io, il);
  ty := call inst_lp(EREC⦃q + 1⦄, EREC⦃q + 2⦄, us, EREC⦃q + 3⦄);
  ez := call erec_put(d, EREC⦃q⦄);
  ez := call erec_put(d + 1, po);
  ez := call erec_put(d + 2, pl);
  ez := call erec_put(d + 3, ty);
  return 0
}

/-- `spn_to_er(d, s, l)`: `EREC[d + j] := SPN[s + j]` for `j < l`. -/
-- con-ron: none — L scratch plumbing (the twin builds a `List`)
@[no_expose] def spnToEr : FunDecl := lfn (d, s, l) locals (ez, u) {
  if l == 0 { return 0 };
  ez := call erec_put(d, SPN.u64[s]);
  u := call spn_to_er(d + 1, s + 1, l - 1);
  return 0
}

/-- `fire_levels_at(fo, fl, ko, kc, us)`: `substLevelsAt` of the `EREC` level slice `(fo, fl)`
with the keys the `EREC` name slice `(ko, kc)` and the values the level list `us`, as a fresh
`EREC` level slice (its offset; its length is `fl`). -/
-- con-ron: ConRon/Arena/Basis.lean:59-65 ConRon.Arena.IRecRuleFire.atLps
@[no_expose, l_impl ConRon.Arena.IRecRuleFire.atLps]
def fireLevelsAt : FunDecl := lfn (fo, fl, ko, kc, us) locals (vo, vc, b, c, x, d) {
  (vo, vc) := call ls_node(us);
  b := call keys_push(ko, kc);
  c := CTL.u64[136];
  if len(SPN.u64) < c { abort };
  if len(SPN.u64) - c < fl { abort };
  x := call sle_go(fo, fl, c, b, kc, vo, vc);
  d := call erec_alloc(fl);
  x := call spn_to_er(d, c, fl);
  CTL.u64[136] := b;
  return d
}

/-- `rules_at_lps_go(ko, kc, us, o, l, d)`: the rules of the `EREC` slice `(o, l)` (11-word
records) at the new names, written to the 11-word records at `d`: each right-hand side
(`instLPFast`), then its firing mode (a `levels` fire's levels substituted, every other mode as it
is), then the rest. Returns `0`. -/
-- con-ron: ConRon/Arena/Basis.lean:67-78 ConRon.Arena.rulesAtLps
@[no_expose, l_impl ConRon.Arena.rulesAtLps]
def rulesAtLpsGo : FunDecl := lfn (ko, kc, us, o, l, d) locals (rhs, k, lo, ez, u) {
  if l == 0 { return 0 };
  rhs := call inst_lp(ko, kc, us, EREC⦃o + 8⦄);
  k := EREC⦃o + 3⦄;
  lo := EREC⦃o + 4⦄;
  if k == 2 { lo := call fire_levels_at(EREC⦃o + 4⦄, EREC⦃o + 5⦄, ko, kc, us) };
  ez := call erec_put(d, EREC⦃o⦄);
  ez := call erec_put(d + 1, EREC⦃o + 1⦄);
  ez := call erec_put(d + 2, 0);
  ez := call erec_put(d + 3, k);
  ez := call erec_put(d + 4, lo);
  ez := call erec_put(d + 5, EREC⦃o + 5⦄);
  ez := call erec_put(d + 6, EREC⦃o + 6⦄);
  ez := call erec_put(d + 7, EREC⦃o + 7⦄);
  ez := call erec_put(d + 8, rhs);
  ez := call erec_put(d + 9, 0);
  ez := call erec_put(d + 10, 0);
  u := call rules_at_lps_go(ko, kc, us, o + 11, l - 1, d + 11);
  return 0
}

/-- `er_copy_er(d, s, l)`: `EREC[d + j] := EREC[s + j]` for `j < l`. -/
-- con-ron: none — L record plumbing (the twin's structure update keeps the other fields)
@[no_expose] def erCopyEr : FunDecl := lfn (d, s, l) locals (ez, u) {
  if l == 0 { return 0 };
  ez := call erec_put(d, EREC⦃s⦄);
  u := call er_copy_er(d + 1, s + 1, l - 1);
  return 0
}

/-- `ci_at_lps(p, po, pl)`: `IConstantInfo.atLps ci ps`: a fresh record of `p`'s kind, its cv at
the names `ps` (the `EREC` slice `(po, pl)`), a definition's value and a recursor's rules renamed,
every other word copied. -/
-- con-ron: ConRon/Arena/Basis.lean:80-100 ConRon.Arena.IConstantInfo.atLps
@[no_expose, l_impl ConRon.Arena.IConstantInfo.atLps]
def ciAtLps : FunDecl := lfn (p, po, pl) locals (k, n, r, z, us, io, il, v, ez, ro, rl) {
  k := EREC⦃p⦄;
  if 5 < k { abort };
  n := 5;
  if k == 1 { n := 8 } else if k == 3 { n := 20 } else if k == 4 { n := 7 } else if k == 5 {
    n := 10 };
  r := call erec_alloc(n);
  ez := call erec_put(r, k);
  z := call cv_at_lps(r + 1, p + 1, po, pl);
  if k == 1 {
    (io, il) := call er_to_iw(po, pl);
    us := call param_levels(io, il);
    v := call inst_lp(EREC⦃p + 2⦄, EREC⦃p + 3⦄, us, EREC⦃p + 5⦄);
    ez := call erec_put(r + 5, v);
    z := call er_copy_er(r + 6, p + 6, 2);
    return r
  };
  if k == 3 { z := call er_copy_er(r + 5, p + 5, 15); return r };
  if k == 4 { z := call er_copy_er(r + 5, p + 5, 2); return r };
  if k == 5 {
    (io, il) := call er_to_iw(po, pl);
    us := call param_levels(io, il);
    rl := EREC⦃p + 8⦄;
    if 1152921504606846976 <= rl { abort };
    ro := call erec_alloc(11 * rl);
    z := call rules_at_lps_go(EREC⦃p + 2⦄, EREC⦃p + 3⦄, us, EREC⦃p + 7⦄, rl, ro);
    ez := call erec_put(r + 5, EREC⦃p + 5⦄);
    ez := call erec_put(r + 6, EREC⦃p + 6⦄);
    ez := call erec_put(r + 7, ro);
    ez := call erec_put(r + 8, rl);
    ez := call erec_put(r + 9, EREC⦃p + 9⦄);
    return r
  };
  return r
}

/-! ## The block's comparison with its pin -/

/-- `pin_agrees(c, c')`: `pinAgrees`: two inductive records by their constant values (no
capabilities compared), every other pair by the derived equality. -/
-- con-ron: ConRon/Arena/Basis.lean:102-107 ConRon.Arena.pinAgrees
@[no_expose, l_impl ConRon.Arena.pinAgrees]
def pinAgrees : FunDecl := lfn (c, d) locals (e) {
  if EREC⦃c⦄ == 3 && EREC⦃d⦄ == 3 { e := call cv_eq(c + 1, d + 1); return e };
  e := call ci_eq(c, d);
  return e
}

/-- `pin_copy_ok(c, pin)`: `pinCopyOk`: `c`'s names distinct and as many as the pin's, and `c`
the pin at them (`ci_at_lps`, computed only then). -/
-- con-ron: ConRon/Arena/Basis.lean:109-116 ConRon.Arena.pinCopyOk
@[no_expose, l_impl ConRon.Arena.pinCopyOk]
def pinCopyOk : FunDecl := lfn (c, pin) locals (io, il, d, a, e) {
  (io, il) := call cv_lps(c + 1);
  d := call sl_nodup(io, il);
  if d != 0 && il == EREC⦃pin + 3⦄ {
    a := call ci_at_lps(pin, EREC⦃c + 2⦄, EREC⦃c + 3⦄);
    e := call pin_agrees(c, a);
    return e
  };
  return 0
}

/-- `pin_link_go(ro, rl, rpo, rpl, co, cpo, n)`: the first `n` names of the `IW` slices `C` (at
`co`) and `Cp` (at `cpo`): `C[i]` is `Cp[i]` under the renaming `Rp ↦ R` (`Level.subst` of a
parameter: the first match, unlisted or past `R` unchanged: `canon_name_map`). -/
-- con-ron: ConRon/Arena/Basis.lean:118-127 ConRon.Arena.pinLinkOk
@[no_expose, l_impl ConRon.Arena.pinLinkOk]
def pinLinkGo : FunDecl := lfn (ro, rl, rpo, rpl, co, cpo, n) locals (x, r) {
  if n == 0 { return 1 };
  x := call canon_name_map(rpo, rpl, ro, rl, IW.u64[cpo]);
  if IW.u64[co] != x { return 0 };
  r := call pin_link_go(ro, rl, rpo, rpl, co + 1, cpo + 1, n - 1);
  return r
}

/-- `pin_link_ok(ro, rl, rpo, rpl, co, cl, cpo, cpl)`: `pinLinkOk R Rp C Cp` (four `IW` name
slices): the constructor's names are the pin constructor's at the recursor's renaming, as lists of
`.param` levels (equally long, pairwise). -/
-- con-ron: ConRon/Arena/Basis.lean:118-127 ConRon.Arena.pinLinkOk
@[no_expose, l_impl ConRon.Arena.pinLinkOk]
def pinLinkOk : FunDecl := lfn (ro, rl, rpo, rpl, co, cl, cpo, cpl) locals (r) {
  if cl != cpl { return 0 };
  r := call pin_link_go(ro, rl, rpo, rpl, co, cpo, cl);
  return r
}

/-- `const_named(o, l, n)`: `constNamed? cs n` on an `IW` slice of constant records: `(1, c)` for
the first named `n`, else `(0, 0)`. -/
-- con-ron: ConRon/Arena/Basis.lean:129-132 ConRon.Arena.constNamed?
@[no_expose, l_impl ConRon.Arena.constNamed?]
def constNamed : FunDecl := lfn (o, l, n) locals (c, f, r) {
  if l == 0 { return (0, 0) };
  c := IW.u64[o];
  if EREC⦃c + 1⦄ == n { return (1, c) };
  (f, r) := call const_named(o + 1, l - 1, n);
  return (f, r)
}

/-- `rules_link_ok(bo, bl, po, pl, ro, rl, rpo, rpl, qo, ql)`: the pin's rules (the `EREC` slice
`(qo, ql)`): each rule's constructor found in the block and in the pins (`IW` slices), linked as
`pin_link_ok` says at the recursors' names `R`, `Rp` (`IW` slices). -/
-- con-ron: ConRon/Arena/Basis.lean:134-146 ConRon.Arena.rulesLinkOk
@[no_expose, l_impl ConRon.Arena.rulesLinkOk]
def rulesLinkOk : FunDecl :=
    lfn (bo, bl, po, pl, ro, rl, rpo, rpl, qo, ql) locals (f, c, g, d, co, cl, so, sl, e) {
  if ql == 0 { return 1 };
  (f, c) := call const_named(bo, bl, EREC⦃qo⦄);
  (g, d) := call const_named(po, pl, EREC⦃qo⦄);
  if f == 0 || g == 0 { return 0 };
  (co, cl) := call cv_lps(c + 1);
  (so, sl) := call cv_lps(d + 1);
  e := call pin_link_ok(ro, rl, rpo, rpl, co, cl, so, sl);
  if e == 0 { return 0 };
  e := call rules_link_ok(bo, bl, po, pl, ro, rl, rpo, rpl, qo + 11, ql - 1);
  return e
}

/-- `block_link_ok_at(bo, bl, po, pl, fo, fl, c, p)`: one pair of `blockLinksOk`: a constructor
carries the former's names (the `EREC` slice `(fo, fl)`); a recursor against a pin recursor links
the pin's rules; every other pair passes. -/
-- con-ron: ConRon/Arena/Basis.lean:148-155 ConRon.Arena.blockLinkOkAt
@[no_expose, l_impl ConRon.Arena.blockLinkOkAt]
def blockLinkOkAt : FunDecl :=
    lfn (bo, bl, po, pl, fo, fl, c, p) locals (e, ro, rl, rpo, rpl) {
  if EREC⦃c⦄ == 4 {
    e := call er_sl_eq(EREC⦃c + 2⦄, EREC⦃c + 3⦄, fo, fl);
    return e
  };
  if EREC⦃c⦄ == 5 && EREC⦃p⦄ == 5 {
    (ro, rl) := call cv_lps(c + 1);
    (rpo, rpl) := call cv_lps(p + 1);
    e := call rules_link_ok(bo, bl, po, pl, ro, rl, rpo, rpl, EREC⦃p + 7⦄, EREC⦃p + 8⦄);
    return e
  };
  return 1
}

/-- `block_links_ok_go(bo, bl, po, pl, fo, fl, co, cl, qo, ql)`: `block_link_ok_at` over the
pairs of the two `IW` slices `(co, cl)`, `(qo, ql)` (the shorter ends it). -/
-- con-ron: ConRon/Arena/Basis.lean:157-164 ConRon.Arena.blockLinksOkGo
@[no_expose, l_impl ConRon.Arena.blockLinksOkGo]
def blockLinksOkGo : FunDecl :=
    lfn (bo, bl, po, pl, fo, fl, co, cl, qo, ql) locals (e) {
  if cl == 0 || ql == 0 { return 1 };
  e := call block_link_ok_at(bo, bl, po, pl, fo, fl, IW.u64[co], IW.u64[qo]);
  if e == 0 { return 0 };
  e := call block_links_ok_go(bo, bl, po, pl, fo, fl, co + 1, cl - 1, qo + 1, ql - 1);
  return e
}

/-- `block_links_ok(bo, bl, po, pl)`: `blockLinksOk block pins` (two `IW` slices): the former's
names are the first member's (none for an empty block). -/
-- con-ron: ConRon/Arena/Basis.lean:166-171 ConRon.Arena.blockLinksOk
@[no_expose, l_impl ConRon.Arena.blockLinksOk]
def blockLinksOk : FunDecl := lfn (bo, bl, po, pl) locals (c, fo, fl, e) {
  fo := 0;
  fl := 0;
  if bl != 0 {
    c := IW.u64[bo];
    fo := EREC⦃c + 2⦄;
    fl := EREC⦃c + 3⦄
  };
  e := call block_links_ok_go(bo, bl, po, pl, fo, fl, bo, bl, po, pl);
  return e
}

/-- `pin_copies_ok(co, cl, po, pl)`: `listBeqBy pinCopyOk`: equally long, `pin_copy_ok` pairwise. -/
-- con-ron: ConRon/Arena/Basis.lean:173-180 ConRon.Arena.pinCopiesOk
@[no_expose, l_impl ConRon.Arena.pinCopiesOk]
def pinCopiesOk : FunDecl := lfn (co, cl, po, pl) locals (e) {
  if cl == 0 && pl == 0 { return 1 };
  if cl == 0 || pl == 0 { return 0 };
  e := call pin_copy_ok(IW.u64[co], IW.u64[po]);
  if e == 0 { return 0 };
  e := call pin_copies_ok(co + 1, cl - 1, po + 1, pl - 1);
  return e
}

/-- `pin_list_ok(bo, bl, po, pl)`: `pinListOk block pins` (two `IW` slices): the copies, then the
links. -/
-- con-ron: ConRon/Arena/Basis.lean:182-185 ConRon.Arena.pinListOk
@[no_expose, l_impl ConRon.Arena.pinListOk]
def pinListOk : FunDecl := lfn (bo, bl, po, pl) locals (e) {
  e := call pin_copies_ok(bo, bl, po, pl);
  if e == 0 { return 0 };
  e := call block_links_ok(bo, bl, po, pl);
  return e
}

/-! ## Recognising a pinned block in a stream record -/

/-- `block_names_eq(ao, al, bo, bl)`: `blockNames a == blockNames b` (two `IW` slices of constant
records: equally long, the names pairwise equal). -/
-- con-ron: ConRon/Arena/Basis.lean:189-191 ConRon.Arena.blockNames
@[no_expose, l_impl ConRon.Arena.blockNames]
def blockNamesEq : FunDecl := lfn (ao, al, bo, bl) locals (e) {
  if al != bl { return 0 };
  if al == 0 { return 1 };
  if EREC⦃IW.u64[ao] + 1⦄ != EREC⦃IW.u64[bo] + 1⦄ { return 0 };
  e := call block_names_eq(ao + 1, al - 1, bo + 1, bl - 1);
  return e
}

/-- `basis_name_hit_go(io, il, k)`: the kinds `k, …, 3` (`eqK`, `natK`, `emptyK`, `falseK`) in
order: the first whose pinned block's names are the block's (an `IW` slice) → `(1, k)`; none →
`(0, 0)`. -/
-- con-ron: ConRon/Arena/Basis.lean:193-200 ConRon.Arena.basisNameHitGo
@[no_expose, l_impl ConRon.Arena.basisNameHitGo]
def basisNameHitGo : FunDecl := lfn (io, il, k) locals (po, pl, e, f, r) {
  if 4 <= k { return (0, 0) };
  (po, pl) := call rom_basis_decls(k);
  e := call block_names_eq(po, pl, io, il);
  if e != 0 { return (1, k) };
  (f, r) := call basis_name_hit_go(io, il, k + 1);
  return (f, r)
}

/-- `basis_name_hit(bo, bl)`: `basisNameHit block` (the block an `EREC` slice of record
pointers, as `ind_block_to_erec` makes it) → `(hit, kind)`. -/
-- con-ron: ConRon/Arena/Basis.lean:202-206 ConRon.Arena.basisNameHit
@[no_expose, l_impl ConRon.Arena.basisNameHit]
def basisNameHit : FunDecl := lfn (bo, bl) locals (io, il, f, k) {
  (io, il) := call er_to_iw(bo, bl);
  (f, k) := call basis_name_hit_go(io, il, 0);
  return (f, k)
}

/-- `at_block_go(po, pl, co, cl)`: each pin at the names its record declares (the shorter list
ends it), a fresh `IW` slice of records. -/
-- con-ron: ConRon/Arena/Basis.lean:208-215 ConRon.Arena.atBlockGo
@[no_expose, l_impl ConRon.Arena.atBlockGo]
def atBlockGo : FunDecl := lfn (po, pl, co, cl) locals (c, x, ro, rl, q, m) {
  if pl == 0 || cl == 0 { return (0, 0) };
  c := IW.u64[co];
  x := call ci_at_lps(IW.u64[po], EREC⦃c + 2⦄, EREC⦃c + 3⦄);
  (ro, rl) := call at_block_go(po + 1, pl - 1, co + 1, cl - 1);
  (q, m) := call sl_cons(x, ro, rl);
  return (q, m)
}

/-- `basis_at_block(kind, bo, bl)`: `BasisKind.atBlock kind block` (the block an `EREC` slice of
record pointers) → an `IW` slice of the records a pinned block's check installs. -/
-- con-ron: ConRon/Arena/Basis.lean:217-221 ConRon.Arena.BasisKind.atBlock
@[no_expose, l_impl ConRon.Arena.BasisKind.atBlock]
def basisAtBlock : FunDecl := lfn (kind, bo, bl) locals (po, pl, io, il, ro, rl) {
  (po, pl) := call rom_basis_decls(kind);
  (io, il) := call er_to_iw(bo, bl);
  (ro, rl) := call at_block_go(po, pl, io, il);
  return (ro, rl)
}

/-! ## The quotient records -/

/-- `quot_pin(k)`: `quotPin k`, the pinned quotient package's record at slot `k`. The ROM's block
has the five slots; a slot past it (the twin's `getD … default`, unreachable) aborts. -/
-- con-ron: ConRon/Arena/Basis.lean:223-227 ConRon.Arena.quotPin
@[no_expose, l_impl ConRon.Arena.quotPin]
def quotPin : FunDecl := lfn (k) locals (o, l) {
  (o, l) := call rom_basis_decls(4);
  if l <= k { abort };
  return IW.u64[o + k]
}

/-- `quot_at(k, q)`: `quotAt k cv` (`q` a constant value): the slot's pin at `cv`'s names. -/
-- con-ron: ConRon/Arena/Basis.lean:229-232 ConRon.Arena.quotAt
@[no_expose, l_impl ConRon.Arena.quotAt]
def quotAt : FunDecl := lfn (k, q) locals (c, r) {
  c := call quot_pin(k);
  r := call ci_at_lps(c, EREC⦃q + 1⦄, EREC⦃q + 2⦄);
  return r
}

/-- `quot_pin_hit(k, q)`: `quotPinHit k cv`: `cv`'s names distinct and as many as the pin's, and
`cv` the pin's constant value at them. -/
-- con-ron: ConRon/Arena/Basis.lean:234-242 ConRon.Arena.quotPinHit
@[no_expose, l_impl ConRon.Arena.quotPinHit]
def quotPinHitL : FunDecl := lfn (k, q) locals (c, io, il, d, a, z, e) {
  c := call quot_pin(k);
  (io, il) := call cv_lps(q);
  d := call sl_nodup(io, il);
  if d != 0 && il == EREC⦃c + 3⦄ {
    a := call erec_alloc(4);
    z := call cv_at_lps(a, c + 1, EREC⦃q + 1⦄, EREC⦃q + 2⦄);
    e := call cv_eq(q, a);
    return e
  };
  return 0
}

/-- `quot_preds_ok(vis, k)`: `quotPredsOk fe k`: the constants slot `k`'s type mentions stored
(`Eq`, `Quot`, `Quot.mk`: pin slots `0`, `47`, `51`), all three read first. -/
-- con-ron: ConRon/Arena/Basis.lean:244-256 ConRon.Arena.quotPredsOk
@[no_expose, l_impl ConRon.Arena.quotPredsOk]
def quotPredsOk : FunDecl := lfn (vis, k) locals (n, he, hq, hm, r) {
  n := call pin_at(0);
  (he, r) := call env_find(n, vis);
  n := call pin_at(47);
  (hq, r) := call env_find(n, vis);
  n := call pin_at(51);
  (hm, r) := call env_find(n, vis);
  if k == 0 { return he };
  if k == 1 { return hq };
  if k == 2 || k == 4 {
    if he != 0 && hq != 0 && hm != 0 { return 1 };
    return 0
  };
  if hq != 0 && hm != 0 { return 1 };
  return 0
}

/-! ## The module's program -/

/-- This module's functions. -/
def basisFns : Prog :=
  [("cv_at_lps", cvAtLps), ("spn_to_er", spnToEr), ("fire_levels_at", fireLevelsAt),
   ("rules_at_lps_go", rulesAtLpsGo), ("er_copy_er", erCopyEr), ("ci_at_lps", ciAtLps),
   ("pin_agrees", pinAgrees), ("pin_copy_ok", pinCopyOk), ("pin_link_go", pinLinkGo),
   ("pin_link_ok", pinLinkOk), ("const_named", constNamed), ("rules_link_ok", rulesLinkOk),
   ("block_link_ok_at", blockLinkOkAt), ("block_links_ok_go", blockLinksOkGo),
   ("block_links_ok", blockLinksOk), ("pin_copies_ok", pinCopiesOk), ("pin_list_ok", pinListOk),
   ("block_names_eq", blockNamesEq), ("basis_name_hit_go", basisNameHitGo),
   ("basis_name_hit", basisNameHit), ("at_block_go", atBlockGo),
   ("basis_at_block", basisAtBlock), ("quot_pin", quotPin), ("quot_at", quotAt),
   ("quot_pin_hit", quotPinHitL), ("quot_preds_ok", quotPredsOk)]

end L.Ind
