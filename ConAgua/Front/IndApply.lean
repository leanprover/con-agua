module

public import ConAgua.Front.IndFields
public import ConAgua.Front.ApplyDecl
import ConAgua.Census.Attr

@[expose] public section

/-!
# `inductive` lines into the parse state: `validateIndD`, `installIndD` (lane `induct`, worker I)

The L translation of con-ron's `processLineCoreD` `.ind` arm
(`vendor/con-ron/ConRon/Arena/Frontend/ExportC.lean:411`): `validateIndD` (the block's checks,
reading the state and changing nothing), then `installIndD` (the block's constants, pushed as one
`indDecl`), with their helpers `indPiTeleLen`, `parseRuleD` (same file) and
`piSortTeleLen?` (`ConRon/Arena/Env.lean:326`). Every `return .inl (.declined …)`/`.invalid …` and
every `fail` is an `abort` (`fail R` with the twin's message as the reason `R`,
`Arena/Reasons.lean`); no message is built. A name comparison is
a handle (word) comparison.

## The declarations: `DECL` kind `6`, and the constant records in `DIND` (= `DLP`)

`DECL` (67, `ApplyDecl.lean`) gets a sixth record kind: **`6` = `indDecl block nP`**, the eight
words `[6, 0, block.off, block.cnt, nP, 0, 0, 0]` (written by `decl_push(6, 0, off, cnt, nP, 0, 0,
0)`), where `block` is a slice of `DIND` words, each a pointer to a constant record in `DIND`.

`DIND` is `DLP` (68): word `0` is its top (records at `1 + top`, pointers absolute), the pool the
other declarations' universe parameter lists live in; a constant's universe parameters are
`lp_put`'s slice of it. The constant records use lane `pinsenv`'s layout `decCI`
(`ConAgua/Arena/EnvRec.lean`) over the pool itself (a recursor's rule slice is a slice of it too):

| constant | words at `p` |
|---|---|
| `indInfo cv {}` | `3`, cv (4: name, lps.off, lps.len, type), the default `IIndCaps` (15: `0,0,0,0,0,0,0, 1,0,0, 0,0, 0, 0,0`) — 20 |
| `ctorInfo cv nP nF induct` | `4`, cv, `nP`, `nF`, `induct` — 8 |
| `recInfo cv major pre rules` | `5`, cv, `major`, `pre`, rules.off, rules.cnt — 9; each rule 11 words (`decRule`): `ctor, nfields, 0, 0 (plain), 0, 0, 0, 0, rhs, 0, 0` |

The relation is `IndDeclAt` (`StateDR.lean`). The line's hook: `Line.lean`'s `apply_dline` calls
`apply_ind(nm)` at `pl = 25`, `nm` being the `inductive` member's value position (`decl_val`,
`FieldsDecl.lean`); `apply_ind_line(j)` (the line's first member) is the same entry from the line.
The refinement: `applyInd_ref` (`FrontPreOK2.lean`), on `validate_ref` (`IndApplyRefine9`) and
`installW_twin` (`IndInstallRefine5`); the line's (`applyDLine_ref`, `ApplyDLineRef.lean`) reads
it through `apply_ind`'s unified model.

## The work lists

The validation's lists (`tyNames`, `tyTypes`, `listed.flatten`, the constructor names, the
ordered constructors) are `IFL` slices (`IndFields.lean`); the ordered constructors are pointers to
their `IFR` records. their `IFR` records, the types that list them (their `induct`) a parallel `IFL` slice of names.
`kExpected?` is one word: `0` none, `1` `some false`, `2` `some true`.

## The functions

Every loop of the twin (a `List` recursion, `mapM`, `for`) is a self-recursive L function over an
index `j` (`…_go`), so that its refinement is one induction mirroring the list.

`store_fuel()`, `ind_pi_tele_len(f, e)`, `pi_sort_tele_len(f, e)`,
`name_rec_pre(n)` (`viewN n` matched against `.str T "rec"`), `ifl_contains`, `ifl_nodup`,
`ifl_find_last`; `vi_unsafe`, `vi_np_go`/`vi_nparams`, `vi_map_go`/`vi_map`,
`vi_ids_go`/`vi_listed_go`/`vi_listed`, `vi_ctor`, `vi_order_in`/`vi_order_go`/`vi_order`,
`vi_rec_idx`, `vi_rec`, `vi_nested`/`vi_recs_go`/`vi_recs`, `vi_tail`,
`validate_ind_d`;
`dind_alloc`, `ind_cv`, `ind_caps`, `parse_rule_d`, `ind_rules_go`/`ind_rules`, `ind_type`,
`ind_ctor`, `ind_rec`, `inst_types`/`inst_ctors`/`inst_recs`, `install_ind_d`; `apply_ind(v)`,
`apply_ind_line(j)`.
-/

open L.Arena

namespace L.Front.Ind

open L.Front

/-! ## Telescopes -/

/-- `ctl_sum(k, c)`: `CTL[k] + … + CTL[k + c - 1]`. -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:84-90 ConRon.Arena.Frontend.storeFuel
@[no_expose, l_impl ConRon.Arena.Frontend.storeFuel]
def ctlSum : FunDecl := lfn (k, c) locals (r) {
  if c == 0 { return 0 };
  r := call ctl_sum(k + 1, c - 1);
  return CTL.u64[k] + r
}

/-- `store_fuel()`: `storeFuel`, the expression store's node count `+ 1` (both tiers of the ten
expression tables, `e_view`'s counts). -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:84-90 ConRon.Arena.Frontend.storeFuel
@[no_expose, l_impl ConRon.Arena.Frontend.storeFuel]
def storeFuel : FunDecl := lfn () locals (a, b, c) {
  a := call ctl_sum(2, 4);
  b := call ctl_sum(16, 8);
  c := call ctl_sum(26, 8);
  return a + b + c + 1
}

/-- `ind_pi_tele_len(f, e)`: `indPiTeleLen f e`. -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:239-248 ConRon.Arena.Frontend.indPiTeleLen
@[no_expose, l_impl ConRon.Arena.Frontend.indPiTeleLen]
def indPiTeleLen : FunDecl := lfn (f, h) locals (g, x, y, z, r) {
  if f == 0 { abort };
  (g, x, y, z) := call e_view(h);
  if g == 6 {
    r := call ind_pi_tele_len(f - 1, y);
    return r + 1
  };
  return 0
}

/-- `pi_sort_tele_len(f, e)`: `piSortTeleLen? f e` as `(ok, n)`. -/
-- con-ron: ConRon/Arena/Env.lean:321-331 ConRon.Arena.piSortTeleLen?
@[no_expose, l_impl ConRon.Arena.piSortTeleLen?]
def piSortTeleLen : FunDecl := lfn (f, h) locals (g, x, y, z, ok, r) {
  if f == 0 { abort };
  (g, x, y, z) := call e_view(h);
  if g == 6 {
    (ok, r) := call pi_sort_tele_len(f - 1, y);
    if ok == 0 { return (0, 0) };
    return (1, r + 1)
  };
  if g == 2 { return (1, 0) };
  return (0, 0)
}

/-- `name_rec_pre(n)`: `viewN n` (aborting on a dangling handle, as `viewN` fails) matched against
`.str T "rec"`: `(1, T)`, else `(0, 0)`. Name tags: `0` anonymous (`NAREC`, counts `CTL[34 + t]`),
`1` str (`NSREC`, four words a node, the string's bytes a `POOL` slice, counts `CTL[36 + t]`),
`2` num (counts `CTL[38 + t]`). -/
-- con-ron: ConRon/Arena/Monad.lean:377-382 ConRon.Arena.viewN
@[no_expose, l_impl ConRon.Arena.viewN]
def nameRecPre : FunDecl := lfn (h) locals (g, t, i, o) {
  if 4294967295 < h { abort };
  g := ⟦h⟧.tag;
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if g == 0 { if NANON⟨t⟩.count <= i { abort }; return (0, 0) };
  if g == 2 { if NNUM⟨t⟩.count <= i { abort }; return (0, 0) };
  if g != 1 { abort };
  if NSTR⟨t⟩.count <= i { abort };
  if NSTR⟨t, i⟩.l != 3 { return (0, 0) };
  o := NSTR⟨t, i⟩.o;
  if POOL⦃o⦄ == 114 && POOL⦃o + 1⦄ == 101 && POOL⦃o + 2⦄ == 99 {
    return (1, NSTR⟨t, i⟩.p)
  };
  return (0, 0)
}

/-! ## `IFL` slices -/

/-- `ifl_contains(o, n, x, j)`: `x` among `IFL[o + j‥o + n)`. -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
@[no_expose] def iflContains : FunDecl := lfn (o, n, x, j) locals (r) {
  if n <= j { return 0 };
  if IFL.u64[o + j] == x { return 1 };
  r := call ifl_contains(o, n, x, j + 1);
  return r
}

/-- `ifl_nodup(o, n, j)`: `List.Nodup` of `IFL[o + j‥o + n)` (word equality). -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
@[no_expose] def iflNodup : FunDecl := lfn (o, n, j) locals (b, r) {
  if n <= j { return 1 };
  b := call ifl_contains(o, n, IFL.u64[o + j], j + 1);
  if b != 0 { return 0 };
  r := call ifl_nodup(o, n, j + 1);
  return r
}

/-- `ifl_find_last(o, x, j)`: the last index of `x` in `IFL[o‥o + j)` as `(ok, k)` (a
`HashMap.insert` fold's lookup: the last insert of a key wins). -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
@[no_expose] def iflFindLast : FunDecl := lfn (o, x, j) locals (f, k) {
  if j == 0 { return (0, 0) };
  if IFL.u64[o + j - 1] == x { return (1, j - 1) };
  (f, k) := call ifl_find_last(o, x, j - 1);
  return (f, k)
}

/-! ## `validateIndD` -/

/-- `vi_unsafe(to, tn, j)`: no type record from the `j`-th on is `isUnsafe` (else the block is
declined: abort). -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:256-354 ConRon.Arena.Frontend.validateIndD
@[no_expose, l_impl ConRon.Arena.Frontend.validateIndD]
def viUnsafe : FunDecl := lfn (to, tn, j) locals (u) {
  if tn <= j { return 0 };
  if IFR.u64[to + 11 * j + 7] != 0 { fail R_UNSAFE_INDUCTIVE_DECLARATION };
  u := call vi_unsafe(to, tn, j + 1);
  return 0
}

/-- `vi_np_go(to, tn, d, j)`: every type record from the `j`-th on has `numParams = d` (else
declined: abort). -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:256-354 ConRon.Arena.Frontend.validateIndD
@[no_expose, l_impl ConRon.Arena.Frontend.validateIndD]
def viNpGo : FunDecl := lfn (to, tn, d, j) locals (u) {
  if tn <= j { return 0 };
  if IFR.u64[to + 11 * j + 10] != d { fail R_INDUCTIVE_BLOCK_WHOSE };
  u := call vi_np_go(to, tn, d, j + 1);
  return 0
}

/-- `vi_nparams(to, tn)`: `nPd`, the first type's `numParams` (`0` without types); every type
agrees (else declined: abort). -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:256-354 ConRon.Arena.Frontend.validateIndD
@[no_expose, l_impl ConRon.Arena.Frontend.validateIndD]
def viNparams : FunDecl := lfn (to, tn) locals (d, u) {
  if tn == 0 { return 0 };
  d := IFR.u64[to + 10];
  u := call vi_np_go(to, tn, d, 0);
  return d
}

/-- `vi_map_go(o, n, sz, s, f, j)`: for the records of size `sz` at `o` from the `j`-th to the
`n`-th, the id in word `s` looked up (`f = 0`: `name_get`, else `expr_get`) and pushed to `IFL`. -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:256-354 ConRon.Arena.Frontend.validateIndD
@[no_expose, l_impl ConRon.Arena.Frontend.validateIndD]
def viMapGo : FunDecl := lfn (o, n, sz, s, f, j) locals (h, u) {
  if n <= j { return 0 };
  if f == 0 { h := call name_get(IFR.u64[o + sz * j + s]) }
  else { h := call expr_get(IFR.u64[o + sz * j + s]) };
  h := call ifl_push(h);
  u := call vi_map_go(o, n, sz, s, f, j + 1);
  return 0
}

/-- `vi_map(o, n, sz, s, f)`: `vi_map_go` from the first record, into a fresh `IFL` slice
`(off, n)`. -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:256-354 ConRon.Arena.Frontend.validateIndD
@[no_expose, l_impl ConRon.Arena.Frontend.validateIndD]
def viMap : FunDecl := lfn (o, n, sz, s, f) locals (lo, u) {
  lo := call ifl_alloc(0);
  u := call vi_map_go(o, n, sz, s, f, 0);
  return (lo, n)
}

/-- `vi_ids_go(o, n, k)`: the name ids `IFL[o + k‥o + n)` looked up and pushed to `IFL`. -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:256-354 ConRon.Arena.Frontend.validateIndD
@[no_expose, l_impl ConRon.Arena.Frontend.validateIndD]
def viIdsGo : FunDecl := lfn (o, n, k) locals (h, u) {
  if n <= k { return 0 };
  h := call name_get(IFL.u64[o + k]);
  h := call ifl_push(h);
  u := call vi_ids_go(o, n, k + 1);
  return 0
}

/-- `vi_listed_go(to, tn, j)`: `vi_ids_go` on the constructor list of every type record from the
`j`-th on. -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:256-354 ConRon.Arena.Frontend.validateIndD
@[no_expose, l_impl ConRon.Arena.Frontend.validateIndD]
def viListedGo : FunDecl := lfn (to, tn, j) locals (t, u) {
  if tn <= j { return 0 };
  t := to + 11 * j;
  u := call vi_ids_go(IFR.u64[t + 3], IFR.u64[t + 4], 0);
  u := call vi_listed_go(to, tn, j + 1);
  return 0
}

/-- `vi_listed(to, tn)`: `(listed).flatten`, every type's constructor name ids looked up, type by
type, into a fresh `IFL` slice `(off, cnt)`. -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:256-354 ConRon.Arena.Frontend.validateIndD
@[no_expose, l_impl ConRon.Arena.Frontend.validateIndD]
def viListed : FunDecl := lfn (to, tn) locals (lo, u) {
  lo := call ifl_alloc(0);
  u := call vi_listed_go(to, tn, 0);
  return (lo, IFL.u64[0] + 1 - lo)
}

/-- `vi_ctor(n, j, T, nP, fuel, cno, cn, co)`: constructor `n`, number `j` of type `T`: its
record (the last of the constructor records named `n`, `ctorIx`), checked (`cidx`, `induct`,
`numFields` against the telescope); the record's pointer. -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:256-354 ConRon.Arena.Frontend.validateIndD
@[no_expose, l_impl ConRon.Arena.Frontend.validateIndD]
def viCtor : FunDecl := lfn (n, j, tt, np, fuel, cno, cn, co) locals (f, k, c, x, t) {
  (f, k) := call ifl_find_last(cno, n, cn);
  if f == 0 { fail R_NO_SUCH_CONSTRUCTOR };
  c := co + 10 * k;
  if IFR.u64[c + 6] != 0 { if IFR.u64[c + 7] != j { fail R_CONSTRUCTOR_DECLARES_CIDX } };
  if IFR.u64[c + 8] != 0 {
    x := call name_get(IFR.u64[c + 9]);
    if x != tt { fail R_CONSTRUCTOR_DECLARES_INDUCT }
  };
  t := call expr_get(IFR.u64[c + 2]);
  x := call ind_pi_tele_len(fuel, t);
  if np + IFR.u64[c + 4] != x { fail R_CONSTRUCTOR_DECLARES_FIELDS };
  return c
}

/-- `vi_order_in(fo, cno, co, cn, fuel, nP, oo, tf, t, T, jj, pos)`: the constructors of the type
record at `IFR[t]` (named `T`) from its `jj`-th on, the `pos`-th of the block's own order first:
each checked by `vi_ctor`, its record pointer written to `IFL[oo + pos]` and the type that lists it,
its `induct`, to `IFL[tf + pos]`; the position after. -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:256-354 ConRon.Arena.Frontend.validateIndD
@[no_expose, l_impl ConRon.Arena.Frontend.validateIndD]
def viOrderIn : FunDecl := lfn (fo, cno, co, cn, fuel, np, oo, tf, t, tt, jj, pos) locals (c, r) {
  if IFR.u64[t + 4] <= jj { return pos };
  c := call vi_ctor(IFL.u64[fo + pos], jj, tt, np, fuel, cno, cn, co);
  IFL.u64[oo + pos] := c;
  IFL.u64[tf + pos] := tt;
  r := call vi_order_in(fo, cno, co, cn, fuel, np, oo, tf, t, tt, jj + 1, pos + 1);
  return r
}

/-- `vi_order_go(to, tn, tyN, fo, cno, co, cn, fuel, nP, oo, tf, ti, pos)`: `vi_order_in` for every
type record from the `ti`-th on. -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:256-354 ConRon.Arena.Frontend.validateIndD
@[no_expose, l_impl ConRon.Arena.Frontend.validateIndD]
def viOrderGo : FunDecl := lfn (to, tn, tyn, fo, cno, co, cn, fuel, np, oo, tf, ti, pos) locals (p, u) {
  if tn <= ti { return 0 };
  p := call vi_order_in(fo, cno, co, cn, fuel, np, oo, tf, to + 11 * ti, IFL.u64[tyn + ti], 0, pos);
  u := call vi_order_go(to, tn, tyn, fo, cno, co, cn, fuel, np, oo, tf, ti + 1, p);
  return 0
}

/-- `vi_order(to, tn, tyN, fo, cno, co, cn, fuel, nP)`: the constructors in the block's own order
(`types[].ctors`, type by type), each checked by `vi_ctor`, each paired with the type that lists it:
two `IFL` slices of `cn` words, the record pointers `(oo, cn)` and the types' names `(tf, cn)` (`cn`
is the flattened list's length, checked before). -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:256-354 ConRon.Arena.Frontend.validateIndD
@[no_expose, l_impl ConRon.Arena.Frontend.validateIndD]
def viOrder : FunDecl := lfn (to, tn, tyn, fo, cno, co, cn, fuel, np) locals (oo, tf, u) {
  oo := call ifl_alloc(cn);
  tf := call ifl_alloc(cn);
  u := call vi_order_go(to, tn, tyn, fo, cno, co, cn, fuel, np, oo, tf, 0, 0);
  return (oo, tf)
}

/-- `vi_rec_idx(T, nI, nP, tn, tyN, tyT, fuel, j)`: for every type from the `j`-th on named `T`
(in order), its telescope to a sort, if any, has `nP + nI` binders (else invalid: abort). -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:256-354 ConRon.Arena.Frontend.validateIndD
@[no_expose, l_impl ConRon.Arena.Frontend.validateIndD]
def viRecIdx : FunDecl := lfn (tt, ni, np, tn, tyn, tyt, fuel, j) locals (ok, n, u) {
  if tn <= j { return 0 };
  if IFL.u64[tyn + j] == tt {
    (ok, n) := call pi_sort_tele_len(fuel, IFL.u64[tyt + j]);
    if ok != 0 { if np + ni != n { fail R_RECURSOR_DECLARES_INDICES } }
  };
  u := call vi_rec_idx(tt, ni, np, tn, tyn, tyt, fuel, j + 1);
  return 0
}

/-- `vi_rec(r, nP, tn, cn, tyN, tyT, fuel)`: the recursor record at `r` checked. -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:256-354 ConRon.Arena.Frontend.validateIndD
@[no_expose, l_impl ConRon.Arena.Frontend.validateIndD]
def viRec : FunDecl := lfn (r, np, tn, cn, tyn, tyt, fuel) locals (rn, f, tt, u) {
  rn := call name_get(IFR.u64[r]);
  if IFR.u64[r + 8] != np { fail R_RECURSOR_DECLARES_PARAMETERS };
  if IFR.u64[r + 7] != tn { fail R_RECURSOR_DECLARES_MOTIVES };
  if IFR.u64[r + 6] != cn { fail R_RECURSOR_DECLARES_MINOR };
  (f, tt) := call name_rec_pre(rn);
  if f != 0 { u := call vi_rec_idx(tt, IFR.u64[r + 5], np, tn, tyn, tyt, fuel, 0) };
  return 0
}

/-- `vi_nested(to, tn, j)`: some type record from the `j`-th on has `numNested ≠ 0` (`1`), else
`0`. -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:256-354 ConRon.Arena.Frontend.validateIndD
@[no_expose, l_impl ConRon.Arena.Frontend.validateIndD]
def viNested : FunDecl := lfn (to, tn, j) locals (r) {
  if tn <= j { return 0 };
  if IFR.u64[to + 11 * j + 9] != 0 { return 1 };
  r := call vi_nested(to, tn, j + 1);
  return r
}

/-- `vi_recs_go(ro, rn, nP, tn, cn, tyN, tyT, fuel, j)`: the recursor records from the `j`-th
on checked. -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:256-354 ConRon.Arena.Frontend.validateIndD
@[no_expose, l_impl ConRon.Arena.Frontend.validateIndD]
def viRecsGo : FunDecl := lfn (ro, rn, np, tn, cn, tyn, tyt, fuel, j) locals (u) {
  if rn <= j { return 0 };
  u := call vi_rec(ro + 11 * j, np, tn, cn, tyn, tyt, fuel);
  u := call vi_recs_go(ro, rn, np, tn, cn, tyn, tyt, fuel, j + 1);
  return 0
}

/-- `vi_recs(to, tn, ro, rn, nP, cn, tyN, tyT, fuel)`: the recursor records checked, unless
the block is nested (some type has `numNested ≠ 0`). -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:256-354 ConRon.Arena.Frontend.validateIndD
@[no_expose, l_impl ConRon.Arena.Frontend.validateIndD]
def viRecs : FunDecl := lfn (to, tn, ro, rn, np, cn, tyn, tyt, fuel) locals (u) {
  u := call vi_nested(to, tn, 0);
  if u != 0 { return 0 };
  u := call vi_recs_go(ro, rn, np, tn, cn, tyn, tyt, fuel, 0);
  return 0
}

/-- `vi_tail(to, tn, co, cn, ro, rn, nP, tyN, tyT, fo, cno)`: `validateIndD` after the length
check: the store's fuel, the ordered constructors, the recursors; the ordered constructors' two
slices' offsets (`vi_order`). -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:256-354 ConRon.Arena.Frontend.validateIndD
@[no_expose, l_impl ConRon.Arena.Frontend.validateIndD]
def viTail : FunDecl := lfn (to, tn, co, cn, ro, rn, np, tyn, tyt, fo, cno) locals (fuel, oo, tf, u) {
  fuel := call store_fuel();
  (oo, tf) := call vi_order(to, tn, tyn, fo, cno, co, cn, fuel, np);
  u := call vi_recs(to, tn, ro, rn, np, cn, tyn, tyt, fuel);
  return (oo, tf)
}

/-- `validate_ind_d(to, tn, co, cn, ro, rn)`: `validateIndD` on the block's three lists (`IFR`
records); `(ordered.off, families.off, nPd)` (the ordered constructors are `cn` record pointers,
each paired with its type's name at the same position of the second slice). -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:256-354 ConRon.Arena.Frontend.validateIndD
@[no_expose, l_impl ConRon.Arena.Frontend.validateIndD]
def validateIndD : FunDecl := lfn (to, tn, co, cn, ro, rn)
    locals (np, tyn, tyt, fo, cno, x, u, oo, tf) {
  u := call vi_unsafe(to, tn, 0);
  np := call vi_nparams(to, tn);
  (tyn, x) := call vi_map(to, tn, 11, 0, 0);
  (tyt, x) := call vi_map(to, tn, 11, 2, 1);
  (fo, x) := call vi_listed(to, tn);
  (cno, u) := call vi_map(co, cn, 10, 0, 0);
  u := call ifl_nodup(fo, x, 0);
  if u == 0 { fail R_DUPLICATE_CONSTRUCTOR_NAME };
  if x != cn { fail R_THE_INDUCTIVE_BLOCK };
  (oo, tf) := call vi_tail(to, tn, co, cn, ro, rn, np, tyn, tyt, fo, cno);
  return (oo, tf, np)
}

/-! ## `installIndD` -/

/-- `dind_alloc(n)`: `n` words of `DIND`; their absolute index. -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:356-381 ConRon.Arena.Frontend.installIndD
@[no_expose, l_impl ConRon.Arena.Frontend.installIndD]
def dindAlloc : FunDecl := lfn (n) locals (o) {
  if len(DIND.u64) == 0 { abort };
  o := DIND.u64[0] + 1;
  if len(DIND.u64) < o { abort R_CAP_TABLE };
  if len(DIND.u64) - o < n { abort R_CAP_TABLE };
  DIND.u64[0] := o - 1 + n;
  return o
}

/-- `ind_cv(q, name, lps, type)`: `parseCVD` (name, type, universe parameters, in that order),
written as the 4-word constant value at `DIND[q]`; the universe parameters are `lp_put`'s slice
(`ApplyDecl.lean`, the same pool). -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:230-237 ConRon.Arena.Frontend.parseCVD
@[no_expose, l_impl ConRon.Arena.Frontend.parseCVD]
def indCv : FunDecl := lfn (q, nm, lps, ty) locals (n, t, o, l) {
  n := call name_get(nm);
  t := call expr_get(ty);
  (o, l) := call lp_put(lps);
  DIND.u64[q] := n;
  DIND.u64[q + 1] := o + 1;
  DIND.u64[q + 2] := l;
  DIND.u64[q + 3] := t;
  return 0
}

/-- `ind_caps(q)`: the default `IIndCaps` (`{}`) in the 15-word record at `DIND[q]` (`decCaps`; words
`q + 1‥q + 5` are unused). -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:356-381 ConRon.Arena.Frontend.installIndD
@[no_expose, l_impl ConRon.Arena.Frontend.installIndD]
def indCaps : FunDecl := lfn (q) {
  DIND.u64[q] := 0; DIND.u64[q + 6] := 0; DIND.u64[q + 7] := 0;
  DIND.u64[q + 8] := 0; DIND.u64[q + 9] := 0; DIND.u64[q + 10] := 0; DIND.u64[q + 11] := 0;
  DIND.u64[q + 12] := 0; DIND.u64[q + 13] := 0; DIND.u64[q + 14] := 0;
  return 0
}

/-- `parse_rule_d(q, rp)`: `parseRuleD` of the rule record `IFL[rp‥rp + 3)`, written as the
11-word `IRecRule` at `DIND[q]` (`decRule`). -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:250-254 ConRon.Arena.Frontend.parseRuleD
@[no_expose, l_impl ConRon.Arena.Frontend.parseRuleD]
def parseRuleD : FunDecl := lfn (q, rp) locals (n, e) {
  n := call name_get(IFL.u64[rp]);
  e := call expr_get(IFL.u64[rp + 2]);
  DIND.u64[q] := n; DIND.u64[q + 1] := IFL.u64[rp + 1]; DIND.u64[q + 2] := 0;
  DIND.u64[q + 3] := 0; DIND.u64[q + 4] := 0; DIND.u64[q + 5] := 0; DIND.u64[q + 6] := 0;
  DIND.u64[q + 7] := 0; DIND.u64[q + 8] := e; DIND.u64[q + 9] := 0; DIND.u64[q + 10] := 0;
  return 0
}

/-- `ind_rules_go(lo, o, n, j)`: the rule records at `IFL[o]` from the `j`-th to the `n`-th,
written as 11-word rules at `DIND[lo]`. -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:356-381 ConRon.Arena.Frontend.installIndD
@[no_expose, l_impl ConRon.Arena.Frontend.installIndD]
def indRulesGo : FunDecl := lfn (lo, o, n, j) locals (u) {
  if n <= j { return 0 };
  u := call parse_rule_d(lo + 11 * j, o + 3 * j);
  u := call ind_rules_go(lo, o, n, j + 1);
  return 0
}

/-- `ind_rules(o, n)`: the `n` rule records at `IFL[o]` (3 words each) as a fresh `DIND` slice of
11-word rules; `(off, n)`. -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:356-381 ConRon.Arena.Frontend.installIndD
@[no_expose, l_impl ConRon.Arena.Frontend.installIndD]
def indRules : FunDecl := lfn (o, n) locals (lo, u) {
  if 4294967296 <= n { abort R_CAP_WORD };
  lo := call dind_alloc(11 * n);
  u := call ind_rules_go(lo, o, n, 0);
  return (lo, n)
}

/-- `ind_type(t)`: the `indInfo` record of the type record at `IFR[t]`; its pointer. -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:356-381 ConRon.Arena.Frontend.installIndD
@[no_expose, l_impl ConRon.Arena.Frontend.installIndD]
def indType : FunDecl := lfn (t) locals (q, u) {
  q := call dind_alloc(20);
  DIND.u64[q] := 3;
  u := call ind_cv(q + 1, IFR.u64[t], IFR.u64[t + 1], IFR.u64[t + 2]);
  u := call ind_caps(q + 5);
  return q
}

/-- `ind_ctor(c, T)`: the `ctorInfo` record of the constructor record at `IFR[c]`, its family `T`;
its pointer. -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:356-381 ConRon.Arena.Frontend.installIndD
@[no_expose, l_impl ConRon.Arena.Frontend.installIndD]
def indCtor : FunDecl := lfn (c, tt) locals (q, u) {
  q := call dind_alloc(8);
  DIND.u64[q] := 4;
  u := call ind_cv(q + 1, IFR.u64[c], IFR.u64[c + 1], IFR.u64[c + 2]);
  DIND.u64[q + 5] := IFR.u64[c + 5];
  DIND.u64[q + 6] := IFR.u64[c + 4];
  DIND.u64[q + 7] := tt;
  return q
}

/-- `ind_rec(r)`: the `recInfo` record of the recursor record at `IFR[r]` (its rules first, then
its constant value, as the twin); its pointer. -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:356-381 ConRon.Arena.Frontend.installIndD
@[no_expose, l_impl ConRon.Arena.Frontend.installIndD]
def indRec : FunDecl := lfn (r) locals (q, u, lo, ln, a) {
  q := call dind_alloc(10);
  DIND.u64[q] := 5;
  (lo, ln) := call ind_rules(IFR.u64[r + 9], IFR.u64[r + 10]);
  u := call ind_cv(q + 1, IFR.u64[r], IFR.u64[r + 1], IFR.u64[r + 2]);
  a := IFR.u64[r + 8] + IFR.u64[r + 7] + IFR.u64[r + 6];
  DIND.u64[q + 5] := a + IFR.u64[r + 5];
  DIND.u64[q + 6] := a;
  DIND.u64[q + 7] := lo;
  DIND.u64[q + 8] := ln;
  DIND.u64[q + 9] := IFR.u64[r + 4];
  return q
}

/-- `inst_types(bo, to, tn, j)`: the `indInfo` records of the type records from the `j`-th on,
their pointers at `DIND[bo + j]`. -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:356-381 ConRon.Arena.Frontend.installIndD
@[no_expose, l_impl ConRon.Arena.Frontend.installIndD]
def instTypes : FunDecl := lfn (bo, to, tn, j) locals (q, u) {
  if tn <= j { return 0 };
  q := call ind_type(to + 11 * j);
  DIND.u64[bo + j] := q;
  u := call inst_types(bo, to, tn, j + 1);
  return 0
}

/-- `inst_ctors(bo, oo, tf, on, j)`: the `ctorInfo` records of the ordered constructors (record
pointers `IFL[oo + j]`, their families `IFL[tf + j]`) from the `j`-th on, their pointers at
`DIND[bo + j]`. -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:356-381 ConRon.Arena.Frontend.installIndD
@[no_expose, l_impl ConRon.Arena.Frontend.installIndD]
def instCtors : FunDecl := lfn (bo, oo, tf, on, j) locals (q, u) {
  if on <= j { return 0 };
  q := call ind_ctor(IFL.u64[oo + j], IFL.u64[tf + j]);
  DIND.u64[bo + j] := q;
  u := call inst_ctors(bo, oo, tf, on, j + 1);
  return 0
}

/-- `inst_recs(bo, ro, rn, j)`: the `recInfo` records of the recursor records from the `j`-th on,
their pointers at `DIND[bo + j]`. -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:356-381 ConRon.Arena.Frontend.installIndD
@[no_expose, l_impl ConRon.Arena.Frontend.installIndD]
def instRecs : FunDecl := lfn (bo, ro, rn, j) locals (q, u) {
  if rn <= j { return 0 };
  q := call ind_rec(ro + 11 * j);
  DIND.u64[bo + j] := q;
  u := call inst_recs(bo, ro, rn, j + 1);
  return 0
}

/-- `install_ind_d(to, tn, oo, tf, on, ro, rn, nP)`: `installIndD`: the block (types, the ordered
constructors with their families, recursors) as `DIND` constant records, pushed as one `DECL`
record of kind `6`. -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:356-381 ConRon.Arena.Frontend.installIndD
@[no_expose, l_impl ConRon.Arena.Frontend.installIndD]
def installIndD : FunDecl := lfn (to, tn, oo, tf, on, ro, rn, np) locals (bo, u) {
  if 4294967296 <= tn || 4294967296 <= on || 4294967296 <= rn { abort R_CAP_WORD };
  bo := call dind_alloc(tn + on + rn);
  u := call inst_types(bo, to, tn, 0);
  u := call inst_ctors(bo + tn, oo, tf, on, 0);
  u := call inst_recs(bo + tn + on, ro, rn, 0);
  u := call decl_push(6, 0, bo, tn + on + rn, np, 0, 0, 0);
  return 0
}

/-! ## The entries -/

/-- `apply_ind(v)`: the `.ind` arm of `processLineCoreD` for the `inductive` object whose `{` is
at `v`: its fields, `validateIndD`, `installIndD`. -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:383-433 ConRon.Arena.Frontend.processLineCoreD
@[no_expose, l_impl ConRon.Arena.Frontend.processLineCoreD]
def applyInd : FunDecl := lfn (v) locals (to, tn, co, cn, ro, rn, oo, tf, np, u) {
  (to, tn, co, cn, ro, rn) := call ind_fields(v);
  (oo, tf, np) := call validate_ind_d(to, tn, co, cn, ro, rn);
  u := call install_ind_d(to, tn, oo, tf, cn, ro, rn, np);
  return 0
}

/-- `apply_ind_line(j)`: an `inductive` declaration line (`j` after its `{`; `rec_decl_line`
reported `pl = 25`, so its one member is `inductive`, key `23`), applied. -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:383-433 ConRon.Arena.Frontend.processLineCoreD
@[no_expose, l_impl ConRon.Arena.Frontend.processLineCoreD]
def applyIndLine : FunDecl := lfn (j) locals (tag, ks, w, k, v, u) {
  (tag, ks, w, k, v) := call next_member(j, 1);
  if tag == 0 || tag == 1 || k != 23 { abort };
  u := call apply_ind(v);
  return 0
}

/-- The apply step's functions. -/
def indApplyFns : Prog :=
  [("ctl_sum", ctlSum), ("store_fuel", storeFuel), ("ind_pi_tele_len", indPiTeleLen),
   ("pi_sort_tele_len", piSortTeleLen), ("name_rec_pre", nameRecPre),
   ("ifl_contains", iflContains), ("ifl_nodup", iflNodup), ("ifl_find_last", iflFindLast),
   ("vi_unsafe", viUnsafe), ("vi_np_go", viNpGo), ("vi_nparams", viNparams),
   ("vi_map_go", viMapGo), ("vi_map", viMap), ("vi_ids_go", viIdsGo),
   ("vi_listed_go", viListedGo), ("vi_listed", viListed), ("vi_ctor", viCtor),
   ("vi_order_in", viOrderIn), ("vi_order_go", viOrderGo), ("vi_order", viOrder),
   ("vi_rec_idx", viRecIdx), ("vi_rec", viRec),
   ("vi_nested", viNested), ("vi_recs_go", viRecsGo), ("vi_recs", viRecs),
   ("vi_tail", viTail), ("validate_ind_d", validateIndD),
   ("dind_alloc", dindAlloc), ("ind_cv", indCv), ("ind_caps", indCaps),
   ("parse_rule_d", parseRuleD), ("ind_rules_go", indRulesGo), ("ind_rules", indRules),
   ("ind_type", indType), ("ind_ctor", indCtor), ("ind_rec", indRec),
   ("inst_types", instTypes), ("inst_ctors", instCtors), ("inst_recs", instRecs),
   ("install_ind_d", installIndD),
   ("apply_ind", applyInd), ("apply_ind_line", applyIndLine)]

end L.Front.Ind
