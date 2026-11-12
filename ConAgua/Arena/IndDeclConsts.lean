module

public import ConAgua.Arena.IndIface
meta import ConAgua.Arena.IndIface

@[expose] public section

/-!
# What a declaration installs (lane `induct`, module `IndDeclConsts`)

The L translation of `vendor/con-ron/ConRon/Arena/Install.lean`: a declaration's constants and
projection tables, read off the record with no environment, no inference and no reduction
(`declConstants`, `declTables`, `blockConstants`, `blockFormers`, `blockCtors`, `blockRecs`,
`recFire`, `exprDropVars`, `blockTables`), and the pushes (`IFEnv.pushAll`, `pushTables`,
`pushDelta`). The block's check pushes the block's part of this once its checks pass
(`check_block`, `IndInstall.lean`); the stream index is built from `decl_constants(i)` and
`decl_tables(i)` before any check runs (the lead's `build_index`, with the scratch tier off, so
every record these build lands in `EREC` tier 0).

**Results.** A list of constants or tables is an `IW` slice `(off, cnt)` of `EREC` record
addresses (constant records, `decCI`; table records, 13 words, `EnvRec.lean`). Every list a
record keeps (a table's `lps` and `bodies`, a rule's fire slices) is copied into `EREC`
(`er_from_iw`).

**`decl_constants(i)`, `decl_tables(i)`** read the front's `DECL` record `i` (`Front/StateDR.lean`'s
`DeclAt`: word `k` at `1 + 8 i + k`; kind `1` axiom, `2` definition, `3` theorem, `4` opaque, `5`
quotient (its kind word `6`: `1` type, `2` ctor, `3` lift, else ind), `6` inductive block). A
one-constant record's constant is `erec_ci(i, kind)` (the lead's `DeclStep.lean`, the `decCI` kinds
`0` axiom, `1` defn, `2` thm); a block is `ind_block_to_erec(i)`'s `EREC` slice, its `nP` word `4`.

**Foreign callees** (the lead's pins): `basis_name_hit(bo, bl)` → `(hit, kind)`,
`basis_at_block(kind, bo, bl)` → `IW` slice, `quot_at(slot, cv)` → constant record (`slot`
`QuotKind.slot`: `0` type, `1` ctor, `2` lift, `3` ind, `4` sound; `cv` an `EREC` constant value);
`pin_at`, `erec_ci`, `ind_block_to_erec`; this lane's `block_shape`, `block_is_rec`,
`block_caps_at`, `ind_info_rec`, `ctor_info_rec`, `block_shape_declared`, `block_shape_all_ctors`,
`block_shape_lps`, `struct_proj_bodies`, `rec_info_rec`.
-/

namespace L.Ind

open L.Arena
open L.Front (DECL)

/-! ## The pushes -/

/-- `ifenv_push_all(vis, L.off, L.len)`: push a list of records, head first. -/
-- con-ron: ConRon/Arena/Install.lean:36-40 ConRon.Arena.IFEnv.pushAll
@[no_expose, l_impl ConRon.Arena.IFEnv.pushAll]
def ifenvPushAll : FunDecl := lfn (vis, o, l) locals (v, r) {
  if l == 0 { return vis };
  v := call env_push(vis, IW.u64[o]);
  r := call ifenv_push_all(v, o + 1, l - 1);
  return r
}

/-- `ifenv_push_tables(Q.off, Q.len)`: the tables, pushed in order. -/
-- con-ron: ConRon/Arena/Install.lean:42-46 ConRon.Arena.IFEnv.pushTables
@[no_expose, l_impl ConRon.Arena.IFEnv.pushTables]
def ifenvPushTables : FunDecl := lfn (o, l) locals (u) {
  if l == 0 { return 0 };
  u := call env_push_table(IW.u64[o]);
  u := call ifenv_push_tables(o + 1, l - 1);
  return 0
}

/-- `ifenv_push_delta(vis, L.off, L.len, Q.off, Q.len)`: the environment with a declaration's
constants and tables pushed, each list oldest first: the constants, then the tables. -/
-- con-ron: ConRon/Arena/Install.lean:48-53 ConRon.Arena.IFEnv.pushDelta
@[no_expose, l_impl ConRon.Arena.IFEnv.pushDelta]
def ifenvPushDelta : FunDecl := lfn (vis, lo, ll, qo, ql) locals (v, u) {
  v := call ifenv_push_all(vis, lo, ll);
  u := call ifenv_push_tables(qo, ql);
  return v
}

/-! ## A block's constants -/

/-- `block_formers_go(p, isRec, d.off, d.len, i)`: the formers as declared from member `i` on,
each `.indInfo` with its capability record at `isRec`. -/
-- con-ron: ConRon/Arena/Install.lean:55-59 ConRon.Arena.blockFormers
@[no_expose, l_impl ConRon.Arena.blockFormers]
def blockFormersGo : FunDecl := lfn (p, isRec, dO, dL, i) locals (caps, q, ro, rl, o, l) {
  if dL == 0 { return (0, 0) };
  caps := call block_caps_at(p, i, isRec);
  q := call ind_info_rec(IW.u64[dO], caps);
  (ro, rl) := call block_formers_go(p, isRec, dO + 1, dL - 1, i + 1);
  (o, l) := call sl_cons(q, ro, rl);
  return (o, l)
}

/-- `block_formers(p, isRec)`: the formers, in block order, as declared, with the capabilities
their block gives them. -/
-- con-ron: ConRon/Arena/Install.lean:55-59 ConRon.Arena.blockFormers
@[no_expose, l_impl ConRon.Arena.blockFormers]
def blockFormers : FunDecl := lfn (p, isRec) locals (dO, dL, o, l) {
  (dO, dL) := call block_shape_declared(p);
  (o, l) := call block_formers_go(p, isRec, dO, dL, 0);
  return (o, l)
}

/-- `block_ctors_go(nP, c.off, c.len)`: `.ctorInfo c.1 nP c.2` for each `[cv, nF]`. -/
-- con-ron: ConRon/Arena/Install.lean:61-64 ConRon.Arena.blockCtors
@[no_expose, l_impl ConRon.Arena.blockCtors]
def blockCtorsGo : FunDecl := lfn (nP, co, cl) locals (c, q, ro, rl, o, l) {
  if cl == 0 { return (0, 0) };
  c := IW.u64[co];
  q := call ctor_info_rec(IW.u64[c], nP, IW.u64[c + 1]);
  (ro, rl) := call block_ctors_go(nP, co + 1, cl - 1);
  (o, l) := call sl_cons(q, ro, rl);
  return (o, l)
}

/-- `block_ctors(p)`: the constructors of every member, as declared, in block order. -/
-- con-ron: ConRon/Arena/Install.lean:61-64 ConRon.Arena.blockCtors
@[no_expose, l_impl ConRon.Arena.blockCtors]
def blockCtors : FunDecl := lfn (p) locals (co, cl, o, l) {
  (co, cl) := call block_shape_all_ctors(p);
  (o, l) := call block_ctors_go(IW.u64[p + 4], co, cl);
  return (o, l)
}

/-- `expr_drop_vars(n, e)`: `n` variables below a term's own, which do not occur in it, dropped:
each instantiated at `Sort 0`. -/
-- con-ron: ConRon/Arena/Install.lean:66-73 ConRon.Arena.exprDropVars
@[no_expose, l_impl ConRon.Arena.exprDropVars]
def exprDropVars : FunDecl := lfn (n, e) locals (z, s0, e2, r) {
  if n == 0 { return e };
  z := call pin_word(53);
  s0 := call intern_sort(z);
  if 4294967296 <= s0 { abort };
  e2 := call instantiate1_fast(⟪CWF⟫, e, s0, 0);
  r := call expr_drop_vars(n - 1, e2);
  return r
}

/-- `expr_drop_vars_list(nI, a.off, a.len)`: `as.mapM (exprDropVars nI)`, a fresh `IW` slice. -/
-- con-ron: ConRon/Arena/Install.lean:75-102 ConRon.Arena.recFire
@[no_expose, l_impl ConRon.Arena.recFire]
def exprDropVarsList : FunDecl := lfn (nI, ao, al) locals (x, ro, rl, o, l) {
  if al == 0 { return (0, 0) };
  x := call expr_drop_vars(nI, IW.u64[ao]);
  (ro, rl) := call expr_drop_vars_list(nI, ao + 1, al - 1);
  (o, l) := call sl_cons(x, ro, rl);
  return (o, l)
}

/-- `rec_fire(p, rc)`: how a recursor's rules fire, `(kind, lvls.off, lvls.len, pins.off,
pins.len)` (`IW` slices): `.plain` (kind `0`) at a member major; at a major outside the block,
`.nested` (kind `1`) at the levels and parameters of the major's container, read off the major's
domain (its arguments ending in the `mI - rP` index variables, the parameters moved from under
the index binders to the rule prefix). -/
-- con-ron: ConRon/Arena/Install.lean:75-102 ConRon.Arena.recFire
@[no_expose, l_impl ConRon.Arena.recFire]
def recFire : FunDecl := lfn (p, rc) locals
    (ok, bo, bl, rest, g, dom, b, z, hd, x, us, lo, ll, ao, al, nI, po, pl) {
  if IW.u64[rc + 3] < IW.u64[p + 1] { return (0, 0, 0, 0, 0) };
  (ok, bo, bl, rest) := call strip_pis(IW.u64[rc + 2], EREC⦃IW.u64[rc] + 3⦄);
  if ok == 0 { return (0, 0, 0, 0, 0) };
  if ⟦rest⟧.tag != 6 { return (0, 0, 0, 0, 0) };
  (g, dom, b, z) := call e_view(rest);
  hd := call get_app_fn_f(⟪CWF⟫, dom);
  if ⟦hd⟧.tag != 3 { return (0, 0, 0, 0, 0) };
  (g, x, us, z) := call e_view(hd);
  (lo, ll) := call view_ls(us);
  (ao, al) := call get_app_args_f(⟪CWF⟫, dom);
  nI := IW.u64[rc + 2] - IW.u64[rc + 1];
  if IW.u64[rc + 2] < IW.u64[rc + 1] { nI := 0 };
  if al < nI { al := 0 } else { al := al - nI };
  (po, pl) := call expr_drop_vars_list(nI, ao, al);
  return (1, lo, ll, po, pl)
}

/-- `rules_refire(d, s, cnt, kind, lvls.off, lvls.len, pins.off, pins.len)`: the `cnt` rules of the
`EREC` run at `s` copied to the run at `d`, each with the given fire (`{ · with fire := f }`; the
fire's slices in `EREC`). -/
-- con-ron: ConRon/Arena/Install.lean:104-112 ConRon.Arena.blockRecs
@[no_expose, l_impl ConRon.Arena.blockRecs]
def rulesRefire : FunDecl := lfn (d, s, cnt, kind, lo, ll, po, pl) locals (ez, u) {
  if cnt == 0 { return 0 };
  ez := call erec_put(d, EREC⦃s⦄);
  ez := call erec_put(d + 1, EREC⦃s + 1⦄);
  ez := call erec_put(d + 2, 0);
  ez := call erec_put(d + 3, kind);
  ez := call erec_put(d + 4, lo);
  ez := call erec_put(d + 5, ll);
  ez := call erec_put(d + 6, po);
  ez := call erec_put(d + 7, pl);
  ez := call erec_put(d + 8, EREC⦃s + 8⦄);
  ez := call erec_put(d + 9, 0);
  ez := call erec_put(d + 10, 0);
  u := call rules_refire(d + 11, s + 11, cnt - 1, kind, lo, ll, po, pl);
  return 0
}

/-- `block_rec(p, rc)`: one recursor's record — the stream's record with its rules' firing mode
(`rec_fire`, its slices copied into `EREC`). -/
-- con-ron: ConRon/Arena/Install.lean:104-112 ConRon.Arena.blockRecs
@[no_expose, l_impl ConRon.Arena.blockRecs]
def blockRec : FunDecl := lfn (p, rc) locals
    (k, lo, ll, po, pl, elo, ell, epo, epl, cnt, run, u, q) {
  (k, lo, ll, po, pl) := call rec_fire(p, rc);
  (elo, ell) := call er_from_iw(lo, ll);
  (epo, epl) := call er_from_iw(po, pl);
  cnt := IW.u64[rc + 5];
  if 4294967296 <= cnt { abort };
  run := call erec_alloc(11 * cnt);
  u := call rules_refire(run, IW.u64[rc + 4], cnt, k, elo, ell, epo, epl);
  q := call rec_info_rec(IW.u64[rc], IW.u64[rc + 2], IW.u64[rc + 1], IW.u64[rc + 6], run, cnt);
  return q
}

/-- `block_recs(p, recs.off, recs.len)`: the recursors, in block order: each record with its rules'
firing mode. -/
-- con-ron: ConRon/Arena/Install.lean:104-112 ConRon.Arena.blockRecs
@[no_expose, l_impl ConRon.Arena.blockRecs]
def blockRecs : FunDecl := lfn (p, ro, rl) locals (q, to, tl, o, l) {
  if rl == 0 { return (0, 0) };
  q := call block_rec(p, IW.u64[ro]);
  (to, tl) := call block_recs(p, ro + 1, rl - 1);
  (o, l) := call sl_cons(q, to, tl);
  return (o, l)
}

/-- `block_table(p, ms)`: a structure-like member's table record (13 words: kind `6`, `0`,
`structName`, lps, `numParams`, `ctor`, `numFields`, `0`, bodies, `0`, `0`; its lists copied into
`EREC`), `(1, q)`; `(0, 0)` at a member that is not structure-like; `(2, 0)` where its
constructor's type is too short for the bodies (the twin's `none`). -/
-- con-ron: ConRon/Arena/Install.lean:114-130 ConRon.Arena.blockTables
@[no_expose, l_impl ConRon.Arena.blockTables]
def blockTable : FunDecl := lfn (p, ms) locals
    (c, cv, T, ok, bo, bl, lo, ll, elo, ell, ebo, ebl, q, ez) {
  if IW.u64[ms + 3] != 1 { return (0, 0) };
  if IW.u64[ms + 1] != 0 { return (0, 0) };
  c := IW.u64[IW.u64[ms + 2]];
  cv := IW.u64[c];
  T := EREC⦃IW.u64[ms + 4]⦄;
  (ok, bo, bl) := call struct_proj_bodies(T, IW.u64[p + 4], IW.u64[c + 1], EREC⦃cv + 3⦄);
  if ok == 0 { return (2, 0) };
  (lo, ll) := call block_shape_lps(p);
  (elo, ell) := call er_from_iw(lo, ll);
  (ebo, ebl) := call er_from_iw(bo, bl);
  q := call erec_alloc(13);
  ez := call erec_put(q, 6);
  ez := call erec_put(q + 1, 0);
  ez := call erec_put(q + 2, T);
  ez := call erec_put(q + 3, elo);
  ez := call erec_put(q + 4, ell);
  ez := call erec_put(q + 5, IW.u64[p + 4]);
  ez := call erec_put(q + 6, EREC⦃cv⦄);
  ez := call erec_put(q + 7, IW.u64[c + 1]);
  ez := call erec_put(q + 8, 0);
  ez := call erec_put(q + 9, ebo);
  ez := call erec_put(q + 10, ebl);
  ez := call erec_put(q + 11, 0);
  ez := call erec_put(q + 12, 0);
  return (1, q)
}

/-- `block_tables(p, ms.off, ms.len)`: the projection tables, in block order, one per
structure-like member: `(1, off, len)`, or `(0, 0, 0)` where a structure-like member's constructor
type is too short to read its bodies (the twin's `none`; the rest is not read). -/
-- con-ron: ConRon/Arena/Install.lean:114-130 ConRon.Arena.blockTables
@[no_expose, l_impl ConRon.Arena.blockTables]
def blockTables : FunDecl := lfn (p, mo, ml) locals (st, q, ok, to, tl, o, l) {
  if ml == 0 { return (1, 0, 0) };
  (st, q) := call block_table(p, IW.u64[mo]);
  if st == 2 { return (0, 0, 0) };
  (ok, to, tl) := call block_tables(p, mo + 1, ml - 1);
  if st == 0 { return (ok, to, tl) };
  if ok == 0 { return (0, 0, 0) };
  (o, l) := call sl_cons(q, to, tl);
  return (1, o, l)
}

/-- `block_constants(p)`: the block's constants, in push order: the formers (at official's
`is_rec`, `block_is_rec`), the constructors, the recursors. -/
-- con-ron: ConRon/Arena/Install.lean:132-138 ConRon.Arena.blockConstants
@[no_expose, l_impl ConRon.Arena.blockConstants]
def blockConstants : FunDecl := lfn (p) locals (isRec, fo, fl, co, cl, ro, rl, ao, al, bo, bl) {
  isRec := call block_is_rec(p);
  (fo, fl) := call block_formers(p, isRec);
  (co, cl) := call block_ctors(p);
  (ro, rl) := call block_recs(p, IW.u64[p + 2], IW.u64[p + 3]);
  (ao, al) := call sl_append(fo, fl, co, cl);
  (bo, bl) := call sl_append(ao, al, ro, rl);
  return (bo, bl)
}

/-! ## A declaration's constants and tables -/

/-- `decl_constants_axiom(q)`: the `.axiomDecl` arm (`q` the record's `axiomInfo`): `Quot.sound`
installs its pin at the record's names, `sorryAx` nothing, any other axiom itself. -/
-- con-ron: ConRon/Arena/Install.lean:140-146 ConRon.Arena.declConstantsAxiom
@[no_expose, l_impl ConRon.Arena.declConstantsAxiom]
def declConstantsAxiom : FunDecl := lfn (q) locals (qs, sa, r, o, l) {
  qs := call pin_at(4);
  if EREC⦃q + 1⦄ == qs {
    r := call quot_at(4, q + 1);
    (o, l) := call sl_new1(r);
    return (o, l)
  };
  sa := call pin_at(13);
  if EREC⦃q + 1⦄ == sa { return (0, 0) };
  (o, l) := call sl_new1(q);
  return (o, l)
}

/-- `decl_constants_ind(bo, bl, nP)`: the `.indDecl` arm: a block with a pinned block's names
installs the pin at the names the record declares, a block the recogniser reads its constants,
any other nothing (it declines). -/
-- con-ron: ConRon/Arena/Install.lean:148-162 ConRon.Arena.declConstants
-- con-ron: CHANGED since 01ecb31c — below `ConRon.Arena.declConstants`, `ConRon.Arena.readBlock` changed; re-check the L code and its proofs, then delete this line
-- con-ron: CHANGED since 01ecb31c — `ConRon.Arena.declConstants` changed; re-check the L code and its proofs, then delete this line
@[no_expose, l_impl ConRon.Arena.declConstants]
def declConstantsInd : FunDecl := lfn (bo, bl, nP) locals (hit, kind, o, l, ok, p) {
  (hit, kind) := call basis_name_hit(bo, bl);
  if hit != 0 {
    (o, l) := call basis_at_block(kind, bo, bl);
    return (o, l)
  };
  (ok, p) := call block_shape(nP, bo, bl);
  if ok == 0 { return (0, 0) };
  (o, l) := call block_constants(p);
  return (o, l)
}

/-- `decl_constants(i)`: the constants `DECL` record `i` installs, in push order (an `IW` slice of
`EREC` constant records). -/
-- con-ron: ConRon/Arena/Install.lean:148-162 ConRon.Arena.declConstants
-- con-ron: CHANGED since 01ecb31c — below `ConRon.Arena.declConstants`, `ConRon.Arena.readBlock` changed; re-check the L code and its proofs, then delete this line
-- con-ron: CHANGED since 01ecb31c — `ConRon.Arena.declConstants` changed; re-check the L code and its proofs, then delete this line
@[no_expose, l_impl ConRon.Arena.declConstants]
def declConstants : FunDecl := lfn (i) locals (k, q, w, slot, r, bo, bl, o, l) {
  k := DECL.u64[1 + 8 * i];
  if k == 2 { q := call erec_ci(i, 1); (o, l) := call sl_new1(q); return (o, l) };
  if k == 3 { q := call erec_ci(i, 2); (o, l) := call sl_new1(q); return (o, l) };
  if k == 4 { q := call erec_ci(i, 0); (o, l) := call sl_new1(q); return (o, l) };
  if k == 1 {
    q := call erec_ci(i, 0);
    (o, l) := call decl_constants_axiom(q);
    return (o, l)
  };
  if k == 5 {
    q := call erec_ci(i, 0);
    w := DECL.u64[7 + 8 * i];
    slot := 3;
    if w == 1 { slot := 0 } else if w == 2 { slot := 1 } else if w == 3 { slot := 2 };
    r := call quot_at(slot, q + 1);
    (o, l) := call sl_new1(r);
    return (o, l)
  };
  if k == 6 {
    (bo, bl) := call ind_block_to_erec(i);
    (o, l) := call decl_constants_ind(bo, bl, DECL.u64[5 + 8 * i]);
    return (o, l)
  };
  abort
}

/-- `decl_tables(i)`: the projection tables `DECL` record `i` installs: those of a recognised
inductive block (a pinned block's names install none); none for any other record. -/
-- con-ron: ConRon/Arena/Install.lean:164-176 ConRon.Arena.declTables
-- con-ron: CHANGED since 01ecb31c — below `ConRon.Arena.declTables`, `ConRon.Arena.readBlock` changed; re-check the L code and its proofs, then delete this line
-- con-ron: CHANGED since 01ecb31c — `ConRon.Arena.declTables` changed; re-check the L code and its proofs, then delete this line
@[no_expose, l_impl ConRon.Arena.declTables]
def declTables : FunDecl := lfn (i) locals (bo, bl, hit, kind, ok, p, o, l) {
  if DECL.u64[1 + 8 * i] != 6 { return (0, 0) };
  (bo, bl) := call ind_block_to_erec(i);
  (hit, kind) := call basis_name_hit(bo, bl);
  if hit != 0 { return (0, 0) };
  (ok, p) := call block_shape(DECL.u64[5 + 8 * i], bo, bl);
  if ok == 0 { return (0, 0) };
  (o, l) := call block_tables(p, IW.u64[p], IW.u64[p + 1]);
  return (o, l)
}

/-- This module's functions. -/
def indDeclConstsFns : Prog :=
  [("ifenv_push_all", ifenvPushAll), ("ifenv_push_tables", ifenvPushTables),
   ("ifenv_push_delta", ifenvPushDelta), ("block_formers_go", blockFormersGo),
   ("block_formers", blockFormers), ("block_ctors_go", blockCtorsGo), ("block_ctors", blockCtors),
   ("expr_drop_vars", exprDropVars), ("expr_drop_vars_list", exprDropVarsList),
   ("rec_fire", recFire), ("rules_refire", rulesRefire), ("block_rec", blockRec),
   ("block_recs", blockRecs), ("block_table", blockTable), ("block_tables", blockTables),
   ("block_constants", blockConstants), ("decl_constants_axiom", declConstantsAxiom),
   ("decl_constants_ind", declConstantsInd), ("decl_constants", declConstants),
   ("decl_tables", declTables)]

/-- Stubs for the functions of OTHER modules this module calls. -/
def indDeclConstsForeign : Prog :=
  [("block_caps_at", stub 3), ("ind_info_rec", stub 2), ("ctor_info_rec", stub 3),
   ("block_shape_declared", stub 1), ("block_shape_all_ctors", stub 1), ("block_shape_lps", stub 1),
   ("struct_proj_bodies", stub 4), ("rec_info_rec", stub 6), ("er_from_iw", stub 2),
   ("block_is_rec", stub 1), ("block_shape", stub 3), ("basis_name_hit", stub 2),
   ("basis_at_block", stub 3), ("quot_at", stub 2), ("erec_ci", stub 2),
   ("ind_block_to_erec", stub 1), ("env_push_table", stub 1)]

-- `ifenv_push_delta` of two empty lists: the view unchanged.
#guard
  match run (indDeclConstsFns ++ libFns ++ stubFns ++ masterFns ++ indDeclConstsForeign) 100
      "ifenv_push_delta" [7, 0, 0, 0, 0] testMem with
  | .ok ([7], _) => true
  | _ => false

end L.Ind
