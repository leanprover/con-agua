module

public import ConAgua.Arena.IndIface
meta import ConAgua.Arena.IndIface

@[expose] public section

/-!
# The inductive block's check, at k members (lane `induct`, module `IndInstall`)

The L translation of `vendor/con-ron/ConRon/Arena/Inductives/BlockInstall.lean` and
`.../BlockTail.lean`: the capability record per member, official's `is_rec`, the formers' stage
(telescopes, the two agreements, the cons as declared), the constructors' stage, the positivity
check on the stored constructors, the index sorts and the constructors' cons
(`BlockInstall.lean`), then the members reduced to their telescopes (`reduceMember(s)`), one pass
over formers, constructors and classes, the generated recursors, the stream's recursors and K
flags against them (at the generated family pushed in place and popped, `consBlockRecsTemp`), the
projection tables' checks, and the block's install pushed onto the constructors' environment
(`checkBlock`, `BlockTail.lean`). One L function per twin function (more for the bigger ones),
each tagged `@[l_impl …]`.

**Foreign callees** (owned by other modules, named by the project's naming rule; each is a
`stub` in `indInstallForeign`, closing this module's program on its own):

* `IndSum`: `check_sum_tele(n, cvTa0) → (cvTa, s)`; `check_sum_ctors(vis0, vis, T, lps.off,
  lps.len, nP, nIdx, resSort, isProp, large, cvTa, ctors.off, ctors.len)`; `cons_sum_ctors(nP, T,
  ctors.off, ctors.len, vis) → vis'`;
  `check_struct_field_sorts_i(vis, isProp, large, s, nP, fvs.off, fvs.len, idx.off, idx.len, j)`;
  `param_levels(lps.off, lps.len) → lvls`; `check_struct_proj_table(T, lps.off, lps.len, nP, nF,
  cvCa, vis)`.
* `IndPos`/`IndPos2`: `mentions_any_const`, `nest_holes(ctx) → (ok, off, len)`, `nest_ctx_hi_at`,
  `nest_uniform`, `nest_root`, `nest_seeds`, `reduced_former(vis, cv, n) → cv'`.
* `IndParts`: `block_shape_with_sort(p, s)`, `block_shape_with_members(p, ms.off, ms.len)`,
  `block_shape_member_names`, `block_shape_lps`, `block_shape_n_idxs`, `block_shape_formers`,
  `block_shape_declared`, `block_shape_member_ctors` (a list of pointers to the members' ctor-slice
  headers), `block_shape_ctor_groups` (the member records, read as the groups), `block_shape_all_ctors`.
* `RecGen`: `check_block_classes(vis, p, params.off, params.len) → (rd, ms.off, ms.len)`,
  `class_seeds`, `gen_rec_check(vis, p, nested, params.off, params.len, tbl.off, tbl.len, rd,
  ms.off, ms.len, block.off, block.len) → (vis', out.off, out.len)`, `gen_rec_check_pop_all`.
* `RecCheck`: `block_nested_bit`, `block_rec_infos_tf(p, m, out.off, out.len) → (infos.off,
  infos.len)`.
* `IndStream`: `stream_k_check(p, recs.off, recs.len, out.off, out.len)`,
  `stream_recs_check(vis, recs.off, recs.len, out.off, out.len)`.
* `IndDeclConsts`: `block_recs(p, recs.off, recs.len)`, `block_tables(p, ms.off, ms.len)`,
  `ifenv_push_delta(vis, L.off, L.len, Q.off, Q.len) → vis'`.
* the core tier: `former_z(ty) → (w, o, c)` (`Core.lean`'s `formerZ`), `former_def_headed(ty)` (`Core.lean`'s `formerDefHeaded`), the declarations':
  `check_constant_val(vis, cv, allowOp)`.
-/

namespace L.Ind

open L.Arena

/-! ## `blockCapsAt`: one member's `IIndCaps` (`decCaps`) -/

/-- `block_caps_ctor_names(o, l)`: the ctor-name list of a `(cv, nF)` pointer slice `(o, l)`, built
fresh in `IW`. -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:57-84 ConRon.Arena.blockCapsAt
@[no_expose, l_impl ConRon.Arena.blockCapsAt]
def blockCapsCtorNames : FunDecl := lfn (o, l) locals (q, u) {
  q := call iw_alloc(l);
  u := call member_names_copy(q, o, l);
  return (q, l)
}

/-- `block_caps_at_er_copy(o, l)`: an `IW` slice copied into fresh `EREC` words (the reverse of
`er_to_iw`), for `IIndCaps`'s `all`/`ctors` fields (both EREC slices). -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:57-84 ConRon.Arena.blockCapsAt
@[no_expose, l_impl ConRon.Arena.blockCapsAt]
def blockCapsAtErCopy : FunDecl := lfn (o, l) locals (q, u) {
  q := call erec_alloc(l);
  u := call block_caps_at_er_copy_go(q, o, l);
  return (q, l)
}

/-- `block_caps_at_er_copy_go(d, s, l)`: `EREC[d + j] := IW[s + j]` for `j < l`, recursively. -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:57-84 ConRon.Arena.blockCapsAt
@[no_expose, l_impl ConRon.Arena.blockCapsAt]
def blockCapsAtErCopyGo : FunDecl := lfn (d, s, l) locals (u, ez) {
  if l == 0 { return 0 };
  ez := call erec_put(d, IW.u64[s]);
  u := call block_caps_at_er_copy_go(d + 1, s + 1, l - 1);
  return 0
}

/-- `member_never_zero(p, mi)`: `memberNeverZero` — whether member `mi`'s former, as declared
(member word `4`), ends in a sort that is never zero: `former_z`'s datum is `never` (its first word
`0`); `0` past the members (the default member's type ends in no sort). The level heap's top
`CTL[192]`, which `former_z` leaves raised, is put back. -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:47-55 ConRon.Arena.memberNeverZero
@[no_expose, l_impl ConRon.Arena.memberNeverZero]
def memberNeverZero : FunDecl := lfn (p, mi) locals (ms, t0, w, o, c) {
  if IW.u64[p + 1] <= mi { return 0 };
  ms := IW.u64[IW.u64[p] + mi];
  t0 := CTL.u64[192];
  (w, o, c) := call former_z(EREC⦃IW.u64[ms + 4] + ⟪CV.type⟫⦄);
  CTL.u64[192] := t0;
  return u64(w == 0)
}

/-- `block_caps_at(p, mi, is_rec)`: member `mi`'s `IIndCaps`, a fresh `IW` record of `Caps.size`
words (the `EREC` layout of `decCaps`, `RecLayout/Caps.lean`; `ind_info_rec` copies it into the
former's record). First the member's never-zero fact (`member_never_zero`), then: at exactly one
constructor `eta` (index-free, the block not recursive: official's `is_non_rec_structure`); else
its default `0`. At every member `all` (the member names, copied into `EREC`), `nparams`, `nIdx`
(`0` past the members), the member's ctor names (copied into `EREC`) and `neverZero`. Every field
is computed first, the record written last (`block_caps_fin`, field by field). -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:57-84 ConRon.Arena.blockCapsAt
@[no_expose, l_impl ConRon.Arena.blockCapsAt]
def blockCapsAt : FunDecl := lfn (p, mi, isRec) locals (nz, coff, clen, one, ms, nIdx, w0, caps) {
  nz := call member_never_zero(p, mi);
  (coff, clen, one, ms, nIdx) := call block_caps_head(p, mi);
  if one == 1 {
    w0 := call block_caps_one(ms, isRec)
  } else {
    w0 := 0
  };
  caps := call block_caps_fin(p, coff, clen, w0, nIdx, nz);
  return caps
}

/-- `block_caps_fin(p, coff, clen, w0, nIdx, nz)`: `blockCapsAt`'s record — the member names and
the ctor names copied into `EREC`, then a fresh record of `Caps.size` words at the pool top, its
fields written by name (words no field names are left as `iw_alloc` gives them). -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:57-84 ConRon.Arena.blockCapsAt
@[no_expose, l_impl ConRon.Arena.blockCapsAt]
def blockCapsFin : FunDecl := lfn (p, coff, clen, w0, nIdx, nz) locals
    (namesO, namesL, allQ, allL, ctNO, ctNL, ctQ, ctL, np, caps) {
  (namesO, namesL) := call block_shape_member_names(p);
  (allQ, allL) := call block_caps_at_er_copy(namesO, namesL);
  (ctNO, ctNL) := call block_caps_ctor_names(coff, clen);
  (ctQ, ctL) := call block_caps_at_er_copy(ctNO, ctNL);
  np := IW.u64[p + 4];
  caps := call iw_alloc(⟪Caps.size⟫);
  IW.u64[caps + ⟪Caps.eta⟫] := w0;
  IW.u64[caps + ⟪Caps.nIdx⟫] := nIdx;
  IW.u64[caps + ⟪Caps.neverZero⟫] := nz;
  IW.u64[caps + ⟪Caps.allOff⟫] := allQ;
  IW.u64[caps + ⟪Caps.allLen⟫] := allL;
  IW.u64[caps + ⟪Caps.nparams⟫] := np;
  IW.u64[caps + ⟪Caps.ctorsOff⟫] := ctQ;
  IW.u64[caps + ⟪Caps.ctorsLen⟫] := ctL;
  return caps
}

/-- `block_caps_head(p, mi)`: member `mi`'s constructor slice `(coff, clen)` (`(0, 0)` past the
members, and at no constructor), whether it has exactly one constructor, its record pointer, and
its index count (`0` past the members: the default member's). -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:57-84 ConRon.Arena.blockCapsAt
@[no_expose, l_impl ConRon.Arena.blockCapsAt]
def blockCapsHead : FunDecl := lfn (p, mi) locals (ms) {
  if IW.u64[p + 1] <= mi { return (0, 0, 0, 0, 0) };
  ms := IW.u64[IW.u64[p] + mi];
  if IW.u64[ms + 3] == 0 { return (0, 0, 0, ms, IW.u64[ms + 1]) };
  return (IW.u64[ms + 2], IW.u64[ms + 3], u64(IW.u64[ms + 3] == 1), ms, IW.u64[ms + 1])
}

/-- `block_caps_one(ms, is_rec)`: the one-constructor field `eta` (index-free, the block not
recursive: official's `is_non_rec_structure`). -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:57-84 ConRon.Arena.blockCapsAt
@[no_expose, l_impl ConRon.Arena.blockCapsAt]
def blockCapsOne : FunDecl := lfn (ms, isRec) locals () {
  return u64(IW.u64[ms + 1] == 0) & u64(isRec == 0)
}

/-! ## `piDomsMentionAny`, `blockIsRec`: official's `is_rec` -/

/-- `pi_doms_mention_any(names.off, names.len, fuel, e)`: does some binder domain of the
syntactic `∀`-telescope of `e` mention one of `names`? Fueled (recurses on a handle). -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:86-99 ConRon.Arena.piDomsMentionAny
@[no_expose, l_impl ConRon.Arena.piDomsMentionAny]
def piDomsMentionAny : FunDecl := lfn (namesO, namesL, fuel, e) locals (g, x, y, z, b, r) {
  if fuel == 0 { abort };
  (g, x, y, z) := call e_view(e);
  if g != 6 { return 0 };
  b := call mentions_any_const(namesO, namesL, x);
  if b != 0 { return 1 };
  r := call pi_doms_mention_any(namesO, namesL, fuel - 1, y);
  return r
}

/-- `block_is_rec_member(names.off, names.len, coff, clen)`: does some DECLARED constructor type of
the member (its ctor slice) mention one of `names` in some binder domain of its telescope? -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:101-107 ConRon.Arena.blockIsRec
@[no_expose, l_impl ConRon.Arena.blockIsRec]
def blockIsRecMember : FunDecl := lfn (namesO, namesL, coff, clen) locals (b, r) {
  if clen == 0 { return 0 };
  b := call pi_doms_mention_any(namesO, namesL, ⟪CWF⟫, EREC⦃IW.u64[IW.u64[coff]] + ⟪CV.type⟫⦄);
  if b != 0 { return 1 };
  r := call block_is_rec_member(namesO, namesL, coff + 1, clen - 1);
  return r
}

/-- `block_is_rec_go(names.off, names.len, moff, mlen)`: the members' `anyM`, in order. -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:101-107 ConRon.Arena.blockIsRec
@[no_expose, l_impl ConRon.Arena.blockIsRec]
def blockIsRecGo : FunDecl := lfn (namesO, namesL, moff, mlen) locals (ms, b, r) {
  if mlen == 0 { return 0 };
  ms := IW.u64[moff];
  b := call block_is_rec_member(namesO, namesL, IW.u64[ms + 2], IW.u64[ms + 3]);
  if b != 0 { return 1 };
  r := call block_is_rec_go(namesO, namesL, moff + 1, mlen - 1);
  return r
}

/-- `block_is_rec(p)`: official's `is_rec` — some member occurs in some binder domain of some
declared constructor's telescope. -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:101-107 ConRon.Arena.blockIsRec
@[no_expose, l_impl ConRon.Arena.blockIsRec]
def blockIsRec : FunDecl := lfn (p) locals (namesO, namesL, b) {
  (namesO, namesL) := call block_shape_member_names(p);
  b := call block_is_rec_go(namesO, namesL, IW.u64[p], IW.u64[p + 1]);
  return b
}

/-! ## Stage 1: the formers -/

/-- `check_block_tele(vis, nP, ms)`: one member's type former (at its telescope) — the constant
check, the telescope and the result sort (`nP + nIdx` past `2^64` a capacity abort). -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:111-124 ConRon.Arena.checkBlockTele
@[no_expose, l_impl ConRon.Arena.checkBlockTele]
def checkBlockTele : FunDecl := lfn (vis, nP, ms) locals
    (cvT, z, cvTa, s, ok, bsOff, bsLen, body, srt, k) {
  cvT := IW.u64[ms];
  k := nP + IW.u64[ms + 1];
  if k < nP { abort };
  z := call check_constant_val(vis, cvT, 0, 0, 0);
  (cvTa, s) := call check_sum_tele(k, cvT);
  (ok, bsOff, bsLen, body) := call strip_pis(k, EREC⦃cvTa + ⟪CV.type⟫⦄);
  if ok == 0 { abort };
  srt := call intern_sort(s);
  if body == srt { return (cvTa, s) };
  abort
}

/-- `check_block_teles(vis, nP, ms.off, ms.len)`: the members' type formers, in block order, each
a pointer to `[cvTa, s]`; recursion as the twin's, each record consed onto the rest's slice
(`sl_cons`, a copy per element: docs/deviations.md D18). -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:126-135 ConRon.Arena.checkBlockTeles
@[no_expose, l_impl ConRon.Arena.checkBlockTeles]
def checkBlockTeles : FunDecl := lfn (vis, nP, msOff, msLen) locals (cvTa, s, rp, ro, rl, o, l) {
  if msLen == 0 { return (0, 0) };
  (cvTa, s) := call check_block_tele(vis, nP, IW.u64[msOff]);
  rp := call rec2(cvTa, s);
  (ro, rl) := call check_block_teles(vis, nP, msOff + 1, msLen - 1);
  (o, l) := call sl_cons(rp, ro, rl);
  return (o, l)
}

/-- `check_block_doms_at(vis, off, fvs.off, fvs.len, doms.off, doms.len, j)`: binder `j - 1`'s
domain against member 0's, defeq at depth `off + j - 1`, then recurses down to `j - 1` — the
last binder to the first, structurally on `j` (as the twin recurses on its `Nat` argument). -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:137-151 ConRon.Arena.checkBlockDomsAt
@[no_expose, l_impl ConRon.Arena.checkBlockDomsAt]
def checkBlockDomsAt : FunDecl := lfn (vis, off, fvsO, fvsL, domsO, domsL, j) locals
    (j1, a, b, aT, eq, u) {
  if j == 0 { return 0 };
  j1 := j - 1;
  if fvsL <= j1 { abort };
  a := IW.u64[fvsO + j1];
  if domsL <= j1 { abort };
  b := IW.u64[domsO + j1];
  aT := call fvar_type_d(a);
  eq := call is_def_eq_core(vis, off + j1, aT, b);
  if eq == 0 { fail R_PARAMETERS_OF_ALL };
  u := call check_block_doms_at(vis, off, fvsO, fvsL, domsO, domsL, j1);
  return u
}

/-- `check_block_agree_one(vis, nP, fvs0.off, fvs0.len, s0, cvTa, s)`: one member's two
agreements against member 0's — the parameter domains (`check_block_doms_at`) and the result
sort. -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:153-172 ConRon.Arena.checkBlockAgree
@[no_expose, l_impl ConRon.Arena.checkBlockAgree]
def checkBlockAgreeOne : FunDecl := lfn (vis, nP, fvs0O, fvs0L, s0, cvTa, s) locals
    (ok, fvsO, fvsL, body, domsO, domsL, u, eq) {
  (ok, fvsO, fvsL, body) := call open_pis_at_fvars_f(nP, EREC⦃cvTa + ⟪CV.type⟫⦄, 0);
  if ok == 0 { fail R_PARAMETERS_OF_ALL };
  if fvsL != fvs0L { fail R_PARAMETERS_OF_ALL };
  (domsO, domsL) := call fvar_type_ds(fvs0O, fvs0L);
  u := call check_block_doms_at(vis, 0, fvsO, fvsL, domsO, domsL, nP);
  eq := call lvl_eq_fueled(s, s0);
  if eq == 0 { fail R_MUTUALLY_INDUCTIVE_TYPES }
}

/-- `check_block_agree(vis, nP, cvTa0, s0, rest.off, rest.len)`: official's two agreements
between member 0 and every other member (`rest`, a slice of pointers to `[cvTa, s]`), by
recursion on `rest` as the twin's. Member 0's telescope is opened once per member, as the twin
does (lane `indproofs`: round 1 opened it always and aborted on `ok0 = 0` where the twin
succeeds; lane `indproofs2`: round 2 opened it once, where the twin's state after the second
opening differs). -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:153-172 ConRon.Arena.checkBlockAgree
@[no_expose, l_impl ConRon.Arena.checkBlockAgree]
def checkBlockAgree : FunDecl := lfn (vis, nP, cvTa0, s0, restO, restL) locals
    (ok0, fvs0O, fvs0L, body0, rp, u) {
  if restL == 0 { return 0 };
  (ok0, fvs0O, fvs0L, body0) := call open_pis_at_fvars_f(nP, EREC⦃cvTa0 + ⟪CV.type⟫⦄, 0);
  if ok0 == 0 { abort };
  rp := IW.u64[restO];
  u := call check_block_agree_one(vis, nP, fvs0O, fvs0L, s0, IW.u64[rp], IW.u64[rp + 1]);
  u := call check_block_agree(vis, nP, cvTa0, s0, restO + 1, restL - 1);
  return 0
}

/-- `cons_block_inds(p1, is_rec, cvs.off, cvs.len, vis, i)`: the formers `cvs` (as declared)
consed, in block order, each with its capability record at `is_rec` (member `i` first), by
recursion as the twin's; the `.indInfo` record (kind `3`, the constant's four words, the
capability record) is `ind_info_rec`'s. Returns the new view. -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:174-183 ConRon.Arena.consBlockInds
@[no_expose, l_impl ConRon.Arena.consBlockInds]
def consBlockInds : FunDecl := lfn (p1, isRec, cvO, cvL, vis, i) locals (caps, rec, v1, v2) {
  if cvL == 0 { return vis };
  caps := call block_caps_at(p1, i, isRec);
  rec := call ind_info_rec(IW.u64[cvO], caps);
  v1 := call env_push(vis, rec);
  v2 := call cons_block_inds(p1, isRec, cvO + 1, cvL - 1, v1, i + 1);
  return v2
}

/-- `ind_info_rec(cv, caps)`: a fresh `.indInfo` record — kind `3` and the constant value at `cv`
copied (`er_put_ci`), then the capability record's `Caps.size` `IW` words at `caps`, copied
to `CI.indCaps` (`block_caps_at_er_copy_go`). -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:174-183 ConRon.Arena.consBlockInds
@[no_expose, l_impl ConRon.Arena.consBlockInds]
def indInfoRec : FunDecl := lfn (cv, caps) locals (q, u) {
  q := call erec_alloc(⟪CI.indSize⟫);
  u := call er_put_ci(q, 3, cv);
  u := call block_caps_at_er_copy_go(q + ⟪CI.indCaps⟫, caps, ⟪Caps.size⟫);
  return q
}

/-- `er_put_ci(q, k, cv)`: a constant record's head at `q` — the kind word `k` and a copy of the
constant value at `cv` (its fields read first, then stored at `q + CI.cv + CV.f`). -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:174-183 ConRon.Arena.consBlockInds
@[no_expose, l_impl ConRon.Arena.consBlockInds]
def erPutCi : FunDecl := lfn (q, k, cv) locals (n, lo, ll, t, ez) {
  n := EREC⦃cv⦄; lo := EREC⦃cv + ⟪CV.lpsOff⟫⦄; ll := EREC⦃cv + ⟪CV.lpsLen⟫⦄;
  t := EREC⦃cv + ⟪CV.type⟫⦄;
  ez := call erec_put(q, k);
  ez := call erec_put(q + ⟪CI.cv⟫, n);
  ez := call erec_put(q + ⟪CI.cv + CV.lpsOff⟫, lo);
  ez := call erec_put(q + ⟪CI.cv + CV.lpsLen⟫, ll);
  ez := call erec_put(q + ⟪CI.cv + CV.type⟫, t);
  return 0
}

/-- `check_block_inds(vis, p, is_rec)`: **stage 1** — the k type formers, checked, agreed and
consed as declared (`block_shape_declared`); returns `(vis', p1)`. -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:185-201 ConRon.Arena.checkBlockInds
@[no_expose, l_impl ConRon.Arena.checkBlockInds]
def checkBlockInds : FunDecl := lfn (vis, p, isRec) locals
    (moff, mlen, ms0, nP, cvTa0, s0, cvsO, cvsL, u, p1, dO, dL, fe1) {
  moff := IW.u64[p]; mlen := IW.u64[p + 1];
  if mlen == 0 { abort };
  ms0 := IW.u64[moff];
  nP := IW.u64[p + 4];
  (cvTa0, s0) := call check_block_tele(vis, nP, ms0);
  (cvsO, cvsL) := call check_block_teles(vis, nP, moff + 1, mlen - 1);
  u := call check_block_agree(vis, nP, cvTa0, s0, cvsO, cvsL);
  p1 := call block_shape_with_sort(p, s0);
  (dO, dL) := call block_shape_declared(p);
  fe1 := call cons_block_inds(p1, isRec, dO, dL, vis, 0);
  return (fe1, p1)
}

/-! ## Stage 1b: the constructors, and the positivity check -/

/-- `block_shape_nest_ctx(p, fvsP.off, fvsP.len)`: the block's positivity context at the
canonical parameter variables `fvsP`, with the members' formers at their telescopes (a pointer to
the 13-word `NestCtx` record). -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:205-214 ConRon.Arena.BlockShape.nestCtx
@[no_expose, l_impl ConRon.Arena.BlockShape.nestCtx]
def blockShapeNestCtx : FunDecl := lfn (p, fvsPO, fvsPL) locals
    (namesO, namesL, lpsO, lpsL, nIdxsO, nIdxsL, lvls, np, srt, fO, fL, q) {
  (namesO, namesL) := call block_shape_member_names(p);
  (lpsO, lpsL) := call block_shape_lps(p);
  (nIdxsO, nIdxsL) := call block_shape_n_idxs(p);
  lvls := call param_levels(lpsO, lpsL);
  np := IW.u64[p + 4];
  srt := IW.u64[p + 6];
  (fO, fL) := call block_shape_formers(p);
  q := call iw_alloc(13);
  IW.u64[q] := namesO; IW.u64[q + 1] := namesL;
  IW.u64[q + 2] := lpsO; IW.u64[q + 3] := lpsL;
  IW.u64[q + 4] := np;
  IW.u64[q + 5] := nIdxsO; IW.u64[q + 6] := nIdxsL;
  IW.u64[q + 7] := fvsPO; IW.u64[q + 8] := fvsPL;
  IW.u64[q + 9] := srt;
  IW.u64[q + 10] := lvls;
  IW.u64[q + 11] := fO; IW.u64[q + 12] := fL;
  return q
}

/-- `check_block_ctors(vis0, vis, p, ms.off, ms.len)`: every member's constructors against the
member's former at its telescope, at the environment holding all the formers; recursion as the
twin's (the block's level parameters read per member, as the twin's `p.lps`). -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:216-226 ConRon.Arena.checkBlockCtors
@[no_expose, l_impl ConRon.Arena.checkBlockCtors]
def checkBlockCtors : FunDecl := lfn (vis0, vis, p, msO, msL) locals (ms, lpsO, lpsL, u) {
  if msL == 0 { return 0 };
  ms := IW.u64[msO];
  (lpsO, lpsL) := call block_shape_lps(p);
  u := call check_sum_ctors(vis0, vis, EREC⦃IW.u64[ms]⦄, lpsO, lpsL, IW.u64[p + 4], IW.u64[ms + 1],
    IW.u64[p + 6], IW.u64[p + 8], IW.u64[p + 7], IW.u64[ms], IW.u64[ms + 2], IW.u64[ms + 3]);
  u := call check_block_ctors(vis0, vis, p, msO + 1, msL - 1);
  return 0
}

/-- `check_abs_ctor_sorts_one(vis, ctx, isProp, nF, tyN, hi)`: one constructor's fields' universes
at the holes. -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:228-248 ConRon.Arena.checkAbsCtorSorts
@[no_expose, l_impl ConRon.Arena.checkAbsCtorSorts]
def checkAbsCtorSortsOne : FunDecl := lfn (vis, ctx, isProp, nF, tyN, hi) locals
    (srt, ok, fvsO, fvsL, body, so) {
  srt := IW.u64[ctx + 9];
  if hi + nF < hi { abort };
  (ok, fvsO, fvsL, body) := call open_pis_at_fvars_f(nF, tyN, hi);
  if ok == 0 { abort };
  so := call check_struct_field_sorts_i(vis, isProp, 0, srt, hi, fvsO, fvsL, 0, 0, nF);
  return 0
}

/-- `check_abs_ctor_sorts(vis, ctx, isProp, c.off, c.len, o.off, o.len)`: the fields' universes at
the holes, pairwise over the constructors `c` (`[cv, nF]` pointers) and their positivity normal
forms `o` (`[k.off, k.len, e]` pointers), stopping at the shorter list; recursion as the
twin's. -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:228-248 ConRon.Arena.checkAbsCtorSorts
@[no_expose, l_impl ConRon.Arena.checkAbsCtorSorts]
def checkAbsCtorSorts : FunDecl := lfn (vis, ctx, isProp, cOff, cLen, oOff, oLen) locals
    (c, o, ok, hi, u) {
  if cLen == 0 { return 0 };
  if oLen == 0 { return 0 };
  c := IW.u64[cOff];
  o := IW.u64[oOff];
  ok := call all_level_params_defined(IW.u64[ctx + 2], IW.u64[ctx + 3], IW.u64[o + 2]);
  if ok == 0 { abort };
  hi := call nest_ctx_hi_at(ctx, 0);
  u := call check_abs_ctor_sorts_one(vis, ctx, isProp, IW.u64[c + 1], IW.u64[o + 2], hi);
  u := call check_abs_ctor_sorts(vis, ctx, isProp, cOff + 1, cLen - 1, oOff + 1, oLen - 1);
  return 0
}

/-- `check_abs_ctor_sorts_all(vis, ctx, isProp, cs.off, cs.len, os.off, os.len)`:
`check_abs_ctor_sorts` on every member's constructors, stopping at the shorter list; recursion as
the twin's. -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:250-259 ConRon.Arena.checkAbsCtorSortsAll
@[no_expose, l_impl ConRon.Arena.checkAbsCtorSortsAll]
def checkAbsCtorSortsAll : FunDecl := lfn (vis, ctx, isProp, csOff, csLen, osOff, osLen) locals
    (cp, op, u) {
  if csLen == 0 { return 0 };
  if osLen == 0 { return 0 };
  cp := IW.u64[csOff];
  op := IW.u64[osOff];
  u := call check_abs_ctor_sorts(vis, ctx, isProp, IW.u64[cp], IW.u64[cp + 1], IW.u64[op], IW.u64[op + 1]);
  u := call check_abs_ctor_sorts_all(vis, ctx, isProp, csOff + 1, csLen - 1, osOff + 1, osLen - 1);
  return 0
}

/-- `block_nest_ctx(p)`: the walk's context — the canonical parameter variables are the first
former's (at its telescope) opened telescope, with the members' holes (the parameters' and
members' counts summing past `2^64` a capacity abort). -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:261-274 ConRon.Arena.blockNestCtx
@[no_expose, l_impl ConRon.Arena.blockNestCtx]
def blockNestCtx : FunDecl := lfn (p) locals
    (fO, fL, cvTa0, ok, pqO, pqL, body, ctx, ok2, hO, hL) {
  (fO, fL) := call block_shape_formers(p);
  if fL == 0 { abort };
  if IW.u64[p + 4] + IW.u64[p + 1] < IW.u64[p + 4] { abort };
  cvTa0 := IW.u64[fO];
  (ok, pqO, pqL, body) := call open_pis_at_fvars_f(IW.u64[p + 4], EREC⦃cvTa0 + ⟪CV.type⟫⦄, 0);
  if ok == 0 { abort };
  if pqL + IW.u64[p + 1] < pqL { abort };
  ctx := call block_shape_nest_ctx(p, pqO, pqL);
  (ok2, hO, hL) := call nest_holes(ctx);
  if ok2 == 0 { abort };
  return (ctx, hO, hL)
}

/-- `nest_out_kinds(outs.off, outs.len)`: the root frame's outputs' field kinds, `outs.map (·.map
(·.1))`. No copy: an output record `[k.off, k.len, e]` starts with its kinds' slice, so the
outputs' list of `[off, len]` headers already reads as the kinds' (`decKL`). -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:276-280 ConRon.Arena.nestOutKinds
@[no_expose, l_impl ConRon.Arena.nestOutKinds]
def nestOutKinds : FunDecl := lfn (o, l) locals () {
  return (o, l)
}

/-- `check_block_positivity_init()`: `{}`, a fresh all-zero `NestState` (three empty lists). -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:282-298 ConRon.Arena.checkBlockPositivity
@[no_expose, l_impl ConRon.Arena.checkBlockPositivity]
def checkBlockPositivityInit : FunDecl := lfn () locals (q) {
  q := call iw_alloc(6);
  IW.u64[q] := 0; IW.u64[q + 1] := 0; IW.u64[q + 2] := 0;
  IW.u64[q + 3] := 0; IW.u64[q + 4] := 0; IW.u64[q + 5] := 0;
  return q
}

/-- `check_block_positivity(vis, p)`: the block's positivity on its stored constructors
(`p.memberCtors`), at the walk's context; returns the root frame's outputs and the walk's
state. -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:282-298 ConRon.Arena.checkBlockPositivity
@[no_expose, l_impl ConRon.Arena.checkBlockPositivity]
def checkBlockPositivity : FunDecl := lfn (vis, p) locals
    (ctx, hO, hL, caOff, caLen, u, nsEmpty, outsO, outsL, nsPtr, z, isProp, u2) {
  (ctx, hO, hL) := call block_nest_ctx(p);
  (caOff, caLen) := call block_shape_member_ctors(p);
  u := call nest_uniform(ctx, caOff, caLen);
  nsEmpty := call check_block_positivity_init();
  (outsO, outsL, nsPtr) := call nest_root(vis, ctx, hO, hL, caOff, caLen, nsEmpty, 0, 0);
  z := call pin_word(53);
  isProp := call lvl_eq_true(IW.u64[ctx + 9], z);
  u2 := call check_abs_ctor_sorts_all(vis, ctx, isProp, caOff, caLen, outsO, outsL);
  return (outsO, outsL, nsPtr)
}

/-! ## Stage 2: the tail -/

/-- `check_block_idx_sorts(vis, p, ms.off, ms.len)`: every member's INDEX binders have sorts: the
member's telescope (at its former's telescope) opened at variables, each index domain's sort
inferred (`nP + nIdx` past `2^64` a capacity abort; the index binders the telescope's tail past
`nP`, the empty slice at offset `0` when there is none). -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:302-313 ConRon.Arena.checkBlockIdxSorts
@[no_expose, l_impl ConRon.Arena.checkBlockIdxSorts]
def checkBlockIdxSorts : FunDecl := lfn (vis, p, msO, msL) locals
    (ms, nP, ni, srt, k, ok, tqO, tqL, body, dOff, dLen, u) {
  if msL == 0 { return 0 };
  ms := IW.u64[msO];
  nP := IW.u64[p + 4]; ni := IW.u64[ms + 1]; srt := IW.u64[p + 6];
  k := nP + ni;
  if k < nP { abort };
  (ok, tqO, tqL, body) := call open_pis_at_fvars_f(k, EREC⦃IW.u64[ms] + ⟪CV.type⟫⦄, 0);
  if ok == 0 { abort };
  dOff := 0; dLen := 0;
  if nP < tqL { dOff := tqO + nP; dLen := tqL - nP };
  u := call check_struct_field_sorts_i(vis, 1, 0, srt, nP, dOff, dLen, 0, 0, ni);
  u := call check_block_idx_sorts(vis, p, msO + 1, msL - 1);
  return 0
}

/-- `cons_block_ctors(nP, groups.off, groups.len, vis)`: the members' constructors consed, member
by member, in block order, each group under its member's name (`BlockShape.ctorGroups`: the groups
are the member records, `block_shape_ctor_groups`; the name the `EREC` word at the member's `cvT`,
the constructors its `[ctors.off, ctors.len]` words `2`, `3`); recursion as the twin's. -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:315-322 ConRon.Arena.consBlockCtors
@[no_expose, l_impl ConRon.Arena.consBlockCtors]
def consBlockCtors : FunDecl := lfn (nP, gOff, gLen, vis) locals (ms, v1, v2) {
  if gLen == 0 { return vis };
  ms := IW.u64[gOff];
  v1 := call cons_sum_ctors(nP, EREC⦃IW.u64[ms]⦄, IW.u64[ms + 2], IW.u64[ms + 3], vis);
  v2 := call cons_block_ctors(nP, gOff + 1, gLen - 1, v1);
  return v2
}

/-! ## `BlockTail.lean`: the pass, the tail, the block's check -/

/-- `check_block_pass_rec(fe1, p, kinds.off, kinds.len, params.off, params.len, rd, cls.off,
cls.len, tbl.off, tbl.len)`: the 11-word `BlockPass` record (layout in `IndIface`). -/
-- con-ron: ConRon/Arena/Inductives/BlockTail.lean:64-83 ConRon.Arena.checkBlockPass
@[no_expose, l_impl ConRon.Arena.checkBlockPass]
def checkBlockPassRec : FunDecl := lfn (fe1, p1, kO, kL, pO, pL, rd, mO, mL, tO, tL) locals (q) {
  q := call iw_alloc(11);
  IW.u64[q] := fe1;
  IW.u64[q + 1] := p1;
  IW.u64[q + 2] := kO; IW.u64[q + 3] := kL;
  IW.u64[q + 4] := pO; IW.u64[q + 5] := pL;
  IW.u64[q + 6] := rd;
  IW.u64[q + 7] := mO; IW.u64[q + 8] := mL;
  IW.u64[q + 9] := tO; IW.u64[q + 10] := tL;
  return q
}

/-- `check_block_pass(vis, p0, is_rec)`: one pass over the formers, the constructors and the
classes — the formers (and the flush entering the environment that holds them all), the
constructors, the walk's context, the classes, the positivity check and the seeds; returns a
pointer to the `BlockPass` record. -/
-- con-ron: ConRon/Arena/Inductives/BlockTail.lean:64-83 ConRon.Arena.checkBlockPass
@[no_expose, l_impl ConRon.Arena.checkBlockPass]
def checkBlockPass : FunDecl := lfn (vis, p0, isRec) locals
    (fe1, p1, u, ctx, holesO, holesL, rd, msO, msL, outsO, outsL, nsPtr, seedsO, seedsL, ns2,
     kO, kL, q) {
  (fe1, p1) := call check_block_inds(vis, p0, isRec);
  u := call flush_caches();
  u := call check_block_ctors(fe1, fe1, p1, IW.u64[p1], IW.u64[p1 + 1]);
  (ctx, holesO, holesL) := call block_nest_ctx(p1);
  (rd, msO, msL) := call check_block_classes(fe1, p1, IW.u64[ctx + 7], IW.u64[ctx + 8]);
  (outsO, outsL, nsPtr) := call check_block_positivity(fe1, p1);
  (seedsO, seedsL) := call class_seeds(ctx, holesO, holesL, msO, msL);
  ns2 := call nest_seeds(fe1, ctx, seedsO, seedsL, nsPtr);
  (kO, kL) := call nest_out_kinds(outsO, outsL);
  q := call check_block_pass_rec(fe1, p1, kO, kL, IW.u64[ctx + 7], IW.u64[ctx + 8], rd, msO, msL,
    IW.u64[ns2 + 4], IW.u64[ns2 + 5]);
  return q
}

/-- `check_block_rec(vis, p, nested, params.off, params.len, tbl.off, tbl.len, rd, ms.off, ms.len,
block.off, block.len)`: the generated recursor stage at the constructors' environment. -/
-- con-ron: ConRon/Arena/Inductives/BlockTail.lean:85-94 ConRon.Arena.checkBlockRec
@[no_expose, l_impl ConRon.Arena.checkBlockRec]
def checkBlockRec : FunDecl := lfn
    (vis, p, nested, paramsO, paramsL, tblO, tblL, rd, msO, msL, blockO, blockL)
    locals (fe2, outO, outL) {
  (fe2, outO, outL) := call gen_rec_check(vis, p, nested, paramsO, paramsL, tblO, tblL, rd, msO, msL,
    blockO, blockL);
  return (fe2, outO, outL)
}

/-- `cons_block_recs_temp(infos.off, infos.len, vis, prevs.off, prevs.len)`: the checked family's
records (`EREC` constant records) pushed TEMPORARILY, in order; returns the new view and the rows
the pushes displaced (`[name, c, q]`, the own layer's raw row before each push, `env_row_get`), in
push order (`prevs ++ [·]`, `sl_snoc`), for the pop. -/
-- con-ron: ConRon/Arena/Inductives/BlockTail.lean:96-108 ConRon.Arena.consBlockRecsTemp
@[no_expose, l_impl ConRon.Arena.consBlockRecsTemp]
def consBlockRecsTemp : FunDecl := lfn (io, il, vis, po, pl) locals (ci, nm, c, q, e, v, no, nl, ro, rl, rv) {
  if il == 0 { return (vis, po, pl) };
  ci := IW.u64[io];
  nm := EREC⦃ci + ⟪CI.cv + CV.name⟫⦄;
  (c, q) := call env_row_get(nm);
  e := call rec3(nm, c, q);
  v := call env_push(vis, ci);
  (no, nl) := call sl_snoc(po, pl, e);
  (rv, ro, rl) := call cons_block_recs_temp(io + 1, il - 1, v, no, nl);
  return (rv, ro, rl)
}

/-- `check_block_tables(vis, Q.off, Q.len)`: the checks of the block's projection tables (the
`IW` slice of table records `block_tables` built), at the environment holding the formers and the
constructors. -/
-- con-ron: ConRon/Arena/Inductives/BlockTail.lean:110-118 ConRon.Arena.checkBlockTables
@[no_expose, l_impl ConRon.Arena.checkBlockTables]
def checkBlockTables : FunDecl := lfn (vis, tO, tL) locals (u) {
  if tL == 0 { return 0 };
  u := call check_struct_proj_table(IW.u64[tO], vis);
  u := call check_block_tables(vis, tO + 1, tL - 1);
  return 0
}

/-- `check_block_tail_stream(p, fe2b, out.off, out.len)`: the second half of `checkBlockTail` (the
Rust's `check_block_tail_stream`): the stream's K flags against the generated recursors, the
generated family's records pushed in place (a flush entering), the stream's recursors against them,
the pushes undone in reverse order (`gen_rec_check_pop_all`), the literal flags set back (`env_set_flags`
of `CTL[160]`, `CTL[161]` saved before the pushes) and the flush leaving. Returns the
constructors' environment. -/
-- con-ron: ConRon/Arena/Inductives/BlockTail.lean:120-146 ConRon.Arena.checkBlockTail
@[no_expose, l_impl ConRon.Arena.checkBlockTail]
def checkBlockTailStream : FunDecl := lfn (p, fe2b, outO, outL) locals
    (u, io, il, feG, po, pl, fe3, nl, sl) {
  u := call stream_k_check(p, IW.u64[p + 2], IW.u64[p + 3], outO, outL);
  nl := CTL.u64[160];
  sl := CTL.u64[161];
  (io, il) := call block_rec_infos_tf(p, 0, outO, outL);
  (feG, po, pl) := call cons_block_recs_temp(io, il, fe2b, 0, 0);
  u := call flush_caches();
  u := call stream_recs_check(feG, IW.u64[p + 2], IW.u64[p + 3], outO, outL);
  fe3 := call gen_rec_check_pop_all(feG, po, pl);
  u := call env_set_flags(nl, sl);
  u := call flush_caches();
  return fe3
}

/-- `check_block_tail(block.off, block.len, q, Q.off, Q.len)`: the checks after the pass — the index
binders' sorts, the constructors consed (and the flush entering that environment), the generated
recursors, the stream's K flags and recursors against them (`check_block_tail_stream`), and the
checks of the block's projection tables `Q` (an `IW` slice of table records); returns the
constructors' environment (`q` a `BlockPass` pointer). -/
-- con-ron: ConRon/Arena/Inductives/BlockTail.lean:120-146 ConRon.Arena.checkBlockTail
@[no_expose, l_impl ConRon.Arena.checkBlockTail]
def checkBlockTail : FunDecl := lfn (blockO, blockL, q, tO, tL) locals
    (env1, p, u, mcO, mcL, fe2, nested, fe2b, outO, outL, fe3) {
  env1 := IW.u64[q];
  p := IW.u64[q + 1];
  u := call check_block_idx_sorts(env1, p, IW.u64[p], IW.u64[p + 1]);
  (mcO, mcL) := call block_shape_ctor_groups(p);
  fe2 := call cons_block_ctors(IW.u64[p + 4], mcO, mcL, env1);
  u := call flush_caches();
  nested := call block_nested_bit(p, IW.u64[q + 2], IW.u64[q + 3]);
  (fe2b, outO, outL) := call check_block_rec(fe2, p, nested, IW.u64[q + 4], IW.u64[q + 5],
    IW.u64[q + 9], IW.u64[q + 10], IW.u64[q + 6], IW.u64[q + 7], IW.u64[q + 8], blockO, blockL);
  fe3 := call check_block_tail_stream(p, fe2b, outO, outL);
  u := call check_block_tables(fe3, tO, tL);
  return fe3
}

/-! ## The block's check -/

/-- `declined_at_definition()`: the families declined at a definition — the names a literal's
constructor form applies (`String.ofList`, `List.nil`, `List.cons`, `Char.ofNat`) and `Bool`, off
the pin table, as an `IW` list. -/
-- con-ron: ConRon/Arena/Inductives/BlockTail.lean:150-154 ConRon.Arena.declinedAtDefinition
@[no_expose, l_impl ConRon.Arena.declinedAtDefinition]
def declinedAtDefinition : FunDecl := lfn () locals (a, b, c, d, e, q) {
  a := call pin_at(6);
  b := call pin_at(8);
  c := call pin_at(9);
  d := call pin_at(12);
  e := call pin_at(29);
  q := call iw_alloc(5);
  IW.u64[q] := a; IW.u64[q + 1] := b; IW.u64[q + 2] := c; IW.u64[q + 3] := d; IW.u64[q + 4] := e;
  return (q, 5)
}

/-- `reduce_member(vis, ms, nP)`: a member's former at its telescope — where the declared type
does not show one (`former_def_headed`), and the family is not one declined at a definition, the
declared type checked, reduced (`reduced_former`) and the two compared, a fresh member record with
`cvT` the reduct; else `ms` itself. -/
-- con-ron: ConRon/Arena/Inductives/BlockTail.lean:156-173 ConRon.Arena.reduceMember
@[no_expose, l_impl ConRon.Arena.reduceMember]
def reduceMember : FunDecl := lfn (vis, ms, nP) locals (cvT, dh, dO, dL, hit, u, k, cvR, eq, q) {
  cvT := IW.u64[ms];
  dh := call former_def_headed(EREC⦃cvT + ⟪CV.type⟫⦄);
  if dh == 0 { return ms };
  (dO, dL) := call declined_at_definition();
  hit := call sl_contains(dO, dL, EREC⦃cvT⦄);
  if hit != 0 { fail R_THIS_FAMILY_STORED };
  u := call check_constant_val(vis, cvT, 0, 0, 0);
  k := nP + IW.u64[ms + 1];
  if k < nP { abort };
  cvR := call reduced_former(vis, cvT, k);
  eq := call is_def_eq_core(vis, 0, EREC⦃cvT + ⟪CV.type⟫⦄, EREC⦃cvR + ⟪CV.type⟫⦄);
  if eq == 0 { fail R_DIRECT_SUM_A };
  q := call rec5(cvR, IW.u64[ms + 1], IW.u64[ms + 2], IW.u64[ms + 3], IW.u64[ms + 4]);
  return q
}

/-- `reduce_members(vis, nP, ms.off, ms.len)`: the members, each at its telescope, a flush before
each (the cached twin's); recursion as the twin's, each record consed onto the rest's slice. -/
-- con-ron: ConRon/Arena/Inductives/BlockTail.lean:175-185 ConRon.Arena.reduceMembers
@[no_expose, l_impl ConRon.Arena.reduceMembers]
def reduceMembers : FunDecl := lfn (vis, nP, msO, msL) locals (u, m, ro, rl, o, l) {
  if msL == 0 { return (0, 0) };
  u := call flush_caches();
  m := call reduce_member(vis, IW.u64[msO], nP);
  (ro, rl) := call reduce_members(vis, nP, msO + 1, msL - 1);
  (o, l) := call sl_cons(m, ro, rl);
  return (o, l)
}

/-- `check_block_names(p0)`: `checkBlock`'s opening guards — the distinct constructor and member
names, and no member at a `Bool` constructor's name. -/
-- con-ron: ConRon/Arena/Inductives/BlockTail.lean:187-217 ConRon.Arena.checkBlock
@[no_expose, l_impl ConRon.Arena.checkBlock]
def checkBlockNames : FunDecl := lfn (p0) locals (ctO, ctL, cnO, cnL, nmO, nmL, nd1, nd2, bt, bf, h1, h2) {
  (ctO, ctL) := call block_shape_all_ctors(p0);
  (cnO, cnL) := call block_caps_ctor_names(ctO, ctL);
  (nmO, nmL) := call block_shape_member_names(p0);
  nd1 := call sl_nodup(cnO, cnL);
  nd2 := call sl_nodup(nmO, nmL);
  if nd1 == 0 || nd2 == 0 { fail R_DIRECT_REC_DUPLICATE };
  bt := call pin_at(30);
  bf := call pin_at(31);
  h1 := call sl_contains(nmO, nmL, bt);
  h2 := call sl_contains(nmO, nmL, bf);
  if h1 != 0 || h2 != 0 { fail R_DIRECT_REC_A };
  return 0
}

/-- `check_block(vis, boff, blen, p0)`: check an inductive block and install it — the names'
guards, each former reduced to its telescope once (`reduce_members`), the flush, the pass at
official's `is_rec` (`block_is_rec`, read off the block as declared), the projection tables read
off the block once (`block_tables`; an internal error, an `abort`, where a constructor is too short
for them), the checks after the pass (those tables' among them), and the block's install
(`block_recs` and the same tables pushed onto the constructors' environment the tail hands back,
`ifenv_push_delta`). -/
-- con-ron: ConRon/Arena/Inductives/BlockTail.lean:187-217 ConRon.Arena.checkBlock
@[no_expose, l_impl ConRon.Arena.checkBlock]
def checkBlock : FunDecl := lfn (vis, blockO, blockL, p0) locals
    (u, msO, msL, isRec, p1, q, tok, tO, tL, fe2, rO, rL, fe) {
  u := call check_block_names(p0);
  (msO, msL) := call reduce_members(vis, IW.u64[p0 + 4], IW.u64[p0], IW.u64[p0 + 1]);
  u := call flush_caches();
  isRec := call block_is_rec(p0);
  p1 := call block_shape_with_members(p0, msO, msL);
  q := call check_block_pass(vis, p1, isRec);
  (tok, tO, tL) := call block_tables(p0, IW.u64[p0], IW.u64[p0 + 1]);
  if tok == 0 { abort };
  fe2 := call check_block_tail(blockO, blockL, q, tO, tL);
  (rO, rL) := call block_recs(p0, IW.u64[p0 + 2], IW.u64[p0 + 3]);
  fe := call ifenv_push_delta(fe2, rO, rL, tO, tL);
  return fe
}

/-! ## The program, the foreign closure and the well-formedness check -/

/-- This module's L functions. -/
def indInstallFns : Prog :=
  [("block_caps_ctor_names", blockCapsCtorNames), ("block_caps_at_er_copy", blockCapsAtErCopy),
   ("block_caps_at_er_copy_go", blockCapsAtErCopyGo),
   ("member_never_zero", memberNeverZero),
   ("block_caps_at", blockCapsAt), ("block_caps_head", blockCapsHead), ("block_caps_fin", blockCapsFin), ("block_caps_one", blockCapsOne),
   ("pi_doms_mention_any", piDomsMentionAny), ("block_is_rec_member", blockIsRecMember), ("block_is_rec_go", blockIsRecGo),
   ("block_is_rec", blockIsRec), ("check_block_tele", checkBlockTele),
   ("check_block_teles", checkBlockTeles), ("check_block_doms_at", checkBlockDomsAt),
   ("check_block_agree_one", checkBlockAgreeOne), ("check_block_agree", checkBlockAgree),
   ("cons_block_inds", consBlockInds), ("ind_info_rec", indInfoRec), ("er_put_ci", erPutCi),
   ("check_block_inds", checkBlockInds), ("block_shape_nest_ctx", blockShapeNestCtx),
   ("check_block_ctors", checkBlockCtors),
   ("check_abs_ctor_sorts_one", checkAbsCtorSortsOne), ("check_abs_ctor_sorts", checkAbsCtorSorts),
   ("check_abs_ctor_sorts_all", checkAbsCtorSortsAll), ("block_nest_ctx", blockNestCtx),
   ("nest_out_kinds", nestOutKinds),
   ("check_block_positivity_init", checkBlockPositivityInit),
   ("check_block_positivity", checkBlockPositivity),
   ("check_block_idx_sorts", checkBlockIdxSorts),
   ("cons_block_ctors", consBlockCtors), ("check_block_pass_rec", checkBlockPassRec),
   ("check_block_pass", checkBlockPass), ("check_block_rec", checkBlockRec),
   ("cons_block_recs_temp", consBlockRecsTemp), ("check_block_tables", checkBlockTables),
   ("check_block_tail_stream", checkBlockTailStream), ("check_block_tail", checkBlockTail),
   ("declined_at_definition", declinedAtDefinition), ("reduce_member", reduceMember),
   ("reduce_members", reduceMembers), ("check_block_names", checkBlockNames),
   ("check_block", checkBlock)]

/-- Stubs for the functions of OTHER modules this module calls (arity per the naming rule; see
the module doc comment for each one's convention). -/
def indInstallForeign : Prog :=
  [("check_sum_tele", stub 2), ("check_sum_ctors", stub 13), ("cons_sum_ctors", stub 5),
   ("check_struct_field_sorts_i", stub 10), ("param_levels", stub 2),
   ("check_struct_proj_table", stub 7),
   ("mentions_any_const", stub 3), ("nest_holes", stub 1), ("nest_ctx_hi_at", stub 2),
   ("nest_uniform", stub 3), ("nest_root", stub 9), ("nest_seeds", stub 5),
   ("block_shape_with_sort", stub 2), ("block_shape_with_members", stub 3),
   ("block_shape_member_names", stub 1), ("block_shape_lps", stub 1), ("block_shape_n_idxs", stub 1),
   ("block_shape_formers", stub 1), ("block_shape_declared", stub 1),
   ("block_shape_member_ctors", stub 1), ("block_shape_ctor_groups", stub 1),
   ("block_shape_all_ctors", stub 1), ("check_block_classes", stub 4),
   ("class_seeds", stub 5), ("gen_rec_check", stub 12), ("block_nested_bit", stub 3),
   ("gen_rec_check_pop_all", stub 3), ("stream_k_check", stub 5), ("stream_recs_check", stub 5),
   ("block_rec_infos_tf", stub 4), ("block_recs", stub 3), ("block_tables", stub 3),
   ("ifenv_push_delta", stub 5), ("former_def_headed", stub 1), ("reduced_former", stub 3),
   ("check_constant_val", stub 3), ("member_names_copy", stub 3), ("former_z", stub 1),
   ("env_set_flags", stub 2)]

-- `check_block_doms_at` at `j = 0`: no binders to compare, no callee touched.
#guard
  match run (indInstallFns ++ libFns ++ stubFns ++ masterFns ++ indInstallForeign) 100
      "check_block_doms_at" [0, 0, 0, 0, 0, 0, 0] testMem with
  | .ok ([0], _) => true
  | _ => false

-- `cons_block_ctors` at an empty member list: the view is unchanged, no callee touched.
#guard
  match run (indInstallFns ++ libFns ++ stubFns ++ masterFns ++ indInstallForeign) 100
      "cons_block_ctors" [0, 0, 0, 7] testMem with
  | .ok ([7], _) => true
  | _ => false

-- `check_abs_ctor_sorts` at two empty lists: no callee touched.
#guard
  match run (indInstallFns ++ libFns ++ stubFns ++ masterFns ++ indInstallForeign) 100
      "check_abs_ctor_sorts" [0, 0, 0, 0, 0, 0, 0] testMem with
  | .ok ([0], _) => true
  | _ => false

-- `check_block_positivity_init`: a fresh zero `NestState`.
#guard
  match run (indInstallFns ++ libFns ++ stubFns ++ masterFns ++ indInstallForeign) 100
      "check_block_positivity_init" [] testMem with
  | .ok ([q], m) => (List.range 6).all (fun j => rdW (m.arr64 IW) (q + UInt64.ofNat j) == 0)
  | _ => false

end L.Ind
