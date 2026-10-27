import ConAgua.Arena.IndIface

/-!
# The uniform inductive install, at k members (lane `induct`, module `IndInstall`)

The L translation of `vendor/con-ron/ConRon/Arena/Inductives/BlockInstall.lean` and
`.../BlockTail.lean`: the capability record per member, the formers' stage (telescopes, the two
agreements, the cons), the constructors' stage, the positivity check on the stored constructors,
the index sorts and the constructors' cons (`BlockInstall.lean`), then one pass over formers,
constructors and classes, the recursor stage, the projection tables and the entry `check_block`
(`BlockTail.lean`). No proofs this round: the translation is split, one L function per twin
function (more for the bigger ones), each tagged `@[l_impl …]`.

**One pointer serves as both a `BlockShape` and a `BlockParts`.** `BlockParts` (`decBP`) is a
one-field wrapper around `BlockShape` (`decBS`) at the SAME pool offset (`BlockParts.complete`
is the identity on that pointer), so every `p : BlockParts` argument below is just the
`BlockShape` pointer, and `BlockParts.complete _ p₁` is simply `p₁`.

**Foreign callees** (owned by other modules, named by the project's naming rule; each is a
`stub` here, closing this module's program on its own):

* `IndSum`: `check_sum_tele(vis, cv, n, cvTa0) → (cvTa, s)`; `check_sum_ctors(vis0, vis, T,
  lps.off, lps.len, nP, nIdx, resSort, isProp, large, cvTa, ctors.off, ctors.len) → (cs.off,
  cs.len, ss.off, ss.len)`; `cons_sum_ctors(nP, ctors.off, ctors.len, vis) → vis'`;
  `check_struct_field_sorts_i(vis, isProp, large, s, nP, fvs.off, fvs.len, idx.off, idx.len, j) →
  (off, len)`; `param_levels(lps.off, lps.len) → lvls`; `struct_proj_guards(cty, nP, nF,
  sorts.off, sorts.len) → (off, len)`; `check_struct_proj_table(T, C, lps.off, lps.len, nP, nF,
  resSort, guards.off, guards.len, off, cvCa, vis) → vis'`.
* `IndPos`/`IndPos2`: `mentions_any_const(names.off, names.len, e) → bool`; `nest_holes(vis,
  ctx) → (ok, off, len)`; `nest_ctx_hi_at(ctx, nf) → hi`; `nest_uniform(ctx, ctorsAs.off,
  ctorsAs.len)`; `nest_root(vis, ctx, holes.off, holes.len, ctorsAs.off, ctorsAs.len, ns, outs.off,
  outs.len) → (outs'.off, outs'.len, ns')`; `nest_seeds(vis, ctx, seeds.off, seeds.len, ns) →
  ns'`.
* `IndParts`: `block_shape_with_sort(p, s) → p'`; `block_shape_member_names(p) → (off, len)`;
  `block_shape_lps(p) → (off, len)`; `block_shape_n_idxs(p) → (off, len)`;
  `block_shape_all_ctors(p) → (off, len)` (a list of `[cv, nF]` pointers).
* `RecGen`: `check_block_classes(vis, p, params.off, params.len, ctorsAs.off, ctorsAs.len) →
  (rd, ms.off, ms.len)`; `class_seeds(ctx, holes.off, holes.len, ms.off, ms.len) → (off, len)`;
  `gen_rec_check(vis, p, nested, params.off, params.len, tbl.off, tbl.len, rd, ms.off, ms.len,
  block.off, block.len, cvTas.off, cvTas.len) → (fe', out.off, out.len)` (`checkBlockRec`'s own
  parameter order has `block` before `cvTas`; `genRecCheck`'s has `ms`, `cvTas`, `block` — the
  wrapper reorders).
* `RecCheck`: `block_nested_bit(p, kinds.off, kinds.len) → nested`; `cons_block_recs_tf(vis2, p,
  m, out.off, out.len, vis) → vis'`.

`block_large_elim_allowed` (also IndParts) is not called by anything in this module.
-/

namespace L.Ind

open L.Arena

/-! ## `blockCapsAt`: one member's `IIndCaps`, built in `EREC` (`decCaps`, 15 words) -/

/-- `block_caps_ctor_names(o, l)`: the ctor-name list of a `(cv, nF)` pointer slice `(o, l)`, built
fresh in `IW`. -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:47-92 ConRon.Arena.blockCapsAt
@[l_impl ConRon.Arena.blockCapsAt]
def blockCapsCtorNames : FunDecl := lfn (o, l) locals (q, u) {
  q := call iw_alloc(l);
  u := call member_names_copy(q, o, l);
  return (q, l)
}

/-- `block_caps_at_er_copy(o, l)`: an `IW` slice copied into fresh `EREC` words (the reverse of
`er_to_iw`), for `IIndCaps`'s `all`/`ctors` fields (both EREC slices). -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:47-92 ConRon.Arena.blockCapsAt
@[l_impl ConRon.Arena.blockCapsAt]
def blockCapsAtErCopy : FunDecl := lfn (o, l) locals (q, u) {
  q := call erec_alloc(l);
  u := call block_caps_at_er_copy_go(q, o, l);
  return (q, l)
}

/-- `block_caps_at_er_copy_go(d, s, l)`: `EREC[d + j] := IW[s + j]` for `j < l`, recursively. -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:47-92 ConRon.Arena.blockCapsAt
@[l_impl ConRon.Arena.blockCapsAt]
def blockCapsAtErCopyGo : FunDecl := lfn (d, s, l) locals (u) {
  if l == 0 { return 0 };
  EREC.u64[d] := IW.u64[s];
  u := call block_caps_at_er_copy_go(d + 1, s + 1, l - 1);
  return 0
}

/-- `block_caps_at(p, mi, is_rec)`: member `mi`'s `IIndCaps`, a fresh 15-word `IW` record (the
`EREC` layout of `decCaps`; `cons_block_inds` copies it into the former's record). At exactly one
constructor `c`: `eta`, `etaCtor`, `etaParams`, `etaFields`, `unitlike`, `unitParams`, `ruleK`
(AENEAS_FINDINGS F18); else (no member, or another ctor count) their defaults `0`. At every
member the result sort's zero-ness (`lv_zero_caps`, three words), `all` (the member names, copied
into `EREC`), `nparams`, `ctors` (the member's ctor names, copied into `EREC`). Every field is
computed first, the record written last (three consecutive `rec5`s) (lane `indproofs2`: round 2 wrote the record across
calls, below the record pool's top, which the stage relation cannot follow; and `ruleK` took the
`isProp` word unnormalised, wrong for a word other than `0`/`1`). -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:47-92 ConRon.Arena.blockCapsAt
@[l_impl ConRon.Arena.blockCapsAt]
def blockCapsAt : FunDecl := lfn (p, mi, isRec) locals
    (coff, clen, one, ms, w0, w1, w2, w3, w4, w6, z0, z1, z2, caps) {
  (coff, clen, one, ms) := call block_caps_head(p, mi);
  if one == 1 {
    (w0, w1, w2, w3, w4, w6) := call block_caps_one(p, ms, isRec)
  } else {
    w0 := 0; w1 := 0; w2 := 0; w3 := 0; w4 := 0; w6 := 0
  };
  (z0, z1, z2) := call lv_zero_caps(IW.u64[p + 6]);
  caps := call block_caps_fin(p, coff, clen, w0, w1, w2, w3, w4, w6, z0, z1, z2);
  return caps
}

/-- `block_caps_fin(p, coff, clen, w0, w1, w2, w3, w4, w6, z0, z1, z2)`: `blockCapsAt`'s record —
the member names and the ctor names copied into `EREC`, then the 15 words (three consecutive
`rec5`s at the pool top). -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:47-92 ConRon.Arena.blockCapsAt
@[l_impl ConRon.Arena.blockCapsAt]
def blockCapsFin : FunDecl := lfn (p, coff, clen, w0, w1, w2, w3, w4, w6, z0, z1, z2) locals
    (namesO, namesL, allQ, allL, ctNO, ctNL, ctQ, ctL, np, caps, u) {
  (namesO, namesL) := call block_shape_member_names(p);
  (allQ, allL) := call block_caps_at_er_copy(namesO, namesL);
  (ctNO, ctNL) := call block_caps_ctor_names(coff, clen);
  (ctQ, ctL) := call block_caps_at_er_copy(ctNO, ctNL);
  np := IW.u64[p + 4];
  caps := call rec5(w0, w1, w2, w3, w4);
  u := call rec5(w2, w6, z0, z1, z2);
  u := call rec5(allQ, allL, np, ctQ, ctL);
  return caps
}

/-- `block_caps_head(p, mi)`: member `mi`'s constructor slice `(coff, clen)` (`(0, 0)` past the
members; `(0, 0)` also at no constructor, whatever its offset word), whether it has exactly one
constructor, and its record pointer. -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:47-92 ConRon.Arena.blockCapsAt
@[l_impl ConRon.Arena.blockCapsAt]
def blockCapsHead : FunDecl := lfn (p, mi) locals (ms) {
  if IW.u64[p + 1] <= mi { return (0, 0, 0, 0) };
  ms := IW.u64[IW.u64[p] + mi];
  if IW.u64[ms + 3] == 0 { return (0, 0, 0, ms) };
  return (IW.u64[ms + 2], IW.u64[ms + 3], u64(IW.u64[ms + 3] == 1), ms)
}

/-- `block_caps_one(p, ms, is_rec)`: the fields of exactly one constructor `c` — `eta`,
`etaCtor`, `etaParams` (= `unitParams`), `etaFields`, `unitlike`, `ruleK` (AENEAS_FINDINGS F18;
`isProp` normalised to `0`/`1`). -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:47-92 ConRon.Arena.blockCapsAt
@[l_impl ConRon.Arena.blockCapsAt]
def blockCapsOne : FunDecl := lfn (p, ms, isRec) locals (nIdx, c, nF, isP) {
  nIdx := IW.u64[ms + 1]; c := IW.u64[IW.u64[ms + 2]]; nF := IW.u64[c + 1];
  isP := u64(IW.u64[p + 8] != 0);
  return (u64(nIdx == 0) & u64(isP == 0) & u64(isRec == 0), EREC.u64[IW.u64[c]], IW.u64[p + 4], nF,
    u64(nIdx == 0) & u64(nF == 0) & u64(isRec == 0), u64(IW.u64[p + 1] == 1) & u64(nF == 0) & isP)
}

/-! ## `piDomsMentionAny`, `blockRawRec`: official's `is_rec` -/

/-- `pi_doms_mention_any(names.off, names.len, fuel, e)`: does some binder domain of the
syntactic `∀`-telescope of `e` mention one of `names`? Fueled (recurses on a handle). -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:94-106 ConRon.Arena.piDomsMentionAny
@[l_impl ConRon.Arena.piDomsMentionAny]
def piDomsMentionAny : FunDecl := lfn (namesO, namesL, fuel, e) locals (g, x, y, z, b, r) {
  if fuel == 0 { abort };
  (g, x, y, z) := call e_view(e);
  if g != 6 { return 0 };
  b := call mentions_any_const(namesO, namesL, x);
  if b != 0 { return 1 };
  r := call pi_doms_mention_any(namesO, namesL, fuel - 1, y);
  return r
}

/-- `block_raw_rec_member(names.off, names.len, ms)`: does some DECLARED constructor type of
member `ms` mention one of `names` in some binder domain of its telescope? -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:108-114 ConRon.Arena.blockRawRec
@[l_impl ConRon.Arena.blockRawRec]
def blockRawRecMember : FunDecl := lfn (namesO, namesL, coff, clen) locals (b, r) {
  if clen == 0 { return 0 };
  b := call pi_doms_mention_any(namesO, namesL, ⟪CWF⟫, EREC.u64[IW.u64[IW.u64[coff]] + 3]);
  if b != 0 { return 1 };
  r := call block_raw_rec_member(namesO, namesL, coff + 1, clen - 1);
  return r
}

/-- `block_raw_rec_go(names.off, names.len, moff, mlen)`: the members' `anyM`, in order
(recursive, lane `indproofs2`: was a loop). -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:108-114 ConRon.Arena.blockRawRec
@[l_impl ConRon.Arena.blockRawRec]
def blockRawRecGo : FunDecl := lfn (namesO, namesL, moff, mlen) locals (ms, b, r) {
  if mlen == 0 { return 0 };
  ms := IW.u64[moff];
  b := call block_raw_rec_member(namesO, namesL, IW.u64[ms + 2], IW.u64[ms + 3]);
  if b != 0 { return 1 };
  r := call block_raw_rec_go(namesO, namesL, moff + 1, mlen - 1);
  return r
}

/-- `block_raw_rec(p)`: official's `is_rec` — some member occurs in some binder domain of some
declared constructor's telescope. -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:108-114 ConRon.Arena.blockRawRec
@[l_impl ConRon.Arena.blockRawRec]
def blockRawRec : FunDecl := lfn (p) locals (namesO, namesL, b) {
  (namesO, namesL) := call block_shape_member_names(p);
  b := call block_raw_rec_go(namesO, namesL, IW.u64[p], IW.u64[p + 1]);
  return b
}

/-! ## Stage 1: the formers -/

/-- `check_block_tele(vis, nP, ms)`: one member's type former — the constant check, official's
telescope loop and the result sort (`nP + nIdx` past `2^64` a capacity abort). -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:118-131 ConRon.Arena.checkBlockTele
@[l_impl ConRon.Arena.checkBlockTele]
def checkBlockTele : FunDecl := lfn (vis, nP, ms) locals
    (cvT, z, cvTa, s, ok, bsOff, bsLen, body, srt, k) {
  cvT := IW.u64[ms];
  k := nP + IW.u64[ms + 1];
  if k < nP { abort };
  z := call check_constant_val(vis, cvT);
  (cvTa, s) := call check_sum_tele(vis, cvT, k, cvT);
  (ok, bsOff, bsLen, body) := call strip_pis(k, EREC.u64[cvTa + 3]);
  if ok == 0 { abort };
  srt := call intern_sort(s);
  if body == srt { return (cvTa, s) };
  abort
}

/-- `check_block_teles(vis, nP, ms.off, ms.len)`: the members' type formers, in block order, each
a pointer to `[cvTa, s]`; recursion as the twin's, each record consed onto the rest's slice
(`sl_cons`, a copy per element: docs/deviations.md D18). -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:133-142 ConRon.Arena.checkBlockTeles
@[l_impl ConRon.Arena.checkBlockTeles]
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
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:144-158 ConRon.Arena.checkBlockDomsAt
@[l_impl ConRon.Arena.checkBlockDomsAt]
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
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:160-179 ConRon.Arena.checkBlockAgree
@[l_impl ConRon.Arena.checkBlockAgree]
def checkBlockAgreeOne : FunDecl := lfn (vis, nP, fvs0O, fvs0L, s0, cvTa, s) locals
    (ok, fvsO, fvsL, body, domsO, domsL, u, eq) {
  (ok, fvsO, fvsL, body) := call open_pis_at_fvars_f(nP, EREC.u64[cvTa + 3], 0);
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
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:160-179 ConRon.Arena.checkBlockAgree
@[l_impl ConRon.Arena.checkBlockAgree]
def checkBlockAgree : FunDecl := lfn (vis, nP, cvTa0, s0, restO, restL) locals
    (ok0, fvs0O, fvs0L, body0, rp, u) {
  if restL == 0 { return 0 };
  (ok0, fvs0O, fvs0L, body0) := call open_pis_at_fvars_f(nP, EREC.u64[cvTa0 + 3], 0);
  if ok0 == 0 { abort };
  rp := IW.u64[restO];
  u := call check_block_agree_one(vis, nP, fvs0O, fvs0L, s0, IW.u64[rp], IW.u64[rp + 1]);
  u := call check_block_agree(vis, nP, cvTa0, s0, restO + 1, restL - 1);
  return 0
}

/-- `cons_block_inds(p1, is_rec, cvTas.off, cvTas.len, vis, i)`: the members' formers consed, in
block order, each with its capability record at `is_rec` (member `i` first), by recursion as the
twin's; the `.indInfo` record (kind `3`, the constant's four words, the capability record's 15) is
`ind_info_rec`'s. Returns the new view. -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:181-190 ConRon.Arena.consBlockInds
@[l_impl ConRon.Arena.consBlockInds]
def consBlockInds : FunDecl := lfn (p1, isRec, cvO, cvL, vis, i) locals (caps, rec, v1, v2) {
  if cvL == 0 { return vis };
  caps := call block_caps_at(p1, i, isRec);
  rec := call ind_info_rec(IW.u64[cvO], caps);
  v1 := call env_push(vis, rec);
  v2 := call cons_block_inds(p1, isRec, cvO + 1, cvL - 1, v1, i + 1);
  return v2
}

/-- `ind_info_rec(cv, caps)`: a fresh `.indInfo` record — kind `3`, the constant's four `EREC`
words at `cv`, the capability record's 15 `IW` words at `caps` — written right after its
allocation, five words at a time. -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:181-190 ConRon.Arena.consBlockInds
@[l_impl ConRon.Arena.consBlockInds]
def indInfoRec : FunDecl := lfn (cv, caps) locals (q, u) {
  q := call erec_alloc(20);
  u := call er_put5(q, 3, EREC.u64[cv], EREC.u64[cv + 1], EREC.u64[cv + 2], EREC.u64[cv + 3]);
  u := call er_put5(q + 5, IW.u64[caps], IW.u64[caps + 1], IW.u64[caps + 2], IW.u64[caps + 3],
    IW.u64[caps + 4]);
  u := call er_put5(q + 10, IW.u64[caps + 5], IW.u64[caps + 6], IW.u64[caps + 7], IW.u64[caps + 8],
    IW.u64[caps + 9]);
  u := call er_put5(q + 15, IW.u64[caps + 10], IW.u64[caps + 11], IW.u64[caps + 12],
    IW.u64[caps + 13], IW.u64[caps + 14]);
  return q
}

/-- `er_put5(d, a, b, c, e, f)`: `EREC[d‥d+5) := [a, b, c, e, f]`. -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:181-190 ConRon.Arena.consBlockInds
@[l_impl ConRon.Arena.consBlockInds]
def erPut5 : FunDecl := lfn (d, a, b, c, e, f) locals () {
  EREC.u64[d] := a; EREC.u64[d + 1] := b; EREC.u64[d + 2] := c; EREC.u64[d + 3] := e;
  EREC.u64[d + 4] := f;
  return 0
}

/-- `check_block_inds_cv_tas(cvTa0, rest.off, rest.len)`: `cvTa0 :: rest.map (·.1)`, the
formers' constants, a fresh `IW` slice (consed: `sl_cons`, D18). -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:192-209 ConRon.Arena.checkBlockInds
@[l_impl ConRon.Arena.checkBlockInds]
def checkBlockIndsCvTas : FunDecl := lfn (cvTa0, restO, restL) locals (ro, rl, o, l) {
  (ro, rl) := call check_block_inds_cv_tas_go(restO, restL);
  (o, l) := call sl_cons(cvTa0, ro, rl);
  return (o, l)
}

/-- `check_block_inds_cv_tas_go(s, l)`: `[IW[IW[s + j]] | j < l]` (each former's constant, the
first word of its `(cv, s)` pointer), by recursion, each consed onto the rest's slice. -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:192-209 ConRon.Arena.checkBlockInds
@[l_impl ConRon.Arena.checkBlockInds]
def checkBlockIndsCvTasGo : FunDecl := lfn (s, l) locals (ro, rl, o, l2) {
  if l == 0 { return (0, 0) };
  (ro, rl) := call check_block_inds_cv_tas_go(s + 1, l - 1);
  (o, l2) := call sl_cons(IW.u64[IW.u64[s]], ro, rl);
  return (o, l2)
}

/-- `check_block_inds(vis, p, is_rec)`: **stage 1** — the k type formers, checked, agreed and
consed (`p` a `BlockParts`/`BlockShape` pointer, same word). -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:192-209 ConRon.Arena.checkBlockInds
@[l_impl ConRon.Arena.checkBlockInds]
def checkBlockInds : FunDecl := lfn (vis, p, isRec) locals
    (moff, mlen, ms0, nP, cvTa0, s0, cvsO, cvsL, u, p1, cvTasO, cvTasL, fe1) {
  moff := IW.u64[p]; mlen := IW.u64[p + 1];
  if mlen == 0 { abort };
  ms0 := IW.u64[moff];
  nP := IW.u64[p + 4];
  (cvTa0, s0) := call check_block_tele(vis, nP, ms0);
  (cvsO, cvsL) := call check_block_teles(vis, nP, moff + 1, mlen - 1);
  u := call check_block_agree(vis, nP, cvTa0, s0, cvsO, cvsL);
  p1 := call block_shape_with_sort(p, s0);
  (cvTasO, cvTasL) := call check_block_inds_cv_tas(cvTa0, cvsO, cvsL);
  fe1 := call cons_block_inds(p1, isRec, cvTasO, cvTasL, vis, 0);
  return (fe1, cvTasO, cvTasL, p1)
}

/-! ## Stage 1b: the constructors, and the positivity check -/

/-- `block_shape_nest_ctx(p, fvsP.off, fvsP.len)`: the block's positivity context at the
canonical parameter variables `fvsP` (a pointer to the 11-word `NestCtx` record). -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:213-222 ConRon.Arena.BlockShape.nestCtx
@[l_impl ConRon.Arena.BlockShape.nestCtx]
def blockShapeNestCtx : FunDecl := lfn (p, fvsPO, fvsPL) locals
    (namesO, namesL, lpsO, lpsL, nIdxsO, nIdxsL, lvls, np, srt, q) {
  (namesO, namesL) := call block_shape_member_names(p);
  (lpsO, lpsL) := call block_shape_lps(p);
  (nIdxsO, nIdxsL) := call block_shape_n_idxs(p);
  lvls := call param_levels(lpsO, lpsL);
  np := IW.u64[p + 4];
  srt := IW.u64[p + 6];
  q := call iw_alloc(11);
  IW.u64[q] := namesO; IW.u64[q + 1] := namesL;
  IW.u64[q + 2] := lpsO; IW.u64[q + 3] := lpsL;
  IW.u64[q + 4] := np;
  IW.u64[q + 5] := nIdxsO; IW.u64[q + 6] := nIdxsL;
  IW.u64[q + 7] := fvsPO; IW.u64[q + 8] := fvsPL;
  IW.u64[q + 9] := srt;
  IW.u64[q + 10] := lvls;
  return q
}

/-- `check_block_ctors_one(vis0, vis, p, lps.off, lps.len, ms, cvTa)`: one member's constructors,
at the environment holding all the formers. -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:224-237 ConRon.Arena.checkBlockCtors
@[l_impl ConRon.Arena.checkBlockCtors]
def checkBlockCtorsOne : FunDecl := lfn (vis0, vis, p, lpsO, lpsL, ms, cvTa) locals
    (cvT, nIdx, coff, clen, csO, csL, ssO, ssL, h1, h2) {
  cvT := IW.u64[ms];
  nIdx := IW.u64[ms + 1];
  coff := IW.u64[ms + 2]; clen := IW.u64[ms + 3];
  (csO, csL, ssO, ssL) := call check_sum_ctors(vis0, vis, EREC.u64[cvT], lpsO, lpsL,
    IW.u64[p + 4], nIdx, IW.u64[p + 6], IW.u64[p + 8], IW.u64[p + 7], cvTa, coff, clen);
  h1 := call rec2(csO, csL);
  h2 := call rec2(ssO, ssL);
  return (h1, h2)
}

/-- `check_block_ctors(vis0, vis, p, ms.off, ms.len, cvTa.off, cvTa.len)`: every member's
constructors beside its checked former (stopping at the shorter list), each wrapped as a pointer
(`List (List …)`); the block's level parameters read once. -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:224-237 ConRon.Arena.checkBlockCtors
@[l_impl ConRon.Arena.checkBlockCtors]
def checkBlockCtors : FunDecl := lfn (vis0, vis, p, msO, msL, cvO, cvL) locals
    (lpsO, lpsL, aO, aL, bO, bL) {
  (lpsO, lpsL) := call block_shape_lps(p);
  (aO, aL, bO, bL) := call check_block_ctors_go(vis0, vis, p, lpsO, lpsL, msO, msL, cvO, cvL);
  return (aO, aL, bO, bL)
}

/-- `check_block_ctors_go(vis0, vis, p, lps.off, lps.len, ms.off, ms.len, cvTa.off, cvTa.len)`:
recursion as the twin's, each member's two pointers consed onto the rest's slices (`sl_cons`,
D18). -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:224-237 ConRon.Arena.checkBlockCtors
@[l_impl ConRon.Arena.checkBlockCtors]
def checkBlockCtorsGo : FunDecl := lfn (vis0, vis, p, lpsO, lpsL, msO, msL, cvO, cvL) locals
    (h1, h2, aO, aL, bO, bL, o1, l1, o2, l2) {
  if msL == 0 { return (0, 0, 0, 0) };
  if cvL == 0 { return (0, 0, 0, 0) };
  (h1, h2) := call check_block_ctors_one(vis0, vis, p, lpsO, lpsL, IW.u64[msO], IW.u64[cvO]);
  (aO, aL, bO, bL) := call check_block_ctors_go(vis0, vis, p, lpsO, lpsL, msO + 1, msL - 1, cvO + 1, cvL - 1);
  (o1, l1) := call sl_cons(h1, aO, aL);
  (o2, l2) := call sl_cons(h2, bO, bL);
  return (o1, l1, o2, l2)
}

/-- `check_abs_ctor_sorts_one(vis, ctx, isProp, nF, tyN, hi)`: one constructor's fields' universes
at the holes. -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:239-258 ConRon.Arena.checkAbsCtorSorts
@[l_impl ConRon.Arena.checkAbsCtorSorts]
def checkAbsCtorSortsOne : FunDecl := lfn (vis, ctx, isProp, nF, tyN, hi) locals
    (srt, ok, fvsO, fvsL, body, so, sl) {
  srt := IW.u64[ctx + 9];
  if hi + nF < hi { abort };
  (ok, fvsO, fvsL, body) := call open_pis_at_fvars_f(nF, tyN, hi);
  if ok == 0 { abort };
  (so, sl) := call check_struct_field_sorts_i(vis, isProp, 0, srt, hi, fvsO, fvsL, 0, 0, nF);
  return 0
}

/-- `check_abs_ctor_sorts(vis, ctx, isProp, c.off, c.len, o.off, o.len)`: the fields' universes at
the holes, pairwise over the constructors `c` (`[cv, nF]` pointers) and their positivity normal
forms `o` (`[k.off, k.len, e]` pointers), stopping at the shorter list; recursion as the
twin's. -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:239-258 ConRon.Arena.checkAbsCtorSorts
@[l_impl ConRon.Arena.checkAbsCtorSorts]
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
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:260-268 ConRon.Arena.checkAbsCtorSortsAll
@[l_impl ConRon.Arena.checkAbsCtorSortsAll]
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

/-- `block_nest_ctx(vis, p, cvTas.off, cvTas.len)`: the walk's context — the canonical parameter
variables are the first former's opened telescope, with the members' holes (the parameters' and
members' counts summing past `2^64` a capacity abort). -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:270-284 ConRon.Arena.blockNestCtx
@[l_impl ConRon.Arena.blockNestCtx]
def blockNestCtx : FunDecl := lfn (vis, p, cvO, cvL) locals
    (cvTa0, ok, pqO, pqL, body, ctx, ok2, hO, hL) {
  if cvL == 0 { abort };
  if IW.u64[p + 4] + IW.u64[p + 1] < IW.u64[p + 4] { abort };
  cvTa0 := IW.u64[cvO];
  (ok, pqO, pqL, body) := call open_pis_at_fvars_f(IW.u64[p + 4], EREC.u64[cvTa0 + 3], 0);
  if ok == 0 { abort };
  if pqL + IW.u64[p + 1] < pqL { abort };
  ctx := call block_shape_nest_ctx(p, pqO, pqL);
  (ok2, hO, hL) := call nest_holes(vis, ctx);
  if ok2 == 0 { abort };
  return (ctx, hO, hL)
}

/-- `check_block_positivity_init()`: `{}`, a fresh all-zero `NestState` (three empty lists). -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:286-302 ConRon.Arena.checkBlockPositivity
@[l_impl ConRon.Arena.checkBlockPositivity]
def checkBlockPositivityInit : FunDecl := lfn () locals (q) {
  q := call iw_alloc(6);
  IW.u64[q] := 0; IW.u64[q + 1] := 0; IW.u64[q + 2] := 0;
  IW.u64[q + 3] := 0; IW.u64[q + 4] := 0; IW.u64[q + 5] := 0;
  return q
}

/-- `check_block_positivity_nfs_member(o, l)`: one member's normal forms `pairs.map (·.2)` from its
`(kinds × eidx)` pointer list `(o, l)` (word `2` of each record), a fresh handle slice; recursion as
the twin's `map`, each handle consed onto the rest's slice (`sl_cons`, D18). -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:286-302 ConRon.Arena.checkBlockPositivity
@[l_impl ConRon.Arena.checkBlockPositivity]
def checkBlockPositivityNfsMember : FunDecl := lfn (o, l) locals (e, ro, rl, qo, ql) {
  if l == 0 { return (0, 0) };
  e := IW.u64[o];
  (ro, rl) := call check_block_positivity_nfs_member(o + 1, l - 1);
  (qo, ql) := call sl_cons(IW.u64[e + 2], ro, rl);
  return (qo, ql)
}

/-- `check_block_positivity_nfs(outs.off, outs.len)`: `outs.map (·.map (·.2))`, each member's
handle slice wrapped as a fresh `[off, len]` pointer (`rec2`), consed onto the rest's slice
(`sl_cons`, D18). The kinds `outs.map (·.map (·.1))` need no copy: a `(kinds, eidx)` record's
first two words are its kinds' `[off, len]`, so `outs` itself reads as the kinds. -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:286-302 ConRon.Arena.checkBlockPositivity
@[l_impl ConRon.Arena.checkBlockPositivity]
def checkBlockPositivityNfs : FunDecl := lfn (s, l) locals (mp, no, nl, hp, ro, rl, qo, ql) {
  if l == 0 { return (0, 0) };
  mp := IW.u64[s];
  (no, nl) := call check_block_positivity_nfs_member(IW.u64[mp], IW.u64[mp + 1]);
  hp := call rec2(no, nl);
  (ro, rl) := call check_block_positivity_nfs(s + 1, l - 1);
  (qo, ql) := call sl_cons(hp, ro, rl);
  return (qo, ql)
}

/-- `check_block_positivity(vis, p, cvTas.off, cvTas.len, ctorsAs.off, ctorsAs.len)`: the block's
positivity on its stored constructors, at the walk's context; returns the walk's kinds, its
normal forms and its state. -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:286-302 ConRon.Arena.checkBlockPositivity
@[l_impl ConRon.Arena.checkBlockPositivity]
def checkBlockPositivity : FunDecl := lfn (vis, p, cvO, cvL, caOff, caLen) locals
    (ctx, hO, hL, u, nsEmpty, outsO, outsL, nsPtr, z, isProp, u2, nOuterO, nOuterL) {
  (ctx, hO, hL) := call block_nest_ctx(vis, p, cvO, cvL);
  u := call nest_uniform(ctx, caOff, caLen);
  nsEmpty := call check_block_positivity_init();
  (outsO, outsL, nsPtr) := call nest_root(vis, ctx, hO, hL, caOff, caLen, nsEmpty, 0, 0);
  z := call pin_word(53);
  isProp := call lvl_eq_true(IW.u64[ctx + 9], z);
  u2 := call check_abs_ctor_sorts_all(vis, ctx, isProp, caOff, caLen, outsO, outsL);
  (nOuterO, nOuterL) := call check_block_positivity_nfs(outsO, outsL);
  return (outsO, outsL, nOuterO, nOuterL, nsPtr)
}

/-! ## Stage 2: the tail -/

/-- `check_block_idx_sorts_one(vis, p, ms, cvTa)`: one member's index binders' universes, as a
pointer `[off, len]` (`nP + nIdx` past `2^64` a capacity abort; the index binders the telescope's
tail past `nP`, the empty slice at offset `0` when there is none). -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:306-320 ConRon.Arena.checkBlockIdxSorts
@[l_impl ConRon.Arena.checkBlockIdxSorts]
def checkBlockIdxSortsOne : FunDecl := lfn (vis, p, ms, cvTa) locals
    (nP, ni, srt, k, ok, tqO, tqL, body, dOff, dLen, isO, isL, hp) {
  nP := IW.u64[p + 4]; ni := IW.u64[ms + 1]; srt := IW.u64[p + 6];
  k := nP + ni;
  if k < nP { abort };
  (ok, tqO, tqL, body) := call open_pis_at_fvars_f(k, EREC.u64[cvTa + 3], 0);
  if ok == 0 { abort };
  dOff := 0; dLen := 0;
  if nP < tqL { dOff := tqO + nP; dLen := tqL - nP };
  (isO, isL) := call check_struct_field_sorts_i(vis, 1, 0, srt, nP, dOff, dLen, 0, 0, ni);
  hp := call rec2(isO, isL);
  return hp
}

/-- `check_block_idx_sorts(vis, p, ms.off, ms.len, cvTa.off, cvTa.len)`: every member's index
binders' universes (beside its checked former), stopping at the shorter list; recursion as the
twin's, each member's pointer consed onto the rest's slice (`sl_cons`, D18). -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:306-320 ConRon.Arena.checkBlockIdxSorts
@[l_impl ConRon.Arena.checkBlockIdxSorts]
def checkBlockIdxSorts : FunDecl := lfn (vis, p, msO, msL, cvO, cvL) locals (hp, ro, rl, o, l) {
  if msL == 0 { return (0, 0) };
  if cvL == 0 { return (0, 0) };
  hp := call check_block_idx_sorts_one(vis, p, IW.u64[msO], IW.u64[cvO]);
  (ro, rl) := call check_block_idx_sorts(vis, p, msO + 1, msL - 1, cvO + 1, cvL - 1);
  (o, l) := call sl_cons(hp, ro, rl);
  return (o, l)
}

/-- `cons_block_ctors(nP, ctorsAs.off, ctorsAs.len, vis)`: the members' constructors consed,
member by member, in block order (recursion as the twin's). -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:322-328 ConRon.Arena.consBlockCtors
@[l_impl ConRon.Arena.consBlockCtors]
def consBlockCtors : FunDecl := lfn (nP, caOff, caLen, vis) locals (mp, v1, v2) {
  if caLen == 0 { return vis };
  mp := IW.u64[caOff];
  v1 := call cons_sum_ctors(nP, IW.u64[mp], IW.u64[mp + 1], vis);
  v2 := call cons_block_ctors(nP, caOff + 1, caLen - 1, v1);
  return v2
}

/-- `check_block_pass_rec(fe1, cvTas.off, cvTas.len, p, ctorsAs.off, ctorsAs.len, sortsss.off,
sortsss.len, kinds.off, kinds.len, nfs.off, nfs.len, params.off, params.len, rd, cls.off, cls.len,
tbl.off, tbl.len)`: the 19-word `BlockPass` record (layout in `IndIface`) in a fresh `IW` block. -/
-- con-ron: ConRon/Arena/Inductives/BlockTail.lean:53-74 ConRon.Arena.checkBlockPass
@[l_impl ConRon.Arena.checkBlockPass]
def checkBlockPassRec : FunDecl := lfn
    (fe1, cO, cL, p1, aO, aL, sO, sL, kO, kL, nO, nL, pO, pL, rd, mO, mL, tO, tL) locals (q) {
  q := call iw_alloc(19);
  IW.u64[q] := fe1;
  IW.u64[q + 1] := cO; IW.u64[q + 2] := cL;
  IW.u64[q + 3] := p1;
  IW.u64[q + 4] := aO; IW.u64[q + 5] := aL;
  IW.u64[q + 6] := sO; IW.u64[q + 7] := sL;
  IW.u64[q + 8] := kO; IW.u64[q + 9] := kL;
  IW.u64[q + 10] := nO; IW.u64[q + 11] := nL;
  IW.u64[q + 12] := pO; IW.u64[q + 13] := pL;
  IW.u64[q + 14] := rd;
  IW.u64[q + 15] := mO; IW.u64[q + 16] := mL;
  IW.u64[q + 17] := tO; IW.u64[q + 18] := tL;
  return q
}

/-- `check_block_pass(vis, p0, is_rec)`: one pass over the formers, the constructors and the
classes — returns a pointer to the 19-word `BlockPass` record (`check_block_pass_rec`; the words
copied from the context and the positivity state are read before the record is allocated). -/
-- con-ron: ConRon/Arena/Inductives/BlockTail.lean:53-74 ConRon.Arena.checkBlockPass
@[l_impl ConRon.Arena.checkBlockPass]
def checkBlockPass : FunDecl := lfn (vis, p0, isRec) locals
    (fe1, cvTasO, cvTasL, p1, u, ctorsAsO, ctorsAsL, sortsssO, sortsssL, ctx, holesO, holesL,
     rd, msO, msL, kindsO, kindsL, nfsO, nfsL, nsPtr, seedsO, seedsL, ns2, q) {
  (fe1, cvTasO, cvTasL, p1) := call check_block_inds(vis, p0, isRec);
  u := call flush_caches();
  (ctorsAsO, ctorsAsL, sortsssO, sortsssL) :=
    call check_block_ctors(fe1, fe1, p1, IW.u64[p1], IW.u64[p1 + 1], cvTasO, cvTasL);
  (ctx, holesO, holesL) := call block_nest_ctx(fe1, p1, cvTasO, cvTasL);
  (rd, msO, msL) := call check_block_classes(fe1, p1, IW.u64[ctx + 7], IW.u64[ctx + 8], ctorsAsO, ctorsAsL);
  (kindsO, kindsL, nfsO, nfsL, nsPtr) := call check_block_positivity(fe1, p1, cvTasO, cvTasL, ctorsAsO, ctorsAsL);
  (seedsO, seedsL) := call class_seeds(ctx, holesO, holesL, msO, msL);
  ns2 := call nest_seeds(fe1, ctx, seedsO, seedsL, nsPtr);
  q := call check_block_pass_rec(fe1, cvTasO, cvTasL, p1, ctorsAsO, ctorsAsL, sortsssO, sortsssL,
    kindsO, kindsL, nfsO, nfsL, IW.u64[ctx + 7], IW.u64[ctx + 8], rd, msO, msL,
    IW.u64[ns2 + 4], IW.u64[ns2 + 5]);
  return q
}

/-- `check_block_rec(vis, p, nested, params.off, params.len, tbl.off, tbl.len, rd, ms.off, ms.len,
block.off, block.len, cvTas.off, cvTas.len)`: the generated recursor stage, at the constructors'
environment — a thin wrapper reordering its arguments to `gen_rec_check`'s own order. -/
-- con-ron: ConRon/Arena/Inductives/BlockTail.lean:76-84 ConRon.Arena.checkBlockRec
@[l_impl ConRon.Arena.checkBlockRec]
def checkBlockRec : FunDecl := lfn
    (vis, p, nested, paramsO, paramsL, tblO, tblL, rd, msO, msL, blockO, blockL, cvO, cvL)
    locals (fe2, outO, outL) {
  (fe2, outO, outL) := call gen_rec_check(vis, p, nested, paramsO, paramsL, tblO, tblL, rd, msO, msL,
    cvO, cvL, blockO, blockL);
  return (fe2, outO, outL)
}

/-- `check_block_tables_one(p, m, cs.off, ss.off, vis)`: one structure-like member's (one
constructor, no index) projection table install (`nP + nF + 1` past `2^64` a capacity abort:
the twin's `structProjGuards` computes it in `Nat`). -/
-- con-ron: ConRon/Arena/Inductives/BlockTail.lean:86-104 ConRon.Arena.checkBlockTables
@[l_impl ConRon.Arena.checkBlockTables]
def checkBlockTablesOne : FunDecl := lfn (p, m, csOff, ssOff, vis) locals
    (ctorPtr, cA, nF, sortsPtr, sortsO, sortsL, lpsO, lpsL, guardsO, guardsL, vis2) {
  ctorPtr := IW.u64[csOff]; cA := IW.u64[ctorPtr]; nF := IW.u64[ctorPtr + 1];
  sortsPtr := IW.u64[ssOff]; sortsO := IW.u64[sortsPtr]; sortsL := IW.u64[sortsPtr + 1];
  if IW.u64[p + 4] + nF + 1 <= IW.u64[p + 4] { abort };
  (guardsO, guardsL) := call struct_proj_guards(EREC.u64[cA + 3], IW.u64[p + 4], nF, sortsO, sortsL);
  (lpsO, lpsL) := call block_shape_lps(p);
  vis2 := call check_struct_proj_table(EREC.u64[IW.u64[m]], EREC.u64[cA], lpsO, lpsL,
    IW.u64[p + 4], nF, IW.u64[p + 6], guardsO, guardsL, cA, vis);
  return vis2
}

/-- `check_block_tables(p, ms.off, ms.len, cs.off, cs.len, ss.off, ss.len, vis)`: the projection
table at every structure-like member, the three lists walked side by side, stopping at the
shortest; recursion as the twin's. -/
-- con-ron: ConRon/Arena/Inductives/BlockTail.lean:86-104 ConRon.Arena.checkBlockTables
@[l_impl ConRon.Arena.checkBlockTables]
def checkBlockTables : FunDecl := lfn (p, msO, msL, csO, csL, ssO, ssL, vis) locals
    (m, csp, ssp, vis2) {
  if msL == 0 { return vis };
  if csL == 0 { return vis };
  if ssL == 0 { return vis };
  m := IW.u64[msO];
  csp := IW.u64[csO];
  ssp := IW.u64[ssO];
  vis2 := vis;
  if IW.u64[csp + 1] == 1 {
    if IW.u64[ssp + 1] == 1 {
      if IW.u64[m + 1] == 0 {
        vis2 := call check_block_tables_one(p, m, IW.u64[csp], IW.u64[ssp], vis)
      }
    }
  };
  vis2 := call check_block_tables(p, msO + 1, msL - 1, csO + 1, csL - 1, ssO + 1, ssL - 1, vis2);
  return vis2
}

/-- `check_block_tail(block.off, block.len, q)`: the install after the pass — the index binders'
sorts, the constructors consed (with the flush entering that environment), the container bit, then
`check_block_tail_rec` (`q` a `BlockPass` pointer). -/
-- con-ron: ConRon/Arena/Inductives/BlockTail.lean:106-121 ConRon.Arena.checkBlockTail
@[l_impl ConRon.Arena.checkBlockTail]
def checkBlockTail : FunDecl := lfn (blockO, blockL, q) locals
    (env1, p, isoO, isoL, fe2, u, nested, fe4) {
  env1 := IW.u64[q];
  p := IW.u64[q + 3];
  (isoO, isoL) := call check_block_idx_sorts(env1, p, IW.u64[p], IW.u64[p + 1], IW.u64[q + 1], IW.u64[q + 2]);
  fe2 := call cons_block_ctors(IW.u64[p + 4], IW.u64[q + 4], IW.u64[q + 5], env1);
  u := call flush_caches();
  nested := call block_nested_bit(p, IW.u64[q + 8], IW.u64[q + 9]);
  fe4 := call check_block_tail_rec(blockO, blockL, q, p, fe2, nested);
  return fe4
}

/-- `check_block_tail_rec(block.off, block.len, q, p, fe2, nested)`: the rest of the tail — the
recursor stage at the constructors' environment `fe2`, the recursors consed at their majors (the
rules' lookups bounded at `fe2`), and the projection tables. -/
-- con-ron: ConRon/Arena/Inductives/BlockTail.lean:106-121 ConRon.Arena.checkBlockTail
@[l_impl ConRon.Arena.checkBlockTail]
def checkBlockTailRec : FunDecl := lfn (blockO, blockL, q, p, fe2, nested) locals
    (fe2b, outO, outL, fe3, fe4) {
  (fe2b, outO, outL) := call check_block_rec(fe2, p, nested, IW.u64[q + 12], IW.u64[q + 13],
    IW.u64[q + 17], IW.u64[q + 18], IW.u64[q + 14], IW.u64[q + 15], IW.u64[q + 16], blockO, blockL,
    IW.u64[q + 1], IW.u64[q + 2]);
  fe3 := call cons_block_recs_tf(fe2, p, 0, outO, outL, fe2b);
  fe4 := call check_block_tables(p, IW.u64[p], IW.u64[p + 1], IW.u64[q + 4], IW.u64[q + 5],
    IW.u64[q + 6], IW.u64[q + 7], fe3);
  return fe4
}

/-- `check_block(vis, boff, blen, p)`: check and install a block on the uniform route — the
distinct names, the flush, the pass at official's `is_rec`, and the install after it. -/
-- con-ron: ConRon/Arena/Inductives/BlockTail.lean:123-136 ConRon.Arena.checkBlock
@[l_impl ConRon.Arena.checkBlock]
def checkBlock : FunDecl := lfn (vis, blockO, blockL, p0) locals
    (ctO, ctL, cnO, cnL, nmO, nmL, nd1, nd2, u, raw, q, fe) {
  (ctO, ctL) := call block_shape_all_ctors(p0);
  (cnO, cnL) := call block_caps_ctor_names(ctO, ctL);
  (nmO, nmL) := call block_shape_member_names(p0);
  nd1 := call sl_nodup(cnO, cnL);
  nd2 := call sl_nodup(nmO, nmL);
  if nd1 == 0 || nd2 == 0 { fail R_DIRECT_REC_DUPLICATE };
  u := call flush_caches();
  raw := call block_raw_rec(p0);
  q := call check_block_pass(vis, p0, raw);
  fe := call check_block_tail(blockO, blockL, q);
  return fe
}

/-! ## The program, the foreign closure and the well-formedness check -/

/-- This module's L functions. -/
def indInstallFns : Prog :=
  [("block_caps_ctor_names", blockCapsCtorNames), ("block_caps_at_er_copy", blockCapsAtErCopy),
   ("block_caps_at_er_copy_go", blockCapsAtErCopyGo),
   ("block_caps_at", blockCapsAt), ("block_caps_head", blockCapsHead), ("block_caps_fin", blockCapsFin), ("block_caps_one", blockCapsOne),
   ("pi_doms_mention_any", piDomsMentionAny), ("block_raw_rec_member", blockRawRecMember), ("block_raw_rec_go", blockRawRecGo),
   ("block_raw_rec", blockRawRec), ("check_block_tele", checkBlockTele),
   ("check_block_teles", checkBlockTeles), ("check_block_doms_at", checkBlockDomsAt),
   ("check_block_agree_one", checkBlockAgreeOne), ("check_block_agree", checkBlockAgree),
   ("cons_block_inds", consBlockInds), ("ind_info_rec", indInfoRec), ("er_put5", erPut5), ("check_block_inds_cv_tas", checkBlockIndsCvTas), ("check_block_inds_cv_tas_go", checkBlockIndsCvTasGo),
   ("check_block_inds", checkBlockInds), ("block_shape_nest_ctx", blockShapeNestCtx),
   ("check_block_ctors_one", checkBlockCtorsOne), ("check_block_ctors", checkBlockCtors), ("check_block_ctors_go", checkBlockCtorsGo),
   ("check_abs_ctor_sorts_one", checkAbsCtorSortsOne), ("check_abs_ctor_sorts", checkAbsCtorSorts),
   ("check_abs_ctor_sorts_all", checkAbsCtorSortsAll), ("block_nest_ctx", blockNestCtx),
   ("check_block_positivity_init", checkBlockPositivityInit),
   ("check_block_positivity_nfs_member", checkBlockPositivityNfsMember),
   ("check_block_positivity_nfs", checkBlockPositivityNfs),
   ("check_block_positivity", checkBlockPositivity),
   ("check_block_idx_sorts_one", checkBlockIdxSortsOne), ("check_block_idx_sorts", checkBlockIdxSorts),
   ("cons_block_ctors", consBlockCtors), ("check_block_pass_rec", checkBlockPassRec),
   ("check_block_pass", checkBlockPass),
   ("check_block_rec", checkBlockRec), ("check_block_tables_one", checkBlockTablesOne),
   ("check_block_tables", checkBlockTables), ("check_block_tail", checkBlockTail),
   ("check_block_tail_rec", checkBlockTailRec),
   ("check_block", checkBlock)]

/-- Stubs for the functions of OTHER modules this module calls (arity per the naming rule; see
the module doc comment for each one's convention). -/
def indInstallForeign : Prog :=
  [("check_sum_tele", stub 4), ("check_sum_ctors", stub 13), ("cons_sum_ctors", stub 4),
   ("check_struct_field_sorts_i", stub 10), ("param_levels", stub 2),
   ("struct_proj_guards", stub 5), ("check_struct_proj_table", stub 12),
   ("mentions_any_const", stub 3), ("nest_holes", stub 2), ("nest_ctx_hi_at", stub 2),
   ("nest_uniform", stub 3), ("nest_root", stub 9), ("nest_seeds", stub 5),
   ("block_shape_with_sort", stub 2), ("block_shape_member_names", stub 1),
   ("block_shape_lps", stub 1), ("block_shape_n_idxs", stub 1),
   ("block_shape_all_ctors", stub 1), ("check_block_classes", stub 6),
   ("class_seeds", stub 5), ("gen_rec_check", stub 14), ("block_nested_bit", stub 3),
   ("cons_block_recs_tf", stub 6), ("member_names_copy", stub 3)]

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
