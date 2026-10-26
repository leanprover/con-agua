import ConAgua.Arena.IndIface
import ConAgua.Arena.Reasons

/-!
# `IndSum`: the direct-sum install's L translation (lane `induct`, worker C)

The L translation of:

* `vendor/con-ron/ConRon/Arena/Inductives/SumInstall.lean`: `whnfTelescope`, `checkSumTele` (+
  `.checkSumTeleSlow`), `checkStructFieldSortsI`, `fieldDomsResolve`, `idxArgsResolve`,
  `checkSumCtor`, `checkSumCtors`, `consSumCtors`, `sumRules`.
* `vendor/con-ron/ConRon/Arena/Inductives/StructInstall.lean`: `checkStructDomsAt`,
  `checkStructProjTable`.
* `vendor/con-ron/ConRon/Arena/Inductives/StructParts.lean`: `paramLevels` (+ `.go`),
  `structPsAt` (+ `.go`), `structElimLevel`, `structCtorResidOk`, `structProjPs`,
  `structProjArgP`, `hasLooseBVarBIns`, `hasLooseBVarBGo`, `hasLooseBVarBFast`, `structUsedLater`,
  `structUsedLaterGo`, `structUsedLaterList`, `structProjGuards` (+ `.col`, `.row`),
  `structProjBodiesGo`, `structProjBodies`, `mentionsConstGo`, `mentionsConst`.

No proofs here: only the translation, tagged
`@[l_impl ConRon.Arena.T]`, plus a closure check (`indSum_wf`).

**Gap found in `IndIface`**: nothing copies a freshly-built `IW` list into a permanent `EREC`
record (the reverse of `er_to_iw`). `checkStructProjTable` needs exactly this (its `lps`, `bodies`
and `guards` fields must survive `iw_reset`, since the projection table they sit in is installed
into the persistent environment). `erFromIw` below is a stopgap local definition (real code, not a
stub, since it only needs `erec_alloc`); it likely belongs in `libFns` since every other
persistent-record-building install routine (constructors, recursor rules, …) will eventually need
the same.
-/

namespace L.Ind

open L.Arena

/-! ## `er_from_iw`: the reverse of `er_to_iw` (plumbing, no twin — see the module note) -/

/-- `er_from_iw(o, l)`: an `IW` slice copied into a fresh `EREC` allocation, so that a list built
while processing (in `IW`) can be stored in a persistent record (in `EREC`). -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
def erFromIw : FunDecl := lfn (o, l) locals (q, z) {
  q := call erec_alloc(l);
  z := call er_from_iw_go(q, o, l);
  return (q, l)
}

/-- `er_from_iw_go(q, o, l)`: copy the `IW` slice `(o, l)` to `EREC[q ‥]`, word by word, first to
last. Self-recursive (lane `indproofs2`: split off `er_from_iw`'s `while` loop for the proof). -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
def erFromIwGo : FunDecl := lfn (q, o, l) locals (z) {
  if l == 0 { return 0 };
  EREC.u64[q] := IW.u64[o];
  z := call er_from_iw_go(q + 1, o + 1, l - 1);
  return 0
}

/-! ## `SumInstall.lean`: the type former's telescope -/

/-- `whnf_telescope(vis, i, n, e)`: peel `n` Π binders off `e`'s whnf, reducing before each binder
and at the end, where it must be a sort. Returns `(bs.off, bs.len, s)`. -/
-- con-ron: ConRon/Arena/Inductives/SumInstall.lean:37-55 ConRon.Arena.whnfTelescope
@[l_impl ConRon.Arena.whnfTelescope]
def whnfTelescopeL : FunDecl := lfn (vis, i, n, e) locals (e', g, x, y, z, fv, b, bo, bl, s, o, l) {
  e' := call whnf_top(vis, i, e);
  (g, x, y, z) := call e_view(e');
  if g == 2 && n == 0 { return (0, 0, x) };
  if g == 6 && n != 0 {
    fv := call intern_fvar(i, x);
    if 4294967296 <= fv { abort };
    b := call instantiate1_fast(⟪CWF⟫, y, fv, 0);
    (bo, bl, s) := call whnf_telescope(vis, i + 1, n - 1, b);
    (o, l) := call sl_cons(x, bo, bl);
    return (o, l, s)
  };
  fail R_DIRECT_SUM_TYPE_FORMER_DOES
}

/-- `check_sum_tele_slow(vis, cv, n, cvTa0)`: the slow arm (`cvTa0.type` is not already a
telescope ending in a sort): the whnf'd telescope, closed and checked in `cvTa0`'s place; `cv`'s
name and level parameters carry over (`{cv with type := ty}`). Returns `(cvTa, s)`. -/
-- con-ron: ConRon/Arena/Inductives/SumInstall.lean:57-85 ConRon.Arena.checkSumTele.checkSumTeleSlow
@[l_impl ConRon.Arena.checkSumTele.checkSumTeleSlow]
def checkSumTeleSlowL : FunDecl := lfn (vis, cv, n, cvTa0) locals (bo, bl, s, sortS, ty, cvTaNew, u) {
  (bo, bl, s) := call whnf_telescope(vis, 0, n, EREC.u64[cvTa0 + 3]);
  sortS := call intern_sort(s);
  if 4294967296 <= sortS { abort };
  ty := call close_telescope(bo, bl, 0, sortS);
  cvTaNew := call cv_new(EREC.u64[cv], EREC.u64[cv + 1], EREC.u64[cv + 2], ty);
  u := call check_constant_val(vis, cvTaNew);
  return (cvTaNew, s)
}

/-- `check_sum_tele(vis, cv, n, cvTa0)`: the checked declared type when it is already a syntactic
telescope of `n` Π binders ending in a sort, else the slow arm. Returns `(cvTa, s)`. -/
-- con-ron: ConRon/Arena/Inductives/SumInstall.lean:57-85 ConRon.Arena.checkSumTele
@[l_impl ConRon.Arena.checkSumTele]
def checkSumTeleL : FunDecl := lfn (vis, cv, n, cvTa0) locals (ok, bso, bsl, body, g, x, y, z, cvTaOut, s) {
  (ok, bso, bsl, body) := call strip_pis(n, EREC.u64[cvTa0 + 3]);
  if ok == 1 && (body >> 28) == 2 {
    (g, x, y, z) := call e_view(body);
    return (cvTa0, x)
  };
  (cvTaOut, s) := call check_sum_tele_slow(vis, cv, n, cvTa0);
  return (cvTaOut, s)
}

/-! ## `SumInstall.lean`: the constructors' stage -/

/-- `check_struct_field_sorts_i(vis, isProp, large, s, nP, fvsOff, fvsLen, idxOff, idxLen, n)`:
the fields' sorts over the opened constructor telescope (official's per-field universe bound
unless the family is propositional). The twin walks the fields from the last to the first
(effects in that order) and returns the sorts in field order; both happen naturally by writing
field `j`'s sort at position `j` of a pre-sized result while the recursion counts down
(`check_struct_field_sorts_i_go`). -/
-- con-ron: ConRon/Arena/Inductives/SumInstall.lean:89-113 ConRon.Arena.checkStructFieldSortsI
@[l_impl ConRon.Arena.checkStructFieldSortsI]
def checkStructFieldSortsIL : FunDecl :=
  lfn (vis, isProp, large, s, nP, fvsOff, fvsLen, idxOff, idxLen, n)
  locals (res, z) {
  res := call iw_alloc(n);
  z := call check_struct_field_sorts_i_go(vis, isProp, large, s, nP, fvsOff, fvsLen, idxOff, idxLen,
    res, n);
  return (res, n)
}

/-- `check_field_sort_bound(isProp, large, s, idxOff, idxLen, fv, u)`: one field's universe bound
in `check_struct_field_sorts_i_go`: `u ≤ s` unless the family is propositional, else (large
elimination) `u` is zero or `fv` is an index argument; aborts otherwise (lane `indproofs2`: split
off for the proof). -/
-- con-ron: ConRon/Arena/Inductives/SumInstall.lean:89-113 ConRon.Arena.checkStructFieldSortsI
@[l_impl ConRon.Arena.checkStructFieldSortsI]
def checkFieldSortBoundL : FunDecl :=
  lfn (isProp, large, s, idxOff, idxLen, fv, u) locals (r, z, eq, ct) {
  if isProp == 0 {
    r := call lv_leq_top(u, s);
    if r == 0 { fail R_RESOURCE_LIMIT_FUEL };
    if r != 2 { fail R_DIRECT_SUM_FIELD_UNIVERSE }
  } else if large != 0 {
    z := call pin_word(53);
    eq := call lvl_eq_true(u, z);
    ct := call sl_contains(idxOff, idxLen, fv);
    if eq == 0 && ct == 0 { fail R_DIRECT_SUM_LARGE }
  };
  return 0
}

/-- `check_struct_field_sorts_i_go(vis, isProp, large, s, nP, fvsOff, fvsLen, idxOff, idxLen, res,
j)`: the twin's recursion at `j`: field `j - 1` first (its sort written at `res + (j - 1)`), then
the fields below it. Self-recursive, as the twin is (lane `indproofs2`: split off
`check_struct_field_sorts_i`'s `while` loop for the proof). -/
-- con-ron: ConRon/Arena/Inductives/SumInstall.lean:89-113 ConRon.Arena.checkStructFieldSortsI
@[l_impl ConRon.Arena.checkStructFieldSortsI]
def checkStructFieldSortsIGoL : FunDecl :=
  lfn (vis, isProp, large, s, nP, fvsOff, fvsLen, idxOff, idxLen, res, j)
  locals (fv, t, ty, u, z, w) {
  if j == 0 { return 0 };
  fv := call sl_get(fvsOff, fvsLen, j - 1);
  t := call fvar_type_d(fv);
  ty := call infer_type_core(vis, nP + (j - 1), t);
  u := call ensure_sort_core(vis, nP + (j - 1), ty);
  z := call check_field_sort_bound(isProp, large, s, idxOff, idxLen, fv, u);
  IW.u64[res + (j - 1)] := u;
  w := call check_struct_field_sorts_i_go(vis, isProp, large, s, nP, fvsOff, fvsLen, idxOff, idxLen,
    res, j - 1);
  return 0
}

/-- `field_doms_resolve(vis0, off, len)`: every field domain resolves at the pre-block
environment (stops at the first that does not). Self-recursive on the slice, as the twin is on
the list (lane `indproofs`: rewritten from a `while` loop for the refinement). -/
-- con-ron: ConRon/Arena/Inductives/SumInstall.lean:115-121 ConRon.Arena.fieldDomsResolve
@[l_impl ConRon.Arena.fieldDomsResolve]
def fieldDomsResolveL : FunDecl := lfn (vis0, off, n) locals (t, r) {
  if n == 0 { return 1 };
  t := call fvar_type_d(IW.u64[off]);
  r := call consts_resolve_ffast(vis0, t);
  if r == 0 { return 0 };
  r := call field_doms_resolve(vis0, off + 1, n - 1);
  return r
}

/-- `idx_args_resolve(vis0, off, len)`: the index expressions never mention the block (stops at
the first that does). Self-recursive on the slice, as the twin is on the list (lane `indproofs`:
rewritten from a `while` loop for the refinement). -/
-- con-ron: ConRon/Arena/Inductives/SumInstall.lean:123-128 ConRon.Arena.idxArgsResolve
@[l_impl ConRon.Arena.idxArgsResolve]
def idxArgsResolveL : FunDecl := lfn (vis0, off, n) locals (r) {
  if n == 0 { return 1 };
  r := call consts_resolve_ffast(vis0, IW.u64[off]);
  if r == 0 { return 0 };
  r := call idx_args_resolve(vis0, off + 1, n - 1);
  return r
}

/-- `check_sum_ctor_tail(vis0, vis, T, lpsOff, lpsLen, nP, nIdx, resSort, isProp, large, nF, cqOff,
cqLen, cqBody)`: the second half of `checkSumCtor` (split off to keep each L function small): the
constructor's field telescope, the opened residual's shape, the pre-block field/index resolution,
and the per-field sorts. Returns `(sortsOff, sortsLen)`. -/
-- con-ron: ConRon/Arena/Inductives/SumInstall.lean:130-174 ConRon.Arena.checkSumCtor
@[l_impl ConRon.Arena.checkSumCtor]
def checkSumCtorTailL : FunDecl :=
  lfn (vis0, vis, T, lpsOff, lpsLen, nP, nIdx, resSort, isProp, large, nF, cqOff, cqLen, cqBody)
  locals (xqOk, xqOff, xqLen, xqBody, us, hd, xfn, xargsOff, xargsLen, eqFn, eqLen, leOk, eqTake,
    idxOff, idxLen, r1, r2, sortsOff, sortsLen) {
  (xqOk, xqOff, xqLen, xqBody) := call open_pis_at_fvars_f(nF, cqBody, nP);
  if xqOk == 0 { fail R_DIRECT_SUM_CONSTRUCTOR };
  us := call param_levels(lpsOff, lpsLen);
  hd := call intern_const(T, us);
  if 4294967296 <= hd { abort };
  xfn := call get_app_fn_f(⟪CWF⟫, xqBody);
  (xargsOff, xargsLen) := call get_app_args_f(⟪CWF⟫, xqBody);
  eqFn := u64(xfn == hd);
  eqLen := u64(xargsLen == nP + nIdx);
  leOk := u64(nP <= xargsLen);
  eqTake := 0;
  if leOk == 1 { eqTake := call sl_eq(xargsOff, nP, cqOff, cqLen) };
  if eqFn == 0 || eqLen == 0 || eqTake == 0 { fail R_DIRECT_SUM_OPENED };
  idxOff := xargsOff + nP;
  idxLen := xargsLen - nP;
  r1 := call field_doms_resolve(vis0, xqOff, xqLen);
  if r1 == 0 { fail R_DIRECT_SUM_FIELD };
  r2 := call idx_args_resolve(vis0, idxOff, idxLen);
  if r2 == 0 { fail R_DIRECT_SUM_INDEX };
  (sortsOff, sortsLen) :=
    call check_struct_field_sorts_i(vis, isProp, large, resSort, nP, xqOff, xqLen, idxOff, idxLen, nF);
  return (sortsOff, sortsLen)
}

/-- `check_sum_ctor(vis0, vis, T, lpsOff, lpsLen, nP, nIdx, resSort, isProp, large, cvC, nF,
cvTa)`: one constructor's type (the ordinary constant check — stored AS DECLARED —, the result
shape, the parameter pins against the opened type-former telescope); the rest is
`check_sum_ctor_tail`. Returns `(cvCa, sortsOff, sortsLen)` (`cvCa` is `cvC` itself: the twin's
`cvCa := cvC` is a pure rename). -/
-- con-ron: ConRon/Arena/Inductives/SumInstall.lean:130-174 ConRon.Arena.checkSumCtor
@[l_impl ConRon.Arena.checkSumCtor]
def checkSumCtorL : FunDecl :=
  lfn (vis0, vis, T, lpsOff, lpsLen, nP, nIdx, resSort, isProp, large, cvC, nF, cvTa)
  locals (u1, ok1, bso1, bsl1, cbody, resOk, cqOk, cqOff, cqLen, cqBody, tqOk, tqOff, tqLen, tqBody,
    tdOff, tdLen, u2, sortsOff, sortsLen) {
  u1 := call check_constant_val(vis, cvC);
  (ok1, bso1, bsl1, cbody) := call strip_pis(nP + nF, EREC.u64[cvC + 3]);
  if ok1 == 0 { fail R_DIRECT_SUM_CONSTRUCTOR_TELESCOPE };
  resOk := call struct_ctor_resid_ok(T, lpsOff, lpsLen, nP, nF, nIdx, cbody);
  if resOk == 0 { fail R_DIRECT_SUM_INVALID };
  (cqOk, cqOff, cqLen, cqBody) := call open_pis_at_fvars_f(nP, EREC.u64[cvC + 3], 0);
  if cqOk == 0 { fail R_DIRECT_SUM_CONSTRUCTOR_TELESCOPE };
  (tqOk, tqOff, tqLen, tqBody) := call open_pis_at_fvars_f(nP, EREC.u64[cvTa + 3], 0);
  if tqOk == 0 { fail R_DIRECT_SUM_TYPE };
  (tdOff, tdLen) := call fvar_type_ds(tqOff, tqLen);
  u2 := call check_struct_doms_at(vis, 0, cqOff, cqLen, tdOff, tdLen, nP);
  (sortsOff, sortsLen) := call check_sum_ctor_tail(vis0, vis, T, lpsOff, lpsLen, nP, nIdx, resSort,
    isProp, large, nF, cqOff, cqLen, cqBody);
  return (cvC, sortsOff, sortsLen)
}

/-- `check_sum_ctors(vis0, vis, T, lpsOff, lpsLen, nP, nIdx, resSort, isProp, large, cvTa,
ctorsOff, ctorsLen)`: all constructors' types (stage 2), in order (the twin processes the head
before recursing on the tail, i.e. list order). Returns `(newCtorsOff, newCtorsLen, sortsListOff,
sortsListLen)` — `newCtors`/`ctors` are slices of pointers to `[cv, nF]`, `sortsList` a slice of
pointers to `[off, len]` headers (`List (List LIdx)`). Self-recursive on the slice, as the twin is on
the list; the head's records are consed onto the rest's slices (`sl_cons`, a copy per element: every
written word lies above the old pool top, docs/deviations.md D18; lane `indproofs2`: rewritten from a
`while` loop writing into pre-allocated slices). -/
-- con-ron: ConRon/Arena/Inductives/SumInstall.lean:176-190 ConRon.Arena.checkSumCtors
@[l_impl ConRon.Arena.checkSumCtors]
def checkSumCtorsL : FunDecl :=
  lfn (vis0, vis, T, lpsOff, lpsLen, nP, nIdx, resSort, isProp, large, cvTa, ctorsOff, ctorsLen)
  locals (c, cv, nF, cvCaOut, sOff, sLen, newC, sHead, rO, rL, sO, sL, o1, l1, o2, l2) {
  if ctorsLen == 0 { return (0, 0, 0, 0) };
  if nP + nIdx < nP { abort };
  c := IW.u64[ctorsOff];
  cv := IW.u64[c];
  nF := IW.u64[c + 1];
  if nP + nF < nP { abort };
  (cvCaOut, sOff, sLen) := call check_sum_ctor(vis0, vis, T, lpsOff, lpsLen, nP, nIdx, resSort,
    isProp, large, cv, nF, cvTa);
  newC := call rec2(cvCaOut, nF);
  sHead := call rec2(sOff, sLen);
  (rO, rL, sO, sL) := call check_sum_ctors(vis0, vis, T, lpsOff, lpsLen, nP, nIdx, resSort, isProp,
    large, cvTa, ctorsOff + 1, ctorsLen - 1);
  (o1, l1) := call sl_cons(newC, rO, rL);
  (o2, l2) := call sl_cons(sHead, sO, sL);
  return (o1, l1, o2, l2)
}

/-- `ctor_info_rec(cv, nP, nF)`: the `.ctorInfo cv nP nF` constant record in `EREC` (`decCI` kind
4: `[4, cv's 4 words copied inline, nP, nF]`, 7 words). The name word is checked to be a handle
(lane `indproofs2`: `env_push`'s spec needs it; a decoded constant's name always is). -/
-- con-ron: ConRon/Arena/Inductives/SumInstall.lean:192-198 ConRon.Arena.consSumCtors
@[l_impl ConRon.Arena.consSumCtors]
def ctorInfoRecL : FunDecl := lfn (cv, nP, nF) locals (rec) {
  rec := call erec_alloc(7);
  EREC.u64[rec] := 4;
  EREC.u64[rec + 1] := EREC.u64[cv];
  EREC.u64[rec + 2] := EREC.u64[cv + 1];
  EREC.u64[rec + 3] := EREC.u64[cv + 2];
  EREC.u64[rec + 4] := EREC.u64[cv + 3];
  EREC.u64[rec + 5] := nP;
  EREC.u64[rec + 6] := nF;
  if 4294967296 <= EREC.u64[rec + 1] { abort };
  return rec
}

/-- `cons_sum_ctors(nP, ctorsOff, ctorsLen, vis)`: the constructors' conses, in order (the twin
processes the head before recursing on the tail). Pure (the index push touches no term): the only
effect is the environment push. Returns the new view. Self-recursive on the slice, as the twin is on
the list (lane `indproofs2`: rewritten from a `while` loop for the refinement). -/
-- con-ron: ConRon/Arena/Inductives/SumInstall.lean:192-198 ConRon.Arena.consSumCtors
@[l_impl ConRon.Arena.consSumCtors]
def consSumCtorsL : FunDecl := lfn (nP, ctorsOff, ctorsLen, vis) locals (c, cv, nF, rec, v, r) {
  if ctorsLen == 0 { return vis };
  c := IW.u64[ctorsOff];
  cv := IW.u64[c];
  nF := IW.u64[c + 1];
  rec := call ctor_info_rec(cv, nP, nF);
  v := call env_push(vis, rec);
  r := call cons_sum_ctors(nP, ctorsOff + 1, ctorsLen - 1, v);
  return r
}

/-- `sum_rules(vis, recName, nP, ctorsOff, ctorsLen, rhssOff, rhssLen)`: the stored rules,
constructor `j`'s with the generated right-hand side `j`, `.plain` fire, and the two rescue bits
`rec_rule_bits` stamps. `recName` is unused (as in the twin: threaded but never read). Stops at the
shorter of the two lists, as the twin's paired match does. Returns the `EREC` rule pointers as an
`IW` list. -/
-- con-ron: ConRon/Arena/Inductives/SumInstall.lean:200-211 ConRon.Arena.sumRules
@[l_impl ConRon.Arena.sumRules]
def sumRulesL : FunDecl :=
  lfn (vis, recName, nP, ctorsOff, ctorsLen, rhssOff, rhssLen)
  locals (n, o, z) {
  n := ctorsLen;
  if rhssLen < n { n := rhssLen };
  o := call iw_alloc(n);
  z := call sum_rules_go(vis, nP, ctorsOff, ctorsLen, rhssOff, rhssLen, o);
  return (o, n)
}

/-- `sum_rules_go(vis, nP, cO, cL, rO, rL, o)`: the rules of the paired slices `(cO, cL)`,
`(rO, rL)`, their pointers written at `o, o + 1, …`; stops at the shorter. Self-recursive, as the
twin is (lane `indproofs2`: split off `sum_rules`' `while` loop for the proof). -/
-- con-ron: ConRon/Arena/Inductives/SumInstall.lean:200-211 ConRon.Arena.sumRules
@[l_impl ConRon.Arena.sumRules]
def sumRulesGoL : FunDecl :=
  lfn (vis, nP, cO, cL, rO, rL, o) locals (c, cv, nF, ctorN, rhs, k, eta, rec, z) {
  if cL == 0 || rL == 0 { return 0 };
  c := IW.u64[cO];
  cv := IW.u64[c];
  nF := IW.u64[c + 1];
  ctorN := EREC.u64[cv];
  rhs := IW.u64[rO];
  (k, eta) := call rec_rule_bits(vis, ctorN);
  rec := call erec_alloc(11);
  EREC.u64[rec] := ctorN;
  EREC.u64[rec + 1] := nF;
  EREC.u64[rec + 2] := nP;
  EREC.u64[rec + 3] := 0;
  EREC.u64[rec + 4] := 0;
  EREC.u64[rec + 5] := 0;
  EREC.u64[rec + 6] := 0;
  EREC.u64[rec + 7] := 0;
  EREC.u64[rec + 8] := rhs;
  EREC.u64[rec + 9] := k;
  EREC.u64[rec + 10] := eta;
  IW.u64[o] := rec;
  z := call sum_rules_go(vis, nP, cO + 1, cL - 1, rO + 1, rL - 1, o + 1);
  return 0
}

/-! ## `StructInstall.lean` -/

/-- `check_struct_doms_at(vis, off, fvsOff, fvsLen, domsOff, domsLen, n)`: the reference kernels'
binder-domain comparisons, binder by binder at its own frame (`off + j`), from the last binder to
the first (`n` the twin's own recursion count, `j = n - 1` the index it checks before recursing to
`n - 1`). No result (`Unit`): self-recursive, as the twin is, so the proof is a plain induction on
`n` (round 2: rewritten from a `while` loop to make the refinement tractable). -/
-- con-ron: ConRon/Arena/Inductives/StructInstall.lean:22-37 ConRon.Arena.checkStructDomsAt
@[l_impl ConRon.Arena.checkStructDomsAt]
def checkStructDomsAtL : FunDecl := lfn (vis, off, fvsOff, fvsLen, domsOff, domsLen, n)
  locals (a, b, t, r, z) {
  if n != 0 {
    a := call sl_get(fvsOff, fvsLen, n - 1);
    b := call sl_get(domsOff, domsLen, n - 1);
    t := call fvar_type_d(a);
    r := call is_def_eq_core(vis, off + (n - 1), t, b);
    if r == 0 { fail R_DIRECT_STRUCTURE_BINDER };
    z := call check_struct_doms_at(vis, off, fvsOff, fvsLen, domsOff, domsLen, n - 1)
  }
}

/-- `check_struct_proj_table_scoped(vis, nP, lpsOff, lpsLen, bodiesOff, bodiesLen)`: the bodies'
scoping check split off `check_struct_proj_table` (the twin's `bodies.toList.allM`): for each
body, all four checks run (`&&` on already-fetched values), and the scan stops at the first body
that fails any of them. Self-recursive on the slice, as `List.allM` is on the list (lane
`indproofs2`: rewritten from a `while` loop for the proof). -/
-- con-ron: ConRon/Arena/Inductives/StructInstall.lean:39-65 ConRon.Arena.checkStructProjTable
@[l_impl ConRon.Arena.checkStructProjTable]
def checkStructProjTableScopedL : FunDecl :=
  lfn (vis, nP, lpsOff, lpsLen, bodiesOff, bodiesLen) locals (b, r1, r2, r3, r4, r) {
  if bodiesLen == 0 { return 1 };
  b := IW.u64[bodiesOff];
  r1 := call has_fvar_fast(⟪CWF⟫, b);
  r2 := call all_level_params_defined(lpsOff, lpsLen, b);
  r3 := call consts_resolve_ffast(vis, b);
  r4 := call loose_bvars_bounded_fast(⟪CWF⟫, nP + 1, b);
  if r1 == 0 && r2 == 1 && r3 == 1 && r4 == 1 {
    r := call check_struct_proj_table_scoped(vis, nP, lpsOff, lpsLen, bodiesOff + 1, bodiesLen - 1);
    return r
  };
  return 0
}

/-- `check_struct_proj_table(T, C, lpsOff, lpsLen, nP, nF, resSort, guardsOff, guardsLen, cvCa,
vis)`: stage 5, the projection table. The bodies' scoping is validated once at insertion
(`check_struct_proj_table_scoped`); the structure must be stored (else an internal error, an
`abort`) and its table not yet taken. `lps`, `bodies` and `guards` are copied into `EREC` (via
`er_from_iw`, the module note's stopgap) so the persistent table record does not point into `IW`,
which the next declaration's `iw_reset` would invalidate. The record (13 words, `EnvRec.lean`;
word `rec + 1` unused, `0`) is pushed (`env_push_table`, the twin's `IFEnv.pushTable`); the view
is unchanged and returned. -/
-- con-ron: ConRon/Arena/Inductives/StructInstall.lean:39-65 ConRon.Arena.checkStructProjTable
@[l_impl ConRon.Arena.checkStructProjTable]
def checkStructProjTableL : FunDecl :=
  lfn (T, C, lpsOff, lpsLen, nP, nF, resSort, guardsOff, guardsLen, cvCa, vis)
  locals (bOk, bOff, bLen, scopedOk, found, q, r, lo2, ll2, bo2, bl2, go2, gl2, rec, z) {
  (bOk, bOff, bLen) := call struct_proj_bodies(T, nP, nF, EREC.u64[cvCa + 3]);
  if bOk == 0 { abort };
  scopedOk := call check_struct_proj_table_scoped(vis, nP, lpsOff, lpsLen, bOff, bLen);
  if bLen != nF { abort };
  if scopedOk != 1 { abort };
  (found, q) := call env_find(T, vis);
  if found == 0 { abort };
  r := call find_table(vis, T);
  if r != 0 { fail R_PROJECTION_TABLE_TAKEN };
  (lo2, ll2) := call er_from_iw(lpsOff, lpsLen);
  (bo2, bl2) := call er_from_iw(bOff, bLen);
  (go2, gl2) := call er_from_iw(guardsOff, guardsLen);
  rec := call erec_alloc(13);
  EREC.u64[rec] := 6;
  EREC.u64[rec + 1] := 0;
  EREC.u64[rec + 2] := T;
  EREC.u64[rec + 3] := lo2;
  EREC.u64[rec + 4] := ll2;
  EREC.u64[rec + 5] := nP;
  EREC.u64[rec + 6] := C;
  EREC.u64[rec + 7] := nF;
  EREC.u64[rec + 8] := resSort;
  EREC.u64[rec + 9] := bo2;
  EREC.u64[rec + 10] := bl2;
  EREC.u64[rec + 11] := go2;
  EREC.u64[rec + 12] := gl2;
  z := call env_push_table(rec);
  return vis
}

/-! ## `StructParts.lean`: level lists, spines -/

/-- `param_levels_go(off, n)`: `lps.map .param`, interned one at a time, in order (`n` the
remaining length; the head at `off` is interned, then the tail `(off + 1, n - 1)`, then consed).
Self-recursive, as the twin's `go` is (round 2: rewritten from a `while` loop). -/
-- con-ron: ConRon/Arena/Inductives/StructParts.lean:54-65 ConRon.Arena.paramLevels.go
@[l_impl ConRon.Arena.paramLevels.go]
def paramLevelsGoL : FunDecl := lfn (off, n) locals (res, nm, u, ro, rl, res2, len2) {
  if n == 0 { res := call iw_alloc(0); return (res, 0) };
  nm := call sl_get(off, n, 0);
  u := call intern_param(nm);
  if 4294967296 <= u { abort };
  (ro, rl) := call param_levels_go(off + 1, n - 1);
  (res2, len2) := call sl_cons(u, ro, rl);
  return (res2, len2)
}

/-- `param_levels(off, len)`: the interned level list `lps.map .param`. -/
-- con-ron: ConRon/Arena/Inductives/StructParts.lean:54-65 ConRon.Arena.paramLevels
@[l_impl ConRon.Arena.paramLevels]
def paramLevelsL : FunDecl := lfn (off, n) locals (lo, ll, us) {
  (lo, ll) := call param_levels_go(off, n);
  us := call intern_ls_iw(lo, ll);
  return us
}

/-- `struct_ps_at_go(o, nP, n, k)`: `nP`'s parameter spine as seen from `o` extra binders,
`p_k = bvar (o + nP - 1 - k)`, for `k = k, …, k + n - 1` (so the top call `n = nP, k = 0` builds
the whole spine). Self-recursive, as the twin's `go` is (round 2: rewritten from a `while` loop):
`bvar (o + nP - 1 - k)` interned first, then the rest at `(n - 1, k + 1)`, then consed. -/
-- con-ron: ConRon/Arena/Inductives/StructParts.lean:69-79 ConRon.Arena.structPsAt.go
@[l_impl ConRon.Arena.structPsAt.go]
def structPsAtGoL : FunDecl := lfn (o, nP, n, k) locals (res, b, ro, rl, res2, len2) {
  if n == 0 { res := call iw_alloc(0); return (res, 0) };
  b := call intern_bvar(o + nP - 1 - k);
  if 4294967296 <= b { abort };
  (ro, rl) := call struct_ps_at_go(o, nP, n - 1, k + 1);
  (res2, len2) := call sl_cons(b, ro, rl);
  return (res2, len2)
}

/-- `struct_ps_at(o, nP)`: the parameter variables as seen from under `o` extra binders. -/
-- con-ron: ConRon/Arena/Inductives/StructParts.lean:69-79 ConRon.Arena.structPsAt
@[l_impl ConRon.Arena.structPsAt]
def structPsAtL : FunDecl := lfn (o, nP) locals (ro, rl) {
  (ro, rl) := call struct_ps_at_go(o, nP, nP, 0);
  return (ro, rl)
}

/-- `struct_elim_level(elim, large)`: the recursor's elimination level: the fresh parameter at the
large eliminator, `zero` at the small one. -/
-- con-ron: ConRon/Arena/Inductives/StructParts.lean:81-85 ConRon.Arena.structElimLevel
@[l_impl ConRon.Arena.structElimLevel]
def structElimLevelL : FunDecl := lfn (elim, large) locals (u) {
  if large != 0 { u := call intern_param(elim); return u };
  u := call intern_zero();
  return u
}

/-- `struct_ctor_resid_ok(T, lpsOff, lpsLen, nP, o, nIdx, cbody)`: a constructor residual's shape
at an indexed family: the family at exactly the parameter variables (`o` binders below the
parameter frame) followed by `nIdx` index expressions. The length guard before `sl_eq` avoids
reading past the (possibly shorter) `args` slice — the twin's `take` never reads out of bounds. -/
-- con-ron: ConRon/Arena/Inductives/StructParts.lean:89-100 ConRon.Arena.structCtorResidOk
@[l_impl ConRon.Arena.structCtorResidOk]
def structCtorResidOkL : FunDecl :=
  lfn (T, lpsOff, lpsLen, nP, o, nIdx, cbody)
  locals (us, hd, fn, argsOff, argsLen, psOff, psLen, eq1, eq2, le, eq3) {
  us := call param_levels(lpsOff, lpsLen);
  hd := call intern_const(T, us);
  if 4294967296 <= hd { abort };
  fn := call get_app_fn_f(⟪CWF⟫, cbody);
  (argsOff, argsLen) := call get_app_args_f(⟪CWF⟫, cbody);
  (psOff, psLen) := call struct_ps_at(o, nP);
  eq1 := u64(fn == hd);
  eq2 := u64(argsLen == nP + nIdx);
  le := u64(psLen <= argsLen);
  eq3 := 0;
  if le == 1 { eq3 := call sl_eq(argsOff, psLen, psOff, psLen) };
  return eq1 & eq2 & eq3
}

/-- `struct_proj_ps(nP)`: the parameter spine of the generated projection types, at the frame of
the final `∀ p⃗ (t : T p⃗), _` telescope. -/
-- con-ron: ConRon/Arena/Inductives/StructParts.lean:104-107 ConRon.Arena.structProjPs
@[l_impl ConRon.Arena.structProjPs]
def structProjPsL : FunDecl := lfn (nP) locals (o, l) {
  (o, l) := call struct_ps_at(1, nP);
  return (o, l)
}

/-- `struct_proj_arg_p(T, j)`: the `j`-th earlier-field substitute `t.j` (`.proj T j` of the
subject). -/
-- con-ron: ConRon/Arena/Inductives/StructParts.lean:109-114 ConRon.Arena.structProjArgP
@[l_impl ConRon.Arena.structProjArgP]
def structProjArgPL : FunDecl := lfn (T, j) locals (b, e) {
  b := call intern_bvar(0);
  e := call mk_proj(T, j, b);
  return e
}

/-! ## `StructParts.lean`: `hasLooseBVarB` (one twin for the pure walk, the cutoff and the memo) -/

/-- `has_loose_b_var_b_ins(e, i, r)`: record the answer `r` for `(e, i)` in the `hb` memo and
return it (probes again right before the put, as every insert does). -/
-- con-ron: ConRon/Arena/Inductives/StructParts.lean:118-123 ConRon.Arena.hasLooseBVarBIns
@[l_impl ConRon.Arena.hasLooseBVarBIns]
def hasLooseBVarBInsL : FunDecl := lfn (e, i, r) locals (fd, j, d, u) {
  (fd, j, d) := call hb_find(e, i);
  u := call hb_put(e, i, r, fd, j);
  return r
}

/-- `has_loose_b_var_b_go(f, i, h)`: does `bvar i` occur loose in `h`? The twin's fuel `f` (abort at
`0`, the children and `bvar_b` at `f - 1`), then the `bvarB` cutoff (no memo touch below it), then
the tag: `bvar`/`fvar`/`sort`/`const`/`lit` direct answers, the rest (`app`, `lam`, `forallE`,
`letE`, `proj`) through the `hb` memo, short-circuiting at the first `true` child (as the twin's
`match` does for `app`/`lam`/`forallE`/`letE`). The twin's `memo` is dropped (the memo is the `hb`
array, per `IndIface`'s per-call-memo convention). -/
-- con-ron: ConRon/Arena/Inductives/StructParts.lean:125-171 ConRon.Arena.hasLooseBVarBGo
@[l_impl ConRon.Arena.hasLooseBVarBGo]
def hasLooseBVarBGoL : FunDecl :=
  lfn (f, i, h) locals (bb, g, x, y, z, fd, j, d, r1, r) {
  if f == 0 { abort };
  bb := call bvar_b(f - 1, h);
  if bb <= i { return 0 };
  (g, x, y, z) := call e_view(h);
  if g == 0 { return u64(i == x) };
  if g == 1 || g == 2 || g == 3 || g == 8 { return 0 };
  if i >= 4294967296 { abort };
  (fd, j, d) := call hb_find(h, i);
  if fd != 0 { return HBM.u64[j * 4 + 3] };
  if g == 4 {
    r1 := call has_loose_b_var_b_go(f - 1, i, x);
    if r1 == 1 { r := 1 } else { r := call has_loose_b_var_b_go(f - 1, i, y) }
  } else if g == 5 || g == 6 {
    r1 := call has_loose_b_var_b_go(f - 1, i, x);
    if r1 == 1 { r := 1 } else { r := call has_loose_b_var_b_go(f - 1, i + 1, y) }
  } else if g == 7 {
    r1 := call has_loose_b_var_b_go(f - 1, i, x);
    if r1 == 1 { r := 1 }
    else {
      r1 := call has_loose_b_var_b_go(f - 1, i, y);
      if r1 == 1 { r := 1 } else { r := call has_loose_b_var_b_go(f - 1, i + 1, z) }
    }
  } else { r := call has_loose_b_var_b_go(f - 1, i, z) };
  r := call has_loose_b_var_b_ins(h, i, r);
  return r
}

/-- `has_loose_b_var_b_fast(i, e)`: the executed `hasLooseBVarB` — clear the `hb` memo, walk. -/
-- con-ron: ConRon/Arena/Inductives/StructParts.lean:173-176 ConRon.Arena.hasLooseBVarBFast
@[l_impl ConRon.Arena.hasLooseBVarBFast]
def hasLooseBVarBFastL : FunDecl := lfn (i, e) locals (u, r) {
  u := call hb_clear();
  r := call has_loose_b_var_b_go(⟪CWF⟫, i, e);
  return r
}

/-- `struct_used_later(cty, nP, j)`: field `j` is used by a later field (official's `infer_proj`'s
`has_loose_bvars(binding_body(r))` at step `j`). Its own top call (clears `hb`). -/
-- con-ron: ConRon/Arena/Inductives/StructParts.lean:178-184 ConRon.Arena.structUsedLater
@[l_impl ConRon.Arena.structUsedLater]
def structUsedLaterL : FunDecl := lfn (cty, nP, j) locals (ok, bo, bl, body, r) {
  (ok, bo, bl, body) := call strip_pis(nP + j + 1, cty);
  if ok == 0 { return 0 };
  r := call has_loose_b_var_b_fast(0, body);
  return r
}

/-- `struct_used_later_go(cty, nP, j)`: memoized `structUsedLater`, sharing the caller's `hb`
memo (no clear). -/
-- con-ron: ConRon/Arena/Inductives/StructParts.lean:186-192 ConRon.Arena.structUsedLaterGo
@[l_impl ConRon.Arena.structUsedLaterGo]
def structUsedLaterGoL : FunDecl := lfn (cty, nP, j) locals (ok, bo, bl, body, r) {
  (ok, bo, bl, body) := call strip_pis(nP + j + 1, cty);
  if ok == 0 { return 0 };
  r := call has_loose_b_var_b_go(⟪CWF⟫, 0, body);
  return r
}

/-- `struct_used_later_list(cty, nP, n, base)`: `structUsedLater cty nP j` for `j = base, …, base +
n - 1`, in order, through one shared `hb` memo (no clear: the caller owns it). Self-recursive, as the
twin is (lane `indproofs`: rewritten from a `while` loop for the refinement; the conses copy,
quadratic in the field count). -/
-- con-ron: ConRon/Arena/Inductives/StructParts.lean:194-203 ConRon.Arena.structUsedLaterList
@[l_impl ConRon.Arena.structUsedLaterList]
def structUsedLaterListL : FunDecl := lfn (cty, nP, n, base) locals (res, r, ro, rl, o, l) {
  if n == 0 { res := call iw_alloc(0); return (res, 0) };
  r := call struct_used_later_go(cty, nP, base);
  (ro, rl) := call struct_used_later_list(cty, nP, n - 1, base + 1);
  (o, l) := call sl_cons(r, ro, rl);
  return (o, l)
}

/-- `struct_proj_guards_col(usedOff, usedLen, sortsOff, sortsLen, z, j, k, acc)`: the twin's `col j
k acc` (the join of `acc` with the sorts of the used fields `j, …, j + k - 1`). Self-recursive, as
the twin is (lane `indproofs`: rewritten from a `while` loop for the refinement; `used` read with
the twin's `getD _ false`, the joined level guarded below `2^32`). -/
-- con-ron: ConRon/Arena/Inductives/StructParts.lean:205-230 ConRon.Arena.structProjGuards.col
@[l_impl ConRon.Arena.structProjGuards.col]
def structProjGuardsColL : FunDecl :=
  lfn (usedOff, usedLen, sortsOff, sortsLen, z, j, k, acc) locals (u, sj, m, r) {
  if k == 0 { return acc };
  u := call sl_getd(usedOff, usedLen, j, 0);
  if u != 0 {
    sj := call sl_getd(sortsOff, sortsLen, j, z);
    m := call intern_max(acc, sj);
    if 4294967296 <= m { abort };
    r := call struct_proj_guards_col(usedOff, usedLen, sortsOff, sortsLen, z, j + 1, k - 1, m);
    return r
  };
  r := call struct_proj_guards_col(usedOff, usedLen, sortsOff, sortsLen, z, j + 1, k - 1, acc);
  return r
}

/-- `struct_proj_guards_row(usedOff, usedLen, sortsOff, sortsLen, z, i, k)`: the twin's `row i k`:
field `i'`s guard for `i' = i, …, i + k - 1`. Self-recursive, as the twin is (lane `indproofs`:
rewritten from a `while` loop; the conses copy, quadratic in the field count). -/
-- con-ron: ConRon/Arena/Inductives/StructParts.lean:205-230 ConRon.Arena.structProjGuards.row
@[l_impl ConRon.Arena.structProjGuards.row]
def structProjGuardsRowL : FunDecl :=
  lfn (usedOff, usedLen, sortsOff, sortsLen, z, i, k) locals (res, acc, g, ro, rl, o, l) {
  if k == 0 { res := call iw_alloc(0); return (res, 0) };
  acc := call sl_getd(sortsOff, sortsLen, i, z);
  g := call struct_proj_guards_col(usedOff, usedLen, sortsOff, sortsLen, z, 0, i, acc);
  (ro, rl) := call struct_proj_guards_row(usedOff, usedLen, sortsOff, sortsLen, z, i + 1, k - 1);
  (o, l) := call sl_cons(g, ro, rl);
  return (o, l)
}

/-- `struct_proj_guards(cty, nP, nF, sortsOff, sortsLen)`: the projection guard levels, one per
field: its own sort joined with the sorts of the earlier fields a later field uses. Its own top
call (clears `hb` once, the shared `∅` of the twin's `structUsedLaterList ... ∅ ...`). -/
-- con-ron: ConRon/Arena/Inductives/StructParts.lean:205-230 ConRon.Arena.structProjGuards
@[l_impl ConRon.Arena.structProjGuards]
def structProjGuardsL : FunDecl :=
  lfn (cty, nP, nF, sortsOff, sortsLen) locals (z, u, usedOff, usedLen, ro, rl) {
  z := call pin_word(53);
  u := call hb_clear();
  (usedOff, usedLen) := call struct_used_later_list(cty, nP, nF, 0);
  (ro, rl) := call struct_proj_guards_row(usedOff, usedLen, sortsOff, sortsLen, z, 0, nF);
  return (ro, rl)
}

/-- `struct_proj_bodies_go(T, k, i, h)`: the projection bodies of a recognised block, one walk of
the constructor telescope: field `i`'s domain is body `i`, the field replaced by the subject's
projection before the walk continues. Returns `(ok, off, len)` (`Option (List EIdx)`). -/
-- con-ron: ConRon/Arena/Inductives/StructParts.lean:232-248 ConRon.Arena.structProjBodiesGo
@[l_impl ConRon.Arena.structProjBodiesGo]
def structProjBodiesGoL : FunDecl :=
  lfn (T, k, i, h) locals (g, x, y, z, a, b, ok2, ro, rl, no, nl) {
  if k == 0 { return (1, 0, 0) };
  if h >> 28 != 6 { return (0, 0, 0) };
  (g, x, y, z) := call e_view(h);
  a := call struct_proj_arg_p(T, i);
  if 4294967296 <= a { abort };
  b := call instantiate1_lift_fast(⟪CWF⟫, y, a, 0);
  (ok2, ro, rl) := call struct_proj_bodies_go(T, k - 1, i + 1, b);
  if ok2 == 0 { return (0, 0, 0) };
  (no, nl) := call sl_cons(x, ro, rl);
  return (1, no, nl)
}

/-- `struct_proj_bodies(T, nP, nF, cty)`: the block's projection bodies, as the table stores
them. Returns `(ok, off, len)` (`Option (Array EIdx)`, an `IW` slice either way). -/
-- con-ron: ConRon/Arena/Inductives/StructParts.lean:250-259 ConRon.Arena.structProjBodies
@[l_impl ConRon.Arena.structProjBodies]
def structProjBodiesL : FunDecl :=
  lfn (T, nP, nF, cty) locals (psOff, psLen, ok1, e1, ok2, bo, bl) {
  (psOff, psLen) := call struct_proj_ps(nP);
  (ok1, e1) := call inst_pis_at_lift(⟪CWF⟫, psOff, psLen, cty);
  if ok1 == 0 { return (0, 0, 0) };
  (ok2, bo, bl) := call struct_proj_bodies_go(T, nF, 0, e1);
  if ok2 == 0 { return (0, 0, 0) };
  return (1, bo, bl)
}

/-! ## `StructParts.lean`: `mentionsConst` (one twin for the pure walk and the memo) -/

/-- `mentions_const_go(f, T, h)`: does the constant `T` occur in `h`? The twin's fuel `f` (abort at
`0`, the children at `f - 1`), then a syntactic walk (`fvar` annotations included; a `.proj` node
names its structure), through the `mc` memo for every kind but `bvar`/`sort`/`lit`/`const` (unlike
`hasLooseBVarBGo`, `fvar` is memoized: it recurses into the annotation). Not short-circuiting (`||`
here combines two/three already-computed results). The twin's `memo` is dropped (the memo is the
`mc` array, as in `hasLooseBVarBGo`). -/
-- con-ron: ConRon/Arena/Inductives/StructParts.lean:263-304 ConRon.Arena.mentionsConstGo
@[l_impl ConRon.Arena.mentionsConstGo]
def mentionsConstGoL : FunDecl :=
  lfn (f, T, h) locals (g, x, y, z, fd, j, d, r, b1, b2, b3, fd2, j2, d2, u2) {
  if f == 0 { abort };
  (g, x, y, z) := call e_view(h);
  if g == 0 || g == 2 || g == 8 { return 0 };
  if g == 3 { return u64(x == T) };
  (fd, j, d) := call mc_find(h, 0);
  if fd != 0 { return MCM.u64[j * 4 + 3] };
  if g == 1 { r := call mentions_const_go(f - 1, T, y) }
  else if g == 4 || g == 5 || g == 6 {
    b1 := call mentions_const_go(f - 1, T, x);
    b2 := call mentions_const_go(f - 1, T, y);
    r := b1 | b2
  } else if g == 7 {
    b1 := call mentions_const_go(f - 1, T, x);
    b2 := call mentions_const_go(f - 1, T, y);
    b3 := call mentions_const_go(f - 1, T, z);
    r := b1 | b2 | b3
  } else {
    b1 := call mentions_const_go(f - 1, T, z);
    r := u64(x == T) | b1
  };
  (fd2, j2, d2) := call mc_find(h, 0);
  u2 := call mc_put(h, 0, r, fd2, j2);
  return r
}

/-- `mentions_const(T, e)`: the executed `mentionsConst` — clear the `mc` memo, walk. -/
-- con-ron: ConRon/Arena/Inductives/StructParts.lean:306-309 ConRon.Arena.mentionsConst
@[l_impl ConRon.Arena.mentionsConst]
def mentionsConstL : FunDecl := lfn (T, e) locals (u, r) {
  u := call mc_clear();
  r := call mentions_const_go(⟪CWF⟫, T, e);
  return r
}

/-! ## `CheckerBase.lean`: the verdict at a term whose constants do not all resolve -/

/-- `has_str_lit_go(f, h)`: does `h` contain a string literal? The twin's fuel `f` (abort at `0`,
the twin's `.internal`; the children at `f - 1`), the node viewed first and the leaves decided off
the view (a literal of kind `≠ 0` is a string), then the visited set: the `mc` memo under the key
`(h, 1)` (`mentions_const_go` uses `(h, 0)`), every entry `0`, inserted before the children are
walked, so a visited node answers `0` as the twin's `memo[e]? = some _` does. Short-circuiting. -/
-- con-ron: ConRon/Arena/CheckerBase.lean:188-221 ConRon.Arena.hasStrLitGo
@[l_impl ConRon.Arena.hasStrLitGo]
def hasStrLitGoL : FunDecl := lfn (f, h) locals (g, x, y, z, t, i, fd, j, d, u, r) {
  if f == 0 { abort };
  (g, x, y, z) := call e_view(h);
  if g == 8 {
    t := ⟦h⟧.tier;
    i := ⟦h⟧.idx;
    return u64(LIT⟨t, i⟩.kind != 0)
  };
  if g == 0 || g == 2 || g == 3 { return 0 };
  (fd, j, d) := call mc_find(h, 1);
  if fd != 0 { return 0 };
  u := call mc_put(h, 1, 0, fd, j);
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

/-- `unresolved_consts_error(vis, e, w)`: the twin's `fail (← unresolvedConstsErrorL (←
strLitSupported fe) where_ e)` (`w ≤ 1`) and `fail (← unresolvedConstsError where_ e)` (`w ≥ 2`):
always aborts. `w` names the twin's `where_` (`0` "type", `1` "value", `2` "type of", `3`
"generated rule of", `4` "the domains of a generated rule of"; the reason of each message). For
`w ≤ 1`: without the String support declarations, a string literal in `e` (`has_str_lit_go` on a
cleared memo) declines. Then a term mentioning `sorryAx` (pin 13, `mentions_const`) declines,
anything else rejects. -/
-- con-ron: ConRon/Arena/CheckerBase.lean:176-186 ConRon.Arena.unresolvedConstsError
-- con-ron: ConRon/Arena/CheckerBase.lean:223-235 ConRon.Arena.unresolvedConstsErrorL
@[l_impl ConRon.Arena.unresolvedConstsError ConRon.Arena.unresolvedConstsErrorL]
def unresolvedConstsErrorL : FunDecl := lfn (vis, e, w) locals (s, u, r, sa, m) {
  if w <= 1 {
    s := call str_lit_supported(vis);
    if s == 0 {
      u := call mc_clear();
      r := call has_str_lit_go(⟪CWF⟫, e);
      if r != 0 { fail R_STRING_LITERALS_BEFORE }
    }
  };
  sa := call pin_at(13);
  m := call mentions_const(sa, e);
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

/-! ## The program, the foreign stubs, and the closure check -/

/-- This module's functions. -/
def indSumFns : Prog :=
  [("er_from_iw", erFromIw), ("er_from_iw_go", erFromIwGo),
   ("whnf_telescope", whnfTelescopeL), ("check_sum_tele_slow", checkSumTeleSlowL),
   ("check_sum_tele", checkSumTeleL), ("check_struct_field_sorts_i", checkStructFieldSortsIL),
   ("check_struct_field_sorts_i_go", checkStructFieldSortsIGoL),
   ("check_field_sort_bound", checkFieldSortBoundL),
   ("field_doms_resolve", fieldDomsResolveL), ("idx_args_resolve", idxArgsResolveL),
   ("check_sum_ctor_tail", checkSumCtorTailL), ("check_sum_ctor", checkSumCtorL),
   ("check_sum_ctors", checkSumCtorsL), ("ctor_info_rec", ctorInfoRecL),
   ("cons_sum_ctors", consSumCtorsL), ("sum_rules", sumRulesL), ("sum_rules_go", sumRulesGoL),
   ("check_struct_doms_at", checkStructDomsAtL),
   ("check_struct_proj_table_scoped", checkStructProjTableScopedL),
   ("check_struct_proj_table", checkStructProjTableL),
   ("param_levels_go", paramLevelsGoL), ("param_levels", paramLevelsL),
   ("struct_ps_at_go", structPsAtGoL), ("struct_ps_at", structPsAtL),
   ("struct_elim_level", structElimLevelL), ("struct_ctor_resid_ok", structCtorResidOkL),
   ("struct_proj_ps", structProjPsL), ("struct_proj_arg_p", structProjArgPL),
   ("has_loose_b_var_b_ins", hasLooseBVarBInsL), ("has_loose_b_var_b_go", hasLooseBVarBGoL),
   ("has_loose_b_var_b_fast", hasLooseBVarBFastL),
   ("struct_used_later", structUsedLaterL), ("struct_used_later_go", structUsedLaterGoL),
   ("struct_used_later_list", structUsedLaterListL),
   ("struct_proj_guards_col", structProjGuardsColL), ("struct_proj_guards_row", structProjGuardsRowL),
   ("struct_proj_guards", structProjGuardsL),
   ("struct_proj_bodies_go", structProjBodiesGoL), ("struct_proj_bodies", structProjBodiesL),
   ("mentions_const_go", mentionsConstGoL), ("mentions_const", mentionsConstL),
   ("has_str_lit_go", hasStrLitGoL), ("unresolved_consts_error", unresolvedConstsErrorL)]

/-- Stubs for the functions of OTHER modules this module calls: `close_telescope(bs.off, bs.len,
i, body) → e` (`ConLeche/Kernel/Inductives/Positivity.lean`'s, translated in module `IndPos`). -/
def indSumForeign : Prog := [("close_telescope", stub 4)]

/-! ## A few `#guard`s, where a function is pure enough to run without hitting a stub -/

-- `struct_ps_at` at `nP = 0`: the empty spine, no interning touched.
#guard
  match run (indSumFns ++ libFns ++ stubFns ++ masterFns ++ indSumForeign) 1000
    "struct_ps_at" [5, 0] testMem with
  | .ok ([_, 0], _) => true
  | _ => false

-- `cons_sum_ctors` on the empty constructor list: the view is unchanged.
#guard
  match run (indSumFns ++ libFns ++ stubFns ++ masterFns ++ indSumForeign) 1000
    "cons_sum_ctors" [2, 0, 0, 7] testMem with
  | .ok ([7], _) => true
  | _ => false

-- `sum_rules` on the empty constructor list: the empty rule list, no rule built.
#guard
  match run (indSumFns ++ libFns ++ stubFns ++ masterFns ++ indSumForeign) 1000
    "sum_rules" [3, 9, 2, 0, 0, 0, 0] testMem with
  | .ok ([_, 0], _) => true
  | _ => false

-- `check_struct_doms_at` at `n = 0`: no comparison, no result words.
#guard
  match run (indSumFns ++ libFns ++ stubFns ++ masterFns ++ indSumForeign) 1000
    "check_struct_doms_at" [3, 0, 0, 0, 0, 0, 0] testMem with
  | .ok ([], _) => true
  | _ => false

end L.Ind
