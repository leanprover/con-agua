module

public import ConAgua.Arena.IndIface
meta import ConAgua.Arena.IndIface

@[expose] public section

/-!
# `IndSum`: the direct-sum install's L translation (lane `induct`, worker C)

The L translation of:

* `vendor/con-ron/ConRon/Arena/Inductives/SumInstall.lean`: `checkSumTele`,
  `checkStructFieldSortsI`, `fieldDomsResolve`, `idxArgsResolve`, `checkSumCtor`,
  `checkSumCtors`, `consSumCtors`, `sumRules`; `Positivity.lean`'s `whnfTelescope` (it moved
  there upstream; its L stays here).
* `vendor/con-ron/ConRon/Arena/Inductives/StructInstall.lean`: `checkStructDomsAt`,
  `checkStructProjTable` (the checks only: the table is the block's install).
* `vendor/con-ron/ConRon/Arena/Inductives/StructParts.lean`: `paramLevels` (+ `.go`),
  `structPsAt` (+ `.go`), `structElimLevel`, `structCtorResidOk`, `structProjPs`,
  `structProjArgP`, `structProjBodiesGo`, `structProjBodies`, `mentionsConstGo`, `mentionsConst`;
  `Core.lean`'s `hasLooseBVarBIns`, `hasLooseBVarBGo`, `hasLooseBVarBFast`, `structUsedLater`
  (they moved to `Core.lean` upstream; their L stays here, one body each).

No proofs here: only the translation, tagged
`@[l_impl ConRon.Arena.T]`, plus a closure check (`indSum_wf`).

`er_from_iw` copies a freshly-built `IW` list into `EREC` (the reverse of `er_to_iw`): a list a
record keeps (an installed table's `lps`, `bodies`, a rule's fire slices) must not point into `IW`.
-/

namespace L.Ind

open L.Arena

/-! ## `er_from_iw`: the reverse of `er_to_iw` (plumbing, no twin — see the module note) -/

/-- `er_from_iw(o, l)`: an `IW` slice copied into a fresh `EREC` allocation, so that a list built
while processing (in `IW`) can be stored in a persistent record (in `EREC`). -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
@[no_expose] def erFromIw : FunDecl := lfn (o, l) locals (q, z) {
  q := call erec_alloc(l);
  z := call er_from_iw_go(q, o, l);
  return (q, l)
}

/-- `er_from_iw_go(q, o, l)`: copy the `IW` slice `(o, l)` to `EREC[q ‥]`, word by word, first to
last. Self-recursive (lane `indproofs2`: split off `er_from_iw`'s `while` loop for the proof). -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
@[no_expose] def erFromIwGo : FunDecl := lfn (q, o, l) locals (z, ez) {
  if l == 0 { return 0 };
  ez := call erec_put(q, IW.u64[o]);
  z := call er_from_iw_go(q + 1, o + 1, l - 1);
  return 0
}

/-! ## `SumInstall.lean`: the type former's telescope -/

/-- `whnf_telescope(vis, i, n, e, out.off, out.len)`: official's telescope loop — peel `n` Π
binders off `e`, reducing to weak head normal form before each binder and at the end, where it
must be a sort; binder `i` opened at the free variable `i`, the binders accumulated on the way in
(`out ++ [dom]`, `sl_snoc`). Returns `(bs.off, bs.len, s)`. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:185-210 ConRon.Arena.whnfTelescope
@[no_expose, l_impl ConRon.Arena.whnfTelescope]
def whnfTelescopeL : FunDecl := lfn (vis, i, n, e, oo, ol) locals (e', g, x, y, z, fv, b, no, nl, bo, bl, s) {
  e' := call whnf_top(vis, i, e);
  (g, x, y, z) := call e_view(e');
  if g == 2 {
    if n == 0 { return (oo, ol, x) };
    fail R_DIRECT_SUM_TYPE_FORMER_DOES
  };
  if g == 6 {
    if n == 0 { fail R_DIRECT_SUM_TYPE_FORMER };
    fv := call intern_fvar(i, x);
    if 4294967296 <= fv { abort };
    b := call instantiate1_fast(⟪CWF⟫, y, fv, 0);
    (no, nl) := call sl_snoc(oo, ol, x);
    (bo, bl, s) := call whnf_telescope(vis, i + 1, n - 1, b, no, nl);
    return (bo, bl, s)
  };
  if n == 0 { fail R_DIRECT_SUM_TYPE_FORMER };
  fail R_DIRECT_SUM_TYPE_FORMER_DOES
}

/-- `check_sum_tele(n, cvTa0)`: the type former's telescope — `n` Π binders ending in a sort (the
block's check puts a former at its telescope, `reduce_member`). Returns `(cvTa0, s)`. -/
-- con-ron: ConRon/Arena/Inductives/SumInstall.lean:31-43 ConRon.Arena.checkSumTele
@[no_expose, l_impl ConRon.Arena.checkSumTele]
def checkSumTeleL : FunDecl := lfn (n, cvTa0) locals (ok, bso, bsl, body, g, x, y, z) {
  (ok, bso, bsl, body) := call strip_pis(n, EREC⦃cvTa0 + 3⦄);
  if ok == 0 { fail R_DIRECT_SUM_TYPE_FORMER };
  if ⟦body⟧.tag != 2 { fail R_DIRECT_SUM_TYPE_FORMER };
  (g, x, y, z) := call e_view(body);
  return (cvTa0, x)
}

/-! ## `SumInstall.lean`: the constructors' stage -/

/-- `check_struct_field_sorts_i(vis, isProp, large, s, nP, fvsOff, fvsLen, idxOff, idxLen, j)`:
every field's domain has a sort over the opened constructor telescope, under official's per-field
universe bound unless the family is propositional; the fields from the last to the first (field
`j - 1`, then the fields below it), as the twin's recursion. -/
-- con-ron: ConRon/Arena/Inductives/SumInstall.lean:47-70 ConRon.Arena.checkStructFieldSortsI
@[no_expose, l_impl ConRon.Arena.checkStructFieldSortsI]
def checkStructFieldSortsIL : FunDecl :=
  lfn (vis, isProp, large, s, nP, fvsOff, fvsLen, idxOff, idxLen, j)
  locals (fv, t, ty, u, z, w) {
  if j == 0 { return 0 };
  fv := call sl_get(fvsOff, fvsLen, j - 1);
  t := call fvar_type_d(fv);
  ty := call infer_type_core(vis, nP + (j - 1), t);
  u := call ensure_sort_core(vis, nP + (j - 1), ty);
  z := call check_field_sort_bound(isProp, large, s, idxOff, idxLen, fv, u);
  w := call check_struct_field_sorts_i(vis, isProp, large, s, nP, fvsOff, fvsLen, idxOff, idxLen,
    j - 1);
  return 0
}

/-- `check_field_sort_bound(isProp, large, s, idxOff, idxLen, fv, u)`: one field's universe bound
in `check_struct_field_sorts_i_go`: `u ≤ s` unless the family is propositional, else (large
elimination) `u` is zero or `fv` is an index argument; aborts otherwise (lane `indproofs2`: split
off for the proof). -/
-- con-ron: ConRon/Arena/Inductives/SumInstall.lean:47-70 ConRon.Arena.checkStructFieldSortsI
@[no_expose, l_impl ConRon.Arena.checkStructFieldSortsI]
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

/-- `field_doms_resolve(vis0, off, len)`: every field domain resolves at the pre-block
environment (stops at the first that does not). Self-recursive on the slice, as the twin is on
the list (lane `indproofs`: rewritten from a `while` loop for the refinement). -/
-- con-ron: ConRon/Arena/Inductives/SumInstall.lean:72-79 ConRon.Arena.fieldDomsResolve
@[no_expose, l_impl ConRon.Arena.fieldDomsResolve]
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
-- con-ron: ConRon/Arena/Inductives/SumInstall.lean:81-87 ConRon.Arena.idxArgsResolve
@[no_expose, l_impl ConRon.Arena.idxArgsResolve]
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
and the per-field universe bound. -/
-- con-ron: ConRon/Arena/Inductives/SumInstall.lean:89-129 ConRon.Arena.checkSumCtor
@[no_expose, l_impl ConRon.Arena.checkSumCtor]
def checkSumCtorTailL : FunDecl :=
  lfn (vis0, vis, T, lpsOff, lpsLen, nP, nIdx, resSort, isProp, large, nF, cqOff, cqLen, cqBody)
  locals (xqOk, xqOff, xqLen, xqBody, us, hd, xfn, xargsOff, xargsLen, eqFn, eqLen, leOk, eqTake,
    idxOff, idxLen, r1, r2, u) {
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
  u := call check_struct_field_sorts_i(vis, isProp, large, resSort, nP, xqOff, xqLen, idxOff, idxLen,
    nF);
  return 0
}

/-- `check_sum_ctor(vis0, vis, T, lpsOff, lpsLen, nP, nIdx, resSort, isProp, large, cvC, nF,
cvTa)`: one constructor's type (the ordinary constant check — stored AS DECLARED —, the result
shape, the parameter pins against the opened type-former telescope); the rest is
`check_sum_ctor_tail`. -/
-- con-ron: ConRon/Arena/Inductives/SumInstall.lean:89-129 ConRon.Arena.checkSumCtor
@[no_expose, l_impl ConRon.Arena.checkSumCtor]
def checkSumCtorL : FunDecl :=
  lfn (vis0, vis, T, lpsOff, lpsLen, nP, nIdx, resSort, isProp, large, cvC, nF, cvTa)
  locals (u1, ok1, bso1, bsl1, cbody, resOk, cqOk, cqOff, cqLen, cqBody, tqOk, tqOff, tqLen, tqBody,
    tdOff, tdLen, u2, u3) {
  u1 := call check_constant_val(vis, cvC, 0);
  (ok1, bso1, bsl1, cbody) := call strip_pis(nP + nF, EREC⦃cvC + 3⦄);
  if ok1 == 0 { fail R_DIRECT_SUM_CONSTRUCTOR_TELESCOPE };
  resOk := call struct_ctor_resid_ok(T, lpsOff, lpsLen, nP, nF, nIdx, cbody);
  if resOk == 0 { fail R_DIRECT_SUM_INVALID };
  (cqOk, cqOff, cqLen, cqBody) := call open_pis_at_fvars_f(nP, EREC⦃cvC + 3⦄, 0);
  if cqOk == 0 { fail R_DIRECT_SUM_CONSTRUCTOR_TELESCOPE };
  (tqOk, tqOff, tqLen, tqBody) := call open_pis_at_fvars_f(nP, EREC⦃cvTa + 3⦄, 0);
  if tqOk == 0 { fail R_DIRECT_SUM_TYPE };
  (tdOff, tdLen) := call fvar_type_ds(tqOff, tqLen);
  u2 := call check_struct_doms_at(vis, 0, cqOff, cqLen, tdOff, tdLen, nP);
  u3 := call check_sum_ctor_tail(vis0, vis, T, lpsOff, lpsLen, nP, nIdx, resSort,
    isProp, large, nF, cqOff, cqLen, cqBody);
  return 0
}

/-- `check_sum_ctors(vis0, vis, T, lpsOff, lpsLen, nP, nIdx, resSort, isProp, large, cvTa,
ctorsOff, ctorsLen)`: all constructors' types (stage 2), in order (`ctors` a slice of pointers to
`[cv, nF]`); self-recursive on the slice, as the twin is on the list. -/
-- con-ron: ConRon/Arena/Inductives/SumInstall.lean:131-141 ConRon.Arena.checkSumCtors
@[no_expose, l_impl ConRon.Arena.checkSumCtors]
def checkSumCtorsL : FunDecl :=
  lfn (vis0, vis, T, lpsOff, lpsLen, nP, nIdx, resSort, isProp, large, cvTa, ctorsOff, ctorsLen)
  locals (c, cv, nF, u) {
  if ctorsLen == 0 { return 0 };
  if nP + nIdx < nP { abort };
  c := IW.u64[ctorsOff];
  cv := IW.u64[c];
  nF := IW.u64[c + 1];
  if nP + nF < nP { abort };
  u := call check_sum_ctor(vis0, vis, T, lpsOff, lpsLen, nP, nIdx, resSort, isProp, large, cv, nF,
    cvTa);
  u := call check_sum_ctors(vis0, vis, T, lpsOff, lpsLen, nP, nIdx, resSort, isProp, large, cvTa,
    ctorsOff + 1, ctorsLen - 1);
  return 0
}

/-- `ctor_info_rec(cv, nP, nF)`: the `.ctorInfo cv nP nF` constant record in `EREC` (`decCI` kind
4: `[4, cv's 4 words copied inline, nP, nF]`, 7 words). The name word is checked to be a handle
(lane `indproofs2`: `env_push`'s spec needs it; a decoded constant's name always is). -/
-- con-ron: ConRon/Arena/Inductives/SumInstall.lean:143-149 ConRon.Arena.consSumCtors
@[no_expose, l_impl ConRon.Arena.consSumCtors]
def ctorInfoRecL : FunDecl := lfn (cv, nP, nF) locals (rec, ez) {
  rec := call erec_alloc(7);
  ez := call erec_put(rec, 4);
  ez := call erec_put(rec + 1, EREC⦃cv⦄);
  ez := call erec_put(rec + 2, EREC⦃cv + 1⦄);
  ez := call erec_put(rec + 3, EREC⦃cv + 2⦄);
  ez := call erec_put(rec + 4, EREC⦃cv + 3⦄);
  ez := call erec_put(rec + 5, nP);
  ez := call erec_put(rec + 6, nF);
  if 4294967296 <= EREC⦃rec + 1⦄ { abort };
  return rec
}

/-- `cons_sum_ctors(nP, ctorsOff, ctorsLen, vis)`: the constructors' conses, in order (the twin
processes the head before recursing on the tail). Pure (the index push touches no term): the only
effect is the environment push. Returns the new view. Self-recursive on the slice, as the twin is on
the list (lane `indproofs2`: rewritten from a `while` loop for the refinement). -/
-- con-ron: ConRon/Arena/Inductives/SumInstall.lean:143-149 ConRon.Arena.consSumCtors
@[no_expose, l_impl ConRon.Arena.consSumCtors]
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

/-- `sum_rules(ctorsOff, ctorsLen, rhssOff, rhssLen)`: the rules, constructor `j`'s with the
generated right-hand side `j`, `.plain` (each a fresh 11-word `EREC` rule record, `EnvRec.lean`;
the unread words `0`), stopping at the shorter of the two lists, as the twin's paired match does.
Returns the rule pointers as an `IW` list. -/
-- con-ron: ConRon/Arena/Inductives/SumInstall.lean:151-157 ConRon.Arena.sumRules
@[no_expose, l_impl ConRon.Arena.sumRules]
def sumRulesL : FunDecl := lfn (cO, cL, rO, rL) locals (n, o, z) {
  n := cL;
  if rL < n { n := rL };
  o := call iw_alloc(n);
  z := call sum_rules_go(cO, cL, rO, rL, o);
  return (o, n)
}

/-- `sum_rules_go(cO, cL, rO, rL, o)`: the rules of the paired slices `(cO, cL)`, `(rO, rL)`, their
pointers written at `o, o + 1, …`; stops at the shorter. Self-recursive, as the twin is. -/
-- con-ron: ConRon/Arena/Inductives/SumInstall.lean:151-157 ConRon.Arena.sumRules
@[no_expose, l_impl ConRon.Arena.sumRules]
def sumRulesGoL : FunDecl := lfn (cO, cL, rO, rL, o) locals (c, cv, nF, rec, z, ez) {
  if cL == 0 || rL == 0 { return 0 };
  c := IW.u64[cO];
  cv := IW.u64[c];
  nF := IW.u64[c + 1];
  rec := call erec_alloc(11);
  ez := call erec_put(rec, EREC⦃cv⦄);
  ez := call erec_put(rec + 1, nF);
  ez := call erec_put(rec + 2, 0);
  ez := call erec_put(rec + 3, 0);
  ez := call erec_put(rec + 4, 0);
  ez := call erec_put(rec + 5, 0);
  ez := call erec_put(rec + 6, 0);
  ez := call erec_put(rec + 7, 0);
  ez := call erec_put(rec + 8, IW.u64[rO]);
  ez := call erec_put(rec + 9, 0);
  ez := call erec_put(rec + 10, 0);
  IW.u64[o] := rec;
  z := call sum_rules_go(cO + 1, cL - 1, rO + 1, rL - 1, o + 1);
  return 0
}

/-! ## `StructInstall.lean` -/

/-- `check_struct_doms_at(vis, off, fvsOff, fvsLen, domsOff, domsLen, n)`: the reference kernels'
binder-domain comparisons, binder by binder at its own frame (`off + j`), from the last binder to
the first (`n` the twin's own recursion count, `j = n - 1` the index it checks before recursing to
`n - 1`). No result (`Unit`): self-recursive, as the twin is, so the proof is a plain induction on
`n` (round 2: rewritten from a `while` loop to make the refinement tractable). -/
-- con-ron: ConRon/Arena/Inductives/StructInstall.lean:27-41 ConRon.Arena.checkStructDomsAt
@[no_expose, l_impl ConRon.Arena.checkStructDomsAt]
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
-- con-ron: ConRon/Arena/Inductives/StructInstall.lean:43-65 ConRon.Arena.checkStructProjTable
-- con-ron: CHANGED since 01ecb31c — `ConRon.Arena.checkStructProjTable` changed; re-check the L code and its proofs, then delete this line
@[no_expose, l_impl ConRon.Arena.checkStructProjTable]
def checkStructProjTableScopedL : FunDecl :=
  lfn (vis, nP, lpsOff, lpsLen, bodiesOff, bodiesLen) locals (b, r1, r2, r3, r4, r, ez) {
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

/-- `check_struct_proj_table(T, lpsOff, lpsLen, nP, nF, cvCa, vis)`: stage 5, the projection
table's checks: the bodies (read off the stored constructor type by substitution alone) validated
once (`check_struct_proj_table_scoped`), the structure stored (else an internal error, an `abort`)
and its table not yet taken. Nothing is pushed: the table is the block's install
(`block_tables`, `IndDeclConsts.lean`). -/
-- con-ron: ConRon/Arena/Inductives/StructInstall.lean:43-65 ConRon.Arena.checkStructProjTable
-- con-ron: CHANGED since 01ecb31c — `ConRon.Arena.checkStructProjTable` changed; re-check the L code and its proofs, then delete this line
@[no_expose, l_impl ConRon.Arena.checkStructProjTable]
def checkStructProjTableL : FunDecl :=
  lfn (T, lpsOff, lpsLen, nP, nF, cvCa, vis)
  locals (bOk, bOff, bLen, scopedOk, found, q, r) {
  (bOk, bOff, bLen) := call struct_proj_bodies(T, nP, nF, EREC⦃cvCa + 3⦄);
  if bOk == 0 { abort };
  scopedOk := call check_struct_proj_table_scoped(vis, nP, lpsOff, lpsLen, bOff, bLen);
  if bLen != nF { abort };
  if scopedOk != 1 { abort };
  (found, q) := call env_find(T, vis);
  if found == 0 { abort };
  r := call find_table(vis, T);
  if r != 0 { fail R_PROJECTION_TABLE_TAKEN };
  return 0
}

/-! ## `StructParts.lean`: level lists, spines -/

/-- `param_levels_go(off, n)`: `lps.map .param`, interned one at a time, in order (`n` the
remaining length; the head at `off` is interned, then the tail `(off + 1, n - 1)`, then consed).
Self-recursive, as the twin's `go` is (round 2: rewritten from a `while` loop). -/
-- con-ron: ConRon/Arena/Inductives/StructParts.lean:47-58 ConRon.Arena.paramLevels.go
@[no_expose, l_impl ConRon.Arena.paramLevels.go]
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
-- con-ron: ConRon/Arena/Inductives/StructParts.lean:47-58 ConRon.Arena.paramLevels
@[no_expose, l_impl ConRon.Arena.paramLevels]
def paramLevelsL : FunDecl := lfn (off, n) locals (lo, ll, us) {
  (lo, ll) := call param_levels_go(off, n);
  us := call intern_ls_iw(lo, ll);
  return us
}

/-- `struct_ps_at_go(o, nP, n, k)`: `nP`'s parameter spine as seen from `o` extra binders,
`p_k = bvar (o + nP - 1 - k)`, for `k = k, …, k + n - 1` (so the top call `n = nP, k = 0` builds
the whole spine). Self-recursive, as the twin's `go` is (round 2: rewritten from a `while` loop):
`bvar (o + nP - 1 - k)` interned first, then the rest at `(n - 1, k + 1)`, then consed. -/
-- con-ron: ConRon/Arena/Inductives/StructParts.lean:62-72 ConRon.Arena.structPsAt.go
@[no_expose, l_impl ConRon.Arena.structPsAt.go]
def structPsAtGoL : FunDecl := lfn (o, nP, n, k) locals (res, b, ro, rl, res2, len2) {
  if n == 0 { res := call iw_alloc(0); return (res, 0) };
  b := call intern_bvar(o + nP - 1 - k);
  if 4294967296 <= b { abort };
  (ro, rl) := call struct_ps_at_go(o, nP, n - 1, k + 1);
  (res2, len2) := call sl_cons(b, ro, rl);
  return (res2, len2)
}

/-- `struct_ps_at(o, nP)`: the parameter variables as seen from under `o` extra binders. -/
-- con-ron: ConRon/Arena/Inductives/StructParts.lean:62-72 ConRon.Arena.structPsAt
@[no_expose, l_impl ConRon.Arena.structPsAt]
def structPsAtL : FunDecl := lfn (o, nP) locals (ro, rl) {
  (ro, rl) := call struct_ps_at_go(o, nP, nP, 0);
  return (ro, rl)
}

/-- `struct_elim_level(elim, large)`: the recursor's elimination level: the fresh parameter at the
large eliminator, `zero` at the small one. -/
-- con-ron: ConRon/Arena/Inductives/StructParts.lean:74-78 ConRon.Arena.structElimLevel
@[no_expose, l_impl ConRon.Arena.structElimLevel]
def structElimLevelL : FunDecl := lfn (elim, large) locals (u) {
  if large != 0 { u := call intern_param(elim); return u };
  u := call intern_zero();
  return u
}

/-- `struct_ctor_resid_ok(T, lpsOff, lpsLen, nP, o, nIdx, cbody)`: a constructor residual's shape
at an indexed family: the family at exactly the parameter variables (`o` binders below the
parameter frame) followed by `nIdx` index expressions. The length guard before `sl_eq` avoids
reading past the (possibly shorter) `args` slice — the twin's `take` never reads out of bounds. -/
-- con-ron: ConRon/Arena/Inductives/StructParts.lean:82-93 ConRon.Arena.structCtorResidOk
@[no_expose, l_impl ConRon.Arena.structCtorResidOk]
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
-- con-ron: ConRon/Arena/Inductives/StructParts.lean:97-100 ConRon.Arena.structProjPs
@[no_expose, l_impl ConRon.Arena.structProjPs]
def structProjPsL : FunDecl := lfn (nP) locals (o, l) {
  (o, l) := call struct_ps_at(1, nP);
  return (o, l)
}

/-- `struct_proj_arg_p(T, j)`: the `j`-th earlier-field substitute `t.j` (`.proj T j` of the
subject). -/
-- con-ron: ConRon/Arena/Inductives/StructParts.lean:102-107 ConRon.Arena.structProjArgP
@[no_expose, l_impl ConRon.Arena.structProjArgP]
def structProjArgPL : FunDecl := lfn (T, j) locals (b, e) {
  b := call intern_bvar(0);
  e := call mk_proj(T, j, b);
  return e
}

/-! ## `StructParts.lean`: `hasLooseBVarB` (one twin for the pure walk, the cutoff and the memo) -/

/-- `has_loose_b_var_b_ins(e, i, r)`: record the answer `r` for `(e, i)` in the `hb` memo and
return it (probes again right before the put, as every insert does). -/
-- con-ron: ConRon/Arena/Core.lean:2897-2902 ConRon.Arena.hasLooseBVarBIns
@[no_expose, l_impl ConRon.Arena.hasLooseBVarBIns]
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
-- con-ron: ConRon/Arena/Core.lean:2904-2950 ConRon.Arena.hasLooseBVarBGo
@[no_expose, l_impl ConRon.Arena.hasLooseBVarBGo]
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
-- con-ron: ConRon/Arena/Core.lean:2952-2955 ConRon.Arena.hasLooseBVarBFast
@[no_expose, l_impl ConRon.Arena.hasLooseBVarBFast]
def hasLooseBVarBFastL : FunDecl := lfn (i, e) locals (u, r) {
  u := call hb_clear();
  r := call has_loose_b_var_b_go(⟪CWF⟫, i, e);
  return r
}

/-- `struct_used_later(cty, nP, j)`: field `j` is used by a later field (official's `infer_proj`'s
`has_loose_bvars(binding_body(r))` at step `j`). Its own top call (clears `hb`). -/
-- con-ron: ConRon/Arena/Core.lean:3010-3016 ConRon.Arena.structUsedLater
@[no_expose, l_impl ConRon.Arena.structUsedLater]
def structUsedLaterL : FunDecl := lfn (cty, nP, j) locals (ok, bo, bl, body, r) {
  (ok, bo, bl, body) := call strip_pis(nP + j + 1, cty);
  if ok == 0 { return 0 };
  r := call has_loose_b_var_b_fast(0, body);
  return r
}

/-- `struct_proj_bodies_go(T, k, i, h)`: the projection bodies of a recognised block, one walk of
the constructor telescope: field `i`'s domain is body `i`, the field replaced by the subject's
projection before the walk continues. Returns `(ok, off, len)` (`Option (List EIdx)`). -/
-- con-ron: ConRon/Arena/Inductives/StructParts.lean:109-129 ConRon.Arena.structProjBodiesGo
-- con-ron: CHANGED since 01ecb31c — `ConRon.Arena.structProjBodiesGo` changed; re-check the L code and its proofs, then delete this line
-- con-ron: CHANGED since 01ecb31c — below `ConRon.Arena.structProjBodiesGo`, `ConRon.Arena.instantiateLiftFast` changed; re-check the L code and its proofs, then delete this line
@[no_expose, l_impl ConRon.Arena.structProjBodiesGo]
def structProjBodiesGoL : FunDecl :=
  lfn (T, k, i, h) locals (g, x, y, z, a, b, ok2, ro, rl, no, nl) {
  if k == 0 { return (1, 0, 0) };
  if ⟦h⟧.tag != 6 { return (0, 0, 0) };
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
-- con-ron: ConRon/Arena/Inductives/StructParts.lean:131-144 ConRon.Arena.structProjBodies
-- con-ron: CHANGED since 01ecb31c — `ConRon.Arena.structProjBodies` changed; re-check the L code and its proofs, then delete this line
@[no_expose, l_impl ConRon.Arena.structProjBodies]
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
-- con-ron: ConRon/Arena/Inductives/StructParts.lean:148-190 ConRon.Arena.mentionsConstGo
@[no_expose, l_impl ConRon.Arena.mentionsConstGo]
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
-- con-ron: ConRon/Arena/Inductives/StructParts.lean:192-195 ConRon.Arena.mentionsConst
@[no_expose, l_impl ConRon.Arena.mentionsConst]
def mentionsConstL : FunDecl := lfn (T, e) locals (u, r) {
  u := call mc_clear();
  r := call mentions_const_go(⟪CWF⟫, T, e);
  return r
}

/-! ## The program, the foreign stubs, and the closure check -/

/-- This module's functions. -/
def indSumFns : Prog :=
  [("er_from_iw", erFromIw), ("er_from_iw_go", erFromIwGo),
   ("whnf_telescope", whnfTelescopeL),
   ("check_sum_tele", checkSumTeleL), ("check_struct_field_sorts_i", checkStructFieldSortsIL),
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
   ("struct_used_later", structUsedLaterL),
   ("struct_proj_bodies_go", structProjBodiesGoL), ("struct_proj_bodies", structProjBodiesL),
   ("mentions_const_go", mentionsConstGoL), ("mentions_const", mentionsConstL)]

/-- Stubs for the functions of OTHER modules this module calls: none. -/
def indSumForeign : Prog := []

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
    "sum_rules" [0, 0, 0, 0] testMem with
  | .ok ([_, 0], _) => true
  | _ => false

-- `check_struct_doms_at` at `n = 0`: no comparison, no result words.
#guard
  match run (indSumFns ++ libFns ++ stubFns ++ masterFns ++ indSumForeign) 1000
    "check_struct_doms_at" [3, 0, 0, 0, 0, 0, 0] testMem with
  | .ok ([], _) => true
  | _ => false

end L.Ind
