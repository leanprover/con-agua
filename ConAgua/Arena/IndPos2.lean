import ConAgua.Arena.IndIface

/-!
# The inductive stage in L: nested positivity, part 2 (lane `induct`, worker E)

The L translation of `vendor/con-ron/ConRon/Arena/Inductives/Positivity.lean`, from `nestInstType`
to the end of the file: the container's former (`nestInstType`), a frame constructor's residual
checks (`nestResHead`, `nestCtorNf`), a frame's helpers (`nestGroupCtors`, `nestBlockOf`,
`nestFrameMates`, `nestArity`, `nestGrowGroup`, `nestAcceptGroup`, `nestWalkStack`), the
`nestPos` mutual block (`nestFields`, `nestCtors`, `nestFrame`, `nestContNew`, `nestContKey`,
`nestCont`, `nestPos`), the member holes and uniform-occurrence checks (`nestHoles`,
`nestRootCanon`, `piDomsOcc`, `nestUniformOk`, `nestUniform`), and the root frame and the seeds
(`nestRoot`, `nestSeedOf`, `nestSeeds`).

No proofs this round: every `@[l_impl]`-tagged function here is a (hoped-)faithful translation,
checked only by `Prog.wf` (closure) and, where nothing on the path stubs out, a `#guard`.

## Conventions carried over from `IndIface.lean`

`NestKey` `[cname, lvls, ds.off, ds.len]`, `NestHole` `[key, base]`, `NestCtorNf`
`[ctor, lvls, ds.off, ds.len, ty]`, `NestCtx`
`[names.off, names.len, lps.off, lps.len, nP, nIdxs.off, nIdxs.len, params.off, params.len, sort,
lvls]`, `NestState` `[keys.off, keys.len, active.off, active.len, nfs.off, nfs.len]` (keys/active:
`NestKey` pointers; nfs: `NestCtorNf` pointers). `IConstantInfo` word `p` is the kind (3 =
`indInfo`); `cv` at `p + 1` (4 words: name, lps.off, lps.len, type); `indInfo`'s caps at `p + 5`
(15 words: … `all.off`/`all.len` at `p + 5 + 10`/`+ 11`, `nparams` at `+ 12`, `ctors.off`/`.len`
at `+ 13`/`+ 14`).

`NestKey` equality is word-wise (name, lvls, and the `ds` list all equal): `nest_key_eq`,
`nest_keys_contains` below. `nest_occ_any` is the repeated `List.anyM (nestOcc …)` pattern;
`nest_ds_closed` is the repeated `ds.allM (fvarB ≤ hiAt 0)` pattern (`nestWalkStack`,
`nestContNew`, `nestContKey` all compute exactly this). Both are untagged library-style helpers,
like `sl_eq`/`sl_contains` in `IndIface.lean`, not themselves twin functions.

Callees from module `IndPos` (stubbed here as `indPos2Foreign`, closure only — the whole program
uses the real ones): `nest_occ`, `nest_container`, `nest_crest`, `nest_canon_crest`,
`replace_fvars`, `replace_apps`, `inst_pis_with`, `close_telescope`, `whnf_walk_fuel`,
`nest_ctx_hi_at`, `nest_hole_at`. From module `IndParts`: `pi_binders`. From module `IndSum`:
`struct_used_later`.
-/

namespace L.Ind

open L.Arena
open ConRon.Arena

/-! ## Untagged helpers: `NestKey` equality, the repeated `anyM`/`allM` patterns -/

/-- `nest_key_eq(k1, k2)`: `NestKey` equality (name, lvls, and the `ds` list all equal). -/
-- con-ron: none — `NestKey` equality and membership (the twin's derived `BEq`)
def nestKeyEqL : FunDecl := lfn (k1, k2) locals (e) {
  if IW.u64[k1] != IW.u64[k2] { return 0 };
  if IW.u64[k1 + 1] != IW.u64[k2 + 1] { return 0 };
  e := call sl_eq(IW.u64[k1 + 2], IW.u64[k1 + 3], IW.u64[k2 + 2], IW.u64[k2 + 3]);
  return e
}

/-- `nest_keys_contains(off, l, k)`: `xs.contains k` over a slice of `NestKey` pointers,
recursively (like `sl_contains`). -/
-- con-ron: none — `NestKey` equality and membership (the twin's derived `BEq`)
def nestKeysContainsL : FunDecl := lfn (off, l, k) locals (r) {
  if l == 0 { return 0 };
  r := call nest_key_eq(IW.u64[off], k);
  if r != 0 { return 1 };
  r := call nest_keys_contains(off + 1, l - 1, k);
  return r
}

/-- `nest_occ_any(namesOff, namesLen, lo, hi, off, l)`: `xs.anyM (nestOcc names lo hi ·)`,
short-circuiting, recursively. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:212-216 ConRon.Arena.nestOcc
def nestOccAnyL : FunDecl := lfn (namesOff, namesLen, lo, hi, off, l) locals (b, r) {
  if l == 0 { return 0 };
  b := call nest_occ(namesOff, namesLen, lo, hi, IW.u64[off]);
  if b != 0 { return 1 };
  r := call nest_occ_any(namesOff, namesLen, lo, hi, off + 1, l - 1);
  return r
}

/-- `nest_ds_closed_go(hi0, off, l)`: the loop of `nest_ds_closed`, as a recursion. -/
-- con-ron: none — the loop of nest_ds_closed as a self-recursive function (proof shape)
def nestDsClosedGoL : FunDecl := lfn (hi0, off, l) locals (b, r) {
  if l == 0 { return 1 };
  b := call fvar_b(⟪CWF⟫, IW.u64[off]);
  if hi0 < b { return 0 };
  r := call nest_ds_closed_go(hi0, off + 1, l - 1);
  return r
}

/-- `nest_ds_closed(ctx, off, l)`: `ds.allM (fun x => do let b ← fvarB coreWalkFuel x; pure (b ≤
ctx.hiAt 0))`, short-circuiting. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:1038-1097 ConRon.Arena.nestPos
def nestDsClosedL : FunDecl := lfn (ctx, off, l) locals (hi0, r) {
  hi0 := call nest_ctx_hi_at(ctx, 0);
  r := call nest_ds_closed_go(hi0, off, l);
  return r
}

/-! ## `nestInstType`: the container's former -/

/-- Part of `nestInstType`: the instantiated, parameter-applied type `ty` (the container's
constant found, its level count and binder count checked). -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:708-744 ConRon.Arena.nestInstType
@[l_impl ConRon.Arena.nestInstType]
def nestInstTypeTyL : FunDecl := lfn (vis, key) locals
    (found, q, kind, cvC, nl, ok2, bo, bl, bdy, lo, ll, ok3, ty) {
  (found, q) := call env_find(IW.u64[key], vis);
  if found == 0 { abort };
  kind := EREC.u64[q];
  if kind != 3 { abort };
  cvC := q + 1;
  (found, nl) := call view_ls_len(IW.u64[key + 1]);
  if nl != EREC.u64[cvC + 2] { fail R_NESTED_POSITIVITY_INCORRECT };
  (ok2, bo, bl, bdy) := call strip_pis(IW.u64[key + 3], EREC.u64[cvC + 3]);
  if ok2 == 0 { fail R_NESTED_POSITIVITY_INVALID_NESTED_INDUCTIVE_DATATYPE };
  (lo, ll) := call cv_lps(cvC);
  ty := call inst_lp_fast(⟪CWF⟫, lo, ll, IW.u64[key + 1], EREC.u64[cvC + 3]);
  (ok3, ty) := call inst_pis_with(IW.u64[key + 2], IW.u64[key + 3], ty);
  if ok3 == 0 { fail R_NESTED_POSITIVITY_INVALID_NESTED_INDUCTIVE_DATATYPE };
  return ty
}

/-- `nest_inst_type(vis, ctx, hi, key)`: the index count and the container's type at the key. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:708-744 ConRon.Arena.nestInstType
@[l_impl ConRon.Arena.nestInstType]
def nestInstTypeL : FunDecl := lfn (vis, ctx, hi, key) locals
    (ty, bo, bl, res, g, s, zz1, zz2, occ, ok) {
  ty := call nest_inst_type_ty(vis, key);
  (bo, bl, res) := call pi_binders(⟪CWF⟫, ty);
  (g, s, zz1, zz2) := call e_view(res);
  if g != 2 { fail R_NESTED_POSITIVITY_INVALID_NESTED_INDUCTIVE_DATATYPE_ITS };
  occ := call nest_occ_any(IW.u64[ctx], IW.u64[ctx + 1], IW.u64[ctx + 4], hi, bo, bl);
  if occ != 0 { fail R_NESTED_POSITIVITY_A };
  ok := call lvl_eq_fueled(s, IW.u64[ctx + 9]);
  if ok == 0 { fail R_NESTED_POSITIVITY_MUTUALLY };
  return (bl, ty)
}

/-! ## `nestResHead`, `nestCtorNf` -/

/-- `nest_res_head(e)`: a constructor's result is headed by a variable (its hole). -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:746-750 ConRon.Arena.nestResHead
@[l_impl ConRon.Arena.nestResHead]
def nestResHeadL : FunDecl := lfn (e) locals (hd) {
  hd := call get_app_fn_f(⟪CWF⟫, e);
  return u64((hd >> 28) == 1)
}

/-- `nest_ctor_nf(ctx, progOff, progLen, us, dsOff, dsLen, cv, closed)`: a frame constructor's
record, read back through `FvMap.holeImg ctx prog prog.length`. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:752-762 ConRon.Arena.nestCtorNf
@[l_impl ConRon.Arena.nestCtorNf]
def nestCtorNfL : FunDecl := lfn (ctx, progOff, progLen, us, dsOff, dsLen, cv, closed) locals
    (f, ds2Off, ds2Len, ty, nf) {
  f := call rec5(0, ctx, progOff, progLen, progLen);
  (ds2Off, ds2Len) := call nest_hole_img_ds(f, dsOff, dsLen);
  ty := call replace_fvars(f, closed);
  nf := call rec5(EREC.u64[cv], us, ds2Off, ds2Len, ty);
  return nf
}

/-! ## A container frame's helpers -/

/-- `nest_block_of(vis, c)`: the recorded block of the inductive `c` (`IndCaps.all`), `[]` when
none is recorded. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:780-786 ConRon.Arena.nestBlockOf
@[l_impl ConRon.Arena.nestBlockOf]
def nestBlockOfL : FunDecl := lfn (vis, c) locals (found, q, kind) {
  (found, q) := call env_find(c, vis);
  if found == 0 { return (0, 0) };
  kind := EREC.u64[q];
  if kind != 3 { return (0, 0) };
  return (EREC.u64[q + 15], EREC.u64[q + 16])
}

/-- `nestFrameMates.go`: the group-mates accumulator, each kept once, recursively (like
`sl_contains`). The input slice `[off, off + l)` is `IndCaps.all`, hence `EREC`-resident (as
module `IndPos`'s `nest_container_ctors` reads `caps.ctors` straight out of `EREC`, no copy); the
accumulator `out` is `IW`-resident (built by `sl_snoc`). -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:788-797 ConRon.Arena.nestFrameMates.go
@[l_impl ConRon.Arena.nestFrameMates.go]
def nestFrameMatesGoL : FunDecl := lfn (c, off, l, outOff, outLen) locals (b, r1, r2) {
  if l == 0 { return (outOff, outLen) };
  b := call sl_contains(outOff, outLen, EREC.u64[off]);
  if EREC.u64[off] == c || b != 0 {
    (r1, r2) := call nest_frame_mates_go(c, off + 1, l - 1, outOff, outLen);
    return (r1, r2)
  };
  (outOff, outLen) := call sl_snoc(outOff, outLen, EREC.u64[off]);
  (r1, r2) := call nest_frame_mates_go(c, off + 1, l - 1, outOff, outLen);
  return (r1, r2)
}

/-- `nest_frame_mates(vis, c)`: a frame's group-mates (N2-eager). -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:788-797 ConRon.Arena.nestFrameMates
@[l_impl ConRon.Arena.nestFrameMates]
def nestFrameMatesL : FunDecl := lfn (vis, c) locals (bOff, bLen, outOff, outLen) {
  (bOff, bLen) := call nest_block_of(vis, c);
  (outOff, outLen) := call nest_frame_mates_go(c, bOff, bLen, 0, 0);
  return (outOff, outLen)
}

/-- `nest_arity(vis, c)`: a frame hole's full arity (its container member's recorded type's
binder count). -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:799-807 ConRon.Arena.nestArity
@[l_impl ConRon.Arena.nestArity]
def nestArityL : FunDecl := lfn (vis, c) locals (found, q, kind, ty, bo, bl, bdy) {
  (found, q) := call env_find(c, vis);
  if found == 0 { return 0 };
  kind := EREC.u64[q];
  if kind != 3 { return 0 };
  ty := EREC.u64[q + 4];
  (bo, bl, bdy) := call pi_binders(⟪CWF⟫, ty);
  return bl
}

/-- `nest_group_ctors(vis, nPc, off, l, outOff, outLen)`: the constructors of every container
in the slice, looked up and appended. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:766-778 ConRon.Arena.nestGroupCtors
@[l_impl ConRon.Arena.nestGroupCtors]
def nestGroupCtorsL : FunDecl := lfn (vis, nPc, off, l, outOff, outLen) locals
    (ok, nPc2, csOff, csLen, r1, r2) {
  if l == 0 { return (outOff, outLen) };
  (ok, nPc2, csOff, csLen) := call nest_container(vis, IW.u64[off]);
  if ok == 0 { fail R_NESTED_POSITIVITY_NON_VALID };
  if nPc2 != nPc && csLen != 0 { fail R_NESTED_POSITIVITY_NUMBER };
  (outOff, outLen) := call sl_append(outOff, outLen, csOff, csLen);
  (r1, r2) := call nest_group_ctors(vis, nPc, off + 1, l - 1, outOff, outLen);
  return (r1, r2)
}

/-- `nest_grow_group(vis, ctx, hi, us, dsOff, dsLen, csOff, csLen, grpOff, grpLen)`: a frame's
group grown by the named containers, each at the frame's instantiation. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:809-817 ConRon.Arena.nestGrowGroup
@[l_impl ConRon.Arena.nestGrowGroup]
def nestGrowGroupL : FunDecl := lfn (vis, ctx, hi, us, dsOff, dsLen, csOff, csLen, grpOff, grpLen)
    locals (c, key, nI, cty, pr, r1, r2) {
  if csLen == 0 { return (grpOff, grpLen) };
  c := IW.u64[csOff];
  key := call rec4(c, us, dsOff, dsLen);
  (nI, cty) := call nest_inst_type(vis, ctx, hi, key);
  pr := call rec2(c, cty);
  (grpOff, grpLen) := call sl_snoc(grpOff, grpLen, pr);
  (r1, r2) := call nest_grow_group(vis, ctx, hi, us, dsOff, dsLen, csOff + 1, csLen - 1, grpOff, grpLen);
  return (r1, r2)
}

/-- `nest_accept_group(us, dsOff, dsLen, grpOff, grpLen, keysOff, keysLen)`: a frame's group
accepted with its instantiation, those not cached yet, recursively (like `sl_contains`). -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:819-828 ConRon.Arena.nestAcceptGroup
@[l_impl ConRon.Arena.nestAcceptGroup]
def nestAcceptGroupL : FunDecl :=
    lfn (us, dsOff, dsLen, grpOff, grpLen, keysOff, keysLen) locals (c, key, b, r1, r2) {
  if grpLen == 0 { return (keysOff, keysLen) };
  c := IW.u64[IW.u64[grpOff]];
  key := call rec4(c, us, dsOff, dsLen);
  b := call nest_keys_contains(keysOff, keysLen, key);
  if b != 0 {
    (r1, r2) := call nest_accept_group(us, dsOff, dsLen, grpOff + 1, grpLen - 1, keysOff, keysLen);
    return (r1, r2)
  };
  (keysOff, keysLen) := call sl_snoc(keysOff, keysLen, key);
  (r1, r2) := call nest_accept_group(us, dsOff, dsLen, grpOff + 1, grpLen - 1, keysOff, keysLen);
  return (r1, r2)
}

/-- `nest_walk_stack(ctx, dsOff, dsLen, progOff, progLen)`: the frame stack an instantiation is
walked under: empty when its parameters mention no frame hole, else the frames met under. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:830-839 ConRon.Arena.nestWalkStack
@[l_impl ConRon.Arena.nestWalkStack]
def nestWalkStackL : FunDecl := lfn (ctx, dsOff, dsLen, progOff, progLen) locals (c) {
  c := call nest_ds_closed(ctx, dsOff, dsLen);
  if c != 0 { return (0, 0) };
  return (progOff, progLen)
}

/-! ## The positivity function and the container frames (one mutual block in the twin) -/

/-- `nest_fields(vis, ctx, fuel, progOff, progLen, base, nF, j, cur, ns, ksOff, ksLen, ndsOff,
ndsLen)`: a constructor's field telescope, each field through the walk at its depth. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:850-875 ConRon.Arena.nestFields
@[l_impl ConRon.Arena.nestFields]
def nestFieldsL : FunDecl :=
    lfn (vis, ctx, fuel, progOff, progLen, base, nF, j, cur, ns, ksOff, ksLen, ndsOff, ndsLen)
      locals (tag, g, a, b, zz, k, nd, ns2, bj, r0, r1, r2, r3, r4, r5) {
  if nF == 0 { return (ksOff, ksLen, ndsOff, ndsLen, cur, ns) };
  tag := cur >> 28;
  if tag != 6 { fail R_NESTED_POSITIVITY_INVALID_NESTED };
  bj := base + j;
  if bj < base { abort };
  if bj + 1 == 0 { abort };
  (g, a, b, zz) := call e_view(cur);
  (k, nd, ns2) := call nest_pos(vis, ctx, fuel, progOff, progLen, bj, 0, a, ns);
  zz := call intern_fvar(bj, a);
  if 4294967296 <= zz { abort };
  b := call instantiate1_fast(⟪CWF⟫, b, zz, 0);
  (ksOff, ksLen) := call sl_snoc(ksOff, ksLen, k);
  (ndsOff, ndsLen) := call sl_snoc(ndsOff, ndsLen, nd);
  (r0, r1, r2, r3, r4, r5) := call nest_fields(vis, ctx, fuel, progOff, progLen, base, nF - 1, j + 1, b,
    ns2, ksOff, ksLen, ndsOff, ndsLen);
  return (r0, r1, r2, r3, r4, r5)
}

/-- Part of `nestCtors`: U4 (a non-ordinary field read later, the kind tested first). -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:877-928 ConRon.Arena.nestCtors
@[l_impl ConRon.Arena.nestCtors]
def nestCtorsU4L : FunDecl := lfn (ksOff, nF, closed, i) locals (kind, su, r) {
  if nF <= i { return 0 };
  kind := IW.u64[ksOff + i];
  if kind != 0 {
    su := call struct_used_later(closed, 0, i);
    if su != 0 { return 1 }
  };
  r := call nest_ctors_u4(ksOff, nF, closed, i + 1);
  return r
}

/-- Part of `nestCtors`: the result check (headed by a hole, hole-free indices). -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:877-928 ConRon.Arena.nestCtors
@[l_impl ConRon.Arena.nestCtors]
def nestCtorsResOkL : FunDecl := lfn (ctx, hi, cur) locals (rh, argsOff, argsLen, occ) {
  rh := call nest_res_head(cur);
  if rh == 0 { return 0 };
  (argsOff, argsLen) := call get_app_args_f(⟪CWF⟫, cur);
  occ := call nest_occ_any(IW.u64[ctx], IW.u64[ctx + 1], IW.u64[ctx + 4], hi, argsOff, argsLen);
  return u64(occ == 0)
}

/-- Part of `nestCtors`: the group abstracted (`nestCrest`), TYPED at the frame's context. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:877-928 ConRon.Arena.nestCtors
@[l_impl ConRon.Arena.nestCtors]
def nestCtorsCrestL : FunDecl :=
    lfn (vis, namesOff, namesLen, us, dsOff, dsLen, holesOff, holesLen, cv, hi) locals
      (lo, ll, nodup, cty, ok, ty, zz) {
  (lo, ll) := call cv_lps(cv);
  nodup := call sl_nodup(lo, ll);
  if nodup == 0 { fail R_NESTED_POSITIVITY_INVALID };
  cty := call inst_lp_fast(⟪CWF⟫, lo, ll, us, EREC.u64[cv + 3]);
  (ok, cty) := call nest_crest(namesOff, namesLen, us, dsOff, dsLen, holesOff, holesLen, cty);
  if ok == 0 { fail R_NESTED_POSITIVITY_INVALID_NESTED_INDUCTIVE };
  ty := call infer_type_core(vis, hi, cty);
  zz := call ensure_sort_core(vis, hi, ty);
  return cty
}

/-- Part of `nestCtors`: the fields walked above `hi` (root: at the input-derived fuel; else the
enclosing walk's fuel), then closed back into a telescope. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:877-928 ConRon.Arena.nestCtors
@[l_impl ConRon.Arena.nestCtors]
def nestCtorsWalkL : FunDecl :=
    lfn (vis, ctx, root, fuel, progOff, progLen, hi, nF, crest, ns) locals
      (fuelC, f2, ndsOff, ndsLen, cur, closed, ksOff, ksLen) {
  if root != 0 { fuelC := call whnf_walk_fuel(crest); f2 := fuelC } else { f2 := fuel };
  (ksOff, ksLen, ndsOff, ndsLen, cur, ns) :=
    call nest_fields(vis, ctx, f2, progOff, progLen, hi, nF, 0, crest, ns, 0, 0, 0, 0);
  closed := call close_telescope(ndsOff, ndsLen, hi, cur);
  return (ksOff, ksLen, cur, closed, ns)
}

/-- Part of `nestCtors`: one constructor, typed, walked, checked, and recorded. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:877-928 ConRon.Arena.nestCtors
@[l_impl ConRon.Arena.nestCtors]
def nestCtorsOneL : FunDecl :=
    lfn (vis, ctx, root, fuel, progOff, progLen, hi, us, dsOff, dsLen, namesOff, namesLen,
      holesOff, holesLen, cv, nF, ns) locals
      (crest, ksOff, ksLen, cur, closed, ns2, u4, resOk, nf, nfsOff, nfsLen, nsOut) {
  crest := call nest_ctors_crest(vis, namesOff, namesLen, us, dsOff, dsLen, holesOff, holesLen,
    cv, hi);
  (ksOff, ksLen, cur, closed, ns2) :=
    call nest_ctors_walk(vis, ctx, root, fuel, progOff, progLen, hi, nF, crest, ns);
  u4 := call nest_ctors_u4(ksOff, nF, closed, 0);
  if u4 != 0 { fail R_NESTED_POSITIVITY_NON_VALID_OCCURRENCE };
  resOk := call nest_ctors_res_ok(ctx, hi, cur);
  if resOk == 0 { fail R_NESTED_POSITIVITY_INVALID_RETURN };
  nf := call nest_ctor_nf(ctx, progOff, progLen, us, dsOff, dsLen, cv, closed);
  (nfsOff, nfsLen) := call sl_snoc(IW.u64[ns2 + 4], IW.u64[ns2 + 5], nf);
  nsOut := call rec6(IW.u64[ns2], IW.u64[ns2 + 1], IW.u64[ns2 + 2], IW.u64[ns2 + 3], nfsOff,
    nfsLen);
  return (ksOff, ksLen, closed, nsOut)
}

/-- `nest_ctors(vis, ctx, root, fuel, progOff, progLen, hi, us, dsOff, dsLen, namesOff, namesLen,
holesOff, holesLen, csOff, csLen, ns, outsOff, outsLen)`: a frame's constructors, root and
container alike. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:877-928 ConRon.Arena.nestCtors
@[l_impl ConRon.Arena.nestCtors]
def nestCtorsL : FunDecl :=
    lfn (vis, ctx, root, fuel, progOff, progLen, hi, us, dsOff, dsLen, namesOff, namesLen,
      holesOff, holesLen, csOff, csLen, ns, outsOff, outsLen) locals
      (cPtr, cv, nF, ksOff, ksLen, closed, rec, ns2, r0, r1, r2) {
  if csLen == 0 { return (outsOff, outsLen, ns) };
  cPtr := IW.u64[csOff];
  cv := IW.u64[cPtr];
  nF := IW.u64[cPtr + 1];
  (ksOff, ksLen, closed, ns2) := call nest_ctors_one(vis, ctx, root, fuel, progOff, progLen, hi,
    us, dsOff, dsLen, namesOff, namesLen, holesOff, holesLen, cv, nF, ns);
  rec := call rec3(ksOff, ksLen, closed);
  (outsOff, outsLen) := call sl_snoc(outsOff, outsLen, rec);
  (r0, r1, r2) := call nest_ctors(vis, ctx, root, fuel, progOff, progLen, hi, us, dsOff, dsLen,
    namesOff, namesLen, holesOff, holesLen, csOff + 1, csLen - 1, ns2, outsOff, outsLen);
  return (r0, r1, r2)
}

/-- Part of `nestFrame`: the stack grown by the group's holes, and the group's own names. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:930-955 ConRon.Arena.nestFrame
@[l_impl ConRon.Arena.nestFrame]
def nestFrameGrpL : FunDecl :=
    lfn (hi, us, dsOff, dsLen, grpOff, grpLen, accPOff, accPLen, accNOff, accNLen) locals
      (c, key, hole, r0, r1, r2, r3) {
  if grpLen == 0 { return (accPOff, accPLen, accNOff, accNLen) };
  c := IW.u64[IW.u64[grpOff]];
  key := call rec4(c, us, dsOff, dsLen);
  hole := call rec2(key, hi);
  (accPOff, accPLen) := call sl_snoc(accPOff, accPLen, hole);
  (accNOff, accNLen) := call sl_snoc(accNOff, accNLen, c);
  (r0, r1, r2, r3) := call nest_frame_grp(hi, us, dsOff, dsLen, grpOff + 1, grpLen - 1, accPOff,
    accPLen, accNOff, accNLen);
  return (r0, r1, r2, r3)
}

/-- Part of `nestFrame`: the holes, the container's WHOLE recorded group, interned in order. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:930-955 ConRon.Arena.nestFrame
@[l_impl ConRon.Arena.nestFrame]
def nestFrameHolesL : FunDecl := lfn (hi, grpOff, grpLen, accOff, accLen) locals (hv, r0, r1) {
  if grpLen == 0 { return (accOff, accLen) };
  if hi + 1 == 0 { abort };
  hv := call intern_fvar(hi, IW.u64[IW.u64[grpOff] + 1]);
  if 4294967296 <= hv { abort };
  (accOff, accLen) := call sl_snoc(accOff, accLen, hv);
  (r0, r1) := call nest_frame_holes(hi + 1, grpOff + 1, grpLen - 1, accOff, accLen);
  return (r0, r1)
}

/-- `nest_frame(vis, ctx, fuel, progOff, progLen, hi, us, dsOff, dsLen, nPc, grpOff, grpLen,
ns)`: a container frame, at the instantiation `(us, ds)`. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:930-955 ConRon.Arena.nestFrame
@[l_impl ConRon.Arena.nestFrame]
def nestFrameL : FunDecl :=
    lfn (vis, ctx, fuel, progOff, progLen, hi, us, dsOff, dsLen, nPc, grpOff, grpLen, ns) locals
      (hn, hc, app, zz, prog2Off, prog2Len, namesOff, namesLen, ctorsOff, ctorsLen, holesOff,
        holesLen, hiTot, outsOff, outsLen, nsOut2) {
  if grpLen == 0 { hn := call intern_nanon() } else { hn := IW.u64[IW.u64[grpOff]] };
  if 4294967296 <= hn { abort };
  hc := call intern_const(hn, us);
  if 4294967296 <= hc { abort };
  app := call mk_app_n_f(hc, dsOff, dsLen);
  zz := call infer_type_core(vis, hi, app);
  (prog2Off, prog2Len, namesOff, namesLen) :=
    call nest_frame_grp(hi, us, dsOff, dsLen, grpOff, grpLen, progOff, progLen, 0, 0);
  (ctorsOff, ctorsLen) := call nest_group_ctors(vis, nPc, namesOff, namesLen, 0, 0);
  (holesOff, holesLen) := call nest_frame_holes(hi, grpOff, grpLen, 0, 0);
  hiTot := hi + grpLen;
  if hiTot < hi { abort };
  if dsLen + grpLen < dsLen { abort };
  (outsOff, outsLen, nsOut2) := call nest_ctors(vis, ctx, 0, fuel, prog2Off, prog2Len, hiTot, us,
    dsOff, dsLen, namesOff, namesLen, holesOff, holesLen, ctorsOff, ctorsLen, ns, 0, 0);
  return nsOut2
}

/-- Part of `nestContNew`: the group's keys, prepended to the state's active list. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:957-978 ConRon.Arena.nestContNew
@[l_impl ConRon.Arena.nestContNew]
def nestContNewActiveL : FunDecl :=
    lfn (us, dsOff, dsLen, grpOff, grpLen, accOff, accLen) locals (key, r0, r1) {
  if grpLen == 0 { return (accOff, accLen) };
  key := call rec4(IW.u64[IW.u64[grpOff]], us, dsOff, dsLen);
  (accOff, accLen) := call sl_snoc(accOff, accLen, key);
  (r0, r1) := call nest_cont_new_active(us, dsOff, dsLen, grpOff + 1, grpLen - 1, accOff, accLen);
  return (r0, r1)
}

/-- Part of `nestContNew`: the group cached when its parameters mention no frame hole; the
original active list restored, the kind computed. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:957-978 ConRon.Arena.nestContNew
@[l_impl ConRon.Arena.nestContNew]
def nestContNewFinishL : FunDecl :=
    lfn (ctx, us, dsOff, dsLen, grpOff, grpLen, ns2, actOff, actLen, kb) locals
      (closedB, keysOff, keysLen, nsFinal) {
  closedB := call nest_ds_closed(ctx, dsOff, dsLen);
  if closedB != 0 {
    (keysOff, keysLen) :=
      call nest_accept_group(us, dsOff, dsLen, grpOff, grpLen, IW.u64[ns2], IW.u64[ns2 + 1])
  } else {
    keysOff := IW.u64[ns2];
    keysLen := IW.u64[ns2 + 1]
  };
  nsFinal := call rec6(keysOff, keysLen, actOff, actLen, IW.u64[ns2 + 4], IW.u64[ns2 + 5]);
  return (4 + 8 * u64(kb != 0), nsFinal)
}

/-- `nest_cont_new(vis, ctx, fuel, progOff, progLen, kb, n, us, dsOff, dsLen, nPc, cty, ns)`: an
instantiation's frame: the group-mates' former checks, the frame walked with the whole group in
progress, and the group cached when closed. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:957-978 ConRon.Arena.nestContNew
@[l_impl ConRon.Arena.nestContNew]
def nestContNewL : FunDecl :=
    lfn (vis, ctx, fuel, progOff, progLen, kb, n, us, dsOff, dsLen, nPc, cty, ns) locals
      (wpOff, wpLen, matesOff, matesLen, hw, ncty, grp0Off, grp0Len, grpOff, grpLen, actOff,
        actLen, ns1, ns2, k9, n9) {
  (wpOff, wpLen) := call nest_walk_stack(ctx, dsOff, dsLen, progOff, progLen);
  (matesOff, matesLen) := call nest_frame_mates(vis, n);
  hw := call nest_ctx_hi_at(ctx, wpLen);
  ncty := call rec2(n, cty);
  (grp0Off, grp0Len) := call sl_new1(ncty);
  (grpOff, grpLen) :=
    call nest_grow_group(vis, ctx, hw, us, dsOff, dsLen, matesOff, matesLen, grp0Off, grp0Len);
  (actOff, actLen) := call nest_cont_new_active(us, dsOff, dsLen, grpOff, grpLen, 0, 0);
  (actOff, actLen) := call sl_append(actOff, actLen, IW.u64[ns + 2], IW.u64[ns + 3]);
  ns1 := call rec6(IW.u64[ns], IW.u64[ns + 1], actOff, actLen, IW.u64[ns + 4], IW.u64[ns + 5]);
  ns2 := call nest_frame(vis, ctx, fuel, wpOff, wpLen, hw, us, dsOff, dsLen, nPc, grpOff, grpLen,
    ns1);
  (k9, n9) := call nest_cont_new_finish(ctx, us, dsOff, dsLen, grpOff, grpLen, ns2,
    IW.u64[ns + 2], IW.u64[ns + 3], kb);
  return (k9, n9)
}

/-- `nest_cont_key(vis, ctx, fuel, progOff, progLen, kb, n, us, dsOff, dsLen, nPc, cty, ns)`: the
instantiation met: in progress, cached, or a new frame. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:980-997 ConRon.Arena.nestContKey
@[l_impl ConRon.Arena.nestContKey]
def nestContKeyL : FunDecl :=
    lfn (vis, ctx, fuel, progOff, progLen, kb, n, us, dsOff, dsLen, nPc, cty, ns) locals
      (key, inProg, closedB, inKeys, k9, n9) {
  key := call rec4(n, us, dsOff, dsLen);
  inProg := call nest_keys_contains(IW.u64[ns + 2], IW.u64[ns + 3], key);
  if inProg != 0 { fail R_NESTED_POSITIVITY_NON_VALID_OCCURRENCE_OF };
  closedB := call nest_ds_closed(ctx, dsOff, dsLen);
  if closedB != 0 {
    inKeys := call nest_keys_contains(IW.u64[ns], IW.u64[ns + 1], key);
    if inKeys != 0 { return (4 + 8 * u64(kb != 0), ns) }
  };
  (k9, n9) := call nest_cont_new(vis, ctx, fuel, progOff, progLen, kb, n, us, dsOff, dsLen, nPc,
    cty, ns);
  return (k9, n9)
}

/-- Part of `nestCont`: the container's parameters have no local variables (`bvarB` tested
first). -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:999-1036 ConRon.Arena.nestCont
@[l_impl ConRon.Arena.nestCont]
def nestContParamsClosedL : FunDecl := lfn (hp, dsOff, dsLen) locals (bb, fb, r) {
  if dsLen == 0 { return 1 };
  bb := call bvar_b(⟪CWF⟫, IW.u64[dsOff]);
  if bb != 0 { return 0 };
  fb := call fvar_b(⟪CWF⟫, IW.u64[dsOff]);
  if hp < fb { return 0 };
  r := call nest_cont_params_closed(hp, dsOff + 1, dsLen - 1);
  return r
}

/-- Part of `nestCont`: hole-free indices, not `Quot`, parameters without local variables. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:999-1036 ConRon.Arena.nestCont
@[l_impl ConRon.Arena.nestCont]
def nestContChecksL : FunDecl :=
    lfn (ctx, hp, n, dsOff, dsLen, idxOff, idxLen) locals (occ, q, pc) {
  occ := call nest_occ_any(IW.u64[ctx], IW.u64[ctx + 1], IW.u64[ctx + 4], hp, idxOff, idxLen);
  if occ != 0 { fail R_NESTED_POSITIVITY_NON_VALID };
  q := call pin_at(47);
  if n == q { fail R_NESTED_POSITIVITY_NON_VALID };
  pc := call nest_cont_params_closed(hp, dsOff, dsLen);
  if pc == 0 { fail R_NESTED_POSITIVITY_NESTED };
  return 0
}

/-- `nest_cont(vis, ctx, fuel, progOff, progLen, kb, n, us, argsOff, argsLen, ns)`: the container
case of `nestPos`. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:999-1036 ConRon.Arena.nestCont
@[l_impl ConRon.Arena.nestCont]
def nestContL : FunDecl :=
    lfn (vis, ctx, fuel, progOff, progLen, kb, n, us, argsOff, argsLen, ns) locals
      (ok, nPc, zz1, zz2, hp, idxOff, idxLen, dsOff, dsLen, zz3, key, nI, cty, kind2) {
  (ok, nPc, zz1, zz2) := call nest_container(vis, n);
  if ok == 0 { fail R_NESTED_POSITIVITY_NON_VALID };
  hp := call nest_ctx_hi_at(ctx, progLen);
  if argsLen < nPc { fail R_NESTED_POSITIVITY_NON_VALID };
  idxOff := argsOff + nPc;
  idxLen := argsLen - nPc;
  dsOff := argsOff;
  dsLen := nPc;
  zz3 := call nest_cont_checks(ctx, hp, n, dsOff, dsLen, idxOff, idxLen);
  key := call rec4(n, us, dsOff, dsLen);
  (nI, cty) := call nest_inst_type(vis, ctx, hp, key);
  if argsLen != nPc + nI { fail R_NESTED_POSITIVITY_TYPE };
  (kind2, ns) := call nest_cont_key(vis, ctx, fuel, progOff, progLen, kb, n, us, dsOff, dsLen,
    nPc, cty, ns);
  return (kind2, ns)
}

/-- Part of `nestPos`: the field kind of a member or frame hole met at the head. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:1038-1097 ConRon.Arena.nestPos
@[l_impl ConRon.Arena.nestPos]
def nestPosHoleKindL : FunDecl := lfn (ctx, kb, i) locals (hi0, t) {
  hi0 := call nest_ctx_hi_at(ctx, 0);
  t := i - IW.u64[ctx + 4];
  if i < hi0 {
    if 1152921504606846976 <= t { abort };
    if kb == 0 { return 1 + 8 * t };
    return 2 + 8 * t
  };
  return 3
}

/-- Part of `nestPos`: the `fvar` head of an application (a member or frame hole, at its full
arity, hole-free indices). -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:1038-1097 ConRon.Arena.nestPos
@[l_impl ConRon.Arena.nestPos]
def nestPosFvarL :=
    lfn (vis, ctx, progOff, progLen, kb, hi, i, argsOff, argsLen) locals
      (okh, holeP, occA, keyP, cname, ar, dsLen2, kind2) {
  (okh, holeP) := call nest_hole_at(ctx, progOff, progLen, i);
  if okh == 0 { fail R_NESTED_POSITIVITY_NON_VALID };
  occA := call nest_occ_any(IW.u64[ctx], IW.u64[ctx + 1], IW.u64[ctx + 4], hi, argsOff, argsLen);
  if occA != 0 { fail R_NESTED_POSITIVITY_NON_VALID };
  keyP := IW.u64[holeP];
  cname := IW.u64[keyP];
  dsLen2 := IW.u64[keyP + 3];
  ar := call nest_arity(vis, cname);
  if argsLen + dsLen2 < argsLen { abort };
  if argsLen + dsLen2 != ar { fail R_NESTED_POSITIVITY_NON_VALID };
  kind2 := call nest_pos_hole_kind(ctx, kb, i);
  return kind2
}

/-- Part of `nestPos`: the non-`Π` branch — the application's head, by tag. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:1038-1097 ConRon.Arena.nestPos
@[l_impl ConRon.Arena.nestPos]
def nestPosAppL : FunDecl :=
    lfn (vis, ctx, fuel, progOff, progLen, kb, hi, w, ns) locals
      (argsOff, argsLen, hd, g2, x2, y2, zz, kind2, occA) {
  (argsOff, argsLen) := call get_app_args_f(⟪CWF⟫, w);
  hd := call get_app_fn_f(⟪CWF⟫, w);
  (g2, x2, y2, zz) := call e_view(hd);
  if g2 == 1 {
    kind2 := call nest_pos_fvar(vis, ctx, progOff, progLen, kb, hi, x2, argsOff, argsLen);
    return (kind2, ns)
  };
  if g2 == 3 {
    occA := call sl_contains(IW.u64[ctx], IW.u64[ctx + 1], x2);
    if occA != 0 { fail R_NESTED_POSITIVITY_NON_VALID };
    (kind2, ns) := call nest_cont(vis, ctx, fuel, progOff, progLen, kb, x2, y2, argsOff, argsLen,
      ns);
    return (kind2, ns)
  };
  fail R_NESTED_POSITIVITY_NON_VALID
}

/-- Part of `nestPos`: the `Π` branch — the domain checked, the codomain walked one binder in. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:1038-1097 ConRon.Arena.nestPos
@[l_impl ConRon.Arena.nestPos]
def nestPosBindL : FunDecl :=
    lfn (vis, ctx, fuel, progOff, progLen, dep, kb, w, ns) locals
      (hi, g, a, b, zz, occA, fv, k, nb, ns2) {
  hi := call nest_ctx_hi_at(ctx, progLen);
  (g, a, b, zz) := call e_view(w);
  occA := call nest_occ(IW.u64[ctx], IW.u64[ctx + 1], IW.u64[ctx + 4], hi, a);
  if occA != 0 { fail R_NESTED_POSITIVITY_NON };
  if dep + 1 == 0 { abort };
  if kb + 1 == 0 { abort };
  fv := call intern_fvar(dep, a);
  if 4294967296 <= fv { abort };
  b := call instantiate1_fast(⟪CWF⟫, b, fv, 0);
  (k, nb, ns2) := call nest_pos(vis, ctx, fuel, progOff, progLen, dep + 1, kb + 1, b, ns);
  nb := call abstract1_fast(⟪CWF⟫, nb, dep, 0);
  zz := call mk_forall(a, nb);
  if 4294967296 <= zz { abort };
  return (k, zz, ns2)
}

/-- `nest_pos(vis, ctx, fuel, progOff, progLen, dep, kb, e, ns)`: **the positivity function** —
the domain's reduct, by whnf; ordinary when it (or, failing that, the input) mentions no member
and no hole, else a `Π` (`nest_pos_bind`), or an application (`nest_pos_app`). -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:1038-1097 ConRon.Arena.nestPos
@[l_impl ConRon.Arena.nestPos]
def nestPosL : FunDecl :=
    lfn (vis, ctx, fuel, progOff, progLen, dep, kb, e, ns) locals
      (hi, w, occW, occE, tag, kind, ns2) {
  if fuel == 0 { fail R_NESTED_POSITIVITY_FUEL };
  fuel -= 1;
  hi := call nest_ctx_hi_at(ctx, progLen);
  w := call whnf_top(vis, dep, e);
  occW := call nest_occ(IW.u64[ctx], IW.u64[ctx + 1], IW.u64[ctx + 4], hi, w);
  if occW == 0 {
    occE := call nest_occ(IW.u64[ctx], IW.u64[ctx + 1], IW.u64[ctx + 4], hi, e);
    if occE != 0 { return (0, w, ns) };
    return (0, e, ns)
  };
  tag := w >> 28;
  if tag == 6 {
    (kind, w, ns2) := call nest_pos_bind(vis, ctx, fuel, progOff, progLen, dep, kb, w, ns);
    return (kind, w, ns2)
  };
  (kind, ns2) := call nest_pos_app(vis, ctx, fuel, progOff, progLen, kb, hi, w, ns);
  return (kind, w, ns2)
}

/-! ## The member holes and the root frame's crest -/

/-- `nestHoles.go`: the member holes, member by member — the former's type instantiated at the
canonical parameters, recursively over the names; `(0, _, _)` (the twin's `none`) when a member
is not a stored former or its type does not bind the parameters. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:1103-1120 ConRon.Arena.nestHoles.go
@[l_impl ConRon.Arena.nestHoles.go]
def nestHolesGoL : FunDecl := lfn (vis, ctx, mm, off, l, outOff, outLen) locals
    (found, q, ok2, t, v, r0, r1, r2) {
  if l == 0 { return (1, outOff, outLen) };
  (found, q) := call env_find(IW.u64[off], vis);
  if found == 0 { return (0, 0, 0) };
  if EREC.u64[q] != 3 { return (0, 0, 0) };
  (ok2, t) := call inst_pis_with(IW.u64[ctx + 7], IW.u64[ctx + 8], EREC.u64[q + 4]);
  if ok2 == 0 { return (0, 0, 0) };
  v := call intern_fvar(IW.u64[ctx + 4] + mm, t);
  if 4294967296 <= v { abort };
  (outOff, outLen) := call sl_snoc(outOff, outLen, v);
  (r0, r1, r2) := call nest_holes_go(vis, ctx, mm + 1, off + 1, l - 1, outOff, outLen);
  return (r0, r1, r2)
}

/-- `nest_holes(vis, ctx)`: the member holes (`go 0 ctx.names []`). -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:1103-1120 ConRon.Arena.nestHoles
@[l_impl ConRon.Arena.nestHoles]
def nestHolesL : FunDecl := lfn (vis, ctx) locals (namesOff, namesLen, ok, outOff, outLen) {
  namesOff := IW.u64[ctx];
  namesLen := IW.u64[ctx + 1];
  (ok, outOff, outLen) := call nest_holes_go(vis, ctx, 0, namesOff, namesLen, 0, 0);
  return (ok, outOff, outLen)
}

/-- `nest_root_canon(ctx, cv)`: the root frame's canonical crest of a member constructor. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:1122-1127 ConRon.Arena.nestRootCanon
@[l_impl ConRon.Arena.nestRootCanon]
def nestRootCanonL : FunDecl := lfn (ctx, cv) locals (lo, ll, t, ok, e) {
  (lo, ll) := call cv_lps(cv);
  t := call inst_lp_fast(⟪CWF⟫, lo, ll, IW.u64[ctx + 10], EREC.u64[cv + 3]);
  (ok, e) := call nest_canon_crest(IW.u64[ctx], IW.u64[ctx + 1], IW.u64[ctx + 10],
    IW.u64[ctx + 4], t);
  return (ok, e)
}

/-! ## Uniform occurrences: official's `check_uniform_ind_occs` -/

/-- `pi_doms_occ(namesOff, namesLen, lo, hi, n, e)`: does a member or a hole occur in one of the
first `n` binder domains of `e`? -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:1131-1143 ConRon.Arena.piDomsOcc
@[l_impl ConRon.Arena.piDomsOcc]
def piDomsOccL : FunDecl := lfn (namesOff, namesLen, lo, hi, n, e) locals (g, d, b, z, occ, r) {
  if n == 0 { return 0 };
  if e >> 28 != 6 { return 0 };
  (g, d, b, z) := call e_view(e);
  occ := call nest_occ(namesOff, namesLen, lo, hi, d);
  if occ != 0 { return 1 };
  r := call pi_doms_occ(namesOff, namesLen, lo, hi, n - 1, b);
  return r
}

/-- `nest_uniform_ok(ctx, cv)`: official's `check_uniform_ind_occs` at one constructor. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:1145-1156 ConRon.Arena.nestUniformOk
@[l_impl ConRon.Arena.nestUniformOk]
def nestUniformOkL : FunDecl := lfn (ctx, cv) locals (hi0, occ1, ok, e, occ2) {
  hi0 := call nest_ctx_hi_at(ctx, 0);
  occ1 := call pi_doms_occ(IW.u64[ctx], IW.u64[ctx + 1], IW.u64[ctx + 4], hi0, IW.u64[ctx + 4],
    EREC.u64[cv + 3]);
  if occ1 != 0 { return 0 };
  (ok, e) := call nest_root_canon(ctx, cv);
  if ok == 0 { return 0 };
  occ2 := call nest_occ(IW.u64[ctx], IW.u64[ctx + 1], 0, 0, e);
  return u64(occ2 == 0)
}

/-- `nest_uniform_cs(ctx, csOff, csLen)`: `cs.allM (fun c => nestUniformOk ctx c.1)` over a slice of
`[cv, nF]` pointers, short-circuiting (the inner loop of `nest_uniform`, as a recursion). -/
-- con-ron: none — the inner loop of nest_uniform as a self-recursive function (proof shape)
def nestUniformCsL : FunDecl := lfn (ctx, csOff, csLen) locals (ok, r) {
  if csLen == 0 { return 1 };
  ok := call nest_uniform_ok(ctx, IW.u64[IW.u64[csOff]]);
  if ok == 0 { return 0 };
  r := call nest_uniform_cs(ctx, csOff + 1, csLen - 1);
  return r
}

/-- `nest_uniform(ctx, off, l)`: `nestUniformOk` at every stored constructor of every member,
stopping at the first failure (recursively over the members). -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:1158-1166 ConRon.Arena.nestUniform
@[l_impl ConRon.Arena.nestUniform]
def nestUniformL : FunDecl := lfn (ctx, off, l) locals (hdr, b, u) {
  if l == 0 { return 0 };
  hdr := IW.u64[off];
  b := call nest_uniform_cs(ctx, IW.u64[hdr], IW.u64[hdr + 1]);
  if b == 0 { fail R_INVALID_OCCURRENCE_OF };
  u := call nest_uniform(ctx, off + 1, l - 1);
  return 0
}

/-! ## The root frame and the seeds -/

/-- `nest_root(vis, ctx, holesOff, holesLen, ctorssOff, ctorssLen, ns, outsOff, outsLen)`: every
member's constructors through `nest_ctors` at the root key, member by member (the loop as a
self-recursion over the members' slice). -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:1170-1182 ConRon.Arena.nestRoot
@[l_impl ConRon.Arena.nestRoot]
def nestRootL : FunDecl :=
    lfn (vis, ctx, holesOff, holesLen, ctorssOff, ctorssLen, ns, outsOff, outsLen) locals
      (hi0, hdr, csOff, csLen, oOff, oLen, ns2, hdrOut, r0, r1, r2) {
  if ctorssLen == 0 { return (outsOff, outsLen, ns) };
  hi0 := call nest_ctx_hi_at(ctx, 0);
  hdr := IW.u64[ctorssOff];
  csOff := IW.u64[hdr];
  csLen := IW.u64[hdr + 1];
  (oOff, oLen, ns2) := call nest_ctors(vis, ctx, 1, 0, 0, 0, hi0, IW.u64[ctx + 10],
    IW.u64[ctx + 7], IW.u64[ctx + 8], IW.u64[ctx], IW.u64[ctx + 1], holesOff, holesLen, csOff,
    csLen, ns, 0, 0);
  hdrOut := call rec2(oOff, oLen);
  (outsOff, outsLen) := call sl_snoc(outsOff, outsLen, hdrOut);
  (r0, r1, r2) := call nest_root(vis, ctx, holesOff, holesLen, ctorssOff + 1, ctorssLen - 1, ns2,
    outsOff, outsLen);
  return (r0, r1, r2)
}

/-- `nest_seed_of_go(ctx, f, dsOff, dsLen, q, j)`: the rest of the class's parameters read back,
written at `q + j`, … (the loop of `nest_seed_of`, as a recursion). -/
-- con-ron: none — the loop of nest_seed_of as a self-recursive function (proof shape)
def nestSeedOfGoL : FunDecl := lfn (ctx, f, dsOff, dsLen, q, j) locals (y, z, u) {
  if j >= dsLen { return 0 };
  y := call replace_apps(IW.u64[ctx], IW.u64[ctx + 1], IW.u64[ctx + 10], 0, IW.u64[ctx + 4], IW.u64[dsOff + j]);
  if 4294967296 <= y { abort };
  z := call replace_fvars(f, y);
  IW.u64[q + j] := z;
  u := call nest_seed_of_go(ctx, f, dsOff, dsLen, q, j + 1);
  return 0
}

/-- `nest_seed_of(ctx, holesOff, holesLen, ind, us, dsOff, dsLen, nPc)`: a resolved class as a
seed, its parameters read back through the walk's representation. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:1184-1194 ConRon.Arena.nestSeedOf
@[l_impl ConRon.Arena.nestSeedOf]
def nestSeedOfL :=
    lfn (ctx, holesOff, holesLen, ind, us, dsOff, dsLen, nPc) locals (f, q, u, key) {
  f := call rec5(1, IW.u64[ctx + 7], IW.u64[ctx + 8], holesOff, holesLen);
  q := call iw_alloc(dsLen);
  u := call nest_seed_of_go(ctx, f, dsOff, dsLen, q, 0);
  key := call rec4(ind, us, q, dsLen);
  return (key, nPc)
}

/-- `nest_seeds_fuel(dO, dL, k, f)`: the seed's fuel, `f` maxed with `whnf_walk_fuel` of the
parameters from `k` on (the inner loop of `nest_seeds`, as a recursion). -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:1196-1210 ConRon.Arena.nestSeeds
@[l_impl ConRon.Arena.nestSeeds]
def nestSeedsFuelL : FunDecl := lfn (dO, dL, k, f) locals (w, r) {
  if dL <= k { return f };
  w := call whnf_walk_fuel(IW.u64[dO + k]);
  if f < w { f := w };
  r := call nest_seeds_fuel(dO, dL, k + 1, f);
  return r
}

/-- `nest_seeds(vis, ctx, seedsOff, seedsLen, ns)`: the seeds walked, in order, at the root (the
loop as a self-recursion over the seeds' slice). -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:1196-1210 ConRon.Arena.nestSeeds
@[l_impl ConRon.Arena.nestSeeds]
def nestSeedsL : FunDecl := lfn (vis, ctx, seedsOff, seedsLen, ns) locals
    (hi0, sp, key, nPc, f, nI, cty, kind, ns2, r) {
  if seedsLen == 0 { return ns };
  hi0 := call nest_ctx_hi_at(ctx, 0);
  sp := IW.u64[seedsOff];
  key := IW.u64[sp];
  nPc := IW.u64[sp + 1];
  f := call nest_seeds_fuel(IW.u64[key + 2], IW.u64[key + 3], 0, ⟪SLACK⟫);
  (nI, cty) := call nest_inst_type(vis, ctx, hi0, key);
  (kind, ns2) := call nest_cont_key(vis, ctx, f, 0, 0, 0, IW.u64[key], IW.u64[key + 1],
    IW.u64[key + 2], IW.u64[key + 3], nPc, cty, ns);
  r := call nest_seeds(vis, ctx, seedsOff + 1, seedsLen - 1, ns2);
  return r
}

/-! ## The module's program and its closure -/

/-- All of this module's L functions. -/
def indPos2Fns : Prog :=
  [("nest_key_eq", nestKeyEqL), ("nest_keys_contains", nestKeysContainsL),
   ("nest_occ_any", nestOccAnyL), ("nest_ds_closed_go", nestDsClosedGoL),
   ("nest_ds_closed", nestDsClosedL),
   ("nest_inst_type_ty", nestInstTypeTyL), ("nest_inst_type", nestInstTypeL),
   ("nest_res_head", nestResHeadL), ("nest_ctor_nf", nestCtorNfL),
   ("nest_block_of", nestBlockOfL), ("nest_frame_mates_go", nestFrameMatesGoL),
   ("nest_frame_mates", nestFrameMatesL), ("nest_arity", nestArityL),
   ("nest_group_ctors", nestGroupCtorsL), ("nest_grow_group", nestGrowGroupL),
   ("nest_accept_group", nestAcceptGroupL), ("nest_walk_stack", nestWalkStackL),
   ("nest_fields", nestFieldsL), ("nest_ctors_u4", nestCtorsU4L),
   ("nest_ctors_res_ok", nestCtorsResOkL), ("nest_ctors_crest", nestCtorsCrestL),
   ("nest_ctors_walk", nestCtorsWalkL), ("nest_ctors_one", nestCtorsOneL),
   ("nest_ctors", nestCtorsL), ("nest_frame_grp", nestFrameGrpL),
   ("nest_frame_holes", nestFrameHolesL), ("nest_frame", nestFrameL),
   ("nest_cont_new_active", nestContNewActiveL), ("nest_cont_new_finish", nestContNewFinishL),
   ("nest_cont_new", nestContNewL), ("nest_cont_key", nestContKeyL),
   ("nest_cont_params_closed", nestContParamsClosedL), ("nest_cont_checks", nestContChecksL),
   ("nest_cont", nestContL), ("nest_pos_hole_kind", nestPosHoleKindL),
   ("nest_pos_fvar", nestPosFvarL), ("nest_pos_app", nestPosAppL),
   ("nest_pos_bind", nestPosBindL), ("nest_pos", nestPosL),
   ("nest_holes_go", nestHolesGoL), ("nest_holes", nestHolesL),
   ("nest_root_canon", nestRootCanonL), ("pi_doms_occ", piDomsOccL),
   ("nest_uniform_ok", nestUniformOkL), ("nest_uniform_cs", nestUniformCsL),
   ("nest_uniform", nestUniformL),
   ("nest_root", nestRootL), ("nest_seed_of_go", nestSeedOfGoL), ("nest_seed_of", nestSeedOfL),
   ("nest_seeds_fuel", nestSeedsFuelL), ("nest_seeds", nestSeedsL)]

/-- Stubs for the functions of OTHER modules this module calls: `nest_occ`, `nest_container`,
`nest_crest`, `nest_canon_crest`, `replace_fvars`, `replace_apps`, `inst_pis_with`,
`close_telescope`, `whnf_walk_fuel`, `nest_ctx_hi_at`, `nest_hole_at` (module `IndPos`);
`pi_binders` (module `IndParts`); `struct_used_later` (module `IndSum`). -/
def indPos2Foreign : Prog :=
  [("nest_occ", stub 5), ("nest_container", stub 2), ("nest_crest", stub 8),
   ("nest_canon_crest", stub 5), ("replace_fvars", stub 2), ("replace_apps", stub 6),
   ("inst_pis_with", stub 3), ("close_telescope", stub 4), ("whnf_walk_fuel", stub 1),
   ("nest_ctx_hi_at", stub 2), ("nest_hole_at", stub 4), ("pi_binders", stub 2),
   ("struct_used_later", stub 3), ("nest_hole_img_ds", stub 3)]

/-- `testMem` with `EREC[0..4) = [3, 5, 3, 7]` (`nestFrameMates.go`'s input is `IndCaps.all`, an
`EREC` slice). -/
def fmTestMem : Mem := { testMem with
  words := testMem.words.set! EREC (#[(3 : Word), 5, 3, 7] ++ Array.replicate 60 0) }

-- `nestFrameMates.go` over the `EREC` block `[3, 5, 3, 7]` at `c = 5`: `[3, 7]` (5 filtered, the
-- repeated 3 deduped), built into `IW`.
#guard
  match run (indPos2Fns ++ libFns ++ stubFns ++ masterFns ++ indPos2Foreign) 1000
      "nest_frame_mates_go" [5, 0, 4, 0, 0] fmTestMem with
  | .ok ([oo, 2], m5) =>
    rdW (m5.arr64 IW) oo == 3 && rdW (m5.arr64 IW) (oo + 1) == 7
  | _ => false

end L.Ind
