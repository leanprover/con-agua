import ConAgua.Arena.IndIface

/-!
# The recursor stage's class kit, in L (lane `induct`, module `RecCheck`)

The L translation of `vendor/con-ron/ConRon/Arena/Inductives/RecCheck.lean`: the member
abstraction (`target_abs`), the per-component class match (`target_class_match`) and the table
entries it selects (`target_major_nfs`), a class resolved from a major (`target_major_of`) and
typed (`target_major_pins`), the recursor records' pins (`target_rec_pins`), node agreement
(`target_k53`, K.53′), and the stored family's rules (`tgt_stored_rules`, `cons_block_recs_tf`)
with the container bit (`block_nested_bit`).

No proofs this round (DESIGN §8, lane `induct`): every `FunDecl` below is tagged with the twin
function it translates; a later round proves refinement.

## Layout reminders (IndIface.lean)

`TargetMajor` (13 words at `M`): `[ind, lvls, ds.off, ds.len, nPc, nIdx, ctors.off, ctors.len,
member, nfs.off, nfs.len, pfvs.off, pfvs.len]` (`member`: `0` none, `t + 1` some `t`).
`BlockShape` (9 words at `p`): `[members.off, members.len, recs.off, recs.len, nP, elim, resSort,
large, isProp]`. `MemberShape` (4 words): `[cvT, nIdx, ctors.off, ctors.len]`. `RecShape` (6
words): `[cvR, rP, mI, tgt, rhss.off, rhss.len]`. `IConstantVal` (4 words at `cv`): `[name,
lps.off, lps.len, type]`. An `IRecRule` is an 11-word `EREC` record (`decRule`, `ConAgua/Arena/
EnvRec.lean`): `[ctor, nfields, ctorParams, fire kind, fire lvls (off, len), fire pins (off, len),
rhs, k, eta]`.
-/

namespace L.Ind

open L.Arena

/-! ## `target_abs`: the member abstraction, one memoised DAG walk (schema `ta`) -/

/-- The `const n us` arm: `h` unless `us` is the walk's `lvls` and `n` is a member name with a
hole at its index. -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:56-110 ConRon.Arena.targetAbsGo
@[l_impl ConRon.Arena.targetAbsGo]
def targetAbsConst : FunDecl := lfn (no, nl, lvls, ho, hl, h, n, vus) locals (ok, t) {
  if vus != lvls { return h };
  (ok, t) := call sl_find(no, nl, n);
  if ok == 0 { return h };
  if hl <= t { return h };
  return IW.u64[ho + t]
}

/-- `target_abs_node(names.off, names.len, lvls, holes.off, holes.len, fuel1, g, x, y, z)`: the memoised
fallback's arms (`app`, `lam`, `forallE`, `letE`, else `proj`; the other five tags are handled in
`target_abs_go` before the memo is touched). -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:56-110 ConRon.Arena.targetAbsGo
@[l_impl ConRon.Arena.targetAbsGo]
def targetAbsNode : FunDecl := lfn (no, nl, lvls, ho, hl, fuel, g, x, y, z) locals (a2, x2, c2, r) {
  if g == 4 {
    a2 := call target_abs_go(no, nl, lvls, ho, hl, fuel, x);
    x2 := call target_abs_go(no, nl, lvls, ho, hl, fuel, y);
    r := call mk_app(a2, x2);
    return r
  };
  if g == 5 {
    a2 := call target_abs_go(no, nl, lvls, ho, hl, fuel, x);
    x2 := call target_abs_go(no, nl, lvls, ho, hl, fuel, y);
    r := call mk_lam(a2, x2);
    return r
  };
  if g == 6 {
    a2 := call target_abs_go(no, nl, lvls, ho, hl, fuel, x);
    x2 := call target_abs_go(no, nl, lvls, ho, hl, fuel, y);
    r := call mk_forall(a2, x2);
    return r
  };
  if g == 7 {
    a2 := call target_abs_go(no, nl, lvls, ho, hl, fuel, x);
    x2 := call target_abs_go(no, nl, lvls, ho, hl, fuel, y);
    c2 := call target_abs_go(no, nl, lvls, ho, hl, fuel, z);
    r := call mk_let(a2, x2, c2);
    return r
  };
  -- g == 9 (proj)
  a2 := call target_abs_go(no, nl, lvls, ho, hl, fuel, z);
  r := call mk_proj(x, y, a2);
  return r
}

/-- **`target_abs_go`**: `bvar`/`sort`/`lit`/`fvar` unchanged, `const` via `target_abs_const`,
else probe the `ta` memo and, on a miss, dispatch (`target_abs_node`) and insert. -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:56-110 ConRon.Arena.targetAbsGo
@[l_impl ConRon.Arena.targetAbsGo]
def targetAbsGo : FunDecl := lfn (no, nl, lvls, ho, hl, fuel, h) locals (g, x, y, z, fd, j, d, r, u) {
  if fuel == 0 { abort };
  (g, x, y, z) := call e_view(h);
  if g == 0 { return h };
  if g == 1 { return h };
  if g == 2 { return h };
  if g == 8 { return h };
  if g == 3 {
    r := call target_abs_const(no, nl, lvls, ho, hl, h, x, y);
    return r
  };
  (fd, j, d) := call ta_find(h, 0);
  if fd != 0 { return TAM.u64[j * 4 + 3] };
  r := call target_abs_node(no, nl, lvls, ho, hl, fuel - 1, g, x, y, z);
  (fd, j, d) := call ta_find(h, 0);
  u := call ta_put(h, 0, r, fd, j);
  return r
}

/-- **`target_abs`**: the fresh-memo entry (`ta_clear`, then the walk at `⟪CWF⟫`). -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:112-117 ConRon.Arena.targetAbs
@[l_impl ConRon.Arena.targetAbs]
def targetAbs : FunDecl := lfn (no, nl, lvls, ho, hl, e) locals (z, r) {
  z := call ta_clear();
  r := call target_abs_go(no, nl, lvls, ho, hl, ⟪CWF⟫, e);
  return r
}

/-- **`target_holes`**: the rule frame's holes, `fvar (base + j)` at the former's type, in
member order. -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:119-127 ConRon.Arena.targetHoles
@[l_impl ConRon.Arena.targetHoles]
def targetHoles : FunDecl := lfn (tyo, tyl, base) locals (v, ro, rl, qo, ql) {
  if tyl == 0 { return (0, 0) };
  v := call intern_fvar(base, IW.u64[tyo]);
  if 4294967296 <= v { abort };
  (ro, rl) := call target_holes(tyo + 1, tyl - 1, base + 1);
  (qo, ql) := call sl_cons(v, ro, rl);
  return (qo, ql)
}

/-! ## The major -/

/-- A fresh `TargetMajor` record (13 words), untagged library plumbing (akin to `rec2`…`rec6`). -/
-- con-ron: none — a fresh record (L plumbing, like `rec2`…`rec6`)
def mkTargetMajor : FunDecl :=
  lfn (ind, lvls, dso, dsl, nPc, nIdx, ctorso, ctorsl, member, nfso, nfsl, pfvso, pfvsl) locals (p) {
    p := call iw_alloc(13);
    IW.u64[p] := ind;
    IW.u64[p + 1] := lvls;
    IW.u64[p + 2] := dso;
    IW.u64[p + 3] := dsl;
    IW.u64[p + 4] := nPc;
    IW.u64[p + 5] := nIdx;
    IW.u64[p + 6] := ctorso;
    IW.u64[p + 7] := ctorsl;
    IW.u64[p + 8] := member;
    IW.u64[p + 9] := nfso;
    IW.u64[p + 10] := nfsl;
    IW.u64[p + 11] := pfvso;
    IW.u64[p + 12] := pfvsl;
    return p
  }

/-- **`target_major_default`**: the anonymous inductive at no level/parameter, the `deriving
Inhabited` fallback `Ms.getD c default` reads. -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:151-160 ConRon.Arena.targetMajorDefault
@[l_impl ConRon.Arena.targetMajorDefault]
def targetMajorDefault : FunDecl := lfn () locals (anon, ls, r) {
  anon := call intern_nanon();
  ls := call pin_word(52);
  r := call mk_target_major(anon, ls, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0);
  return r
}

/-- **`target_major_at`**: `ms[c]?`, else `target_major_default`. -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:162-167 ConRon.Arena.targetMajorAt
@[l_impl ConRon.Arena.targetMajorAt]
def targetMajorAt : FunDecl := lfn (mo, ml, c) locals (r) {
  if c < ml { return IW.u64[mo + c] };
  r := call target_major_default();
  return r
}

/-- **`erase_fvar_tys`**: `replaceFVars .erase e`, `f` a fresh `[2]` `FvMap` record. -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:169-173 ConRon.Arena.eraseFVarTys
@[l_impl ConRon.Arena.eraseFVarTys]
def eraseFVarTys : FunDecl := lfn (e) locals (f, r) {
  f := call iw_alloc(1);
  IW.u64[f] := 2;
  r := call replace_fvars(f, e);
  return r
}

/-- **`target_canon_params`**: `replaceFVars (.canon pfvs) e`, `f = [3, pfvs.off, pfvs.len]` (an
empty `pfvs` recorded at offset `0`: its offset is whatever the caller's record holds). -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:175-179 ConRon.Arena.targetCanonParams
@[l_impl ConRon.Arena.targetCanonParams]
def targetCanonParams : FunDecl := lfn (pfo, pfl, e) locals (po, f, r) {
  po := pfo;
  if pfl == 0 { po := 0 };
  f := call rec3(3, po, pfl);
  r := call replace_fvars(f, e);
  return r
}

/-- One step of `target_params_def_eq`'s loop: the closedness test (short-circuiting, `bvar_b a`,
`bvar_b b`, `fvar_b a`, `fvar_b b` in order), then member-abstracted canon forms, then syntactic
or inferred-and-defeq. Returns `1` to continue the loop, `0` to stop it (the overall `false`). -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:181-208 ConRon.Arena.targetParamsDefEq
@[l_impl ConRon.Arena.targetParamsDefEq]
def targetParamsDefEqStep : FunDecl := lfn (vis, d, no, nl, lvls, ho, hl, pfo, pfl, a, b)
    locals (bb, fb, ac, av, bc, bv, u, deq) {
  bb := call bvar_b(⟪CWF⟫, a);
  if bb != 0 { return 0 };
  bb := call bvar_b(⟪CWF⟫, b);
  if bb != 0 { return 0 };
  fb := call fvar_b(⟪CWF⟫, a);
  if pfl < fb { return 0 };
  fb := call fvar_b(⟪CWF⟫, b);
  if pfl < fb { return 0 };
  ac := call target_canon_params(pfo, pfl, a);
  av := call target_abs(no, nl, lvls, ho, hl, ac);
  if 4294967296 <= av { abort };
  bc := call target_canon_params(pfo, pfl, b);
  bv := call target_abs(no, nl, lvls, ho, hl, bc);
  if 4294967296 <= bv { abort };
  if av == bv { return 1 };
  u := call infer_type_core(vis, d, av);
  u := call infer_type_core(vis, d, bv);
  deq := call is_def_eq_core(vis, d, av, bv);
  return deq
}

/-- **`target_params_def_eq`**: per-component parameter defeq, stopping at the first mismatch; a
self-recursion on both slices, as the twin's list recursion (lists of different lengths are
compared up to the shorter one's end, then `false`). -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:181-208 ConRon.Arena.targetParamsDefEq
@[l_impl ConRon.Arena.targetParamsDefEq]
def targetParamsDefEq : FunDecl := lfn (vis, d, no, nl, lvls, ho, hl, pfo, pfl, ao, al, bo, bl)
    locals (r) {
  if al == 0 { return u64(bl == 0) };
  if bl == 0 { return 0 };
  r := call target_params_def_eq_step(vis, d, no, nl, lvls, ho, hl, pfo, pfl, IW.u64[ao], IW.u64[bo]);
  if r == 0 { return 0 };
  r := call target_params_def_eq(vis, d, no, nl, lvls, ho, hl, pfo, pfl, ao + 1, al - 1, bo + 1, bl - 1);
  return r
}

/-- **`target_class_match`**: levels up to `lvls_eq_c` (the cached `lvlsEq?`, as the twin), then
per-component parameter defeq over the recursor prefix `pfvs` with the member holes on top. -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:210-224 ConRon.Arena.targetClassMatch
@[l_impl ConRon.Arena.targetClassMatch]
def targetClassMatch : FunDecl := lfn (vis, p, fto, ftl, pfo, pfl, us, dso, dsl, lvls, edso, edsl)
    locals (e, mno, mnl, lpso, lpsl, blvls, ho, hl, d, r) {
  e := call lvls_eq_c(us, lvls);
  if e != 2 { return 0 };
  (mno, mnl) := call block_shape_member_names(p);
  (lpso, lpsl) := call block_shape_lps(p);
  blvls := call param_levels(lpso, lpsl);
  d := pfl + ftl;
  if d < pfl { abort };
  (ho, hl) := call target_holes(fto, ftl, pfl);
  r := call target_params_def_eq(vis, d, mno, mnl, blvls, ho, hl, pfo, pfl, dso, dsl, edso, edsl);
  return r
}

/-- Does any of `ctors` carry the constructor name `name`? -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:226-241 ConRon.Arena.targetMajorNfs
@[l_impl ConRon.Arena.targetMajorNfs]
def ctorsHaveName : FunDecl := lfn (co, cl, name) locals (ce, r) {
  if cl == 0 { return 0 };
  ce := IW.u64[co];
  if EREC.u64[IW.u64[ce]] == name { return 1 };
  r := call ctors_have_name(co + 1, cl - 1, name);
  return r
}

/-- **`target_major_nfs`**: the walk's recorded constructor normal forms matching this class, as the
twin's recursion: the tail first (so the class-match calls fire from the last entry to the first),
each kept entry consed onto the kept tail (`sl_cons`, D18). -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:226-241 ConRon.Arena.targetMajorNfs
@[l_impl ConRon.Arena.targetMajorNfs]
def targetMajorNfs : FunDecl := lfn (vis, p, fto, ftl, pfo, pfl, us, dso, dsl, cto, ctl, nfo, nfl)
    locals (ro, rl, eptr, has, keep, qo, ql) {
  if nfl == 0 { return (0, 0) };
  (ro, rl) := call target_major_nfs(vis, p, fto, ftl, pfo, pfl, us, dso, dsl, cto, ctl, nfo + 1, nfl - 1);
  eptr := IW.u64[nfo];
  has := call ctors_have_name(cto, ctl, IW.u64[eptr]);
  if has == 0 { return (ro, rl) };
  keep := call target_class_match(vis, p, fto, ftl, pfo, pfl, us, dso, dsl, IW.u64[eptr + 1],
    IW.u64[eptr + 2], IW.u64[eptr + 3]);
  if keep == 0 { return (ro, rl) };
  (qo, ql) := call sl_cons(eptr, ro, rl);
  return (qo, ql)
}

/-- **`target_ctors_of`**: a stored inductive's constructors and parameter count. -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:243-248 ConRon.Arena.targetCtorsOf
@[l_impl ConRon.Arena.targetCtorsOf]
def targetCtorsOf : FunDecl := lfn (vis, I) locals (ok, nPc, cso, csl) {
  (ok, nPc, cso, csl) := call nest_container(vis, I);
  return (ok, nPc, cso, csl)
}

/-- **`target_outside_inst`**: an OUTSIDE major's instantiated type former: its index count and
result sort. -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:250-267 ConRon.Arena.targetOutsideInst
@[l_impl ConRon.Arena.targetOutsideInst]
def targetOutsideInst : FunDecl := lfn (vis, I, us, dso, dsl)
    locals (f, q, kind, tl, ok, ty, bso, bsl, body, g, x, y, z, lo, ll) {
  (f, q) := call env_find(I, vis);
  if f == 0 { fail R_TARGET_REC_THE_RECURSOR_S_MAJOR_IS_NOT };
  kind := EREC.u64[q];
  if kind != 3 { fail R_TARGET_REC_THE_RECURSOR_S_MAJOR_IS_NOT };
  (lo, ll) := call er_to_iw(EREC.u64[q + 2], EREC.u64[q + 3]);
  tl := call inst_lp_fast(⟪CWF⟫, lo, ll, us, EREC.u64[q + 4]);
  (ok, ty) := call inst_pis_with(dso, dsl, tl);
  if ok == 0 { fail R_TARGET_REC_THE_MAJOR_S };
  (bso, bsl, body) := call pi_binders(⟪CWF⟫, ty);
  (g, x, y, z) := call e_view(body);
  if g != 2 { fail R_TARGET_REC_THE_MAJOR_S_TYPE };
  return (bsl, x)
}

/-- `target_major_of`'s MEMBER branch: the member at the block's levels and parameters. -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:271-334 ConRon.Arena.targetMajorOf
@[l_impl ConRon.Arena.targetMajorOf]
def targetMajorOfMember : FunDecl := lfn (p, cao, cal, pfo, pfl, fvo, fvl, args_o, args_l, I, us, t)
    locals (mo, ml, ms, nidx, ch, ctor_o, ctor_l, nP, lpso, lpsl, blvls, al2, fl2, eq1, eq2, r) {
  mo := IW.u64[p];
  ml := IW.u64[p + 1];
  if ml <= t { abort };
  ms := IW.u64[mo + t];
  nidx := IW.u64[ms + 1];
  if cal <= t { abort };
  ch := IW.u64[cao + t];
  ctor_o := IW.u64[ch];
  ctor_l := IW.u64[ch + 1];
  nP := IW.u64[p + 4];
  (lpso, lpsl) := call block_shape_lps(p);
  blvls := call param_levels(lpso, lpsl);
  al2 := args_l;
  if nP < args_l { al2 := nP };
  fl2 := fvl;
  if nP < fvl { fl2 := nP };
  eq1 := u64(us == blvls);
  eq2 := call sl_eq(args_o, al2, fvo, fl2);
  if eq1 == 0 { fail R_TARGET_REC_THE_RECURSOR_S_MAJOR_PREMISE_IS };
  if eq2 == 0 { fail R_TARGET_REC_THE_RECURSOR_S_MAJOR_PREMISE_IS };
  r := call mk_target_major(I, us, fvo, fl2, nP, nidx, ctor_o, ctor_l, t + 1, 0, 0, pfo, pfl);
  return r
}

/-- `target_major_of`'s OUTSIDE branch: the closedness test over the instantiation's
parameters (`ds.allM`, stopping at the first failure). -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:271-334 ConRon.Arena.targetMajorOf
@[l_impl ConRon.Arena.targetMajorOf]
def targetMajorOfOutsideClosed : FunDecl := lfn (dso, dsl, nP) locals (x, bb, fb, r) {
  if dsl == 0 { return 1 };
  x := IW.u64[dso];
  bb := call bvar_b(⟪CWF⟫, x);
  if bb != 0 { return 0 };
  fb := call fvar_b(⟪CWF⟫, x);
  if nP < fb { return 0 };
  r := call target_major_of_outside_closed(dso + 1, dsl - 1, nP);
  return r
}

/-- `target_major_of`'s OUTSIDE branch: does any parameter occur as a member or hole
(`ds.anyM`, stopping at the first hit; a self-recursion). -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:271-334 ConRon.Arena.targetMajorOf
@[l_impl ConRon.Arena.targetMajorOf]
def targetMajorOfOutsideOcc : FunDecl := lfn (mno, mnl, dso, dsl) locals (b, r) {
  if dsl == 0 { return 0 };
  b := call nest_occ(mno, mnl, 0, 0, IW.u64[dso]);
  if b != 0 { return 1 };
  r := call target_major_of_outside_occ(mno, mnl, dso + 1, dsl - 1);
  return r
}

/-- `target_major_of`'s OUTSIDE branch, after the parameter checks: the instantiation's index
count and sort, in the block's universe (Q1), the record. -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:271-334 ConRon.Arena.targetMajorOf
@[l_impl ConRon.Arena.targetMajorOf]
def targetMajorOfOutsideTail : FunDecl := lfn (vis, p, pfo, pfl, I, us, dso, dsl, cso, csl)
    locals (nidx, sI, e, r) {
  (nidx, sI) := call target_outside_inst(vis, I, us, dso, dsl);
  e := call lvl_eq_c(sI, IW.u64[p + 6]);
  if e == 0 { fail R_RESOURCE_LIMIT_FUEL };
  if e != 2 { fail R_TARGET_REC_THE_RECURSOR_S_MAJOR_LIVES };
  r := call mk_target_major(I, us, dso, dsl, dsl, nidx, cso, csl, 0, 0, 0, pfo, pfl);
  return r
}

/-- `target_major_of`'s OUTSIDE branch: not `Quot`, a stored inductive, parameters closed and
occurring, in the block's universe (Q1). -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:271-334 ConRon.Arena.targetMajorOf
@[l_impl ConRon.Arena.targetMajorOf]
def targetMajorOfOutside : FunDecl := lfn (vis, p, pfo, pfl, I, us, args_o, args_l, mno, mnl)
    locals (qq, ok3, nPc, cso, csl, cl, r) {
  qq := call pin_at(47);
  if I == qq { fail R_TARGET_REC_THE_RECURSOR_S_MAJOR };
  (ok3, nPc, cso, csl) := call target_ctors_of(vis, I);
  if ok3 == 0 { fail R_TARGET_REC_THE_RECURSOR_S_MAJOR_IS_NOT };
  if args_l < nPc { fail R_TARGET_REC_THE_MAJOR };
  cl := call target_major_of_outside_closed(args_o, nPc, IW.u64[p + 4]);
  if cl == 0 { fail R_TARGET_REC_THE_MAJOR };
  cl := call target_major_of_outside_occ(mno, mnl, args_o, nPc);
  if cl == 0 { fail R_TARGET_REC_THE_RECURSOR_S_MAJOR_IS };
  r := call target_major_of_outside_tail(vis, p, pfo, pfl, I, us, args_o, nPc, cso, csl);
  return r
}

/-- `target_major_of` after the head's `const` view: the member or the outside branch. -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:271-334 ConRon.Arena.targetMajorOf
@[l_impl ConRon.Arena.targetMajorOf]
def targetMajorOfConst : FunDecl := lfn (vis, p, cao, cal, pfo, pfl, fvo, fvl, args_o, args_l, x, y)
    locals (mno, mnl, ok2, t, r) {
  (mno, mnl) := call block_shape_member_names(p);
  (ok2, t) := call sl_find(mno, mnl, x);
  if ok2 != 0 {
    r := call target_major_of_member(p, cao, cal, pfo, pfl, fvo, fvl, args_o, args_l, x, y, t);
    return r
  };
  r := call target_major_of_outside(vis, p, pfo, pfl, x, y, args_o, args_l, mno, mnl);
  return r
}

/-- **`target_major_of`**: a recursor's major, resolved from its opened type — a MEMBER, or an
OUTSIDE stored inductive (a nested block's container). -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:271-334 ConRon.Arena.targetMajorOf
@[l_impl ConRon.Arena.targetMajorOf]
def targetMajorOf : FunDecl := lfn (vis, p, cao, cal, pfo, pfl, fvo, fvl, mty)
    locals (args_o, args_l, hd, tag, g, x, y, z, r) {
  (args_o, args_l) := call get_app_args_f(⟪CWF⟫, mty);
  hd := call get_app_fn_f(⟪CWF⟫, mty);
  tag := hd >> 28;
  if tag != 3 { fail R_TARGET_REC_THE_RECURSOR_S_MAJOR_PREMISE };
  (g, x, y, z) := call e_view(hd);
  r := call target_major_of_const(vis, p, cao, cal, pfo, pfl, fvo, fvl, args_o, args_l, x, y);
  return r
}

/-! ## The pins at a resolved major -/

/-- **`target_pin_tys`**: an outside major's parameters, typed at the rule prefix, in order. -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:336-343 ConRon.Arena.targetPinTys
@[l_impl ConRon.Arena.targetPinTys]
def targetPinTys : FunDecl := lfn (vis, d, xo, xl) locals (u) {
  if xl == 0 { skip }
  else {
    u := call infer_type_core(vis, d, IW.u64[xo]);
    u := call target_pin_tys(vis, d, xo + 1, xl - 1)
  }
}

/-- **`target_major_pins`**: nothing at a member; an outside major's parameters and the
instantiation itself, typed at the rule prefix. -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:345-358 ConRon.Arena.targetMajorPins
@[l_impl ConRon.Arena.targetMajorPins]
def targetMajorPins : FunDecl := lfn (vis, rP, M) locals (mem, hd, app, u) {
  mem := IW.u64[M + 8];
  if mem != 0 { skip }
  else {
    u := call target_pin_tys(vis, rP, IW.u64[M + 2], IW.u64[M + 3]);
    hd := call intern_const(IW.u64[M], IW.u64[M + 1]);
    if 4294967296 <= hd { abort };
    app := call mk_app_n_f(hd, IW.u64[M + 2], IW.u64[M + 3]);
    u := call infer_type_core(vis, rP, app)
  }
}

/-! ## The recursor records' pins -/

/-- Split the block's recursors into its own (`tgt < k`) and the auxiliary ones: the twin's two
`filter`s, a self-recursion consing each recursor onto its side's slice (`sl_cons`, D18). -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:362-397 ConRon.Arena.targetRecPins
@[l_impl ConRon.Arena.targetRecPins]
def blockRecSplitOwnAux : FunDecl := lfn (reco, recl, k) locals (oo, ol, ao, al, rc, qo, ql) {
  if recl == 0 { return (0, 0, 0, 0) };
  (oo, ol, ao, al) := call block_rec_split_own_aux(reco + 1, recl - 1, k);
  rc := IW.u64[reco];
  if IW.u64[rc + 3] < k {
    (qo, ql) := call sl_cons(rc, oo, ol);
    return (qo, ql, ao, al)
  };
  (qo, ql) := call sl_cons(rc, ao, al);
  return (oo, ol, qo, ql)
}

/-- The wanted auxiliary names `n₀.rec_{j+1} … n₀.rec_{j+auxl}`, interned in order (the twin's
`mapM` over `List.range`), a self-recursion consing each name (`sl_cons`, D18). -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:362-397 ConRon.Arena.targetRecPins
@[l_impl ConRon.Arena.targetRecPins]
def blockRecWantAuxNames : FunDecl := lfn (n0, j, auxl) locals (nm, ro, rl, qo, ql) {
  if auxl == 0 { return (0, 0) };
  nm := call name_rec_i(n0, j + 1);
  (ro, rl) := call block_rec_want_aux_names(n0, j + 1, auxl - 1);
  (qo, ql) := call sl_cons(nm, ro, rl);
  return (qo, ql)
}

/-- `ptr_names_copy(d, s, l)`: `IW[d + j] := EREC[IW[IW[s + j]]]` for `j < l`, recursively (the
constants' names of a slice of pointers whose word `0` is a constant pointer). -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:362-397 ConRon.Arena.targetRecPins
@[l_impl ConRon.Arena.targetRecPins]
def ptrNamesCopy : FunDecl := lfn (d, s, l) locals (ptr, cv, u) {
  if l == 0 { return 0 };
  ptr := IW.u64[s];
  cv := IW.u64[ptr];
  IW.u64[d] := EREC.u64[cv];
  u := call ptr_names_copy(d + 1, s + 1, l - 1);
  return 0
}

/-- The constants' names of a slice of pointers whose word `0` is a constant pointer (a
`RecShape`'s `cvR`, or a `(cv, nF)` constructor entry). -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:362-397 ConRon.Arena.targetRecPins
@[l_impl ConRon.Arena.targetRecPins]
def ptrListNames : FunDecl := lfn (o, l) locals (go, u) {
  go := call iw_alloc(l);
  u := call ptr_names_copy(go, o, l);
  return (go, l)
}

/-- The name pins: `n₀`, the auxiliary names as a set, no two recursors sharing a name. -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:362-397 ConRon.Arena.targetRecPins
@[l_impl ConRon.Arena.targetRecPins]
def targetRecPinsNames : FunDecl := lfn (mo, k, reco, recl, auxo, auxl)
    locals (n0, ms0, cvt0, wo, wl, go, gl, ok, nodupo, nodupl) {
  if k == 0 { n0 := call intern_nanon() }
  else { ms0 := IW.u64[mo]; cvt0 := IW.u64[ms0]; n0 := EREC.u64[cvt0] };
  (wo, wl) := call block_rec_want_aux_names(n0, 0, auxl);
  (go, gl) := call ptr_list_names(auxo, auxl);
  ok := call sl_set_eq(wo, wl, go, gl);
  if ok == 0 { return 0 };
  (nodupo, nodupl) := call ptr_list_names(reco, recl);
  ok := call sl_nodup(nodupo, nodupl);
  return ok
}

/-- The constructor grouping pin: the block splits, with `k` formers, as many rules as
recursors, and the same constructors in the same order. -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:362-397 ConRon.Arena.targetRecPins
@[l_impl ConRon.Arena.targetRecPins]
def targetRecPinsSplit : FunDecl := lfn (p, k, recl, blocko, blockl)
    locals (ok, q, cvtsl, rsl, cso, csl, aco, acl, an_o, an_l, cn_o, cn_l) {
  (ok, q) := call block_split(blocko, blockl);
  if ok == 0 { return 0 };
  cvtsl := IW.u64[q + 1];
  if cvtsl != k { return 0 };
  rsl := IW.u64[q + 5];
  if rsl != recl { return 0 };
  cso := IW.u64[q + 2];
  csl := IW.u64[q + 3];
  (aco, acl) := call block_shape_all_ctors(p);
  (an_o, an_l) := call ptr_list_names(aco, acl);
  (cn_o, cn_l) := call ptr_list_names(cso, csl);
  ok := call sl_eq(an_o, an_l, cn_o, cn_l);
  return ok
}

/-- **`target_rec_pins`**: level parameters, reserved names, the member/auxiliary recursor name
pins, no shared names, and the constructor grouping against the stream. -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:362-397 ConRon.Arena.targetRecPins
@[l_impl ConRon.Arena.targetRecPins]
def targetRecPins : FunDecl := lfn (p, blocko, blockl)
    locals (ok, reco, recl, k, owno, ownl, auxo, auxl, mo) {
  reco := IW.u64[p + 2];
  recl := IW.u64[p + 3];
  ok := call block_rec_lps_ok(p);
  if ok == 0 { fail R_TARGET_REC_THE_RECURSOR_S };
  ok := call block_rec_names_unreserved(reco, recl);
  if ok == 0 { fail R_TARGET_REC_A };
  k := IW.u64[p + 1];
  (owno, ownl, auxo, auxl) := call block_rec_split_own_aux(reco, recl, k);
  mo := IW.u64[p];
  ok := call block_rec_name_set_ok(mo, k, owno, ownl);
  if ok == 0 { fail R_TARGET_REC_THE_BLOCK_S };
  ok := call target_rec_pins_names(mo, k, reco, recl, auxo, auxl);
  if ok == 0 { fail R_TARGET_REC_THE_BLOCK };
  ok := call target_rec_pins_split(p, k, recl, blocko, blockl);
  if ok == 0 { fail R_TARGET_REC_THE_RECURSOR }
}

/-! ## A class's constructors, and node agreement (K.53′) -/

/-- **`target_ctor_at`**: a member's constructor type as stored, an outside inductive's
instantiated at the major's levels. -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:401-407 ConRon.Arena.targetCtorAt
@[l_impl ConRon.Arena.targetCtorAt]
def targetCtorAt : FunDecl := lfn (M, c) locals (mem, r, lo, ll, us) {
  mem := IW.u64[M + 8];
  if mem != 0 { return EREC.u64[c + 3] };
  us := IW.u64[M + 1];
  (lo, ll) := call cv_lps(c);
  r := call inst_lp_fast(⟪CWF⟫, lo, ll, us, EREC.u64[c + 3]);
  return r
}

/-- Erase the free-variable annotations of every element of a slice, in order: the twin's `mapM`
as a self-recursion, each result consed onto the rest's slice (`sl_cons`, D18). -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:409-448 ConRon.Arena.targetK53
@[l_impl ConRon.Arena.targetK53]
def eraseEach : FunDecl := lfn (o, l) locals (v, ro, rl, qo, ql) {
  if l == 0 { return (0, 0) };
  v := call erase_fvar_tys(IW.u64[o]);
  (ro, rl) := call erase_each(o + 1, l - 1);
  (qo, ql) := call sl_cons(v, ro, rl);
  return (qo, ql)
}

/-- `target_k53`'s telescope check: the stripped domains and the recorded telescope agree up to
erased annotations. -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:409-448 ConRon.Arena.targetK53
@[l_impl ConRon.Arena.targetK53]
def targetK53Tele : FunDecl := lfn (bso, bsl, teo, tel) locals (ewo, ewl, eto, etl, r) {
  (ewo, ewl) := call erase_each(bso, bsl);
  (eto, etl) := call erase_each(teo, tel);
  r := call sl_eq(ewo, ewl, eto, etl);
  return r
}

/-- `target_k53`'s head check: both leaf and major domain are constant applications of the same
head, of equal arity. -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:409-448 ConRon.Arena.targetK53
@[l_impl ConRon.Arena.targetK53]
def targetK53Heads : FunDecl := lfn (vis, p, fto, ftl, Mc, leafW, majDom)
    locals (lh, mh, ltag, mtag, g, x, y, z, ip, usp, ii, lao, lal, mao, mal, r) {
  lh := call get_app_fn_f(⟪CWF⟫, leafW);
  mh := call get_app_fn_f(⟪CWF⟫, majDom);
  ltag := lh >> 28;
  mtag := mh >> 28;
  if ltag != 3 { return 0 };
  if mtag != 3 { return 0 };
  (g, x, y, z) := call e_view(lh);
  ip := x;
  usp := y;
  (g, x, y, z) := call e_view(mh);
  ii := x;
  (lao, lal) := call get_app_args_f(⟪CWF⟫, leafW);
  (mao, mal) := call get_app_args_f(⟪CWF⟫, majDom);
  if ip != ii { return 0 };
  if lal != mal { return 0 };
  r := call target_k53_args(vis, p, fto, ftl, Mc, ip, usp, lao, lal, mao, mal);
  return r
}

/-- `target_k53`'s argument check: the indices (past `Mc.nPc`) erase equal, the class the leaf's
parameters name is a member occurrence, and it matches the callee's class. -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:409-448 ConRon.Arena.targetK53
@[l_impl ConRon.Arena.targetK53]
def targetK53Args : FunDecl := lfn (vis, p, fto, ftl, Mc, ip, usp, lao, lal, mao, mal)
    locals (nPc, ld_o, ld_l, md_o, md_l, leo, lel, meo, mel, r, lpl, hd, app, mno, mnl, occ) {
  nPc := IW.u64[Mc + 4];
  if lal < nPc { ld_o := lao; ld_l := 0 } else { ld_o := lao + nPc; ld_l := lal - nPc };
  if mal < nPc { md_o := mao; md_l := 0 } else { md_o := mao + nPc; md_l := mal - nPc };
  (leo, lel) := call erase_each(ld_o, ld_l);
  (meo, mel) := call erase_each(md_o, md_l);
  r := call sl_eq(leo, lel, meo, mel);
  if r == 0 { return 0 };
  if lal < nPc { lpl := lal } else { lpl := nPc };
  hd := call intern_const(ip, usp);
  if 4294967296 <= hd { abort };
  app := call mk_app_n_f(hd, lao, lpl);
  (mno, mnl) := call block_shape_member_names(p);
  occ := call nest_occ(mno, mnl, 0, 0, app);
  if occ == 0 { return 0 };
  r := call target_class_match(vis, p, fto, ftl, IW.u64[Mc + 11], IW.u64[Mc + 12], IW.u64[Mc + 1],
    IW.u64[Mc + 2], IW.u64[Mc + 3], usp, lao, lpl);
  return r
}

/-- **`target_k53`**: K.53′ at one recorded field. -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:409-448 ConRon.Arena.targetK53
@[l_impl ConRon.Arena.targetK53]
def targetK53 : FunDecl := lfn (vis, p, fto, ftl, Mc, teo, tel, majDom, f) locals (ok, bso, bsl, leafW, r) {
  (ok, bso, bsl, leafW) := call strip_pis(tel, f);
  if ok == 0 { return 0 };
  r := call target_k53_tele(bso, bsl, teo, tel);
  if r == 0 { return 0 };
  r := call target_k53_heads(vis, p, fto, ftl, Mc, leafW, majDom);
  return r
}

/-- **`target_pi_doms_with`**: the domains of the first `|xs|` `∀` binders, each instantiated at
the earlier `xs`; `(0, 0, 0)` when `e` runs out of binders first. -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:450-464 ConRon.Arena.targetPiDomsWith
@[l_impl ConRon.Arena.targetPiDomsWith]
def targetPiDomsWith : FunDecl := lfn (xo, xl, e) locals (tag, g, d, b, z, xj, cur, ok, ro, rl, qo, ql) {
  if xl == 0 { return (1, 0, 0) };
  tag := e >> 28;
  if tag != 6 { return (0, 0, 0) };
  (g, d, b, z) := call e_view(e);
  xj := IW.u64[xo];
  cur := call instantiate1_fast(⟪CWF⟫, b, xj, 0);
  (ok, ro, rl) := call target_pi_doms_with(xo + 1, xl - 1, cur);
  if ok == 0 { return (0, 0, 0) };
  (qo, ql) := call sl_cons(d, ro, rl);
  return (1, qo, ql)
}

/-! ## The stored family -/

/-- **`abstract_prefix`**: the free variables `0 … k-1` closed at cursor `c`, innermost first. -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:468-476 ConRon.Arena.abstractPrefix
@[l_impl ConRon.Arena.abstractPrefix]
def abstractPrefix : FunDecl := lfn (k, c, e) locals (cur, r) {
  if k == 0 { return e };
  cur := call abstract1_fast(⟪CWF⟫, e, k - 1, c);
  r := call abstract_prefix(k - 1, c + 1, cur);
  return r
}

/-- **`abstract_prefix_list`**: `ds.map (abstractPrefix rP)`, in order. -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:478-486 ConRon.Arena.abstractPrefixList
@[l_impl ConRon.Arena.abstractPrefixList]
def abstractPrefixList : FunDecl := lfn (rP, dso, dsl) locals (x, qo, ql, ro, rl) {
  if dsl == 0 { return (0, 0) };
  x := call abstract_prefix(rP, 0, IW.u64[dso]);
  (qo, ql) := call abstract_prefix_list(rP, dso + 1, dsl - 1);
  (ro, rl) := call sl_cons(x, qo, ql);
  return (ro, rl)
}

/-- **`aux_rule_fire`**: the firing mode of a rule at an OUTSIDE major — `.nested` at the class's
levels and its parameters closed over the rule prefix. Result: `(1, lvls.off, lvls.len, pins.off,
pins.len)` (kind `1` nested). -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:488-496 ConRon.Arena.auxRuleFire
@[l_impl ConRon.Arena.auxRuleFire]
def auxRuleFire : FunDecl := lfn (M, rP) locals (lo, ll, po, pl) {
  (lo, ll) := call view_ls(IW.u64[M + 1]);
  (po, pl) := call abstract_prefix_list(rP, IW.u64[M + 2], IW.u64[M + 3]);
  return (1, lo, ll, po, pl)
}

/-- `tgt_rule_nested(old, flo, fll, fpo, fpl)`: a fresh 11-word rule record, `old`'s fields with the
NESTED fire at the record-pool slices `(flo, fll)` (levels), `(fpo, fpl)` (pins). -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:498-509 ConRon.Arena.tgtStoredRules
@[l_impl ConRon.Arena.tgtStoredRules]
def tgtRuleNested : FunDecl := lfn (old, flo, fll, fpo, fpl) locals (newp) {
  newp := call erec_alloc(11);
  EREC.u64[newp] := EREC.u64[old];
  EREC.u64[newp + 1] := EREC.u64[old + 1];
  EREC.u64[newp + 2] := EREC.u64[old + 2];
  EREC.u64[newp + 3] := 1;
  EREC.u64[newp + 4] := flo;
  EREC.u64[newp + 5] := fll;
  EREC.u64[newp + 6] := fpo;
  EREC.u64[newp + 7] := fpl;
  EREC.u64[newp + 8] := EREC.u64[old + 8];
  EREC.u64[newp + 9] := EREC.u64[old + 9];
  EREC.u64[newp + 10] := EREC.u64[old + 10];
  return newp
}

/-- Rebuild each rule record of `(ro, rl)` with the given NESTED fire (its level and pin slices in
`EREC`), as fresh `EREC` records; the twin's `rules.map`, a self-recursion consing each new record
pointer onto the rest's slice (`sl_cons`, D18). -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:498-509 ConRon.Arena.tgtStoredRules
@[l_impl ConRon.Arena.tgtStoredRules]
def tgtStoredRulesRemap : FunDecl := lfn (ro, rl, flo, fll, fpo, fpl) locals (newp, to, tl, qo, ql) {
  if rl == 0 { return (0, 0) };
  newp := call tgt_rule_nested(IW.u64[ro], flo, fll, fpo, fpl);
  (to, tl) := call tgt_stored_rules_remap(ro + 1, rl - 1, flo, fll, fpo, fpl);
  (qo, ql) := call sl_cons(newp, to, tl);
  return (qo, ql)
}

/-- **`tgt_stored_rules`**: `sum_rules` at the major's parameters and constructors; at an OUTSIDE
major every rule's fire is recomputed once (`aux_rule_fire`, its slices in `IW`), its slices copied
to `EREC` (`er_from_iw`: a rule record's fire slices are read from the record pool, `decRule`), and
the rules rebuilt. -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:498-509 ConRon.Arena.tgtStoredRules
@[l_impl ConRon.Arena.tgtStoredRules]
def tgtStoredRules : FunDecl := lfn (vis, cv, rP, M, rhso, rhsl)
    locals (ro, rl, fk, flo, fll, fpo, fpl, elo, ell, epo, epl, no, nl) {
  (ro, rl) := call sum_rules(vis, EREC.u64[cv], IW.u64[M + 4], IW.u64[M + 6], IW.u64[M + 7],
    rhso, rhsl);
  if IW.u64[M + 8] != 0 { return (ro, rl) };
  (fk, flo, fll, fpo, fpl) := call aux_rule_fire(M, rP);
  (elo, ell) := call er_from_iw(flo, fll);
  (epo, epl) := call er_from_iw(fpo, fpl);
  (no, nl) := call tgt_stored_rules_remap(ro, rl, elo, ell, epo, epl);
  return (no, nl)
}

/-- `block_nested_bit_go(reco, recl, k)`: some recursor's major is not a member
(`recs.any (fun rc => !(rc.tgt < k))`), a self-recursion. -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:511-515 ConRon.Arena.blockNestedBit
@[l_impl ConRon.Arena.blockNestedBit]
def blockNestedBitGo : FunDecl := lfn (reco, recl, k) locals (r) {
  if recl == 0 { return 0 };
  if k <= IW.u64[IW.u64[reco] + 3] { return 1 };
  r := call block_nested_bit_go(reco + 1, recl - 1, k);
  return r
}

/-- **`block_nested_bit`**: some field kind is not flat, or some recursor's major is not a
member. -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:511-515 ConRon.Arena.blockNestedBit
@[l_impl ConRon.Arena.blockNestedBit]
def blockNestedBit : FunDecl := lfn (p, ko, kl) locals (flat, r) {
  flat := call nest_kinds_flat(ko, kl);
  if flat == 0 { return 1 };
  r := call block_nested_bit_go(IW.u64[p + 2], IW.u64[p + 3], IW.u64[p + 1]);
  return r
}

/-- `rule_copy(b, old)`: the 11 words of the rule record at `old` copied to `EREC[b ‥ b + 11)`. -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:517-534 ConRon.Arena.consBlockRecsTF
@[l_impl ConRon.Arena.consBlockRecsTF]
def ruleCopy : FunDecl := lfn (b, old) locals () {
  EREC.u64[b] := EREC.u64[old];
  EREC.u64[b + 1] := EREC.u64[old + 1];
  EREC.u64[b + 2] := EREC.u64[old + 2];
  EREC.u64[b + 3] := EREC.u64[old + 3];
  EREC.u64[b + 4] := EREC.u64[old + 4];
  EREC.u64[b + 5] := EREC.u64[old + 5];
  EREC.u64[b + 6] := EREC.u64[old + 6];
  EREC.u64[b + 7] := EREC.u64[old + 7];
  EREC.u64[b + 8] := EREC.u64[old + 8];
  EREC.u64[b + 9] := EREC.u64[old + 9];
  EREC.u64[b + 10] := EREC.u64[old + 10];
  return 0
}

/-- `rules_to_erec_go(base, ro, rl)`: copy the 11-word rule records `IW[ro ‥ ro + rl)` point to into
the `EREC` run at `base`, first to last; a self-recursion. -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:517-534 ConRon.Arena.consBlockRecsTF
@[l_impl ConRon.Arena.consBlockRecsTF]
def rulesToErecGo : FunDecl := lfn (base, ro, rl) locals (u) {
  if rl == 0 { return 0 };
  u := call rule_copy(base, IW.u64[ro]);
  u := call rules_to_erec_go(base + 11, ro + 1, rl - 1);
  return 0
}

/-- Copy an `IW` pointer-list of 11-word rule records into one fresh CONSECUTIVE `EREC` run (a
capacity abort above `2^32` rules). -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:517-534 ConRon.Arena.consBlockRecsTF
@[l_impl ConRon.Arena.consBlockRecsTF]
def rulesToErec : FunDecl := lfn (ro, rl) locals (base, u) {
  if 4294967296 <= rl { abort };
  base := call erec_alloc(rl * 11);
  u := call rules_to_erec_go(base, ro, rl);
  return (base, rl)
}

/-- `rec_info_rec(cv, mI, rP, reo, rel)`: a fresh 9-word `.recInfo` record (kind `5`, `cv`'s 4 words
inline, `major`, `pre`, the rules' run). -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:517-534 ConRon.Arena.consBlockRecsTF
@[l_impl ConRon.Arena.consBlockRecsTF]
def recInfoRec : FunDecl := lfn (cv, mI, rP, reo, rel) locals (q) {
  q := call erec_alloc(9);
  EREC.u64[q] := 5;
  EREC.u64[q + 1] := EREC.u64[cv];
  EREC.u64[q + 2] := EREC.u64[cv + 1];
  EREC.u64[q + 3] := EREC.u64[cv + 2];
  EREC.u64[q + 4] := EREC.u64[cv + 3];
  EREC.u64[q + 5] := mI;
  EREC.u64[q + 6] := rP;
  EREC.u64[q + 7] := reo;
  EREC.u64[q + 8] := rel;
  return q
}

/-- Build the `recInfo` record (kind `5`: `cv`'s 4 words inline, `major`, `pre`, the rules copied
to one fresh `EREC` run) and `env_push` it. -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:517-534 ConRon.Arena.consBlockRecsTF
@[l_impl ConRon.Arena.consBlockRecsTF]
def consBlockRecsPush : FunDecl := lfn (vis, cv, mI, rP, ro, rl) locals (reo, rel, q, nvis) {
  (reo, rel) := call rules_to_erec(ro, rl);
  q := call rec_info_rec(cv, mI, rP, reo, rel);
  nvis := call env_push(vis, q);
  return nvis
}

/-- **`cons_block_recs_tf`**: the checked family consed through the index, at its majors; the
rules' lookups at the constructors' visibility bound `vis₂` (fixed), the recursors pushed above
the growing `vis`; the twin's list recursion. -/
-- con-ron: ConRon/Arena/Inductives/RecCheck.lean:517-534 ConRon.Arena.consBlockRecsTF
@[l_impl ConRon.Arena.consBlockRecsTF]
def consBlockRecsTF : FunDecl := lfn (vis2, p, m, lo, ll, vis)
    locals (trip, cv, M, rhso, rhsl, mI, rP, ro, rl, nvis, r) {
  if ll == 0 { return vis };
  trip := IW.u64[lo];
  cv := IW.u64[trip];
  M := IW.u64[trip + 1];
  rhso := IW.u64[trip + 2];
  rhsl := IW.u64[trip + 3];
  mI := call block_shape_major_idx_at(p, m);
  rP := call block_shape_rule_prefix_at(p, m);
  (ro, rl) := call tgt_stored_rules(vis2, cv, rP, M, rhso, rhsl);
  nvis := call cons_block_recs_push(vis, cv, mI, rP, ro, rl);
  r := call cons_block_recs_tf(vis2, p, m + 1, lo + 1, ll - 1, nvis);
  return r
}

/-! ## The program -/

/-- This module's functions. -/
def recCheckFns : Prog :=
  [("target_abs_const", targetAbsConst),
   ("target_abs_node", targetAbsNode), ("target_abs_go", targetAbsGo), ("target_abs", targetAbs),
   ("target_holes", targetHoles), ("mk_target_major", mkTargetMajor),
   ("target_major_default", targetMajorDefault), ("target_major_at", targetMajorAt),
   ("erase_fvar_tys", eraseFVarTys), ("target_canon_params", targetCanonParams),
   ("target_params_def_eq_step", targetParamsDefEqStep),
   ("target_params_def_eq", targetParamsDefEq), ("target_class_match", targetClassMatch),
   ("ctors_have_name", ctorsHaveName), ("target_major_nfs", targetMajorNfs),
   ("target_ctors_of", targetCtorsOf), ("target_outside_inst", targetOutsideInst),
   ("target_major_of_member", targetMajorOfMember),
   ("target_major_of_outside_closed", targetMajorOfOutsideClosed),
   ("target_major_of_outside_occ", targetMajorOfOutsideOcc),
   ("target_major_of_outside", targetMajorOfOutside),
   ("target_major_of_outside_tail", targetMajorOfOutsideTail), ("target_major_of", targetMajorOf),
   ("target_major_of_const", targetMajorOfConst),
   ("target_pin_tys", targetPinTys), ("target_major_pins", targetMajorPins),
   ("block_rec_split_own_aux", blockRecSplitOwnAux),
   ("block_rec_want_aux_names", blockRecWantAuxNames), ("ptr_names_copy", ptrNamesCopy), ("ptr_list_names", ptrListNames),
   ("target_rec_pins_names", targetRecPinsNames), ("target_rec_pins_split", targetRecPinsSplit),
   ("target_rec_pins", targetRecPins), ("target_ctor_at", targetCtorAt),
   ("erase_each", eraseEach), ("target_k53_tele", targetK53Tele),
   ("target_k53_heads", targetK53Heads), ("target_k53_args", targetK53Args),
   ("target_k53", targetK53), ("target_pi_doms_with", targetPiDomsWith),
   ("abstract_prefix", abstractPrefix), ("abstract_prefix_list", abstractPrefixList),
   ("aux_rule_fire", auxRuleFire), ("tgt_rule_nested", tgtRuleNested), ("tgt_stored_rules_remap", tgtStoredRulesRemap),
   ("tgt_stored_rules", tgtStoredRules), ("block_nested_bit_go", blockNestedBitGo), ("block_nested_bit", blockNestedBit),
   ("rule_copy", ruleCopy), ("rules_to_erec_go", rulesToErecGo), ("rec_info_rec", recInfoRec), ("rules_to_erec", rulesToErec), ("cons_block_recs_push", consBlockRecsPush),
   ("cons_block_recs_tf", consBlockRecsTF)]

/-- Stubs for the functions of OTHER modules this module calls.

* `nest_container`, `nest_occ`, `inst_pis_with`, `nest_kinds_flat`, `block_shape_major_idx_at`,
  `block_shape_rule_prefix_at`, `pi_binders` and `block_split`/`block_shape_member_names`/
  `block_shape_all_ctors`/`block_rec_lps_ok`/`block_rec_names_unreserved` are `Inductives/
  Positivity.lean`'s and `BlockParts.lean`'s, per the brief's exact conventions.
* `replace_fvars` is `IndPos`'s `FvMap` replacement; `param_levels` is `IndSum`'s; `sum_rules` is
  `IndSum`'s `sumRules`, read at a resolved major's parameter count and constructors.
* `block_rec_name_set_ok(members.off, members.len, recs.off, recs.len)`: the brief left this
  callee's parameter convention unstated (`block_rec_name_set_ok(...)`); this module ASSUMES the
  twin's own argument order, `blockRecNameSetOk (members : List MemberShape) (recs : List
  RecShape)`, flattened to four words. -/
def recCheckForeign : Prog :=
  [("nest_container", stub 2), ("nest_occ", stub 5), ("inst_pis_with", stub 3),
   ("replace_fvars", stub 2), ("nest_kinds_flat", stub 2), ("param_levels", stub 2),
   ("block_shape_member_names", stub 1), ("block_shape_all_ctors", stub 1),
   ("block_rec_lps_ok", stub 1), ("block_rec_names_unreserved", stub 2),
   ("block_rec_name_set_ok", stub 4), ("block_split", stub 2),
   ("block_shape_major_idx_at", stub 2), ("block_shape_rule_prefix_at", stub 2),
   ("pi_binders", stub 2), ("sum_rules", stub 7), ("block_shape_lps", stub 1),
   ("er_from_iw", stub 2)]

-- `abstract_prefix` at `k = 0`: the identity.
#guard
  match run (recCheckFns ++ libFns ++ stubFns ++ masterFns ++ recCheckForeign) 1000
    "abstract_prefix" [0, 5, 42] testMem with
  | .ok ([42], _) => true
  | _ => false

-- `target_holes` at an empty telescope: the empty list.
#guard
  match run (recCheckFns ++ libFns ++ stubFns ++ masterFns ++ recCheckForeign) 1000
    "target_holes" [0, 0, 5] testMem with
  | .ok ([_, 0], _) => true
  | _ => false

-- `target_major_at` hits a stored class directly (no default).
#guard
  match run (recCheckFns ++ libFns ++ stubFns ++ masterFns ++ recCheckForeign) 1000
    "sl_new1" [77] testMem with
  | .ok ([o, 1], m1) =>
    (match run (recCheckFns ++ libFns ++ stubFns ++ masterFns ++ recCheckForeign) 1000
      "target_major_at" [o, 1, 0] m1 with
     | .ok ([77], _) => true
     | _ => false)
  | _ => false

-- `cons_block_recs_tf` over an empty list: the view is unchanged, nothing else read.
#guard
  match run (recCheckFns ++ libFns ++ stubFns ++ masterFns ++ recCheckForeign) 1000
    "cons_block_recs_tf" [0, 0, 0, 0, 0, 5] testMem with
  | .ok ([5], _) => true
  | _ => false

end L.Ind
