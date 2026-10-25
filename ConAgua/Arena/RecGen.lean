import ConAgua.Arena.IndIface
import ConAgua.Arena.Reasons

/-!
# `RecGen`: the generated-recursor stage, from `ClassSlot.isMinor` to `genRecCheck`

The L translation of `vendor/con-ron/ConRon/Arena/Inductives/GenRec.lean` from `ClassSlot.isMinor`
to the end (lane `induct`, round 1, worker G). No proofs this round: every `FunDecl` here is a
best-effort faithful translation, tagged `@[l_impl ConRon.Arena.<T>]` for its twin function `T`;
a helper split off a twin function carries the same tag.

Callees outside this module: the library (`libFns`), the stubs (`stubFns`), the master
environment/interning/level/memo primitives (`masterFns`), all from `IndIface`, and the following
**foreign** callees of other `induct` modules (`recGenForeign`, arity per the naming rule, derived
from the twin's signature):

* module `IndPos`: `nest_occ(names.off, names.len, lo, hi, e) → b`.
* module `IndParts`: `pi_binders(fuel, e) → (bs.off, bs.len, body)`,
  `block_large_elim_allowed(p, nested) → b`, `block_shape_member_names(p) → (off, len)`.
* module `RecCheck`: `target_pi_doms_with(xs.off, xs.len, e) → (ok, off, len)`,
  `target_k53(vis, p, ft.off, ft.len, mc, tele.off, tele.len, majDom, f) → b`,
  `target_major_at(ms.off, ms.len, c) → m`, `target_ctor_at(m, c) → e`,
  `target_major_of(vis, p, ctorsAs.off, ctorsAs.len, pfvs.off, pfvs.len, fvs.off, fvs.len, mty) → m`,
  `target_major_pins(vis, rP, m) → 0`,
  `target_major_nfs(vis, p, ft.off, ft.len, pfvs.off, pfvs.len, us, ds.off, ds.len, ctors.off,
  ctors.len, tbl.off, tbl.len) → (off, len)`, `target_canon_params(pfvs.off, pfvs.len, e) → e'`,
  `target_rec_pins(p, block.off, block.len) → 0`.
* module `RecClass`: `class_gen_rec_ty(g, c) → (ok, e)`,
  `class_gen_rule(g, recCls.off, recCls.len, cvGs.off, cvGs.len, rlvls, c, x) → (ok, e)`,
  `class_gen_prefix_binders(g) → (ok, off, len)`,
  `class_read(p, vis, nP, recs.off, recs.len) → (ok, rd)`,
  `class_read_classes(slots.off, slots.len) → (off, len)`.
* module `IndSum`: `struct_elim_level(elim, large) → e`, `param_levels(off, len) → us`.
* module `IndPos2`: `nest_seed_of(ctx, holes.off, holes.len, I, us, ds.off, ds.len, nPc) → (key, n)`.
* module `IndPos`: `inst_pis_with(ds.off, ds.len, e) → (ok, e')`.

`BlockShape.k`, `.majorIdxAt`, `.rulePrefixAt` are read inline (plain field reads of the
`BlockShape`/`RecShape` records, no call needed). `exprGetD` (used once, in `classFieldsAgree`) is
inlined too: `xs.getD i (intern_bvar 0)`.
-/

namespace L.Ind

open L.Arena

/-! ## `ClassSlot.isMinor`, `classMinorSlot` -/

/-- `class_slot_is_minor(s)`: the slot's tag is `1` (`.minor`). -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:322-326 ConRon.Arena.ClassSlot.isMinor
@[l_impl ConRon.Arena.ClassSlot.isMinor]
def classSlotIsMinor : FunDecl := lfn (s) locals () {
  return u64(IW.u64[s] == 1)
}

/-- `classMinorSlot` helper, a small recursive helper (not a `while` loop, so that its proof is
plain induction on the fuel, as `bbGo`): scans slots `off + j, …, off + j + rem - 1` (`off` the
slots' fixed base, `j` the current index), counting the `.minor c cc _` hits and remembering the
last one's `ihs`. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:328-338 ConRon.Arena.classMinorSlot
@[l_impl ConRon.Arena.classMinorSlot]
def classMinorSlotGo : FunDecl := lfn (off, rem, j, c, cc, cnt, rS, rOff, rLen)
    locals (p, cnt2, rS2, rOff2, rLen2) {
  if rem == 0 { return (cnt, rS, rOff, rLen) };
  p := IW.u64[off + j];
  if IW.u64[p] == 1 && IW.u64[p + 1] == c && IW.u64[p + 2] == cc {
    (cnt2, rS2, rOff2, rLen2) := call class_minor_slot_go(off, rem - 1, j + 1, c, cc, cnt + 1,
      j, IW.u64[p + 3], IW.u64[p + 4])
  } else {
    (cnt2, rS2, rOff2, rLen2) := call class_minor_slot_go(off, rem - 1, j + 1, c, cc, cnt, rS,
      rOff, rLen)
  };
  return (cnt2, rS2, rOff2, rLen2)
}

/-- `class_minor_slot(rd, c, cc)`: the single slot of `rd.slots` that is `.minor c cc _`, as
`(s, ihs.off, ihs.len)`; aborts if there is not exactly one. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:328-338 ConRon.Arena.classMinorSlot
@[l_impl ConRon.Arena.classMinorSlot]
def classMinorSlotL : FunDecl := lfn (rd, c, cc) locals (cnt, rS, rOff, rLen) {
  (cnt, rS, rOff, rLen) := call class_minor_slot_go(IW.u64[rd], IW.u64[rd + 1], 0, c, cc, 0, 0, 0,
    0);
  if cnt != 1 { fail R_GENERATED_RECURSOR_THE_RECURSORS };
  return (rS, rOff, rLen)
}

/-! ## `classFieldsOf` -/

/-- `classFieldsOf` helper: the count and (if one) the class of the hits of `ihs` at field `i`. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:340-361 ConRon.Arena.classFieldsOf
@[l_impl ConRon.Arena.classFieldsOf]
def classFieldsOfHits : FunDecl := lfn (ihsOff, ihsLen, i) locals (q, cnt, cls) {
  if ihsLen == 0 { return (0, 0) };
  q := IW.u64[ihsOff];
  (cnt, cls) := call class_fields_of_hits(ihsOff + 1, ihsLen - 1, i);
  if IW.u64[q] == i {
    if cnt == 0 { return (1, IW.u64[q + 1]) };
    return (cnt + 1, cls)
  };
  return (cnt, cls)
}

/-- `class_fields_of_go(mn.off, mn.len, ihs.off, ihs.len, i, fs.off, fs.len)`: `classFieldsOf`'s
recursion (from field index `i`), the `ClassField` records consed onto the rest's slice. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:340-361 ConRon.Arena.classFieldsOf
@[l_impl ConRon.Arena.classFieldsOf]
def classFieldsOfGo : FunDecl := lfn (mnOff, mnLen, ihsOff, ihsLen, i, fsOff, fsLen)
    locals (w, occ, hc, hCls, bsOff, bsLen, body, cf, ro, rl, o, l) {
  if fsLen == 0 { return (0, 0) };
  w := call fvar_type_d(IW.u64[fsOff]);
  occ := call nest_occ(mnOff, mnLen, 0, 0, w);
  (hc, hCls) := call class_fields_of_hits(ihsOff, ihsLen, i);
  if occ == 0 && hc == 0 {
    cf := call iw_alloc(1);
    IW.u64[cf] := 0
  } else {
    if occ != 0 && hc == 1 {
      (bsOff, bsLen, body) := call pi_binders(⟪CWF⟫, w);
      cf := call rec3(1, hCls, bsLen)
    } else { fail R_GENERATED_RECURSOR_THE_INDUCTIVE }
  };
  (ro, rl) := call class_fields_of_go(mnOff, mnLen, ihsOff, ihsLen, i + 1, fsOff + 1, fsLen - 1);
  (o, l) := call sl_cons(cf, ro, rl);
  return (o, l)
}

/-- `class_fields_of(p, ihs.off, ihs.len, i0, fs.off, fs.len)`: the `ClassField` of every field of
`fs`, from index `i0`. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:340-361 ConRon.Arena.classFieldsOf
@[l_impl ConRon.Arena.classFieldsOf]
def classFieldsOfL : FunDecl := lfn (p, ihsOff, ihsLen, i0, fsOff, fsLen)
    locals (mnOff, mnLen, o, l) {
  (mnOff, mnLen) := call block_shape_member_names(p);
  (o, l) := call class_fields_of_go(mnOff, mnLen, ihsOff, ihsLen, i0, fsOff, fsLen);
  return (o, l)
}

/-! ## `classNodesAgree`, `classLeafAt`, `classFieldsAgree` -/

/-- `class_nodes_agree(vis, p, ft.off, ft.len, mc, tele.off, tele.len, leaf, fvs.off, fvs.len, i,
es.off, es.len)`: K.53′ at every entry of `es`. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:363-381 ConRon.Arena.classNodesAgree
@[l_impl ConRon.Arena.classNodesAgree]
def classNodesAgreeL : FunDecl := lfn
    (vis, p, ftOff, ftLen, mc, teleOff, teleLen, leaf, fvsOff, fvsLen, i, esOff, esLen)
    locals (j, e, ok, domsOff, domsLen, f, b) {
  j := 0;
  while j < esLen {
    e := IW.u64[esOff + j];
    (ok, domsOff, domsLen) := call target_pi_doms_with(fvsOff, fvsLen, IW.u64[e + 4]);
    if ok == 0 { domsLen := 0 };
    if domsLen <= i { fail R_GENERATED_RECURSOR_A };
    f := IW.u64[domsOff + i];
    b := call target_k53(vis, p, ftOff, ftLen, mc, teleOff, teleLen, leaf, f);
    if b == 0 { fail R_GENERATED_RECURSOR_FIELD_OF };
    j += 1
  };
  return 0
}

/-- `class_leaf_at(m, leaf)`: `leaf`'s walked head is `m`'s inductive. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:383-391 ConRon.Arena.classLeafAt
@[l_impl ConRon.Arena.classLeafAt]
def classLeafAtL : FunDecl := lfn (m, leaf) locals (hd, g, nI, us, z) {
  hd := call get_app_fn_f(⟪CWF⟫, leaf);
  if hd >> 28 != 3 { return 0 };
  (g, nI, us, z) := call e_view(hd);
  return u64(nI == IW.u64[m])
}

/-- `class_fields_agree(vis, p, ft.off, ft.len, ms.off, ms.len, fvs.off, fvs.len, es.off, es.len,
i0, ks.off, ks.len)`: node agreement at every recursive field of `ks`, from index `i0`. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:393-413 ConRon.Arena.classFieldsAgree
@[l_impl ConRon.Arena.classFieldsAgree]
def classFieldsAgreeL : FunDecl := lfn
    (vis, p, ftOff, ftLen, msOff, msLen, fvsOff, fvsLen, esOff, esLen, i0, ksOff, ksLen)
    locals (j, i, kf, tag, t, tele, fv, fty, ok, teleOff, teleLen, leaf, mt, b) {
  j := 0;
  i := i0;
  while j < ksLen {
    kf := IW.u64[ksOff + j];
    tag := IW.u64[kf];
    if tag == 1 {
      t := IW.u64[kf + 1];
      tele := IW.u64[kf + 2];
      if i < fvsLen { fv := IW.u64[fvsOff + i] } else { fv := call intern_bvar(0) };
      fty := call fvar_type_d(fv);
      (ok, teleOff, teleLen, leaf) := call strip_pis(tele, fty);
      if ok == 0 { abort };
      mt := call target_major_at(msOff, msLen, t);
      b := call class_leaf_at(mt, leaf);
      if b == 0 { fail R_GENERATED_RECURSOR_FIELD };
      b := call class_nodes_agree(vis, p, ftOff, ftLen, mt, teleOff, teleLen, leaf, fvsOff, fvsLen,
        i, esOff, esLen)
    };
    i := i + 1;
    j += 1
  };
  return 0
}

/-! ## `classCtorOf`, `classCtorsOf`, `classesCtors` -/

/-- `classCtorOf` helper: the entries of `nfs` whose `ctor` is `name`. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:415-439 ConRon.Arena.classCtorOf
@[l_impl ConRon.Arena.classCtorOf]
def classCtorOfNfs : FunDecl := lfn (nfsOff, nfsLen, name) locals (q, j, nf, rp) {
  q := call iw_alloc(nfsLen);
  j := 0;
  rp := 0;
  while j < nfsLen {
    nf := IW.u64[nfsOff + j];
    if IW.u64[nf] == name { IW.u64[q + rp] := nf; rp += 1 };
    j += 1
  };
  return (q, rp)
}

/-- `class_ctor_of(vis, p, ft.off, ft.len, rd, ms.off, ms.len, c, cA)`: class `c`'s constructor
`cA`, read for the generator. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:415-439 ConRon.Arena.classCtorOf
@[l_impl ConRon.Arena.classCtorOf]
def classCtorOfL : FunDecl := lfn (vis, p, ftOff, ftLen, rd, msOff, msLen, c, cA)
    locals (m, cv, esOff, esLen, e0, s0, ihsOff, ihsLen, ok, fvsOff, fvsLen, body, kindsOff,
      kindsLen, t0, tyD, cc, r) {
  m := call target_major_at(msOff, msLen, c);
  cv := IW.u64[cA];
  (esOff, esLen) := call class_ctor_of_nfs(IW.u64[m + 9], IW.u64[m + 10], EREC.u64[cv]);
  if esLen == 0 { abort };
  e0 := IW.u64[esOff];
  (s0, ihsOff, ihsLen) := call class_minor_slot(rd, c, EREC.u64[cv]);
  (ok, fvsOff, fvsLen, body) := call open_pis_at_fvars_f(IW.u64[cA + 1], IW.u64[e0 + 4],
    IW.u64[p + 4] + IW.u64[p + 1]);
  if ok == 0 { abort };
  (kindsOff, kindsLen) := call class_fields_of(p, ihsOff, ihsLen, 0, fvsOff, fvsLen);
  r := call class_fields_agree(vis, p, ftOff, ftLen, msOff, msLen, fvsOff, fvsLen, esOff, esLen, 0,
    kindsOff, kindsLen);
  t0 := call target_ctor_at(m, cv);
  (ok, tyD) := call inst_pis_with(IW.u64[m + 2], IW.u64[m + 3], t0);
  if ok == 0 { abort };
  cc := call rec6(cv, IW.u64[cA + 1], kindsOff, kindsLen, tyD, IW.u64[e0 + 4]);
  return cc
}

/-- `class_ctors_of(vis, p, ft.off, ft.len, rd, ms.off, ms.len, c, cAs.off, cAs.len)`: every
constructor of class `c`. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:441-450 ConRon.Arena.classCtorsOf
@[l_impl ConRon.Arena.classCtorsOf]
def classCtorsOfL : FunDecl := lfn (vis, p, ftOff, ftLen, rd, msOff, msLen, c, cAsOff, cAsLen)
    locals (q, j, cc) {
  q := call iw_alloc(cAsLen);
  j := 0;
  while j < cAsLen {
    cc := call class_ctor_of(vis, p, ftOff, ftLen, rd, msOff, msLen, c, IW.u64[cAsOff + j]);
    IW.u64[q + j] := cc;
    j += 1
  };
  return (q, cAsLen)
}

/-- `classes_ctors(vis, p, ft.off, ft.len, rd, ms.off, ms.len)`: every class's constructors (class
`c`'s majors read at `ms[c]`, the twin's walked tail being `ms`'s own tail). -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:452-461 ConRon.Arena.classesCtors
@[l_impl ConRon.Arena.classesCtors]
def classesCtorsL : FunDecl := lfn (vis, p, ftOff, ftLen, rd, msOff, msLen)
    locals (q, c, m, xsOff, xsLen, hdr) {
  q := call iw_alloc(msLen);
  c := 0;
  while c < msLen {
    m := IW.u64[msOff + c];
    (xsOff, xsLen) := call class_ctors_of(vis, p, ftOff, ftLen, rd, msOff, msLen, c,
      IW.u64[m + 6], IW.u64[m + 7]);
    hdr := call rec2(xsOff, xsLen);
    IW.u64[q + c] := hdr;
    c += 1
  };
  return (q, msLen)
}

/-! ## `classMajors`, `classesNfs` -/

/-- `class_majors(vis, p, ctorsAs.off, ctorsAs.len, pfvs.off, pfvs.len, keys.off, keys.len)`: every
class checked as a major. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:463-476 ConRon.Arena.classMajors
@[l_impl ConRon.Arena.classMajors]
def classMajorsL : FunDecl := lfn (vis, p, ctorsAsOff, ctorsAsLen, pfvsOff, pfvsLen, keysOff,
    keysLen)
    locals (key, hd, mty, m, r, ro, rl, qo, ql) {
  if keysLen == 0 { return (0, 0) };
  key := IW.u64[keysOff];
  hd := call intern_const(IW.u64[key], IW.u64[key + 1]);
  if 4294967296 <= hd { abort };
  mty := call mk_app_n_f(hd, IW.u64[key + 2], IW.u64[key + 3]);
  m := call target_major_of(vis, p, ctorsAsOff, ctorsAsLen, pfvsOff, pfvsLen, pfvsOff, pfvsLen,
    mty);
  r := call target_major_pins(vis, IW.u64[p + 4], m);
  (ro, rl) := call class_majors(vis, p, ctorsAsOff, ctorsAsLen, pfvsOff, pfvsLen, keysOff + 1,
    keysLen - 1);
  (qo, ql) := call sl_cons(m, ro, rl);
  return (qo, ql)
}

/-- `classes_nfs(vis, p, ft.off, ft.len, tbl.off, tbl.len, ms.off, ms.len)`: every class with its
entries of `tbl`. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:478-486 ConRon.Arena.classesNfs
@[l_impl ConRon.Arena.classesNfs]
def classesNfsL : FunDecl := lfn (vis, p, ftOff, ftLen, tblOff, tblLen, msOff, msLen)
    locals (q, j, m, esOff, esLen, nm, k) {
  q := call iw_alloc(msLen);
  j := 0;
  while j < msLen {
    m := IW.u64[msOff + j];
    (esOff, esLen) := call target_major_nfs(vis, p, ftOff, ftLen, IW.u64[m + 11], IW.u64[m + 12],
      IW.u64[m + 1], IW.u64[m + 2], IW.u64[m + 3], IW.u64[m + 6], IW.u64[m + 7], tblOff, tblLen);
    nm := call iw_alloc(13);
    k := 0;
    while k < 9 { IW.u64[nm + k] := IW.u64[m + k]; k += 1 };
    IW.u64[nm + 9] := esOff;
    IW.u64[nm + 10] := esLen;
    IW.u64[nm + 11] := IW.u64[m + 11];
    IW.u64[nm + 12] := IW.u64[m + 12];
    IW.u64[q + j] := nm;
    j += 1
  };
  return (q, msLen)
}

/-! ## `classFormerTy`, `classConstOk` -/

/-- `class_former_ty(vis, cvTas.off, cvTas.len, m)`: class `m`'s former type. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:488-500 ConRon.Arena.classFormerTy
@[l_impl ConRon.Arena.classFormerTy]
def classFormerTyL : FunDecl := lfn (vis, cvTasOff, cvTasLen, m) locals (mem, t, cvp, f, q, e, lo, ll) {
  mem := IW.u64[m + 8];
  if mem != 0 {
    t := mem - 1;
    if t < cvTasLen {
      cvp := IW.u64[cvTasOff + t];
      return EREC.u64[cvp + 3]
    };
    e := call intern_bvar(0);
    if 4294967296 <= e { abort };
    return e
  };
  (f, q) := call env_find(IW.u64[m], vis);
  if f == 0 { abort };
  if EREC.u64[q] != 3 { abort };
  (lo, ll) := call er_to_iw(EREC.u64[q + 2], EREC.u64[q + 3]);
  e := call inst_lp_fast(⟪CWF⟫, lo, ll, IW.u64[m + 1], EREC.u64[q + 4]);
  return e
}

/-- `class_const_ok_header(vis, q)`: `classConstOk`'s guards, the syntactic checks of a constant
(the body of lane `decls2`'s `install_header`, whose model `ihW` is this function's). -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:502-523 ConRon.Arena.classConstOk
-- con-ron: CHANGED since 12752ca7 — `ConRon.Arena.classConstOk` changed; re-check the L code and its proofs, then delete this line
@[l_impl ConRon.Arena.classConstOk]
def classConstOkHeader : FunDecl := lfn (vis, q) locals (n, t, f, r, c, s, o, l, d, b, h, a) {
  n := EREC.u64[q];
  t := EREC.u64[q + 3];
  (f, r) := call env_find(n, vis);
  if f != 0 { fail R_DUPLICATE_DECLARATION_2 };
  c := call reserved_contains(n);
  if c != 0 { fail R_RESERVED_BASIS_NAME };
  s := call is_proj_fn_shape(n);
  if s != 0 { fail R_RESERVED_PROJECTION_NAME };
  (o, l) := call cv_lps(q);
  d := call sl_nodup(o, l);
  if d == 0 { fail R_DUPLICATE_UNIVERSE_PARAMETERS_IN };
  b := call loose_bvars_bounded_fast(4000000000, 0, t);
  if b == 0 { abort };
  h := call has_fvar_fast(4000000000, t);
  if h != 0 { abort };
  a := call all_level_params_defined(o, l, t);
  if a == 0 { fail R_UNDECLARED_UNIVERSE_PARAMETER_IN };
  c := call consts_resolve_ffast(vis, t);
  if c == 0 { abort };
  return 0
}

/-- `class_const_ok(vis, cv)`: a generated constant, checked (`checkConstantValF`). -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:502-523 ConRon.Arena.classConstOk
-- con-ron: CHANGED since 12752ca7 — `ConRon.Arena.classConstOk` changed; re-check the L code and its proofs, then delete this line
@[l_impl ConRon.Arena.classConstOk]
def classConstOkL : FunDecl := lfn (vis, cv) locals (u, s) {
  u := call class_const_ok_header(vis, cv);
  s := call infer_type_core(vis, 0, EREC.u64[cv + 3]);
  u := call ensure_sort_core(vis, 0, s);
  return 0
}

/-! ## `classRecTyOk`, `classRecTysOk` -/

/-- `class_rec_ty_ok(vis, g, k, rc, cvRi, c)`: recursor `c`'s generated type, checked and compared
with the stream's `cvRi`. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:525-545 ConRon.Arena.classRecTyOk
@[l_impl ConRon.Arena.classRecTyOk]
def classRecTyOkL : FunDecl := lfn (vis, g, k, rc, cvRi, c)
    locals (u, ok, gty, cvp, cvG, r, eq) {
  u := call class_rec_ty_ok_guards(g, k, rc, c);
  (ok, gty) := call class_gen_rec_ty(g, c);
  if ok == 0 { abort };
  cvp := IW.u64[rc];
  cvG := call cv_new(EREC.u64[cvp], EREC.u64[cvp + 1], EREC.u64[cvp + 2], gty);
  r := call class_const_ok(vis, cvG);
  eq := call is_def_eq_core(vis, 0, EREC.u64[cvRi + 3], gty);
  if eq == 0 { fail R_GENERATED_RECURSOR_THE_TYPE };
  return cvG
}

/-- `class_rec_ty_ok_guards(g, k, rc, c)`: `classRecTyOk`'s guards: the record's member, rule
prefix and major index are the generated ones (aborts where the twin fails; the word sums must not
wrap). -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:525-545 ConRon.Arena.classRecTyOk
@[l_impl ConRon.Arena.classRecTyOk]
def classRecTyOkGuards : FunDecl := lfn (g, k, rc, c) locals (ci, memw, memv) {
  ci := call target_major_at(IW.u64[g + 3], IW.u64[g + 4], c);
  memw := IW.u64[ci + 8];
  memv := k;
  if memw != 0 { memv := memw - 1 };
  if IW.u64[rc + 3] != memv { fail R_GENERATED_RECURSOR_THE_RECURSOR_RECORD };
  if IW.u64[rc + 1] != IW.u64[g] + IW.u64[g + 8] { fail R_GENERATED_RECURSOR_THE_RECURSOR_RECORD_S };
  if IW.u64[rc + 1] + IW.u64[ci + 5] < IW.u64[rc + 1] { abort };
  if IW.u64[rc + 2] != IW.u64[rc + 1] + IW.u64[ci + 5] { fail R_GENERATED_RECURSOR_THE_RECURSOR_RECORD_S };
  return 0
}

/-- `class_rec_tys_ok(vis, g, k, rcs.off, rcs.len, cvs.off, cvs.len, cs.off, cs.len)`: every
recursor's generated type, pairwise with `cvs` and `cs` (stops once `rcs` runs out; aborts if
`cvs`/`cs` run out first). -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:547-557 ConRon.Arena.classRecTysOk
@[l_impl ConRon.Arena.classRecTysOk]
def classRecTysOkL : FunDecl := lfn (vis, g, k, rcsOff, rcsLen, cvsOff, cvsLen, csOff, csLen)
    locals (x, o, l, o2, l2) {
  if rcsLen == 0 { return (0, 0) };
  if cvsLen == 0 || csLen == 0 { abort };
  x := call class_rec_ty_ok(vis, g, k, IW.u64[rcsOff], IW.u64[cvsOff], IW.u64[csOff]);
  (o, l) := call class_rec_tys_ok(vis, g, k, rcsOff + 1, rcsLen - 1, cvsOff + 1, cvsLen - 1, csOff + 1,
    csLen - 1);
  (o2, l2) := call sl_cons(x, o, l);
  return (o2, l2)
}

/-! ## `classRuleOk`, `classRulesOk`, `classRecsRulesOk` -/

/-- `classRuleOk` helper: `rbs.allM (fun b => constsResolveFFast (feR.restrictTo visT) b)`. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:559-587 ConRon.Arena.classRuleOk
@[l_impl ConRon.Arena.classRuleOk]
def classRuleOkDomains : FunDecl := lfn (visT, off, cnt) locals (b, r) {
  if cnt == 0 { return 1 };
  b := call consts_resolve_ffast(visT, IW.u64[off]);
  if b == 0 { return 0 };
  r := call class_rule_ok_domains(visT, off + 1, cnt - 1);
  return r
}

/-- `class_rule_ok_guards(visR, cvR, gen)`: `classRuleOk`'s first guards: closed, its level
parameters the recursor's, resolving. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:559-587 ConRon.Arena.classRuleOk
@[l_impl ConRon.Arena.classRuleOk]
def classRuleOkGuards : FunDecl := lfn (visR, cvR, gen) locals (b, lo, ll) {
  b := call loose_bvars_bounded_fast(⟪CWF⟫, 0, gen);
  if b == 0 { abort };
  b := call has_fvar_fast(⟪CWF⟫, gen);
  if b != 0 { abort };
  (lo, ll) := call cv_lps(cvR);
  b := call all_level_params_defined(lo, ll, gen);
  if b == 0 { abort };
  b := call consts_resolve_ffast(visR, gen);
  if b == 0 { abort };
  return 0
}

/-- `class_rule_ok(visT, visR, cvR, n, gen)`: one generated rule, installed as generated. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:559-587 ConRon.Arena.classRuleOk
@[l_impl ConRon.Arena.classRuleOk]
def classRuleOkL : FunDecl := lfn (visT, visR, cvR, n, gen)
    locals (u, s, f, ok, rbsOff, rbsLen, bodyD, closed) {
  u := call class_rule_ok_guards(visR, cvR, gen);
  s := call infer_type_core(visR, 0, gen);
  f := call flush_caches();
  (ok, rbsOff, rbsLen, bodyD) := call strip_lams(n, gen);
  if ok == 0 { abort };
  closed := call class_rule_ok_domains(visT, rbsOff, rbsLen);
  if closed == 0 { abort };
  return gen
}

/-- `class_rules_ok_one(visT, visR, g, cvR, x, gen)`: `classRulesOk`'s rule check at the telescope
length `nP + |slots| + nF` (aborts on a word overflow, a capacity). -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:589-603 ConRon.Arena.classRulesOk
@[l_impl ConRon.Arena.classRulesOk]
def classRulesOkOne : FunDecl := lfn (visT, visR, g, cvR, x, gen) locals (nn, r) {
  nn := IW.u64[g] + IW.u64[g + 8];
  if nn + IW.u64[x + 1] < nn { abort };
  r := call class_rule_ok(visT, visR, cvR, nn + IW.u64[x + 1], gen);
  return r
}

/-- `class_rules_ok(visT, visR, g, recCls.off, recCls.len, cvGs.off, cvGs.len, cvR, c, xs.off,
xs.len)`: a recursor's generated rules, one per constructor `xs` (the twin's recursion; the telescope
length `nP + |slots| + nF` aborts on a word overflow, a capacity). -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:589-603 ConRon.Arena.classRulesOk
@[l_impl ConRon.Arena.classRulesOk]
def classRulesOkL : FunDecl := lfn (visT, visR, g, recClsOff, recClsLen, cvGsOff, cvGsLen, cvR, c,
    xsOff, xsLen)
    locals (x, rlvls, ok, gen, r, lo, ll, ro, rl, qo, ql) {
  if xsLen == 0 { return (0, 0) };
  x := IW.u64[xsOff];
  (lo, ll) := call cv_lps(cvR);
  rlvls := call param_levels(lo, ll);
  (ok, gen) := call class_gen_rule(g, recClsOff, recClsLen, cvGsOff, cvGsLen, rlvls, c, x);
  if ok == 0 { fail R_GENERATED_RECURSOR_THE_RULE };
  r := call class_rules_ok_one(visT, visR, g, cvR, x, gen);
  (ro, rl) := call class_rules_ok(visT, visR, g, recClsOff, recClsLen, cvGsOff, cvGsLen, cvR, c,
    xsOff + 1, xsLen - 1);
  (qo, ql) := call sl_cons(r, ro, rl);
  return (qo, ql)
}

/-- `class_recs_rules_ok_go(visT, visR, g, recCls.off, recCls.len, cvGs.off, cvGs.len, cvs.off,
cvs.len, cs.off, cs.len)`: the twin's recursion over the walked tails `cvs`, `cs` of the whole
lists `cvGs`, `recCls`. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:605-618 ConRon.Arena.classRecsRulesOk
@[l_impl ConRon.Arena.classRecsRulesOk]
def classRecsRulesOkGo : FunDecl := lfn (visT, visR, g, recClsOff, recClsLen, cvGsOff, cvGsLen,
    cvsOff, cvsLen, csOff, csLen)
    locals (cvG, c, hdr, xsOff, xsLen, rhssOff, rhssLen, m, rec, ro, rl, qo, ql) {
  if cvsLen == 0 { return (0, 0) };
  if csLen == 0 { return (0, 0) };
  cvG := IW.u64[cvsOff];
  c := IW.u64[csOff];
  xsOff := 0;
  xsLen := 0;
  if c < IW.u64[g + 10] {
    hdr := IW.u64[IW.u64[g + 9] + c];
    xsOff := IW.u64[hdr];
    xsLen := IW.u64[hdr + 1]
  };
  (rhssOff, rhssLen) := call class_rules_ok(visT, visR, g, recClsOff, recClsLen, cvGsOff, cvGsLen,
    cvG, c, xsOff, xsLen);
  m := call target_major_at(IW.u64[g + 3], IW.u64[g + 4], c);
  rec := call rec4(cvG, m, rhssOff, rhssLen);
  (ro, rl) := call class_recs_rules_ok_go(visT, visR, g, recClsOff, recClsLen, cvGsOff, cvGsLen,
    cvsOff + 1, cvsLen - 1, csOff + 1, csLen - 1);
  (qo, ql) := call sl_cons(rec, ro, rl);
  return (qo, ql)
}

/-- `class_recs_rules_ok(visT, visR, g, recCls.off, recCls.len, cvGs.off, cvGs.len)`: every
recursor's generated rules, with its class (the shorter of `cvGs`/`recCls` decides). -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:605-618 ConRon.Arena.classRecsRulesOk
@[l_impl ConRon.Arena.classRecsRulesOk]
def classRecsRulesOkL : FunDecl := lfn (visT, visR, g, recClsOff, recClsLen, cvGsOff, cvGsLen)
    locals (qo, ql) {
  (qo, ql) := call class_recs_rules_ok_go(visT, visR, g, recClsOff, recClsLen, cvGsOff, cvGsLen,
    cvGsOff, cvGsLen, recClsOff, recClsLen);
  return (qo, ql)
}

/-! ## `classStreamRecs`, `classKeyCanon`, `classSeeds`, `classKeyOf` -/

/-- `class_stream_recs(vis, rcs.off, rcs.len)`: the stream's recursor constants, checked. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:620-627 ConRon.Arena.classStreamRecs
@[l_impl ConRon.Arena.classStreamRecs]
def classStreamRecsL : FunDecl := lfn (vis, rcsOff, rcsLen) locals (rc, cv, r, ro, rl, qo, ql) {
  if rcsLen == 0 { return (0, 0) };
  rc := IW.u64[rcsOff];
  cv := IW.u64[rc];
  r := call check_constant_val(vis, cv);
  (ro, rl) := call class_stream_recs(vis, rcsOff + 1, rcsLen - 1);
  (qo, ql) := call sl_cons(cv, ro, rl);
  return (qo, ql)
}

/-- `class_key_canon(params.off, params.len, k)`: `k`'s parameters moved to the canonical ones. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:629-634 ConRon.Arena.classKeyCanon
@[l_impl ConRon.Arena.classKeyCanon]
def classKeyCanonL : FunDecl := lfn (paramsOff, paramsLen, k) locals (dsOff, dsLen, q, u, nk) {
  dsOff := IW.u64[k + 2];
  dsLen := IW.u64[k + 3];
  q := call iw_alloc(dsLen);
  u := call class_key_canon_go(paramsOff, paramsLen, dsOff, dsLen, q, 0);
  nk := call rec4(IW.u64[k], IW.u64[k + 1], q, dsLen);
  return nk
}

/-- `class_key_canon_go(params.off, params.len, ds.off, ds.len, q, j)`: the rest of the key's
parameters moved to the canonical ones, written at `q + j`, … (the loop of `class_key_canon`, as a
recursion). -/
-- con-ron: none — the loop of class_key_canon as a self-recursive function (proof shape)
def classKeyCanonGo : FunDecl := lfn (paramsOff, paramsLen, dsOff, dsLen, q, j) locals (e, u) {
  if j >= dsLen { return 0 };
  e := call target_canon_params(paramsOff, paramsLen, IW.u64[dsOff + j]);
  IW.u64[q + j] := e;
  u := call class_key_canon_go(paramsOff, paramsLen, dsOff, dsLen, q, j + 1);
  return 0
}

/-- `class_seeds(ctx, holes.off, holes.len, ms.off, ms.len)`: the seeds, every outside class of
`ms` in order. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:636-647 ConRon.Arena.classSeeds
@[l_impl ConRon.Arena.classSeeds]
def classSeedsL : FunDecl := lfn (ctx, holesOff, holesLen, msOff, msLen)
    locals (m, key, n, p2, ro, rl, qo, ql) {
  if msLen == 0 { return (0, 0) };
  m := IW.u64[msOff];
  if IW.u64[m + 8] != 0 {
    (ro, rl) := call class_seeds(ctx, holesOff, holesLen, msOff + 1, msLen - 1);
    return (ro, rl)
  };
  (key, n) := call nest_seed_of(ctx, holesOff, holesLen, IW.u64[m], IW.u64[m + 1],
    IW.u64[m + 2], IW.u64[m + 3], IW.u64[m + 4]);
  p2 := call rec2(key, n);
  (ro, rl) := call class_seeds(ctx, holesOff, holesLen, msOff + 1, msLen - 1);
  (qo, ql) := call sl_cons(p2, ro, rl);
  return (qo, ql)
}

/-- `classKeyOf` helper: `k2.ds.allM (closed under nP)`, stopping at the first open one. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:649-661 ConRon.Arena.classKeyOf
@[l_impl ConRon.Arena.classKeyOf]
def classKeyOfClosed : FunDecl := lfn (nP, dsOff, dsLen) locals (e, b, f, r) {
  if dsLen == 0 { return 1 };
  e := IW.u64[dsOff];
  b := call bvar_b(⟪CWF⟫, e);
  if b != 0 { return 0 };
  f := call fvar_b(⟪CWF⟫, e);
  if nP < f { return 0 };
  r := call class_key_of_closed(nP, dsOff + 1, dsLen - 1);
  return r
}

/-- `class_key_of(nP, params.off, params.len, k)`: a class key made checkable. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:649-661 ConRon.Arena.classKeyOf
@[l_impl ConRon.Arena.classKeyOf]
def classKeyOfL : FunDecl := lfn (nP, paramsOff, paramsLen, k) locals (k2, ok) {
  k2 := call class_key_canon(paramsOff, paramsLen, k);
  ok := call class_key_of_closed(nP, IW.u64[k2 + 2], IW.u64[k2 + 3]);
  if ok == 0 { fail R_TARGET_REC_THE_MAJOR };
  return k2
}

/-! ## `checkBlockClasses` -/

/-- `checkBlockClasses` helper: `ks.mapM (classKeyOf p.nP params)`. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:663-682 ConRon.Arena.checkBlockClasses
@[l_impl ConRon.Arena.checkBlockClasses]
def checkBlockClassesKeys : FunDecl := lfn (nP, paramsOff, paramsLen, ksOff, ksLen)
    locals (k2, ro, rl, qo, ql) {
  if ksLen == 0 { return (0, 0) };
  k2 := call class_key_of(nP, paramsOff, paramsLen, IW.u64[ksOff]);
  (ro, rl) := call check_block_classes_keys(nP, paramsOff, paramsLen, ksOff + 1, ksLen - 1);
  (qo, ql) := call sl_cons(k2, ro, rl);
  return (qo, ql)
}

/-- `checkBlockClasses` helper: how many classes of `ms` have the member word `w` (`member ==
some (w - 1)`), as the twin's `(ms.filter (·.member == some t)).length`. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:663-682 ConRon.Arena.checkBlockClasses
@[l_impl ConRon.Arena.checkBlockClasses]
def checkBlockClassesCount : FunDecl := lfn (msOff, msLen, w) locals (r) {
  if msLen == 0 { return 0 };
  r := call check_block_classes_count(msOff + 1, msLen - 1, w);
  if IW.u64[IW.u64[msOff] + 8] == w { r := r + 1 };
  return r
}

/-- `checkBlockClasses` helper: exactly one class per member `t`, for `t = j, …, k - 1` (the twin's
`(List.range p.k).all`, as a recursion). -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:663-682 ConRon.Arena.checkBlockClasses
@[l_impl ConRon.Arena.checkBlockClasses]
def checkBlockClassesOnePerMember : FunDecl := lfn (j, k, msOff, msLen) locals (c, r) {
  if k <= j { return 1 };
  c := call check_block_classes_count(msOff, msLen, j + 1);
  if c != 1 { return 0 };
  r := call check_block_classes_one_per_member(j + 1, k, msOff, msLen);
  return r
}

/-- `check_block_classes(vis, p, params.off, params.len, ctorsAs.off, ctorsAs.len)`: the classes,
read and checked, as `(rd, ms.off, ms.len)`. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:663-682 ConRon.Arena.checkBlockClasses
@[l_impl ConRon.Arena.checkBlockClasses]
def checkBlockClassesL : FunDecl := lfn (vis, p, paramsOff, paramsLen, ctorsAsOff, ctorsAsLen)
    locals (ok, rd, slOff, slLen, ksOff, ksLen, keysOff, keysLen, msOff, msLen, good) {
  (ok, rd) := call class_read(p, vis, IW.u64[p + 4], IW.u64[p + 2], IW.u64[p + 3]);
  if ok == 0 { fail R_GENERATED_RECURSOR_THE_RECURSOR_FAMILY };
  slOff := IW.u64[rd];
  slLen := IW.u64[rd + 1];
  (ksOff, ksLen) := call class_read_classes(slOff, slLen);
  (keysOff, keysLen) := call check_block_classes_keys(IW.u64[p + 4], paramsOff, paramsLen, ksOff,
    ksLen);
  (msOff, msLen) := call class_majors(vis, p, ctorsAsOff, ctorsAsLen, paramsOff, paramsLen, keysOff,
    keysLen);
  good := call check_block_classes_one_per_member(0, IW.u64[p + 1], msOff, msLen);
  if good == 0 { fail R_GENERATED_RECURSOR_THE_RECURSOR };
  return (rd, msOff, msLen)
}

/-! ## `classFeR` -/

/-- `class_fe_r_rec(cv, mi, rp3)`: the rule-less `.recInfo` record of the constant at `cv` (aborts
unless the copied name word is a handle, which `env_push` needs). -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:684-701 ConRon.Arena.classFeR
@[l_impl ConRon.Arena.classFeR]
def classFeRRec : FunDecl := lfn (cv, mi, rp3) locals (q) {
  q := call erec_alloc(9);
  EREC.u64[q] := 5;
  EREC.u64[q + 1] := EREC.u64[cv];
  EREC.u64[q + 2] := EREC.u64[cv + 1];
  EREC.u64[q + 3] := EREC.u64[cv + 2];
  EREC.u64[q + 4] := EREC.u64[cv + 3];
  EREC.u64[q + 5] := mi;
  EREC.u64[q + 6] := rp3;
  EREC.u64[q + 7] := 0;
  EREC.u64[q + 8] := 0;
  if 4294967296 <= EREC.u64[q + 1] { abort };
  return q
}

/-- `class_fe_r_go(cvs.off, cvs.len, rcl, recs.off, recs.len, vis, m)`: the twin's `classFeR.go` at
recursor `m` (the walked tail `cvs` of `cvGs`, `rcl` entries of `recCls` left), as
`(vis', prevs.off, prevs.len)`. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:684-701 ConRon.Arena.classFeR
@[l_impl ConRon.Arena.classFeR]
def classFeRGo : FunDecl := lfn (cvo, cvl, rcl, recsOff, recsLen, vis, m)
    locals (cv, nm, c, q, mi, rp3, rc, kindp, cur, entry, vo, ro, rl, qo, ql) {
  if cvl == 0 { return (vis, 0, 0) };
  if rcl == 0 { return (vis, 0, 0) };
  cv := IW.u64[cvo];
  nm := EREC.u64[cv];
  (c, q) := call env_row_get(nm);
  mi := 0;
  rp3 := 0;
  if m < recsLen {
    rc := IW.u64[recsOff + m];
    mi := IW.u64[rc + 2];
    rp3 := IW.u64[rc + 1]
  };
  kindp := call class_fe_r_rec(cv, mi, rp3);
  cur := call env_push(vis, kindp);
  entry := call rec3(nm, c, q);
  (vo, ro, rl) := call class_fe_r_go(cvo + 1, cvl - 1, rcl - 1, recsOff, recsLen, cur, m + 1);
  (qo, ql) := call sl_cons(entry, ro, rl);
  return (vo, qo, ql)
}

/-- `class_fe_r(p, cvGs.off, cvGs.len, recCls.off, recCls.len, vis)`: the rule-less generated
recursors consed onto the environment, pushed temporarily, as `(vis', prevs.off, prevs.len)`. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:684-701 ConRon.Arena.classFeR
@[l_impl ConRon.Arena.classFeR]
def classFeRL : FunDecl := lfn (p, cvGsOff, cvGsLen, recClsOff, recClsLen, vis) locals (v, o, l) {
  (v, o, l) := call class_fe_r_go(cvGsOff, cvGsLen, recClsLen, IW.u64[p + 2], IW.u64[p + 3], vis, 0);
  return (v, o, l)
}

/-! ## `genRecCheck` -/

/-- `genRecCheck` helper: `nestedBit || ms.any (·.member.isNone)`'s second disjunct. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:703-756 ConRon.Arena.genRecCheck
@[l_impl ConRon.Arena.genRecCheck]
def genRecCheckAnyNoMember : FunDecl := lfn (msOff, msLen) locals (m, r) {
  if msLen == 0 { return 0 };
  m := IW.u64[msOff];
  if IW.u64[m + 8] == 0 { return 1 };
  r := call gen_rec_check_any_no_member(msOff + 1, msLen - 1);
  return r
}

/-- `genRecCheck` helper: `cvTas.map (·.type)`. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:703-756 ConRon.Arena.genRecCheck
@[l_impl ConRon.Arena.genRecCheck]
def genRecCheckFormerTys : FunDecl := lfn (cvTasOff, cvTasLen) locals (q, j) {
  q := call iw_alloc(cvTasLen);
  j := 0;
  while j < cvTasLen { IW.u64[q + j] := EREC.u64[IW.u64[cvTasOff + j] + 3]; j += 1 };
  return (q, cvTasLen)
}

/-- `genRecCheck` helper: `ms2.mapM (classFormerTy fe cvTas)`. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:703-756 ConRon.Arena.genRecCheck
@[l_impl ConRon.Arena.genRecCheck]
def genRecCheckFormerTysC : FunDecl := lfn (vis, cvTasOff, cvTasLen, ms2Off, ms2Len)
    locals (q, j, e) {
  q := call iw_alloc(ms2Len);
  j := 0;
  while j < ms2Len {
    e := call class_former_ty(vis, cvTasOff, cvTasLen, IW.u64[ms2Off + j]);
    IW.u64[q + j] := e;
    j += 1
  };
  return (q, ms2Len)
}

/-- `genRecCheck` helper: `(rd.slots.filter ClassSlot.isMinor).length == (ctors.map
List.length).sum` (a sum past `2^64` is above every slot count: `0`). -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:703-756 ConRon.Arena.genRecCheck
@[l_impl ConRon.Arena.genRecCheck]
def genRecCheckMinorOk : FunDecl := lfn (slotsOff, slotsLen, ctorsOff, ctorsLen)
    locals (j, s, minorCnt, ctorSum, hdr) {
  minorCnt := 0;
  j := 0;
  while j < slotsLen {
    s := call class_slot_is_minor(IW.u64[slotsOff + j]);
    minorCnt := minorCnt + s;
    j += 1
  };
  ctorSum := 0;
  j := 0;
  while j < ctorsLen {
    hdr := IW.u64[ctorsOff + j];
    if ctorSum + IW.u64[hdr + 1] < ctorSum { return 0 };
    ctorSum := ctorSum + IW.u64[hdr + 1];
    j += 1
  };
  return u64(minorCnt == ctorSum)
}

/-- `genRecCheck` helper: the pop, `prevs.foldr (fun (n, prev) acc => acc.popTemp n prev) feR`, in
reverse push order. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:703-756 ConRon.Arena.genRecCheck
@[l_impl ConRon.Arena.genRecCheck]
def genRecCheckPopAll : FunDecl := lfn (vis, prevsOff, prevsLen) locals (j, e) {
  j := prevsLen;
  while 0 < j {
    j := j - 1;
    e := IW.u64[prevsOff + j];
    vis := call env_pop_temp(vis, IW.u64[e], IW.u64[e + 1], IW.u64[e + 2])
  };
  return vis
}

/-- `genRecCheck` helper: the pins, the stream's types, the elim guard, the classes' table entries
and constructors, and the generator up to `cvGs` (checked, generated types). Capacity guards first:
the pool's size `+ 5`, the parameter count plus the member count and plus the slot count are words. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:703-756 ConRon.Arena.genRecCheck
@[l_impl ConRon.Arena.genRecCheck]
def genRecCheckPrep : FunDecl := lfn
    (vis, p, nestedBit, paramsOff, paramsLen, tblOff, tblLen, rd, msOff, msLen, cvTasOff, cvTasLen,
     blockOff, blockLen)
    locals
    (r, cvRisOff, cvRisLen, nb, allowed, ftOff, ftLen, ms2Off, ms2Len, ctorsOff, ctorsLen, minorOk,
     ftcOff, ftcLen, elim, g, preOk, preOff, preLen, cvGsOff, cvGsLen) {
  if len(IW.u64) + 5 < 5 { abort };
  if IW.u64[p + 4] + IW.u64[p + 1] < IW.u64[p + 4] { abort };
  if IW.u64[p + 4] + IW.u64[rd + 1] < IW.u64[p + 4] { abort };
  r := call target_rec_pins(p, blockOff, blockLen);
  (cvRisOff, cvRisLen) := call class_stream_recs(vis, IW.u64[p + 2], IW.u64[p + 3]);
  if IW.u64[p + 1] == 0 { fail R_GENERATED_RECURSOR_THE };
  if IW.u64[p + 7] != 0 {
    nb := nestedBit;
    if nb == 0 { nb := call gen_rec_check_any_no_member(msOff, msLen) };
    allowed := call block_large_elim_allowed(p, nb);
    if allowed == 0 { fail R_GENERATED_RECURSOR_LARGE }
  };
  (ftOff, ftLen) := call gen_rec_check_former_tys(cvTasOff, cvTasLen);
  (ms2Off, ms2Len) := call classes_nfs(vis, p, ftOff, ftLen, tblOff, tblLen, msOff, msLen);
  (ctorsOff, ctorsLen) := call classes_ctors(vis, p, ftOff, ftLen, rd, ms2Off, ms2Len);
  minorOk := call gen_rec_check_minor_ok(IW.u64[rd], IW.u64[rd + 1], ctorsOff, ctorsLen);
  if minorOk == 0 { fail R_GENERATED_RECURSOR_THE_RECURSORS_PREFIX };
  (ftcOff, ftcLen) := call gen_rec_check_former_tys_c(vis, cvTasOff, cvTasLen, ms2Off, ms2Len);
  elim := call struct_elim_level(IW.u64[p + 5], IW.u64[p + 7]);
  g := call iw_alloc(14);
  IW.u64[g] := IW.u64[p + 4];
  IW.u64[g + 1] := paramsOff;
  IW.u64[g + 2] := paramsLen;
  IW.u64[g + 3] := ms2Off;
  IW.u64[g + 4] := ms2Len;
  IW.u64[g + 5] := ftcOff;
  IW.u64[g + 6] := ftcLen;
  IW.u64[g + 7] := IW.u64[rd];
  IW.u64[g + 8] := IW.u64[rd + 1];
  IW.u64[g + 9] := ctorsOff;
  IW.u64[g + 10] := ctorsLen;
  IW.u64[g + 11] := elim;
  IW.u64[g + 12] := 0;
  IW.u64[g + 13] := 0;
  (preOk, preOff, preLen) := call class_gen_prefix_binders(g);
  if preOk == 0 { abort };
  IW.u64[g + 12] := preOff;
  IW.u64[g + 13] := preLen;
  (cvGsOff, cvGsLen) := call class_rec_tys_ok(vis, g, IW.u64[p + 1], IW.u64[p + 2], IW.u64[p + 3],
    cvRisOff, cvRisLen, IW.u64[rd + 2], IW.u64[rd + 3]);
  return (g, cvGsOff, cvGsLen)
}

/-- `gen_rec_check(vis, p, nestedBit, params.off, params.len, tbl.off, tbl.len, rd, ms.off, ms.len,
cvTas.off, cvTas.len, block.off, block.len)`: **the generated recursor stage**, as
`(vis', out.off, out.len)`. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:703-756 ConRon.Arena.genRecCheck
@[l_impl ConRon.Arena.genRecCheck]
def genRecCheckL : FunDecl := lfn
    (vis, p, nestedBit, paramsOff, paramsLen, tblOff, tblLen, rd, msOff, msLen, cvTasOff, cvTasLen,
     blockOff, blockLen)
    locals (g, cvGsOff, cvGsLen, visT, feR, prevsOff, prevsLen, r, outOff, outLen, fe2) {
  (g, cvGsOff, cvGsLen) := call gen_rec_check_prep(vis, p, nestedBit, paramsOff, paramsLen, tblOff,
    tblLen, rd, msOff, msLen, cvTasOff, cvTasLen, blockOff, blockLen);
  visT := vis;
  (feR, prevsOff, prevsLen) := call class_fe_r(p, cvGsOff, cvGsLen, IW.u64[rd + 2], IW.u64[rd + 3],
    vis);
  r := call flush_caches();
  (outOff, outLen) := call class_recs_rules_ok(visT, feR, g, IW.u64[rd + 2], IW.u64[rd + 3],
    cvGsOff, cvGsLen);
  fe2 := call gen_rec_check_pop_all(feR, prevsOff, prevsLen);
  r := call flush_caches();
  return (fe2, outOff, outLen)
}

/-! ## The program, the foreign stubs, closure -/

/-- This module's functions. -/
def recGenFns : Prog :=
  [("class_slot_is_minor", classSlotIsMinor), ("class_minor_slot_go", classMinorSlotGo),
   ("class_minor_slot", classMinorSlotL),
   ("class_fields_of_hits", classFieldsOfHits), ("class_fields_of_go", classFieldsOfGo),
   ("class_fields_of", classFieldsOfL),
   ("class_nodes_agree", classNodesAgreeL), ("class_leaf_at", classLeafAtL),
   ("class_fields_agree", classFieldsAgreeL), ("class_ctor_of_nfs", classCtorOfNfs),
   ("class_ctor_of", classCtorOfL), ("class_ctors_of", classCtorsOfL),
   ("classes_ctors", classesCtorsL), ("class_majors", classMajorsL),
   ("classes_nfs", classesNfsL), ("class_former_ty", classFormerTyL),
   ("class_const_ok_header", classConstOkHeader), ("class_const_ok", classConstOkL), ("class_rec_ty_ok", classRecTyOkL),
   ("class_rec_ty_ok_guards", classRecTyOkGuards),
   ("class_rec_tys_ok", classRecTysOkL), ("class_rule_ok_domains", classRuleOkDomains),
   ("class_rule_ok_guards", classRuleOkGuards), ("class_rule_ok", classRuleOkL), ("class_rules_ok", classRulesOkL),
   ("class_rules_ok_one", classRulesOkOne),
   ("class_recs_rules_ok", classRecsRulesOkL),
   ("class_recs_rules_ok_go", classRecsRulesOkGo), ("class_stream_recs", classStreamRecsL),
   ("class_key_canon", classKeyCanonL), ("class_key_canon_go", classKeyCanonGo),
   ("class_seeds", classSeedsL),
   ("class_key_of_closed", classKeyOfClosed), ("class_key_of", classKeyOfL),
   ("check_block_classes_keys", checkBlockClassesKeys),
   ("check_block_classes_count", checkBlockClassesCount),
   ("check_block_classes_one_per_member", checkBlockClassesOnePerMember),
   ("check_block_classes", checkBlockClassesL), ("class_fe_r", classFeRL), ("class_fe_r_go", classFeRGo),
   ("class_fe_r_rec", classFeRRec),
   ("gen_rec_check_any_no_member", genRecCheckAnyNoMember),
   ("gen_rec_check_former_tys", genRecCheckFormerTys),
   ("gen_rec_check_former_tys_c", genRecCheckFormerTysC),
   ("gen_rec_check_minor_ok", genRecCheckMinorOk), ("gen_rec_check_pop_all", genRecCheckPopAll),
   ("gen_rec_check_prep", genRecCheckPrep), ("gen_rec_check", genRecCheckL)]

/-- Stubs for the functions of OTHER modules this module calls (arity per the naming rule): module
`IndPos`'s `nest_occ`, `inst_pis_with`; `IndParts`'s `pi_binders`, `block_large_elim_allowed`,
`block_shape_member_names`; `RecCheck`'s `target_pi_doms_with`, `target_k53`, `target_major_at`,
`target_ctor_at`, `target_major_of`, `target_major_pins`, `target_major_nfs`,
`target_canon_params`, `target_rec_pins`; `RecClass`'s `class_gen_rec_ty`, `class_gen_rule`,
`class_gen_prefix_binders`, `class_read`, `class_read_classes`; `IndSum`'s `struct_elim_level`,
`param_levels`; `IndPos2`'s `nest_seed_of`. -/
def recGenForeign : Prog :=
  [("nest_occ", stub 5), ("pi_binders", stub 2), ("target_pi_doms_with", stub 3),
   ("target_k53", stub 9), ("target_major_at", stub 3), ("target_ctor_at", stub 2),
   ("inst_pis_with", stub 3), ("target_major_of", stub 9), ("target_major_pins", stub 3),
   ("target_major_nfs", stub 13), ("class_gen_rec_ty", stub 2), ("class_gen_rule", stub 8),
   ("param_levels", stub 2), ("target_canon_params", stub 3), ("nest_seed_of", stub 8),
   ("class_read", stub 5), ("class_read_classes", stub 2), ("target_rec_pins", stub 3),
   ("block_large_elim_allowed", stub 2), ("struct_elim_level", stub 2),
   ("class_gen_prefix_binders", stub 1), ("block_shape_member_names", stub 1)]

/-! ## A pure-enough slice, exercised -/

-- `class_slot_is_minor` on a `.minor` record and on a `.motive` record; `class_fields_of_hits`
-- finds field `0`'s class, field `1`'s class, and misses field `5`; `class_minor_slot` finds the
-- one `.minor c cc` slot and reports its `ihs`.
#guard
  match run (recGenFns ++ libFns ++ stubFns ++ masterFns ++ recGenForeign) 1000 "rec2" [0, 42]
      testMem with
  | .ok ([motive], m1) =>
    (match run (recGenFns ++ libFns ++ stubFns ++ masterFns ++ recGenForeign) 1000
        "class_slot_is_minor" [motive] m1 with
     | .ok ([0], _) => true | _ => false) &&
    (match run (recGenFns ++ libFns ++ stubFns ++ masterFns ++ recGenForeign) 1000 "rec2" [0, 10]
        m1 with
     | .ok ([h0], m2) =>
       match run (recGenFns ++ libFns ++ stubFns ++ masterFns ++ recGenForeign) 1000 "rec2" [1, 20]
           m2 with
       | .ok ([h1], m3) =>
         match run (recGenFns ++ libFns ++ stubFns ++ masterFns ++ recGenForeign) 1000 "sl_new1"
             [h0] m3 with
         | .ok ([o0, 1], m4) =>
           match run (recGenFns ++ libFns ++ stubFns ++ masterFns ++ recGenForeign) 1000 "sl_snoc"
               [o0, 1, h1] m4 with
           | .ok ([ihsOff, 2], m5) =>
             (match run (recGenFns ++ libFns ++ stubFns ++ masterFns ++ recGenForeign) 1000
                 "class_fields_of_hits" [ihsOff, 2, 0] m5 with
              | .ok ([1, 10], _) => true | _ => false) &&
             (match run (recGenFns ++ libFns ++ stubFns ++ masterFns ++ recGenForeign) 1000
                 "class_fields_of_hits" [ihsOff, 2, 1] m5 with
              | .ok ([1, 20], _) => true | _ => false) &&
             (match run (recGenFns ++ libFns ++ stubFns ++ masterFns ++ recGenForeign) 1000
                 "class_fields_of_hits" [ihsOff, 2, 5] m5 with
              | .ok ([0, 0], _) => true | _ => false) &&
             (match run (recGenFns ++ libFns ++ stubFns ++ masterFns ++ recGenForeign) 1000 "rec5"
                 [1, 7, 100, ihsOff, 2] m5 with
              | .ok ([minorSlot], m6) =>
                (match run (recGenFns ++ libFns ++ stubFns ++ masterFns ++ recGenForeign) 1000
                    "class_slot_is_minor" [minorSlot] m6 with
                 | .ok ([1], _) => true | _ => false) &&
                (match run (recGenFns ++ libFns ++ stubFns ++ masterFns ++ recGenForeign) 1000
                    "sl_new1" [minorSlot] m6 with
                 | .ok ([slotsOff, 1], m7) =>
                   match run (recGenFns ++ libFns ++ stubFns ++ masterFns ++ recGenForeign) 1000
                       "rec4" [slotsOff, 1, 0, 0] m7 with
                   | .ok ([rd], m8) =>
                     (match run (recGenFns ++ libFns ++ stubFns ++ masterFns ++ recGenForeign) 1000
                         "class_minor_slot" [rd, 7, 100] m8 with
                      | .ok ([0, ihsOff', 2], _) => ihsOff' == ihsOff | _ => false) &&
                     (match run (recGenFns ++ libFns ++ stubFns ++ masterFns ++ recGenForeign) 1000
                         "class_minor_slot" [rd, 7, 999] m8 with
                      | .ok _ => false | _ => true)
                   | _ => false
                 | _ => false)
              | _ => false)
           | _ => false
         | _ => false
       | _ => false
     | _ => false)
  | _ => false

end L.Ind
