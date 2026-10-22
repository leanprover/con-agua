import ConAgua.Arena.IndIface

/-!
# The generated-recursor stage in L: the pre-pass and the generator (lane `induct`)

The L translation of `vendor/con-ron/ConRon/Arena/Inductives/ClassRead.lean` (the pre-pass that
reads the shared prefix and every recursor's class, syntactically) and the top of
`vendor/con-ron/ConRon/Arena/Inductives/GenRec.lean` through `classGenRule` (the generator: the
recursor family's prefix, each class's recursor type, each constructor's rule). No proofs this
round (IndIface's note); correctness of the translation is what matters.

Layouts (IndIface): `ClassKey`/`NestKey` `[ind, lvls, ds.off, ds.len]`; `ClassSlot` `.motive key`
`[0, key]`, `.minor cls ctor ihs` `[1, cls, ctor, ihs.off, ihs.len]` (`ihs`: pointers to
`[field, cls]`); `ClassRead` `[slots.off, slots.len, recCls.off, recCls.len]`; `BlockShape`
`[members.off, members.len, recs.off, recs.len, nP, elim, resSort, large, isProp]`; `RecShape`
`[cvR, rP, mI, tgt, rhss.off, rhss.len]`; `TargetMajor` `[ind, lvls, ds.off, ds.len, nPc, nIdx,
ctors.off, ctors.len, member, nfs.off, nfs.len, pfvs.off, pfvs.len]`; `ClassField` `[0]` ordinary,
`[1, cls, tele]` recursive; `ClassCtor` `[cv, nF, kinds.off, kinds.len, tyD, tyN]`; `ClassGen`
`[nP, params.off, params.len, cls.off, cls.len, formerTys.off, formerTys.len, slots.off,
slots.len, ctors.off, ctors.len, elim, pre.off, pre.len]`. `classNPcOf` reads the environment's
`indInfo` caps inline at the constant record: kind at `q`, caps at `q + 5`, `nparams` at caps word
12, i.e. `q + 17`.
-/

namespace L.Ind

open L.Arena

/-! ## `ClassRead.lean`: the pre-pass -/

/-- `class_read_classes(so, sl)`: the motives' keys, in prefix order (`slots.filterMap`). -/
-- con-ron: ConRon/Arena/Inductives/ClassRead.lean:66-72 ConRon.Arena.ClassRead.classes
@[l_impl ConRon.Arena.ClassRead.classes]
def classReadClasses : FunDecl := lfn (so, sl) locals (sp, ro, rl, qo, ql) {
  if sl == 0 { return (0, 0) };
  sp := IW.u64[so];
  (ro, rl) := call class_read_classes(so + 1, sl - 1);
  if IW.u64[sp] == 0 {
    (qo, ql) := call sl_cons(IW.u64[sp + 1], ro, rl);
    return (qo, ql)
  };
  return (ro, rl)
}

/-- `class_read_motive_slot(so, sl, c)`: the prefix position of class `c`'s motive. -/
-- con-ron: ConRon/Arena/Inductives/ClassRead.lean:74-82 ConRon.Arena.ClassRead.motiveSlot
@[l_impl ConRon.Arena.ClassRead.motiveSlot]
def classReadMotiveSlot : FunDecl := lfn (so, sl, c) locals (sp, ok, j) {
  if sl == 0 { return (0, 0) };
  sp := IW.u64[so];
  if IW.u64[sp] == 0 {
    if c == 0 { return (1, 0) };
    (ok, j) := call class_read_motive_slot(so + 1, sl - 1, c - 1)
  } else {
    (ok, j) := call class_read_motive_slot(so + 1, sl - 1, c)
  };
  if ok == 0 { return (0, 0) };
  return (1, j + 1)
}

/-- `class_of_motive_var(nP, mo, ml, p)`: the motive ordinal of prefix variable `p`
(`motPos.findIdx? (· == p - nP)`, `sl_find`'s search). -/
-- con-ron: ConRon/Arena/Inductives/ClassRead.lean:84-88 ConRon.Arena.classOfMotiveVar
@[l_impl ConRon.Arena.classOfMotiveVar]
def classOfMotiveVar : FunDecl := lfn (nP, mo, ml, p) locals (r, i) {
  if p < nP { return (0, 0) };
  (r, i) := call sl_find(mo, ml, p - nP);
  return (r, i)
}

/-- `fvar_head(e)`: the `fvar` head of an application, its index (`none` at any other head). -/
-- con-ron: ConRon/Arena/Inductives/ClassRead.lean:90-99 ConRon.Arena.fvarHead
@[l_impl ConRon.Arena.fvarHead]
def fvarHead : FunDecl := lfn (e) locals (hd, g, x, y, z) {
  hd := call get_app_fn(⟪CWF⟫, e);
  if hd >> 28 == 1 {
    (g, x, y, z) := call e_view(hd);
    return (1, x)
  };
  return (0, 0)
}

/-- `class_read_minor_ih1(nP, mo, ml, d, x)`: `classReadMinor`'s `fvs.filterMapM` body for one
opened binder `x`: its walked type's conclusion's motive, as `(ok, field, cls)`. -/
-- con-ron: ConRon/Arena/Inductives/ClassRead.lean:101-145 ConRon.Arena.classReadMinor
@[l_impl ConRon.Arena.classReadMinor]
def classReadMinorIh1 : FunDecl := lfn (nP, mo, ml, d, x) locals (r, ok, v, t) {
  r := call fvar_type_d(x);
  r := call pi_result(⟪CWF⟫, r);
  (ok, v) := call fvar_head(r);
  if ok == 0 { return (0, 0, 0) };
  (ok, t) := call class_of_motive_var(nP, mo, ml, v);
  if ok == 0 { return (0, 0, 0) };
  (r, v) := call get_app_args(⟪CWF⟫, r);
  if v == 0 { return (0, 0, 0) };
  v := IW.u64[r + v - 1];
  (ok, v) := call fvar_head(v);
  if ok == 0 { return (0, 0, 0) };
  if v < d { return (0, 0, 0) };
  return (1, v - d, t)
}

/-- `class_read_minor_ihs(nP, mo, ml, d, fo, fl)`: `classReadMinor`'s inductive-hypothesis list,
`fvs.filterMapM` (a self-recursion: the head's hypothesis, the rest, then the cons). -/
-- con-ron: ConRon/Arena/Inductives/ClassRead.lean:101-145 ConRon.Arena.classReadMinor
@[l_impl ConRon.Arena.classReadMinor]
def classReadMinorIhs : FunDecl := lfn (nP, mo, ml, d, fo, fl) locals (ok, f, t, ro, rl, rp, co, cl) {
  if fl == 0 { return (0, 0) };
  (ok, f, t) := call class_read_minor_ih1(nP, mo, ml, d, IW.u64[fo]);
  (ro, rl) := call class_read_minor_ihs(nP, mo, ml, d, fo + 1, fl - 1);
  if ok == 1 {
    rp := call rec2(f, t);
    (co, cl) := call sl_cons(rp, ro, rl);
    return (co, cl)
  };
  return (ro, rl)
}

/-- `class_read_minor_finish(nP, mo, ml, d, fo, fl, hd, c)`: after the conclusion's head is read,
test its tag and build the `.minor` slot. -/
-- con-ron: ConRon/Arena/Inductives/ClassRead.lean:101-145 ConRon.Arena.classReadMinor
@[l_impl ConRon.Arena.classReadMinor]
def classReadMinorFinish : FunDecl := lfn (nP, mo, ml, d, fo, fl, hd, c) locals
    (g, cn, us, z, ihso, ihsl, slot) {
  if hd >> 28 != 3 { return (0, 0) };
  (g, cn, us, z) := call e_view(hd);
  (ihso, ihsl) := call class_read_minor_ihs(nP, mo, ml, d, fo, fl);
  slot := call rec5(1, c, cn, ihso, ihsl);
  return (1, slot)
}

/-- `class_read_minor_tail(nP, mo, ml, d, fo, fl, concl, c)`: `classReadMinor` after the class is
read off the conclusion: its last argument's head, then `class_read_minor_finish`. -/
-- con-ron: ConRon/Arena/Inductives/ClassRead.lean:101-145 ConRon.Arena.classReadMinor
@[l_impl ConRon.Arena.classReadMinor]
def classReadMinorTail : FunDecl := lfn (nP, mo, ml, d, fo, fl, concl, c) locals
    (cao, cal, last, hd, ok, r) {
  (cao, cal) := call get_app_args(⟪CWF⟫, concl);
  if cal == 0 { return (0, 0) };
  last := IW.u64[cao + cal - 1];
  hd := call get_app_fn(⟪CWF⟫, last);
  (ok, r) := call class_read_minor_finish(nP, mo, ml, d, fo, fl, hd, c);
  return (ok, r)
}

/-- `class_read_minor(nP, mo, ml, d, dom)`: read one minor premise's type, opened at `d`. -/
-- con-ron: ConRon/Arena/Inductives/ClassRead.lean:101-145 ConRon.Arena.classReadMinor
@[l_impl ConRon.Arena.classReadMinor]
def classReadMinor : FunDecl := lfn (nP, mo, ml, d, dom) locals
    (bo, bl, body, ok, fo, fl, concl, p, c, r) {
  (bo, bl, body) := call pi_binders(⟪CWF⟫, dom);
  (ok, fo, fl, concl) := call open_pis_at_fvars_f(bl, dom, d);
  if ok == 0 { return (0, 0) };
  (ok, p) := call fvar_head(concl);
  if ok == 0 { return (0, 0) };
  (ok, c) := call class_of_motive_var(nP, mo, ml, p);
  if ok == 0 { return (0, 0) };
  (ok, r) := call class_read_minor_tail(nP, mo, ml, d, fo, fl, concl, c);
  return (ok, r)
}

/-- `class_n_pc_of(p, vis, i)`: an inductive's declared parameter count, the block's at a member,
the environment's `indInfo` caps otherwise. -/
-- con-ron: ConRon/Arena/Inductives/ClassRead.lean:147-156 ConRon.Arena.classNPcOf
@[l_impl ConRon.Arena.classNPcOf]
def classNPcOf : FunDecl := lfn (p, vis, i) locals (mo, ml, b, found, q, kind) {
  (mo, ml) := call block_shape_member_names(p);
  b := call sl_contains(mo, ml, i);
  if b == 1 { return IW.u64[p + 4] };
  (found, q) := call env_find(i, vis);
  if found == 0 { return 0 };
  kind := EREC.u64[q];
  if kind == 3 { return EREC.u64[q + 17] };
  return 0
}

/-- `class_read_slot_motive(p, vis, dom)`: `classReadSlot`'s motive arm (the telescope ends in a
sort): the class is its last binder's domain, at the class's parameter count. -/
-- con-ron: ConRon/Arena/Inductives/ClassRead.lean:158-179 ConRon.Arena.classReadSlot
@[l_impl ConRon.Arena.classReadSlot]
def classReadSlotMotive : FunDecl := lfn (p, vis, dom) locals
    (bo, bl, body, mdom, hd, g, iName, us, z, ao, al, n, cnt, key, slot) {
  (bo, bl, body) := call pi_binders(⟪CWF⟫, dom);
  if bl == 0 { return (0, 0) };
  mdom := IW.u64[bo + bl - 1];
  hd := call get_app_fn(⟪CWF⟫, mdom);
  if hd >> 28 != 3 { return (0, 0) };
  (g, iName, us, z) := call e_view(hd);
  (ao, al) := call get_app_args(⟪CWF⟫, mdom);
  n := call class_n_pc_of(p, vis, iName);
  cnt := al;
  if n < al { cnt := n };
  key := call rec4(iName, us, ao, cnt);
  slot := call rec2(0, key);
  return (1, slot)
}

/-- `class_read_slot(p, vis, np, mo, ml, d, dom)`: one prefix binder's domain, read as a motive
(a telescope ending in a sort) or a minor premise. -/
-- con-ron: ConRon/Arena/Inductives/ClassRead.lean:158-179 ConRon.Arena.classReadSlot
@[l_impl ConRon.Arena.classReadSlot]
def classReadSlot : FunDecl := lfn (p, vis, np, mo, ml, d, dom) locals (r, ok, slot) {
  r := call pi_result(⟪CWF⟫, dom);
  if r >> 28 == 2 {
    (ok, slot) := call class_read_slot_motive(p, vis, dom);
    return (ok, slot)
  };
  (ok, slot) := call class_read_minor(np, mo, ml, d, dom);
  return (ok, slot)
}

/-- `class_read_slots(p, vis, np, n, mo, ml, d, e)`: read `n` prefix binders of a recursor type
opened at the parameters, classifying each. -/
-- con-ron: ConRon/Arena/Inductives/ClassRead.lean:181-205 ConRon.Arena.classReadSlots
@[l_impl ConRon.Arena.classReadSlots]
def classReadSlots : FunDecl := lfn (p, vis, np, n, mo, ml, d, e) locals
    (ok, dom, body, g, z, slot, co, cl) {
  if n == 0 { return (1, 0, 0) };
  if e >> 28 != 6 { return (0, 0, 0) };
  (g, dom, body, z) := call e_view(e);
  (ok, slot) := call class_read_slot(p, vis, np, mo, ml, d, dom);
  if ok == 0 { return (0, 0, 0) };
  (ok, co, cl) := call class_read_slots_next(p, vis, np, n, mo, ml, d, dom, body, slot);
  return (ok, co, cl)
}

/-- `class_read_slots_snoc(mo, ml, np, d)`: `motPos ++ [d - np]` (the truncated difference). -/
-- con-ron: ConRon/Arena/Inductives/ClassRead.lean:181-205 ConRon.Arena.classReadSlots
@[l_impl ConRon.Arena.classReadSlots]
def classReadSlotsSnoc : FunDecl := lfn (mo, ml, np, d) locals (o, l) {
  if np <= d {
    (o, l) := call sl_snoc(mo, ml, d - np);
    return (o, l)
  };
  (o, l) := call sl_snoc(mo, ml, 0);
  return (o, l)
}

/-- `class_read_slots_next(p, vis, np, n, mo, ml, d, dom, body, slot)`: `classReadSlots` after the
slot is read: the motive positions, the binder opened at `d`, the rest, then the cons. -/
-- con-ron: ConRon/Arena/Inductives/ClassRead.lean:181-205 ConRon.Arena.classReadSlots
@[l_impl ConRon.Arena.classReadSlots]
def classReadSlotsNext : FunDecl := lfn (p, vis, np, n, mo, ml, d, dom, body, slot) locals
    (tag, mo2, ml2, fv, b2, ok, ro, rl, co, cl) {
  tag := IW.u64[slot];
  mo2 := mo;
  ml2 := ml;
  if tag == 0 { (mo2, ml2) := call class_read_slots_snoc(mo, ml, np, d) };
  fv := call intern_fvar(d, dom);
  if 4294967296 <= fv { abort };
  b2 := call instantiate1_fast(⟪CWF⟫, body, fv, 0);
  (ok, ro, rl) := call class_read_slots(p, vis, np, n - 1, mo2, ml2, d + 1, b2);
  if ok == 0 { return (0, 0, 0) };
  (co, cl) := call sl_cons(slot, ro, rl);
  return (1, co, cl)
}

/-- `class_read_rec_cls(nP, mo, ml, ro, rl)`: every recursor's class off its conclusion. -/
-- con-ron: ConRon/Arena/Inductives/ClassRead.lean:207-224 ConRon.Arena.classReadRecCls
@[l_impl ConRon.Arena.classReadRecCls]
def classReadRecCls : FunDecl := lfn (nP, mo, ml, ro, rl) locals
    (rc, mI, ty, ok, p, c, concl, reo, rel, co, cl) {
  if rl == 0 { return (1, 0, 0) };
  rc := IW.u64[ro];
  mI := IW.u64[rc + 2];
  ty := EREC.u64[IW.u64[rc] + 3];
  (ok, p, c, concl) := call open_pis_at_fvars_f(mI + 1, ty, 0);
  if ok == 0 { return (0, 0, 0) };
  (ok, p) := call fvar_head(concl);
  if ok == 0 { return (0, 0, 0) };
  (ok, c) := call class_of_motive_var(nP, mo, ml, p);
  if ok == 0 { return (0, 0, 0) };
  (ok, reo, rel) := call class_read_rec_cls(nP, mo, ml, ro + 1, rl - 1);
  if ok == 0 { return (0, 0, 0) };
  (co, cl) := call sl_cons(c, reo, rel);
  return (1, co, cl)
}

/-- `class_read_mot_pos(so, sl, j)`: the prefix positions `j ‥< sl` whose slot is a motive (the
motive positions `classRead` filters off the slots), a self-recursion. -/
-- con-ron: ConRon/Arena/Inductives/ClassRead.lean:226-247 ConRon.Arena.classRead
@[l_impl ConRon.Arena.classRead]
def classReadMotPos : FunDecl := lfn (so, sl, j) locals (ro, rl, co, cl) {
  if sl <= j { return (0, 0) };
  (ro, rl) := call class_read_mot_pos(so, sl, j + 1);
  if IW.u64[IW.u64[so + j]] == 0 {
    (co, cl) := call sl_cons(j, ro, rl);
    return (co, cl)
  };
  return (ro, rl)
}

/-- `class_read_finish(nP, so, sl, ro, rl)`: the motive positions off the slots just read, then
every recursor's class, then the `ClassRead` record. -/
-- con-ron: ConRon/Arena/Inductives/ClassRead.lean:226-247 ConRon.Arena.classRead
@[l_impl ConRon.Arena.classRead]
def classReadFinish : FunDecl := lfn (nP, so, sl, ro, rl) locals (qo, ql, ok, reco, recl, res) {
  (qo, ql) := call class_read_mot_pos(so, sl, 0);
  (ok, reco, recl) := call class_read_rec_cls(nP, qo, ql, ro, rl);
  if ok == 0 { return (0, 0) };
  res := call rec4(so, sl, reco, recl);
  return (1, res)
}

/-- `class_read_n_slots(rP, nP)`: `rP - nP`, truncated at `0` (the twin's `Nat` subtraction). -/
-- con-ron: ConRon/Arena/Inductives/ClassRead.lean:226-247 ConRon.Arena.classRead
@[l_impl ConRon.Arena.classRead]
def classReadNSlots : FunDecl := lfn (rP, nP) locals () {
  if nP <= rP { return rP - nP };
  return 0
}

/-- `class_read(p, vis, nP, ro, rl)`: the pre-pass, off the first recursor's type. -/
-- con-ron: ConRon/Arena/Inductives/ClassRead.lean:226-247 ConRon.Arena.classRead
@[l_impl ConRon.Arena.classRead]
def classRead : FunDecl := lfn (p, vis, nP, ro, rl) locals
    (rc0, ty, ok, jo, jl, body, k, so, sl, res) {
  if rl == 0 { return (0, 0) };
  rc0 := IW.u64[ro];
  ty := EREC.u64[IW.u64[rc0] + 3];
  (ok, jo, jl, body) := call open_pis_at_fvars_f(nP, ty, 0);
  if ok == 0 { return (0, 0) };
  k := call class_read_n_slots(IW.u64[rc0 + 1], nP);
  (ok, so, sl) := call class_read_slots(p, vis, nP, k, 0, 0, nP, body);
  if ok == 0 { return (0, 0) };
  (ok, res) := call class_read_finish(nP, so, sl, ro, rl);
  return (ok, res)
}

/-! ## `GenRec.lean`, through `classGenRule`: the generator -/

/-- `close_lams(bo, bl, i, body)`: close a telescope of `λ`s opened at `i ‥< i + bl`, innermost
first. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:66-74 ConRon.Arena.closeLams
@[l_impl ConRon.Arena.closeLams]
def closeLams : FunDecl := lfn (bo, bl, i, body) locals (inner, closed, e) {
  if bl == 0 { return body };
  inner := call close_lams(bo + 1, bl - 1, i + 1, body);
  closed := call abstract1_fast(⟪CWF⟫, inner, i, 0);
  e := call mk_lam(IW.u64[bo], closed);
  if 4294967296 <= e { abort };
  return e
}

/-- `expr_get_d(o, l, i)`: `xs.getD i default`, the default the interned `.bvar 0`. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:91-97 ConRon.Arena.exprGetD
@[l_impl ConRon.Arena.exprGetD]
def exprGetD : FunDecl := lfn (o, l, i) locals (x) {
  if i < l { return IW.u64[o + i] };
  x := call intern_bvar(0);
  if 4294967296 <= x { abort };
  return x
}

/-- `class_binder(x)`: the binder of an opened variable, its type. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:99-102 ConRon.Arena.classBinder
@[l_impl ConRon.Arena.classBinder]
def classBinder : FunDecl := lfn (x) locals (t) {
  t := call fvar_type_d(x);
  return t
}

/-- `class_gen_binder(g, x)`: a generated binder of an opened variable. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:104-107 ConRon.Arena.ClassGen.binder
@[l_impl ConRon.Arena.ClassGen.binder]
def classGenBinder : FunDecl := lfn (g, x) locals (t) {
  t := call fvar_type_d(x);
  return t
}

/-- `class_gen_slot_var(g, s)`: the prefix variable of slot `s`. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:109-113 ConRon.Arena.ClassGen.slotVar
@[l_impl ConRon.Arena.ClassGen.slotVar]
def classGenSlotVar : FunDecl := lfn (g, s) locals (u, z, fv) {
  u := call pin_word(53);
  if 4294967296 <= u { abort };
  z := call intern_sort(u);
  if 4294967296 <= z { abort };
  fv := call intern_fvar(IW.u64[g] + s, z);
  if 4294967296 <= fv { abort };
  return fv
}

/-- `class_gen_mot_var(g, c)`: class `c`'s motive variable. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:115-118 ConRon.Arena.ClassGen.motVar
@[l_impl ConRon.Arena.ClassGen.motVar]
def classGenMotVar : FunDecl := lfn (g, c) locals (ok, s, r, so, sl) {
  so := IW.u64[g + 7];
  sl := IW.u64[g + 8];
  (ok, s) := call class_read_motive_slot(so, sl, c);
  if ok == 0 { s := 0 };
  r := call class_gen_slot_var(g, s);
  return r
}

/-- `class_gen_major(g, c, d)`: class `c`'s index telescope opened at `d`, and its major domain. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:120-133 ConRon.Arena.ClassGen.major
@[l_impl ConRon.Arena.ClassGen.major]
def classGenMajor : FunDecl := lfn (g, c, d) locals
    (ci, fty, ok, ty, fo, fl, body, hd, dso, dsl, mt) {
  ci := call target_major_at(IW.u64[g + 3], IW.u64[g + 4], c);
  fty := call expr_get_d(IW.u64[g + 5], IW.u64[g + 6], c);
  (ok, ty) := call inst_pis_with(IW.u64[ci + 2], IW.u64[ci + 3], fty);
  if ok == 0 { return (0, 0, 0, 0) };
  (ok, fo, fl, body) := call open_pis_at_fvars_f(IW.u64[ci + 5], ty, d);
  if ok == 0 { return (0, 0, 0, 0) };
  hd := call intern_const(IW.u64[ci], IW.u64[ci + 1]);
  (dso, dsl) := call sl_append(IW.u64[ci + 2], IW.u64[ci + 3], fo, fl);
  mt := call mk_app_n(hd, dso, dsl);
  return (1, fo, fl, mt)
}

/-- `class_gen_motive_ty(g, c, d)`: class `c`'s motive type at depth `d`. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:135-145 ConRon.Arena.ClassGen.motiveTy
@[l_impl ConRon.Arena.ClassGen.motiveTy]
def classGenMotiveTy : FunDecl := lfn (g, c, d) locals (ok, fo, fl, maj, srt, body2, bo, bl, r) {
  (ok, fo, fl, maj) := call class_gen_major(g, c, d);
  if ok == 0 { return (0, 0) };
  srt := call intern_sort(IW.u64[g + 11]);
  body2 := call mk_forall(maj, srt);
  (bo, bl) := call fvar_type_ds(fo, fl);
  r := call close_telescope(bo, bl, d, body2);
  return (1, r)
}

/-- `class_gen_ih_parts(g, t, tele, w, d)`: the inductive hypothesis of a recursive field whose
walked type is `w`, opened at `d`: its telescope and its index arguments. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:147-159 ConRon.Arena.ClassGen.ihParts
@[l_impl ConRon.Arena.ClassGen.ihParts]
def classGenIhParts : FunDecl := lfn (g, t, tele, w, d) locals
    (ok, xo, xl, leaf, clsLen, ptr, nPc, ao, al, dOff, dLen) {
  clsLen := IW.u64[g + 4];
  nPc := 0;
  if t < clsLen { ptr := IW.u64[IW.u64[g + 3] + t]; nPc := IW.u64[ptr + 4] };
  (ok, xo, xl, leaf) := call open_pis_at_fvars_f(tele, w, d);
  if ok == 0 { return (0, 0, 0, 0, 0) };
  (ao, al) := call get_app_args(⟪CWF⟫, leaf);
  dOff := ao;
  dLen := al;
  if nPc < al { dOff := ao + nPc; dLen := al - nPc } else { dLen := 0 };
  return (1, xo, xl, dOff, dLen)
}

/-- `class_gen_minor_ty_ih1(g, t, tele, wso, wsl, fvso, fvsl, i, e)`: `minorTy`'s `ihsGo` body for
one recursive field `i` landing at class `t`, its inductive hypothesis at depth `e`. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:161-208 ConRon.Arena.ClassGen.minorTy
@[l_impl ConRon.Arena.ClassGen.minorTy]
def classGenMinorTyIh1 : FunDecl := lfn (g, t, tele, wso, wsl, fvso, fvsl, i, e) locals
    (w, ok, xso, xsl, idxo, idxl, f, fx, mt, appo, appl, body, bso, bsl, ih) {
  w := call expr_get_d(wso, wsl, i);
  (ok, xso, xsl, idxo, idxl) := call class_gen_ih_parts(g, t, tele, w, e);
  if ok == 0 { return (0, 0) };
  f := call expr_get_d(fvso, fvsl, i);
  fx := call mk_app_n(f, xso, xsl);
  mt := call class_gen_mot_var(g, t);
  (appo, appl) := call sl_snoc(idxo, idxl, fx);
  body := call mk_app_n(mt, appo, appl);
  (bso, bsl) := call fvar_type_ds(xso, xsl);
  ih := call close_telescope(bso, bsl, e, body);
  return (1, ih)
}

/-- `class_gen_minor_ty_ihs_go(g, x, d, nF, wso, wsl, fvso, fvsl, i, l)`: `ClassGen.minorTy`'s
`ihsGo`, over constructor `x`'s fields `i ‥< nF`, `l` the count of recursive fields seen. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:161-208 ConRon.Arena.ClassGen.minorTy
@[l_impl ConRon.Arena.ClassGen.minorTy]
def classGenMinorTyIhsGo : FunDecl := lfn (g, x, d, nF, wso, wsl, fvso, fvsl, i, l) locals
    (kp, tag, t, tele, ok, ih, resto, restl, cono, conl) {
  if nF <= i { return (1, 0, 0) };
  tag := 0;
  if i < IW.u64[x + 3] { kp := IW.u64[IW.u64[x + 2] + i]; tag := IW.u64[kp] };
  if tag == 1 {
    t := IW.u64[kp + 1];
    tele := IW.u64[kp + 2];
    (ok, ih) := call class_gen_minor_ty_ih1(g, t, tele, wso, wsl, fvso, fvsl, i, d + nF + l);
    if ok == 0 { return (0, 0, 0) };
    (ok, resto, restl) := call class_gen_minor_ty_ihs_go(g, x, d, nF, wso, wsl, fvso, fvsl,
      i + 1, l + 1);
    if ok == 0 { return (0, 0, 0) };
    (cono, conl) := call sl_cons(ih, resto, restl);
    return (1, cono, conl)
  };
  (ok, resto, restl) := call class_gen_minor_ty_ihs_go(g, x, d, nF, wso, wsl, fvso, fvsl, i + 1, l);
  return (ok, resto, restl)
}

/-- `class_gen_minor_ty(g, c, x, d)`: constructor `x`'s minor premise type at depth `d`, of
class `c`. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:161-208 ConRon.Arena.ClassGen.minorTy
@[l_impl ConRon.Arena.ClassGen.minorTy]
def classGenMinorTy : FunDecl := lfn (g, c, x, d) locals
    (ci, ok, fo, fl, res, wso, wsl, ihso, ihsl, rao, ral, cc, capo, capl, mc, dOff, dLen,
     bo, bl, fbso, fbsl, allo, alll, r) {
  ci := call target_major_at(IW.u64[g + 3], IW.u64[g + 4], c);
  (ok, fo, fl, res) := call open_pis_at_fvars_f(IW.u64[x + 1], IW.u64[x + 4], d);
  if ok == 0 { return (0, 0) };
  (ok, wso, wsl) := call target_pi_doms_with(fo, fl, IW.u64[x + 5]);
  if ok == 0 { return (0, 0) };
  (ok, ihso, ihsl) := call class_gen_minor_ty_ihs_go(g, x, d, IW.u64[x + 1], wso, wsl, fo, fl, 0, 0);
  if ok == 0 { return (0, 0) };
  (rao, ral) := call get_app_args(⟪CWF⟫, res);
  cc := call intern_const(EREC.u64[IW.u64[x]], IW.u64[ci + 1]);
  (capo, capl) := call sl_append(IW.u64[ci + 2], IW.u64[ci + 3], fo, fl);
  cc := call mk_app_n(cc, capo, capl);
  mc := call class_gen_mot_var(g, c);
  dOff := rao;
  dLen := ral;
  if IW.u64[ci + 4] < ral { dOff := rao + IW.u64[ci + 4]; dLen := ral - IW.u64[ci + 4] }
  else { dLen := 0 };
  (bo, bl) := call sl_snoc(dOff, dLen, cc);
  res := call mk_app_n(mc, bo, bl);
  (fbso, fbsl) := call fvar_type_ds(fo, fl);
  (allo, alll) := call sl_append(fbso, fbsl, ihso, ihsl);
  r := call close_telescope(allo, alll, d, res);
  return (1, r)
}

/-- `class_gen_prefix_binders_find_ctor(g, c, cName)`: the constructor of class `c` named
`cName`, in `g.ctors[c]`. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:210-239 ConRon.Arena.ClassGen.prefixBinders
@[l_impl ConRon.Arena.ClassGen.prefixBinders]
def classGenPrefixBindersFindCtor : FunDecl := lfn (g, c, cName) locals (ctorsLen, lp, io, il, j, cp) {
  ctorsLen := IW.u64[g + 10];
  if ctorsLen <= c { return (0, 0) };
  lp := IW.u64[IW.u64[g + 9] + c];
  io := IW.u64[lp];
  il := IW.u64[lp + 1];
  j := 0;
  while j < il {
    cp := IW.u64[io + j];
    if EREC.u64[IW.u64[cp]] == cName { return (1, cp) };
    j += 1
  };
  return (0, 0)
}

/-- `class_gen_prefix_binders_slots_go(g, s, mc)`: `ClassGen.prefixBinders`'s `slotsGo`, `mc` the
count of motives before slot `s`. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:210-239 ConRon.Arena.ClassGen.prefixBinders
@[l_impl ConRon.Arena.ClassGen.prefixBinders]
def classGenPrefixBindersSlotsGo : FunDecl := lfn (g, s, mc) locals
    (so, sl, sp, tag, d, ok, ty, cls2, ctor2, ok2, x, restok, resto, restl, co, cl) {
  so := IW.u64[g + 7];
  sl := IW.u64[g + 8];
  if sl <= s { return (1, 0, 0) };
  sp := IW.u64[so + s];
  tag := IW.u64[sp];
  d := IW.u64[g] + s;
  if tag == 0 {
    (ok, ty) := call class_gen_motive_ty(g, mc, d);
    if ok == 0 { return (0, 0, 0) };
    (restok, resto, restl) := call class_gen_prefix_binders_slots_go(g, s + 1, mc + 1);
    if restok == 0 { return (0, 0, 0) };
    (co, cl) := call sl_cons(ty, resto, restl);
    return (1, co, cl)
  };
  cls2 := IW.u64[sp + 1];
  ctor2 := IW.u64[sp + 2];
  (ok2, x) := call class_gen_prefix_binders_find_ctor(g, cls2, ctor2);
  if ok2 == 0 { return (0, 0, 0) };
  (ok, ty) := call class_gen_minor_ty(g, cls2, x, d);
  if ok == 0 { return (0, 0, 0) };
  (restok, resto, restl) := call class_gen_prefix_binders_slots_go(g, s + 1, mc);
  if restok == 0 { return (0, 0, 0) };
  (co, cl) := call sl_cons(ty, resto, restl);
  return (1, co, cl)
}

/-- `class_gen_prefix_binders(g)`: the generated prefix binders: the parameters, then every
slot in the stream's order. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:210-239 ConRon.Arena.ClassGen.prefixBinders
@[l_impl ConRon.Arena.ClassGen.prefixBinders]
def classGenPrefixBinders : FunDecl := lfn (g) locals (pbo, pbl, ok, so, sl, allo, alll) {
  (pbo, pbl) := call fvar_type_ds(IW.u64[g + 1], IW.u64[g + 2]);
  (ok, so, sl) := call class_gen_prefix_binders_slots_go(g, 0, 0);
  if ok == 0 { return (0, 0, 0) };
  (allo, alll) := call sl_append(pbo, pbl, so, sl);
  return (1, allo, alll)
}

/-- `class_gen_rec_ty(g, c)`: the generated recursor type at class `c`. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:241-255 ConRon.Arena.classGenRecTy
@[l_impl ConRon.Arena.classGenRecTy]
def classGenRecTy : FunDecl := lfn (g, c) locals
    (rP, ok, fo, fl, maj, t, ibo, ibl, b1o, b1l, b2o, b2l, mv, a1o, a1l, body, r) {
  rP := IW.u64[g + 13];
  (ok, fo, fl, maj) := call class_gen_major(g, c, rP);
  if ok == 0 { return (0, 0) };
  t := call intern_fvar(rP + fl, maj);
  (ibo, ibl) := call fvar_type_ds(fo, fl);
  (b1o, b1l) := call sl_append(IW.u64[g + 12], rP, ibo, ibl);
  (b2o, b2l) := call sl_snoc(b1o, b1l, maj);
  mv := call class_gen_mot_var(g, c);
  (a1o, a1l) := call sl_snoc(fo, fl, t);
  body := call mk_app_n(mv, a1o, a1l);
  r := call close_telescope(b2o, b2l, 0, body);
  return (1, r)
}

/-- `class_rec_of(rco, rcl, cgo, cgl, t)`: the recursor a call at class `t` names: the family's
first recursor at that class. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:257-263 ConRon.Arena.classRecOf
@[l_impl ConRon.Arena.classRecOf]
def classRecOf : FunDecl := lfn (rco, rcl, cgo, cgl, t) locals (v, nr, ok, nm) {
  if cgl == 0 { return (0, 0) };
  v := 0;
  nr := 0;
  if rcl != 0 { v := IW.u64[rco]; nr := rcl - 1 };
  if v == t { return (1, EREC.u64[IW.u64[cgo]]) };
  (ok, nm) := call class_rec_of(rco + 1, nr, cgo + 1, cgl - 1, t);
  return (ok, nm)
}

/-- `class_gen_rule_find_slot(g, c, ctorName)`: `classGenRule`'s `hit`, the prefix position of
the minor premise of constructor `ctorName` at class `c`. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:265-318 ConRon.Arena.classGenRule
@[l_impl ConRon.Arena.classGenRule]
def classGenRuleFindSlot : FunDecl := lfn (g, c, ctorName) locals (so, sl, j, sp, tag) {
  so := IW.u64[g + 7];
  sl := IW.u64[g + 8];
  j := 0;
  while j < sl {
    sp := IW.u64[so + j];
    tag := IW.u64[sp];
    if tag == 1 && IW.u64[sp + 1] == c && IW.u64[sp + 2] == ctorName { return (1, j) };
    j += 1
  };
  return (0, 0)
}

/-- `class_gen_rule_pvars_go(g, rP, i)`: `classGenRule`'s `pvars`, the prefix variables
`i ‥< rP`. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:265-318 ConRon.Arena.classGenRule
@[l_impl ConRon.Arena.classGenRule]
def classGenRulePvarsGo : FunDecl := lfn (g, rP, i) locals (v, resto, restl, co, cl) {
  if rP <= i { return (0, 0) };
  if i < IW.u64[g + 0] { v := call expr_get_d(IW.u64[g + 1], IW.u64[g + 2], i) }
  else { v := call class_gen_slot_var(g, i - IW.u64[g + 0]) };
  (resto, restl) := call class_gen_rule_pvars_go(g, rP, i + 1);
  (co, cl) := call sl_cons(v, resto, restl);
  return (co, cl)
}

/-- `class_gen_rule_call1(g, t, tele, wso, wsl, fvso, fvsl, pvo, pvl, rlvls, rco, rcl, cgo, cgl,
i, e)`: `classGenRule`'s `callsGo` body for one recursive field `i` landing at class `t`. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:265-318 ConRon.Arena.classGenRule
@[l_impl ConRon.Arena.classGenRule]
def classGenRuleCall1 : FunDecl := lfn
    (g, t, tele, wso, wsl, fvso, fvsl, pvo, pvl, rlvls, rco, rcl, cgo, cgl, i, e) locals
    (w, ok, xso, xsl, idxo, idxl, rc, f, fx, a1o, a1l, a2o, a2l, bso, bsl, rv) {
  w := call expr_get_d(wso, wsl, i);
  (ok, xso, xsl, idxo, idxl) := call class_gen_ih_parts(g, t, tele, w, e);
  if ok == 0 { return (0, 0) };
  (ok, rc) := call class_rec_of(rco, rcl, cgo, cgl, t);
  if ok == 0 { return (0, 0) };
  f := call expr_get_d(fvso, fvsl, i);
  fx := call mk_app_n(f, xso, xsl);
  rc := call intern_const(rc, rlvls);
  (a1o, a1l) := call sl_append(pvo, pvl, idxo, idxl);
  (a2o, a2l) := call sl_snoc(a1o, a1l, fx);
  rv := call mk_app_n(rc, a2o, a2l);
  (bso, bsl) := call fvar_type_ds(xso, xsl);
  rv := call close_lams(bso, bsl, e, rv);
  return (1, rv)
}

/-- `class_gen_rule_calls_go(g, x, wso, wsl, fvso, fvsl, pvo, pvl, rlvls, rco, rcl, cgo, cgl, e,
n, i)`: `classGenRule`'s `callsGo`, over constructor `x`'s fields `i ‥< i + n`. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:265-318 ConRon.Arena.classGenRule
@[l_impl ConRon.Arena.classGenRule]
def classGenRuleCallsGo : FunDecl := lfn
    (g, x, wso, wsl, fvso, fvsl, pvo, pvl, rlvls, rco, rcl, cgo, cgl, e, n, i) locals
    (kp, tag, t, tele, ok, rv, resto, restl, co, cl) {
  if n == 0 { return (1, 0, 0) };
  tag := 0;
  if i < IW.u64[x + 3] { kp := IW.u64[IW.u64[x + 2] + i]; tag := IW.u64[kp] };
  if tag == 1 {
    t := IW.u64[kp + 1];
    tele := IW.u64[kp + 2];
    (ok, rv) := call class_gen_rule_call1(g, t, tele, wso, wsl, fvso, fvsl, pvo, pvl, rlvls,
      rco, rcl, cgo, cgl, i, e);
    if ok == 0 { return (0, 0, 0) };
    (ok, resto, restl) := call class_gen_rule_calls_go(g, x, wso, wsl, fvso, fvsl, pvo, pvl,
      rlvls, rco, rcl, cgo, cgl, e, n - 1, i + 1);
    if ok == 0 { return (0, 0, 0) };
    (co, cl) := call sl_cons(rv, resto, restl);
    return (1, co, cl)
  };
  (ok, resto, restl) := call class_gen_rule_calls_go(g, x, wso, wsl, fvso, fvsl, pvo, pvl, rlvls,
    rco, rcl, cgo, cgl, e, n - 1, i + 1);
  return (ok, resto, restl)
}

/-- `class_gen_rule(g, rco, rcl, cgo, cgl, rlvls, c, x)`: the generated rule of a recursor at
class `c` for its constructor `x`. -/
-- con-ron: ConRon/Arena/Inductives/GenRec.lean:265-318 ConRon.Arena.classGenRule
@[l_impl ConRon.Arena.classGenRule]
def classGenRule : FunDecl := lfn (g, rco, rcl, cgo, cgl, rlvls, c, x) locals
    (rP, ok, s, fo, fl, jnk, wso, wsl, pvo, pvl, nF, e, ihso, ihsl, sv, a1o, a1l, body,
     fbso, fbsl, prefo, prefl, allo, alll, r) {
  rP := IW.u64[g + 13];
  (ok, s) := call class_gen_rule_find_slot(g, c, EREC.u64[IW.u64[x]]);
  if ok == 0 { return (0, 0) };
  (ok, fo, fl, jnk) := call open_pis_at_fvars_f(IW.u64[x + 1], IW.u64[x + 4], rP);
  if ok == 0 { return (0, 0) };
  (ok, wso, wsl) := call target_pi_doms_with(fo, fl, IW.u64[x + 5]);
  if ok == 0 { return (0, 0) };
  (pvo, pvl) := call class_gen_rule_pvars_go(g, rP, 0);
  nF := IW.u64[x + 1];
  e := rP + nF;
  (ok, ihso, ihsl) := call class_gen_rule_calls_go(g, x, wso, wsl, fo, fl, pvo, pvl, rlvls,
    rco, rcl, cgo, cgl, e, nF, 0);
  if ok == 0 { return (0, 0) };
  sv := call class_gen_slot_var(g, s);
  (a1o, a1l) := call sl_append(fo, fl, ihso, ihsl);
  body := call mk_app_n(sv, a1o, a1l);
  (fbso, fbsl) := call fvar_type_ds(fo, fl);
  prefo := IW.u64[g + 12];
  prefl := IW.u64[g + 13];
  (allo, alll) := call sl_append(prefo, prefl, fbso, fbsl);
  r := call close_lams(allo, alll, 0, body);
  return (1, r)
}

/-! ## The program and its closure -/

/-- The functions of this module. -/
def recClassFns : Prog :=
  [("class_read_classes", classReadClasses), ("class_read_motive_slot", classReadMotiveSlot),
   ("class_of_motive_var", classOfMotiveVar), ("fvar_head", fvarHead),
   ("class_read_minor_ih1", classReadMinorIh1), ("class_read_minor_ihs", classReadMinorIhs),
   ("class_read_minor_finish", classReadMinorFinish), ("class_read_minor_tail", classReadMinorTail),
   ("class_read_minor", classReadMinor),
   ("class_n_pc_of", classNPcOf), ("class_read_slot_motive", classReadSlotMotive),
   ("class_read_slot", classReadSlot),
   ("class_read_slots", classReadSlots), ("class_read_slots_next", classReadSlotsNext),
   ("class_read_slots_snoc", classReadSlotsSnoc), ("class_read_rec_cls", classReadRecCls),
   ("class_read_mot_pos", classReadMotPos), ("class_read_finish", classReadFinish),
   ("class_read_n_slots", classReadNSlots), ("class_read", classRead),
   ("close_lams", closeLams), ("expr_get_d", exprGetD), ("class_binder", classBinder),
   ("class_gen_binder", classGenBinder), ("class_gen_slot_var", classGenSlotVar),
   ("class_gen_mot_var", classGenMotVar), ("class_gen_major", classGenMajor),
   ("class_gen_motive_ty", classGenMotiveTy), ("class_gen_ih_parts", classGenIhParts),
   ("class_gen_minor_ty_ih1", classGenMinorTyIh1),
   ("class_gen_minor_ty_ihs_go", classGenMinorTyIhsGo), ("class_gen_minor_ty", classGenMinorTy),
   ("class_gen_prefix_binders_find_ctor", classGenPrefixBindersFindCtor),
   ("class_gen_prefix_binders_slots_go", classGenPrefixBindersSlotsGo),
   ("class_gen_prefix_binders", classGenPrefixBinders), ("class_gen_rec_ty", classGenRecTy),
   ("class_rec_of", classRecOf), ("class_gen_rule_find_slot", classGenRuleFindSlot),
   ("class_gen_rule_pvars_go", classGenRulePvarsGo), ("class_gen_rule_call1", classGenRuleCall1),
   ("class_gen_rule_calls_go", classGenRuleCallsGo), ("class_gen_rule", classGenRule)]

/-- Stubs for the functions of OTHER modules this module calls: `pi_binders` and
`block_shape_member_names` (`IndParts`), `target_major_at` and `target_pi_doms_with`
(`RecCheck`), `inst_pis_with` and `close_telescope` (`IndPos`). -/
def RecClassForeign : Prog :=
  [("pi_binders", stub 2), ("block_shape_member_names", stub 1), ("target_major_at", stub 3),
   ("inst_pis_with", stub 3), ("close_telescope", stub 4), ("target_pi_doms_with", stub 3)]

theorem recClass_wf :
    L.Compiler.Prog.wf indTab
      (recClassFns ++ libFns ++ stubFns ++ masterFns ++ RecClassForeign) = true :=
  L.Compiler.Prog.wf_of_wfFast (by decide +kernel)

-- A small slots list (one motive slot whose class key is `[10, 20, 0, 0]`, one minor slot
-- `(cls 5, ctor 7)`) at `IW[16‥18)`, and a motive-position list `[3]` at `IW[20]`:
-- `class_read_classes` finds the one motive's key, `class_read_motive_slot` its position, and
-- `class_of_motive_var` resolves prefix variable `5` (at `nP = 2`) to it but not variable `4`.
#guard
  let iw : Array Word :=
    #[0, 4, 0, 0, 10, 20, 0, 0, 1, 5, 7, 0, 0, 0, 0, 0, 0, 8, 0, 0, 3, 0, 0, 0, 0]
  let m : Mem := { words := (Array.replicate 224 (#[] : Array Word)) |>.set! CTL ((Array.replicate 256 0).set! 200 21) |>.set! IW iw |>.set! EREC (Array.replicate 8 0) }
  let prog := recClassFns ++ libFns ++ stubFns ++ masterFns ++ RecClassForeign
  match run prog 1000 "class_read_classes" [16, 2] m with
  | .ok ([q, 1], m1) =>
    rdW (m1.arr64 IW) q == 4 &&
    (match run prog 1000 "class_read_motive_slot" [16, 2, 0] m1 with
     | .ok ([1, 0], _) => true | _ => false) &&
    (match run prog 1000 "class_of_motive_var" [2, 20, 1, 5] m1 with
     | .ok ([1, 0], _) => true | _ => false) &&
    (match run prog 1000 "class_of_motive_var" [2, 20, 1, 4] m1 with
     | .ok ([0, 0], _) => true | _ => false)
  | _ => false

end L.Ind
