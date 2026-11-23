module

public import ConAgua.Arena.IotaReadDec
meta import ConAgua.Arena.IndIface

@[expose] public section

/-!
# The ι reading rule in L, part 1: the recursor's frame and the two readings (lane ronsync8)

The L translation of the first two sections of `vendor/con-ron/ConRon/Arena/Inductives/IotaRead.lean`
(con-leche #622, con-ron #164 lane I): a recursor's own type read once (`iota_rec_of`: the rule
prefix, the minor premises of the motive the body applies, the major's levels and parameters),
a rule's parts read off it (`iota_parts_of_at`) and read through the constructor
(`iota_parts_at`). The records and their words are `IotaReadDec.lean`'s (`IotaRec`,
`IIotaParts`: seven words each, the lists `IW` slices).

**Fuel.** The twin's `piTele coreWalkFuel` is a loop counting the binders; past `CWF` binders it
aborts, where the twin's fuel runs out (`.internal`). The callees take `CWF` explicitly
(`get_app_fn_f`, `get_app_args_f`, `pi_result_f`, `lift_entry`, `instantiate_lift_fast`,
`inst_lp_fast`).

**Lists.** The twin's list recursions (`minorsFrom`, `liftFieldDoms`, `liftIdxArgs`,
`iotaBVars`) are loops filling a fresh `IW` slice allocated up front (its length the input's,
or `preL - q` for `minorsFrom`'s positions, of which the answer is a prefix), so that the
callees' own allocations do not interleave with the answer's words.
-/

namespace L.Ind

open L.Arena

/-! ## The recursor's own type (`IotaEq.lean`) -/

/-- `pi_tele(e)`: a `∀`-telescope's binder count and its body, `(n, body)`; aborts at `CWF`
binders (the twin's fuel). -/
-- con-ron: ConRon/Arena/Inductives/IotaRead.lean:55-66 ConRon.Arena.piTele
@[no_expose, l_impl ConRon.Arena.piTele]
def piTeleL : FunDecl := lfn (e) locals (n, h, g, x, y, z) {
  n := 0;
  h := e;
  while ⟦h⟧.tag == 6 {
    if ⟪CWF⟫ <= n { abort };
    (g, x, y, z) := call e_view(h);
    h := y;
    n := n + 1
  };
  if ⟪CWF⟫ <= n { abort };
  return (n, h)
}

/-- `motive_level(preO, preL, nIdx, body)`: the sort level of the motive the body applies,
`(1, u)`, or `(0, 0)`: the body's head a prefix variable (below the `nIdx` indices and the major)
whose domain ends in `Sort u`. -/
-- con-ron: ConRon/Arena/Inductives/IotaRead.lean:68-89 ConRon.Arena.motiveLevel?
@[no_expose, l_impl ConRon.Arena.motiveLevel?]
def motiveLevelL : FunDecl := lfn (preO, preL, nIdx, body) locals (hd, g, k, y, z, d, r, u) {
  hd := call get_app_fn_f(⟪CWF⟫, body);
  if ⟦hd⟧.tag != 0 { return (0, 0) };
  (g, k, y, z) := call e_view(hd);
  if k < nIdx + 1 { return (0, 0) };
  if nIdx + 1 + preL <= k { return (0, 0) };
  d := call expr_get_d(preO, preL, preL - 1 - (k - (nIdx + 1)));
  r := call pi_result_f(⟪CWF⟫, d);
  if ⟦r⟧.tag != 2 { return (0, 0) };
  (g, u, y, z) := call e_view(r);
  return (1, u)
}

/-- `iota_frame(q, mI, rP)`: a recursor's frame, `(ok, pre.off, pre.len, doms.off, doms.len, body,
u)` (`q` the recursor's constant value): its first `rP` binders, the `mI - rP` index binders and
the major's domains, the body after them, the sort level of the motive the body applies. -/
-- con-ron: ConRon/Arena/Inductives/IotaRead.lean:91-105 ConRon.Arena.iotaFrame
@[no_expose, l_impl ConRon.Arena.iotaFrame]
def iotaFrameL : FunDecl := lfn (q, mI, rP) locals (nI, ok, po, pl, rest, dO, dL, body, u) {
  (ok, po, pl, rest) := call strip_pis(rP, EREC⦃q + ⟪CV.type⟫⦄);
  if ok == 0 { return (0, 0, 0, 0, 0, 0, 0) };
  nI := mI - rP;
  if mI < rP { nI := 0 };
  (ok, dO, dL, body) := call strip_pis(nI + 1, rest);
  if ok == 0 { return (0, 0, 0, 0, 0, 0, 0) };
  (ok, u) := call motive_level(po, pl, nI, body);
  if ok == 0 { return (0, 0, 0, 0, 0, 0, 0) };
  return (1, po, pl, dO, dL, body, u)
}

/-- `is_minor_at(preO, preL, mot, q)`: whether the prefix binder at `q` is a minor premise of the
motive at position `mot`: its conclusion headed by that motive's variable. -/
-- con-ron: ConRon/Arena/Inductives/IotaRead.lean:107-118 ConRon.Arena.isMinorAt
@[no_expose, l_impl ConRon.Arena.isMinorAt]
def isMinorAtL : FunDecl := lfn (preO, preL, mot, q) locals (d, tn, tb, hd, g, k, y, z) {
  d := call expr_get_d(preO, preL, q);
  (tn, tb) := call pi_tele(d);
  hd := call get_app_fn_f(⟪CWF⟫, tb);
  if ⟦hd⟧.tag != 0 { return 0 };
  (g, k, y, z) := call e_view(hd);
  if mot < q { return u64(k == tn + (q - 1 - mot)) };
  return 0
}

/-- `minors_from(preO, preL, mot, q)`: the positions from `q` on whose binders `is_minor_at`
accepts, in order, as a fresh `IW` slice `(off, len)` (the room for `preL - q` positions
allocated first). -/
-- con-ron: ConRon/Arena/Inductives/IotaRead.lean:120-129 ConRon.Arena.minorsFrom
@[no_expose, l_impl ConRon.Arena.minorsFrom]
def minorsFromL : FunDecl := lfn (preO, preL, mot, q) locals (o, c, j, b) {
  if preL <= q { return (0, 0) };
  o := call iw_alloc(preL - q);
  c := 0;
  j := q;
  while j < preL {
    b := call is_minor_at(preO, preL, mot, j);
    if b != 0 {
      IW.u64[o + c] := j;
      c := c + 1
    };
    j := j + 1
  };
  return (o, c)
}

/-- `iota_read_major(preO, preL, domO, domL, nIdx, rP, k)`: `iota_rec_of` past the motive's head
`k`: the minor premises, then the major's type at a constant head (its levels, its leading
arguments with the index variables dropped), `(ok, IotaRec)`. -/
-- con-ron: ConRon/Arena/Inductives/IotaRead.lean:144-160 ConRon.Arena.iotaRecMajor
@[no_expose, l_impl ConRon.Arena.iotaRecMajor]
def iotaReadMajorL : FunDecl := lfn (preO, preL, domO, domL, nIdx, rP, k) locals
    (mot, mo, ml, dom, dh, g, n, us, z, ao, al, t, po, pl) {
  mot := rP + nIdx - k;
  if rP + nIdx < k { mot := 0 };
  (mo, ml) := call minors_from(preO, preL, mot, 0);
  dom := call expr_get_d(domO, domL, nIdx);
  dh := call get_app_fn_f(⟪CWF⟫, dom);
  if ⟦dh⟧.tag != 3 { return (0, 0, 0, 0, 0, 0, 0, 0) };
  (g, n, us, z) := call e_view(dh);
  (ao, al) := call get_app_args_f(⟪CWF⟫, dom);
  t := al - nIdx;
  if al < nIdx { t := 0 };
  (po, pl) := call expr_drop_vars_list(nIdx, ao, t);
  return (1, preO, preL, mo, ml, us, po, pl)
}

/-- `iota_rec_of(q, mI, rP)`: what every rule of the recursor (constant value `q`) reads off its
type, `(ok, IotaRec)`: the frame, the motive the body applies (a variable), `iota_read_major`. -/
-- con-ron: ConRon/Arena/Inductives/IotaRead.lean:162-176 ConRon.Arena.iotaRecOf
@[no_expose, l_impl ConRon.Arena.iotaRecOf]
def iotaRecOfL : FunDecl := lfn (q, mI, rP) locals
    (nI, ok, po, pl, dO, dL, body, u, hd, g, k, y, z, r1, r2, r3, r4, r5, r6, r7) {
  nI := mI - rP;
  if mI < rP { nI := 0 };
  (ok, po, pl, dO, dL, body, u) := call iota_frame(q, mI, rP);
  if ok == 0 { return (0, 0, 0, 0, 0, 0, 0, 0) };
  hd := call get_app_fn_f(⟪CWF⟫, body);
  if ⟦hd⟧.tag != 0 { return (0, 0, 0, 0, 0, 0, 0, 0) };
  (g, k, y, z) := call e_view(hd);
  (ok, r1, r2, r3, r4, r5, r6, r7) := call iota_read_major(po, pl, dO, dL, nI, rP, k);
  return (ok, r1, r2, r3, r4, r5, r6, r7)
}

/-- `lift_field_doms(amt, fo, fl)`: field `j`'s domain lifted by `amt` above its own `j` binders,
for each `j`, as a fresh `IW` slice. -/
-- con-ron: ConRon/Arena/Inductives/IotaRead.lean:188-196 ConRon.Arena.liftFieldDoms
@[no_expose, l_impl ConRon.Arena.liftFieldDoms]
def liftFieldDomsL : FunDecl := lfn (amt, fo, fl) locals (o, j, d) {
  if fl == 0 { return (0, 0) };
  o := call iw_alloc(fl);
  j := 0;
  while j < fl {
    d := call lift_entry(IW.u64[fo + j], amt, j, ⟪CWF⟫);
    IW.u64[o + j] := d;
    j := j + 1
  };
  return (o, fl)
}

/-- `lift_idx_args(amt, nT, nF, ao, al)`: each argument with the `nT` binders behind it dropped,
then lifted by `amt` above the `nF` fields, as a fresh `IW` slice. -/
-- con-ron: ConRon/Arena/Inductives/IotaRead.lean:198-209 ConRon.Arena.liftIdxArgs
@[no_expose, l_impl ConRon.Arena.liftIdxArgs]
def liftIdxArgsL : FunDecl := lfn (amt, nT, nF, ao, al) locals (o, j, b, c) {
  if al == 0 { return (0, 0) };
  o := call iw_alloc(al);
  j := 0;
  while j < al {
    b := call expr_drop_vars(nT, IW.u64[ao + j]);
    c := call lift_entry(b, amt, nF, ⟪CWF⟫);
    IW.u64[o + j] := c;
    j := j + 1
  };
  return (o, al)
}

/-- `iota_parts_of_at(IotaRec, rP, nIdx, i, r)`: a rule's parts read off the recursor's own type
at its frame: the `i`-th minor premise, its first `nfields` binders the fields (lifted past the
later prefix), its conclusion's first `nIdx` arguments the indices; `(ok, IIotaParts)` (`r` the
rule's record). -/
-- con-ron: ConRon/Arena/Inductives/IotaRead.lean:211-230 ConRon.Arena.iotaPartsOfAt
@[no_expose, l_impl ConRon.Arena.iotaPartsOfAt]
def iotaPartsOfAtL : FunDecl := lfn (preO, preL, minO, minL, us, parO, parL, rP, nIdx, i, r) locals
    (qq, d, ok, fdo, fdl, inner, amt, fo, fl, tn, tb, ao, al, io, il) {
  if minL <= i { return (0, 0, 0, 0, 0, 0, 0, 0) };
  qq := IW.u64[minO + i];
  d := call expr_get_d(preO, preL, qq);
  (ok, fdo, fdl, inner) := call strip_pis(EREC⦃r + ⟪Rule.nfields⟫⦄, d);
  if ok == 0 { return (0, 0, 0, 0, 0, 0, 0, 0) };
  amt := rP - qq;
  if rP < qq { amt := 0 };
  (fo, fl) := call lift_field_doms(amt, fdo, fdl);
  (tn, tb) := call pi_tele(inner);
  (ao, al) := call get_app_args_f(⟪CWF⟫, tb);
  if nIdx < al { al := nIdx };
  (io, il) := call lift_idx_args(amt, tn, EREC⦃r + ⟪Rule.nfields⟫⦄, ao, al);
  return (1, fo, fl, io, il, us, parO, parL)
}

/-! ## The proofs' reading: through the constructor (`IotaRead.lean`) -/

/-- `ctor_levels_at(r, lpsO, lpsL)`: the levels the rule `r`'s constructor is used at, interned:
the rule's recorded levels (`nested`, `levels`), else the constructor's own parameters (`IW`
slice `(lpsO, lpsL)`). -/
-- con-ron: ConRon/Arena/Inductives/IotaRead.lean:234-242 ConRon.Arena.ctorLevelsAt
@[no_expose, l_impl ConRon.Arena.ctorLevelsAt]
def ctorLevelsAtL : FunDecl := lfn (r, lpsO, lpsL) locals (o, l, us) {
  if EREC⦃r + ⟪Rule.fire⟫⦄ != 0 {
    (o, l) := call er_to_iw(EREC⦃r + ⟪Rule.lvlsOff⟫⦄, EREC⦃r + ⟪Rule.lvlsLen⟫⦄);
    us := call intern_ls_iw(o, l);
    return us
  };
  us := call param_levels(lpsO, lpsL);
  return us
}

/-- `iota_bvars(rP, n)`: `bvar (rP - 1 - i)` for `i < n`, as a fresh `IW` slice. -/
-- con-ron: ConRon/Arena/Inductives/IotaRead.lean:244-252 ConRon.Arena.iotaBVars
@[no_expose, l_impl ConRon.Arena.iotaBVars]
def iotaBVarsL : FunDecl := lfn (rP, n) locals (o, i, b) {
  if n == 0 { return (0, 0) };
  o := call iw_alloc(n);
  i := 0;
  while i < n {
    b := call intern_bvar(rP - 1 - i);
    if 4294967296 <= b { abort };
    IW.u64[o + i] := b;
    i := i + 1
  };
  return (o, n)
}

/-- `iota_params_at(r, rP, cnP)`: the parameters the rule `r` applies its constructor to: a
nested rule's recorded pins (copied to `IW`), else the prefix's first `min cnP rP` variables. -/
-- con-ron: ConRon/Arena/Inductives/IotaRead.lean:254-261 ConRon.Arena.iotaParamsAt
@[no_expose, l_impl ConRon.Arena.iotaParamsAt]
def iotaParamsAtL : FunDecl := lfn (r, rP, cnP) locals (o, l, k) {
  if EREC⦃r + ⟪Rule.fire⟫⦄ == 1 {
    (o, l) := call er_to_iw(EREC⦃r + ⟪Rule.pinsOff⟫⦄, EREC⦃r + ⟪Rule.pinsLen⟫⦄);
    return (o, l)
  };
  k := cnP;
  if rP < cnP { k := rP };
  (o, l) := call iota_bvars(rP, k);
  return (o, l)
}

/-- `iota_parts_at_body(cnP, mI, rP, r, lvls, parO, parL, pdO, pdL, ctorBody)`: `iota_parts_at`
past the parameters: the constructor's body at the rule's parameters, its next `nfields`
binders, the indices behind the parameters, the shape guard; `(ok, IIotaParts, pdO, pdL)`. -/
-- con-ron: ConRon/Arena/Inductives/IotaRead.lean:263-282 ConRon.Arena.iotaPartsAtBody
@[no_expose, l_impl ConRon.Arena.iotaPartsAtBody]
def iotaPartsAtBodyL : FunDecl := lfn (cnP, mI, rP, r, lvls, parO, parL, pdO, pdL, ctorBody) locals
    (body, ok, fo, fl, concl, ao, al, io, il) {
  body := call instantiate_lift_fast(⟪CWF⟫, ctorBody, parO, parL, 0);
  (ok, fo, fl, concl) := call strip_pis(EREC⦃r + ⟪Rule.nfields⟫⦄, body);
  if ok == 0 { return (0, 0, 0, 0, 0, 0, 0, 0, 0, 0) };
  (ao, al) := call get_app_args_f(⟪CWF⟫, concl);
  io := ao + cnP;
  il := al - cnP;
  if al < cnP { io := ao + al; il := 0 };
  if parL != cnP { return (0, 0, 0, 0, 0, 0, 0, 0, 0, 0) };
  if mI < rP { return (0, 0, 0, 0, 0, 0, 0, 0, 0, 0) };
  if il != mI - rP { return (0, 0, 0, 0, 0, 0, 0, 0, 0, 0) };
  return (1, fo, fl, io, il, lvls, parO, parL, pdO, pdL)
}

/-- `iota_parts_at(qj, cnP, mI, rP, r)`: a rule's parts read through its constructor (constant
value `qj`, `cnP` parameters): its type at the rule's levels, instantiated at the rule's
parameters; `(ok, IIotaParts, pdO, pdL)`, the last the constructor's parameter domains at the
rule's levels. -/
-- con-ron: ConRon/Arena/Inductives/IotaRead.lean:284-298 ConRon.Arena.iotaPartsAt
@[no_expose, l_impl ConRon.Arena.iotaPartsAt]
def iotaPartsAtL : FunDecl := lfn (qj, cnP, mI, rP, r) locals
    (lo, ll, lvls, paO, paL, ty, ok, pdO, pdL, cb, x1, x2, x3, x4, x5, x6, x7, x8, x9) {
  (lo, ll) := call cv_lps(qj);
  lvls := call ctor_levels_at(r, lo, ll);
  (paO, paL) := call iota_params_at(r, rP, cnP);
  ty := call inst_lp_fast(⟪CWF⟫, lo, ll, lvls, EREC⦃qj + ⟪CV.type⟫⦄);
  (ok, pdO, pdL, cb) := call strip_pis(cnP, ty);
  if ok == 0 { return (0, 0, 0, 0, 0, 0, 0, 0, 0, 0) };
  (ok, x1, x2, x3, x4, x5, x6, x7, x8, x9) :=
    call iota_parts_at_body(cnP, mI, rP, r, lvls, paO, paL, pdO, pdL, cb);
  return (ok, x1, x2, x3, x4, x5, x6, x7, x8, x9)
}

/-! ## The module's program -/

/-- This module's functions. -/
def iotaFrameFns : Prog :=
  [("pi_tele", piTeleL), ("motive_level", motiveLevelL), ("iota_frame", iotaFrameL),
   ("is_minor_at", isMinorAtL), ("minors_from", minorsFromL), ("iota_read_major", iotaReadMajorL),
   ("iota_rec_of", iotaRecOfL), ("lift_field_doms", liftFieldDomsL),
   ("lift_idx_args", liftIdxArgsL), ("iota_parts_of_at", iotaPartsOfAtL),
   ("ctor_levels_at", ctorLevelsAtL), ("iota_bvars", iotaBVarsL),
   ("iota_params_at", iotaParamsAtL), ("iota_parts_at_body", iotaPartsAtBodyL),
   ("iota_parts_at", iotaPartsAtL)]

end L.Ind
