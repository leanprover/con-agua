module

public import ConAgua.Arena.WhnfBase

@[expose] public section

/-!
# ι-reduction: `iota_rec_at` split into small functions

The twin's `ConRon.Arena.iotaRecAt` (`vendor/con-ron/ConRon/Arena/Core.lean:2490-2541`) is one
long nest of checks at the record its caller found. `iota_rec_at` (`WhnfIota.lean`, the
`@[l_impl]` function) peels the recursor's telescope and calls the pieces below, one per block of
the twin's nest:

* `iota_rec_major(mode, vis, d, c, us, recP, so, sn)`: the major's preparation and view
  (`prepare_major`: the constructor, its levels and record), the rule;
* `iota_rec_fire(…, major)`: the major's arguments (a slice at the stack top, `get_app_args`), the
  top put back after the rest (`iota_rec_fire2`);
* `iota_rec_fire2(…, mo, mn)`: the argument count, the certificate family (`iota_rec_fam`), the
  rule's body under its binders (`rule_body_at`) with the leading arguments and the fields
  substituted (`iotaVals`: two `eidx_copy_upto`s, then `inst_list`);
* `iota_rec_fam(…)`: the verified-mode block (`iotaNoCert`, then `recFireLevels`, `iotaCase3At` at
  the recursor's `isK` and the constructor's `induct`);
* `iota_rec_vck(…, cmpL)`: the level comparison (`lvls_eq_c`, the twin's cached `lvlsEq?`),
  the parameter comparison (`iota_rec_cmp`), the constructor telescope, the indices;
* `iota_rec_cmp(…)`: the parameter comparands (`rec_fire_args`) against the major's leading
  arguments (`defeq_list`), the top put back;
* `erec_push(o, c, k)`: a nested rule's stored pins (an `EREC` slice) copied to the stack top,
  where `rec_fire_args` reads them; `stack_cover(x)`: the top raised to `x`;
* `eidx_copy_upto(o, n)`: the stack slice `(o, n)` copied to the stack top.

The slices: the recursor's arguments `(so, sn)` below the top; the major's arguments `(mo, mn)`
exactly at the top while `iota_rec_fire2` runs (`iota_certs_full` asks for it); the substituted
values pushed above them.
-/

open ConRon.Arena


namespace L.Arena

/-- The copy loop of `erec_push` (a named block, for the proofs): each word stored at the top,
the top raised past it. -/
def erecPushLoop : Stmt := lblk (o, c, k, so, j) {
  for j < c {
    SPN.u64[so + j] := EREC⦃o + j⦄;
    CTL.u64[136] := so + j + 1
  }
}

/-- A nested rule's stored pins (the `EREC` slice `(o, c)`, `k = 1` the rule's fire kind) pushed
on the stack: the slice's offset is the old top, the top is raised past it. Nothing for `k ≠ 1` (a
plain rule has no pins). -/
-- con-ron: ConRon/Arena/Core.lean:2479-2538 ConRon.Arena.iotaRecAt
@[no_expose] def erecPushL : FunDecl := lfn (o, c, k) locals (so, j) {
  if k != 1 { return 0 };
  so := CTL.u64[136];
  if len(SPN.u64) < so { abort };
  if len(SPN.u64) - so < c { abort };
  j := 0;
  ⟪erecPushLoop⟫;
  return so
}

/-- The stack top raised to `x` if it is below. -/
-- con-ron: none — the stack top, L plumbing for the twin's list values
@[no_expose] def stackCoverL : FunDecl := lfn (x) locals () {
  if CTL.u64[136] < x { CTL.u64[136] := x };
  return 0
}

/-- The parameter comparands of a firing rule (`recFireArgs` over the recursor's spine `(so, mI + 1)`)
against the major's leading `cnP` arguments (`defEqList`; `cnP` the stored constructor's parameter
count, `ctorP + CI.ctorNparams`). A nested rule's pins are copied to the stack first; the
top is raised over the comparand slice (it lies below it already) and put back at the end. -/
-- con-ron: ConRon/Arena/Core.lean:2479-2538 ConRon.Arena.iotaRecAt
@[no_expose] def iotaRecCmpL : FunDecl := lfn (mode, vis, d, us, recP, so, ctorP, rl, mo)
    locals (top, pvo, ao, an, x, ok) {
  top := CTL.u64[136];
  pvo := call erec_push(EREC⦃rl + ⟪Rule.pinsOff⟫⦄, EREC⦃rl + ⟪Rule.pinsLen⟫⦄, EREC⦃rl + ⟪Rule.fire⟫⦄);
  (ao, an) := call rec_fire_args(EREC⦃rl + ⟪Rule.fire⟫⦄, pvo, EREC⦃rl + ⟪Rule.pinsLen⟫⦄,
    EREC⦃recP + ⟪CI.cv + CV.lpsOff⟫⦄, EREC⦃recP + ⟪CI.cv + CV.lpsLen⟫⦄, us, so, EREC⦃recP + ⟪CI.recMajor⟫⦄ + 1,
    EREC⦃recP + ⟪CI.recPrefix⟫⦄, EREC⦃ctorP + ⟪CI.ctorNparams⟫⦄);
  x := call stack_cover(ao + an);
  ok := call defeq_list(mode, vis, d, mo, EREC⦃ctorP + ⟪CI.ctorNparams⟫⦄, ao, an);
  CTL.u64[136] := top;
  return ok
}

/-- The verified checks of a case-3 redex past `iotaCase3At`: the constructor's levels against the
comparands (`lvls_eq_c`; `0`, the twin's fuel exhaustion, is a decline: `abort`), its parameters
(`iota_rec_cmp`), its telescope at the full grade (`iota_certs_full`), the indices
(`iota_index_ok`; the twin's `(args.take mI).drop rP`: the slice from `so + min rP mI`). -/
-- con-ron: ConRon/Arena/Core.lean:2479-2538 ConRon.Arena.iotaRecAt
@[no_expose] def iotaRecVckL : FunDecl := lfn (mode, vis, d, us, recP, so, usj, ctorP, rl, mo, mn, cmpL)
    locals (lok, ok, tyC) {
  lok := call lvls_eq_c(usj, cmpL);
  if lok == 0 { fail R_RESOURCE_LIMIT_FUEL };
  if lok == 1 { return 0 };
  ok := call iota_rec_cmp(mode, vis, d, us, recP, so, ctorP, rl, mo);
  if ok == 0 { return 0 };
  tyC := call const_ty_at(EREC⦃ctorP + ⟪CI.cv + CV.name⟫⦄, EREC⦃ctorP + ⟪CI.cv + CV.lpsOff⟫⦄, EREC⦃ctorP + ⟪CI.cv + CV.lpsLen⟫⦄,
    EREC⦃ctorP + ⟪CI.cv + CV.type⟫⦄, usj);
  ok := call iota_certs_full(mode, vis, d, tyC, mo, mn);
  if ok == 0 { return 0 };
  ok := call iota_index_ok(mode, vis, d, EREC⦃recP + ⟪CI.recMajor⟫⦄, EREC⦃recP + ⟪CI.recPrefix⟫⦄,
    EREC⦃ctorP + ⟪CI.ctorNparams⟫⦄, tyC, mo, mn,
    so + (EREC⦃recP + ⟪CI.recPrefix⟫⦄ -
      (EREC⦃recP + ⟪CI.recPrefix⟫⦄ - EREC⦃recP + ⟪CI.recMajor⟫⦄) * u64(EREC⦃recP + ⟪CI.recMajor⟫⦄ <= EREC⦃recP + ⟪CI.recPrefix⟫⦄)),
    (EREC⦃recP + ⟪CI.recMajor⟫⦄ - EREC⦃recP + ⟪CI.recPrefix⟫⦄) * u64(EREC⦃recP + ⟪CI.recPrefix⟫⦄ <= EREC⦃recP + ⟪CI.recMajor⟫⦄));
  return ok
}

/-- The certificate family: nothing in a trusted mode, where the stored facts need no certificate
(`iota_no_cert` at the rule's comparand level count, `rec_fire_level_count`) or outside case 3;
else `iota_rec_vck`. -/
-- con-ron: ConRon/Arena/Core.lean:2479-2538 ConRon.Arena.iotaRecAt
@[no_expose] def iotaRecFamL : FunDecl := lfn (mode, vis, d, us, recP, so, usj, ctorP, rl, mo, mn)
    locals (lc, nc, cmpL, c3, r) {
  if mode & 1 != 0 { return 1 };
  lc := call rec_fire_level_count(EREC⦃rl + ⟪Rule.fire⟫⦄, EREC⦃rl + ⟪Rule.lvlsLen⟫⦄, EREC⦃ctorP + ⟪CI.cv + CV.lpsLen⟫⦄);
  nc := call iota_no_cert(vis, EREC⦃recP + ⟪CI.recIsK⟫⦄, EREC⦃ctorP + ⟪CI.ctorInduct⟫⦄, lc);
  if nc != 0 { return 1 };
  cmpL := call rec_fire_levels(EREC⦃rl + ⟪Rule.fire⟫⦄, EREC⦃rl + ⟪Rule.lvlsOff⟫⦄, EREC⦃rl + ⟪Rule.lvlsLen⟫⦄,
    EREC⦃recP + ⟪CI.cv + CV.lpsOff⟫⦄, EREC⦃recP + ⟪CI.cv + CV.lpsLen⟫⦄, us, EREC⦃ctorP + ⟪CI.cv + CV.lpsOff⟫⦄,
    EREC⦃ctorP + ⟪CI.cv + CV.lpsLen⟫⦄);
  c3 := call iota_case3_at(mode, vis, EREC⦃recP + ⟪CI.recIsK⟫⦄, EREC⦃ctorP + ⟪CI.ctorInduct⟫⦄, cmpL);
  if c3 == 0 { return 1 };
  r := call iota_rec_vck(mode, vis, d, us, recP, so, usj, ctorP, rl, mo, mn, cmpL);
  return r
}

/-- con-leche: `Cached/CoreC.lean:194-197` `pushRange` — the stack slice `(o, n)` copied to the
stack top (`SPN[o + j]` below the old top), the top raised past it; the copy's offset (the old top)
is the answer. -/
-- con-ron: ConRon/Arena/ExprOps.lean:183-190 ConRon.Arena.eidxCopyUpto
@[no_expose, l_impl ConRon.Arena.eidxCopyUpto]
def eidxCopyUptoL : FunDecl := lfn (o, n) locals (so, j) {
  so := CTL.u64[136];
  if len(SPN.u64) < so { abort };
  if len(SPN.u64) - so < n { abort };
  j := 0;
  for j < n {
    SPN.u64[so + j] := SPN.u64[o + j];
    CTL.u64[136] := so + j + 1
  };
  return so
}

/-- The fire past the major's arguments `(mo, mn)` (at the stack top): their count, the
certificate family (the parameter count `cp` the stored constructor's, the field count the
rule's), the rule's body under its `rP + nfields` binders at the recursor's levels
(`rule_body_at`; a binder count past `2^64` aborts, a capacity check), with the leading `rP` arguments (the twin's `p`: all `mI + 1` of them when
`mI < rP`, so `rP` is capped at `mI + 1`) and the fields pushed above the top (`iotaVals`) and
substituted in one walk (`inst_list`). -/
-- con-ron: ConRon/Arena/Core.lean:2479-2538 ConRon.Arena.iotaRecAt
-- con-ron: ConRon/Arena/Core.lean:2471-2477 ConRon.Arena.iotaVals
@[no_expose] def iotaRecFire2L : FunDecl := lfn (mode, vis, d, c, us, recP, so, usj, ctorP, rl, mo, mn)
    locals (cp, rP, fam, k, body, vo, u, x) {
  cp := EREC⦃ctorP + ⟪CI.ctorNparams⟫⦄;
  if mn < cp { return (0, 0) };
  if mn - cp != EREC⦃rl + ⟪Rule.nfields⟫⦄ { return (0, 0) };
  fam := call iota_rec_fam(mode, vis, d, us, recP, so, usj, ctorP, rl, mo, mn);
  if fam == 0 { return (0, 0) };
  k := EREC⦃recP + ⟪CI.recPrefix⟫⦄ + EREC⦃rl + ⟪Rule.nfields⟫⦄;
  -- a fixed capacity: the binder count past `2^64` aborts
  if k < EREC⦃recP + ⟪CI.recPrefix⟫⦄ { abort };
  body := call rule_body_at(c, EREC⦃rl⦄, EREC⦃recP + ⟪CI.cv + CV.lpsOff⟫⦄, EREC⦃recP + ⟪CI.cv + CV.lpsLen⟫⦄,
    EREC⦃rl + ⟪Rule.rhs⟫⦄, k, us);
  rP := EREC⦃recP + ⟪CI.recPrefix⟫⦄;
  rP := rP - (rP - EREC⦃recP + ⟪CI.recMajor⟫⦄ - 1) * u64(EREC⦃recP + ⟪CI.recMajor⟫⦄ < rP);
  vo := CTL.u64[136];
  u := call eidx_copy_upto(so, rP);
  u := call eidx_copy_upto(mo + cp, mn - cp);
  x := call inst_list(body, vo, rP + (mn - cp), 0);
  CTL.u64[136] := vo;
  return (1, x)
}

/-- The major's arguments on the stack, the fire, the top put back. -/
-- con-ron: ConRon/Arena/Core.lean:2479-2538 ConRon.Arena.iotaRecAt
@[no_expose] def iotaRecFireL : FunDecl := lfn (mode, vis, d, c, us, recP, so, usj, ctorP, rl, major)
    locals (top, mo, mn, r1, r2) {
  top := CTL.u64[136];
  (mo, mn) := call get_app_args(major);
  (r1, r2) := call iota_rec_fire2(mode, vis, d, c, us, recP, so, usj, ctorP, rl, mo, mn);
  CTL.u64[136] := top;
  return (r1, r2)
}

/-- The major premise prepared and classified (`prepare_major`'s view `[t, major, cj, usj, ctorP]`),
a stored constructor with a rule. -/
-- con-ron: ConRon/Arena/Core.lean:2479-2538 ConRon.Arena.iotaRecAt
@[no_expose] def iotaRecMajorL : FunDecl := lfn (mode, vis, d, c, us, recP, so, sn)
    locals (b0, t, major, cj, usj, ctorP, rf, rl, r1, r2) {
  b0 := call intern_bvar(0);
  (t, major, cj, usj, ctorP) := call prepare_major(mode, vis, d, c, EREC⦃recP + ⟪CI.recIsK⟫⦄,
    EREC⦃recP + ⟪CI.recRulesOff⟫⦄, EREC⦃recP + ⟪CI.recRulesLen⟫⦄, SPN.u64[so + EREC⦃recP + ⟪CI.recMajor⟫⦄]);
  if t == 0 { return (0, 0) };
  (rf, rl) := call find_rule(EREC⦃recP + ⟪CI.recRulesOff⟫⦄, EREC⦃recP + ⟪CI.recRulesLen⟫⦄, cj);
  if rf == 0 { return (0, 0) };
  (r1, r2) := call iota_rec_fire(mode, vis, d, c, us, recP, so, usj, ctorP, rl, major);
  return (r1, r2)
}

/-- What the pieces' specs need of a program: the pieces, at their names. -/
structure IotaRecProg (p : Prog) : Prop where
  erecPush : p.lookup "erec_push" = some erecPushL
  stackCover : p.lookup "stack_cover" = some stackCoverL
  cmp : p.lookup "iota_rec_cmp" = some iotaRecCmpL
  vck : p.lookup "iota_rec_vck" = some iotaRecVckL
  fam : p.lookup "iota_rec_fam" = some iotaRecFamL
  fire2 : p.lookup "iota_rec_fire2" = some iotaRecFire2L
  fire : p.lookup "iota_rec_fire" = some iotaRecFireL
  major : p.lookup "iota_rec_major" = some iotaRecMajorL
  copy : p.lookup "eidx_copy_upto" = some eidxCopyUptoL

end L.Arena
