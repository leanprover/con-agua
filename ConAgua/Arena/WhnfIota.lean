import ConAgua.Arena.WhnfBase
import ConAgua.Arena.WhnfSpine
import ConAgua.Arena.WhnfCore
import ConAgua.Arena.Env
import ConAgua.Arena.EnvRec
import ConAgua.Arena.CoreCaches
import ConAgua.Arena.CoreRefine
import ConAgua.Arena.Pins
import ConAgua.Arena.LevelEquiv
import ConAgua.Census.Attr

/-!
# ι-reduction: `ConRon.Arena.Core.lean`, the recursor rule fire

Twin: `vendor/con-ron/ConRon/Arena/Core.lean` (roughly lines 1285-2100): `iotaRecAt` and
everything it calls that is not already owned by another file (`WhnfSpine.lean`'s spine helpers,
`WhnfBase.lean`'s knot/slot machinery, `Env.lean`/`EnvRec.lean`'s `env_find`/record decoders,
`Pins.lean`'s `pin_at`, `LevelEquiv.lean`'s `lvl_eq`/`lvls_eq`).

## Stubs this file assumes (`IotaCallees`)

* `inst_entry(e, v, d)` (ALREADY a real, complete L function, `Inst1Spec.lean`): this file's own
  stub `IotaInst1OK` only PINS its twin fuel at `coreWalkFuel` exactly (the existing
  `instEntry_refines` is generic over any twin fuel `F ≥ n`); named `IotaInst1OK` rather than
  `Inst1OK` to avoid a clash with lane `whnf`'s own `whnfCore`-side stub of the same shape.
* `find_proj(vis, T, i)`, `fire_ok(q, i, us)`: another agent's L functions (`IFEnv.findProj?`,
  `IProjEntry.fireOk`), not yet written anywhere; assumed here as named stubs.
* `caps_never_zero(po, pc, us, swd, so, sc)`: `(Level.substPW ks vs pw).isNever` at the recursor's
  own level parameters (`po, pc`, an `EREC` name slice), the universe arguments `us` (an `LsIdx`),
  and a `PropWhen` datum `(swd, so, sc)` (`swd = 0` never, `1` `ifAllZero` with name slice
  `(so, sc)`, also in `EREC`). Lane `levels`' `lv_substpw`/`lv_spw`/`lv_zero` implement exactly
  this algorithm, but only when its KA/VA/PA arrays are concretely instantiated and wired to a
  flattened `us` slice; that wiring is not yet installed anywhere, so this stays a stub (the
  escape hatch the task note licenses) rather than a mis-wired "real" call.
* `rec_fire_levels(…)`: for the same reason (`Level.subst`'s *per-element* substitution would also
  need its heap-pointer results *reified* back into genuine interned level handles via
  `internLevel`, a walk that does not exist yet either), this whole function is a stub, not just
  its level-algorithm leaf. `rec_fire_args`/`inst_spine_pins`/`inst_spine` are NOT stubs: they only
  need `inst_lp` (already a `WhnfCallees` stub) and `inst_entry` (real), so they are written out in
  full.
* `wscoped_bfast(d, e)`, `loose_bvars_bounded_fast(c, e)`, `leaf_guard(fab, major)`: the task's own
  "phase 4 walks, stubs too".
* `lit_to_ctor_if_nat(vis, h)`: "written by another agent in `WhnfDelta.lean`" (which does not
  exist yet); called by name.

`str_lit_supported`, `str_lit_ctor`, `inst_list`, `inst_lp` are already `WhnfCallees` stubs
(`WhnfBase.lean`) and are reused via that hypothesis, not redeclared here.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedVariables false

namespace L.Arena

/-! ## `is_ctor_app(vis, e)`, `is_str_lit(h)` -/

/-- con-leche: `CoreDefs.lean:51-58` `isCtorApp` — the spine's head is a stored constructor. -/
-- con-ron: ConRon/Arena/Core.lean:327-338 ConRon.Arena.isCtorApp
@[l_impl ConRon.Arena.isCtorApp]
def isCtorAppL : FunDecl := lfn (vis, e) locals (hh, t, i, c, flag, q) {
  hh := call get_app_fn(e);
  if hh >> 28 != 3 { return 0 };
  t := (hh >> 27) & 1;
  i := hh & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[18 + t] <= i { abort };
  c := CREC.u64[i * 4 + t * 2];
  (flag, q) := call env_find(c, vis);
  if flag == 0 { return 0 };
  return u64(EREC.u64[q] == 4)
}

/-- con-leche: `Core.lean:695-699` `Expr.isStrLit` — the tag, then the literal kind. -/
-- con-ron: ConRon/Arena/Core.lean:1903-1911 ConRon.Arena.isStrLit
@[l_impl ConRon.Arena.isStrLit]
def isStrLitL : FunDecl := lfn (h) locals (t, i) {
  if h >> 28 != 8 { return 0 };
  t := (h >> 27) & 1;
  i := h & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[2 + t] <= i { abort };
  return u64(REC.u64[i * 8 + t * 4] == 1)
}

/-! ## `find_rule(ro, rc, c)`, `rec_rule_k(ro, rc)`

Both read only the 11-word rule records at `(ro, rc)` in `EREC`; neither touches `AM`. -/

/-- con-leche: `Core.lean:777-876` (`iotaRec`'s own lookup) `findRule` — the rule whose
constructor is `c`, as a linear scan of the rule-record slice. -/
-- con-ron: ConRon/Arena/Core.lean:2005-2010 ConRon.Arena.findRule
@[l_impl ConRon.Arena.findRule]
def findRuleL : FunDecl := lfn (ro, rc, c) locals (i) {
  i := 0;
  while i < rc {
    if EREC.u64[ro + 11 * i] == c { return (1, ro + 11 * i) };
    i += 1
  };
  return (0, 0)
}

/-- con-leche: `CoreDefs.lean:899-906` `recRuleK` — the stored bit of the single rule. -/
-- con-ron: ConRon/Arena/Core.lean:1896-1901 ConRon.Arena.recRuleK
@[l_impl ConRon.Arena.recRuleK]
def recRuleKL : FunDecl := lfn (ro, rc) locals () {
  if rc != 1 { return 0 };
  return EREC.u64[ro + 9]
}

/-! ## Reserved names: a small fusion of `reservedBasisNames` and `List.contains`

Not tagged `@[l_impl]` on its own (it fuses a lookup declaration and a list membership test, as
the house style allows for small dispatchers); `major_to_ctor`'s eta branch is its only caller. -/

/-- con-ron: ConRon/Arena/Core.lean:1451-1455 ConRon.Arena.reservedBasisNames -/
def reservedContainsL : FunDecl := lfn (x) locals (j) {
  if PINS.u64[0] == 0 { abort };
  j := 0;
  while j < 16 {
    if PINS.u64[55 + j] == x { return 1 };
    j += 1
  };
  return 0
}

/-! ## `caps_never_zero(…)`, `iota_ctor_never_prop(…)`, `iota_case3(…)`

`caps_never_zero` is a named stub (see the module note); `iota_ctor_never_prop` and `iota_case3`
are real dispatchers around it, faithful to the twin's own head-symbol/env-lookup/arity gates. -/

/-- con-leche: `CoreDefs.lean:72-93` `iotaCtorNeverProp` — is the matched constructor's family
never `Prop` at the comparand levels? `ctorP` is the constructor's `IConstantInfo` pointer
(`cvj`'s record base); its type's Π-result's head constant is looked up for the family's `caps`. -/
-- con-ron: ConRon/Arena/Core.lean:348-365 ConRon.Arena.iotaCtorNeverProp
@[l_impl ConRon.Arena.iotaCtorNeverProp]
def iotaCtorNeverPropL : FunDecl := lfn (vis, ctorP, us)
    locals (ty, piRes, hh, t, i, T, indFlag, indP, uso, usl, nz) {
  ty := EREC.u64[ctorP + 4];
  piRes := call pi_result(ty);
  hh := call get_app_fn(piRes);
  if hh >> 28 != 3 { return 0 };
  t := (hh >> 27) & 1;
  i := hh & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[18 + t] <= i { abort };
  T := CREC.u64[i * 4 + t * 2];
  (indFlag, indP) := call env_find(T, vis);
  if indFlag == 0 { return 0 };
  if EREC.u64[indP] != 3 { return 0 };
  (uso, usl) := call ls_node(us);
  if EREC.u64[indP + 3] != usl { return 0 };
  nz := call caps_never_zero(EREC.u64[indP + 2], EREC.u64[indP + 3], us,
    EREC.u64[indP + 12], EREC.u64[indP + 13], EREC.u64[indP + 14]);
  return nz
}

/-- con-leche: `CoreDefs.lean:95-104` `iotaCase3` — case 3 of the ι split: not K, and the
constructor's family may be `Prop` at the comparand levels. `ctorP` as above. -/
-- con-ron: ConRon/Arena/Core.lean:367-376 ConRon.Arena.iotaCase3
@[l_impl ConRon.Arena.iotaCase3]
def iotaCase3L : FunDecl := lfn (rlk, vis, ctorP, us) locals (np) {
  if rlk != 0 { return 0 };
  np := call iota_ctor_never_prop(vis, ctorP, us);
  return u64(np == 0)
}

/-! ## `tower_slots_all(vis, T, nF)`, `eta_projs(T, b, nF)`, `eta_fab_args(…)` -/

/-- con-leche: `CoreDefs.lean:723-728`/`FEnv.lean:195-197` `towerSlotsAll` — are all `nF`
projection slots of `T` table entries? -/
-- con-ron: ConRon/Arena/Core.lean:1429-1433 ConRon.Arena.towerSlotsAll
@[l_impl ConRon.Arena.towerSlotsAll]
def towerSlotsAllL : FunDecl := lfn (vis, T, nF) locals (j, flag, q) {
  j := 0;
  while j < nF {
    (flag, q) := call find_proj(vis, T, j);
    if flag == 0 { return 0 };
    j += 1
  };
  return 1
}

/-- con-leche: `CoreDefs.lean:730-735`/`Cached/CoreC.lean:310-317` `etaProjs`/`projNodesGo` — the
`.proj T j b` spine, `j = 0, …, nF - 1`, pushed in order. -/
-- con-ron: ConRon/Arena/Core.lean:1444-1449 ConRon.Arena.etaProjs
-- con-ron: ConRon/Arena/Core.lean:1435-1442 ConRon.Arena.projNodesGo
@[l_impl ConRon.Arena.etaProjs ConRon.Arena.projNodesGo]
def etaProjsL : FunDecl := lfn (T, b, nF) locals (o, j, pr) {
  o := CTL.u64[136];
  if len(SPN.u64) < o { abort };
  if len(SPN.u64) - o < nF { abort };
  j := 0;
  while j < nF {
    pr := call mk_proj(T, j, b);
    SPN.u64[o + j] := pr;
    j += 1
  };
  CTL.u64[136] := o + nF;
  return (o, nF)
}

/-- con-leche: `CoreDefs.lean:750-754` `etaFabArgsE` — the major's type's arguments, then the
major's projections. The second slice is pushed directly after the first (nothing intervenes), so
the concatenation is the one combined slice. -/
-- con-ron: ConRon/Arena/Core.lean:1637-1643 ConRon.Arena.etaFabArgsE
@[l_impl ConRon.Arena.etaFabArgsE]
def etaFabArgsL : FunDecl := lfn (T, to, tn, major, nF) locals (o2, n2) {
  (o2, n2) := call eta_projs(T, major, nF);
  return (to, tn + n2)
}

/-! ## `and_rescue_slots(vis, ctor, nP, us)` -/

/-- con-leche: `CoreDefs.lean:793-806`/`:808-810`/`FEnv.lean:199-201` `andRescueSlotsGo` /
`andRescueSlots` / `FEnv.andRescueSlotsF` — the pinned `And`'s two projection slots, ready to
fire. `q`, the table pointer `find_proj` hands back, has `ctor` at `q + 6`, `numParams` at `q + 5`,
`numFields` at `q + 7` (`EnvRec.lean`'s `decTbl`). -/
-- con-ron: ConRon/Arena/Core.lean:1658-1670 ConRon.Arena.andRescueSlotsGo
-- con-ron: ConRon/Arena/Core.lean:1672-1680 ConRon.Arena.andRescueSlots
@[l_impl ConRon.Arena.andRescueSlotsGo ConRon.Arena.andRescueSlots]
def andRescueSlotsL : FunDecl := lfn (vis, ctor, nP, us) locals (an, j, flag, q, ok) {
  an := call pin_at(11);
  j := 0;
  while j < 2 {
    (flag, q) := call find_proj(vis, an, j);
    if flag == 0 { return 0 };
    if EREC.u64[q + 6] != ctor { return 0 };
    if EREC.u64[q + 5] != nP { return 0 };
    if EREC.u64[q + 7] != 2 { return 0 };
    ok := call fire_ok(q, j, us);
    if ok == 0 { return 0 };
    j += 1
  };
  return 1
}

/-! ## `fab_scope_ok(d, fab, major)` -/

/-- con-leche: `Core.lean:502-663` (the shared scope guard) `fabScopeOk` — well-scoped, closed
under loose bvars, and every free variable of `fab` is one of `major`'s. All three callees are
phase-4-walk stubs. -/
-- con-ron: ConRon/Arena/Core.lean:1686-1703 ConRon.Arena.fabScopeOk
@[l_impl ConRon.Arena.fabScopeOk]
def fabScopeOkL : FunDecl := lfn (d, fab, major) locals (ok) {
  ok := call wscoped_bfast(d, fab);
  if ok == 0 { return 0 };
  ok := call loose_bvars_bounded_fast(0, fab);
  if ok == 0 { return 0 };
  ok := call leaf_guard(fab, major);
  return ok
}

/-! ## `lit_major_to_ctor(mode, vis, d, h)` -/

/-- con-leche: `Core.lean:665-677` `litMajorToCtor` — a `Nat` literal major one layer, a `String`
literal to its reduced constructor form. -/
-- con-ron: ConRon/Arena/Core.lean:1822-1835 ConRon.Arena.litMajorToCtor
@[l_impl ConRon.Arena.litMajorToCtor]
def litMajorToCtorL : FunDecl := lfn (mode, vis, d, h) locals (t, i, kind, sup, c, r) {
  if h >> 28 != 8 { r := call lit_to_ctor_if_nat(vis, h); return r };
  t := (h >> 27) & 1;
  i := h & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[2 + t] <= i { abort };
  kind := REC.u64[i * 8 + t * 4];
  if kind != 1 { r := call lit_to_ctor_if_nat(vis, h); return r };
  sup := call str_lit_supported(vis);
  if sup == 0 { return h };
  c := call str_lit_ctor(h);
  r := call whnf(mode, vis, d, c);
  return r
}

/-! ## `major_to_ctor(mode, vis, d, rec, ro, rc, major)`

`rec` (the recursor's own name) is unused by the twin (`_recName`) and so by this code too: it is
accepted only to match the twin's argument list. -/

/-- con-leche: `Core.lean:502-663`/`Cached/CoreC.lean:428-453` `majorToCtor`/`majorToCtorI` — the
stuck-major rescue: K-flagged, η-capable, or the pinned `And`. No certificate on a fabricated
spine; the K and `And` fabrications keep the type check, and the proof-irrelevance run is a
certificate family (off at `.trusted`). -/
-- con-ron: ConRon/Arena/Core.lean:1705-1820 ConRon.Arena.majorToCtor
@[l_impl ConRon.Arena.majorToCtor]
def majorToCtorL : FunDecl := lfn (mode, vis, d, rec, ro, rc, major)
    locals (ok, cvjFlag, cvjP, cvjTy, cnP, piRes, hh, t, i, T,
            indFlag, indP, rlK, rlEta, vck,
            ioa, tmaj, hh2, t2, i2, T2, ust, usto, ustl, to, tn, hd, fab,
            scopeOk, ioa2, defOk, irOk,
            nz, resT, resEC, slotsOk, fo, fn,
            an2, p0, p1, ars) {
  ok := call is_ctor_app(vis, major);
  if ok != 0 { return major };
  if rc != 1 { return major };
  (cvjFlag, cvjP) := call env_find(EREC.u64[ro], vis);
  if cvjFlag == 0 { return major };
  if EREC.u64[cvjP] != 4 { return major };
  cvjTy := EREC.u64[cvjP + 4];
  cnP := EREC.u64[cvjP + 5];
  piRes := call pi_result(cvjTy);
  hh := call get_app_fn(piRes);
  if hh >> 28 != 3 { return major };
  t := (hh >> 27) & 1;
  i := hh & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[18 + t] <= i { abort };
  T := CREC.u64[i * 4 + t * 2];
  (indFlag, indP) := call env_find(T, vis);
  if indFlag == 0 { return major };
  if EREC.u64[indP] != 3 { return major };
  rlK := EREC.u64[ro + 9];
  rlEta := EREC.u64[ro + 10];
  vck := u64(mode & 1 == 0);
  if rlK != 0 {
    ioa := call infer_io(mode, vis, d, major);
    tmaj := call whnf(mode, vis, d, ioa);
    hh2 := call get_app_fn(tmaj);
    if hh2 >> 28 != 3 { return major };
    t2 := (hh2 >> 27) & 1;
    i2 := hh2 & 134217727;
    if t2 != 0 && CTL.u64[1] == 0 { abort };
    if CTL.u64[18 + t2] <= i2 { abort };
    T2 := CREC.u64[i2 * 4 + t2 * 2];
    ust := CREC.u64[i2 * 4 + t2 * 2 + 1];
    (usto, ustl) := call ls_node(ust);
    if T2 != T { return major };
    if EREC.u64[cvjP + 3] != ustl { return major };
    (to, tn) := call get_app_args(tmaj);
    if tn < cnP { return major };
    hd := call intern_const(EREC.u64[ro], ust);
    fab := call mk_app_n(hd, to, cnP);
    scopeOk := call fab_scope_ok(d, fab, major);
    if scopeOk == 0 { return major };
    ioa2 := call infer_io(mode, vis, d, fab);
    defOk := call defeq(mode, vis, d, tmaj, ioa2);
    if defOk == 0 { return major };
    if vck != 0 { irOk := call proof_irrel(mode, vis, d, fab, major) } else { irOk := 1 };
    if irOk != 0 { return fab } else { return major }
  } else {
    if rlEta != 0 {
      ioa := call infer_io(mode, vis, d, major);
      tmaj := call whnf(mode, vis, d, ioa);
      hh2 := call get_app_fn(tmaj);
      if hh2 >> 28 != 3 { return major };
      t2 := (hh2 >> 27) & 1;
      i2 := hh2 & 134217727;
      if t2 != 0 && CTL.u64[1] == 0 { abort };
      if CTL.u64[18 + t2] <= i2 { abort };
      T2 := CREC.u64[i2 * 4 + t2 * 2];
      ust := CREC.u64[i2 * 4 + t2 * 2 + 1];
      (usto, ustl) := call ls_node(ust);
      (to, tn) := call get_app_args(tmaj);
      nz := call caps_never_zero(EREC.u64[indP + 2], EREC.u64[indP + 3], ust,
        EREC.u64[indP + 12], EREC.u64[indP + 13], EREC.u64[indP + 14]);
      if T2 != T { return major };
      if tn != EREC.u64[indP + 7] { return major };
      if ustl != EREC.u64[indP + 3] { return major };
      if nz == 0 { return major };
      resT := call reserved_contains(T);
      if resT != 0 { return major };
      resEC := call reserved_contains(EREC.u64[indP + 6]);
      if resEC != 0 { return major };
      slotsOk := call tower_slots_all(vis, T, EREC.u64[indP + 8]);
      if slotsOk == 0 { return major };
      (fo, fn) := call eta_fab_args(T, to, tn, major, EREC.u64[indP + 8]);
      hd := call intern_const(EREC.u64[indP + 6], ust);
      fab := call mk_app_n(hd, fo, fn);
      scopeOk := call fab_scope_ok(d, fab, major);
      if scopeOk == 0 { return major };
      return fab
    } else {
      an2 := call pin_at(11);
      if T != an2 { return major };
      ioa := call infer_io(mode, vis, d, major);
      tmaj := call whnf(mode, vis, d, ioa);
      hh2 := call get_app_fn(tmaj);
      if hh2 >> 28 != 3 { return major };
      t2 := (hh2 >> 27) & 1;
      i2 := hh2 & 134217727;
      if t2 != 0 && CTL.u64[1] == 0 { abort };
      if CTL.u64[18 + t2] <= i2 { abort };
      T2 := CREC.u64[i2 * 4 + t2 * 2];
      ust := CREC.u64[i2 * 4 + t2 * 2 + 1];
      (usto, ustl) := call ls_node(ust);
      (to, tn) := call get_app_args(tmaj);
      ars := call and_rescue_slots(vis, EREC.u64[ro], cnP, ust);
      if T2 != T { return major };
      if tn != cnP { return major };
      if EREC.u64[cvjP + 3] != ustl { return major };
      if ars == 0 { return major };
      p0 := call mk_proj(T, 0, major);
      p1 := call mk_proj(T, 1, major);
      if len(SPN.u64) <= to + tn { abort };
      SPN.u64[to + tn] := p0;
      if len(SPN.u64) <= to + tn + 1 { abort };
      SPN.u64[to + tn + 1] := p1;
      CTL.u64[136] := to + tn + 2;
      hd := call intern_const(EREC.u64[ro], ust);
      fab := call mk_app_n(hd, to, tn + 2);
      scopeOk := call fab_scope_ok(d, fab, major);
      if scopeOk == 0 { return major };
      ioa2 := call infer_io(mode, vis, d, fab);
      defOk := call defeq(mode, vis, d, tmaj, ioa2);
      if defOk == 0 { return major };
      if vck != 0 { irOk := call proof_irrel(mode, vis, d, fab, major) } else { irOk := 1 };
      if irOk != 0 { return fab } else { return major }
    }
  }
}

/-! ## `prepare_major(mode, vis, d, rec, ro, rc, major)` -/

/-- con-leche: `Core.lean:701-775`/`Cached/CoreC.lean:553-575` `prepareMajor`/`prepareMajorI` — at
a K-flagged recursor the K rescue runs on the raw major; elsewhere the structure rescues run on
the major as found first (a `String` literal skips that attempt), and only if they produce no
constructor is the major head-normalized, its literal converted, and the rescue tried again. -/
-- con-ron: ConRon/Arena/Core.lean:1913-1937 ConRon.Arena.prepareMajor
@[l_impl ConRon.Arena.prepareMajor]
def prepareMajorL : FunDecl := lfn (mode, vis, d, rec, ro, rc, major)
    locals (k, majorK, ok, majorE, major0, major1, res) {
  k := call rec_rule_k(ro, rc);
  if k != 0 {
    majorK := call major_to_ctor(mode, vis, d, rec, ro, rc, major);
    ok := call is_ctor_app(vis, majorK);
    if ok != 0 { res := call lit_major_to_ctor(mode, vis, d, majorK); return res }
    else { return majorK }
  } else {
    ok := call is_str_lit(major);
    if ok != 0 { majorE := major }
    else { majorE := call major_to_ctor(mode, vis, d, rec, ro, rc, major) };
    ok := call is_ctor_app(vis, majorE);
    if ok != 0 { return majorE }
    else {
      major0 := call whnf(mode, vis, d, majorE);
      major1 := call lit_major_to_ctor(mode, vis, d, major0);
      res := call major_to_ctor(mode, vis, d, rec, ro, rc, major1);
      return res
    }
  }
}

/-! ## `pi_residual(e, ao, an)` -/

/-- con-leche: `CoreDefs.lean:716-721` `piResidual` — peel a ∀-telescope along an argument
spine `(ao, an)`. -/
-- con-ron: ConRon/Arena/Core.lean:1326-1337 ConRon.Arena.piResidual
@[l_impl ConRon.Arena.piResidual]
def piResidualL : FunDecl := lfn (e, ao, an) locals (i, t, x, body, b2) {
  i := 0;
  while i < an {
    if e >> 28 != 6 { return (0, 0) };
    t := (e >> 27) & 1;
    x := e & 134217727;
    if t != 0 && CTL.u64[1] == 0 { abort };
    if CTL.u64[30 + t] <= x { abort };
    body := FAREC.u64[x * 4 + t * 2 + 1];
    b2 := call inst_entry(body, SPN.u64[ao + i], 0);
    e := b2;
    i += 1
  };
  return (1, e)
}

/-! ## `defeq_list(mode, vis, d, ao, an, bo, bn)` -/

/-- con-leche: `Core.lean:269-278` `defEqList` — pairwise definitional equality of two spines. -/
-- con-ron: ConRon/Arena/Core.lean:1339-1346 ConRon.Arena.defEqList
@[l_impl ConRon.Arena.defEqList]
def defeqListL : FunDecl := lfn (mode, vis, d, ao, an, bo, bn) locals (i, ok) {
  if an != bn { return 0 };
  i := 0;
  while i < an {
    ok := call defeq(mode, vis, d, SPN.u64[ao + i], SPN.u64[bo + i]);
    if ok == 0 { return 0 };
    i += 1
  };
  return 1
}

/-! ## `iota_index_ok(mode, vis, d, mI, rP, cnP, tyCtor, mo, mn, xo, xn)` -/

/-- con-leche: `Core.lean:280-296` `iotaIndexOk` — the canonical-index comparison of a firing
ι redex. -/
-- con-ron: ConRon/Arena/Core.lean:1348-1358 ConRon.Arena.iotaIndexOk
@[l_impl ConRon.Arena.iotaIndexOk]
def iotaIndexOkL : FunDecl := lfn (mode, vis, d, mI, rP, cnP, tyCtor, mo, mn, xo, xn)
    locals (flag, res, ao2, an2, an3) {
  if mI == rP { return 1 };
  (flag, res) := call pi_residual(tyCtor, mo, mn);
  if flag == 0 { return 0 };
  (ao2, an2) := call get_app_args(res);
  an3 := (an2 - cnP) * u64(cnP <= an2);
  res := call defeq_list(mode, vis, d, ao2 + cnP, an3, xo, xn);
  return res
}

/-! ## `proof_irrel(mode, vis, d, a, b)` -/

/-- con-leche: `Core.lean:298-320` `proofIrrel` — proof irrelevance: both sides' types' sorts are
`Prop`. `lvl_eq`'s result word is `0` none (a decline, `abort`), `1` false, `2` true. -/
-- con-ron: ConRon/Arena/Core.lean:1360-1385 ConRon.Arena.proofIrrel
@[l_impl ConRon.Arena.proofIrrel]
def proofIrrelL : FunDecl := lfn (mode, vis, d, a, b)
    locals (ta, tta, hh, t, i, uT, z, okA, tb, ttb, hh2, t2, i2, vT, okB) {
  ta := call infer_io(mode, vis, d, a);
  tta := call infer_io(mode, vis, d, ta);
  hh := call whnf(mode, vis, d, tta);
  if hh >> 28 != 2 { return 0 };
  t := (hh >> 27) & 1;
  i := hh & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[16 + t] <= i { abort };
  uT := SOREC.u64[i * 2 + t];
  z := call pin_word(53);
  okA := call lvl_eq(uT, z);
  if okA == 0 { abort };
  okA := u64(okA == 2);
  tb := call infer_io(mode, vis, d, b);
  ttb := call infer_io(mode, vis, d, tb);
  hh2 := call whnf(mode, vis, d, ttb);
  if hh2 >> 28 != 2 { return 0 };
  t2 := (hh2 >> 27) & 1;
  i2 := hh2 & 134217727;
  if t2 != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[16 + t2] <= i2 { abort };
  vT := SOREC.u64[i2 * 2 + t2];
  z := call pin_word(53);
  okB := call lvl_eq(vT, z);
  if okB == 0 { abort };
  okB := u64(okB == 2);
  return u64(okA != 0) & u64(okB != 0)
}

/-! ## `rule_rhs_at(rec, ctor, po, pl, rhs, us)`, `const_ty_at(n, po, pl, ty, us)`

Both are thin memo wrappers around `inst_lp` (a `WhnfCallees` stub), over the already-installed
caches `ruleRhsC` (array 104, `rrSch`) and `constTyC` (array 102, `ctSch`): `CoreCaches.lean`,
`CoreRefine.lean`'s `rrKey`/`memoRG_findR`/`memoRG_findP`. -/

/-- con-leche: none — `ruleRhsAt`'s cache probe, `rrSch`'s key `(rec, ctor ||| us << 32)`. -/
-- con-ron: ConRon/Arena/Core.lean:209-224 ConRon.Arena.ruleRhsAt
@[l_impl ConRon.Arena.ruleRhsAt]
def ruleRhsAtL : FunDecl := lfn (rec, ctor, po, pl, rhs, us)
    locals (k2, fd, j, dd, r, dum) {
  k2 := ctor | (us << 32);
  (fd, j, dd) := call rr_find(rec, k2);
  if fd != 0 { return rrSch.arr.u64[j * 4 + 3] };
  r := call inst_lp(po, pl, us, rhs);
  dum := call rr_put(rec, k2, r, fd, j);
  return r
}

/-- con-leche: none — `constTyAt`'s cache probe, `ctSch`'s key `(n, us)`. -/
-- con-ron: ConRon/Arena/Core.lean:178-191 ConRon.Arena.constTyAt
@[l_impl ConRon.Arena.constTyAt]
def constTyAtL : FunDecl := lfn (n, po, pl, ty, us) locals (fd, j, dd, r, dum) {
  (fd, j, dd) := call ct_find(n, us);
  if fd != 0 { return ctSch.arr.u64[j * 4 + 3] };
  r := call inst_lp(po, pl, us, ty);
  dum := call ct_put(n, us, r, fd, j);
  return r
}

/-! ## `rec_fire_args(…)`: `instSpine`, `inst_spine_pins`, `rec_fire_args` -/

/-- con-leche: `ExprOps.lean:1305-1313` `instSpine` — instantiate a telescope-context expression
at an argument spine `(ao, an)`, the fuel-like index `t` decreasing by one per argument. -/
-- con-ron: ConRon/Arena/ExprOps.lean:1379-1385 ConRon.Arena.instSpine
@[l_impl ConRon.Arena.instSpine]
def instSpineL : FunDecl := lfn (ao, an, t, e) locals (i) {
  i := 0;
  while i < an {
    e := call inst_entry(e, SPN.u64[ao + i], t);
    t := t - 1;
    i += 1
  };
  return e
}

/-- con-leche: `CoreDefs.lean:908-927` `recFireComparands` (the nested rule's stored parameter
pins, `instSpinePins`) — each pin level-instantiated (`inst_lp`) then spined over the leading
`rP` arguments (`inst_spine`), pushed in order. -/
-- con-ron: ConRon/Arena/Core.lean:1963-1973 ConRon.Arena.instSpinePins
@[l_impl ConRon.Arena.instSpinePins]
def instSpinePinsL : FunDecl := lfn (po, pl, us, ao, rP, pvo, pvc) locals (so, j, q, s) {
  so := CTL.u64[136];
  if len(SPN.u64) < so { abort };
  if len(SPN.u64) - so < pvc { abort };
  j := 0;
  while j < pvc {
    q := call inst_lp(po, pl, us, SPN.u64[pvo + j]);
    s := call inst_spine(ao, rP, rP - 1, q);
    SPN.u64[so + j] := s;
    j += 1
  };
  CTL.u64[136] := so + pvc;
  return (so, pvc)
}

/-- con-leche: `CoreDefs.lean:908-927` `recFireComparands` (its `.2`) — the constructor-PARAMETER
comparands of a firing rule: a `.nested` rule's stored pins, instantiated and spined; a `.plain`
rule's the recursor's own leading `ctorParams` arguments. -/
-- con-ron: ConRon/Arena/Core.lean:1995-2003 ConRon.Arena.recFireArgs
@[l_impl ConRon.Arena.recFireArgs]
def recFireArgsL : FunDecl := lfn (fireKind, pvo, pvc, po, pc, us, ao, rP, ctorParams)
    locals (so, sc) {
  if fireKind == 1 {
    (so, sc) := call inst_spine_pins(po, pc, us, ao, rP, pvo, pvc);
    return (so, sc)
  };
  return (ao, ctorParams)
}

/-! ## `iota_certs_full(mode, vis, d, h, ao, an)` -/

/-- con-leche: `Kernel/Core.lean:252-267`/`Cached/CoreC.lean:149-181` `iotaCertsFullAux`/
`iotaCertsFull`/`iotaCertsFullI` — certify a spine against a constructor telescope: every
argument's FULL-grade inferred type is defeq to the corresponding (instantiated) domain, the
pending substitutions carried in an accumulator opened in one `instantiateList`. The accumulator
is the stack slice `(aco, acn)`, pushed directly above the fixed spine `(ao, an)`; nothing
intervenes between a growth and the next read, so it stays contiguous. -/
-- con-ron: ConRon/Arena/Core.lean:1285-1317 ConRon.Arena.iotaCertsFullAux
@[l_impl ConRon.Arena.iotaCertsFullAux]
def iotaCertsFullAuxL : FunDecl := lfn (mode, vis, d, h, aco, acn, ao, an, i)
    locals (t, x, ty, body, arg, ty2, ta, ok, top, dum) {
  if i < an {
    if h >> 28 == 6 {
      t := (h >> 27) & 1;
      x := h & 134217727;
      if t != 0 && CTL.u64[1] == 0 { abort };
      if CTL.u64[30 + t] <= x { abort };
      ty := FAREC.u64[x * 4 + t * 2];
      body := FAREC.u64[x * 4 + t * 2 + 1];
      arg := SPN.u64[ao + i];
      ty2 := call inst_list(ty, aco, acn, 0);
      ta := call infer(mode, vis, d, arg);
      ok := call defeq(mode, vis, d, ta, ty2);
      if ok == 0 { return 0 };
      if len(SPN.u64) <= aco + acn { abort };
      SPN.u64[aco + acn] := arg;
      CTL.u64[136] := aco + acn + 1;
      acn := acn + 1;
      dum := call iota_certs_full_aux(mode, vis, d, body, aco, acn, ao, an, i + 1);
      return dum
    };
    if h >> 28 == 0 {
      if acn == 0 { return 0 };
      ty2 := call inst_list(h, aco, acn, 0);
      top := aco + acn;
      dum := call iota_certs_full_aux(mode, vis, d, ty2, top, 0, ao, an, i);
      return dum
    };
    return 0
  };
  return 1
}

/-- con-leche: `Kernel/Core.lean:252-267`/`Cached/CoreC.lean:178-181` `iotaCertsFull`/
`iotaCertsFullI` — the empty-accumulator entry. -/
-- con-ron: ConRon/Arena/Core.lean:1319-1324 ConRon.Arena.iotaCertsFull
@[l_impl ConRon.Arena.iotaCertsFull]
def iotaCertsFullL : FunDecl := lfn (mode, vis, d, h, ao, an) locals (top, res) {
  top := CTL.u64[136];
  res := call iota_certs_full_aux(mode, vis, d, h, top, 0, ao, an, 0);
  return res
}

/-! ## `iota_rec_at(mode, vis, d, hd, so, sn)` -/

/-- con-leche: `Core.lean:777-876` `iotaRec`/`iotaRecAt` — one ι step at a spine the caller
already holds: `hd` the head, `(so, sn)` the stack slice of arguments, `sn` the spine's length
(`whnfApp`'s only call site passes `va.size` for both `n` and the slice length). -/
-- con-ron: ConRon/Arena/Core.lean:2012-2097 ConRon.Arena.iotaRecAt
@[l_impl ConRon.Arena.iotaRecAt]
def iotaRecAtL : FunDecl := lfn (mode, vis, d, hd, so, sn)
    locals (t, i, c, flag, recP, mI, rP, ro, rc, uso, usl, peelFlag, peelRes,
            b0, major, hh, t2, i2, cj, ctorFlag, ctorP, rflag, rl, margs, margCnt,
            fam, usj2, t3, vck, cmpL, lok, cmpAo, cmpAc, deqOk, tyC, certOk, idxOk,
            rhs, xo, xn, x) {
  if hd >> 28 != 3 { return (0, 0) };
  t := (hd >> 27) & 1;
  i := hd & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[18 + t] <= i { abort };
  c := CREC.u64[i * 4 + t * 2];
  usj2 := CREC.u64[i * 4 + t * 2 + 1];
  (flag, recP) := call env_find(c, vis);
  if flag == 0 { return (0, 0) };
  if EREC.u64[recP] != 5 { return (0, 0) };
  mI := EREC.u64[recP + 5];
  rP := EREC.u64[recP + 6];
  ro := EREC.u64[recP + 7];
  rc := EREC.u64[recP + 8];
  if sn != mI + 1 { return (0, 0) };
  (uso, usl) := call ls_node(usj2);
  if usl != EREC.u64[recP + 3] { return (0, 0) };
  (peelFlag, peelRes) := call peel_pis(mI + 1, EREC.u64[recP + 4]);
  if peelFlag == 0 { return (0, 0) };
  b0 := call intern_bvar(0);
  if mI < sn { major := SPN.u64[so + mI] } else { major := b0 };
  major := call prepare_major(mode, vis, d, c, ro, rc, major);
  hh := call get_app_fn(major);
  if hh >> 28 != 3 { return (0, 0) };
  t2 := (hh >> 27) & 1;
  i2 := hh & 134217727;
  if t2 != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[18 + t2] <= i2 { abort };
  cj := CREC.u64[i2 * 4 + t2 * 2];
  (ctorFlag, ctorP) := call env_find(cj, vis);
  if ctorFlag == 0 { return (0, 0) };
  if EREC.u64[ctorP] != 4 { return (0, 0) };
  (rflag, rl) := call find_rule(ro, rc, cj);
  if rflag == 0 { return (0, 0) };
  (margs, margCnt) := call get_app_args(major);
  if margCnt != EREC.u64[rl + 2] + EREC.u64[rl + 1] { return (0, 0) };
  vck := u64(mode & 1 == 0);
  if vck != 0 {
    cmpL := call rec_fire_levels(EREC.u64[rl + 3], EREC.u64[rl + 4], EREC.u64[rl + 5],
      EREC.u64[recP + 2], EREC.u64[recP + 3], usj2, EREC.u64[ctorP + 2], EREC.u64[ctorP + 3]);
    fam := call iota_case3(EREC.u64[rl + 9], vis, ctorP, cmpL);
    if fam != 0 {
      t3 := CREC.u64[i2 * 4 + t2 * 2 + 1];
      lok := call lvls_eq(t3, cmpL);
      if lok == 0 { abort };
      if lok == 2 {
        (cmpAo, cmpAc) := call rec_fire_args(EREC.u64[rl + 3], EREC.u64[rl + 6], EREC.u64[rl + 7],
          EREC.u64[recP + 2], EREC.u64[recP + 3], usj2, so, rP, EREC.u64[rl + 2]);
        deqOk := call defeq_list(mode, vis, d, margs, EREC.u64[rl + 2], cmpAo, cmpAc);
        if deqOk != 0 {
          tyC := call const_ty_at(cj, EREC.u64[ctorP + 2], EREC.u64[ctorP + 3],
            EREC.u64[ctorP + 4], t3);
          certOk := call iota_certs_full(mode, vis, d, tyC, margs, margCnt);
          if certOk != 0 {
            idxOk := call iota_index_ok(mode, vis, d, mI, rP, EREC.u64[rl + 2], tyC,
              margs, margCnt, so + rP, (mI - rP) * u64(rP <= mI));
            fam := idxOk
          } else { fam := 0 }
        } else { fam := 0 }
      } else { fam := 0 }
    } else { fam := 1 }
  } else {
    fam := 1
  };
  if fam == 0 { return (0, 0) };
  rhs := call rule_rhs_at(c, cj, EREC.u64[recP + 2], EREC.u64[recP + 3], EREC.u64[rl + 8], usj2);
  if len(SPN.u64) < so + rP { abort };
  xo := so;
  xn := rP;
  x := call mk_app_n(rhs, xo, xn);
  x := call mk_app_n_from(x, margs, margCnt, EREC.u64[rl + 2]);
  return (1, x)
}

/-! ## The program -/

/-- The functions this file provides (not the named stubs: `inst_entry` is `Inst1Spec.lean`'s,
`caps_never_zero`/`find_proj`/`fire_ok`/`rec_fire_levels`/`wscoped_bfast`/
`loose_bvars_bounded_fast`/`leaf_guard`/`lit_to_ctor_if_nat` have none yet). -/
def iotaProg : Prog :=
  [("is_ctor_app", isCtorAppL), ("is_str_lit", isStrLitL), ("find_rule", findRuleL),
   ("rec_rule_k", recRuleKL), ("reserved_contains", reservedContainsL),
   ("iota_ctor_never_prop", iotaCtorNeverPropL), ("iota_case3", iotaCase3L),
   ("tower_slots_all", towerSlotsAllL), ("eta_projs", etaProjsL),
   ("eta_fab_args", etaFabArgsL), ("and_rescue_slots", andRescueSlotsL),
   ("fab_scope_ok", fabScopeOkL), ("lit_major_to_ctor", litMajorToCtorL),
   ("major_to_ctor", majorToCtorL), ("prepare_major", prepareMajorL),
   ("pi_residual", piResidualL), ("defeq_list", defeqListL), ("iota_index_ok", iotaIndexOkL),
   ("proof_irrel", proofIrrelL), ("rule_rhs_at", ruleRhsAtL), ("const_ty_at", constTyAtL),
   ("inst_spine", instSpineL), ("inst_spine_pins", instSpinePinsL),
   ("rec_fire_args", recFireArgsL), ("iota_certs_full_aux", iotaCertsFullAuxL),
   ("iota_certs_full", iotaCertsFullL), ("iota_rec_at", iotaRecAtL)]

/-- What this file's specs need of a program: its own functions, at their names. -/
structure IotaProg (p : Prog) : Prop where
  isCtorApp : p.lookup "is_ctor_app" = some isCtorAppL
  isStrLit : p.lookup "is_str_lit" = some isStrLitL
  findRule : p.lookup "find_rule" = some findRuleL
  recRuleK : p.lookup "rec_rule_k" = some recRuleKL
  reservedContains : p.lookup "reserved_contains" = some reservedContainsL
  iotaCtorNeverProp : p.lookup "iota_ctor_never_prop" = some iotaCtorNeverPropL
  iotaCase3 : p.lookup "iota_case3" = some iotaCase3L
  towerSlotsAll : p.lookup "tower_slots_all" = some towerSlotsAllL
  etaProjs : p.lookup "eta_projs" = some etaProjsL
  etaFabArgs : p.lookup "eta_fab_args" = some etaFabArgsL
  andRescueSlots : p.lookup "and_rescue_slots" = some andRescueSlotsL
  fabScopeOk : p.lookup "fab_scope_ok" = some fabScopeOkL
  litMajorToCtor : p.lookup "lit_major_to_ctor" = some litMajorToCtorL
  majorToCtor : p.lookup "major_to_ctor" = some majorToCtorL
  prepareMajor : p.lookup "prepare_major" = some prepareMajorL
  piResidual : p.lookup "pi_residual" = some piResidualL
  defeqList : p.lookup "defeq_list" = some defeqListL
  iotaIndexOk : p.lookup "iota_index_ok" = some iotaIndexOkL
  proofIrrel : p.lookup "proof_irrel" = some proofIrrelL
  ruleRhsAt : p.lookup "rule_rhs_at" = some ruleRhsAtL
  constTyAt : p.lookup "const_ty_at" = some constTyAtL
  instSpine : p.lookup "inst_spine" = some instSpineL
  instSpinePins : p.lookup "inst_spine_pins" = some instSpinePinsL
  recFireArgs : p.lookup "rec_fire_args" = some recFireArgsL
  iotaCertsFullAux : p.lookup "iota_certs_full_aux" = some iotaCertsFullAuxL
  iotaCertsFull : p.lookup "iota_certs_full" = some iotaCertsFullL
  iotaRecAt : p.lookup "iota_rec_at" = some iotaRecAtL

/-! ## The stub callees -/

/-- A level-list handle result (`LsIdx`): the word, decoded. -/
def decLs (r : List Word) : LsIdx := decI (r.headD 0)

/-- `inst_entry(e, v, d)` refines `instantiate1Fast coreWalkFuel e v d` exactly: `Inst1Spec.lean`'s
`instEntry_refines` is generic over any twin fuel `F ≥ n`; this pins `F := coreWalkFuel`. Named to
avoid a clash with lane `whnf`'s own `Inst1OK` (its `whnfCore`'s ζ step). -/
def IotaInst1OK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb e v d : Word), CoreS dn s₀.mem a₀ vis fe MM eb → HW e →
    CoreSpec p n "inst_entry" [e, v, d]
      (instantiate1Fast coreWalkFuel (decE e) (decE v) d.toNat) decH s₀ a₀ dn vis fe MM eb

/-- `caps_never_zero(po, pc, us, swd, so, sc)` refines `(Level.substPW ks vs pw).isNever` at the
`EREC` name slice `(po, pc)` (read back to `ks`), the level-list handle `us` (read back to `vs`),
and the `PropWhen` datum `(swd, so, sc)` (`swd = 0` `.never`, `1` `.ifAllZero` with the `EREC` name
slice `(so, sc)` read back): see the module note on why this is a stub rather than a real
`lv_substpw` wiring. -/
def CapsNeverZeroOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb po pc us swd so sc : Word) (ks : List ConLeche.Name)
    (vs : List ConLeche.Level) (pw : ConLeche.PropWhen), CoreS dn s₀.mem a₀ vis fe MM eb →
    CoreSpec p n "caps_never_zero" [po, pc, us, swd, so, sc]
      (pure (ConLeche.Level.substPW ks vs pw).isNever : AM Bool) decBool s₀ a₀ dn vis fe MM eb

/-- `rec_fire_levels(fireKind, fvo, fvc, po, pc, us, qo, qc)` refines `recFireLevels rl lps us
cvjLps` (`rl.fire` decoded from `(fireKind, fvo, fvc)`, `lps` the `EREC` slice `(po, pc)`, `cvjLps`
the `EREC` slice `(qo, qc)`): a stub, see the module note. -/
def RecFireLevelsOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb fireKind fvo fvc po pc us qo qc : Word) (rl : IRecRule) (lps cvjLps : List NIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb →
    CoreSpec p n "rec_fire_levels" [fireKind, fvo, fvc, po, pc, us, qo, qc]
      (recFireLevels rl lps (decI us) cvjLps) decLs s₀ a₀ dn vis fe MM eb

/-- `wscoped_bfast(d, e)` refines `wscopedBFast coreWalkFuel d.toNat e` (a phase-4 walk stub). -/
def WscopedBFastOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb d e : Word), CoreS dn s₀.mem a₀ vis fe MM eb → HW e →
    CoreSpec p n "wscoped_bfast" [d, e] (wscopedBFast coreWalkFuel d.toNat (decE e)) decBool s₀ a₀
      dn vis fe MM eb

/-- `loose_bvars_bounded_fast(c, e)` refines `looseBVarsBoundedFast coreWalkFuel c.toNat e` (a
phase-4 walk stub). -/
def LooseBVarsBoundedFastOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb c e : Word), CoreS dn s₀.mem a₀ vis fe MM eb → HW e →
    CoreSpec p n "loose_bvars_bounded_fast" [c, e]
      (looseBVarsBoundedFast coreWalkFuel c.toNat (decE e)) decBool s₀ a₀ dn vis fe MM eb

/-- `leaf_guard(fab, major)` refines `leafGuard coreWalkFuel fab major` (a phase-4 walk stub). -/
def LeafGuardOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb fab major : Word), CoreS dn s₀.mem a₀ vis fe MM eb → HW fab → HW major →
    CoreSpec p n "leaf_guard" [fab, major] (leafGuard coreWalkFuel (decE fab) (decE major)) decBool
      s₀ a₀ dn vis fe MM eb

/-- `lit_to_ctor_if_nat(vis, h)` refines `litToCtorIfNat fe h`: another agent's L function
(`WhnfDelta.lean`), not written yet. -/
def LitToCtorIfNatOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb h : Word), CoreS dn s₀.mem a₀ vis fe MM eb → HW h →
    CoreSpec p n "lit_to_ctor_if_nat" [vis, h] (litToCtorIfNat fe (decE h)) decH s₀ a₀ dn vis fe MM
      eb

/-- **This file's stub callees.** -/
structure IotaCallees (p : Prog) : Prop where
  inst1 : IotaInst1OK p
  findProj : FindProjOK p
  fireOk : FireOkOK p
  capsNeverZero : CapsNeverZeroOK p
  recFireLevels : RecFireLevelsOK p
  wscopedBFast : WscopedBFastOK p
  looseBVarsBoundedFast : LooseBVarsBoundedFastOK p
  leafGuard : LeafGuardOK p
  litToCtorIfNat : LitToCtorIfNatOK p

/-- **The stubs' specs, assumed** until their L code lands. -/
theorem iotaCallees_stub (p : Prog) : IotaCallees p := sorry

/-! ## The statements (`CoreSpec` shape; all `sorry` for now)

A knot-calling function quantifies over the knot fuel `F` (`n ≤ F`) and takes `KnotUpTo p n` for the
slots one level down, stating its own `CoreSpec` at L-fuel `n + 1`; the rest need only `CoreS`.
`eta_projs`/`eta_fab_args`/`inst_spine_pins`/`rec_fire_args` return a `List EIdx`, whose decoder
needs the resulting memory (`SpineR`), so they are stated directly rather than through `CoreSpec`'s
`dec : List Word → α`, exactly as `WhnfSpine.lean`'s slice-returning specs are. -/

section specs
variable (p : Prog) (hp : IotaProg p) (hw : WhnfCallees p) (hc : IotaCallees p)

/-- con-leche: `CoreDefs.lean:51-58` `isCtorApp`. -/
def IsCtorAppOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb e : Word), CoreS dn s₀.mem a₀ vis fe MM eb → HW e →
    CoreSpec p n "is_ctor_app" [vis, e] (isCtorApp fe (decE e)) decBool s₀ a₀ dn vis fe MM eb

@[refines ConRon.Arena.isCtorApp]
theorem isCtorApp_refines : IsCtorAppOK p := sorry

/-- con-leche: `Core.lean:695-699` `isStrLit`. -/
def IsStrLitOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb h : Word), CoreS dn s₀.mem a₀ vis fe MM eb → HW h →
    CoreSpec p n "is_str_lit" [h] (isStrLit (decE h)) decBool s₀ a₀ dn vis fe MM eb

/-- con-leche: `CoreDefs.lean:72-93` `iotaCtorNeverProp`. -/
def IotaCtorNeverPropOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb ctorP us : Word) (cvj : IConstantVal) (cnP cnF : Nat),
    CoreS dn s₀.mem a₀ vis fe MM eb → HW us →
    decCI (s₀.mem.arr64 EREC) dn ctorP.toNat = some (.ctorInfo cvj cnP cnF) →
    CoreSpec p n "iota_ctor_never_prop" [vis, ctorP, us] (iotaCtorNeverProp fe cvj (decI us)) decBool
      s₀ a₀ dn vis fe MM eb

@[refines ConRon.Arena.iotaCtorNeverProp]
theorem iotaCtorNeverProp_refines : IotaCtorNeverPropOK p := sorry

/-- con-leche: `CoreDefs.lean:95-104` `iotaCase3`. -/
def IotaCase3OK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb rlk ctorP us : Word) (rl : IRecRule) (cvj : IConstantVal) (cnP cnF : Nat),
    CoreS dn s₀.mem a₀ vis fe MM eb → HW us → rl.k = (rlk != 0) →
    decCI (s₀.mem.arr64 EREC) dn ctorP.toNat = some (.ctorInfo cvj cnP cnF) →
    CoreSpec p n "iota_case3" [rlk, vis, ctorP, us] (iotaCase3 fe rl cvj (decI us)) decBool s₀ a₀ dn
      vis fe MM eb

@[refines ConRon.Arena.iotaCase3]
theorem iotaCase3_refines : IotaCase3OK p := sorry

/-- con-leche: `CoreDefs.lean:723-728`/`FEnv.lean:195-197` `towerSlotsAll`. -/
def TowerSlotsAllOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb T nF : Word), CoreS dn s₀.mem a₀ vis fe MM eb → HW T →
    CoreSpec p n "tower_slots_all" [vis, T, nF] (towerSlotsAll fe (decI T) nF.toNat) decBool s₀ a₀
      dn vis fe MM eb

@[refines ConRon.Arena.towerSlotsAll]
theorem towerSlotsAll_refines : TowerSlotsAllOK p := sorry

/-- con-leche: `CoreDefs.lean:730-735`/`Cached/CoreC.lean:310-317` `etaProjs`. -/
def EtaProjsOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb T b nF : Word), CoreS dn s₀.mem a₀ vis fe MM eb → HW T → HW b →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "eta_projs" [T, b, nF]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (etaProjs (decI T) (decE b) nF.toNat) a₀ ∧
      CoreAfter dn s₀.mem s'.mem (AM.st (etaProjs (decI T) (decE b) nF.toNat) a₀) vis fe MM eb ∧
      ∃ xs, AM.res (etaProjs (decI T) (decE b) nF.toNat) a₀ = xs ∧
        SpineR s'.mem (r.headD 0) (r.tail.headD 0) xs.toArray; ⊤⦄

@[refines ConRon.Arena.etaProjs]
theorem etaProjs_refines : EtaProjsOK p := sorry

/-- con-leche: `CoreDefs.lean:750-754` `etaFabArgsE`. -/
def EtaFabArgsOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb T to tn major nF : Word) (targs : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → HW T → HW major → SpineR s₀.mem to tn targs →
    to + tn = spTop s₀.mem →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "eta_fab_args" [T, to, tn, major, nF]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (etaFabArgsE (decI T) targs.toList (decE major) nF.toNat) a₀ ∧
      CoreAfter dn s₀.mem s'.mem (AM.st (etaFabArgsE (decI T) targs.toList (decE major) nF.toNat) a₀)
        vis fe MM eb ∧
      ∃ xs, AM.res (etaFabArgsE (decI T) targs.toList (decE major) nF.toNat) a₀ = xs ∧
        SpineR s'.mem (r.headD 0) (r.tail.headD 0) xs.toArray; ⊤⦄

@[refines ConRon.Arena.etaFabArgsE]
theorem etaFabArgs_refines : EtaFabArgsOK p := sorry

/-- con-leche: `CoreDefs.lean:793-806`/`:808-810`/`FEnv.lean:199-201` `andRescueSlots`. -/
def AndRescueSlotsOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb ctor nP us : Word), CoreS dn s₀.mem a₀ vis fe MM eb → HW ctor → HW us →
    CoreSpec p n "and_rescue_slots" [vis, ctor, nP, us]
      (andRescueSlots fe (decI ctor) nP.toNat (decI us)) decBool s₀ a₀ dn vis fe MM eb

@[refines ConRon.Arena.andRescueSlots]
theorem andRescueSlots_refines : AndRescueSlotsOK p := sorry

/-- con-leche: `Core.lean:502-663` (the shared scope guard) `fabScopeOk`. -/
def FabScopeOkOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb d fab major : Word), CoreS dn s₀.mem a₀ vis fe MM eb → HW fab → HW major →
    CoreSpec p n "fab_scope_ok" [d, fab, major] (fabScopeOk d.toNat (decE fab) (decE major)) decBool
      s₀ a₀ dn vis fe MM eb

@[refines ConRon.Arena.fabScopeOk]
theorem fabScopeOk_refines : FabScopeOkOK p := sorry

/-- con-leche: `Core.lean:665-677` `litMajorToCtor`. -/
def LitMajorToCtorOK (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d h : Word), CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → HW h →
    CoreSpec p (n + 1) "lit_major_to_ctor" [mode, vis, d, h]
      (litMajorToCtor (coreKnot (decMode mode) fe id F) fe d.toNat (decE h)) decH s₀ a₀ dn vis fe MM
      eb

@[refines ConRon.Arena.litMajorToCtor]
theorem litMajorToCtor_refines : LitMajorToCtorOK p := sorry

/-- con-leche: `Core.lean:502-663`/`Cached/CoreC.lean:428-453` `majorToCtor`. -/
def MajorToCtorOK (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d rec ro rc major : Word) (rules : List IRecRule),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → HW major →
    decRules (s₀.mem.arr64 EREC) ro.toNat rc.toNat = some rules →
    CoreSpec p (n + 1) "major_to_ctor" [mode, vis, d, rec, ro, rc, major]
      (majorToCtor (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI rec) rules
        (decE major)) decH s₀ a₀ dn vis fe MM eb

@[refines ConRon.Arena.majorToCtor]
theorem majorToCtor_refines : MajorToCtorOK p := sorry

/-- con-leche: `Core.lean:701-775`/`Cached/CoreC.lean:553-575` `prepareMajor`. -/
def PrepareMajorOK (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d rec ro rc major : Word) (rules : List IRecRule),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → HW major →
    decRules (s₀.mem.arr64 EREC) ro.toNat rc.toNat = some rules →
    CoreSpec p (n + 1) "prepare_major" [mode, vis, d, rec, ro, rc, major]
      (prepareMajor (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI rec) rules
        (decE major)) decH s₀ a₀ dn vis fe MM eb

@[refines ConRon.Arena.prepareMajor]
theorem prepareMajor_refines : PrepareMajorOK p := sorry

/-- con-leche: `CoreDefs.lean:716-721` `piResidual`. -/
def PiResidualOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb e ao an : Word) (args : Array EIdx), CoreS dn s₀.mem a₀ vis fe MM eb →
    HW e → SpineR s₀.mem ao an args →
    CoreSpec p n "pi_residual" [e, ao, an] (piResidual (decE e) args.toList) decOptR s₀ a₀ dn vis fe
      MM eb

/-- con-leche: `Core.lean:269-278` `defEqList`. -/
def DefeqListOK (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d ao an bo bn : Word) (aas bs : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → SpineR s₀.mem ao an aas → SpineR s₀.mem bo bn bs →
    CoreSpec p (n + 1) "defeq_list" [mode, vis, d, ao, an, bo, bn]
      (defEqList (coreKnot (decMode mode) fe id F) fe d.toNat aas.toList bs.toList) decBool s₀ a₀ dn
      vis fe MM eb

/-- con-leche: `Core.lean:280-296` `iotaIndexOk`. -/
def IotaIndexOkOK (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d mI rP cnP tyCtor mo mn xo xn : Word) (margs idx : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → HW tyCtor → SpineR s₀.mem mo mn margs →
    SpineR s₀.mem xo xn idx →
    CoreSpec p (n + 1) "iota_index_ok" [mode, vis, d, mI, rP, cnP, tyCtor, mo, mn, xo, xn]
      (iotaIndexOk (coreKnot (decMode mode) fe id F) fe d.toNat mI.toNat rP.toNat cnP.toNat
        (decE tyCtor) margs.toList idx.toList) decBool s₀ a₀ dn vis fe MM eb

@[refines ConRon.Arena.iotaIndexOk]
theorem iotaIndexOk_refines : IotaIndexOkOK p := sorry

/-- con-leche: `Core.lean:298-320` `proofIrrel`. -/
def ProofIrrelOK (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d a b : Word), CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → HW a →
    HW b →
    CoreSpec p (n + 1) "proof_irrel" [mode, vis, d, a, b]
      (proofIrrel (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) decBool s₀ a₀ dn
      vis fe MM eb

@[refines ConRon.Arena.proofIrrel]
theorem proofIrrel_refines : ProofIrrelOK p := sorry

/-- con-leche: none (`ruleRhsAt`'s cache probe). -/
def RuleRhsAtOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb rec ctor po pl rhs us : Word) (lps : List NIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → HW rec → HW ctor → HW rhs → HW us →
    hslice? (s₀.mem.arr64 EREC) po.toNat pl.toNat = some lps →
    CoreSpec p n "rule_rhs_at" [rec, ctor, po, pl, rhs, us]
      (ruleRhsAt (decI rec) (decI ctor) lps (decE rhs) (decI us)) decH s₀ a₀ dn vis fe MM eb

@[refines ConRon.Arena.ruleRhsAt]
theorem ruleRhsAt_refines : RuleRhsAtOK p := sorry

/-- con-leche: none (`constTyAt`'s cache probe). -/
def ConstTyAtOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb nn po pl ty us : Word) (lps : List NIdx), CoreS dn s₀.mem a₀ vis fe MM eb →
    HW nn → HW ty → HW us → hslice? (s₀.mem.arr64 EREC) po.toNat pl.toNat = some lps →
    CoreSpec p n "const_ty_at" [nn, po, pl, ty, us]
      (constTyAt ⟨decI nn, lps, decE ty⟩ (decI us)) decH s₀ a₀ dn vis fe MM eb

@[refines ConRon.Arena.constTyAt]
theorem constTyAt_refines : ConstTyAtOK p := sorry

/-- con-leche: `ExprOps.lean:1305-1313` `instSpine`. -/
def InstSpineOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb ao an t e : Word) (args : Array EIdx), CoreS dn s₀.mem a₀ vis fe MM eb →
    HW e → SpineR s₀.mem ao an args →
    CoreSpec p n "inst_spine" [ao, an, t, e] (instSpine coreWalkFuel args.toList t.toNat (decE e))
      decH s₀ a₀ dn vis fe MM eb

@[refines ConRon.Arena.instSpine]
theorem instSpine_refines : InstSpineOK p := sorry

/-- con-leche: `CoreDefs.lean:908-927` `instSpinePins`. -/
def InstSpinePinsOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb po pl us ao rP pvo pvc : Word) (lps : List NIdx) (args pins : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → HW us →
    hslice? (s₀.mem.arr64 EREC) po.toNat pl.toNat = some lps → SpineR s₀.mem ao rP args →
    SpineR s₀.mem pvo pvc pins →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "inst_spine_pins" [po, pl, us, ao, rP, pvo, pvc]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (instSpinePins lps (decI us) args.toList rP.toNat pins.toList) a₀ ∧
      CoreAfter dn s₀.mem s'.mem
        (AM.st (instSpinePins lps (decI us) args.toList rP.toNat pins.toList) a₀) vis fe MM eb ∧
      ∃ xs, AM.res (instSpinePins lps (decI us) args.toList rP.toNat pins.toList) a₀ = xs ∧
        SpineR s'.mem (r.headD 0) (r.tail.headD 0) xs.toArray; ⊤⦄

@[refines ConRon.Arena.instSpinePins]
theorem instSpinePins_refines : InstSpinePinsOK p := sorry

/-- con-leche: `CoreDefs.lean:908-927` `recFireComparands` (its `.2`, `recFireArgs`). -/
def RecFireArgsOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb fireKind pvo pvc po pc us ao rP ctorParams : Word) (rl : IRecRule)
    (lps : List NIdx) (args : Array EIdx), CoreS dn s₀.mem a₀ vis fe MM eb → HW us →
    hslice? (s₀.mem.arr64 EREC) po.toNat pc.toNat = some lps → SpineR s₀.mem ao rP args →
    (fireKind = 1 → ∃ lvls pins, rl.fire = .nested lvls pins ∧ SpineR s₀.mem pvo pvc pins.toArray) →
    (fireKind ≠ 1 → rl.fire = .plain) → rl.ctorParams = ctorParams.toNat →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "rec_fire_args" [fireKind, pvo, pvc, po, pc, us, ao, rP, ctorParams]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (recFireArgs rl lps (decI us) args.toList rP.toNat) a₀ ∧
      CoreAfter dn s₀.mem s'.mem (AM.st (recFireArgs rl lps (decI us) args.toList rP.toNat) a₀) vis
        fe MM eb ∧
      ∃ xs, AM.res (recFireArgs rl lps (decI us) args.toList rP.toNat) a₀ = xs ∧
        SpineR s'.mem (r.headD 0) (r.tail.headD 0) xs.toArray; ⊤⦄

@[refines ConRon.Arena.recFireArgs]
theorem recFireArgs_refines : RecFireArgsOK p := sorry

/-- con-leche: `ConLeche/Cached/CoreC.lean:149-176` `iotaCertsFullAux`. -/
def IotaCertsFullAuxOK (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d h aco acn ao an i : Word) (acc args : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → HW h → SpineR s₀.mem aco acn acc →
    SpineR s₀.mem ao an args → aco + acn = spTop s₀.mem →
    CoreSpec p (n + 1) "iota_certs_full_aux" [mode, vis, d, h, aco, acn, ao, an, i]
      (iotaCertsFullAux (coreKnot (decMode mode) fe id F) fe d.toNat (decE h) acc args i.toNat)
      decBool s₀ a₀ dn vis fe MM eb

@[refines ConRon.Arena.iotaCertsFullAux]
theorem iotaCertsFullAux_refines : IotaCertsFullAuxOK p := sorry

/-- con-leche: `Kernel/Core.lean:252-267`/`Cached/CoreC.lean:178-181` `iotaCertsFull`. -/
def IotaCertsFullOK (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d h ao an : Word) (args : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → HW h → SpineR s₀.mem ao an args →
    ao + an = spTop s₀.mem →
    CoreSpec p (n + 1) "iota_certs_full" [mode, vis, d, h, ao, an]
      (iotaCertsFull (coreKnot (decMode mode) fe id F) fe d.toNat (decE h) args.toList) decBool s₀
      a₀ dn vis fe MM eb

@[refines ConRon.Arena.iotaCertsFull]
theorem iotaCertsFull_refines : IotaCertsFullOK p := sorry

/-- **`iota_rec_at` refines `iotaRecAt`** (the statement is `WhnfCore.lean`'s `IotaRecAtOK`, what
`whnf_app` assumes). -/
@[refines ConRon.Arena.iotaRecAt]
theorem iotaRecAt_refines (n : Nat) (hk : KnotUpTo p n) : IotaRecAtOK p (n + 1) := sorry

end specs

/-! ## Leaf proofs: `find_rule`, `rec_rule_k`, `is_str_lit`, `defeq_list`, `pi_residual`

Pure/read-only, over `EREC` alone (no `CoreS` needed): `find_rule`, `rec_rule_k`. -/

/-- The rule record at `q` decodes, or `f = 0` and there is none: `find_rule`'s result. -/
def decRuleAt (m : Mem) (f q : Word) : Option IRecRule :=
  if f = 0 then none else decRule (m.arr64 EREC) q.toNat

/-- **`find_rule` refines `findRule`.** -/
@[refines ConRon.Arena.findRule]
theorem findRule_refines (p : Prog) (hp : p.lookup "find_rule" = some findRuleL) (n : Nat)
    (s₀ : St) (ro rc c : Word) (rules : List IRecRule)
    (hr : decRules (s₀.mem.arr64 EREC) ro.toNat rc.toNat = some rules) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "find_rule" [ro, rc, c]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧
      findRule rules (decI c) = decRuleAt s₀.mem (r.headD 0) (r.tail.headD 0); ⊤⦄ := sorry

/-- **`rec_rule_k` refines `recRuleK`.** -/
@[refines ConRon.Arena.recRuleK]
theorem recRuleK_refines (p : Prog) (hp : p.lookup "rec_rule_k" = some recRuleKL) (n : Nat)
    (s₀ : St) (ro rc : Word) (rules : List IRecRule)
    (hr : decRules (s₀.mem.arr64 EREC) ro.toNat rc.toNat = some rules) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "rec_rule_k" [ro, rc]
    ⦃fun r s' => s'.mem = s₀.mem ∧ LocEq s' s₀ ∧ (r.headD 0 != 0) = recRuleK rules; ⊤⦄ := sorry

@[refines ConRon.Arena.isStrLit]
theorem isStrLit_refines (p : Prog) (hp : IotaProg p) : IsStrLitOK p := sorry

theorem defeqList_refines (p : Prog) (hp : IotaProg p) (hw : WhnfCallees p) (hc : IotaCallees p) :
    DefeqListOK p := sorry

theorem piResidual_refines (p : Prog) (hp : IotaProg p) (hw : WhnfCallees p) (hc : IotaCallees p) :
    PiResidualOK p := sorry

end L.Arena
