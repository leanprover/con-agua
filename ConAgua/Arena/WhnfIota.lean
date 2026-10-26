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
* `wscoped_bfast(d, e)`, `loose_bvars_bounded_fast(f, c, e)` (now real: lane `exprops4`'s, `f` the
  counter, `CoreWalks.lean`), `leaf_guard(fab, major)`: the task's own
  "phase 4 walks, stubs too".
* `lit_to_ctor_if_nat(vis, h)`: "written by another agent in `WhnfDelta.lean`" (which does not
  exist yet); called by name.

`str_lit_supported`, `str_lit_ctor`, `inst_list`, `inst_lp` are already `WhnfCallees` stubs
(`WhnfBase.lean`) and are reused via that hypothesis, not redeclared here.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

/-! ## `is_ctor_app(vis, e)`, `is_str_lit(h)` -/

/-- con-leche: `CoreDefs.lean:51-58` `isCtorApp` — the spine's head is a stored constructor. -/
-- con-ron: ConRon/Arena/Core.lean:327-338 ConRon.Arena.isCtorApp
@[l_impl ConRon.Arena.isCtorApp]
def isCtorAppL : FunDecl := lfn (vis, e) locals (hh, t, i, c, flag, q) {
  hh := call get_app_fn(e);
  if hh >> 28 != 3 { return 0 };
  t := ⟦hh⟧.tier;
  i := ⟦hh⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CONST⟨t⟩.count <= i { abort };
  c := CONST⟨t, i⟩.n;
  (flag, q) := call env_find(c, vis);
  if flag == 0 { return 0 };
  return u64(EREC.u64[q] == 4)
}

/-- con-leche: `Core.lean:695-699` `Expr.isStrLit` — the tag, then the literal kind. -/
-- con-ron: ConRon/Arena/Core.lean:1904-1912 ConRon.Arena.isStrLit
@[l_impl ConRon.Arena.isStrLit]
def isStrLitL : FunDecl := lfn (h) locals (t, i) {
  if h >> 28 != 8 { return 0 };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if LIT⟨t⟩.count <= i { abort };
  return u64(LIT⟨t, i⟩.kind == 1)
}

/-! ## `find_rule(ro, rc, c)`, `rec_rule_k(ro, rc)`

Both read only the 11-word rule records at `(ro, rc)` in `EREC`; neither touches `AM`. -/

/-- The scan of `find_rule` (a named block, for the proofs). -/
def findRuleLoop : Stmt := lblk (ro, rc, c, i) {
  while i < rc {
    if EREC.u64[ro + 11 * i] == c { return (1, ro + 11 * i) };
    i += 1
  }
}

/-- con-leche: `Core.lean:777-876` (`iotaRec`'s own lookup) `findRule` — the rule whose
constructor is `c`, as a linear scan of the rule-record slice. -/
-- con-ron: ConRon/Arena/Core.lean:2006-2011 ConRon.Arena.findRule
@[l_impl ConRon.Arena.findRule]
def findRuleL : FunDecl := lfn (ro, rc, c) locals (i) {
  i := 0;
  ⟪findRuleLoop⟫;
  return (0, 0)
}

/-- con-leche: `CoreDefs.lean:899-906` `recRuleK` — the stored bit of the single rule. -/
-- con-ron: ConRon/Arena/Core.lean:1897-1902 ConRon.Arena.recRuleK
@[l_impl ConRon.Arena.recRuleK]
def recRuleKL : FunDecl := lfn (ro, rc) locals () {
  if rc != 1 { return 0 };
  return EREC.u64[ro + 9]
}

/-! ## Reserved names: a small fusion of `reservedBasisNames` and `List.contains`

Not tagged `@[l_impl]` on its own (it fuses a lookup declaration and a list membership test, as
the house style allows for small dispatchers); `major_to_ctor`'s eta branch is its only caller. -/

/-- con-ron: ConRon/Arena/Core.lean:1452-1456 ConRon.Arena.reservedBasisNames -/
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

/-- A word of the record pool (a one-line reader, so that callers' proofs read it through a call). -/
-- con-ron: ConRon/Arena/Core.lean:348-365 ConRon.Arena.iotaCtorNeverProp
def eRecGetL : FunDecl := lfn (k) locals () { return EREC.u64[k] }

/-- The head name of a `const` handle (the view checks, then the stored name). -/
-- con-ron: ConRon/Arena/Core.lean:348-365 ConRon.Arena.iotaCtorNeverProp
def constNameOfL : FunDecl := lfn (hh) locals (t, i) {
  t := ⟦hh⟧.tier;
  i := ⟦hh⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CONST⟨t⟩.count <= i { abort };
  return CONST⟨t, i⟩.n
}

/-- The family test of `iota_ctor_never_prop` at the inductive's record `indP`: it is an
inductive, its level-parameter count is `us`' length, and `caps_never_zero`. -/
-- con-ron: ConRon/Arena/Core.lean:348-365 ConRon.Arena.iotaCtorNeverProp
def indCapsCheckL : FunDecl := lfn (indP, us) locals (k, uso, usl, lp, po, swd, so, sc, nz) {
  k := call e_rec_get(indP);
  if k != 3 { return 0 };
  (uso, usl) := call ls_node(us);
  lp := call e_rec_get(indP + 3);
  if lp != usl { return 0 };
  po := call e_rec_get(indP + 2);
  swd := call e_rec_get(indP + 12);
  so := call e_rec_get(indP + 13);
  sc := call e_rec_get(indP + 14);
  nz := call caps_never_zero(po, lp, us, swd, so, sc);
  return nz
}

/-- con-leche: `CoreDefs.lean:72-93` `iotaCtorNeverProp` — is the matched constructor's family
never `Prop` at the comparand levels? `ctorP` is the constructor's `IConstantInfo` pointer
(`cvj`'s record base); its type's Π-result's head constant is looked up for the family's `caps`. -/
-- con-ron: ConRon/Arena/Core.lean:348-365 ConRon.Arena.iotaCtorNeverProp
@[l_impl ConRon.Arena.iotaCtorNeverProp]
def iotaCtorNeverPropL : FunDecl := lfn (vis, ctorP, us)
    locals (ty, piRes, hh, T, indFlag, indP, nz) {
  ty := call e_rec_get(ctorP + 4);
  piRes := call pi_result(ty);
  hh := call get_app_fn(piRes);
  if hh >> 28 != 3 { return 0 };
  T := call const_name_of(hh);
  (indFlag, indP) := call env_find(T, vis);
  if indFlag == 0 { return 0 };
  nz := call ind_caps_check(indP, us);
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

/-- The slot walk of `tower_slots_all` (a named block, for the proofs). -/
def towerSlotsAllLoop : Stmt := lblk (vis, T, nF, j, flag, q) {
  while j < nF {
    (flag, q) := call find_proj(vis, T, j);
    if flag == 0 { return 0 };
    j += 1
  }
}

/-- con-leche: `CoreDefs.lean:723-728`/`FEnv.lean:195-197` `towerSlotsAll` — are all `nF`
projection slots of `T` table entries? -/
-- con-ron: ConRon/Arena/Core.lean:1430-1434 ConRon.Arena.towerSlotsAll
@[l_impl ConRon.Arena.towerSlotsAll]
def towerSlotsAllL : FunDecl := lfn (vis, T, nF) locals (j, flag, q) {
  j := 0;
  ⟪towerSlotsAllLoop⟫;
  return 1
}

/-- The projection walk of `eta_projs` (a named block, for the proofs). -/
def etaProjsLoop : Stmt := lblk (T, b, nF, o, j, pr) {
  while j < nF {
    pr := call mk_proj(T, j, b);
    SPN.u64[o + j] := pr;
    j += 1
  }
}

/-- con-leche: `CoreDefs.lean:730-735`/`Cached/CoreC.lean:310-317` `etaProjs`/`projNodesGo` — the
`.proj T j b` spine, `j = 0, …, nF - 1`, pushed in order. -/
-- con-ron: ConRon/Arena/Core.lean:1445-1450 ConRon.Arena.etaProjs
-- con-ron: ConRon/Arena/Core.lean:1436-1443 ConRon.Arena.projNodesGo
@[l_impl ConRon.Arena.etaProjs ConRon.Arena.projNodesGo]
def etaProjsL : FunDecl := lfn (T, b, nF) locals (o, j, pr) {
  o := CTL.u64[136];
  if len(SPN.u64) < o { abort };
  if len(SPN.u64) - o < nF { abort };
  j := 0;
  ⟪etaProjsLoop⟫;
  CTL.u64[136] := o + nF;
  return (o, nF)
}

/-- con-leche: `CoreDefs.lean:750-754` `etaFabArgsE` — the major's type's arguments, then the
major's projections. The second slice is pushed directly after the first (nothing intervenes), so
the concatenation is the one combined slice. -/
-- con-ron: ConRon/Arena/Core.lean:1638-1644 ConRon.Arena.etaFabArgsE
@[l_impl ConRon.Arena.etaFabArgsE]
def etaFabArgsL : FunDecl := lfn (T, to, tn, major, nF) locals (o2, n2) {
  (o2, n2) := call eta_projs(T, major, nF);
  return (to, tn + n2)
}

/-! ## `and_rescue_slots(vis, ctor, nP, us)` -/

/-- The two-slot walk of `and_rescue_slots` (a named block, for the proofs). `fire_ok` is called
before the shape checks: the twin's `(← e.fireOk ust)` is lifted out of the `if` and runs
regardless, with its cache effects. -/
def andRescueLoop : Stmt := lblk (vis, ctor, nP, us, an, j, flag, q, ok) {
  while j < 2 {
    (flag, q) := call find_proj(vis, an, j);
    if flag == 0 { return 0 };
    ok := call fire_ok(q, j, us);
    if EREC.u64[q + 6] != ctor { return 0 };
    if EREC.u64[q + 5] != nP { return 0 };
    if EREC.u64[q + 7] != 2 { return 0 };
    if ok == 0 { return 0 };
    j += 1
  }
}

/-- con-leche: `CoreDefs.lean:793-806`/`:808-810`/`FEnv.lean:199-201` `andRescueSlotsGo` /
`andRescueSlots` / `FEnv.andRescueSlotsF` — the pinned `And`'s two projection slots, ready to
fire. `q`, the table pointer `find_proj` hands back, has `ctor` at `q + 6`, `numParams` at `q + 5`,
`numFields` at `q + 7` (`EnvRec.lean`'s `decTbl`). -/
-- con-ron: ConRon/Arena/Core.lean:1659-1671 ConRon.Arena.andRescueSlotsGo
-- con-ron: ConRon/Arena/Core.lean:1673-1681 ConRon.Arena.andRescueSlots
@[l_impl ConRon.Arena.andRescueSlotsGo ConRon.Arena.andRescueSlots]
def andRescueSlotsL : FunDecl := lfn (vis, ctor, nP, us) locals (an, j, flag, q, ok) {
  an := call pin_at(11);
  j := 0;
  ⟪andRescueLoop⟫;
  return 1
}

/-! ## `fab_scope_ok(d, fab, major)` -/

/-- con-leche: `Core.lean:502-663` (the shared scope guard) `fabScopeOk` — well-scoped, closed
under loose bvars, and every free variable of `fab` is one of `major`'s. All three callees are
phase-4-walk stubs. -/
-- con-ron: ConRon/Arena/Core.lean:1687-1704 ConRon.Arena.fabScopeOk
@[l_impl ConRon.Arena.fabScopeOk]
def fabScopeOkL : FunDecl := lfn (d, fab, major) locals (ok) {
  ok := call wscoped_bfast(d, fab);
  if ok == 0 { return 0 };
  ok := call loose_bvars_bounded_fast(4000000000, 0, fab);
  if ok == 0 { return 0 };
  ok := call leaf_guard(fab, major);
  return ok
}

/-! ## `lit_major_to_ctor(mode, vis, d, h)` -/

/-- con-leche: `Core.lean:665-677` `litMajorToCtor` — a `Nat` literal major one layer, a `String`
literal to its reduced constructor form. -/
-- con-ron: ConRon/Arena/Core.lean:1823-1836 ConRon.Arena.litMajorToCtor
@[l_impl ConRon.Arena.litMajorToCtor]
def litMajorToCtorL : FunDecl := lfn (mode, vis, d, h) locals (t, i, kind, sup, c, r) {
  if h >> 28 != 8 { r := call lit_to_ctor_if_nat(vis, h); return r };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if LIT⟨t⟩.count <= i { abort };
  kind := LIT⟨t, i⟩.kind;
  if kind != 1 { r := call lit_to_ctor_if_nat(vis, h); return r };
  sup := call str_lit_supported(vis);
  if sup == 0 { return h };
  c := call str_lit_ctor(h);
  r := call whnf(mode, vis, d, c);
  return r
}

/-! ## `major_to_ctor(mode, vis, d, rec, ro, rc, major)`

`rec` (the recursor's own name) is unused by the twin (`_recName`) and so by this code too: it is
accepted only to match the twin's argument list. The body is split into small functions
(`WhnfM2C.lean`, `m2c_head` and its callees); this one saves the stack top and puts it back (the
K and `And` arms leave slices on the spine stack; the twin has no stack, so restoring is always
faithful). -/

/-- con-leche: `Core.lean:502-663`/`Cached/CoreC.lean:428-453` `majorToCtor`/`majorToCtorI` — the
stuck-major rescue: K-flagged, η-capable, or the pinned `And`. No certificate on a fabricated
spine; the K and `And` fabrications keep the type check, and the proof-irrelevance run is a
certificate family (off at `.trusted`). -/
-- con-ron: ConRon/Arena/Core.lean:1706-1821 ConRon.Arena.majorToCtor
@[l_impl ConRon.Arena.majorToCtor]
def majorToCtorL : FunDecl := lfn (mode, vis, d, rec, ro, rc, major) locals (top, r) {
  top := CTL.u64[136];
  r := call m2c_head(mode, vis, d, ro, rc, major);
  CTL.u64[136] := top;
  return r
}

/-! ## `prepare_major(mode, vis, d, rec, ro, rc, major)` -/

/-- con-leche: `Core.lean:701-775`/`Cached/CoreC.lean:553-575` `prepareMajor`/`prepareMajorI` — at
a K-flagged recursor the K rescue runs on the raw major; elsewhere the structure rescues run on
the major as found first (a `String` literal skips that attempt), and only if they produce no
constructor is the major head-normalized, its literal converted, and the rescue tried again. -/
-- con-ron: ConRon/Arena/Core.lean:1914-1938 ConRon.Arena.prepareMajor
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

/-- The telescope walk of `pi_residual` (a named block, for the proofs). -/
def piResidualLoop : Stmt := lblk (e, ao, an, i, t, x, body, b2) {
  while i < an {
    if e >> 28 != 6 { return (0, 0) };
    t := ⟦e⟧.tier;
    x := ⟦e⟧.idx;
    if t != 0 && CTL.u64[1] == 0 { abort };
    if FORALL⟨t⟩.count <= x { abort };
    body := FORALL⟨t, x⟩.b;
    b2 := call inst_entry(body, SPN.u64[ao + i], 0);
    e := b2;
    i += 1
  }
}

/-- con-leche: `CoreDefs.lean:716-721` `piResidual` — peel a ∀-telescope along an argument
spine `(ao, an)`. -/
-- con-ron: ConRon/Arena/Core.lean:1326-1337 ConRon.Arena.piResidual
@[l_impl ConRon.Arena.piResidual]
def piResidualL : FunDecl := lfn (e, ao, an) locals (i, t, x, body, b2) {
  i := 0;
  ⟪piResidualLoop⟫;
  return (1, e)
}

/-! ## `defeq_list(mode, vis, d, ao, an, bo, bn)` -/

/-- The pairwise walk of `defeq_list` (a named block, for the proofs). -/
def defeqListLoop : Stmt := lblk (mode, vis, d, ao, an, bo, bn, i, ok) {
  while i < an && i < bn {
    ok := call defeq(mode, vis, d, SPN.u64[ao + i], SPN.u64[bo + i]);
    if ok == 0 { return 0 };
    i += 1
  }
}

/-- con-leche: `Core.lean:269-278` `defEqList` — pairwise definitional equality of two spines. As the
twin, it compares the common prefix pairwise (stopping at the first `false`) and only then the
lengths: an early length test would skip the twin's `defeq` calls and their cache writes. -/
-- con-ron: ConRon/Arena/Core.lean:1339-1346 ConRon.Arena.defEqList
@[l_impl ConRon.Arena.defEqList]
def defeqListL : FunDecl := lfn (mode, vis, d, ao, an, bo, bn) locals (i, ok) {
  i := 0;
  ⟪defeqListLoop⟫;
  return u64(an == bn)
}

/-! ## `iota_index_ok(mode, vis, d, mI, rP, cnP, tyCtor, mo, mn, xo, xn)` -/

/-- con-leche: `Core.lean:280-296` `iotaIndexOk` — the canonical-index comparison of a firing
ι redex. The stack top is restored after the `get_app_args` slice (the twin's list is a value; the
refinement specs promise `StackKept`). -/
-- con-ron: ConRon/Arena/Core.lean:1348-1358 ConRon.Arena.iotaIndexOk
@[l_impl ConRon.Arena.iotaIndexOk]
def iotaIndexOkL : FunDecl := lfn (mode, vis, d, mI, rP, cnP, tyCtor, mo, mn, xo, xn)
    locals (flag, res, top, ao2, an2, an3) {
  if mI == rP { return 1 };
  (flag, res) := call pi_residual(tyCtor, mo, mn);
  if flag == 0 { return 0 };
  top := CTL.u64[136];
  (ao2, an2) := call get_app_args(res);
  an3 := (an2 - cnP) * u64(cnP <= an2);
  res := call defeq_list(mode, vis, d, ao2 + cnP, an3, xo, xn);
  CTL.u64[136] := top;
  return res
}

/-! ## `proof_irrel(mode, vis, d, a, b)` -/

/-- One side of `proof_irrel`: infer the type's type at the io grade, head-normalize, and compare a
`Sort`'s level with zero. Result `0`: not a sort; `1`: a sort that is not `Prop`; `2`: `Prop`
(callers test `!= 1`, which the cache decoder `decO` reads the same as `== 2`).
`lvl_eq_c`'s answer word is `0` none (a decline, `abort`), `1` false, `2` true. The comparison is the
CACHED `lvl_eq_c` (the twin's `lvlEq?` consults and fills the verdict cache). -/
-- con-ron: ConRon/Arena/Core.lean:1360-1385 ConRon.Arena.proofIrrel
def proofIrrelHalfL : FunDecl := lfn (mode, vis, d, x)
    locals (ta, tta, hh, t, i, uT, z, ok) {
  ta := call infer_io(mode, vis, d, x);
  tta := call infer_io(mode, vis, d, ta);
  hh := call whnf(mode, vis, d, tta);
  if hh >> 28 != 2 { return 0 };
  t := ⟦hh⟧.tier;
  i := ⟦hh⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if SORT⟨t⟩.count <= i { abort };
  uT := SORT⟨t, i⟩.u;
  z := call pin_word(53);
  ok := call lvl_eq_c(uT, z);
  if ok == 0 { fail R_RESOURCE_LIMIT_FUEL };
  return ok
}

/-- con-leche: `Core.lean:298-320` `proofIrrel` — proof irrelevance: both sides' types' sorts are
`Prop` (two `proof_irrel_half`s; the second only if the first is a sort, as the twin). -/
-- con-ron: ConRon/Arena/Core.lean:1360-1385 ConRon.Arena.proofIrrel
@[l_impl ConRon.Arena.proofIrrel]
def proofIrrelL : FunDecl := lfn (mode, vis, d, a, b) locals (ra, rb) {
  ra := call proof_irrel_half(mode, vis, d, a);
  if ra == 0 { return 0 };
  rb := call proof_irrel_half(mode, vis, d, b);
  if rb == 0 { return 0 };
  return u64(ra != 1) & u64(rb != 1)
}

/-! ## `rule_rhs_at(rec, ctor, po, pl, rhs, us)`, `const_ty_at(n, po, pl, ty, us)`

Both are thin memo wrappers around `inst_lp` (a `WhnfCallees` stub), over the already-installed
caches `ruleRhsC` (array 104, `rrSch`) and `constTyC` (array 102, `ctSch`): `CoreCaches.lean`,
`CoreRefine.lean`'s `rrKey`/`memoRG_findR`/`memoRG_findP`. -/

/-- con-leche: none — `ruleRhsAt`'s cache probe, `rrSch`'s key `(rec, ctor ||| us << 32)`. The probe
is repeated after `inst_lp` (as `const_val_at` does): the slot found before the call is stale if the
callee wrote the memo. -/
-- con-ron: ConRon/Arena/Core.lean:209-224 ConRon.Arena.ruleRhsAt
@[l_impl ConRon.Arena.ruleRhsAt]
def ruleRhsAtL : FunDecl := lfn (rec, ctor, po, pl, rhs, us)
    locals (k2, fd, j, dd, r, dum) {
  k2 := ctor | (us << 32);
  (fd, j, dd) := call rr_find(rec, k2);
  if fd != 0 { return rrSch.arr.u64[j * 4 + 3] };
  r := call inst_lp(po, pl, us, rhs);
  (fd, j, dd) := call rr_find(rec, k2);
  dum := call rr_put(rec, k2, r, fd, j);
  return r
}

/-- con-leche: none — `constTyAt`'s cache probe, `ctSch`'s key `(n, us)`. The probe is repeated
after `inst_lp` (as `const_val_at` does). -/
-- con-ron: ConRon/Arena/Core.lean:178-191 ConRon.Arena.constTyAt
@[l_impl ConRon.Arena.constTyAt]
def constTyAtL : FunDecl := lfn (n, po, pl, ty, us) locals (fd, j, dd, r, dum) {
  (fd, j, dd) := call ct_find(n, us);
  if fd != 0 { return ctSch.arr.u64[j * 4 + 3] };
  r := call inst_lp(po, pl, us, ty);
  (fd, j, dd) := call ct_find(n, us);
  dum := call ct_put(n, us, r, fd, j);
  return r
}

/-! ## `rec_fire_args(…)`: `instSpine`, `inst_spine_pins`, `rec_fire_args` -/

/-- The instantiation walk of `inst_spine` (a named block, for the proofs). -/
def instSpineLoop : Stmt := lblk (ao, an, t, e, i) {
  while i < an {
    e := call inst_entry(e, SPN.u64[ao + i], t);
    t := t - 1;
    i += 1
  }
}

/-- con-leche: `ExprOps.lean:1305-1313` `instSpine` — instantiate a telescope-context expression
at an argument spine `(ao, an)`, the fuel-like index `t` decreasing by one per argument. -/
-- con-ron: ConRon/Arena/ExprOps.lean:1379-1385 ConRon.Arena.instSpine
@[l_impl ConRon.Arena.instSpine]
def instSpineL : FunDecl := lfn (ao, an, t, e) locals (i) {
  i := 0;
  ⟪instSpineLoop⟫;
  return e
}

/-- The pin walk of `inst_spine_pins` (a named block, for the proofs). Each result is pushed (the top
is raised) as soon as it is stored: the next iteration's callees may use the stack above the top,
and the earlier results must lie below it. -/
def instSpinePinsLoop : Stmt := lblk (po, pl, us, ao, an, rP, pvo, pvc, so, j, q, s) {
  while j < pvc {
    q := call inst_lp(po, pl, us, SPN.u64[pvo + j]);
    s := call inst_spine(ao, an, rP - 1, q);
    SPN.u64[so + j] := s;
    CTL.u64[136] := so + j + 1;
    j += 1
  }
}

/-- con-leche: `CoreDefs.lean:908-927` `recFireComparands` (the nested rule's stored parameter
pins, `instSpinePins`) — each pin level-instantiated (`inst_lp`) then spined over the leading
`rP` arguments of the spine `(ao, an)` (`inst_spine`; the twin's `args.take rP`: all `an` of them
when `an < rP`, the index still starting at `rP - 1`), pushed in order. -/
-- con-ron: ConRon/Arena/Core.lean:1964-1974 ConRon.Arena.instSpinePins
@[l_impl ConRon.Arena.instSpinePins]
def instSpinePinsL : FunDecl := lfn (po, pl, us, ao, an, rP, pvo, pvc) locals (so, j, q, s) {
  if rP < an { an := rP };
  so := CTL.u64[136];
  if len(SPN.u64) < so { abort };
  if len(SPN.u64) - so < pvc { abort };
  j := 0;
  ⟪instSpinePinsLoop⟫;
  return (so, pvc)
}

/-- con-leche: `CoreDefs.lean:908-927` `recFireComparands` (its `.2`) — the constructor-PARAMETER
comparands of a firing rule: a `.nested` rule's stored pins, instantiated and spined; a `.plain`
rule's the recursor's own leading `ctorParams` arguments (`args.take ctorParams` of the spine
`(ao, an)`: all `an` of them when `an < ctorParams`). -/
-- con-ron: ConRon/Arena/Core.lean:1996-2004 ConRon.Arena.recFireArgs
@[l_impl ConRon.Arena.recFireArgs]
def recFireArgsL : FunDecl := lfn (fireKind, pvo, pvc, po, pc, us, ao, an, rP, ctorParams)
    locals (so, sc) {
  if fireKind == 1 {
    (so, sc) := call inst_spine_pins(po, pc, us, ao, an, rP, pvo, pvc);
    return (so, sc)
  };
  if an < ctorParams { ctorParams := an };
  return (ao, ctorParams)
}

/-! ## `iota_certs_full(mode, vis, d, h, ao, an)` -/

/-- The domain check of `iota_certs_full_forall`: the argument's FULL-grade inferred type is defeq
to the domain `ty` opened by the accumulator `(aco, acn)`. -/
-- con-ron: ConRon/Arena/Core.lean:1285-1317 ConRon.Arena.iotaCertsFullAux
def iotaCertsFullCheckL : FunDecl := lfn (mode, vis, d, ty, aco, acn, arg) locals (ty2, ta, ok) {
  ty2 := call inst_list(ty, aco, acn, 0);
  ta := call infer(mode, vis, d, arg);
  ok := call defeq(mode, vis, d, ta, ty2);
  return ok
}

/-- The view checks of a handle, by tag (`ViewL.lean`'s `viewOK`): the scratch tier open for a
scratch handle, the index below the tier's count. Aborts on a dangling handle (the twin's `view`
fails there); returns `0`. -/
-- con-ron: ConRon/Arena/Core.lean:1285-1317 ConRon.Arena.iotaCertsFullAux
def exprViewOkL : FunDecl := lfn (h) locals (t, x, g, c) {
  t := ⟦h⟧.tier;
  x := ⟦h⟧.idx;
  g := h >> 28;
  if t != 0 && CTL.u64[1] == 0 { abort };
  c := 0;
  if g == 0 { c := BVAR⟨t⟩.count } else {
    if g == 1 { c := FVAR⟨t⟩.count } else {
      if g == 2 { c := SORT⟨t⟩.count } else {
        if g == 3 { c := CONST⟨t⟩.count } else {
          if g == 4 { c := APP⟨t⟩.count } else {
            if g == 5 { c := LAM⟨t⟩.count } else {
              if g == 6 { c := FORALL⟨t⟩.count } else {
                if g == 7 { c := LET⟨t⟩.count } else {
                  if g == 8 { c := LIT⟨t⟩.count } else {
                    if g == 9 { c := PROJ⟨t⟩.count } else { abort } } } } } } } } } };
  if c <= x { abort };
  return 0
}

/-- A control word (a one-line reader, so that callers' proofs read it through a call). -/
-- con-ron: ConRon/Arena/Core.lean:1319-1324 ConRon.Arena.iotaCertsFull
def ctlGetL : FunDecl := lfn (k) locals () { return CTL.u64[k] }

/-- A stack word (a one-line reader, so that callers' proofs read it through a call). -/
-- con-ron: ConRon/Arena/Core.lean:1285-1317 ConRon.Arena.iotaCertsFullAux
def spnGetL : FunDecl := lfn (k) locals () { return SPN.u64[k] }

/-- The record of a `forallE` handle: its domain and body (the guards of a stored-node read). -/
-- con-ron: ConRon/Arena/Core.lean:1285-1317 ConRon.Arena.iotaCertsFullAux
def iotaCertsFullPartsL : FunDecl := lfn (h) locals (t, x) {
  t := ⟦h⟧.tier;
  x := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if FORALL⟨t⟩.count <= x { abort };
  return (FORALL⟨t, x⟩.ty, FORALL⟨t, x⟩.b)
}

/-- The `forallE` arm of `iota_certs_full_aux` (split off: the function was too long for `vcgen`):
`h` a `forallE`; certify the argument `SPN[ao + i]` against its instantiated domain, push it on the
accumulator, and continue with the body. -/
-- con-ron: ConRon/Arena/Core.lean:1285-1317 ConRon.Arena.iotaCertsFullAux
def iotaCertsFullForallL : FunDecl := lfn (mode, vis, d, h, aco, acn, ao, an, i)
    locals (ty, body, arg, ok, dum) {
  (ty, body) := call iota_certs_full_parts(h);
  arg := call spn_get(ao + i);
  ok := call iota_certs_full_check(mode, vis, d, ty, aco, acn, arg);
  if ok == 0 { return 0 };
  if len(SPN.u64) <= aco + acn { abort };
  SPN.u64[aco + acn] := arg;
  CTL.u64[136] := aco + acn + 1;
  dum := call iota_certs_full_aux(mode, vis, d, body, aco, acn + 1, ao, an, i + 1);
  return dum
}

/-- The `bvar` arm of `iota_certs_full_aux`: the telescope ran out of syntactic binders with a
pending substitution; flush the accumulator into `h` and look again (with an empty accumulator at
the stack top). -/
-- con-ron: ConRon/Arena/Core.lean:1285-1317 ConRon.Arena.iotaCertsFullAux
def iotaCertsFullFlushL : FunDecl := lfn (mode, vis, d, h, aco, acn, ao, an, i) locals (ty2, dum) {
  dum := call expr_view_ok(h);
  if acn == 0 { return 0 };
  ty2 := call inst_list(h, aco, acn, 0);
  dum := call iota_certs_full_aux(mode, vis, d, ty2, aco + acn, 0, ao, an, i);
  return dum
}

/-- con-leche: `Kernel/Core.lean:252-267`/`Cached/CoreC.lean:149-181` `iotaCertsFullAux`/
`iotaCertsFull`/`iotaCertsFullI` — certify a spine against a constructor telescope: every
argument's FULL-grade inferred type is defeq to the corresponding (instantiated) domain, the
pending substitutions carried in an accumulator opened in one `instantiateList`. The accumulator
is the stack slice `(aco, acn)`, pushed directly above the fixed spine `(ao, an)`; nothing
intervenes between a growth and the next read, so it stays contiguous. -/
-- con-ron: ConRon/Arena/Core.lean:1285-1317 ConRon.Arena.iotaCertsFullAux
@[l_impl ConRon.Arena.iotaCertsFullAux]
def iotaCertsFullAuxL : FunDecl := lfn (mode, vis, d, h, aco, acn, ao, an, i) locals (dum) {
  if i < an {
    if h >> 28 == 6 {
      dum := call iota_certs_full_forall(mode, vis, d, h, aco, acn, ao, an, i);
      return dum
    };
    if h >> 28 == 0 {
      dum := call iota_certs_full_flush(mode, vis, d, h, aco, acn, ao, an, i);
      return dum
    };
    dum := call expr_view_ok(h);
    return 0
  };
  return 1
}

/-- con-leche: `Kernel/Core.lean:252-267`/`Cached/CoreC.lean:178-181` `iotaCertsFull`/
`iotaCertsFullI` — the empty-accumulator entry. The stack top is restored after the walk (the
accumulator is scratch; the refinement specs promise `StackKept`). -/
-- con-ron: ConRon/Arena/Core.lean:1319-1324 ConRon.Arena.iotaCertsFull
@[l_impl ConRon.Arena.iotaCertsFull]
def iotaCertsFullL : FunDecl := lfn (mode, vis, d, h, ao, an) locals (top, res) {
  top := call ctl_get(136);
  res := call iota_certs_full_aux(mode, vis, d, h, top, 0, ao, an, 0);
  CTL.u64[136] := top;
  return res
}

/-! ## `iota_rec_at(mode, vis, d, hd, so, sn)` -/

/-- con-leche: `Core.lean:777-876` `iotaRec`/`iotaRecAt` — one ι step at a spine the caller
already holds: `hd` the head, `(so, sn)` the stack slice of arguments, `sn` the spine's length
(`whnfApp`'s only call site passes `va.size` for both `n` and the slice length). The head's
`const` view (`iota_rec_head`), then the rest, split into small functions (`WhnfIotaRec.lean`,
from `iota_rec_c` on). -/
-- con-ron: ConRon/Arena/Core.lean:2013-2098 ConRon.Arena.iotaRecAt
@[l_impl ConRon.Arena.iotaRecAt]
def iotaRecAtL : FunDecl := lfn (mode, vis, d, hd, so, sn) locals (hf, c, us, r1, r2) {
  (hf, c, us) := call iota_rec_head(hd);
  if hf == 0 { return (0, 0) };
  (r1, r2) := call iota_rec_c(mode, vis, d, c, us, so, sn);
  return (r1, r2)
}

/-! ## The program -/

/-- What this file's specs need of a program: its own functions, at their names. -/
structure IotaProg (p : Prog) : Prop where
  isCtorApp : p.lookup "is_ctor_app" = some isCtorAppL
  isStrLit : p.lookup "is_str_lit" = some isStrLitL
  findRule : p.lookup "find_rule" = some findRuleL
  recRuleK : p.lookup "rec_rule_k" = some recRuleKL
  reservedContains : p.lookup "reserved_contains_w" = some reservedContainsL
  iotaCtorNeverProp : p.lookup "iota_ctor_never_prop" = some iotaCtorNeverPropL
  eRecGet : p.lookup "e_rec_get" = some eRecGetL
  constNameOf : p.lookup "const_name_of" = some constNameOfL
  indCapsCheck : p.lookup "ind_caps_check" = some indCapsCheckL
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
  proofIrrelHalf : p.lookup "proof_irrel_half" = some proofIrrelHalfL
  ruleRhsAt : p.lookup "rule_rhs_at" = some ruleRhsAtL
  constTyAt : p.lookup "const_ty_at" = some constTyAtL
  instSpine : p.lookup "inst_spine" = some instSpineL
  instSpinePins : p.lookup "inst_spine_pins" = some instSpinePinsL
  recFireArgs : p.lookup "rec_fire_args" = some recFireArgsL
  iotaCertsFullAux : p.lookup "iota_certs_full_aux" = some iotaCertsFullAuxL
  iotaCertsFullForall : p.lookup "iota_certs_full_forall" = some iotaCertsFullForallL
  iotaCertsFullCheck : p.lookup "iota_certs_full_check" = some iotaCertsFullCheckL
  iotaCertsFullParts : p.lookup "iota_certs_full_parts" = some iotaCertsFullPartsL
  exprViewOk : p.lookup "expr_view_ok" = some exprViewOkL
  ctlGet : p.lookup "ctl_get" = some ctlGetL
  spnGet : p.lookup "spn_get" = some spnGetL
  iotaCertsFullFlush : p.lookup "iota_certs_full_flush" = some iotaCertsFullFlushL
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

/-- A `PropWhen` datum from its three words `(swd, so, sc)` (`swd = 0` `.never`, `1` `.ifAllZero`
with the `EREC` name slice `(so, sc)`), as `decPW` reads it at consecutive words. -/
def decPWw (a : Array Word) (dn : NIdx → Option ConLeche.Name) (swd so sc : Word) :
    Option ConLeche.PropWhen :=
  match swd.toNat with
  | 0 => some .never
  | 1 => do
    let l : List NIdx ← hslice? a so.toNat sc.toNat
    pure (.ifAllZero (← l.mapM dn))
  | _ => none

/-- con-leche: `CoreDefs.lean:60-70` `capsNeverZero`, at a `PropWhen` datum. -/
def capsNeverZeroPW (lps : List NIdx) (us : LsIdx) (pw : ConLeche.PropWhen) : AM Bool := do
  let ks ← readNamesM lps
  let vs ← readLevelsM us
  pure (ConLeche.Level.substPW ks vs pw).isNever

/-- `caps_never_zero(po, pc, us, swd, so, sc)` refines `capsNeverZero lps us caps` at the recursor's
own level parameters (`po, pc`, an `EREC` name slice, read back by `readNamesM`), the universe
arguments `us` (an `LsIdx`, `readLevelsM`), and a `PropWhen` datum `(swd, so, sc)` (`caps.sortZ`).
**Statement correction**: the stub's `ks`, `vs`, `pw` were arbitrary and its twin a `pure`; the real
twin runs the two readbacks (`capsNeverZero`), and the datum is linked to the words. The level
parameters read back (a stored constant's, `StoreDen.constLps`); the list `us` need not: `ls_node`
aborts on a handle that is not stored (`capsNeverZeroOK_of`). -/
def CapsNeverZeroOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb po pc us swd so sc : Word) (lps : List NIdx) (pw : ConLeche.PropWhen),
    CoreS dn s₀.mem a₀ vis fe MM eb → HW us →
    hslice? (s₀.mem.arr64 EREC) po.toNat pc.toNat = some lps →
    (∃ ks, lps.mapM (denoteN a₀.store.ns) = some ks) →
    decPWw (s₀.mem.arr64 EREC) dn swd so sc = some pw →
    CoreSpec p n "caps_never_zero" [po, pc, us, swd, so, sc]
      (capsNeverZeroPW lps (decI us) pw) decBool s₀ a₀ dn vis fe MM eb

/-- **The fire datum at its words, reading back**: kind `0` plain (the constructor's level
parameters the `EREC` name slice `(qo, qc)`, their names reading back), else nested (the stored
levels the `EREC` slice `(fvo, fvc)`, reading back). -/
def FireCore (m : Mem) (a : AState) (fk fvo fvc qo qc : Word) (rl : IRecRule) (cvjLps : List NIdx) :
    Prop :=
  (fk = 0 ∧ rl.fire = .plain ∧ hslice? (m.arr64 EREC) qo.toNat qc.toNat = some cvjLps ∧
      ∃ ks, cvjLps.mapM (denoteN a.store.ns) = some ks) ∨
    (fk ≠ 0 ∧ ∃ lvls pins, rl.fire = .nested lvls pins ∧
      hslice? (m.arr64 EREC) fvo.toNat fvc.toNat = some lvls ∧
      ∀ u ∈ lvls, ∃ L, denoteL a.store.ls u = some L)

/-- **Where a firing rule comes from**: a rule of a recursor of the environment (whose level
parameters are `lps`), and a constructor of the environment. State-free, so it passes down the
ι block's calls; the readbacks follow at any state from `StoreDen` (`constLps`, `recRules`). -/
def FireEnv (fe : IFEnv) (lps : List NIdx) (rule : IRecRule) (cvj : IConstantVal) : Prop :=
  (∃ c cv mI rP rules, fe.find? c = some (.recInfo cv mI rP rules) ∧ cv.levelParams = lps ∧
      rule ∈ rules) ∧
    ∃ c np nf, fe.find? c = some (.ctorInfo cvj np nf)

/-- `rec_fire_levels(fireKind, fvo, fvc, po, pc, us, qo, qc)` refines `recFireLevels rl lps us
cvjLps` (`rl.fire` decoded from `(fireKind, fvo, fvc)`, `lps` the `EREC` slice `(po, pc)`, `cvjLps`
the `EREC` slice `(qo, qc)`), the names and levels it reads reading back (`FireCore`); `us` need
not: `ls_node` aborts on a list that is not stored. -/
def RecFireLevelsOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb fireKind fvo fvc po pc us qo qc : Word) (rl : IRecRule) (lps cvjLps : List NIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → HW us →
    hslice? (s₀.mem.arr64 EREC) po.toNat pc.toNat = some lps →
    (∃ ks, lps.mapM (denoteN a₀.store.ns) = some ks) →
    FireCore s₀.mem a₀ fireKind fvo fvc qo qc rl cvjLps →
    CoreSpec p n "rec_fire_levels" [fireKind, fvo, fvc, po, pc, us, qo, qc]
      (recFireLevels rl lps (decI us) cvjLps) decLs s₀ a₀ dn vis fe MM eb

/-- `wscoped_bfast(d, e)` refines `wscopedBFast coreWalkFuel d.toNat e` (a phase-4 walk stub). -/
def WscopedBFastOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb d e : Word), CoreS dn s₀.mem a₀ vis fe MM eb → HW e →
    CoreSpec p n "wscoped_bfast" [d, e] (wscopedBFast coreWalkFuel d.toNat (decE e)) decBool s₀ a₀
      dn vis fe MM eb

/-- `loose_bvars_bounded_fast(4000000000, c, e)` refines `looseBVarsBoundedFast coreWalkFuel c.toNat e`
(a phase-4 walk stub; the first argument is the L walk fuel of lane exprops4's `(f, k, e)`). -/
def LooseBVarsBoundedFastOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb c e : Word), CoreS dn s₀.mem a₀ vis fe MM eb → HW e →
    CoreSpec p n "loose_bvars_bounded_fast" [4000000000, c, e]
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

/-! ## The statements (`CoreSpec` shape; all `sorry` for now)

A knot-calling function quantifies over the knot fuel `F` (`n ≤ F`) and takes `KnotUpTo p n` for the
slots one level down, stating its own `CoreSpec` at L-fuel `n + 1`; the rest need only `CoreS`.
`eta_projs`/`eta_fab_args`/`inst_spine_pins`/`rec_fire_args` return a `List EIdx`, whose decoder
needs the resulting memory (`SpineR`), so they are stated directly rather than through `CoreSpec`'s
`dec : List Word → α`, exactly as `WhnfSpine.lean`'s slice-returning specs are. -/

section specs
variable (p : Prog) (hp : IotaProg p) (hw : WhnfCallees p) (hc : IotaCallees p)

/-- con-leche: `Core.lean:695-699` `isStrLit`. -/
def IsStrLitOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb h : Word), CoreS dn s₀.mem a₀ vis fe MM eb → HW h →
    CoreSpec p n "is_str_lit" [h] (isStrLit (decE h)) decBool s₀ a₀ dn vis fe MM eb

/-- con-leche: `CoreDefs.lean:723-728`/`FEnv.lean:195-197` `towerSlotsAll`. -/
def TowerSlotsAllOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb T nF : Word), CoreS dn s₀.mem a₀ vis fe MM eb → HW T →
    CoreSpec p n "tower_slots_all" [vis, T, nF] (pure (towerSlotsAll fe (decI T) nF.toNat)) decBool s₀ a₀
      dn vis fe MM eb

/-- con-leche: `CoreDefs.lean:793-806`/`:808-810`/`FEnv.lean:199-201` `andRescueSlots`, at
universe arguments that are a stored `const` node's list (`fire_ok`'s hypothesis, `FireOkOK`). -/
def AndRescueSlotsOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb ctor nP us : Word), CoreS dn s₀.mem a₀ vis fe MM eb → HW ctor → HW us →
    (∃ (h : EIdx) (c : NIdx), a₀.store.view h = some (.const c (decI us))) →
    CoreSpec p n "and_rescue_slots" [vis, ctor, nP, us]
      (andRescueSlots fe (decI ctor) nP.toNat (decI us)) decBool s₀ a₀ dn vis fe MM eb

/-- con-leche: `Core.lean:502-663` (the shared scope guard) `fabScopeOk`. -/
def FabScopeOkOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb d fab major : Word), CoreS dn s₀.mem a₀ vis fe MM eb → HW fab → HW major →
    CoreSpec p n "fab_scope_ok" [d, fab, major] (fabScopeOk d.toNat (decE fab) (decE major)) decBool
      s₀ a₀ dn vis fe MM eb

/-- con-leche: `Core.lean:502-663`/`Cached/CoreC.lean:428-453` `majorToCtor`. -/
def MajorToCtorOK (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d rec ro rc major : Word) (rules : List IRecRule),
    n ≤ 2 ^ 62 → CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 →
    HW major → decRules (s₀.mem.arr64 EREC) ro.toNat rc.toNat = some rules →
    CoreSpec p (n + 1) "major_to_ctor" [mode, vis, d, rec, ro, rc, major]
      (majorToCtor (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI rec) rules
        (decE major)) decH s₀ a₀ dn vis fe MM eb

/-- con-leche: none (`ruleRhsAt`'s cache probe). -/
def RuleRhsAtOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb rec ctor po pl rhs us : Word) (lps : List NIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → HW rec → HW ctor → HW rhs → HW us →
    hslice? (s₀.mem.arr64 EREC) po.toNat pl.toNat = some lps →
    CoreSpec p n "rule_rhs_at" [rec, ctor, po, pl, rhs, us]
      (ruleRhsAt (decI rec) (decI ctor) lps (decE rhs) (decI us)) decH s₀ a₀ dn vis fe MM eb

/-- con-leche: none (`constTyAt`'s cache probe). -/
def ConstTyAtOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb nn po pl ty us : Word) (lps : List NIdx), CoreS dn s₀.mem a₀ vis fe MM eb →
    HW nn → HW ty → HW us → hslice? (s₀.mem.arr64 EREC) po.toNat pl.toNat = some lps →
    CoreSpec p n "const_ty_at" [nn, po, pl, ty, us]
      (constTyAt ⟨decI nn, lps, decE ty⟩ (decI us)) decH s₀ a₀ dn vis fe MM eb

end specs

/-! ## Leaf proofs: `find_rule`, `rec_rule_k`, `is_str_lit`, `defeq_list`, `pi_residual`

Pure/read-only, over `EREC` alone (no `CoreS` needed): `find_rule`, `rec_rule_k`. -/

/-- The rule record at `q` decodes, or `f = 0` and there is none: `find_rule`'s result. -/
def decRuleAt (m : Mem) (f q : Word) : Option IRecRule :=
  if f = 0 then none else decRule (m.arr64 EREC) q.toNat

end L.Arena
