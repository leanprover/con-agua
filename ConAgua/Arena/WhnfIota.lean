module

public import ConAgua.Arena.WhnfCore

@[expose] public section

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
* `find_proj(vis, T, i)`: `IFEnv.findProj?` (`WhnfProj.lean`).
* (formerly `caps_never_zero`, now `former_never_zero` with `lv_spw` on a heap datum)
  `(Level.substPW ks vs pw).isNever` at the family's own level parameters (`po, pc`, an `EREC` name slice), the universe arguments `us` (an `LsIdx`),
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

`str_lit_stored`, `str_lit_ctor`, `inst_list`, `inst_lp` are already `WhnfCallees` stubs
(`WhnfBase.lean`) and are reused via that hypothesis, not redeclared here.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

/-! ## `is_ctor_app(vis, e)`, `is_str_lit(h)` -/

/-- con-leche: `CoreDefs.lean:51-58` `isCtorApp` — the spine's head is a stored constructor. -/
-- con-ron: ConRon/Arena/Core.lean:331-342 ConRon.Arena.isCtorApp
@[no_expose, l_impl ConRon.Arena.isCtorApp]
def isCtorAppL : FunDecl := lfn (vis, e) locals (hh, t, i, c, flag, q) {
  hh := call get_app_fn(e);
  if ⟦hh⟧.tag != 3 { return 0 };
  (t, i) := node CONST⟦hh⟧;
  c := CONST⟨t, i⟩.n;
  (flag, q) := call env_find(c, vis);
  if flag == 0 { return 0 };
  return u64(EREC⦃q⦄ == 4)
}

/-- con-leche: `Core.lean:695-699` `Expr.isStrLit` — the tag, then the literal kind. -/
-- con-ron: ConRon/Arena/Core.lean:2239-2247 ConRon.Arena.isStrLit
@[no_expose, l_impl ConRon.Arena.isStrLit]
def isStrLitL : FunDecl := lfn (h) locals (t, i) {
  if ⟦h⟧.tag != 8 { return 0 };
  (t, i) := node LIT⟦h⟧;
  return u64(LIT⟨t, i⟩.kind == 1)
}

/-! ## `find_rule(ro, rc, c)`

It reads only the 11-word rule records at `(ro, rc)` in `EREC`; it does not touch `AM`. -/

/-- The scan of `find_rule` (a named block, for the proofs). -/
def findRuleLoop : Stmt := lblk (ro, rc, c, i) {
  for i < rc { if EREC⦃ro + 11 * i⦄ == c { return (1, ro + 11 * i) } }
}

/-- con-leche: `Core.lean:777-876` (`iotaRec`'s own lookup) `findRule` — the rule whose
constructor is `c`, as a linear scan of the rule-record slice. -/
-- con-ron: ConRon/Arena/Core.lean:2350-2355 ConRon.Arena.findRule
@[no_expose, l_impl ConRon.Arena.findRule]
def findRuleL : FunDecl := lfn (ro, rc, c) locals (i) {
  i := 0;
  ⟪findRuleLoop⟫;
  return (0, 0)
}

/-! ## Reserved names: a small fusion of `reservedBasisNames` and `List.contains`

Not tagged `@[l_impl]` on its own (it fuses a lookup declaration and a list membership test, as
the house style allows for small dispatchers); `major_to_ctor`'s eta branch is its only caller. -/

/-- con-ron: ConRon/Arena/Core.lean:1549-1553 ConRon.Arena.reservedBasisNames -/
@[no_expose] def reservedContainsL : FunDecl := lfn (x) locals (j) {
  if PINS.u64[0] == 0 { abort };
  j := 0;
  while j < 16 {
    if PINS.u64[55 + j] == x { return 1 };
    j += 1
  };
  return 0
}

/-! ## The family's sort at the use: `former_res_sort`, …, `iota_case3_at`, `eta_rescue_table`

con-leche task #480 removed the install-time data (the rule's `k`/`eta` bits, the capabilities'
`sortZ`): the family's sort zero-ness is computed where it is asked. A stored inductive's record
`p` (kind `3`) has its `IConstantVal` at `p + 1` (level parameters `p + 2`, `p + 3`, type `p + 4`)
and its capabilities at `p + 5` (`eta` `p + 5`, `etaCtor` `p + 6`, `nIdx` `p + 11`, `nparams`
`p + 17`). A zero-ness datum lives on the level heap `LH` (`lv_zero`'s convention), so the core
writes no `EREC` word (`CoreErec.lean`). -/

/-- The head name of a `const` handle (the view checks, then the stored name). -/
-- con-ron: ConRon/Arena/Core.lean:382-395 ConRon.Arena.ctorFamily
@[no_expose] def constNameOfL : FunDecl := lfn (hh) locals (t, i) {
  (t, i) := node CONST⟦hh⟧;
  return CONST⟨t, i⟩.n
}

/-- `former_res_sort(ty)`: the sort a stored type ends in, `(1, u)`, or `(0, 0)`. -/
-- con-ron: ConRon/Arena/Core.lean:344-353 ConRon.Arena.formerResSort
@[no_expose, l_impl ConRon.Arena.formerResSort]
def formerResSortL : FunDecl := lfn (ty) locals (pr, t, i) {
  pr := call pi_result(ty);
  if ⟦pr⟧.tag != 2 { return (0, 0) };
  (t, i) := node SORT⟦pr⟧;
  return (1, SORT⟨t, i⟩.u)
}

/-- `former_def_headed(ty)`: a stored former (type `ty`) that does not show its telescope. -/
-- con-ron: ConRon/Arena/Core.lean:355-360 ConRon.Arena.formerDefHeaded
@[no_expose, l_impl ConRon.Arena.formerDefHeaded]
def formerDefHeadedL : FunDecl := lfn (ty) locals (f, u) {
  (f, u) := call former_res_sort(ty);
  return u64(f == 0)
}

/-- `former_z(ty)`: the family's result-sort zero-ness datum read off its type `ty`, as `lv_zero`
leaves one: `(0, 0, 0)` for `never`, `(1, o, c)` for `ifAllZero` with the names the heap words
`LH[o ‥ o + c)`, pushed above the heap top `CTL[192]` (which stays raised: the caller puts it
back); `ifAllZero []` where the sort is not read. -/
-- con-ron: ConRon/Arena/Core.lean:362-370 ConRon.Arena.formerZ
@[no_expose, l_impl ConRon.Arena.formerZ]
def formerZL : FunDecl := lfn (ty) locals (f, u, t0, z) {
  t0 := CTL.u64[192];
  (f, u) := call former_res_sort(ty);
  if f == 0 { return (1, t0, 0) };
  z := call lv_zero(u);
  if z != 0 { return (0, 0, 0) };
  return (1, t0, CTL.u64[192] - t0)
}

/-- `former_never_zero(p, us)`: the stored inductive `p`'s result sort, at the level instantiation
`us`, is provably nonzero: `Level.substPW ks vs (formerZ cvT)` is `never` (`lv_spw`, the keys the
family's level parameters, an `EREC` slice, the values `us`' `POOL` slice, the datum on the heap);
the heap top put back. -/
-- con-ron: ConRon/Arena/Core.lean:372-380 ConRon.Arena.formerNeverZero
@[no_expose, l_impl ConRon.Arena.formerNeverZero]
def formerNeverZeroL : FunDecl := lfn (p, us) locals (po, pc, t0, w, o, c, vo, vc, x) {
  po := EREC⦃p + 2⦄;
  pc := EREC⦃p + 3⦄;
  t0 := CTL.u64[192];
  (w, o, c) := call former_z(EREC⦃p + 4⦄);
  (vo, vc) := call ls_node(us);
  if w == 0 { CTL.u64[192] := t0; return 1 };
  x := call lv_spw(o, c, po, pc, vo, vc);
  CTL.u64[192] := t0;
  return x
}

/-- `ctor_family(vis, cq)`: the family the constructor record `cq`'s type concludes in, `(1, p)`
with `p` the inductive's record, or `(0, 0)`. -/
-- con-ron: ConRon/Arena/Core.lean:382-395 ConRon.Arena.ctorFamily
@[no_expose, l_impl ConRon.Arena.ctorFamily]
def ctorFamilyL : FunDecl := lfn (vis, cq) locals (pr, hh, T, f, q) {
  pr := call pi_result(EREC⦃cq + 4⦄);
  hh := call get_app_fn(pr);
  if ⟦hh⟧.tag != 3 { return (0, 0) };
  T := call const_name_of(hh);
  (f, q) := call env_find(T, vis);
  if f == 0 { return (0, 0) };
  if EREC⦃q⦄ != 3 { return (0, 0) };
  return (1, q)
}

/-- `former_sort_loop(mode, vis, d, n, e)`: official's walk to a family's sort, `n` binders down,
each reached by `whnf`, then a sort: `(1, u)` or `(0, 0)`. The body is instantiated at a fresh free
variable at depth `d` (`inst_entry`, the memoized `instantiate1`). The depth capacity: `d + 1` must
not wrap. -/
-- con-ron: ConRon/Arena/Core.lean:1958-1982 ConRon.Arena.formerSortLoop
@[no_expose, l_impl ConRon.Arena.formerSortLoop]
def formerSortLoopL : FunDecl := lfn (mode, vis, d, n, e) locals (w, t, i, dom, b, fv, b2, f, u) {
  w := call whnf(mode, vis, d, e);
  if n == 0 {
    if ⟦w⟧.tag != 2 { return (0, 0) };
    (t, i) := node SORT⟦w⟧;
    return (1, SORT⟨t, i⟩.u)
  };
  if ⟦w⟧.tag != 6 { return (0, 0) };
  (t, i) := node FORALL⟦w⟧;
  dom := FORALL⟨t, i⟩.ty;
  b := FORALL⟨t, i⟩.b;
  if d + 1 == 0 { abort };
  fv := call intern_fvar(d, dom);
  b2 := call inst_entry(b, fv, 0);
  (f, u) := call former_sort_loop(mode, vis, d + 1, n - 1, b2);
  return (f, u)
}

/-- `former_never_zero_at(mode, vis, p, us)`: is the family `p`'s sort never zero at the levels
`us`, computed where it is asked: read off a type that ends in a sort (`former_never_zero`), else
walked to by `former_sort_loop` at the use's levels (from depth `0`); no sort reached is `0`. -/
-- con-ron: ConRon/Arena/Core.lean:1984-2001 ConRon.Arena.formerNeverZeroAt
@[no_expose, l_impl ConRon.Arena.formerNeverZeroAt]
def formerNeverZeroAtL : FunDecl := lfn (mode, vis, p, us)
    locals (po, pc, ty, n, f, u, r, ity) {
  po := EREC⦃p + 2⦄;
  pc := EREC⦃p + 3⦄;
  ty := EREC⦃p + 4⦄;
  n := EREC⦃p + 17⦄ + EREC⦃p + 11⦄;
  if n < EREC⦃p + 17⦄ { abort };
  (f, u) := call former_res_sort(ty);
  if f != 0 { r := call former_never_zero(p, us); return r };
  ity := call inst_lp(po, pc, us, ty);
  (f, u) := call former_sort_loop(mode, vis, 0, n, ity);
  if f == 0 { return 0 };
  r := call lv_never(u);
  return r
}

/-- `iota_case3_at(mode, vis, isK, cq, us)`: case 3 of the ι split: the recursor is not K and the
constructor `cq`'s family may be `Prop` at the comparand levels `us` (a family not found, or at
another level count, may). The family is not read at a K recursor. -/
-- con-ron: ConRon/Arena/Core.lean:2003-2021 ConRon.Arena.iotaCase3At
@[no_expose, l_impl ConRon.Arena.iotaCase3At]
def iotaCase3AtL : FunDecl := lfn (mode, vis, isK, cq, us) locals (ok, p, lp, uso, usl, nz) {
  if isK != 0 { return 0 };
  (ok, p) := call ctor_family(vis, cq);
  if ok == 0 { return 1 };
  lp := EREC⦃p + 3⦄;
  (uso, usl) := call ls_node(us);
  if lp != usl { return 1 };
  nz := call former_never_zero_at(mode, vis, p, us);
  return u64(nz == 0)
}

/-- `eta_rescue_table(tq, ctor, cq, p)`: the structure-η rescue's standing condition at use:
`tq` the family's projection table (`find_table`'s answer, `0` for none), `ctor` (its record `cq`)
the table's constructor (word `tq + 5`) of the η family `p` (`eta`) and carrying the family's level
parameters; `And.intro` (pin 48, read only when the chain reaches it) is left to `And`'s rescue.
The table (`tq`) or `0`. -/
-- con-ron: ConRon/Arena/Core.lean:2054-2069 ConRon.Arena.etaRescueTable?
@[no_expose, l_impl ConRon.Arena.etaRescueTable?]
def etaRescueTableL : FunDecl := lfn (tq, ctor, cq, p) locals (r, ai) {
  if tq == 0 { return 0 };
  if EREC⦃p + 5⦄ == 0 { return 0 };
  if EREC⦃tq + 5⦄ != ctor { return 0 };
  r := call er_sl_eq(EREC⦃cq + 2⦄, EREC⦃cq + 3⦄, EREC⦃p + 2⦄, EREC⦃p + 3⦄);
  if r == 0 { return 0 };
  ai := call pin_at(48);
  if ctor == ai { return 0 };
  return tq
}

/-! ## `eta_projs(T, b, nF)`, `eta_fab_args(…)` -/

/-- The projection walk of `eta_projs` (a named block, for the proofs). -/
def etaProjsLoop : Stmt := lblk (T, b, nF, o, j, pr) {
  for j < nF {
    pr := call mk_proj(T, j, b);
    SPN.u64[o + j] := pr
  }
}

/-- con-leche: `CoreDefs.lean:730-735`/`Cached/CoreC.lean:310-317` `etaProjs`/`projNodesGo` — the
`.proj T j b` spine, `j = 0, …, nF - 1`, pushed in order. -/
-- con-ron: ConRon/Arena/Core.lean:1542-1547 ConRon.Arena.etaProjs
-- con-ron: ConRon/Arena/Core.lean:1533-1540 ConRon.Arena.projNodesGo
@[no_expose, l_impl ConRon.Arena.etaProjs ConRon.Arena.projNodesGo]
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
-- con-ron: ConRon/Arena/Core.lean:2023-2029 ConRon.Arena.etaFabArgsE
@[no_expose, l_impl ConRon.Arena.etaFabArgsE]
def etaFabArgsL : FunDecl := lfn (T, to, tn, major, nF) locals (o2, n2) {
  (o2, n2) := call eta_projs(T, major, nF);
  return (to, tn + n2)
}

/-! ## `and_rescue_slots(vis, ctor, nP)` -/

/-- The two-slot walk of `and_rescue_slots` (a named block, for the proofs): each slot stored,
naming the rule's constructor at the major's parameter count, with two fields. -/
def andRescueLoop : Stmt := lblk (vis, ctor, nP, an, j, flag, q) {
  while j < 2 {
    (flag, q) := call find_proj(vis, an, j);
    if flag == 0 { return 0 };
    if EREC⦃q + 6⦄ != ctor { return 0 };
    if EREC⦃q + 5⦄ != nP { return 0 };
    if EREC⦃q + 7⦄ != 2 { return 0 };
    j += 1
  }
}

/-- con-leche: `CoreDefs.lean:793-806`/`:808-810`/`FEnv.lean:199-201` `andRescueSlotsGo` /
`andRescueSlots` / `FEnv.andRescueSlotsF` — the pinned `And`'s two projection slots, ready to
fire. `q`, the table pointer `find_proj` hands back, has `ctor` at `q + 6`, `numParams` at `q + 5`,
`numFields` at `q + 7` (`EnvRec.lean`'s `decTbl`). -/
-- con-ron: ConRon/Arena/Core.lean:2031-2043 ConRon.Arena.andRescueSlotsGo
-- con-ron: ConRon/Arena/Core.lean:2045-2052 ConRon.Arena.andRescueSlots
@[no_expose, l_impl ConRon.Arena.andRescueSlotsGo ConRon.Arena.andRescueSlots]
def andRescueSlotsL : FunDecl := lfn (vis, ctor, nP) locals (an, j, flag, q) {
  an := call pin_at(11);
  j := 0;
  ⟪andRescueLoop⟫;
  return 1
}

/-! ## `fab_scope_ok(d, fab, major)` -/

/-- con-leche: `Core.lean:502-663` (the shared scope guard) `fabScopeOk` — well-scoped, closed
under loose bvars, and every free variable of `fab` is one of `major`'s. All three callees are
phase-4-walk stubs. -/
-- con-ron: ConRon/Arena/Core.lean:2075-2092 ConRon.Arena.fabScopeOk
@[no_expose, l_impl ConRon.Arena.fabScopeOk]
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
-- con-ron: ConRon/Arena/Core.lean:2210-2223 ConRon.Arena.litMajorToCtor
@[no_expose, l_impl ConRon.Arena.litMajorToCtor]
def litMajorToCtorL : FunDecl := lfn (mode, vis, d, h) locals (t, i, kind, sup, c, r) {
  if ⟦h⟧.tag != 8 { r := call lit_to_ctor_if_nat(vis, h); return r };
  (t, i) := node LIT⟦h⟧;
  kind := LIT⟨t, i⟩.kind;
  if kind != 1 { r := call lit_to_ctor_if_nat(vis, h); return r };
  sup := call str_lit_stored(vis);
  if sup == 0 { return h };
  c := call str_lit_ctor(h);
  r := call whnf(mode, vis, d, c);
  return r
}

/-! ## `major_to_ctor(mode, vis, d, rec, isK, ro, rc, major)`

`rec` (the recursor's own name) is unused by the twin (`_recName`) and so by this code too: it is
accepted only to match the twin's argument list. The body is split into small functions
(`WhnfM2C.lean`, `m2c_head` and its callees); this one saves the stack top and puts it back (the
K and `And` arms leave slices on the spine stack; the twin has no stack, so restoring is always
faithful). -/

/-- con-leche: `Core.lean:502-663`/`Cached/CoreC.lean:428-453` `majorToCtor`/`majorToCtorI` — the
stuck-major rescue: K-flagged (the recursor's `isK`), η-capable (`eta_rescue_table`), or the
pinned `And`. No certificate on a fabricated
spine; the K and `And` fabrications keep the type check, and the proof-irrelevance run is a
certificate family (off at `.trusted`). -/
-- con-ron: ConRon/Arena/Core.lean:2094-2208 ConRon.Arena.majorToCtor
@[no_expose, l_impl ConRon.Arena.majorToCtor]
def majorToCtorL : FunDecl := lfn (mode, vis, d, rec, isK, ro, rc, major) locals (top, r) {
  top := CTL.u64[136];
  r := call m2c_head(mode, vis, d, isK, ro, rc, major);
  CTL.u64[136] := top;
  return r
}

/-! ## `prepare_major(mode, vis, d, rec, isK, ro, rc, major)` -/

/-- con-leche: `Core.lean:701-775`/`Cached/CoreC.lean:553-575` `prepareMajor`/`prepareMajorI` — at
a K-flagged recursor (the record's `isK`) the K rescue runs on the raw major; elsewhere the structure rescues run on
the major as found first (a `String` literal skips that attempt), and only if they produce no
constructor is the major head-normalized, its literal converted, and the rescue tried again. -/
-- con-ron: ConRon/Arena/Core.lean:2249-2275 ConRon.Arena.prepareMajor
@[no_expose, l_impl ConRon.Arena.prepareMajor]
def prepareMajorL : FunDecl := lfn (mode, vis, d, rec, isK, ro, rc, major)
    locals (majorK, ok, majorE, major0, major1, res) {
  if isK != 0 {
    majorK := call major_to_ctor(mode, vis, d, rec, isK, ro, rc, major);
    ok := call is_ctor_app(vis, majorK);
    if ok != 0 { res := call lit_major_to_ctor(mode, vis, d, majorK); return res }
    else { return majorK }
  } else {
    ok := call is_str_lit(major);
    if ok != 0 { majorE := major }
    else { majorE := call major_to_ctor(mode, vis, d, rec, isK, ro, rc, major) };
    ok := call is_ctor_app(vis, majorE);
    if ok != 0 { return majorE }
    else {
      major0 := call whnf(mode, vis, d, majorE);
      major1 := call lit_major_to_ctor(mode, vis, d, major0);
      res := call major_to_ctor(mode, vis, d, rec, isK, ro, rc, major1);
      return res
    }
  }
}

/-! ## `pi_residual(e, ao, an)` -/

/-- The telescope walk of `pi_residual` (a named block, for the proofs). -/
def piResidualLoop : Stmt := lblk (e, ao, an, i, t, x, body, b2) {
  for i < an {
    if ⟦e⟧.tag != 6 { return (0, 0) };
    (t, x) := node FORALL⟦e⟧;
    body := FORALL⟨t, x⟩.b;
    b2 := call inst_entry(body, SPN.u64[ao + i], 0);
    e := b2
  }
}

/-- con-leche: `CoreDefs.lean:716-721` `piResidual` — peel a ∀-telescope along an argument
spine `(ao, an)`. -/
-- con-ron: ConRon/Arena/Core.lean:1439-1450 ConRon.Arena.piResidual
@[no_expose, l_impl ConRon.Arena.piResidual]
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
-- con-ron: ConRon/Arena/Core.lean:1452-1459 ConRon.Arena.defEqList
@[no_expose, l_impl ConRon.Arena.defEqList]
def defeqListL : FunDecl := lfn (mode, vis, d, ao, an, bo, bn) locals (i, ok) {
  i := 0;
  ⟪defeqListLoop⟫;
  return u64(an == bn)
}

/-! ## `iota_index_ok(mode, vis, d, mI, rP, cnP, tyCtor, mo, mn, xo, xn)` -/

/-- con-leche: `Core.lean:280-296` `iotaIndexOk` — the canonical-index comparison of a firing
ι redex. The stack top is restored after the `get_app_args` slice (the twin's list is a value; the
refinement specs promise `StackKept`). -/
-- con-ron: ConRon/Arena/Core.lean:1461-1471 ConRon.Arena.iotaIndexOk
@[no_expose, l_impl ConRon.Arena.iotaIndexOk]
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
-- con-ron: ConRon/Arena/Core.lean:1473-1498 ConRon.Arena.proofIrrel
@[no_expose] def proofIrrelHalfL : FunDecl := lfn (mode, vis, d, x)
    locals (ta, tta, hh, t, i, uT, z, ok) {
  ta := call infer_io(mode, vis, d, x);
  tta := call infer_io(mode, vis, d, ta);
  hh := call whnf(mode, vis, d, tta);
  if ⟦hh⟧.tag != 2 { return 0 };
  (t, i) := node SORT⟦hh⟧;
  uT := SORT⟨t, i⟩.u;
  z := call pin_word(53);
  ok := call lvl_eq_c(uT, z);
  if ok == 0 { fail R_RESOURCE_LIMIT_FUEL };
  return ok
}

/-- con-leche: `Core.lean:298-320` `proofIrrel` — proof irrelevance: both sides' types' sorts are
`Prop` (two `proof_irrel_half`s; the second only if the first is a sort, as the twin). -/
-- con-ron: ConRon/Arena/Core.lean:1473-1498 ConRon.Arena.proofIrrel
@[no_expose, l_impl ConRon.Arena.proofIrrel]
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
-- con-ron: ConRon/Arena/Core.lean:213-228 ConRon.Arena.ruleRhsAt
@[no_expose, l_impl ConRon.Arena.ruleRhsAt]
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
-- con-ron: ConRon/Arena/Core.lean:182-195 ConRon.Arena.constTyAt
@[no_expose, l_impl ConRon.Arena.constTyAt]
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
  for i < an {
    e := call inst_entry(e, SPN.u64[ao + i], t);
    t := t - 1
  }
}

/-- con-leche: `ExprOps.lean:1305-1313` `instSpine` — instantiate a telescope-context expression
at an argument spine `(ao, an)`, the fuel-like index `t` decreasing by one per argument. -/
-- con-ron: ConRon/Arena/ExprOps.lean:1386-1392 ConRon.Arena.instSpine
@[no_expose, l_impl ConRon.Arena.instSpine]
def instSpineL : FunDecl := lfn (ao, an, t, e) locals (i) {
  i := 0;
  ⟪instSpineLoop⟫;
  return e
}

/-- The pin walk of `inst_spine_pins` (a named block, for the proofs). Each result is pushed (the top
is raised) as soon as it is stored: the next iteration's callees may use the stack above the top,
and the earlier results must lie below it. -/
def instSpinePinsLoop : Stmt := lblk (po, pl, us, ao, an, rP, pvo, pvc, so, j, q, s) {
  for j < pvc {
    q := call inst_lp(po, pl, us, SPN.u64[pvo + j]);
    s := call inst_spine(ao, an, rP - 1, q);
    SPN.u64[so + j] := s;
    CTL.u64[136] := so + j + 1
  }
}

/-- con-leche: `CoreDefs.lean:908-927` `recFireComparands` (the nested rule's stored parameter
pins, `instSpinePins`) — each pin level-instantiated (`inst_lp`) then spined over the leading
`rP` arguments of the spine `(ao, an)` (`inst_spine`; the twin's `args.take rP`: all `an` of them
when `an < rP`, the index still starting at `rP - 1`), pushed in order. -/
-- con-ron: ConRon/Arena/Core.lean:2301-2311 ConRon.Arena.instSpinePins
@[no_expose, l_impl ConRon.Arena.instSpinePins]
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
or `.levels` rule's the recursor's own leading `cnP` arguments, the stored constructor's parameter
count (`args.take cnP` of the spine `(ao, an)`: all `an` of them when `an < cnP`). -/
-- con-ron: ConRon/Arena/Core.lean:2338-2348 ConRon.Arena.recFireArgs
@[no_expose, l_impl ConRon.Arena.recFireArgs]
def recFireArgsL : FunDecl := lfn (fireKind, pvo, pvc, po, pc, us, ao, an, rP, cnP)
    locals (so, sc) {
  if fireKind == 1 {
    (so, sc) := call inst_spine_pins(po, pc, us, ao, an, rP, pvo, pvc);
    return (so, sc)
  };
  if an < cnP { cnP := an };
  return (ao, cnP)
}

/-! ## `iota_certs_full(mode, vis, d, h, ao, an)` -/

/-- The domain check of `iota_certs_full_forall`: the argument's FULL-grade inferred type is defeq
to the domain `ty` opened by the accumulator `(aco, acn)`. -/
-- con-ron: ConRon/Arena/Core.lean:1398-1430 ConRon.Arena.iotaCertsFullAux
@[no_expose] def iotaCertsFullCheckL : FunDecl := lfn (mode, vis, d, ty, aco, acn, arg) locals (ty2, ta, ok) {
  ty2 := call inst_list(ty, aco, acn, 0);
  ta := call infer(mode, vis, d, arg);
  ok := call defeq(mode, vis, d, ta, ty2);
  return ok
}

/-- The view checks of a handle, by tag (`ViewL.lean`'s `viewOK`): the scratch tier open for a
scratch handle, the index below the tier's count. Aborts on a dangling handle (the twin's `view`
fails there); returns `0`. -/
-- con-ron: ConRon/Arena/Core.lean:1398-1430 ConRon.Arena.iotaCertsFullAux
@[no_expose] def exprViewOkL : FunDecl := lfn (h) locals (t, x, g, c) {
  t := ⟦h⟧.tier;
  x := ⟦h⟧.idx;
  g := ⟦h⟧.tag;
  if t != 0 && CTL.u64[1] == 0 { abort };
  c := 0;
  if g == 0 { c := BVAR⟨t⟩.count } else {
    if g == 1 { c := FVAR⟨t⟩.count } else {
      if g == 2 { c := SORT⟨t⟩.count } else {
        if g == 3 { c := CONST⟨t⟩.count } else {
          if g == 4 { x := ⟦h⟧.aidx; c := APP⟨t⟩.count } else {
            if g == 5 { c := LAM⟨t⟩.count } else {
              if g == 6 { c := FORALL⟨t⟩.count } else {
                if g == 7 { c := LET⟨t⟩.count } else {
                  if g == 8 { c := LIT⟨t⟩.count } else {
                    if g == 9 { c := PROJ⟨t⟩.count } else { abort } } } } } } } } } };
  if c <= x { abort };
  return 0
}

/-- A control word (a one-line reader, so that callers' proofs read it through a call). -/
-- con-ron: ConRon/Arena/Core.lean:1432-1437 ConRon.Arena.iotaCertsFull
@[no_expose] def ctlGetL : FunDecl := lfn (k) locals () { return CTL.u64[k] }

/-- A stack word (a one-line reader, so that callers' proofs read it through a call). -/
-- con-ron: ConRon/Arena/Core.lean:1398-1430 ConRon.Arena.iotaCertsFullAux
@[no_expose] def spnGetL : FunDecl := lfn (k) locals () { return SPN.u64[k] }

/-- The record of a `forallE` handle: its domain and body (the guards of a stored-node read). -/
-- con-ron: ConRon/Arena/Core.lean:1398-1430 ConRon.Arena.iotaCertsFullAux
@[no_expose] def iotaCertsFullPartsL : FunDecl := lfn (h) locals (t, x) {
  (t, x) := node FORALL⟦h⟧;
  return (FORALL⟨t, x⟩.ty, FORALL⟨t, x⟩.b)
}

/-- The `forallE` arm of `iota_certs_full_aux` (split off: the function was too long for `vcgen`):
`h` a `forallE`; certify the argument `SPN[ao + i]` against its instantiated domain, push it on the
accumulator, and continue with the body. -/
-- con-ron: ConRon/Arena/Core.lean:1398-1430 ConRon.Arena.iotaCertsFullAux
@[no_expose] def iotaCertsFullForallL : FunDecl := lfn (mode, vis, d, h, aco, acn, ao, an, i)
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
-- con-ron: ConRon/Arena/Core.lean:1398-1430 ConRon.Arena.iotaCertsFullAux
@[no_expose] def iotaCertsFullFlushL : FunDecl := lfn (mode, vis, d, h, aco, acn, ao, an, i) locals (ty2, dum) {
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
-- con-ron: ConRon/Arena/Core.lean:1398-1430 ConRon.Arena.iotaCertsFullAux
@[no_expose, l_impl ConRon.Arena.iotaCertsFullAux]
def iotaCertsFullAuxL : FunDecl := lfn (mode, vis, d, h, aco, acn, ao, an, i) locals (dum) {
  if i < an {
    if ⟦h⟧.tag == 6 {
      dum := call iota_certs_full_forall(mode, vis, d, h, aco, acn, ao, an, i);
      return dum
    };
    if ⟦h⟧.tag == 0 {
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
-- con-ron: ConRon/Arena/Core.lean:1432-1437 ConRon.Arena.iotaCertsFull
@[no_expose, l_impl ConRon.Arena.iotaCertsFull]
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
-- con-ron: ConRon/Arena/Core.lean:2357-2444 ConRon.Arena.iotaRecAt
@[no_expose, l_impl ConRon.Arena.iotaRecAt]
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
  constNameOf : p.lookup "const_name_of" = some constNameOfL
  formerResSort : p.lookup "former_res_sort" = some formerResSortL
  formerDefHeaded : p.lookup "former_def_headed" = some formerDefHeadedL
  formerZ : p.lookup "former_z" = some formerZL
  formerNeverZero : p.lookup "former_never_zero" = some formerNeverZeroL
  ctorFamily : p.lookup "ctor_family" = some ctorFamilyL
  formerSortLoop : p.lookup "former_sort_loop" = some formerSortLoopL
  formerNeverZeroAt : p.lookup "former_never_zero_at" = some formerNeverZeroAtL
  iotaCase3At : p.lookup "iota_case3_at" = some iotaCase3AtL
  etaRescueTable : p.lookup "eta_rescue_table" = some etaRescueTableL
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

/-- **The fire datum at its words, reading back**: kind `0` plain (the constructor's level
parameters the `EREC` name slice `(qo, qc)`, their names reading back), else nested or levels (the
stored levels the `EREC` slice `(fvo, fvc)`, reading back). -/
def FireCore (m : Mem) (a : AState) (fk fvo fvc qo qc : Word) (rl : IRecRule) (cvjLps : List NIdx) :
    Prop :=
  (fk = 0 ∧ rl.fire = .plain ∧ hslice? (erecP m) qo.toNat qc.toNat = some cvjLps ∧
      ∃ ks, cvjLps.mapM (denoteN a.store.ns) = some ks) ∨
    (fk ≠ 0 ∧ ∃ lvls, (rl.fire = .levels lvls ∨ ∃ pins, rl.fire = .nested lvls pins) ∧
      hslice? (erecP m) fvo.toNat fvc.toNat = some lvls ∧
      ∀ u ∈ lvls, ∃ L, denoteL a.store.ls u = some L)

/-- **Where a firing rule comes from**: a rule of a recursor of the environment (whose level
parameters are `lps`), and a constructor of the environment. State-free, so it passes down the
ι block's calls; the readbacks follow at any state from `StoreDen` (`constLps`, `recRules`). -/
def FireEnv (fe : IFEnv) (lps : List NIdx) (rule : IRecRule) (cvj : IConstantVal) : Prop :=
  (∃ c cv mI rP isK rules, fe.find? c = some (.recInfo cv mI rP isK rules) ∧ cv.levelParams = lps ∧
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
    hslice? (erecP s₀.mem) po.toNat pc.toNat = some lps →
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
  recFireLevels : RecFireLevelsOK p
  wscopedBFast : WscopedBFastOK p
  looseBVarsBoundedFast : LooseBVarsBoundedFastOK p
  leafGuard : LeafGuardOK p
  litToCtorIfNat : LitToCtorIfNatOK p

/-! ## The statements (`CoreSpec` shape; proved in `WhnfIotaRefine*.lean`)

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

/-- con-leche: `CoreDefs.lean:1105-1119`/`FEnv.lean:179-181` `andRescueSlots`. -/
def AndRescueSlotsOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb ctor nP : Word), CoreS dn s₀.mem a₀ vis fe MM eb → HW ctor →
    CoreSpec p n "and_rescue_slots" [vis, ctor, nP]
      (andRescueSlots fe (decI ctor) nP.toNat) decBool s₀ a₀ dn vis fe MM eb

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
    (MM : ModeMaps) (eb mode d rec isK ro rc major : Word) (rules : List IRecRule),
    n ≤ 2 ^ 62 → CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 →
    HW major → decRules (erecP s₀.mem) ro.toNat rc.toNat = some rules →
    CoreSpec p (n + 1) "major_to_ctor" [mode, vis, d, rec, isK, ro, rc, major]
      (majorToCtor (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI rec)
        (isK != 0) rules (decE major)) decH s₀ a₀ dn vis fe MM eb

/-- con-leche: none (`ruleRhsAt`'s cache probe). -/
def RuleRhsAtOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb rec ctor po pl rhs us : Word) (lps : List NIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → HW rec → HW ctor → HW rhs → HW us →
    hslice? (erecP s₀.mem) po.toNat pl.toNat = some lps →
    CoreSpec p n "rule_rhs_at" [rec, ctor, po, pl, rhs, us]
      (ruleRhsAt (decI rec) (decI ctor) lps (decE rhs) (decI us)) decH s₀ a₀ dn vis fe MM eb

/-- con-leche: none (`constTyAt`'s cache probe). -/
def ConstTyAtOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb nn po pl ty us : Word) (lps : List NIdx), CoreS dn s₀.mem a₀ vis fe MM eb →
    HW nn → HW ty → HW us → hslice? (erecP s₀.mem) po.toNat pl.toNat = some lps →
    CoreSpec p n "const_ty_at" [nn, po, pl, ty, us]
      (constTyAt ⟨decI nn, lps, decE ty⟩ (decI us)) decH s₀ a₀ dn vis fe MM eb

end specs

/-! ## Leaf proofs: `find_rule`, `is_str_lit`, `defeq_list`, `pi_residual`

Pure/read-only, over `EREC` alone (no `CoreS` needed): `find_rule`. -/

/-- The rule record at `q` decodes, or `f = 0` and there is none: `find_rule`'s result. -/
def decRuleAt (m : Mem) (f q : Word) : Option IRecRule :=
  if f = 0 then none else decRule (erecP m) q.toNat

end L.Arena
