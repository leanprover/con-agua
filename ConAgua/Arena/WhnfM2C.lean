module

public import ConAgua.Arena.WhnfBase
public import ConAgua.Arena.WhnfIota

@[expose] public section

/-!
# `major_to_ctor` split into small functions

`WhnfIota.lean`'s `major_to_ctor(mode, vis, d, rec, ro, rc, major)` is the twin's
`ConRon.Arena.majorToCtor` (`Core.lean:1705-1820`), one function of about 120 lines with three
rescue arms. Its L code is split here into pieces the proofs can take one at a time
(`WhnfM2CRefine*.lean`); `major_to_ctor` itself only saves the stack top, calls `m2c_head` and
puts the top back (the K and `And` arms leave the major's type's arguments, and the `And` arm two
projections, on the spine stack; the twin has no stack).

| L | twin part |
|---|---|
| `m2c_head(mode, vis, d, isK, ro, rc, major)` | the constructor test, the single rule, its `ctorInfo` |
| `m2c_ctor(mode, vis, d, isK, ro, cvjP, major)` | the family `T` (the constructor's `induct`), its `indInfo` |
| `m2c_const_view(hh)` | the `view` of a `const` head |
| `m2c_arms(mode, vis, d, isK, ro, cvjP, T, indP, major)` | the dispatch on the recursor's `isK`, then `eta_rescue_table` |
| `m2c_pre(mode, vis, d, major)` | the major's type `tmaj` in whnf, its head `T'.{ust}`, `ust`'s length (all three arms) |
| `m2c_k(…)`, `m2c_k2(…)` | the K arm |
| `m2c_eta(…)`, `m2c_eta2(…)` | the η arm |
| `m2c_and(…)`, `m2c_and2(…)` | the `And` arm |
| `m2c_check(mode, vis, d, tmaj, fab, major)` | the type check and proof irrelevance (K and `And`) |

The record words the arms need are read where the record was found (`m2c_arms`, the start of
`m2c_eta`), before any call that could move the record pool.
-/

namespace L.Arena

/-- The constructor test, the single rule, its constructor's record; then `m2c_ctor`.
con-ron: ConRon/Arena/Core.lean:2102-2211 ConRon.Arena.majorToCtor -/
@[no_expose] def m2cHeadL : FunDecl := lfn (mode, vis, d, isK, ro, rc, major) locals (ok, f, q, r) {
  ok := call is_ctor_app(vis, major);
  if ok != 0 { return major };
  if rc != 1 { return major };
  (f, q) := call env_find(EREC⦃ro⦄, vis);
  if f == 0 { return major };
  if EREC⦃q⦄ != 4 { return major };
  r := call m2c_ctor(mode, vis, d, isK, ro, q, major);
  return r
}

/-- The family of the constructor (`cvjP` its record): the one stored at its `induct` (word `7`),
an inductive; then `m2c_arms`.
con-ron: ConRon/Arena/Core.lean:2102-2211 ConRon.Arena.majorToCtor -/
@[no_expose] def m2cCtorL : FunDecl := lfn (mode, vis, d, isK, ro, cvjP, major)
    locals (T, f, indP, r) {
  T := EREC⦃cvjP + 7⦄;
  (f, indP) := call env_find(T, vis);
  if f == 0 { return major };
  if EREC⦃indP⦄ != 3 { return major };
  r := call m2c_arms(mode, vis, d, isK, ro, cvjP, T, indP, major);
  return r
}

/-- The name and the universe arguments of a `const` handle (the view checks, then the stored
record).
con-ron: ConRon/Arena/Core.lean:2102-2211 ConRon.Arena.majorToCtor -/
@[no_expose] def m2cConstViewL : FunDecl := lfn (hh) locals (t, i) {
  (t, i) := node CONST⟦hh⟧;
  return (CONST⟨t, i⟩.n, CONST⟨t, i⟩.us)
}

/-- The recursor's `isK` and the η rescue's standing condition (`eta_rescue_table`, on the
family's projection table) pick the arm;
the K and `And` arms get the rule's constructor, the constructor's level-parameter count and
parameter count.
con-ron: ConRon/Arena/Core.lean:2102-2211 ConRon.Arena.majorToCtor -/
@[no_expose] def m2cArmsL : FunDecl := lfn (mode, vis, d, isK, ro, cvjP, T, indP, major) locals (tq, er, r) {
  if isK != 0 {
    r := call m2c_k(mode, vis, d, T, major, EREC⦃ro⦄, EREC⦃cvjP + 3⦄, EREC⦃cvjP + 5⦄);
    return r
  };
  tq := call find_table(vis, T);
  er := call eta_rescue_table(tq, EREC⦃ro⦄, cvjP, indP);
  if er != 0 {
    r := call m2c_eta(mode, vis, d, T, indP, er, major);
    return r
  };
  r := call m2c_and(mode, vis, d, T, major, EREC⦃ro⦄, EREC⦃cvjP + 3⦄, EREC⦃cvjP + 5⦄);
  return r
}

/-- The major's type in whnf and its head: `(0, …)` if the head is not a constant, else
`(1, tmaj, T', ust, ustl)` (`ustl` the length of `ust`).
con-ron: ConRon/Arena/Core.lean:2102-2211 ConRon.Arena.majorToCtor -/
@[no_expose] def m2cPreL : FunDecl := lfn (mode, vis, d, major) locals (ioa, tmaj, hh, T2, ust, uo, ul) {
  ioa := call infer_io(mode, vis, d, major);
  tmaj := call whnf(mode, vis, d, ioa);
  hh := call get_app_fn(tmaj);
  if ⟦hh⟧.tag != 3 { return (0, 0, 0, 0, 0) };
  (T2, ust) := call m2c_const_view(hh);
  (uo, ul) := call ls_node(ust);
  return (1, tmaj, T2, ust, ul)
}

/-- The type check and the proof-irrelevance run of a fabricated `fab` (K and `And` arms).
con-ron: ConRon/Arena/Core.lean:2102-2211 ConRon.Arena.majorToCtor -/
@[no_expose] def m2cCheckL : FunDecl := lfn (mode, vis, d, tmaj, fab, major) locals (ok, ioa, ir) {
  ok := call fab_scope_ok(d, fab, major);
  if ok == 0 { return major };
  ioa := call infer_io(mode, vis, d, fab);
  ok := call defeq(mode, vis, d, tmaj, ioa);
  if ok == 0 { return major };
  if mode & 1 == 0 { ir := call proof_irrel(mode, vis, d, fab, major) } else { ir := 1 };
  if ir != 0 { return fab };
  return major
}

/-- The K arm: the major's type's head is the family at the constructor's level count.
con-ron: ConRon/Arena/Core.lean:2102-2211 ConRon.Arena.majorToCtor -/
@[no_expose] def m2cKL : FunDecl := lfn (mode, vis, d, T, major, ctor, lpl, cnP)
    locals (f, tmaj, T2, ust, ustl, r) {
  (f, tmaj, T2, ust, ustl) := call m2c_pre(mode, vis, d, major);
  if f == 0 { return major };
  if T2 != T { return major };
  if lpl != ustl { return major };
  r := call m2c_k2(mode, vis, d, ctor, cnP, tmaj, ust, major);
  return r
}

/-- The K arm's fabrication: the constructor applied to the type's first `cnP` arguments.
con-ron: ConRon/Arena/Core.lean:2102-2211 ConRon.Arena.majorToCtor -/
@[no_expose] def m2cK2L : FunDecl := lfn (mode, vis, d, ctor, cnP, tmaj, ust, major)
    locals (to, tn, hd, fab, r) {
  (to, tn) := call get_app_args(tmaj);
  if tn < cnP { return major };
  hd := call intern_const(ctor, ust);
  fab := call mk_app_n(hd, to, cnP);
  r := call m2c_check(mode, vis, d, tmaj, fab, major);
  return r
}

/-- The η arm (`indP` the family's record, `tq` its projection table plus one): the type's head,
argument count (the table's parameter count) and level count.
con-ron: ConRon/Arena/Core.lean:2102-2211 ConRon.Arena.majorToCtor -/
@[no_expose] def m2cEtaL : FunDecl := lfn (mode, vis, d, T, indP, tq, major)
    locals (pc, ec, ep, ef, f, tmaj, T2, ust, ustl, to, tn, r) {
  pc := EREC⦃indP + 3⦄;
  ec := EREC⦃tq + 5⦄;
  ep := EREC⦃tq + 4⦄;
  ef := EREC⦃tq + 6⦄;
  (f, tmaj, T2, ust, ustl) := call m2c_pre(mode, vis, d, major);
  if f == 0 { return major };
  (to, tn) := call get_app_args(tmaj);
  if T2 != T { return major };
  if tn != ep { return major };
  if ustl != pc { return major };
  r := call m2c_eta2(mode, vis, d, T, indP, ec, ef, to, tn, ust, major);
  return r
}

/-- The η arm's fabrication: the instantiated non-`Prop` test at the use, the stored fact first
(`family_never_zero_at`), the η spine at the table's constructor `ec` and field count `ef`.
con-ron: ConRon/Arena/Core.lean:2102-2211 ConRon.Arena.majorToCtor -/
@[no_expose] def m2cEta2L : FunDecl := lfn (mode, vis, d, T, indP, ec, ef, to, tn, ust, major)
    locals (ok, nz, fo, fn, hd, fab) {
  nz := call family_never_zero_at(mode, vis, indP, ust);
  if nz == 0 { return major };
  (fo, fn) := call eta_fab_args(T, to, tn, major, ef);
  hd := call intern_const(ec, ust);
  fab := call mk_app_n(hd, fo, fn);
  ok := call fab_scope_ok(d, fab, major);
  if ok == 0 { return major };
  return fab
}

/-- The `And` arm: the family is the pinned `And`, its two projection slots ready to fire.
con-ron: ConRon/Arena/Core.lean:2102-2211 ConRon.Arena.majorToCtor -/
@[no_expose] def m2cAndL : FunDecl := lfn (mode, vis, d, T, major, ctor, lpl, cnP)
    locals (an, f, tmaj, T2, ust, ustl, to, tn, ars, r) {
  an := call pin_at(11);
  if T != an { return major };
  (f, tmaj, T2, ust, ustl) := call m2c_pre(mode, vis, d, major);
  if f == 0 { return major };
  (to, tn) := call get_app_args(tmaj);
  ars := call and_rescue_slots(vis, ctor, cnP);
  if T2 != T { return major };
  if tn != cnP { return major };
  if lpl != ustl { return major };
  if ars == 0 { return major };
  r := call m2c_and2(mode, vis, d, ctor, T, tmaj, to, tn, ust, major);
  return r
}

/-- The `And` arm's fabrication: the two projections pushed after the type's arguments (the
slice `(to, tn)` ends at the stack top), the constructor applied to all of them.
con-ron: ConRon/Arena/Core.lean:2102-2211 ConRon.Arena.majorToCtor -/
@[no_expose] def m2cAnd2L : FunDecl := lfn (mode, vis, d, ctor, T, tmaj, to, tn, ust, major)
    locals (p0, p1, hd, fab, r) {
  p0 := call mk_proj(T, 0, major);
  p1 := call mk_proj(T, 1, major);
  if len(SPN.u64) <= to + tn { abort };
  SPN.u64[to + tn] := p0;
  if len(SPN.u64) <= to + tn + 1 { abort };
  SPN.u64[to + tn + 1] := p1;
  CTL.u64[136] := to + tn + 2;
  hd := call intern_const(ctor, ust);
  fab := call mk_app_n(hd, to, tn + 2);
  r := call m2c_check(mode, vis, d, tmaj, fab, major);
  return r
}

/-- What the proofs need of a program: the pieces, at their names. -/
structure M2CProg (p : Prog) : Prop where
  head : p.lookup "m2c_head" = some m2cHeadL
  ctor : p.lookup "m2c_ctor" = some m2cCtorL
  constView : p.lookup "m2c_const_view" = some m2cConstViewL
  arms : p.lookup "m2c_arms" = some m2cArmsL
  pre : p.lookup "m2c_pre" = some m2cPreL
  check : p.lookup "m2c_check" = some m2cCheckL
  k : p.lookup "m2c_k" = some m2cKL
  k2 : p.lookup "m2c_k2" = some m2cK2L
  eta : p.lookup "m2c_eta" = some m2cEtaL
  eta2 : p.lookup "m2c_eta2" = some m2cEta2L
  and_ : p.lookup "m2c_and" = some m2cAndL
  and2 : p.lookup "m2c_and2" = some m2cAnd2L
  fnza : p.lookup "former_never_zero_at" = some formerNeverZeroAtL
  fanza : p.lookup "family_never_zero_at" = some familyNeverZeroAtL
  fsl : p.lookup "former_sort_loop" = some formerSortLoopL
  findTable : FindTableProg p

end L.Arena
