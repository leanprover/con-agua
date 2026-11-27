module

public import ConAgua.Arena.DeclArmsNat
public import ConAgua.Arena.BasisL
public import ConAgua.Arena.IndProg
meta import ConAgua.Arena.DeclArmsNat
meta import ConAgua.Arena.BasisL
meta import ConAgua.Arena.IndProg

@[expose] public section

/-!
# `checkDeclKind`'s one-constant arms in L, part 3: the arms (lane `decls2`)

The `.axiomDecl`, `.defnDecl`, `.thmDecl`, `.opaqueDecl` and `.quotDecl` arms of the twin's
`checkDeclKind` and its gates (`vendor/con-ron/ConRon/Arena/CheckDecl.lean`: `checkStructuralNatPin`,
`checkStructuralNatPinAtFe2`) and what they call: `checkConstantVal` (`CheckerBase.lean`),
`valueGuards`, `checkDefnVal`/`checkThmVal`/`checkOpaqueVal`, `stdAxiomOk`, `trustCompilerOk`,
`reduceStoredOk`, `reduceElemOk`, `ofReduceAxOk`, `reducePinGuard`, `checkReducePinPre`,
`checkReducePin`, `installBasisDecl`, `checkQuotRecord` (`DeclCheck.lean`),
`IConstantVal.matchesPin` (`StdAxioms.lean`), the reduce-operation helpers (`TrustAxioms.lean`).
`DeclStep.lean`'s `check_decl_kind(i, vis, bo, bl)` dispatches record `i` of `DECL` (`Front/StateDR.lean`'s
`DeclAt`: kind `1` axiom, `2` definition, `3` theorem, `4` opaque, `5` quotient) to
`check_decl_axiom`, `check_decl_defn`, `check_decl_thm`, `check_decl_opaque`, `check_decl_quot`
(each `(i, vis)` → `vis'`).

* Every arm builds the record's constant in `EREC` first (`erec_ci`, `DeclStep.lean`): the value
  `cv` is at `p + CI.cv`, the value at `p + CI.defnValue`, a definition's hint at `p + CI.defnHint`; its kind is
  the one the twin's value check returns (`defnInfo`, `thmInfo`, `axiomInfo` for an opaque). The
  value checks return it unpushed, the gates push it temporarily (`env_row_get`, `env_push`,
  `env_pop_temp`: the twin's `fe.idx[n]?`, `fe.push ci`, `popTemp`), the arm pushes last.
* A quotient record's kind is `DECL` word 7 (`1` type, `2` ctor, `3` lift, else ind); L passes
  its slot (`QuotKind.slot`: `0`‥`3`, `4` sound) as the `QuotKind` word.
* The con-leche values (`iffA`, …, the basis blocks, the reduce pins) come from the ROM
  (`rom_ci`, `rom_cv`, `rom_basis_decls`, …, `DeclArmsNat.lean`'s `romStubs`); a pinned name is a
  `pin_at` read.
* `unresolvedConstsErrorL` (which error a failed `constsResolve` reports) is not translated: both
  of its answers are a `fail`, an `abort` here, and so are its walks' failures.
-/

namespace L.Ind

open L.Arena
open L.Front (DECL)

/-! ## The constant check -/

/-- `check_constant_val(vis, q, allowOp, allowReduce, allowSorry)`: `checkConstantVal fe cv allowOp
allowReduce allowSorry` (`q` the constant value): the fresh name, a certified operation's name
only where `allowOp`, a compiler-trust name (`reduceOpNames`, pin slots `43`, `44`) only where
`allowReduce`, `sorryAx`'s (pin slot `13`) only where `allowSorry`, a
literal's name only at its shape (`lit_shape_ok` of a fresh `axiomInfo` record of `cv`), the
universe parameters, the type's guards, then the type's sort. -/
-- con-ron: ConRon/Arena/CheckerBase.lean:242-282 ConRon.Arena.checkConstantVal
@[no_expose, l_impl ConRon.Arena.checkConstantVal]
def checkConstantValL : FunDecl :=
    lfn (vis, q, allowOp, allowReduce, allowSorry) locals (n, t, f, r, c, a, ez, o, l, d, b, h, u, st) {
  n := EREC⦃q⦄;
  t := EREC⦃q + ⟪CV.type⟫⦄;
  (f, r) := call env_find(n, vis);
  if f != 0 { fail R_DUPLICATE_DECLARATION_2 };
  c := call nat_op_name(n);
  if c != 0 && allowOp == 0 { fail R_A_CERTIFIED_NAT };
  a := call pin_at(43);
  b := call pin_at(44);
  if n == a || n == b {
    if allowReduce == 0 { fail R_A_COMPILER_TRUST }
  };
  a := call pin_at(13);
  if n == a && allowSorry == 0 { fail R_THE_TOLERATED_AXIOM };
  a := call erec_alloc(⟪CI.axiomSize⟫);
  ez := call erec_put(a, 0);
  ez := call erec_put(a + ⟪CI.cv + CV.name⟫, n);
  ez := call erec_put(a + ⟪CI.cv + CV.lpsOff⟫, EREC⦃q + ⟪CV.lpsOff⟫⦄);
  ez := call erec_put(a + ⟪CI.cv + CV.lpsLen⟫, EREC⦃q + ⟪CV.lpsLen⟫⦄);
  ez := call erec_put(a + ⟪CI.cv + CV.type⟫, t);
  c := call lit_shape_ok(a);
  if c == 0 { fail R_A_DECLARATION_AT };
  (o, l) := call cv_lps(q);
  d := call sl_nodup(o, l);
  if d == 0 { fail R_DUPLICATE_UNIVERSE_PARAMETERS };
  b := call loose_bvars_bounded_fast(4000000000, 0, t);
  if b == 0 { fail R_LOOSE_BOUND_VARIABLE };
  h := call has_fvar_fast(4000000000, t);
  if h != 0 { fail R_UNEXPECTED_FREE_VARIABLE };
  a := call all_level_params_defined(o, l, t);
  if a == 0 { fail R_UNDECLARED_UNIVERSE_PARAMETER };
  c := call consts_resolve_ffast(vis, t);
  if c == 0 { u := call unresolved_consts_error(vis, t, 0); abort };
  st := call infer_type_core(vis, 0, t);
  u := call ensure_sort_core(vis, 0, st);
  return 0
}

/-! ## The three value kinds

Each takes the arm's constant record `p` (built by `erec_ci` with the kind the twin returns:
`defnInfo cv value hint`, `thmInfo cv`, `axiomInfo cv`; the value at `p + CI.defnValue` either way) and
returns it unpushed: the arm runs its pinned gates and pushes last. -/

/-- `value_guards(vis, q, v)`: `valueGuards fe cv v` (`q` the constant value): no loose bound
variable, no free variable, declared universe parameters, resolving constants. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:821-837 ConRon.Arena.valueGuards
@[no_expose, l_impl ConRon.Arena.valueGuards]
def valueGuardsL : FunDecl := lfn (vis, q, v) locals (o, l, b, h, a, c, u) {
  b := call loose_bvars_bounded_fast(4000000000, 0, v);
  if b == 0 { fail R_LOOSE_BOUND_VARIABLE_IN };
  h := call has_fvar_fast(4000000000, v);
  if h != 0 { fail R_UNEXPECTED_FREE_VARIABLE_IN };
  (o, l) := call cv_lps(q);
  a := call all_level_params_defined(o, l, v);
  if a == 0 { fail R_UNDECLARED_UNIVERSE_PARAMETER_IN_VALUE };
  c := call consts_resolve_ffast(vis, v);
  if c == 0 { u := call unresolved_consts_error(vis, v, 1); abort };
  return 0
}

/-- `check_defn_val(vis, p)`: `checkDefnVal fe cv v hint`: the value's guards, its type against the
declared one; returns the record. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:839-852 ConRon.Arena.checkDefnVal
@[no_expose, l_impl ConRon.Arena.checkDefnVal]
def checkDefnValL : FunDecl := lfn (vis, p) locals (v, t, z, vt, d) {
  v := EREC⦃p + ⟪CI.defnValue⟫⦄;
  t := EREC⦃p + ⟪CI.cv + CV.type⟫⦄;
  z := call value_guards(vis, p + ⟪CI.cv⟫, v);
  vt := call infer_type_core(vis, 0, v);
  d := call is_def_eq_core(vis, 0, vt, t);
  if d == 0 { fail R_TYPE_MISMATCH_IN };
  return p
}

/-- `check_thm_val(vis, p)`: `checkThmVal`: the type a proposition, the value's guards and type;
returns the record (stored by its statement). -/
-- con-ron: ConRon/Arena/DeclCheck.lean:854-872 ConRon.Arena.checkThmVal
@[no_expose, l_impl ConRon.Arena.checkThmVal]
def checkThmValL : FunDecl := lfn (vis, p) locals (v, t, st, u, zr, e, z, vt, d) {
  v := EREC⦃p + ⟪CI.defnValue⟫⦄;
  t := EREC⦃p + ⟪CI.cv + CV.type⟫⦄;
  st := call infer_type_core(vis, 0, t);
  u := call ensure_sort_core(vis, 0, st);
  zr := call pin_word(53);
  e := call lvl_eq_fueled(u, zr);
  if e == 0 { fail R_TYPE_OF_THEOREM };
  z := call value_guards(vis, p + ⟪CI.cv⟫, v);
  vt := call infer_type_core(vis, 0, v);
  d := call is_def_eq_core(vis, 0, vt, t);
  if d == 0 { fail R_TYPE_MISMATCH_IN_THEOREM };
  return p
}

/-- `check_opaque_val(vis, p)`: `checkOpaqueVal`: `check_defn_val`'s text (the record `p` is an
`axiomInfo`). -/
-- con-ron: ConRon/Arena/DeclCheck.lean:874-886 ConRon.Arena.checkOpaqueVal
@[no_expose, l_impl ConRon.Arena.checkOpaqueVal]
def checkOpaqueValL : FunDecl := lfn (vis, p) locals (v, t, z, vt, d) {
  v := EREC⦃p + ⟪CI.defnValue⟫⦄;
  t := EREC⦃p + ⟪CI.cv + CV.type⟫⦄;
  z := call value_guards(vis, p + ⟪CI.cv⟫, v);
  vt := call infer_type_core(vis, 0, v);
  d := call is_def_eq_core(vis, 0, vt, t);
  if d == 0 { fail R_TYPE_MISMATCH_IN_OPAQUE };
  return p
}

/-! ## The standard axioms -/

/-- `matches_pin(q, pin)`: `IConstantVal.matchesPin`: name, level parameters and type equal. -/
-- con-ron: ConRon/Arena/StdAxioms.lean:55-63 ConRon.Arena.IConstantVal.matchesPin
@[no_expose, l_impl ConRon.Arena.IConstantVal.matchesPin]
def matchesPinL : FunDecl := lfn (q, pin) locals (e) {
  e := call cv_eq(q, pin);
  return e
}

/-- `find_pinned(vis, n, k, a, b, id)`: the stored constant `n` is of kind `k` (an inductive
`3`; a constructor `4` or a recursor `5` with the two counts `a`, `b` at `CI.ctorNparams`, `CI.ctorNfields`, which are a recursor's `CI.recMajor`, `CI.recPrefix`), and its
constant value matches the pin `rom_ci(id)`'s. One clause of `stdAxiomOk`'s chains. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:52-97 ConRon.Arena.stdAxiomOk
@[no_expose] def findPinned : FunDecl := lfn (vis, n, k, a, b, id) locals (f, r, p, q, e) {
  (f, r) := call env_find(n, vis);
  if f == 0 { return 0 };
  if EREC⦃r⦄ != k { return 0 };
  if k != 3 {
    if EREC⦃r + ⟪CI.ctorNparams⟫⦄ != a || EREC⦃r + ⟪CI.ctorNfields⟫⦄ != b { return 0 }
  };
  p := call rom_ci(id);
  q := call ci_to_cv(p);
  e := call matches_pin(r + ⟪CI.cv⟫, q);
  return e
}

/-- `std_ax_family(vis, q, s1, s2, s3, i1, i2, i3, c2, c3, cvid)`: one family of `stdAxiomOk`: the
inductive at pin slot `s1` matching `rom_ci(i1)`, its constructor (`s2`, counts `c2`, `rom_ci(i2)`),
its recursor (`s3`, counts `c3`, `rom_ci(i3)`), then the axiom `q` against `rom_cv(cvid)`. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:52-97 ConRon.Arena.stdAxiomOk
@[no_expose] def stdAxFamily : FunDecl :=
    lfn (vis, q, s1, s2, s3, i1, i2, i3, c2, c3, cvid) locals (n, e, pa) {
  n := call pin_at(s1);
  e := call find_pinned(vis, n, 3, 0, 0, i1);
  if e == 0 { return 0 };
  n := call pin_at(s2);
  e := call find_pinned(vis, n, 4, c2, c2, i2);
  if e == 0 { return 0 };
  n := call pin_at(s3);
  e := call find_pinned(vis, n, 5, c3, c3, i3);
  if e == 0 { return 0 };
  pa := call rom_cv(cvid);
  e := call matches_pin(q, pa);
  return e
}

/-- `std_axiom_ok(vis, q)`: `stdAxiomOk`: `propext` over the pinned `Eq` and a standard `Iff`
family, or `Classical.choice` over a standard `Nonempty` family (the `choice` name read only past
the `propext` test). -/
-- con-ron: ConRon/Arena/DeclCheck.lean:52-97 ConRon.Arena.stdAxiomOk
@[no_expose, l_impl ConRon.Arena.stdAxiomOk]
def stdAxiomOkL : FunDecl := lfn (vis, q) locals (pn, nm, e, cn) {
  pn := call pin_at(32);
  nm := EREC⦃q⦄;
  if nm == pn {
    e := call eq_stored(vis);
    if e == 0 { return 0 };
    e := call std_ax_family(vis, q, 34, 35, 36, 1, 2, 3, 2, 4, 0);
    return e
  };
  cn := call pin_at(33);
  if nm == cn {
    e := call std_ax_family(vis, q, 37, 38, 39, 4, 5, 6, 1, 3, 1);
    return e
  };
  return 0
}

/-! ## The compiler-trust family -/

/-- `find_pinned_cv(vis, n, k, id)`: the stored constant `n` is of kind `k` (an inductive `3`, or
a constructor `4` with no parameters and no fields), its constant value matching `rom_cv(id)`.
One clause of `trustCompilerOk`. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:101-114 ConRon.Arena.trustCompilerOk
@[no_expose] def findPinnedCv : FunDecl := lfn (vis, n, k, id) locals (f, r, p, e) {
  (f, r) := call env_find(n, vis);
  if f == 0 { return 0 };
  if EREC⦃r⦄ != k { return 0 };
  if k == 4 {
    if EREC⦃r + ⟪CI.ctorNparams⟫⦄ != 0 || EREC⦃r + ⟪CI.ctorNfields⟫⦄ != 0 { return 0 }
  };
  p := call rom_cv(id);
  e := call matches_pin(r + ⟪CI.cv⟫, p);
  return e
}

/-- `trust_compiler_ok(vis, q)`: `trustCompilerOk`: the `True` family stored with the pinned
shapes, the axiom's type the pin's. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:101-114 ConRon.Arena.trustCompilerOk
@[no_expose, l_impl ConRon.Arena.trustCompilerOk]
def trustCompilerOkL : FunDecl := lfn (vis, q) locals (n, e, p) {
  n := call pin_at(40);
  e := call find_pinned_cv(vis, n, 3, 2);
  if e == 0 { return 0 };
  n := call pin_at(41);
  e := call find_pinned_cv(vis, n, 4, 3);
  if e == 0 { return 0 };
  p := call rom_cv(4);
  e := call matches_pin(q, p);
  return e
}

/-- `reduce_op_cv_a(c)`: the pinned type of the reduce operation `c`. -/
-- con-ron: ConRon/Arena/TrustAxioms.lean:91-95 ConRon.Arena.reduceOpCvA
@[no_expose, l_impl ConRon.Arena.reduceOpCvA]
def reduceOpCvAL : FunDecl := lfn (c) locals (rn, p) {
  rn := call pin_at(43);
  if c == rn { p := call rom_cv(6); return p };
  p := call rom_cv(7);
  return p
}

/-- `reduce_stored_ok(vis, c)`: `c` is stored as a checked opaque (`axiomInfo`) of the pinned
type. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:116-123 ConRon.Arena.reduceStoredOk
@[no_expose, l_impl ConRon.Arena.reduceStoredOk]
def reduceStoredOkL : FunDecl := lfn (vis, c) locals (f, r, p, e) {
  (f, r) := call env_find(c, vis);
  if f == 0 { return 0 };
  if EREC⦃r⦄ != 0 { return 0 };
  p := call reduce_op_cv_a(c);
  e := call matches_pin(r + ⟪CI.cv⟫, p);
  return e
}

/-- `reduce_elem_ok(vis, c)`: a stored `Nat` inductive at the pin's constant value (for
`reduceNat`), or a standard `Bool`. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:125-139 ConRon.Arena.reduceElemOk
@[no_expose, l_impl ConRon.Arena.reduceElemOk]
def reduceElemOkL : FunDecl := lfn (vis, c) locals (rn, nn, f, r, na, e, bn, p) {
  rn := call pin_at(43);
  if c == rn {
    nn := call pin_at(1);
    (f, r) := call env_find(nn, vis);
    if f == 0 { return 0 };
    if EREC⦃r⦄ != 3 { return 0 };
    na := call rom_ci(0);
    e := call matches_pin(r + ⟪CI.cv⟫, na + ⟪CI.cv⟫);
    return e
  };
  bn := call pin_at(29);
  (f, r) := call env_find(bn, vis);
  if f == 0 { return 0 };
  if EREC⦃r⦄ != 3 { return 0 };
  p := call rom_cv(5);
  e := call matches_pin(r + ⟪CI.cv⟫, p);
  return e
}

/-- `of_reduce_op(n)`: the reduce operation an `ofReduce*` axiom speaks about. -/
-- con-ron: ConRon/Arena/TrustAxioms.lean:52-57 ConRon.Arena.ofReduceOp
@[no_expose, l_impl ConRon.Arena.ofReduceOp]
def ofReduceOpL : FunDecl := lfn (n) locals (orn, r) {
  orn := call pin_at(45);
  if n == orn { r := call pin_at(43); return r };
  r := call pin_at(44);
  return r
}

/-- `of_reduce_pin_a(n)`: the pin an `ofReduce*` axiom is matched against. -/
-- con-ron: ConRon/Arena/TrustAxioms.lean:97-101 ConRon.Arena.ofReducePinA
@[no_expose, l_impl ConRon.Arena.ofReducePinA]
def ofReducePinAL : FunDecl := lfn (n) locals (orn, p) {
  orn := call pin_at(45);
  if n == orn { p := call rom_cv(8); return p };
  p := call rom_cv(9);
  return p
}

/-- `of_reduce_ax_ok(vis, q)`: `ofReduceAxOk`: the pinned `Eq`, the element inductive, the
stored reduce opaque, the pin. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:141-150 ConRon.Arena.ofReduceAxOk
@[no_expose, l_impl ConRon.Arena.ofReduceAxOk]
def ofReduceAxOkL : FunDecl := lfn (vis, q) locals (nm, c, e, p) {
  nm := EREC⦃q⦄;
  c := call of_reduce_op(nm);
  e := call eq_stored(vis);
  if e == 0 { return 0 };
  e := call reduce_elem_ok(vis, c);
  if e == 0 { return 0 };
  e := call reduce_stored_ok(vis, c);
  if e == 0 { return 0 };
  p := call of_reduce_pin_a(nm);
  e := call matches_pin(q, p);
  return e
}

/-! ## The reduce-operation install pin -/

/-- `reduce_decl_pin(c)`: the pinned defining expression of the reduce operation `c`. -/
-- con-ron: ConRon/Arena/TrustAxioms.lean:113-117 ConRon.Arena.reduceDeclPin
@[no_expose, l_impl ConRon.Arena.reduceDeclPin]
def reduceDeclPinL : FunDecl := lfn (c) locals (rn, e) {
  rn := call pin_at(43);
  if c == rn { e := call rom_expr_pin(0); return e };
  e := call rom_expr_pin(1);
  return e
}

/-- `reduce_cert_var(c)`: `fvar 0` at the element type (`Nat` for `reduceNat`, else `Bool`). -/
-- con-ron: ConRon/Arena/TrustAxioms.lean:119-122 ConRon.Arena.reduceCertVar
-- con-ron: ConRon/Arena/TrustAxioms.lean:76-79 ConRon.Arena.reduceElemTy
-- con-ron: ConRon/Arena/TrustAxioms.lean:70-74 ConRon.Arena.reduceElemName
@[no_expose, l_impl ConRon.Arena.reduceCertVar ConRon.Arena.reduceElemTy ConRon.Arena.reduceElemName]
def reduceCertVarL : FunDecl := lfn (c) locals (rn, n, t, r) {
  rn := call pin_at(43);
  if c == rn { n := call pin_at(1) } else { n := call pin_at(29) };
  t := call const_e(n);
  if 4294967296 <= t { abort };
  r := call intern_fvar(0, t);
  return r
}

/-- `reduce_pin_guard(vis, c)`: the syntactic guards on the reduce pin. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:152-161 ConRon.Arena.reducePinGuard
@[no_expose, l_impl ConRon.Arena.reducePinGuard]
def reducePinGuardL : FunDecl := lfn (vis, c) locals (p, b) {
  p := call reduce_decl_pin(c);
  b := call loose_bvars_bounded_fast(4000000000, 0, p);
  if b == 0 { return 0 };
  b := call has_fvar_fast(4000000000, p);
  if b != 0 { return 0 };
  b := call all_level_params_defined(0, 0, p);
  if b == 0 { return 0 };
  b := call consts_resolve_ffast(vis, p);
  return b
}

/-- `check_reduce_pin_pre(vis, c, v)`: `checkReducePinPre` at the view without the opaque: the
element guard, the pin's guards, the value against the pin, the identity certificate `v x ≡ x`
(its failure an `.internal` error: `abort`). -/
-- con-ron: ConRon/Arena/DeclCheck.lean:747-772 ConRon.Arena.checkReducePinPre
@[no_expose, l_impl ConRon.Arena.checkReducePinPre]
def checkReducePinPreL : FunDecl := lfn (vis, c, v) locals (e, pa, x, ax) {
  e := call reduce_elem_ok(vis, c);
  if e == 0 { fail R_UNSUPPORTED_COMPILER_TRUST_OPAQUE };
  e := call reduce_pin_guard(vis, c);
  if e == 0 { fail R_UNSUPPORTED_COMPILER_TRUST_OPAQUE_SPELLING_PIN };
  pa := call reduce_decl_pin(c);
  e := call is_def_eq_core(vis, 0, v, pa);
  if e == 0 { fail R_UNSUPPORTED_COMPILER_TRUST_OPAQUE_SPELLING };
  x := call reduce_cert_var(c);
  if 4294967296 <= x { abort };
  ax := call mk_app(v, x);
  e := call is_def_eq_core(vis, 1, ax, x);
  if e == 0 { abort };
  return 0
}

/-- `check_reduce_pin(vis, p, c, v)`: `checkReducePin`: the record `p` pushed for the one read at
the extended view (the stored constant's type, `reduce_stored_ok`) and popped (`env_pop_temp`),
the literal flags set back (`env_set_flags`), then `check_reduce_pin_pre` at `vis`; returns the
view. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:774-794 ConRon.Arena.checkReducePin
@[no_expose, l_impl ConRon.Arena.checkReducePin]
def checkReducePinL : FunDecl := lfn (vis, p, c, v) locals (rc, rq, fn, fs, w, st, v2, z) {
  (rc, rq) := call env_row_get(c);
  fn := CTL.u64[160];
  fs := CTL.u64[161];
  w := call env_push(vis, p);
  st := call reduce_stored_ok(w, c);
  v2 := call env_pop_temp(w, c, rc, rq);
  z := call env_set_flags(fn, fs);
  if st == 0 { fail R_UNSUPPORTED_COMPILER_TRUST_OPAQUE };
  z := call check_reduce_pin_pre(v2, c, v);
  return v2
}

/-! ## The quotient records -/

/-- `install_basis_decl(vis, p)`: the constant record `p` installed, duplicate-checked. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:890-897 ConRon.Arena.installBasisDecl
@[no_expose, l_impl ConRon.Arena.installBasisDecl]
def installBasisDeclL : FunDecl := lfn (vis, p) locals (n, f, r, w) {
  n := EREC⦃p + ⟪CI.cv + CV.name⟫⦄;
  (f, r) := call env_find(n, vis);
  if f != 0 { fail R_DUPLICATE_DECLARATION_2 };
  w := call env_push(vis, p);
  return w
}

/-- `check_quot_record(vis, k, q)`: `checkQuotRecord fe k cv` (`k` the slot, `QuotKind.slot`: `0`
type, `1` ctor, `2` lift, `3` ind, `4` sound; `q` the constant value): compared with the slot's
pin, the slots it needs stored, installed at its own names (`quot_at`). A `quot` record off its
pin, or before the slots it needs, is a reject; a `Quot.sound` off its pin is a decline. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:899-913 ConRon.Arena.checkQuotRecord
@[no_expose, l_impl ConRon.Arena.checkQuotRecord]
def checkQuotRecordL : FunDecl := lfn (vis, k, q) locals (e, r, w) {
  e := call quot_pin_hit(k, q);
  if e == 0 {
    if k == 4 { fail R_QUOTIENT_SOUNDNESS_AXIOM };
    fail R_QUOTIENT_DECLARATION_MISMATCH
  };
  e := call quot_preds_ok(vis, k);
  if e == 0 { fail R_QUOTIENT_DECLARATION_BEFORE };
  r := call quot_at(k, q);
  w := call install_basis_decl(vis, r);
  return w
}

/-! ## The arms -/

/-- `check_decl_axiom(i, vis)`: `checkDeclKind`'s `.axiomDecl` arm on record `i`: `Quot.sound` is the
quotient package's record (`check_quot_record`, slot `4`); else the constant check and the five
recognised axioms: the standard two, `Lean.trustCompiler`, the `ofReduce*` pair; `propext`/`choice`
of another shape and every other axiom decline; `sorryAx` is skipped. -/
-- con-ron: ConRon/Arena/CheckDecl.lean:74-158 ConRon.Arena.checkDeclKind
@[no_expose, l_impl ConRon.Arena.checkDeclKind]
def checkDeclAxiom : FunDecl := lfn (i, vis) locals (p, n, s, e, z, w, a, b) {
  p := call erec_ci(i, 0);
  n := EREC⦃p + ⟪CI.cv + CV.name⟫⦄;
  s := call pin_at(4);
  if n == s {
    w := call check_quot_record(vis, 4, p + ⟪CI.cv⟫);
    return w
  };
  z := call check_constant_val(vis, p + ⟪CI.cv⟫, 0, 0, 1);
  e := call std_axiom_ok(vis, p + ⟪CI.cv⟫);
  if e != 0 { w := call env_push(vis, p); return w };
  s := call pin_at(42);
  if n == s {
    e := call trust_compiler_ok(vis, p + ⟪CI.cv⟫);
    if e == 0 { fail R_UNSUPPORTED_LEAN_TRUSTCOMPILER };
    w := call env_push(vis, p);
    return w
  };
  a := call pin_at(45);
  b := call pin_at(46);
  if n == a || n == b {
    e := call of_reduce_ax_ok(vis, p + ⟪CI.cv⟫);
    if e == 0 { fail R_UNSUPPORTED_COMPILER_TRUST };
    w := call env_push(vis, p);
    return w
  };
  a := call pin_at(32);
  b := call pin_at(33);
  if n == a || n == b { fail R_STANDARD_AXIOM_SHAPE };
  s := call pin_at(13);
  if n == s { return vis };
  fail R_NON_STANDARD_AXIOM_CON
}

/-- `check_structural_nat_pin_at_fe2(w, n)`: the structural-`Nat` gate's reads at the extended
view `w`: `natOpGuard` and the operation's own pinned type (`natOpStoredOk`; both computed before either is tested, as
the twin's `g && d`), then the stored definition's value. -/
-- con-ron: ConRon/Arena/CheckDecl.lean:41-53 ConRon.Arena.checkStructuralNatPinAtFe2
@[no_expose, l_impl ConRon.Arena.checkStructuralNatPinAtFe2]
def checkStructuralNatPinAtFe2L : FunDecl := lfn (w, n) locals (g, d, f, r) {
  g := call nat_op_guard(w, n);
  d := call nat_op_stored_ok(w, n);
  if g == 0 || d == 0 { fail R_NONSTANDARD_STRUCTURAL_NAT_OPERATION };
  (f, r) := call env_find(n, w);
  if f == 0 { abort };
  if EREC⦃r⦄ != 1 { abort };
  return EREC⦃r + ⟪CI.defnValue⟫⦄
}

/-- `check_structural_nat_pin(vis, p, n)`: `checkStructuralNatPin`: the record `p` pushed for the
reads at the extended view and popped (`env_pop_temp`, the literal flags set back: `env_set_flags`), then the recurrences of the stored value
(`nat_op_equations 0 n`, `n` replaced by the value) certified at `vis`; returns the view. -/
-- con-ron: ConRon/Arena/CheckDecl.lean:55-72 ConRon.Arena.checkStructuralNatPin
@[no_expose, l_impl ConRon.Arena.checkStructuralNatPin]
def checkStructuralNatPinL : FunDecl :=
    lfn (vis, p, n) locals (rc, rq, fn, fs, w, v, v2, z, eo, el, so, sl, ok) {
  (rc, rq) := call env_row_get(n);
  fn := CTL.u64[160];
  fs := CTL.u64[161];
  w := call env_push(vis, p);
  v := call check_structural_nat_pin_at_fe2(w, n);
  v2 := call env_pop_temp(w, n, rc, rq);
  z := call env_set_flags(fn, fs);
  (eo, el) := call nat_op_equations(0, n);
  (so, sl) := call subst_const0_pairs(n, v, eo, el);
  ok := call certify_nat_eqs(v2, so, sl);
  if ok == 0 { fail R_NONSTANDARD_STRUCTURAL_NAT };
  return v2
}

/-- `check_decl_defn(i, vis)`: the `.defnDecl` arm: the constant check (a certified operation's
name allowed), the definition check, then for a `natOpNames` member the structural-`Nat` gate,
for a `natDivModNames` member the pin gate over the ROM's variants (`rom_pin_sets()`), and the
push. -/
-- con-ron: ConRon/Arena/CheckDecl.lean:74-158 ConRon.Arena.checkDeclKind
@[no_expose, l_impl ConRon.Arena.checkDeclKind]
def checkDeclDefn : FunDecl := lfn (i, vis) locals (p, n, z, v, no, nl, c, po, pl, w) {
  p := call erec_ci(i, 1);
  n := EREC⦃p + ⟪CI.cv + CV.name⟫⦄;
  z := call check_constant_val(vis, p + ⟪CI.cv⟫, 1, 0, 0);
  p := call check_defn_val(vis, p);
  v := vis;
  (no, nl) := call nat_op_names();
  c := call sl_contains(no, nl, n);
  if c != 0 { v := call check_structural_nat_pin(v, p, n) };
  (no, nl) := call nat_div_mod_names();
  c := call sl_contains(no, nl, n);
  if c != 0 {
    (po, pl) := call rom_pin_sets();
    v := call check_div_mod_pin(po, pl, v, p, n)
  };
  w := call env_push(v, p);
  return w
}

/-- `check_decl_thm(i, vis)`: the `.thmDecl` arm. -/
-- con-ron: ConRon/Arena/CheckDecl.lean:74-158 ConRon.Arena.checkDeclKind
@[no_expose, l_impl ConRon.Arena.checkDeclKind]
def checkDeclThm : FunDecl := lfn (i, vis) locals (p, z, w) {
  p := call erec_ci(i, 2);
  z := call check_constant_val(vis, p + ⟪CI.cv⟫, 0, 0, 0);
  p := call check_thm_val(vis, p);
  w := call env_push(vis, p);
  return w
}

/-- `check_decl_opaque(i, vis)`: the `.opaqueDecl` arm: the opaque check, then for
`Lean.reduceNat`/`Lean.reduceBool` (`reduceOpNames`, pin slots `43`, `44`) the pin gate, and the
push. -/
-- con-ron: ConRon/Arena/CheckDecl.lean:74-158 ConRon.Arena.checkDeclKind
@[no_expose, l_impl ConRon.Arena.checkDeclKind]
def checkDeclOpaque : FunDecl := lfn (i, vis) locals (p, n, v, z, u, a, b, w) {
  p := call erec_ci(i, 0);
  n := EREC⦃p + ⟪CI.cv + CV.name⟫⦄;
  v := EREC⦃p + ⟪CI.defnValue⟫⦄;
  z := call check_constant_val(vis, p + ⟪CI.cv⟫, 0, 1, 0);
  p := call check_opaque_val(vis, p);
  u := vis;
  a := call pin_at(43);
  b := call pin_at(44);
  if n == a || n == b {
    u := call check_reduce_pin(u, p, n, v)
  };
  w := call env_push(u, p);
  return w
}

/-- `check_decl_quot(i, vis)`: the `.quotDecl` arm: `check_quot_record` at the record's slot
(`DECL` word 7: `1` type, `2` ctor, `3` lift, else ind). -/
-- con-ron: ConRon/Arena/CheckDecl.lean:74-158 ConRon.Arena.checkDeclKind
@[no_expose, l_impl ConRon.Arena.checkDeclKind]
def checkDeclQuot : FunDecl := lfn (i, vis) locals (kw, k, p, w) {
  kw := DECL.u64[7 + 8 * i];
  k := 3;
  if kw == 1 { k := 0 } else if kw == 2 { k := 1 } else if kw == 3 { k := 2 };
  p := call erec_ci(i, 0);
  w := call check_quot_record(vis, k, p + ⟪CI.cv⟫);
  return w
}

/-! ## The module's program -/

/-- This module's functions. -/
def declArmsFns : Prog :=
  [("check_constant_val", checkConstantValL), ("value_guards", valueGuardsL),
   ("check_defn_val", checkDefnValL), ("check_thm_val", checkThmValL),
   ("check_opaque_val", checkOpaqueValL), ("matches_pin", matchesPinL),
   ("find_pinned", findPinned), ("std_ax_family", stdAxFamily), ("std_axiom_ok", stdAxiomOkL),
   ("find_pinned_cv", findPinnedCv), ("trust_compiler_ok", trustCompilerOkL),
   ("reduce_op_cv_a", reduceOpCvAL), ("reduce_stored_ok", reduceStoredOkL),
   ("reduce_elem_ok", reduceElemOkL), ("of_reduce_op", ofReduceOpL),
   ("of_reduce_pin_a", ofReducePinAL), ("of_reduce_ax_ok", ofReduceAxOkL),
   ("reduce_decl_pin", reduceDeclPinL), ("reduce_cert_var", reduceCertVarL),
   ("reduce_pin_guard", reducePinGuardL), ("check_reduce_pin_pre", checkReducePinPreL),
   ("check_reduce_pin", checkReducePinL),
   ("install_basis_decl", installBasisDeclL), ("check_quot_record", checkQuotRecordL),
   ("check_decl_axiom", checkDeclAxiom),
   ("check_structural_nat_pin_at_fe2", checkStructuralNatPinAtFe2L),
   ("check_structural_nat_pin", checkStructuralNatPinL), ("check_decl_defn", checkDeclDefn),
   ("check_decl_thm", checkDeclThm), ("check_decl_opaque", checkDeclOpaque),
   ("check_decl_quot", checkDeclQuot)]

/-- All the arms modules, with the ROM stubs and the master functions lane `induct`'s program
lacks. -/
def declArmsAll : Prog :=
  declArmsFns ++ basisFns ++ declArmsNatFns ++ declArmsCanonFns ++ romStubs ++ armsMasterFns

/-- The lane-`induct` stubs these modules provide for real: `declStepProg` drops them from lane
`induct`'s program (`stubFns` is lane `induct`'s file). -/
def armsReplaced : List FnName :=
  ["check_constant_val"]

/-- Lane `induct`'s program without the stubs replaced here. -/
def indProgArms : Prog := indProg.filter fun e => !armsReplaced.contains e.1

/-- `DeclStep.lean`'s functions the arms call, as stubs for this module's own closure check. -/
def armsDeclStepFns : Prog :=
  [("erec_ci", stub 2)]

/-! ## Runs on stub-free paths -/

-- `of_reduce_op`: `Lean.ofReduceNat` (slot 45) speaks about `Lean.reduceNat` (slot 43), anything
-- else about `Lean.reduceBool` (slot 44).
#guard
  (match run (withPins (declArmsAll ++ armsDeclStepFns ++ indProgArms)) 1000 "of_reduce_op" [145]
      pinsTestMem with
   | .ok ([143], _) => true | _ => false) &&
  (match run (withPins (declArmsAll ++ armsDeclStepFns ++ indProgArms)) 1000 "of_reduce_op" [146]
      pinsTestMem with
   | .ok ([144], _) => true | _ => false)

end L.Ind
