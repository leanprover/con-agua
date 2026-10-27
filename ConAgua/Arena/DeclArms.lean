import ConAgua.Arena.DeclArmsNat
import ConAgua.Arena.IndProg
import ConAgua.Front.ApplyDecl
import ConAgua.Census.Attr

/-!
# `checkDecl`'s one-constant arms in L, part 3: the arms (lane `decls2`)

The `.axiomDecl`, `.defnDecl`, `.thmDecl`, `.opaqueDecl` and `.quotDecl` arms of the twin's
`checkDecl` (`vendor/con-ron/ConRon/Arena/CheckDecl.lean`) and what they call: `checkConstantVal`
(`CheckerBase.lean`), `checkDefnVal`/`checkThmVal`/`checkOpaqueVal`, `stdAxiomOk`,
`trustCompilerOk`, `reduceStoredOk`, `reduceElemOk`, `ofReduceAxOk`, `reducePinGuard`,
`checkReducePin`, `installBasisDecl(s)` (`DeclCheck.lean`), `IConstantVal.matchesPin`
(`StdAxioms.lean`), the reduce-operation helpers (`TrustAxioms.lean`), `quotPinHit` (`Basis.lean`)
and `checkBasisDecl` (`CheckDecl.lean`). `DeclStep.lean`'s `check_decl(i, vis)` dispatches record
`i` of `DECL` (`Front/StateDR.lean`'s `DeclAt`: kind `1` axiom, `2` definition, `3` theorem, `4`
opaque, `5` quotient) to `check_decl_axiom`, `check_decl_defn`, `check_decl_thm`,
`check_decl_opaque`, `check_decl_quot` (each `(i, vis)` → `vis'`).

* Every arm builds the record's constant in `EREC` first (`erec_ci`, `DeclStep.lean`): the value
  `cv` is at `p + 1`, the value at `p + 5`, a definition's hint at `p + 6`, `p + 7`; its kind is
  the one the twin pushes (`defnInfo`, `thmInfo`, `axiomInfo` for an opaque), so a value check
  pushes that record itself.
* A quotient record's kind is `DECL` word 6 (`quotW`: `1` type, `2` ctor, `3` lift, else ind); L
  passes its slot (`QuotKind.slot`: `0`‥`3`, `4` sound) as the `QuotKind` word.
* The con-leche values (`eqA`, `iffA`, …, the basis blocks, the reduce pins) come from the ROM
  stubs (`romStubs`, `DeclArmsNat.lean`); a pinned name is a `pin_at` read.
* `unresolvedConstsErrorL` (which error a failed `constsResolve` reports) is not translated: both
  of its answers are a `fail`, an `abort` here, and so are its walks' failures.
-/

namespace L.Ind

open L.Arena
open L.Front (DECL)

/-! ## The constant check -/

/-- `check_constant_val(vis, q)`: `checkConstantVal fe cv` (`q` the constant value): the header's
checks (`install_header`: the fresh name, the reserved names, the universe parameters, the type's
guards), then the type's sort. -/
-- con-ron: ConRon/Arena/CheckerBase.lean:239-265 ConRon.Arena.checkConstantVal
@[l_impl ConRon.Arena.checkConstantVal]
def checkConstantValL : FunDecl := lfn (vis, q) locals (t, z, st, u) {
  t := EREC.u64[q + 3];
  z := call install_header(vis, q);
  st := call infer_type_core(vis, 0, t);
  u := call ensure_sort_core(vis, 0, st);
  return 0
}

/-! ## The three value kinds

Each takes the arm's constant record `p` (built by `erec_ci` with the kind the twin pushes:
`defnInfo cv value hint`, `thmInfo cv`, `axiomInfo cv`; the value at `p + 5` either way) and
pushes that record itself. -/

/-- `check_defn_val(vis, p)`: `checkDefnVal fe cv v hint`: the value's guards, its type against the
declared one, the push. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:783-793 ConRon.Arena.checkDefnVal
@[l_impl ConRon.Arena.checkDefnVal]
def checkDefnValL : FunDecl := lfn (vis, p) locals (v, t, z, vt, d, w) {
  v := EREC.u64[p + 5];
  t := EREC.u64[p + 4];
  z := call install_value_guards(vis, p + 1, v);
  vt := call infer_type_core(vis, 0, v);
  d := call is_def_eq_core(vis, 0, vt, t);
  if d == 0 { fail R_TYPE_MISMATCH_IN };
  w := call env_push(vis, p);
  return w
}

/-- `check_thm_val(vis, p)`: `checkThmVal`: the type a proposition, the value's guards and type;
stored by its statement. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:795-811 ConRon.Arena.checkThmVal
@[l_impl ConRon.Arena.checkThmVal]
def checkThmValL : FunDecl := lfn (vis, p) locals (v, t, st, u, zr, e, z, vt, d, w) {
  v := EREC.u64[p + 5];
  t := EREC.u64[p + 4];
  st := call infer_type_core(vis, 0, t);
  u := call ensure_sort_core(vis, 0, st);
  zr := call pin_word(53);
  e := call lvl_eq_fueled(u, zr);
  if e == 0 { fail R_TYPE_OF_THEOREM };
  z := call install_value_guards(vis, p + 1, v);
  vt := call infer_type_core(vis, 0, v);
  d := call is_def_eq_core(vis, 0, vt, t);
  if d == 0 { fail R_TYPE_MISMATCH_IN_THEOREM };
  w := call env_push(vis, p);
  return w
}

/-- `check_opaque_val(vis, p)`: `checkOpaqueVal`: `check_defn_val`'s text (the record `p` is an
`axiomInfo`). -/
-- con-ron: ConRon/Arena/DeclCheck.lean:813-824 ConRon.Arena.checkOpaqueVal
@[l_impl ConRon.Arena.checkOpaqueVal]
def checkOpaqueValL : FunDecl := lfn (vis, p) locals (v, t, z, vt, d, w) {
  v := EREC.u64[p + 5];
  t := EREC.u64[p + 4];
  z := call install_value_guards(vis, p + 1, v);
  vt := call infer_type_core(vis, 0, v);
  d := call is_def_eq_core(vis, 0, vt, t);
  if d == 0 { fail R_TYPE_MISMATCH_IN_OPAQUE };
  w := call env_push(vis, p);
  return w
}

/-! ## The standard axioms -/

/-- `matches_pin(q, pin)`: `IConstantVal.matchesPin`: name, level parameters and type equal. -/
-- con-ron: ConRon/Arena/StdAxioms.lean:51-59 ConRon.Arena.IConstantVal.matchesPin
@[l_impl ConRon.Arena.IConstantVal.matchesPin]
def matchesPinL : FunDecl := lfn (q, pin) locals (e) {
  e := call cv_eq(q, pin);
  return e
}

/-- `find_pinned(vis, n, k, a, b, id)`: the stored constant `n` is of kind `k` (an inductive
`3`; a constructor `4` or a recursor `5` with the two counts `a`, `b` at `+5`, `+6`), and its
constant value matches the pin `rom_ci(id)`'s. One clause of `stdAxiomOk`'s chains. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:35-82 ConRon.Arena.stdAxiomOk
def findPinned : FunDecl := lfn (vis, n, k, a, b, id) locals (f, r, p, q, e) {
  (f, r) := call env_find(n, vis);
  if f == 0 { return 0 };
  if EREC.u64[r] != k { return 0 };
  if k != 3 {
    if EREC.u64[r + 5] != a || EREC.u64[r + 6] != b { return 0 }
  };
  p := call rom_ci(id);
  q := call ci_to_cv(p);
  e := call matches_pin(r + 1, q);
  return e
}

/-- `std_ax_family(vis, q, s1, s2, s3, i1, i2, i3, c2, c3, cvid)`: one family of `stdAxiomOk`: the
inductive at pin slot `s1` matching `rom_ci(i1)`, its constructor (`s2`, counts `c2`, `rom_ci(i2)`),
its recursor (`s3`, counts `c3`, `rom_ci(i3)`), then the axiom `q` against `rom_cv(cvid)`. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:35-82 ConRon.Arena.stdAxiomOk
def stdAxFamily : FunDecl :=
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
-- con-ron: ConRon/Arena/DeclCheck.lean:35-82 ConRon.Arena.stdAxiomOk
@[l_impl ConRon.Arena.stdAxiomOk]
def stdAxiomOkL : FunDecl := lfn (vis, q) locals (pn, nm, en, ea, e, cn) {
  pn := call pin_at(32);
  nm := EREC.u64[q];
  if nm == pn {
    en := call pin_at(0);
    ea := call rom_ci(0);
    e := call find_is(vis, en, ea);
    if e == 0 { return 0 };
    e := call std_ax_family(vis, q, 34, 35, 36, 2, 3, 4, 2, 4, 0);
    return e
  };
  cn := call pin_at(33);
  if nm == cn {
    e := call std_ax_family(vis, q, 37, 38, 39, 5, 6, 7, 1, 3, 1);
    return e
  };
  return 0
}

/-! ## The compiler-trust family -/

/-- `find_pinned_cv(vis, n, k, id)`: the stored constant `n` is of kind `k` (an inductive `3`, or
a constructor `4` with no parameters and no fields), its constant value matching `rom_cv(id)`.
One clause of `trustCompilerOk`. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:86-99 ConRon.Arena.trustCompilerOk
def findPinnedCv : FunDecl := lfn (vis, n, k, id) locals (f, r, p, e) {
  (f, r) := call env_find(n, vis);
  if f == 0 { return 0 };
  if EREC.u64[r] != k { return 0 };
  if k == 4 {
    if EREC.u64[r + 5] != 0 || EREC.u64[r + 6] != 0 { return 0 }
  };
  p := call rom_cv(id);
  e := call matches_pin(r + 1, p);
  return e
}

/-- `trust_compiler_ok(vis, q)`: `trustCompilerOk`: the `True` family stored with the pinned
shapes, the axiom's type the pin's. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:86-99 ConRon.Arena.trustCompilerOk
@[l_impl ConRon.Arena.trustCompilerOk]
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
-- con-ron: ConRon/Arena/TrustAxioms.lean:86-90 ConRon.Arena.reduceOpCvA
@[l_impl ConRon.Arena.reduceOpCvA]
def reduceOpCvAL : FunDecl := lfn (c) locals (rn, p) {
  rn := call pin_at(43);
  if c == rn { p := call rom_cv(6); return p };
  p := call rom_cv(7);
  return p
}

/-- `reduce_stored_ok(vis, c)`: `c` is stored as a checked opaque (`axiomInfo`) of the pinned
type. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:101-108 ConRon.Arena.reduceStoredOk
@[l_impl ConRon.Arena.reduceStoredOk]
def reduceStoredOkL : FunDecl := lfn (vis, c) locals (f, r, p, e) {
  (f, r) := call env_find(c, vis);
  if f == 0 { return 0 };
  if EREC.u64[r] != 0 { return 0 };
  p := call reduce_op_cv_a(c);
  e := call matches_pin(r + 1, p);
  return e
}

/-- `reduce_elem_ok(vis, c)`: the pinned `Nat` basis (for `reduceNat`), or a standard `Bool`. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:110-122 ConRon.Arena.reduceElemOk
@[l_impl ConRon.Arena.reduceElemOk]
def reduceElemOkL : FunDecl := lfn (vis, c) locals (rn, nn, f, r, na, e, bn, p) {
  rn := call pin_at(43);
  if c == rn {
    nn := call pin_at(1);
    (f, r) := call env_find(nn, vis);
    na := call rom_ci(1);
    if f == 0 { return 0 };
    e := call ci_eq(r, na);
    return e
  };
  bn := call pin_at(29);
  (f, r) := call env_find(bn, vis);
  if f == 0 { return 0 };
  if EREC.u64[r] != 3 { return 0 };
  p := call rom_cv(5);
  e := call matches_pin(r + 1, p);
  return e
}

/-- `of_reduce_op(n)`: the reduce operation an `ofReduce*` axiom speaks about. -/
-- con-ron: ConRon/Arena/TrustAxioms.lean:47-52 ConRon.Arena.ofReduceOp
@[l_impl ConRon.Arena.ofReduceOp]
def ofReduceOpL : FunDecl := lfn (n) locals (orn, r) {
  orn := call pin_at(45);
  if n == orn { r := call pin_at(43); return r };
  r := call pin_at(44);
  return r
}

/-- `of_reduce_pin_a(n)`: the pin an `ofReduce*` axiom is matched against. -/
-- con-ron: ConRon/Arena/TrustAxioms.lean:92-96 ConRon.Arena.ofReducePinA
@[l_impl ConRon.Arena.ofReducePinA]
def ofReducePinAL : FunDecl := lfn (n) locals (orn, p) {
  orn := call pin_at(45);
  if n == orn { p := call rom_cv(8); return p };
  p := call rom_cv(9);
  return p
}

/-- `of_reduce_ax_ok(vis, q)`: `ofReduceAxOk`: the pinned `Eq`, the element inductive, the
stored reduce opaque, the pin. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:124-134 ConRon.Arena.ofReduceAxOk
@[l_impl ConRon.Arena.ofReduceAxOk]
def ofReduceAxOkL : FunDecl := lfn (vis, q) locals (nm, c, en, ea, e, p) {
  nm := EREC.u64[q];
  c := call of_reduce_op(nm);
  en := call pin_at(0);
  ea := call rom_ci(0);
  e := call find_is(vis, en, ea);
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
-- con-ron: ConRon/Arena/TrustAxioms.lean:108-112 ConRon.Arena.reduceDeclPin
@[l_impl ConRon.Arena.reduceDeclPin]
def reduceDeclPinL : FunDecl := lfn (c) locals (rn, e) {
  rn := call pin_at(43);
  if c == rn { e := call rom_expr_pin(0); return e };
  e := call rom_expr_pin(1);
  return e
}

/-- `reduce_cert_var(c)`: `fvar 0` at the element type (`Nat` for `reduceNat`, else `Bool`). -/
-- con-ron: ConRon/Arena/TrustAxioms.lean:114-117 ConRon.Arena.reduceCertVar
-- con-ron: ConRon/Arena/TrustAxioms.lean:71-74 ConRon.Arena.reduceElemTy
-- con-ron: ConRon/Arena/TrustAxioms.lean:65-69 ConRon.Arena.reduceElemName
@[l_impl ConRon.Arena.reduceCertVar ConRon.Arena.reduceElemTy ConRon.Arena.reduceElemName]
def reduceCertVarL : FunDecl := lfn (c) locals (rn, n, t, r) {
  rn := call pin_at(43);
  if c == rn { n := call pin_at(1) } else { n := call pin_at(29) };
  t := call const_e(n);
  if 4294967296 <= t { abort };
  r := call intern_fvar(0, t);
  return r
}

/-- `reduce_pin_guard(vis, c)`: the syntactic guards on the reduce pin. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:136-144 ConRon.Arena.reducePinGuard
@[l_impl ConRon.Arena.reducePinGuard]
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

/-- `check_reduce_pin(vis, vis2, c, v)`: `checkReducePin`: the stored constant's type, the element
inductive, the pin's guards (short-circuiting), the value against the pin, the identity
certificate `v x ≡ x`. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:722-756 ConRon.Arena.checkReducePin
@[l_impl ConRon.Arena.checkReducePin]
def checkReducePinL : FunDecl := lfn (vis, vis2, c, v) locals (e, pa, x, ax) {
  e := call reduce_stored_ok(vis2, c);
  if e == 0 { fail R_UNSUPPORTED_COMPILER_TRUST_OPAQUE };
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

/-! ## The pinned basis install, the quotient pin -/

/-- `install_basis_decl(vis, p)`: the constant record `p` installed, duplicate-checked. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:826-833 ConRon.Arena.installBasisDecl
@[l_impl ConRon.Arena.installBasisDecl]
def installBasisDeclL : FunDecl := lfn (vis, p) locals (n, f, r, w) {
  n := EREC.u64[p + 1];
  (f, r) := call env_find(n, vis);
  if f != 0 { fail R_DUPLICATE_DECLARATION_2 };
  w := call env_push(vis, p);
  return w
}

/-- `install_basis_decls(vis, o, l)`: an `IW` slice of constant records, in order. -/
-- con-ron: ConRon/Arena/DeclCheck.lean:835-839 ConRon.Arena.installBasisDecls
@[l_impl ConRon.Arena.installBasisDecls]
def installBasisDeclsL : FunDecl := lfn (vis, o, l) locals (c, w) {
  if l == 0 { return vis };
  c := IW.u64[o];
  w := call install_basis_decl(vis, c);
  w := call install_basis_decls(w, o + 1, l - 1);
  return w
}

/-- `check_basis_decl(vis, kind)`: `checkBasisDecl`: the quotient block requires the pinned `Eq`
basis; then the annotated block is installed. -/
-- con-ron: ConRon/Arena/CheckDecl.lean:37-48 ConRon.Arena.checkBasisDecl
@[l_impl ConRon.Arena.checkBasisDecl]
def checkBasisDeclL : FunDecl := lfn (vis, kind) locals (en, ea, e, o, l, w) {
  if kind == 4 {
    en := call pin_at(0);
    ea := call rom_ci(0);
    e := call find_is(vis, en, ea);
    if e == 0 { fail R_QUOTIENT_BASIS_REQUIRES }
  };
  (o, l) := call rom_basis_decls_a(kind);
  w := call install_basis_decls(vis, o, l);
  return w
}

/-- `quot_pin_hit(k, q)`: the constant value `q` is the pinned quotient block's constant at slot
`k`, up to the canonical form. -/
-- con-ron: ConRon/Arena/Basis.lean:81-90 ConRon.Arena.quotPinHit
@[l_impl ConRon.Arena.quotPinHit]
def quotPinHitL : FunDecl := lfn (k, q) locals (o, l, c, p, e) {
  (o, l) := call rom_basis_decls(4);
  if l <= k { return 0 };
  c := IW.u64[o + k];
  p := call ci_to_cv(c);
  e := call cv_canon_eq(q, p);
  return e
}

/-! ## The arms -/

/-- `check_decl_axiom(i, vis)`: `checkDecl`'s `.axiomDecl` arm on record `i`: `Quot.sound` against
the pinned block (installing nothing), else the constant check and the five recognised axioms:
the standard two, `Lean.trustCompiler`, the `ofReduce*` pair; `propext`/`choice` of another shape
and every other axiom decline; `sorryAx` is skipped. -/
-- con-ron: ConRon/Arena/CheckDecl.lean:82-214 ConRon.Arena.checkDecl
@[l_impl ConRon.Arena.checkDecl]
def checkDeclAxiom : FunDecl := lfn (i, vis) locals (p, n, s, o, l, c, e, z, w, a, b) {
  p := call erec_ci(i, 0);
  n := EREC.u64[p + 1];
  s := call pin_at(4);
  if n == s {
    (o, l) := call rom_basis_decls(4);
    if l <= 4 { fail R_QUOTIENT_SOUNDNESS_AXIOM };
    c := IW.u64[o + 4];
    e := call ci_canon_eq(p, c);
    if e == 0 { fail R_QUOTIENT_SOUNDNESS_AXIOM };
    return vis
  };
  z := call check_constant_val(vis, p + 1);
  e := call std_axiom_ok(vis, p + 1);
  if e != 0 { w := call env_push(vis, p); return w };
  s := call pin_at(42);
  if n == s {
    e := call trust_compiler_ok(vis, p + 1);
    if e == 0 { fail R_UNSUPPORTED_LEAN_TRUSTCOMPILER };
    w := call env_push(vis, p);
    return w
  };
  a := call pin_at(45);
  b := call pin_at(46);
  if n == a || n == b {
    e := call of_reduce_ax_ok(vis, p + 1);
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

/-- `defn_nat_gate(vis, w, n)`: the definition arm's structural-`Nat` gate for the constant `n` at
the extended view `w`: for a `natOpNames` member, the guard and the stored dependencies (both
computed before either is tested, as the twin's `g && (← …)` does), then the recurrences of the
stored value certified at the pre-insertion view `vis`. Returns `0`. -/
-- con-ron: ConRon/Arena/CheckDecl.lean:82-214 ConRon.Arena.checkDecl
def defnNatGate : FunDecl :=
    lfn (vis, w, n) locals (no, nl, c, g, dov, dl, s, ok) {
  (no, nl) := call nat_op_names();
  c := call sl_contains(no, nl, n);
  if c != 0 {
    g := call nat_op_guard(w, n);
    (dov, dl) := call nat_op_deps(n);
    s := call nat_op_stored_ok_all(w, dov, dl);
    if g == 0 || s == 0 { fail R_NONSTANDARD_STRUCTURAL_NAT_OPERATION };
    ok := call defn_nat_cert(vis, w, n)
  };
  return 0
}

/-- `defn_div_gate(vis, w, n)`: the definition arm's `Nat.div`-family pin gate for the constant `n`
over the ROM's variants (`rom_pin_sets()`), at the extended view `w` and the pre-insertion view
`vis`. Returns `0`. -/
-- con-ron: ConRon/Arena/CheckDecl.lean:82-214 ConRon.Arena.checkDecl
def defnDivGate : FunDecl := lfn (vis, w, n) locals (no, nl, c, po, pl, z) {
  (no, nl) := call nat_div_mod_names();
  c := call sl_contains(no, nl, n);
  if c != 0 {
    (po, pl) := call rom_pin_sets();
    z := call check_div_mod_pin(po, pl, vis, w, n)
  };
  return 0
}

/-- `check_decl_defn(i, vis)`: the `.defnDecl` arm: the constant check, the definition check,
then the structural-`Nat` gate (`defn_nat_gate`) and the `Nat.div`-family pin gate
(`defn_div_gate`). -/
-- con-ron: ConRon/Arena/CheckDecl.lean:82-214 ConRon.Arena.checkDecl
@[l_impl ConRon.Arena.checkDecl]
def checkDeclDefn : FunDecl := lfn (i, vis) locals (p, n, z, w) {
  p := call erec_ci(i, 1);
  n := EREC.u64[p + 1];
  z := call check_constant_val(vis, p + 1);
  w := call check_defn_val(vis, p);
  z := call defn_nat_gate(vis, w, n);
  z := call defn_div_gate(vis, w, n);
  return w
}

/-- `check_decl_thm(i, vis)`: the `.thmDecl` arm. -/
-- con-ron: ConRon/Arena/CheckDecl.lean:82-214 ConRon.Arena.checkDecl
@[l_impl ConRon.Arena.checkDecl]
def checkDeclThm : FunDecl := lfn (i, vis) locals (p, z, w) {
  p := call erec_ci(i, 2);
  z := call check_constant_val(vis, p + 1);
  w := call check_thm_val(vis, p);
  return w
}

/-- `check_decl_opaque(i, vis)`: the `.opaqueDecl` arm: the opaque check, then for
`Lean.reduceNat`/`Lean.reduceBool` the install pin. -/
-- con-ron: ConRon/Arena/CheckDecl.lean:82-214 ConRon.Arena.checkDecl
@[l_impl ConRon.Arena.checkDecl]
def checkDeclOpaque : FunDecl := lfn (i, vis) locals (p, n, v, z, w, a, b) {
  p := call erec_ci(i, 0);
  n := EREC.u64[p + 1];
  v := EREC.u64[p + 5];
  z := call check_constant_val(vis, p + 1);
  w := call check_opaque_val(vis, p);
  a := call pin_at(43);
  b := call pin_at(44);
  if n == a || n == b {
    z := call check_reduce_pin(vis, w, n, v)
  };
  return w
}

/-- `check_decl_quot(i, vis)`: the `.quotDecl` arm: the record against the pinned block's
constant at its own slot; `Quot` itself installs the block, the other three install nothing. -/
-- con-ron: ConRon/Arena/CheckDecl.lean:82-214 ConRon.Arena.checkDecl
@[l_impl ConRon.Arena.checkDecl]
def checkDeclQuot : FunDecl := lfn (i, vis) locals (kw, k, p, e, w) {
  kw := DECL.u64[7 + 8 * i];
  k := 3;
  if kw == 1 { k := 0 } else if kw == 2 { k := 1 } else if kw == 3 { k := 2 };
  p := call erec_ci(i, 0);
  e := call quot_pin_hit(k, p + 1);
  if e == 0 { fail R_QUOTIENT_DECLARATION_MISMATCH };
  if k == 0 { w := call check_basis_decl(vis, 4); return w };
  return vis
}

/-! ## The module's program -/

/-- This module's functions. -/
def declArmsFns : Prog :=
  [("check_constant_val", checkConstantValL),
   ("check_defn_val", checkDefnValL), ("check_thm_val", checkThmValL),
   ("check_opaque_val", checkOpaqueValL), ("matches_pin", matchesPinL),
   ("find_pinned", findPinned), ("std_ax_family", stdAxFamily), ("std_axiom_ok", stdAxiomOkL),
   ("find_pinned_cv", findPinnedCv), ("trust_compiler_ok", trustCompilerOkL),
   ("reduce_op_cv_a", reduceOpCvAL), ("reduce_stored_ok", reduceStoredOkL),
   ("reduce_elem_ok", reduceElemOkL), ("of_reduce_op", ofReduceOpL),
   ("of_reduce_pin_a", ofReducePinAL), ("of_reduce_ax_ok", ofReduceAxOkL),
   ("reduce_decl_pin", reduceDeclPinL), ("reduce_cert_var", reduceCertVarL),
   ("reduce_pin_guard", reducePinGuardL), ("check_reduce_pin", checkReducePinL),
   ("install_basis_decl", installBasisDeclL), ("install_basis_decls", installBasisDeclsL),
   ("check_basis_decl", checkBasisDeclL), ("quot_pin_hit", quotPinHitL),
   ("check_decl_axiom", checkDeclAxiom), ("check_decl_defn", checkDeclDefn),
   ("defn_nat_gate", defnNatGate), ("defn_div_gate", defnDivGate),
   ("check_decl_thm", checkDeclThm), ("check_decl_opaque", checkDeclOpaque),
   ("check_decl_quot", checkDeclQuot)]

/-- All three arms modules, with the ROM stubs and the master functions lane `induct`'s program
lacks. -/
def declArmsAll : Prog :=
  declArmsFns ++ declArmsNatFns ++ declArmsCanonFns ++ romStubs ++ armsMasterFns

/-- The two lane-`induct` stubs these modules provide for real: `declStepProg` drops them from
lane `induct`'s program (`stubFns` is lane `induct`'s file). -/
def armsReplaced : List FnName := ["check_constant_val", "check_basis_decl"]

/-- Lane `induct`'s program without the stubs replaced here. -/
def indProgArms : Prog := indProg.filter fun e => !armsReplaced.contains e.1

/-- `DeclStep.lean`'s functions the arms call, as stubs for this module's own closure check. -/
def armsDeclStepFns : Prog :=
  [("erec_ci", stub 2), ("install_value_guards", stub 3), ("install_header", stub 2)]

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
