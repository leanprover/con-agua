import ConAgua.Arena.DeclBase
import ConAgua.Arena.IndProg
import ConAgua.Arena.DeclArms
import ConAgua.Front.IndApply
import ConAgua.Census.Attr

/-!
# Phase A's step body in L: `install_step_go`, `check_decl`, the header and value guards

The twin's `installStepGo` (`vendor/con-ron/ConRon/Arena/Checker.lean`) and `checkDecl`'s dispatch
(`CheckDecl.lean`), `installHeader`/`installValueGuards` (`CheckerSplit.lean`), on lane
`induct`'s conventions (`IndIface.lean`: the work pool `IW`, constants as `EREC` records, the view
word for the environment, the callee names and argument orders of its `stubFns`).

* `install_step_go(i, vis)` → `(vis', flag, g)`: record `i` of `DECL`. A definition (kind `2`),
  theorem (`3`) or opaque (`4`) not among the pinned names is guarded and installed here: its
  constant record is built in `EREC` (`erec_ci`: kind `1` `defnInfo`, `2` `thmInfo`, `0`
  `axiomInfo`), `install_header` and (but for a theorem) `install_value_guards` run on it, it is
  pushed (`env_push`), and its value group is a 6-word `EREC` record (`erec_vg`). Everything else
  goes to `check_decl`. A definition is pinned when its name is one of `PINS[15‥29]`
  (`natOpNames ++ natDivModNames`), an opaque when it is `PINS[44]`/`PINS[45]` (`reduceOpNames`).
* `check_decl(i, vis)` → `vis'`: an inductive block (kind `6`, lane `induct`'s front records in
  `DIND`) is copied into `EREC` (`ind_block_to_erec`: every record, its universe parameters and
  its recursor rules relocated) and checked by lane `induct`'s `check_ind_decl(vis, boff, blen,
  nP)`; every one-constant record goes to its arm (`DeclArms.lean`: `check_decl_axiom`,
  `check_decl_defn`, `check_decl_thm`, `check_decl_opaque`, `check_decl_quot`, each `(i, vis)`).
* `install_header(vis, q)`, `install_value_guards(vis, q, v)`: `q` is a constant value in `EREC`
  (`decCV`: name, universe parameters, type). The checks in the twin's order; every `fail` is
  `abort`.

The refinement of `install_step_go` is `CheckerT.lean`'s `installStepGo_specT`: it
needs the front's `DeclAt` arm for kind `6` (lane `front`), the stub specs of `IndStubs.lean`, and
the callees' frame on `PEND`/`DECL`/`DLP` from the program text.
-/

open ConRon.Arena

namespace L.Arena

open L.Front (DECL DLP)
open L.Front.Ind (DIND)
open L.Ind (IW)

/-! ## Pinned names -/

/-- `pin_in(x, k, hi)`: `1` if `x` is one of `PINS[k‥hi)`; aborts on an empty pin table, where the
twin's pin reads raise `.internal`. -/
-- con-ron: ConRon/Arena/Checker.lean:113-151 ConRon.Arena.installStepGo
def pinIn : FunDecl := lfn (x, k, hi) locals (r) {
  if PINS.u64[0] == 0 { abort R_PIN_DATA };
  if hi <= k { return 0 };
  if PINS.u64[k] == x { return 1 };
  r := call pin_in(x, k + 1, hi);
  return r
}

/-! ## Constant records from the front's records -/

/-- `dlp_copy(d, s, l)`: `EREC[d + j] := DLP[s + j]` cut to 32 bits, for `j < l`. -/
-- con-ron: none — copies the front's records into `EREC` (the twin's `checkDecl` takes the front's values as they are)
def dlpCopy : FunDecl := lfn (d, s, l) locals (u) {
  if l == 0 { return 0 };
  EREC.u64[d] := DLP.u64[s] & 4294967295;
  u := call dlp_copy(d + 1, s + 1, l - 1);
  return 0
}

/-- `erec_ci(i, kind)`: the constant record of `DECL` record `i` with kind word `kind`
(`decCI`'s layout: kind, the constant value, the value, the hint (`0` opaque, `1` abbrev, `2`
regular), the height); its universe parameters a fresh `EREC` slice. -/
-- con-ron: ConRon/Arena/Checker.lean:113-151 ConRon.Arena.installStepGo
def erecCi : FunDecl := lfn (i, kind) locals (lo, ll, s, z, p, hq) {
  lo := DECL.u64[3 + 8 * i];
  ll := DECL.u64[4 + 8 * i];
  s := call erec_alloc(ll);
  z := call dlp_copy(s, 1 + lo, ll);
  p := call erec_alloc(8);
  EREC.u64[p] := kind;
  EREC.u64[p + 1] := DECL.u64[2 + 8 * i] & 4294967295;
  EREC.u64[p + 2] := s;
  EREC.u64[p + 3] := ll;
  EREC.u64[p + 4] := DECL.u64[5 + 8 * i] & 4294967295;
  EREC.u64[p + 5] := DECL.u64[6 + 8 * i] & 4294967295;
  hq := DECL.u64[7 + 8 * i];
  if hq == 1 { EREC.u64[p + 6] := 1 } else if hq == 2 { EREC.u64[p + 6] := 0 } else {
    EREC.u64[p + 6] := 2 };
  EREC.u64[p + 7] := DECL.u64[8 + 8 * i];
  return p
}

/-- `erec_vg(p, vk)`: the value group of the constant record `p` with value kind `vk` (`0`
defn, `1` thm, `2` opaque): kind, the constant value, the value (`p + 5`). -/
-- con-ron: ConRon/Arena/Checker.lean:113-151 ConRon.Arena.installStepGo
def erecVg : FunDecl := lfn (p, vk) locals (g) {
  g := call erec_alloc(6);
  EREC.u64[g] := vk;
  EREC.u64[g + 1] := EREC.u64[p + 1];
  EREC.u64[g + 2] := EREC.u64[p + 2];
  EREC.u64[g + 3] := EREC.u64[p + 3];
  EREC.u64[g + 4] := EREC.u64[p + 4];
  EREC.u64[g + 5] := EREC.u64[p + 5];
  return g
}

/-! ## The guards -/

/-- `install_header(vis, q)`: `installHeader fe cv`, `q` the constant value in `EREC`. -/
-- con-ron: ConRon/Arena/CheckerSplit.lean:59-77 ConRon.Arena.installHeader
-- con-ron: CHANGED since 12752ca7 — `ConRon.Arena.installHeader` changed; re-check the L code and its proofs, then delete this line
@[l_impl ConRon.Arena.installHeader]
def installHeaderL : FunDecl := lfn (vis, q) locals (n, t, f, r, c, s, o, l, d, b, h, a) {
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
  if d == 0 { fail R_DUPLICATE_UNIVERSE_PARAMETERS };
  b := call loose_bvars_bounded_fast(4000000000, 0, t);
  if b == 0 { fail R_LOOSE_BOUND_VARIABLE };
  h := call has_fvar_fast(4000000000, t);
  if h != 0 { fail R_UNEXPECTED_FREE_VARIABLE };
  a := call all_level_params_defined(o, l, t);
  if a == 0 { fail R_UNDECLARED_UNIVERSE_PARAMETER };
  c := call consts_resolve_ffast(vis, t);
  if c == 0 { abort };
  return 0
}

/-- `install_value_guards(vis, q, v)`: `installValueGuards fe cv v`. -/
-- con-ron: ConRon/Arena/CheckerSplit.lean:79-91 ConRon.Arena.installValueGuards
@[l_impl ConRon.Arena.installValueGuards]
def installValueGuardsL : FunDecl := lfn (vis, q, v) locals (o, l, b, h, a, c) {
  (o, l) := call cv_lps(q);
  b := call loose_bvars_bounded_fast(4000000000, 0, v);
  if b == 0 { fail R_LOOSE_BOUND_VARIABLE_IN };
  h := call has_fvar_fast(4000000000, v);
  if h != 0 { fail R_UNEXPECTED_FREE_VARIABLE_IN };
  a := call all_level_params_defined(o, l, v);
  if a == 0 { fail R_UNDECLARED_UNIVERSE_PARAMETER_IN_VALUE };
  c := call consts_resolve_ffast(vis, v);
  if c == 0 { abort };
  return 0
}

/-! ## An inductive block from the front's `DIND` into `EREC` -/

/-- `dind_copy(d, s, l)`: `EREC[d + j] := DIND[s + j]` for `j < l`. A non-empty source at word `0`
(the pool's top, never a record's or a slice's place: the front writes them at `1 + top`) aborts,
so that the copy reads only what `IndDeclAt`'s cut pool (`trunc`, word `0` cleared) decodes. -/
-- con-ron: none — copies the front's records into `EREC` (the twin's `checkDecl` takes the front's values as they are)
def dindCopy : FunDecl := lfn (d, s, l) locals (u) {
  if l == 0 { return 0 };
  if s == 0 { abort };
  EREC.u64[d] := DIND.u64[s];
  u := call dind_copy(d + 1, s + 1, l - 1);
  return 0
}

/-- `ind_rec_copy(s)`: the constant record at `DIND[s]` (kind `3` inductive, 20 words; `4`
constructor, 7; `5` recursor, 9 and its 11-word rules) copied into `EREC`, its slices too. -/
-- con-ron: none — copies the front's records into `EREC` (the twin's `checkDecl` takes the front's values as they are)
def indRecCopy : FunDecl := lfn (s) locals (k, q, z, r, n, p) {
  k := DIND.u64[s];
  q := call erec_alloc(DIND.u64[s + 3]);
  z := call dind_copy(q, DIND.u64[s + 2], DIND.u64[s + 3]);
  r := 0;
  if k == 3 { n := 20 } else if k == 4 { n := 7 } else if k == 5 {
    n := 9;
    if DIND.u64[s + 8] >= 1152921504606846976 { abort };
    r := call erec_alloc(11 * DIND.u64[s + 8]);
    z := call dind_copy(r, DIND.u64[s + 7], 11 * DIND.u64[s + 8])
  } else { abort };
  p := call erec_alloc(n);
  z := call dind_copy(p, s, n);
  EREC.u64[p + 2] := q;
  if k == 5 { EREC.u64[p + 7] := r };
  return p
}

/-- `ind_copy_go(o, bo, bl)`: the records the pointers `DIND[bo‥bo + bl)` name, copied, their
`EREC` pointers to `EREC[o‥]`. -/
-- con-ron: none — copies the front's records into `EREC` (the twin's `checkDecl` takes the front's values as they are)
def indCopyGo : FunDecl := lfn (o, bo, bl) locals (p, u) {
  if bl == 0 { return 0 };
  p := call ind_rec_copy(DIND.u64[bo]);
  EREC.u64[o] := p;
  u := call ind_copy_go(o + 1, bo + 1, bl - 1);
  return 0
}

/-- `ind_block_to_erec(i)`: the block of `DECL` record `i` (kind `6`) as an `EREC` slice. -/
-- con-ron: none — copies the front's records into `EREC` (the twin's `checkDecl` takes the front's values as they are)
def indBlockToErec : FunDecl := lfn (i) locals (bo, bl, o, u) {
  bo := DECL.u64[3 + 8 * i];
  bl := DECL.u64[4 + 8 * i];
  o := call erec_alloc(bl);
  u := call ind_copy_go(o, bo, bl);
  return (o, bl)
}

/-! ## `check_decl`, `install_step_go` -/

/-- `check_decl(i, vis)`: `checkDecl` on record `i`. -/
-- con-ron: ConRon/Arena/CheckDecl.lean:82-214 ConRon.Arena.checkDecl
@[l_impl ConRon.Arena.checkDecl]
def checkDeclL : FunDecl := lfn (i, vis) locals (k, bo, bl, np, v) {
  k := DECL.u64[1 + 8 * i];
  if k == 6 {
    (bo, bl) := call ind_block_to_erec(i);
    np := DECL.u64[5 + 8 * i];
    v := call check_ind_decl(vis, bo, bl, np);
    return v
  };
  if k == 1 { v := call check_decl_axiom(i, vis); return v };
  if k == 2 { v := call check_decl_defn(i, vis); return v };
  if k == 3 { v := call check_decl_thm(i, vis); return v };
  if k == 4 { v := call check_decl_opaque(i, vis); return v };
  if k == 5 { v := call check_decl_quot(i, vis); return v };
  abort
}

/-- `install_value(i, vis, ck, vk)`: `installStepGo`'s guard-and-install arm on record `i` (a
definition, theorem or opaque not among the pinned names): its constant record (kind `ck`, `1`
`defnInfo`, `2` `thmInfo`, `0` `axiomInfo`), the header's guards, the value's guards but for a
theorem (`vk = 1`), the push, the value group (kind `vk`) → the new view and the group's record.
Split out of `install_step_go` so that its call closure is the arm's alone (its write set comes
from the text, `DeclStepSpec.lean`). -/
-- con-ron: ConRon/Arena/Checker.lean:113-151 ConRon.Arena.installStepGo
def installValueL : FunDecl := lfn (i, vis, ck, vk) locals (p, z, v, g) {
  p := call erec_ci(i, ck);
  z := call install_header(vis, p + 1);
  if vk != 1 { z := call install_value_guards(vis, p + 1, EREC.u64[p + 5]) };
  v := call env_push(vis, p);
  g := call erec_vg(p, vk);
  return (v, g)
}

/-- `install_step_go(i, vis)`: `installStepGo` on record `i` → the new view, the value group's
flag and record. -/
-- con-ron: ConRon/Arena/Checker.lean:113-151 ConRon.Arena.installStepGo
@[l_impl ConRon.Arena.installStepGo]
def installStepGoL : FunDecl := lfn (i, vis) locals (k, x, c, v, z, g) {
  z := call iw_reset();
  k := DECL.u64[1 + 8 * i];
  x := DECL.u64[2 + 8 * i] & 4294967295;
  if k == 2 {
    c := call pin_in(x, 15, 30);
    if c != 0 { v := call check_decl(i, vis); return (v, 0, 0) };
    (v, g) := call install_value(i, vis, 1, 0);
    return (v, 1, g)
  };
  if k == 3 {
    (v, g) := call install_value(i, vis, 2, 1);
    return (v, 1, g)
  };
  if k == 4 {
    c := call pin_in(x, 44, 46);
    if c != 0 { v := call check_decl(i, vis); return (v, 0, 0) };
    (v, g) := call install_value(i, vis, 0, 2);
    return (v, 1, g)
  };
  v := call check_decl(i, vis);
  return (v, 0, 0)
}

/-! ## Phase B: `check_value_group` -/

/-- `check_value_group(vis, g)`: `checkValueGroup` on the value group record `g`: the type's
sort, for a theorem the proposition test and the value's guards, the value's type against the
declared one. The level comparison is lane `whnf`'s cached `lvl_eq_c` (`lvlEq?` consults and fills
`lvlEqC`; `0` none, `1` false, `2` true). -/
-- con-ron: ConRon/Arena/CheckerSplit.lean:93-110 ConRon.Arena.checkValueGroup
@[l_impl ConRon.Arena.checkValueGroup]
def checkValueGroupL : FunDecl := lfn (vis, g) locals (z, t, v, st, u, zr, e, vt, d) {
  z := call iw_reset();
  t := EREC.u64[g + 4];
  v := EREC.u64[g + 5];
  st := call infer_type_core(vis, 0, t);
  u := call ensure_sort_core(vis, 0, st);
  if EREC.u64[g] == 1 {
    zr := call pin_word(53);
    e := call lvl_eq_c(u, zr);
    if e == 1 { fail R_TYPE_OF_THEOREM };
    if e != 2 { abort };
    z := call install_value_guards(vis, g + 1, v)
  };
  vt := call infer_type_core(vis, 0, v);
  d := call is_def_eq_core(vis, 0, vt, t);
  if d == 0 {
    if EREC.u64[g] == 1 { fail R_TYPE_MISMATCH_IN_THEOREM };
    if EREC.u64[g] == 2 { fail R_TYPE_MISMATCH_IN_OPAQUE };
    fail R_TYPE_MISMATCH_IN
  };
  return 0
}

/-! ## The program -/

/-- This module's functions. -/
def declStepFns : Prog :=
  [("pin_in", pinIn), ("dlp_copy", dlpCopy), ("erec_ci", erecCi), ("erec_vg", erecVg),
   ("install_header", installHeaderL), ("install_value_guards", installValueGuardsL),
   ("dind_copy", dindCopy), ("ind_rec_copy", indRecCopy), ("ind_copy_go", indCopyGo),
   ("ind_block_to_erec", indBlockToErec), ("check_decl", checkDeclL),
   ("install_value", installValueL), ("install_step_go", installStepGoL),
   ("check_value_group", checkValueGroupL)]

/-- The step's program: this module, the arms (`DeclArms*.lean`, with their ROM stubs and the
master functions lane `induct`'s program lacks), lane `induct`'s stage (with its stubs, but for
the two the arms provide: `L.Ind.armsReplaced`). -/
def declStepProg : Prog := declStepFns ++ L.Ind.declArmsAll ++ L.Ind.indProgArms

end L.Arena
