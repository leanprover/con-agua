import ConAgua.Arena.IndIface
import ConAgua.Arena.WhnfBase
import ConAgua.Census.Attr

/-!
# Former stubs: the inductive stage's telescopes, zero-ness, rule bits (lane `stubs`)

L code for callees of the inductive stage that were `abortStub`s in `checkerProg` (their
`RelAM` contracts are lane `induct`'s, `IndStubs.lean`, still `sorry`):

* `lv_zero_caps(l)`: `zeronessOf` of the level `l` as three words (`decPW`'s layout: `0` for
  `never`, `1, off, len` for `ifAllZero` with the names an `EREC` slice): `lv_zero` pushes the
  parameters on the level heap `LH`, they are copied to fresh `EREC` words, and the heap top is
  restored.
* `rec_rule_bits(vis, c)`: `recRuleBits`' two bits `(k, eta)` of a rule with constructor `c`
  (`recRuleKOf`, `recRuleEtaOf`): the constructor's record, its type's Π-result's head constant,
  that inductive's record and capabilities (`EnvRec.lean`'s `decCI` layout).
* `open_pis_at_fvars_f(n, e, i)`: `openPisAtFvarsF`: `(1, off, len, body)` with the `n` fresh
  free variables an `IW` slice, or `(0, 0, 0, 0)`. The one-pass walk (`opf_go`) keeps the free
  variables made so far on the spine stack `SPN` above `CTL[136]` (the twin's `acc`, oldest
  first, so `inst_list`'s slice convention is the twin's `instantiateListFast … acc`); when it
  fails, the twin's fallback `openPisAtFvars` (`opa_go`, one `instantiate1` per binder) runs, as
  the twin's does, for its effect on the store.
-/

namespace L.Stubs

open L.Arena L.Ind

/-! ## `lv_zero_caps(l)` -/

/-- `lh_er_copy(d, s, l)`: `EREC[d + j] := LH[s + j]` for `j < l`. -/
-- con-ron: none — L scratch-array plumbing (the twin's `PropWhen` is a value)
def lhErCopy : FunDecl := lfn (d, s, l) locals (u) {
  if l == 0 { return 0 };
  EREC.u64[d] := LH.u64[s];
  u := call lh_er_copy(d + 1, s + 1, l - 1);
  return 0
}

/-- `lv_zero_caps(l)`: `(0, 0, 0)` for `never`, `(1, off, len)` for `ifAllZero` with the
parameter names at `EREC[off ‥ off + len)`. -/
-- con-leche: ConLeche/Kernel/Level.lean:187-197 ConLeche.Level.zeronessOf
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:47-92 ConRon.Arena.blockCapsAt
def lvZeroCapsL : FunDecl := lfn (l) locals (t0, z, n, q, u) {
  t0 := CTL.u64[192];
  z := call lv_zero(l);
  if z != 0 { CTL.u64[192] := t0; return (0, 0, 0) };
  n := CTL.u64[192] - t0;
  q := call erec_alloc(n);
  u := call lh_er_copy(q, t0, n);
  CTL.u64[192] := t0;
  return (1, q, n)
}

/-! ## `rec_rule_bits(vis, c)` -/

/-- `ctor_family(vis, c)`: `(cq, tq, ok)`, the constructor `c`'s record and the record of the
inductive its type's Π-result's head constant names, `ok = 1` when both exist (`c` a constructor,
the head a `const` naming an inductive in the environment), else `ok = 0` (and `tq = 0`). The
common prefix of `recRuleKOf` and `recRuleEtaOf`. The flag is a word of its own: a record may
sit at offset `0` of `EREC`, so an offset is no sentinel. -/
-- con-ron: ConRon/Arena/Core.lean:1852-1867 ConRon.Arena.recRuleKOf
-- con-ron: ConRon/Arena/Core.lean:1869-1887 ConRon.Arena.recRuleEtaOf
def ctorFamily : FunDecl := lfn (vis, c) locals (f, q, pr, hh, t, f2, q2) {
  (f, q) := call env_find(c, vis);
  if f == 0 { return (0, 0, 0) };
  if EREC.u64[q] != 4 { return (0, 0, 0) };
  pr := call pi_result_f(⟪CWF⟫, EREC.u64[q + 4]);
  hh := call get_app_fn_f(⟪CWF⟫, pr);
  if hh >> 28 != 3 { return (q, 0, 0) };
  t := call const_name_of(hh);
  (f2, q2) := call env_find(t, vis);
  if f2 == 0 { return (q, 0, 0) };
  if EREC.u64[q2] != 3 { return (q, 0, 0) };
  return (q, q2, 1)
}

/-- con-ron: ConRon/Arena/Core.lean:1852-1867 ConRon.Arena.recRuleKOf -/
@[l_impl ConRon.Arena.recRuleKOf]
def recRuleKOfL : FunDecl := lfn (vis, c) locals (q, tq, ok) {
  (q, tq, ok) := call ctor_family(vis, c);
  if ok == 0 { return 0 };
  if EREC.u64[tq + 11] != 0 && EREC.u64[q + 6] == 0 { return 1 };
  return 0
}

/-- con-ron: ConRon/Arena/Core.lean:1869-1887 ConRon.Arena.recRuleEtaOf -/
@[l_impl ConRon.Arena.recRuleEtaOf]
def recRuleEtaOfL : FunDecl := lfn (vis, c) locals (q, tq, ok, r) {
  (q, tq, ok) := call ctor_family(vis, c);
  if ok == 0 { return 0 };
  if EREC.u64[tq + 5] == 0 { return 0 };
  if EREC.u64[tq + 6] != c { return 0 };
  r := call er_sl_eq(EREC.u64[q + 2], EREC.u64[q + 3], EREC.u64[tq + 2], EREC.u64[tq + 3]);
  return r
}

/-- `rec_rule_bits(vis, c)`: the rule's `(k, eta)`. -/
-- con-ron: ConRon/Arena/Core.lean:1889-1895 ConRon.Arena.recRuleBits
@[l_impl ConRon.Arena.recRuleBits]
def recRuleBitsL : FunDecl := lfn (vis, c) locals (k, eta) {
  k := call rec_rule_k_of(vis, c);
  eta := call rec_rule_eta_of(vis, c);
  return (k, eta)
}

/-! ## `open_pis_at_fvars_f(n, e, i)` -/

/-- `spn_push(x)`: `x` on the spine stack (`CTL[136]` its top). -/
-- con-ron: none — L scratch-array plumbing (the twin's `acc` is an `Array` value)
def spnPush : FunDecl := lfn (x) locals (o) {
  o := CTL.u64[136];
  if len(SPN.u64) <= o { abort };
  SPN.u64[o] := x;
  CTL.u64[136] := o + 1;
  return 0
}

/-- `opf_go(n, e, i, co, cn)`: `openPisAtFvarsFGo acc n e i` with `acc = SPN[co ‥ co + cn)`:
`(1, body)` or `(0, 0)`; the free variables made are pushed. -/
-- con-ron: ConRon/Arena/CheckerBase.lean:287-304 ConRon.Arena.openPisAtFvarsFGo
@[l_impl ConRon.Arena.openPisAtFvarsFGo]
def opfGo : FunDecl := lfn (n, e, i, co, cn) locals (g, x, y, w, d, fv, u, ok, b) {
  if n == 0 { b := call inst_list(e, co, cn, 0); return (1, b) };
  if e >> 28 != 6 { return (0, 0) };
  (g, x, y, w) := call e_view(e);
  d := call inst_list(x, co, cn, 0);
  fv := call intern_fvar(i, d);
  u := call spn_push(fv);
  (ok, b) := call opf_go(n - 1, y, i + 1, co, cn + 1);
  return (ok, b)
}

/-- `opa_go(n, e, i)`: `openPisAtFvars n e i`: `(1, body)` or `(0, 0)`; the free variables made
are pushed. -/
-- con-ron: ConRon/Arena/CheckerBase.lean:269-285 ConRon.Arena.openPisAtFvars
@[l_impl ConRon.Arena.openPisAtFvars]
def opaGo : FunDecl := lfn (n, e, i) locals (g, x, y, w, fv, b, u, ok) {
  if n == 0 { return (1, e) };
  if e >> 28 != 6 { return (0, 0) };
  (g, x, y, w) := call e_view(e);
  fv := call intern_fvar(i, x);
  b := call inst_entry(y, fv, 0);
  u := call spn_push(fv);
  (ok, b) := call opa_go(n - 1, b, i + 1);
  return (ok, b)
}

/-- `open_pis_at_fvars_f(n, e, i)`: `(1, off, n, body)` (the free variables an `IW` slice, in
binder order) or `(0, 0, 0, 0)`. A first fvar index `i ≥ 2^63` aborts (a capacity guard, deviation
D33: the indices `i, i + 1, …` must not wrap). -/
-- con-ron: ConRon/Arena/CheckerBase.lean:306-313 ConRon.Arena.openPisAtFvarsF
@[l_impl ConRon.Arena.openPisAtFvarsF]
def openPisAtFvarsFL : FunDecl := lfn (n, e, i) locals (co, ok, b, q, u) {
  if i >> 63 != 0 { abort };
  co := CTL.u64[136];
  if len(SPN.u64) < co { abort };
  (ok, b) := call opf_go(n, e, i, co, 0);
  if ok == 0 {
    CTL.u64[136] := co;
    (ok, b) := call opa_go(n, e, i);
    if ok == 0 { CTL.u64[136] := co; return (0, 0, 0, 0) }
  };
  q := call iw_alloc(n);
  u := call spn_to_iw(q, co, n);
  CTL.u64[136] := co;
  return (1, q, n, b)
}

end L.Stubs
