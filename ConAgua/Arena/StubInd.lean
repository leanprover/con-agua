module
import ConAgua.Census.Attr
import ConAgua.Layout
import ConAgua.L.Notation
public import ConAgua.L.Syntax


@[expose] public section

/-!
# Former stubs: the inductive stage's telescopes, zero-ness (lane `stubs`)

L code for callees of the inductive stage that were `abortStub`s in `checkerProg` (their
`RelAM` contracts are lane `induct`'s, `IndStubs.lean`):

* `lv_zero_caps(l)`: `zeronessOf` of the level `l` as three words (`decPW`'s layout: `0` for
  `never`, `1, off, len` for `ifAllZero` with the names an `EREC` slice): `lv_zero` pushes the
  parameters on the level heap `LH`, they are copied to fresh `EREC` words, and the heap top is
  restored.
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
@[no_expose] def lhErCopy : FunDecl := lfn (d, s, l) locals (u, ez) {
  if l == 0 { return 0 };
  ez := call erec_put(d, LH.u64[s]);
  u := call lh_er_copy(d + 1, s + 1, l - 1);
  return 0
}

/-- `lv_zero_caps(l)`: `(0, 0, 0)` for `never`, `(1, off, len)` for `ifAllZero` with the
parameter names at `EREC[off ‥ off + len)`. -/
-- con-leche: ConLeche/Kernel/Level.lean:187-197 ConLeche.Level.zeronessOf
-- con-ron: ConRon/Arena/Core.lean:362-370 ConRon.Arena.formerZ
@[no_expose] def lvZeroCapsL : FunDecl := lfn (l) locals (t0, z, n, q, u) {
  t0 := CTL.u64[192];
  z := call lv_zero(l);
  if z != 0 { CTL.u64[192] := t0; return (0, 0, 0) };
  n := CTL.u64[192] - t0;
  q := call erec_alloc(n);
  u := call lh_er_copy(q, t0, n);
  CTL.u64[192] := t0;
  return (1, q, n)
}

/-! ## `open_pis_at_fvars_f(n, e, i)` -/

/-- `spn_push(x)`: `x` on the spine stack (`CTL[136]` its top). -/
-- con-ron: none — L scratch-array plumbing (the twin's `acc` is an `Array` value)
@[no_expose] def spnPush : FunDecl := lfn (x) locals (o) {
  o := CTL.u64[136];
  if len(SPN.u64) <= o { abort };
  SPN.u64[o] := x;
  CTL.u64[136] := o + 1;
  return 0
}

/-- `opf_go(n, e, i, co, cn)`: `openPisAtFvarsFGo acc n e i` with `acc = SPN[co ‥ co + cn)`:
`(1, body)` or `(0, 0)`; the free variables made are pushed. -/
-- con-ron: ConRon/Arena/Core.lean:2598-2615 ConRon.Arena.openPisAtFvarsFGo
-- con-ron: CHANGED since 01ecb31c — `ConRon.Arena.openPisAtFvarsFGo` is gone upstream; re-check the L code and its proofs, then delete this line
@[no_expose, l_impl ConRon.Arena.openPisAtFvarsFGo]
def opfGo : FunDecl := lfn (n, e, i, co, cn) locals (g, x, y, w, d, fv, u, ok, b) {
  if n == 0 { b := call inst_list(e, co, cn, 0); return (1, b) };
  if ⟦e⟧.tag != 6 { return (0, 0) };
  (g, x, y, w) := call e_view(e);
  d := call inst_list(x, co, cn, 0);
  fv := call intern_fvar(i, d);
  u := call spn_push(fv);
  (ok, b) := call opf_go(n - 1, y, i + 1, co, cn + 1);
  return (ok, b)
}

/-- `opa_go(n, e, i)`: `openPisAtFvars n e i`: `(1, body)` or `(0, 0)`; the free variables made
are pushed. -/
-- con-ron: ConRon/Arena/Core.lean:2846-2862 ConRon.Arena.openPisAtFvars
@[no_expose, l_impl ConRon.Arena.openPisAtFvars]
def opaGo : FunDecl := lfn (n, e, i) locals (g, x, y, w, fv, b, u, ok) {
  if n == 0 { return (1, e) };
  if ⟦e⟧.tag != 6 { return (0, 0) };
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
-- con-ron: ConRon/Arena/Core.lean:2885-2895 ConRon.Arena.openPisAtFvarsF
-- con-ron: CHANGED since 01ecb31c — below `ConRon.Arena.openPisAtFvarsF`, `ConRon.Arena.openPisRawGo` changed; re-check the L code and its proofs, then delete this line
-- con-ron: CHANGED since 01ecb31c — `ConRon.Arena.openPisAtFvarsF` changed; re-check the L code and its proofs, then delete this line
@[no_expose, l_impl ConRon.Arena.openPisAtFvarsF]
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
