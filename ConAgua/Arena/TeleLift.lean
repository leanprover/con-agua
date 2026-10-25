import ConAgua.Arena.IndIface
import ConAgua.Arena.WalkLift
import ConAgua.Census.Attr

/-!
# `instPisAtLift`, `fvarTypeD`, `fvarTypeDs` in L (lane `whnf3`)

Lane `induct`'s conventions (`IndStubs.lean`): lists are `IW` slices `(off, len)`, an `Option` result
`(ok, value)`, the walk fuel a word.

* `inst_pis_at_lift(f, off, len, e)`: con-ron's `instPisAtLift fuel xs e`: for each argument, the
  tag test, then the binder view (a dangling handle aborts, as `viewBind` fails),
  `instantiate1_lift_fast(f, body, a, 0)`; `(0, 0)` at a non-`∀` node.
* `fvar_type_d(e)`: `fvarTypeD`: an `fvar`'s annotation (the tag test, then the view), else `e`.
* `fvar_type_ds(off, len)`: `fvarTypeDs`, into a fresh `IW` slice.
-/

namespace L.Ind

open L.Arena

/-- con-ron: ConRon/Arena/ExprOps.lean:2038-2050 ConRon.Arena.instPisAtLift -/
@[l_impl ConRon.Arena.instPisAtLift]
def instPisAtLiftL : FunDecl := lfn (f, o, l, e) locals (h, k, g, x, y, z) {
  h := e;
  k := 0;
  while k < l {
    if h >> 28 != 6 { return (0, 0) };
    (g, x, y, z) := call e_view(h);
    h := call instantiate1_lift_fast(f, y, IW.u64[o + k], 0);
    k := k + 1
  };
  return (1, h)
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1369-1377 ConRon.Arena.fvarTypeD -/
@[l_impl ConRon.Arena.fvarTypeD]
def fvarTypeDL : FunDecl := lfn (e) locals (g, x, y, z) {
  if e >> 28 != 1 { return e };
  (g, x, y, z) := call e_view(e);
  return y
}

/-- con-ron: ConRon/Arena/CheckerBase.lean:157-165 ConRon.Arena.fvarTypeDs -/
@[l_impl ConRon.Arena.fvarTypeDs]
def fvarTypeDsL : FunDecl := lfn (o, l) locals (q, k, t) {
  q := call iw_alloc(l);
  k := 0;
  while k < l {
    t := call fvar_type_d(IW.u64[o + k]);
    IW.u64[q + k] := t;
    k := k + 1
  };
  return (q, l)
}

end L.Ind
