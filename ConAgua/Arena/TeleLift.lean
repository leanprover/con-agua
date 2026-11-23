module

public import ConAgua.Arena.IndIface
import ConAgua.Census.Attr

@[expose] public section

/-!
# `fvarTypeD`, `fvarTypeDs` in L (lane `whnf3`)

Lane `induct`'s conventions (`IndStubs.lean`): lists are `IW` slices `(off, len)`, an `Option` result
`(ok, value)`, the walk fuel a word.

* `fvar_type_d(e)`: `fvarTypeD`: an `fvar`'s annotation (the tag test, then the view), else `e`.
* `fvar_type_ds(off, len)`: `fvarTypeDs`, into a fresh `IW` slice.
-/

namespace L.Ind

open L.Arena

/-- con-ron: ConRon/Arena/ExprOps.lean:1400-1408 ConRon.Arena.fvarTypeD -/
@[no_expose, l_impl ConRon.Arena.fvarTypeD]
def fvarTypeDL : FunDecl := lfn (e) locals (g, x, y, z) {
  if ⟦e⟧.tag != 1 { return e };
  (g, x, y, z) := call e_view(e);
  return y
}

/-- con-ron: ConRon/Arena/CheckerBase.lean:161-169 ConRon.Arena.fvarTypeDs -/
@[no_expose, l_impl ConRon.Arena.fvarTypeDs]
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
