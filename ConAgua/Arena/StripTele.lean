
/-!
# `stripPis`, `stripLams` in L (lane `whnf3`)

con-ron's `stripPis k e` / `stripLams k e` (`Arena/ExprOps.lean:1329-1355`): strip `k` leading
`∀`s (`λ`s), returning their domains (outermost first) and the body, or `none` when a node before the
`k`-th is not a binder of the kind. Lane `induct`'s convention: `(ok, off, len, body)`, the domains
an `IW` slice (`iw_alloc`), `len = k` when `ok = 1`. The loop allocates one `IW` word per binder
(consecutive: nothing else allocates in between) and, on `none`, puts the `IW` top back (the twin
drops its partial list). A dangling binder handle aborts (`e_view`), as the twin's `viewBind` fails.
The twin's recursion is structural on `k`; the L loop counts `n` up to `k` (no fuel).
-/

namespace L.Ind

open L.Arena

/-- `strip_pis`'s loop (named, for its spec). -/
def stripPisLoop : Stmt := lblk (k, e, o, n, h, g, x, y, z, q) {
  while n < k {
    if h >> 28 != 6 { CTL.u64[200] := o; return (0, 0, 0, 0) };
    (g, x, y, z) := call e_view(h);
    q := call iw_alloc(1);
    IW.u64[q] := x;
    h := y;
    n := n + 1
  }
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1342-1355 ConRon.Arena.stripPis -/
@[l_impl ConRon.Arena.stripPis]
def stripPisL : FunDecl := lfn (k, e) locals (o, n, h, g, x, y, z, q) {
  o := CTL.u64[200];
  n := 0;
  h := e;
  ⟪stripPisLoop⟫;
  return (1, o, k, h)
}

/-- `strip_lams`'s loop (named, for its spec). -/
def stripLamsLoop : Stmt := lblk (k, e, o, n, h, g, x, y, z, q) {
  while n < k {
    if h >> 28 != 5 { CTL.u64[200] := o; return (0, 0, 0, 0) };
    (g, x, y, z) := call e_view(h);
    q := call iw_alloc(1);
    IW.u64[q] := x;
    h := y;
    n := n + 1
  }
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1327-1340 ConRon.Arena.stripLams -/
@[l_impl ConRon.Arena.stripLams]
def stripLamsL : FunDecl := lfn (k, e) locals (o, n, h, g, x, y, z, q) {
  o := CTL.u64[200];
  n := 0;
  h := e;
  ⟪stripLamsLoop⟫;
  return (1, o, k, h)
}

end L.Ind
