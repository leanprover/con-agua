module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
import ConAgua.Census.Attr
public import ConAgua.Arena.Abs1
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# `abstractRange`: close `k` free variables at once, on `Abs1.lean`'s scaffolding

con-ron's executed `abstractRangeGo d k` (Lean twin `Arena/ExprOps.lean`, con-leche's
`abstractRangeC`) and its entry `abstractRangeFast`: replace `fvar i`, `d ≤ i < d + k`, by
`bvar (c + (d + k - 1 - i))`, the cursor `c` bumped under binders. It is `abstract1Go` with the
range `(d, k)` for the single `d` and the cursor `c` for `k`: the same cut-off (`ab_fvb`, `fvarB ≤
d`), the same memo `abs1C` keyed `(h, c)` (`Abs1.lean`; the two walks never nest, each entry clears
it), the same rebuild on change (`rbAppW` …). The new pieces: the `fvar` arm's range test, the
entry's `k = 0` identity, and two capacity checks in the `fvar` arm the twin (over `Nat`) does not
need: `d + k` and `c + (d + k - 1 - i)` must not wrap. The depth counter `fu` (last argument) is
`Abs1.lean`'s: the twin's `fuel` exactly, `abort` at `0`, `ab_fvb(h, fu - 1)` and
the arms at `fu - 1`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- con-ron: ConRon/Arena/ExprOps.lean:1789-1810 ConRon.Arena.abstractRangeGo -/
@[no_expose, l_impl ConRon.Arena.abstractRangeGo]
def arGo : FunDecl := lfn (h, c, d, k, fu) locals (x, r) {
  if fu == 0 { abort };
  x := call ab_fvb(h, fu - 1);
  if x <= d { return h };
  r := call ar_node(h, c, d, k, fu - 1);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1789-1810 ConRon.Arena.abstractRangeGo
con-ron: ConRon/Arena/ExprOps.lean:1778-1785 ConRon.Arena.absRangeArmFVar -/
@[no_expose, l_impl ConRon.Arena.absRangeArmFVar]
def arNode : FunDecl := lfn (h, c, d, k, fu) locals (x, g, t, i, v, r) {
  g := ⟦h⟧.tag;
  if g == 4 { r := call ar_app(h, c, d, k, fu); return r };
  if g == 5 { r := call ar_lam(h, c, d, k, fu); return r };
  if g == 6 { r := call ar_forall(h, c, d, k, fu); return r };
  if g == 1 {
    (t, i) := node FVAR⟦h⟧;
    if d + k < d { abort };
    x := FVAR⟨t, i⟩.i;
    if d <= x && x < d + k {
      v := c + (d + k - 1 - x);
      if v < c { abort };
      r := call intern_bvar(v);
      return r
    };
    return h
  };
  if g == 7 { r := call ar_let(h, c, d, k, fu); return r };
  if g == 9 { r := call ar_proj(h, c, d, k, fu); return r };
  return h
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1812-1827 ConRon.Arena.absRangeGoArmApp -/
@[no_expose, l_impl ConRon.Arena.absRangeGoArmApp]
def arApp : FunDecl := lfn (h, c, d, k, fu) locals (fd, j, e0, t, i, f, a, x, y, r, u) {
  (fd, j, e0) := call ab_find(h, c);
  if fd != 0 { return ABMEMO.u64[j * 4 + 3] };
  (t, i) := node APP⟦h⟧;
  f := APP⟨t, i⟩.f;
  a := APP⟨t, i⟩.a;
  x := call ar_go(f, c, d, k, fu);
  y := call ar_go(a, c, d, k, fu);
  if x == f && y == a { r := h } else { r := call mk_app(x, y) };
  (fd, j, e0) := call ab_find(h, c);
  u := call ab_put(h, c, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1829-1844 ConRon.Arena.absRangeGoArmBind -/
@[no_expose, l_impl ConRon.Arena.absRangeGoArmBind]
def arLam : FunDecl := lfn (h, c, d, k, fu) locals (fd, j, e0, t, i, f, a, x, y, r, u) {
  if c + 1 == 0 { abort };
  (fd, j, e0) := call ab_find(h, c);
  if fd != 0 { return ABMEMO.u64[j * 4 + 3] };
  (t, i) := node LAM⟦h⟧;
  f := LAM⟨t, i⟩.ty;
  a := LAM⟨t, i⟩.b;
  x := call ar_go(f, c, d, k, fu);
  y := call ar_go(a, c + 1, d, k, fu);
  if x == f && y == a { r := h } else { r := call mk_lam(x, y) };
  (fd, j, e0) := call ab_find(h, c);
  u := call ab_put(h, c, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1829-1844 ConRon.Arena.absRangeGoArmBind -/
@[no_expose, l_impl ConRon.Arena.absRangeGoArmBind]
def arForall : FunDecl := lfn (h, c, d, k, fu) locals (fd, j, e0, t, i, f, a, x, y, r, u) {
  if c + 1 == 0 { abort };
  (fd, j, e0) := call ab_find(h, c);
  if fd != 0 { return ABMEMO.u64[j * 4 + 3] };
  (t, i) := node FORALL⟦h⟧;
  f := FORALL⟨t, i⟩.ty;
  a := FORALL⟨t, i⟩.b;
  x := call ar_go(f, c, d, k, fu);
  y := call ar_go(a, c + 1, d, k, fu);
  if x == f && y == a { r := h } else { r := call mk_forall(x, y) };
  (fd, j, e0) := call ab_find(h, c);
  u := call ab_put(h, c, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1846-1862 ConRon.Arena.absRangeGoArmLet -/
@[no_expose, l_impl ConRon.Arena.absRangeGoArmLet]
def arLet : FunDecl := lfn (h, c, d, k, fu) locals (fd, j, e0, t, i, f, a, b, x, y, z, r, u) {
  if c + 1 == 0 { abort };
  (fd, j, e0) := call ab_find(h, c);
  if fd != 0 { return ABMEMO.u64[j * 4 + 3] };
  (t, i) := node LET⟦h⟧;
  f := LET⟨t, i⟩.ty;
  a := LET⟨t, i⟩.v;
  b := LET⟨t, i⟩.b;
  x := call ar_go(f, c, d, k, fu);
  y := call ar_go(a, c, d, k, fu);
  z := call ar_go(b, c + 1, d, k, fu);
  if x == f && y == a && z == b { r := h } else { r := call mk_let(x, y, z) };
  (fd, j, e0) := call ab_find(h, c);
  u := call ab_put(h, c, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1864-1878 ConRon.Arena.absRangeGoArmProj -/
@[no_expose, l_impl ConRon.Arena.absRangeGoArmProj]
def arProj : FunDecl := lfn (h, c, d, k, fu) locals (fd, j, e0, t, i, nm, ix, e, x, r, u) {
  (fd, j, e0) := call ab_find(h, c);
  if fd != 0 { return ABMEMO.u64[j * 4 + 3] };
  (t, i) := node PROJ⟦h⟧;
  nm := PROJ⟨t, i⟩.n;
  ix := PROJ⟨t, i⟩.i;
  e := PROJ⟨t, i⟩.e;
  x := call ar_go(e, c, d, k, fu);
  if x == e { r := h } else { r := call mk_proj(nm, ix, x) };
  (fd, j, e0) := call ab_find(h, c);
  u := call ab_put(h, c, r, fd, j);
  return r
}



/-! ## The program and its specs -/

/-- The walk without its entry, over `absWalkProg`. -/
def arWalkProg : Prog :=
  [("ar_go", arGo), ("ar_node", arNode), ("ar_app", arApp), ("ar_lam", arLam),
    ("ar_forall", arForall), ("ar_let", arLet), ("ar_proj", arProj)] ++ absWalkProg

/-- What the specs need of the program: `arWalkProg`'s functions. -/
def ArProg (p : Prog) : Prop := ProgHas p arWalkProg

theorem ArProg.base {p : Prog} (hp : ArProg p) : AbsProg p := hp.right


end L.Arena
