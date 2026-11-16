module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
import ConAgua.Census.Attr
public import ConAgua.Arena.LiftL
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# `instantiateList`: the bulk instantiation, over a slice of the spine stack

con-ron's two walks (Lean twins in `Arena/ExprOps.lean`): the pure `instantiateList vs` and the
memoized `instantiateListGo vs` (memo `instLC`, key `(node, depth)`), entry
`instantiateListFast`. The substitution `vs : Array EIdx` (push order: the innermost binder's
argument is the LAST entry) is a slice `(o, l)` of the spine stack, word array 144 (`SPN` of
`WhnfBase.lean`, here `ILSPN`: the caller's `inst_list(e, off, cnt, d)` interface; `SpineR`
relates it). Each walk is `Inst1.lean`'s shape with `v` replaced by the slice, except:

* **The pure walk's `bvar` arm** (`il_bvar`): `j < d` is `h`; for `q = j - d < l` the
  replacement `v` is the slice's entry `l - 1 - q`; if `v` passes the cut-off it is the answer,
  else the walk recurses into `v` over the slice's **last `q` entries** (`lastEidx vs q`):
  `(o + (l - q), q)`, an `O(1)` adjustment, no copy. Past the slice: `intern_bvar(j - l)`.
* **The memo walk's `bvar` case** calls the pure walk on the whole slice (`il_go`), as the twin
  calls `instantiateList vs`.
* No arm rebuilds on change (the twin interns unconditionally).
* **The depth counter `fu`** (last argument) is the twin's `fuel` exactly: both
  dispatchers `abort` at `fu = 0` and run their arms (and `ilg_go`'s `bvar` call of `il_go`) at
  `fu - 1`; the arms pass their `fu` to their children, `il_bvar` to the replacement's walk.

The memo `instLC` is new: array 50 `ILMEMO`, stamp `CTL[50]`, count `CTL[51]`, `lfKey`'s codec;
like `abs1C` (`Abs1.lean`) it is kept out of `MemosR`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- `instLC`: array 50, stamp `CTL[50]`, count `CTL[51]`. -/
abbrev ilSch : MemoSch := ⟨ILMEMO, 50⟩

/-- The slice's word at `i`. -/
def slW (m : Mem) (i : Word) : Word := rdW (m.arr64 ILSPN) i

/-- The cut-off (shared by both dispatchers and the `bvar` arm's replacement). -/
abbrev ilCut (m : Mem) (h d : Word) : Prop := derBW m h < 32767 ∧ derBW m h ≤ d

/-! ## The L code: the pure walk -/

/-- con-ron: ConRon/Arena/ExprOps.lean:395-423 ConRon.Arena.instantiateList -/
@[no_expose, l_impl ConRon.Arena.instantiateList]
def ilGo : FunDecl := lfn (h, d, o, l, fu) locals (x, g, r) {
  if fu == 0 { abort };
  x := call der_bv(h);
  if x < 32767 && x <= d { return h };
  g := ⟦h⟧.tag;
  if g == 4 { r := call il_app(h, d, o, l, fu - 1); return r };
  if g == 5 { r := call il_lam(h, d, o, l, fu - 1); return r };
  if g == 6 { r := call il_forall(h, d, o, l, fu - 1); return r };
  if g == 7 { r := call il_let(h, d, o, l, fu - 1); return r };
  if g == 9 { r := call il_proj(h, d, o, l, fu - 1); return r };
  if g == 0 { r := call il_bvar(h, d, o, l, fu - 1); return r };
  return h
}

/-- con-ron: ConRon/Arena/ExprOps.lean:425-435 ConRon.Arena.instListArmApp -/
@[no_expose, l_impl ConRon.Arena.instListArmApp]
def ilApp : FunDecl := lfn (h, d, o, l, fu) locals (t, i, f, a, x, y, r) {
  (t, i) := node APP⟦h⟧;
  f := APP⟨t, i⟩.f;
  a := APP⟨t, i⟩.a;
  x := call il_go(f, d, o, l, fu);
  y := call il_go(a, d, o, l, fu);
  r := call mk_app(x, y);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:437-447 ConRon.Arena.instListArmBind -/
@[no_expose, l_impl ConRon.Arena.instListArmBind]
def ilLam : FunDecl := lfn (h, d, o, l, fu) locals (t, i, f, a, x, y, r) {
  if d + 1 == 0 { abort };
  (t, i) := node LAM⟦h⟧;
  f := LAM⟨t, i⟩.ty;
  a := LAM⟨t, i⟩.b;
  x := call il_go(f, d, o, l, fu);
  y := call il_go(a, d + 1, o, l, fu);
  r := call mk_lam(x, y);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:437-447 ConRon.Arena.instListArmBind -/
@[no_expose, l_impl ConRon.Arena.instListArmBind]
def ilForall : FunDecl := lfn (h, d, o, l, fu) locals (t, i, f, a, x, y, r) {
  if d + 1 == 0 { abort };
  (t, i) := node FORALL⟦h⟧;
  f := FORALL⟨t, i⟩.ty;
  a := FORALL⟨t, i⟩.b;
  x := call il_go(f, d, o, l, fu);
  y := call il_go(a, d + 1, o, l, fu);
  r := call mk_forall(x, y);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:449-460 ConRon.Arena.instListArmLet -/
@[no_expose, l_impl ConRon.Arena.instListArmLet]
def ilLet : FunDecl := lfn (h, d, o, l, fu) locals (t, i, f, a, b, x, y, z, r) {
  if d + 1 == 0 { abort };
  (t, i) := node LET⟦h⟧;
  f := LET⟨t, i⟩.ty;
  a := LET⟨t, i⟩.v;
  b := LET⟨t, i⟩.b;
  x := call il_go(f, d, o, l, fu);
  y := call il_go(a, d, o, l, fu);
  z := call il_go(b, d + 1, o, l, fu);
  r := call mk_let(x, y, z);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:462-471 ConRon.Arena.instListArmProj -/
@[no_expose, l_impl ConRon.Arena.instListArmProj]
def ilProj : FunDecl := lfn (h, d, o, l, fu) locals (t, i, nm, ix, e, x, r) {
  (t, i) := node PROJ⟦h⟧;
  nm := PROJ⟨t, i⟩.n;
  ix := PROJ⟨t, i⟩.i;
  e := PROJ⟨t, i⟩.e;
  x := call il_go(e, d, o, l, fu);
  r := call mk_proj(nm, ix, x);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:473-498 ConRon.Arena.instListArmBVar -/
@[no_expose, l_impl ConRon.Arena.instListArmBVar]
def ilBVar : FunDecl := lfn (h, d, o, l, fu) locals (t, i, j, q, v, x, r) {
  (t, i) := node BVAR⟦h⟧;
  j := BVAR⟨t, i⟩.i;
  if j < d { return h };
  q := j - d;
  if q < l {
    v := ILSPN.u64[o + (l - 1 - q)];
    x := call der_bv(v);
    if x < 32767 && x <= d { return v };
    r := call il_go(v, d, o + (l - q), q, fu);
    return r
  };
  r := call intern_bvar(j - l);
  return r
}

/-! ## The L code: the memo walk -/

/-- con-ron: ConRon/Arena/ExprOps.lean:527-551 ConRon.Arena.instantiateListGo -/
@[no_expose, l_impl ConRon.Arena.instantiateListGo]
def ilgGo : FunDecl := lfn (h, d, o, l, fu) locals (x, g, r) {
  if fu == 0 { abort };
  x := call der_bv(h);
  if x < 32767 && x <= d { return h };
  g := ⟦h⟧.tag;
  if g == 4 { r := call ilg_app(h, d, o, l, fu - 1); return r };
  if g == 5 { r := call ilg_lam(h, d, o, l, fu - 1); return r };
  if g == 6 { r := call ilg_forall(h, d, o, l, fu - 1); return r };
  if g == 7 { r := call ilg_let(h, d, o, l, fu - 1); return r };
  if g == 9 { r := call ilg_proj(h, d, o, l, fu - 1); return r };
  if g == 0 { r := call il_go(h, d, o, l, fu - 1); return r };
  return h
}

/-- con-ron: ConRon/Arena/ExprOps.lean:553-568 ConRon.Arena.instListGoArmApp -/
@[no_expose, l_impl ConRon.Arena.instListGoArmApp]
def ilgApp : FunDecl := lfn (h, d, o, l, fu) locals (fd, j, e0, t, i, f, a, x, y, r, u) {
  (fd, j, e0) := call ilm_find(h, d);
  if fd != 0 { return ILMEMO.u64[j * 4 + 3] };
  (t, i) := node APP⟦h⟧;
  f := APP⟨t, i⟩.f;
  a := APP⟨t, i⟩.a;
  x := call ilg_go(f, d, o, l, fu);
  y := call ilg_go(a, d, o, l, fu);
  r := call mk_app(x, y);
  (fd, j, e0) := call ilm_find(h, d);
  u := call ilm_put(h, d, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:570-585 ConRon.Arena.instListGoArmBind -/
@[no_expose, l_impl ConRon.Arena.instListGoArmBind]
def ilgLam : FunDecl := lfn (h, d, o, l, fu) locals (fd, j, e0, t, i, f, a, x, y, r, u) {
  if d + 1 == 0 { abort };
  (fd, j, e0) := call ilm_find(h, d);
  if fd != 0 { return ILMEMO.u64[j * 4 + 3] };
  (t, i) := node LAM⟦h⟧;
  f := LAM⟨t, i⟩.ty;
  a := LAM⟨t, i⟩.b;
  x := call ilg_go(f, d, o, l, fu);
  y := call ilg_go(a, d + 1, o, l, fu);
  r := call mk_lam(x, y);
  (fd, j, e0) := call ilm_find(h, d);
  u := call ilm_put(h, d, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:570-585 ConRon.Arena.instListGoArmBind -/
@[no_expose, l_impl ConRon.Arena.instListGoArmBind]
def ilgForall : FunDecl := lfn (h, d, o, l, fu) locals (fd, j, e0, t, i, f, a, x, y, r, u) {
  if d + 1 == 0 { abort };
  (fd, j, e0) := call ilm_find(h, d);
  if fd != 0 { return ILMEMO.u64[j * 4 + 3] };
  (t, i) := node FORALL⟦h⟧;
  f := FORALL⟨t, i⟩.ty;
  a := FORALL⟨t, i⟩.b;
  x := call ilg_go(f, d, o, l, fu);
  y := call ilg_go(a, d + 1, o, l, fu);
  r := call mk_forall(x, y);
  (fd, j, e0) := call ilm_find(h, d);
  u := call ilm_put(h, d, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:587-603 ConRon.Arena.instListGoArmLet -/
@[no_expose, l_impl ConRon.Arena.instListGoArmLet]
def ilgLet : FunDecl := lfn (h, d, o, l, fu) locals (fd, j, e0, t, i, f, a, b, x, y, z, r, u) {
  if d + 1 == 0 { abort };
  (fd, j, e0) := call ilm_find(h, d);
  if fd != 0 { return ILMEMO.u64[j * 4 + 3] };
  (t, i) := node LET⟦h⟧;
  f := LET⟨t, i⟩.ty;
  a := LET⟨t, i⟩.v;
  b := LET⟨t, i⟩.b;
  x := call ilg_go(f, d, o, l, fu);
  y := call ilg_go(a, d, o, l, fu);
  z := call ilg_go(b, d + 1, o, l, fu);
  r := call mk_let(x, y, z);
  (fd, j, e0) := call ilm_find(h, d);
  u := call ilm_put(h, d, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:605-619 ConRon.Arena.instListGoArmProj -/
@[no_expose, l_impl ConRon.Arena.instListGoArmProj]
def ilgProj : FunDecl := lfn (h, d, o, l, fu) locals (fd, j, e0, t, i, nm, ix, e, x, r, u) {
  (fd, j, e0) := call ilm_find(h, d);
  if fd != 0 { return ILMEMO.u64[j * 4 + 3] };
  (t, i) := node PROJ⟦h⟧;
  nm := PROJ⟨t, i⟩.n;
  ix := PROJ⟨t, i⟩.i;
  e := PROJ⟨t, i⟩.e;
  x := call ilg_go(e, d, o, l, fu);
  r := call mk_proj(nm, ix, x);
  (fd, j, e0) := call ilm_find(h, d);
  u := call ilm_put(h, d, r, fd, j);
  return r
}

/-! ## The program -/

/-- The two walks without the entry, over `liftProg`. -/
def instListWalkProg : Prog :=
  [("ilm_find", memoFindG ilSch), ("ilm_put", memoPutG ilSch), ("ilm_clear", memoClearG ilSch),
    ("ilm_fit", memoClearFitG ilSch),
    ("il_go", ilGo), ("il_app", ilApp), ("il_lam", ilLam), ("il_forall", ilForall),
    ("il_let", ilLet), ("il_proj", ilProj), ("il_bvar", ilBVar), ("ilg_go", ilgGo),
    ("ilg_app", ilgApp), ("ilg_lam", ilgLam), ("ilg_forall", ilgForall), ("ilg_let", ilgLet),
    ("ilg_proj", ilgProj)] ++ liftProg

/-- What the specs need of the program: `instListWalkProg`'s functions. -/
def InstListProg (p : Prog) : Prop := ProgHas p instListWalkProg

theorem InstListProg.base {p : Prog} (hp : InstListProg p) : LiftProg p := by
  have h : ProgHas p liftProg := hp.right
  unfold LiftProg liftProgFns; repeat (first | exact ProgHas.nil | refine ProgHas.cons (h.get _) ?_)

end L.Arena
