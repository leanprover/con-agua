module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
public import ConAgua.Arena.LiftL
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
public import ConAgua.L.ModelGen
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# `instantiate1`: the second interning walk, on the same scaffolding

con-ron's `instantiate1_go` (Lean twin `instantiate1Go`, `Arena/ExprOps.lean`) and its entry
`instantiate1Fast`: replace `bvar d` by `v`, lowering loose `bvar`s above `d` by one, memoized per
`(node, depth)` in `inst1C`, rebuilding through the store. `inst_go(h, d, v, fu)`, as the twin's
dispatcher: `abort` at `fu = 0` (the twin's depth counter `fuel`: it throws), the
derived-range cut-off (`der_b`), then the **tag** (not the view: the leaves and
unknown tags return `h` without reading the store), the `bvar` arm inline (`i = d`: `v`;
`i > d`: `intern_bvar(i - 1)`; else `h`), the compound tags call their arm at `fu - 1`. The arms
(`inst_app`, `inst_lam`, `inst_forall`, `inst_let`, `inst_proj`; the twin's `lam`/`forallE` share
`instantiate1ArmBind`) probe the memo **before** the view checks, as the twin does. The memo is
`imSch` (array 47, `CTL[44]`). Everything else is `Lift.lean`'s, renamed.

The models `instW`/`inst*W`, their continuations, guarded equations and the specs
`instGo_spec` are generated from the L text by `l_model` (`L/ModelGen.lean`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## The L code -/

/-- con-ron: ConRon/Arena/ExprOps.lean:251-277 ConRon.Arena.instantiate1Go -/
@[l_impl ConRon.Arena.instantiate1Go]
def instGo : FunDecl := lfn (h, d, v, fu) locals (x, g, t, i, r) {
  if fu == 0 { abort };
  x := call der_b(h);
  if x < 32767 && x <= d { return h };
  g := h >> 28;
  if g == 4 { r := call inst_app(h, d, v, fu - 1); return r };
  if g == 5 { r := call inst_lam(h, d, v, fu - 1); return r };
  if g == 6 { r := call inst_forall(h, d, v, fu - 1); return r };
  if g == 0 {
    t := ⟦h⟧.tier;
    i := ⟦h⟧.idx;
    if t != 0 && CTL.u64[1] == 0 { abort };
    if BVAR⟨t⟩.count <= i { abort };
    x := BVAR⟨t, i⟩.i;
    if x == d { return v };
    if d < x { r := call intern_bvar(x - 1); return r };
    return h
  };
  if g == 7 { r := call inst_let(h, d, v, fu - 1); return r };
  if g == 9 { r := call inst_proj(h, d, v, fu - 1); return r };
  return h
}

/-- con-ron: ConRon/Arena/ExprOps.lean:279-294 ConRon.Arena.instantiate1ArmApp -/
@[l_impl ConRon.Arena.instantiate1ArmApp]
def instApp : FunDecl := lfn (h, d, v, fu) locals (fd, j, e0, t, i, f, a, x, y, r, u) {
  (fd, j, e0) := call if_find(h, d);
  if fd != 0 { return IMEMO.u64[j * 4 + 3] };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if APP⟨t⟩.count <= i { abort };
  f := APP⟨t, i⟩.f;
  a := APP⟨t, i⟩.a;
  x := call inst_go(f, d, v, fu);
  y := call inst_go(a, d, v, fu);
  r := call mk_app(x, y);
  (fd, j, e0) := call if_find(h, d);
  u := call if_put(h, d, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:296-312 ConRon.Arena.instantiate1ArmBind -/
@[l_impl ConRon.Arena.instantiate1ArmBind]
def instLam : FunDecl := lfn (h, d, v, fu) locals (fd, j, e0, t, i, f, a, x, y, r, u) {
  if d + 1 == 0 { abort };
  (fd, j, e0) := call if_find(h, d);
  if fd != 0 { return IMEMO.u64[j * 4 + 3] };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if LAM⟨t⟩.count <= i { abort };
  f := LAM⟨t, i⟩.ty;
  a := LAM⟨t, i⟩.b;
  x := call inst_go(f, d, v, fu);
  y := call inst_go(a, d + 1, v, fu);
  r := call mk_lam(x, y);
  (fd, j, e0) := call if_find(h, d);
  u := call if_put(h, d, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:296-312 ConRon.Arena.instantiate1ArmBind -/
@[l_impl ConRon.Arena.instantiate1ArmBind]
def instForall : FunDecl := lfn (h, d, v, fu) locals (fd, j, e0, t, i, f, a, x, y, r, u) {
  if d + 1 == 0 { abort };
  (fd, j, e0) := call if_find(h, d);
  if fd != 0 { return IMEMO.u64[j * 4 + 3] };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if FORALL⟨t⟩.count <= i { abort };
  f := FORALL⟨t, i⟩.ty;
  a := FORALL⟨t, i⟩.b;
  x := call inst_go(f, d, v, fu);
  y := call inst_go(a, d + 1, v, fu);
  r := call mk_forall(x, y);
  (fd, j, e0) := call if_find(h, d);
  u := call if_put(h, d, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:314-330 ConRon.Arena.instantiate1ArmLet -/
@[l_impl ConRon.Arena.instantiate1ArmLet]
def instLet : FunDecl := lfn (h, d, v, fu) locals (fd, j, e0, t, i, f, a, b, x, y, z, r, u) {
  if d + 1 == 0 { abort };
  (fd, j, e0) := call if_find(h, d);
  if fd != 0 { return IMEMO.u64[j * 4 + 3] };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if LET⟨t⟩.count <= i { abort };
  f := LET⟨t, i⟩.ty;
  a := LET⟨t, i⟩.v;
  b := LET⟨t, i⟩.b;
  x := call inst_go(f, d, v, fu);
  y := call inst_go(a, d, v, fu);
  z := call inst_go(b, d + 1, v, fu);
  r := call mk_let(x, y, z);
  (fd, j, e0) := call if_find(h, d);
  u := call if_put(h, d, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:332-346 ConRon.Arena.instantiate1ArmProj -/
@[l_impl ConRon.Arena.instantiate1ArmProj]
def instProj : FunDecl := lfn (h, d, v, fu) locals (fd, j, e0, t, i, nm, ix, e, x, r, u) {
  (fd, j, e0) := call if_find(h, d);
  if fd != 0 { return IMEMO.u64[j * 4 + 3] };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if PROJ⟨t⟩.count <= i { abort };
  nm := PROJ⟨t, i⟩.n;
  ix := PROJ⟨t, i⟩.i;
  e := PROJ⟨t, i⟩.e;
  x := call inst_go(e, d, v, fu);
  r := call mk_proj(nm, ix, x);
  (fd, j, e0) := call if_find(h, d);
  u := call if_put(h, d, r, fd, j);
  return r
}

/-! ## The program and its specs -/

/-- What the specs need of the program. -/
structure InstProg (p : Prog) : Prop where
  base : LiftProg p
  iff : p.lookup "if_find" = some (memoFindG imSch)
  ifp : p.lookup "if_put" = some (memoPutG imSch)
  ifc : p.lookup "if_clear" = some (memoClearG imSch)
  go : p.lookup "inst_go" = some instGo
  app : p.lookup "inst_app" = some instApp
  lam : p.lookup "inst_lam" = some instLam
  fa : p.lookup "inst_forall" = some instForall
  le : p.lookup "inst_let" = some instLet
  pj : p.lookup "inst_proj" = some instProj

/-! ## The models and the specs (generated) -/

/-- **`inst_go` and its arms are their models** `instW`, `instAppW`, …, at every fuel. -/
l_model instGo_spec (p : Prog) (hp : InstProg p)
  fns [hp.go ↦ instW, hp.app ↦ instAppW, hp.lam ↦ instLamW, hp.fa ↦ instForallW,
    hp.le ↦ instLetW, hp.pj ↦ instProjW]
  specs [derB_spec p (hp.base.get "der_b") n, internBVar_spec p (hp.base.get "bvar_find") (hp.base.get "bvar_push") (hp.base.get "intern_bvar") n,
    memoFindG_spec imSch p _ hp.iff n, memoPutG_spec imSch p _ hp.ifp n,
    mkApp_spec p (hp.base.get "der_b") (hp.base.get "app_find") (hp.base.get "app_push") (hp.base.get "intern_app") (hp.base.get "mk_app") n,
    mkLam_spec p (hp.base.get "der_b") (hp.base.get "lam_find") (hp.base.get "lam_push") (hp.base.get "intern_lam") (hp.base.get "mk_lam") n,
    mkForall_spec p (hp.base.get "der_b") (hp.base.get "forall_find") (hp.base.get "forall_push") (hp.base.get "intern_forall") (hp.base.get "mk_forall") n,
    mkLet_spec p (hp.base.get "der_b") (hp.base.get "letE_find") (hp.base.get "letE_push") (hp.base.get "intern_letE") (hp.base.get "mk_let") n,
    mkProj_spec p (hp.base.get "der_b") (hp.base.get "proj_find") (hp.base.get "proj_push") (hp.base.get "intern_proj") (hp.base.get "mk_proj") n]
  grind [arena_grind] fold [tierW, idxW]
  extra [evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  finish [tierW, idxW] gen 20 heartbeats 1000000

end L.Arena
