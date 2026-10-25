module

public import ConAgua.Arena.MemoLib
public import ConAgua.Arena.ExprMk
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
import ConAgua.Census.Attr
public import ConAgua.L.ModelGen
public import ConAgua.L.ProgHas

@[expose] public section

/-!
# `liftLooseBVars`: the first walk that interns its results

con-ron's `lift_loose_bvars_go` (Lean twin `liftLooseBVarsGo`, `Arena/ExprOps.lean:668`) and its
entry `lift_loose_bvars_fast` (`liftLooseBVarsFast`): bump every loose bound variable `≥ c` by
`amount`, memoized per `(node, cutoff)` in `liftC`, rebuilding the term through the store.

`lift_go(h, c, k, fu)` (`k` the amount, `fu` the twin's `fuel` as a counter), as
the twin's dispatcher:
* `abort` at `fu = 0` (the twin throws), the arms called at `fu - 1`;
* the **cutoff**: `der_b(h)` (the range field of the derived word, `ExprMk.lean`); if it is below
  `satRange` and at most `c`, return `h`;
* the **view** checks (scratch tier, the tier's count; the twin's `view` fails there), then per tag:
  `bvar i`: `i < c` returns `h`, else `intern_bvar(i + k)` (an `abort` where `i + k` wraps);
  `fvar`, `sort`, `const`, `lit`: `h`; the compound tags call their arm.
* the **arms** `lift_app`, `lift_lam`, `lift_forall`, `lift_let`, `lift_proj` (the twin's
  `liftArmApp`, …): probe the memo `lf_find(h, c)`; on a hit return the value; else walk the
  children (a binder's body and `letE`'s body at `c + 1`), rebuild with `mk_*`, probe again and
  `lf_put`.

`lift_entry(h, k, c, f)` is `liftLooseBVarsFast f k c h`: `lf_clear(); r := lift_go(h, c, k, f); lf_clear()`.
The memo is the library's (`lfSch`: array 41, `CTL[42]`, `CTL[43]`), keys `(h, c)`.

The models `liftW`/`lift*W`, their continuations `lift*W.kᵢ`, their guarded equations
`lift*W.armᵢ` and the specs `liftGo_spec` are generated from the L text by `l_model`
(`L/ModelGen.lean`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## The L code -/

/-- con-ron: ConRon/Arena/ExprOps.lean:655-688 ConRon.Arena.liftLooseBVarsGo -/
@[l_impl ConRon.Arena.liftLooseBVarsGo]
def liftGo : FunDecl := lfn (h, c, k, fu) locals (x, g, t, i, r) {
  if fu == 0 { abort };
  x := call der_b(h);
  if x < 32767 && x <= c { return h };
  g := h >> 28;
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if g == 0 {
    if BVAR⟨t⟩.count <= i { abort };
    x := BVAR⟨t, i⟩.i;
    if x < c { return h };
    if x + k < x { abort };
    r := call intern_bvar(x + k);
    return r
  };
  if g == 4 { if APP⟨t⟩.count <= i { abort }; r := call lift_app(h, c, k, fu - 1); return r };
  if g == 5 { if LAM⟨t⟩.count <= i { abort }; r := call lift_lam(h, c, k, fu - 1); return r };
  if g == 6 { if FORALL⟨t⟩.count <= i { abort }; r := call lift_forall(h, c, k, fu - 1); return r };
  if g == 7 { if LET⟨t⟩.count <= i { abort }; r := call lift_let(h, c, k, fu - 1); return r };
  if g == 9 { if PROJ⟨t⟩.count <= i { abort }; r := call lift_proj(h, c, k, fu - 1); return r };
  if g == 1 { if FVAR⟨t⟩.count <= i { abort }; return h };
  if g == 2 { if SORT⟨t⟩.count <= i { abort }; return h };
  if g == 3 { if CONST⟨t⟩.count <= i { abort }; return h };
  if g == 8 { if LIT⟨t⟩.count <= i { abort }; return h };
  abort
}

/-- con-ron: ConRon/Arena/ExprOps.lean:690-702 ConRon.Arena.liftArmApp -/
@[l_impl ConRon.Arena.liftArmApp]
def liftApp : FunDecl := lfn (h, c, k, fu) locals (fd, j, d, t, i, f, a, x, y, r, u) {
  (fd, j, d) := call lf_find(h, c);
  if fd != 0 { return LMEMO.u64[j * 4 + 3] };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  f := APP⟨t, i⟩.f;
  a := APP⟨t, i⟩.a;
  x := call lift_go(f, c, k, fu);
  y := call lift_go(a, c, k, fu);
  r := call mk_app(x, y);
  (fd, j, d) := call lf_find(h, c);
  u := call lf_put(h, c, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:704-716 ConRon.Arena.liftArmLam -/
@[l_impl ConRon.Arena.liftArmLam]
def liftLam : FunDecl := lfn (h, c, k, fu) locals (fd, j, d, t, i, f, a, x, y, r, u) {
  if c + 1 == 0 { abort };
  (fd, j, d) := call lf_find(h, c);
  if fd != 0 { return LMEMO.u64[j * 4 + 3] };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  f := LAM⟨t, i⟩.ty;
  a := LAM⟨t, i⟩.b;
  x := call lift_go(f, c, k, fu);
  y := call lift_go(a, c + 1, k, fu);
  r := call mk_lam(x, y);
  (fd, j, d) := call lf_find(h, c);
  u := call lf_put(h, c, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:718-730 ConRon.Arena.liftArmForallE -/
@[l_impl ConRon.Arena.liftArmForallE]
def liftForall : FunDecl := lfn (h, c, k, fu) locals (fd, j, d, t, i, f, a, x, y, r, u) {
  if c + 1 == 0 { abort };
  (fd, j, d) := call lf_find(h, c);
  if fd != 0 { return LMEMO.u64[j * 4 + 3] };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  f := FORALL⟨t, i⟩.ty;
  a := FORALL⟨t, i⟩.b;
  x := call lift_go(f, c, k, fu);
  y := call lift_go(a, c + 1, k, fu);
  r := call mk_forall(x, y);
  (fd, j, d) := call lf_find(h, c);
  u := call lf_put(h, c, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:732-745 ConRon.Arena.liftArmLet -/
@[l_impl ConRon.Arena.liftArmLet]
def liftLet : FunDecl := lfn (h, c, k, fu) locals (fd, j, d, t, i, f, a, b, x, y, z, r, u) {
  if c + 1 == 0 { abort };
  (fd, j, d) := call lf_find(h, c);
  if fd != 0 { return LMEMO.u64[j * 4 + 3] };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  f := LET⟨t, i⟩.ty;
  a := LET⟨t, i⟩.v;
  b := LET⟨t, i⟩.b;
  x := call lift_go(f, c, k, fu);
  y := call lift_go(a, c, k, fu);
  z := call lift_go(b, c + 1, k, fu);
  r := call mk_let(x, y, z);
  (fd, j, d) := call lf_find(h, c);
  u := call lf_put(h, c, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:747-758 ConRon.Arena.liftArmProj -/
@[l_impl ConRon.Arena.liftArmProj]
def liftProj : FunDecl := lfn (h, c, k, fu) locals (fd, j, d, t, i, nm, ix, e, x, r, u) {
  (fd, j, d) := call lf_find(h, c);
  if fd != 0 { return LMEMO.u64[j * 4 + 3] };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  nm := PROJ⟨t, i⟩.n;
  ix := PROJ⟨t, i⟩.i;
  e := PROJ⟨t, i⟩.e;
  x := call lift_go(e, c, k, fu);
  r := call mk_proj(nm, ix, x);
  (fd, j, d) := call lf_find(h, c);
  u := call lf_put(h, c, r, fd, j);
  return r
}

/-! ## The program and its specs -/

/-- The functions of `LiftProg`. -/
def liftProgFns : Prog :=
  [("der_b", derB), ("bvar_find", bvarFind), ("bvar_push", bvarPush), ("intern_bvar", internBVar),
   ("lf_find", memoFindG lfSch), ("lf_put", memoPutG lfSch), ("lf_clear", memoClearG lfSch),
   ("lift_go", liftGo), ("lift_app", liftApp), ("lift_lam", liftLam), ("lift_forall", liftForall),
   ("lift_let", liftLet), ("lift_proj", liftProj), ("mk_app", mkApp), ("app_find", appFind),
   ("app_push", appPush), ("intern_app", internApp), ("mk_lam", mkLam), ("lam_find", lamFind),
   ("lam_push", lamPush), ("intern_lam", internLamL), ("mk_forall", mkForall),
   ("forall_find", forallFind), ("forall_push", forallPush), ("intern_forall", internForallL),
   ("mk_let", mkLet), ("letE_find", letFind), ("letE_push", letPush), ("intern_letE", internLet),
   ("mk_proj", mkProj), ("proj_find", projFind), ("proj_push", projPush),
   ("intern_proj", internProj)]

/-- What the specs need of the program: every function the walk calls, by name. -/
abbrev LiftProg (p : Prog) : Prop := ProgHas p liftProgFns

/-! ## The models and the specs (generated) -/

/-- **`lift_go` and its arms are their models** `liftW`, `liftAppW`, …, at every fuel. -/
l_model liftGo_spec (p : Prog) (hp : LiftProg p)
  fns [(hp.get "lift_go") ↦ liftW, (hp.get "lift_app") ↦ liftAppW, (hp.get "lift_lam") ↦ liftLamW, (hp.get "lift_forall") ↦ liftForallW,
    (hp.get "lift_let") ↦ liftLetW, (hp.get "lift_proj") ↦ liftProjW]
  specs [derB_spec p (hp.get "der_b") n, internBVar_spec p (hp.get "bvar_find") (hp.get "bvar_push") (hp.get "intern_bvar") n,
    memoFindG_spec lfSch p _ (hp.get "lf_find") n, memoPutG_spec lfSch p _ (hp.get "lf_put") n,
    mkApp_spec p (hp.get "der_b") (hp.get "app_find") (hp.get "app_push") (hp.get "intern_app") (hp.get "mk_app") n,
    mkLam_spec p (hp.get "der_b") (hp.get "lam_find") (hp.get "lam_push") (hp.get "intern_lam") (hp.get "mk_lam") n,
    mkForall_spec p (hp.get "der_b") (hp.get "forall_find") (hp.get "forall_push") (hp.get "intern_forall") (hp.get "mk_forall") n,
    mkLet_spec p (hp.get "der_b") (hp.get "letE_find") (hp.get "letE_push") (hp.get "intern_letE") (hp.get "mk_let") n,
    mkProj_spec p (hp.get "der_b") (hp.get "proj_find") (hp.get "proj_push") (hp.get "intern_proj") (hp.get "mk_proj") n]
  grind [arena_grind] fold [tierW, idxW]
  extra [evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  finish [tierW, idxW] gen 20 heartbeats 1000000

end L.Arena
