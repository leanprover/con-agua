module

public import ConAgua.Arena.MemoLib
public import ConAgua.Arena.ExprMk
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
import ConAgua.Census.Attr
public import ConAgua.L.ModelGen

@[expose] public section

/-!
# `liftLooseBVars`: the first walk that interns its results

con-ron's `lift_loose_bvars_go` (Lean twin `liftLooseBVarsGo`, `Arena/ExprOps.lean:668`) and its
entry `lift_loose_bvars_fast` (`liftLooseBVarsFast`): bump every loose bound variable `≥ c` by
`amount`, memoized per `(node, cutoff)` in `liftC`, rebuilding the term through the store.

`lift_go(h, c, k)` (`k` the amount), as the twin's dispatcher:
* the **cutoff**: `der_b(h)` (the range field of the derived word, `ExprMk.lean`); if it is below
  `satRange` and at most `c`, return `h`;
* the **view** checks (scratch tier, the tier's count; the twin's `view` fails there), then per tag:
  `bvar i`: `i < c` returns `h`, else `intern_bvar(i + k)` (an `abort` where `i + k` wraps);
  `fvar`, `sort`, `const`, `lit`: `h`; the compound tags call their arm.
* the **arms** `lift_app`, `lift_lam`, `lift_forall`, `lift_let`, `lift_proj` (the twin's
  `liftArmApp`, …): probe the memo `lf_find(h, c)`; on a hit return the value; else walk the
  children (a binder's body and `letE`'s body at `c + 1`), rebuild with `mk_*`, probe again and
  `lf_put`.

`lift_entry(h, k, c)` is `liftLooseBVarsFast`: `lf_clear(); r := lift_go(h, c, k); lf_clear()`.
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
def liftGo : FunDecl := lfn (h, c, k) locals (x, g, t, i, r) {
  x := call der_b(h);
  if x < 32767 && x <= c { return h };
  g := h >> 28;
  t := (h >> 27) & 1;
  i := h & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if g == 0 {
    if CTL.u64[22 + t] <= i { abort };
    x := BREC.u64[i * 2 + t];
    if x < c { return h };
    if x + k < x { abort };
    r := call intern_bvar(x + k);
    return r
  };
  if g == 4 { if CTL.u64[4 + t] <= i { abort }; r := call lift_app(h, c, k); return r };
  if g == 5 { if CTL.u64[28 + t] <= i { abort }; r := call lift_lam(h, c, k); return r };
  if g == 6 { if CTL.u64[30 + t] <= i { abort }; r := call lift_forall(h, c, k); return r };
  if g == 7 { if CTL.u64[20 + t] <= i { abort }; r := call lift_let(h, c, k); return r };
  if g == 9 { if CTL.u64[32 + t] <= i { abort }; r := call lift_proj(h, c, k); return r };
  if g == 1 { if CTL.u64[26 + t] <= i { abort }; return h };
  if g == 2 { if CTL.u64[16 + t] <= i { abort }; return h };
  if g == 3 { if CTL.u64[18 + t] <= i { abort }; return h };
  if g == 8 { if CTL.u64[2 + t] <= i { abort }; return h };
  abort
}

/-- con-ron: ConRon/Arena/ExprOps.lean:690-702 ConRon.Arena.liftArmApp -/
@[l_impl ConRon.Arena.liftArmApp]
def liftApp : FunDecl := lfn (h, c, k) locals (fd, j, d, t, i, f, a, x, y, r, u) {
  (fd, j, d) := call lf_find(h, c);
  if fd != 0 { return LMEMO.u64[j * 4 + 3] };
  t := (h >> 27) & 1;
  i := h & 134217727;
  f := AREC.u64[i * 4 + t * 2];
  a := AREC.u64[i * 4 + t * 2 + 1];
  x := call lift_go(f, c, k);
  y := call lift_go(a, c, k);
  r := call mk_app(x, y);
  (fd, j, d) := call lf_find(h, c);
  u := call lf_put(h, c, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:704-716 ConRon.Arena.liftArmLam -/
@[l_impl ConRon.Arena.liftArmLam]
def liftLam : FunDecl := lfn (h, c, k) locals (fd, j, d, t, i, f, a, x, y, r, u) {
  if c + 1 == 0 { abort };
  (fd, j, d) := call lf_find(h, c);
  if fd != 0 { return LMEMO.u64[j * 4 + 3] };
  t := (h >> 27) & 1;
  i := h & 134217727;
  f := LAREC.u64[i * 4 + t * 2];
  a := LAREC.u64[i * 4 + t * 2 + 1];
  x := call lift_go(f, c, k);
  y := call lift_go(a, c + 1, k);
  r := call mk_lam(x, y);
  (fd, j, d) := call lf_find(h, c);
  u := call lf_put(h, c, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:718-730 ConRon.Arena.liftArmForallE -/
@[l_impl ConRon.Arena.liftArmForallE]
def liftForall : FunDecl := lfn (h, c, k) locals (fd, j, d, t, i, f, a, x, y, r, u) {
  if c + 1 == 0 { abort };
  (fd, j, d) := call lf_find(h, c);
  if fd != 0 { return LMEMO.u64[j * 4 + 3] };
  t := (h >> 27) & 1;
  i := h & 134217727;
  f := FAREC.u64[i * 4 + t * 2];
  a := FAREC.u64[i * 4 + t * 2 + 1];
  x := call lift_go(f, c, k);
  y := call lift_go(a, c + 1, k);
  r := call mk_forall(x, y);
  (fd, j, d) := call lf_find(h, c);
  u := call lf_put(h, c, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:732-745 ConRon.Arena.liftArmLet -/
@[l_impl ConRon.Arena.liftArmLet]
def liftLet : FunDecl := lfn (h, c, k) locals (fd, j, d, t, i, f, a, b, x, y, z, r, u) {
  if c + 1 == 0 { abort };
  (fd, j, d) := call lf_find(h, c);
  if fd != 0 { return LMEMO.u64[j * 4 + 3] };
  t := (h >> 27) & 1;
  i := h & 134217727;
  f := LEREC.u64[i * 6 + t * 3];
  a := LEREC.u64[i * 6 + t * 3 + 1];
  b := LEREC.u64[i * 6 + t * 3 + 2];
  x := call lift_go(f, c, k);
  y := call lift_go(a, c, k);
  z := call lift_go(b, c + 1, k);
  r := call mk_let(x, y, z);
  (fd, j, d) := call lf_find(h, c);
  u := call lf_put(h, c, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:747-758 ConRon.Arena.liftArmProj -/
@[l_impl ConRon.Arena.liftArmProj]
def liftProj : FunDecl := lfn (h, c, k) locals (fd, j, d, t, i, nm, ix, e, x, r, u) {
  (fd, j, d) := call lf_find(h, c);
  if fd != 0 { return LMEMO.u64[j * 4 + 3] };
  t := (h >> 27) & 1;
  i := h & 134217727;
  nm := PJREC.u64[i * 6 + t * 3];
  ix := PJREC.u64[i * 6 + t * 3 + 1];
  e := PJREC.u64[i * 6 + t * 3 + 2];
  x := call lift_go(e, c, k);
  r := call mk_proj(nm, ix, x);
  (fd, j, d) := call lf_find(h, c);
  u := call lf_put(h, c, r, fd, j);
  return r
}

/-! ## The program and its specs -/

/-- What the specs need of the program: every function the walk calls, by name. -/
structure LiftProg (p : Prog) : Prop where
  derb : p.lookup "der_b" = some derB
  bvf : p.lookup "bvar_find" = some bvarFind
  bvp : p.lookup "bvar_push" = some bvarPush
  bvi : p.lookup "intern_bvar" = some internBVar
  lff : p.lookup "lf_find" = some (memoFindG lfSch)
  lfp : p.lookup "lf_put" = some (memoPutG lfSch)
  lfc : p.lookup "lf_clear" = some (memoClearG lfSch)
  go : p.lookup "lift_go" = some liftGo
  app : p.lookup "lift_app" = some liftApp
  lam : p.lookup "lift_lam" = some liftLam
  fa : p.lookup "lift_forall" = some liftForall
  le : p.lookup "lift_let" = some liftLet
  pj : p.lookup "lift_proj" = some liftProj
  mkapp : p.lookup "mk_app" = some mkApp
  appf : p.lookup "app_find" = some appFind
  appp : p.lookup "app_push" = some appPush
  appi : p.lookup "intern_app" = some internApp
  mklam : p.lookup "mk_lam" = some mkLam
  lamf : p.lookup "lam_find" = some lamFind
  lamp : p.lookup "lam_push" = some lamPush
  lami : p.lookup "intern_lam" = some internLamL
  mkfa : p.lookup "mk_forall" = some mkForall
  faf : p.lookup "forall_find" = some forallFind
  fap : p.lookup "forall_push" = some forallPush
  fai : p.lookup "intern_forall" = some internForallL
  mklet : p.lookup "mk_let" = some mkLet
  lef : p.lookup "letE_find" = some letFind
  lep : p.lookup "letE_push" = some letPush
  lei : p.lookup "intern_letE" = some internLet
  mkpj : p.lookup "mk_proj" = some mkProj
  pjf : p.lookup "proj_find" = some projFind
  pjp : p.lookup "proj_push" = some projPush
  pji : p.lookup "intern_proj" = some internProj

/-! ## The models and the specs (generated) -/

/-- **`lift_go` and its arms are their models** `liftW`, `liftAppW`, …, at every fuel. -/
l_model liftGo_spec (p : Prog) (hp : LiftProg p)
  fns [hp.go ↦ liftW, hp.app ↦ liftAppW, hp.lam ↦ liftLamW, hp.fa ↦ liftForallW,
    hp.le ↦ liftLetW, hp.pj ↦ liftProjW]
  specs [derB_spec p hp.derb n, internBVar_spec p hp.bvf hp.bvp hp.bvi n,
    memoFindG_spec lfSch p _ hp.lff n, memoPutG_spec lfSch p _ hp.lfp n,
    mkApp_spec p hp.derb hp.appf hp.appp hp.appi hp.mkapp n,
    mkLam_spec p hp.derb hp.lamf hp.lamp hp.lami hp.mklam n,
    mkForall_spec p hp.derb hp.faf hp.fap hp.fai hp.mkfa n,
    mkLet_spec p hp.derb hp.lef hp.lep hp.lei hp.mklet n,
    mkProj_spec p hp.derb hp.pjf hp.pjp hp.pji hp.mkpj n]
  grind [arena_grind] fold [tierW, idxW] finish [tierW, idxW] gen 20 heartbeats 1000000

end L.Arena
