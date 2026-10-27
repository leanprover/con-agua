module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
public import ConAgua.Arena.MemoLib
public import ConAgua.Arena.ExprMk
import ConAgua.Census.Attr
public import ConAgua.L.ProgHas
public import ConAgua.Arena.BVarStore
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr

@[expose] public section

/-!
# `liftLooseBVars`: the L code and the program

The L code of the walk `lift_go` and its arms, its entry `lift_entry` and the program `liftProg`;
the models and the specs are in `Lift.lean` (the walk) and `LiftSpec.lean` (the entry). Kept apart
so that a module that needs only the program (`Abs1.lean`) does not wait for the proofs.
-/

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

/-- con-ron: ConRon/Arena/ExprOps.lean:789-795 ConRon.Arena.liftLooseBVarsFast -/
@[l_impl ConRon.Arena.liftLooseBVarsFast]
def liftEntry : FunDecl := lfn (h, k, c, f) locals (r, u) {
  u := call lf_clear();
  r := call lift_go(h, c, k, f);
  u := call lf_clear();
  return r
}

/-- The walk, the memo, the `mk_*` and the stores they call, as one program. -/
def liftProg : Prog :=
  [("der_b", derB), ("lf_find", memoFindG lfSch), ("lf_put", memoPutG lfSch),
    ("lf_clear", memoClearG lfSch), ("lift_go", liftGo), ("lift_app", liftApp),
    ("lift_lam", liftLam), ("lift_forall", liftForall), ("lift_let", liftLet),
    ("lift_proj", liftProj), ("lift_entry", liftEntry), ("mk_app", mkApp), ("mk_lam", mkLam),
    ("mk_forall", mkForall), ("mk_let", mkLet), ("mk_proj", mkProj)] ++
  bvarProg ++ appProg ++ lamProg ++ forallProg ++ letProg ++ projProg

end L.Arena
