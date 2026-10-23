module

public import ConAgua.Arena.Inst1
public import ConAgua.Arena.BvarB
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
import ConAgua.Census.Attr

@[expose] public section

/-!
# `instantiate1Lift` in L (lane `whnf3`)

con-ron's `instantiate1LiftGo`/`instantiate1LiftFast` (`Arena/ExprOps.lean:1903-2038`, con-leche's
`instantiate1Lift`): replace `bvar d` by `v`, lifting `v`'s loose `bvar`s past the binders crossed
on the way (`liftLooseBVarsFast fuel d 0 v` at the `bvar d` leaf, lane `exprops`' `lift_entry`),
lowering the loose `bvar`s above `d`, memoized per `(node, depth)` in the twin's `inst1LC`: the memo
library's table at word array `ILFM` (51, stamp/count `CTL[52]`/`CTL[53]`), cleared on entry and
exit as the twin.

`i1l_go(h, d, v, fu)`: `abort` at `fu = 0` (the twin's `fuel` exhausted), the cutoff
`bvar_b(fu - 1, h) ≤ d` (the twin's `bvarB fuel h` at its decremented fuel), the view checks of
every tag (the twin views every node past the cutoff; a dangling handle aborts), the `bvar` arm
inline, the leaves returned as they are, the compound arms at `fu - 1`; the arms probe the memo,
rebuild through the store (`mk_*`), record. `instantiate1_lift_fast(f, e, v, d)`: lane `induct`'s
convention, the fuel word `f` the walk's counter.
-/

set_option experimental.vcgen true

namespace L.Arena

/-- `instantiate1LiftGo`'s memo (`inst1LC`). -/
abbrev ILFM : ArrId := 51
abbrev i1lSch : MemoSch := ⟨ILFM, 52⟩

/-- con-ron: ConRon/Arena/ExprOps.lean:1897-1926 ConRon.Arena.instantiate1LiftGo -/
@[l_impl ConRon.Arena.instantiate1LiftGo]
def i1lGo : FunDecl := lfn (h, d, v, fu) locals (x, g, t, i, r) {
  if fu == 0 { abort };
  x := call bvar_b(fu - 1, h);
  if x <= d { return h };
  g := h >> 28;
  t := (h >> 27) & 1;
  i := h & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if g == 0 {
    if CTL.u64[22 + t] <= i { abort };
    x := BREC.u64[i * 2 + t];
    if x == d { r := call lift_entry(v, d, 0, fu - 1); return r };
    if d < x { r := call intern_bvar(x - 1); return r };
    return h
  };
  if g == 1 { if CTL.u64[26 + t] <= i { abort }; return h };
  if g == 2 { if CTL.u64[16 + t] <= i { abort }; return h };
  if g == 3 { if CTL.u64[18 + t] <= i { abort }; return h };
  if g == 8 { if CTL.u64[2 + t] <= i { abort }; return h };
  if g == 4 { if CTL.u64[4 + t] <= i { abort }; r := call i1l_app(h, d, v, fu - 1); return r };
  if g == 5 { if CTL.u64[28 + t] <= i { abort }; r := call i1l_lam(h, d, v, fu - 1); return r };
  if g == 6 { if CTL.u64[30 + t] <= i { abort }; r := call i1l_forall(h, d, v, fu - 1); return r };
  if g == 7 { if CTL.u64[20 + t] <= i { abort }; r := call i1l_let(h, d, v, fu - 1); return r };
  if g == 9 { if CTL.u64[32 + t] <= i { abort }; r := call i1l_proj(h, d, v, fu - 1); return r };
  abort
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1928-1940 ConRon.Arena.inst1LiftArmApp -/
@[l_impl ConRon.Arena.inst1LiftArmApp]
def i1lApp : FunDecl := lfn (h, d, v, fu) locals (fd, j, e0, t, i, f, a, x, y, r, u) {
  (fd, j, e0) := call i1l_find(h, d);
  if fd != 0 { return ILFM.u64[j * 4 + 3] };
  t := (h >> 27) & 1;
  i := h & 134217727;
  f := AREC.u64[i * 4 + t * 2];
  a := AREC.u64[i * 4 + t * 2 + 1];
  x := call i1l_go(f, d, v, fu);
  y := call i1l_go(a, d, v, fu);
  r := call mk_app(x, y);
  (fd, j, e0) := call i1l_find(h, d);
  u := call i1l_put(h, d, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1942-1954 ConRon.Arena.inst1LiftArmLam -/
@[l_impl ConRon.Arena.inst1LiftArmLam]
def i1lLam : FunDecl := lfn (h, d, v, fu) locals (fd, j, e0, t, i, f, a, x, y, r, u) {
  if d + 1 == 0 { abort };
  (fd, j, e0) := call i1l_find(h, d);
  if fd != 0 { return ILFM.u64[j * 4 + 3] };
  t := (h >> 27) & 1;
  i := h & 134217727;
  f := LAREC.u64[i * 4 + t * 2];
  a := LAREC.u64[i * 4 + t * 2 + 1];
  x := call i1l_go(f, d, v, fu);
  y := call i1l_go(a, d + 1, v, fu);
  r := call mk_lam(x, y);
  (fd, j, e0) := call i1l_find(h, d);
  u := call i1l_put(h, d, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1956-1968 ConRon.Arena.inst1LiftArmForallE -/
@[l_impl ConRon.Arena.inst1LiftArmForallE]
def i1lForall : FunDecl := lfn (h, d, v, fu) locals (fd, j, e0, t, i, f, a, x, y, r, u) {
  if d + 1 == 0 { abort };
  (fd, j, e0) := call i1l_find(h, d);
  if fd != 0 { return ILFM.u64[j * 4 + 3] };
  t := (h >> 27) & 1;
  i := h & 134217727;
  f := FAREC.u64[i * 4 + t * 2];
  a := FAREC.u64[i * 4 + t * 2 + 1];
  x := call i1l_go(f, d, v, fu);
  y := call i1l_go(a, d + 1, v, fu);
  r := call mk_forall(x, y);
  (fd, j, e0) := call i1l_find(h, d);
  u := call i1l_put(h, d, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1970-1983 ConRon.Arena.inst1LiftArmLet -/
@[l_impl ConRon.Arena.inst1LiftArmLet]
def i1lLet : FunDecl := lfn (h, d, v, fu) locals (fd, j, e0, t, i, f, a, b, x, y, z, r, u) {
  if d + 1 == 0 { abort };
  (fd, j, e0) := call i1l_find(h, d);
  if fd != 0 { return ILFM.u64[j * 4 + 3] };
  t := (h >> 27) & 1;
  i := h & 134217727;
  f := LEREC.u64[i * 6 + t * 3];
  a := LEREC.u64[i * 6 + t * 3 + 1];
  b := LEREC.u64[i * 6 + t * 3 + 2];
  x := call i1l_go(f, d, v, fu);
  y := call i1l_go(a, d, v, fu);
  z := call i1l_go(b, d + 1, v, fu);
  r := call mk_let(x, y, z);
  (fd, j, e0) := call i1l_find(h, d);
  u := call i1l_put(h, d, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1985-1996 ConRon.Arena.inst1LiftArmProj -/
@[l_impl ConRon.Arena.inst1LiftArmProj]
def i1lProj : FunDecl := lfn (h, d, v, fu) locals (fd, j, e0, t, i, nm, ix, e, x, r, u) {
  (fd, j, e0) := call i1l_find(h, d);
  if fd != 0 { return ILFM.u64[j * 4 + 3] };
  t := (h >> 27) & 1;
  i := h & 134217727;
  nm := PJREC.u64[i * 6 + t * 3];
  ix := PJREC.u64[i * 6 + t * 3 + 1];
  e := PJREC.u64[i * 6 + t * 3 + 2];
  x := call i1l_go(e, d, v, fu);
  r := call mk_proj(nm, ix, x);
  (fd, j, e0) := call i1l_find(h, d);
  u := call i1l_put(h, d, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:2030-2036 ConRon.Arena.instantiate1LiftFast -/
@[l_impl ConRon.Arena.instantiate1LiftFast]
def i1lFast : FunDecl := lfn (f, e, v, d) locals (r, u) {
  u := call i1l_clear();
  r := call i1l_go(e, d, v, f);
  u := call i1l_clear();
  return r
}

/-- The walk's own functions (with `inst_prog`'s and `lift_entry`'s callees). -/
def i1lFns : Prog :=
  [("i1l_find", memoFindG i1lSch), ("i1l_put", memoPutG i1lSch), ("i1l_clear", memoClearG i1lSch),
   ("i1l_go", i1lGo), ("i1l_app", i1lApp), ("i1l_lam", i1lLam), ("i1l_forall", i1lForall),
   ("i1l_let", i1lLet), ("i1l_proj", i1lProj), ("instantiate1_lift_fast", i1lFast)]

end L.Arena
