module

meta import ConAgua.L.Semantics
public import ConAgua.Arena.LevelSubst
import ConAgua.Census.Attr
import ConAgua.Arena.LevelGrindAttr
import ConAgua.L.ModelGen
import all ConAgua.Arena.LevelSimp

@[expose] public section

/-!
# `leqCore`, `rest`, `imaxRules`, `byCases` on level pointers

con-leche's mutual `Level.leqCore`/`rest`/`imaxRules`/`byCases` (`Kernel/Level.lean`, Rust
`kernel/level.rs:286-444`): decide `eval l ≤ eval r + diff` on simplified levels, nanoda's case
order, with con-leche's **fuel as an exact L counter** (a word argument `f`, decremented by
`leqCore` exactly where con-leche's `fuel + 1` pattern is; at `0` the answer is `none`).

Encodings: the answer `Option Bool` is a word, `0` = `none`, `1` = `some false`, `2` = `some true`;
`diff : Int` is the word `d = diff + 2^32` (so `diff ≥ 0` is `2^32 ≤ d`; the refinement keeps
`|diff| + fuel` small, so `d ± 1` never wraps).

* `lv_leq(f, l, r, d)`: `leqCore` (the two `zero` short-cuts, then `rest` at `f - 1`);
* `lv_rest(f, l, r, d)`: `rest`, arm by arm (the `imax`/`imax` arm compares the children by
  `lv_eq`);
* `lv_imax(f, l, r, d)`: `imaxRules`, with the new comparands built by `lv_dist1`/`lv_dist2`
  (`LevelSubst.lean`);
* `lv_cases(f, p, l, r, d)`: `byCases`, the two substitutions (`p := zero`, `p := succ p`) by
  `lv_cases_at(f, p, l, r, d, v)` = `leqCore f (simplify (subst [p] [v] l)) (… r) d`.

The models are generated (`l_model leqSpecs … defs` after the L code; the specs are its `nodefs`
run in `LevelLeqSpec.lean`): one mutual block over the L fuel `n`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order


namespace L.Arena

/-! ## The L code -/

/-- con-leche: ConLeche/Kernel/Level.lean:86-93 ConLeche.Level.leqCore -/
@[no_expose, l_impl ConLeche.Level.leqCore]
def lvLeq : FunDecl := lfn (f, l, r, d) locals (g, a, b, h, c, e, x) {
  if f == 0 { return 0 };
  (g, a, b) := call lv_node(l);
  if g == 0 && 4294967296 <= d { return 2 };
  (h, c, e) := call lv_node(r);
  if h == 0 && d < 4294967296 { return 1 };
  x := call lv_rest(f - 1, l, r, d);
  return x
}

/-- con-leche: ConLeche/Kernel/Level.lean:95-113 ConLeche.Level.rest -/
@[no_expose, l_impl ConLeche.Level.rest]
def lvRest : FunDecl := lfn (f, l, r, d) locals (g, a, b, h, c, e, x) {
  (g, a, b) := call lv_node(l);
  (h, c, e) := call lv_node(r);
  if g == 4 && h == 4 { if a == c && 4294967296 <= d { return 2 }; return 1 };
  if g == 4 && h == 0 { return 1 };
  if g == 0 && h == 4 { if 4294967296 <= d { return 2 }; return 1 };
  if g == 1 { x := call lv_leq(f, a, r, d - 1); return x };
  if h == 1 { x := call lv_leq(f, l, c, d + 1); return x };
  if g == 2 {
    x := call lv_leq(f, a, r, d);
    if x != 2 { return x };
    x := call lv_leq(f, b, r, d);
    return x
  };
  if h == 2 && (g == 4 || g == 0) {
    x := call lv_leq(f, l, c, d);
    if x != 1 { return x };
    x := call lv_leq(f, l, e, d);
    return x
  };
  if g == 3 && h == 3 && 4294967296 <= d {
    x := call lv_eq(a, c);
    if x != 0 { x := call lv_eq(b, e); if x != 0 { return 2 } }
  };
  x := call lv_imax(f, l, r, d);
  return x
}

/-- con-leche: ConLeche/Kernel/Level.lean:115-125 ConLeche.Level.imaxRules -/
@[no_expose, l_impl ConLeche.Level.imaxRules]
def lvImax : FunDecl := lfn (f, l, r, d) locals (g, a, b, h, c, e, i, j, k, x) {
  (g, a, b) := call lv_node(l);
  if g == 3 {
    (i, j, k) := call lv_node(b);
    if i == 4 { x := call lv_cases(f, j, l, r, d); return x }
  };
  (h, c, e) := call lv_node(r);
  if h == 3 {
    (i, j, k) := call lv_node(e);
    if i == 4 { x := call lv_cases(f, j, l, r, d); return x }
  };
  x := call lv_imax_l(f, l, r, d);
  return x
}

/-- con-leche: ConLeche/Kernel/Level.lean:115-125 ConLeche.Level.imaxRules -/
@[no_expose, l_impl ConLeche.Level.imaxRules]
def lvImaxL : FunDecl := lfn (f, l, r, d) locals (g, a, b, i, j, k, x) {
  (g, a, b) := call lv_node(l);
  if g == 3 {
    (i, j, k) := call lv_node(b);
    if i == 3 { x := call lv_dist1(a, k, b); x := call lv_leq(f, x, r, d); return x };
    if i == 2 { x := call lv_dist2(a, j, k); x := call lv_leq(f, x, r, d); return x }
  };
  x := call lv_imax_r(f, l, r, d);
  return x
}

/-- con-leche: ConLeche/Kernel/Level.lean:115-125 ConLeche.Level.imaxRules -/
@[no_expose, l_impl ConLeche.Level.imaxRules]
def lvImaxR : FunDecl := lfn (f, l, r, d) locals (h, c, e, i, j, k, x) {
  (h, c, e) := call lv_node(r);
  if h == 3 {
    (i, j, k) := call lv_node(e);
    if i == 3 { x := call lv_dist1(c, k, e); x := call lv_leq(f, l, x, d); return x };
    if i == 2 { x := call lv_dist2(c, j, k); x := call lv_leq(f, l, x, d); return x }
  };
  return 0
}

/-- con-leche: ConLeche/Kernel/Level.lean:127-135 ConLeche.Level.byCases -/
@[no_expose, l_impl ConLeche.Level.byCases]
def lvCases : FunDecl := lfn (f, p, l, r, d) locals (z, x) {
  z := call lh_mk(0, 0, 0);
  x := call lv_cases_at(f, p, l, r, d, z);
  if x != 2 { return x };
  z := call lh_mk(4, p, 0);
  z := call lh_mk(1, z, 0);
  x := call lv_cases_at(f, p, l, r, d, z);
  return x
}

/-- con-leche: ConLeche/Kernel/Level.lean:127-135 ConLeche.Level.byCases -/
@[no_expose, l_impl ConLeche.Level.byCases]
def lvCasesAt : FunDecl := lfn (f, p, l, r, d, v) locals (x, y) {
  x := call lv_subsimp(l, p, v);
  y := call lv_subsimp(r, p, v);
  x := call lv_leq(f, x, y, d);
  return x
}

/-- The level functions a program must contain (by name). -/
structure LevelProg (p : Prog) : Prop where
  node : p.lookup "lv_node" = some lvNode
  alloc : p.lookup "lh_mk" = some lhMk
  eq : p.lookup "lv_eq" = some lvEq
  comb : p.lookup "lv_comb" = some lvComb
  simp : p.lookup "lv_simp" = some lvSimp
  subst : p.lookup "lv_subst" = some lvSubst
  subsimp : p.lookup "lv_subsimp" = some lvSubsimp
  dist1 : p.lookup "lv_dist1" = some lvDist1
  dist2 : p.lookup "lv_dist2" = some lvDist2
  leq : p.lookup "lv_leq" = some lvLeq
  rest : p.lookup "lv_rest" = some lvRest
  imax : p.lookup "lv_imax" = some lvImax
  imaxL : p.lookup "lv_imax_l" = some lvImaxL
  imaxR : p.lookup "lv_imax_r" = some lvImaxR
  cases : p.lookup "lv_cases" = some lvCases
  casesAt : p.lookup "lv_cases_at" = some lvCasesAt

/-- **The models of the comparison** (generated; their specs in `LevelLeqSpec.lean`). -/
l_model leqSpecs (p : Prog) (hp : LevelProg p)
  fns [hp.leq ↦ leqW, hp.rest ↦ restW, hp.imax ↦ imaxRW, hp.imaxL ↦ imaxLW, hp.imaxR ↦ imaxRrW,
    hp.cases ↦ casesW, hp.casesAt ↦ caW]
  specs [lvNode_spec p hp.node n, lvEq_spec p hp.node hp.eq n, lhMk_spec p hp.alloc n,
    lvDist1_spec p hp.alloc hp.dist1 n, lvDist2_spec p hp.node hp.alloc hp.comb hp.simp hp.dist2 n,
    lvSubsimp_spec p hp.node hp.alloc hp.comb hp.simp hp.subst hp.subsimp n]
  grind [level_grind] fold [lvG, lvA, lvB] gen 20 noguard ["lv_node"] defs

end L.Arena
