module

meta import ConAgua.L.Semantics
import ConAgua.Census.Attr
public import ConAgua.Arena.LevelLeq
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.LevelGrindAttr
import ConAgua.Arena.LevelLeqSpec
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# `leq`, `isEquiv`, `isEquivList`: the entries of the level comparison

con-leche's `Level.leq` (`leqCore defaultFuel (simplify l) (simplify r) 0`), `Level.isEquiv`
(structural equality, then equality of the simplified forms, then `leq` both ways, short-circuit)
and `Level.isEquivList` (pairwise, `false` on a length mismatch only after the common prefix
compared equal), Rust `kernel/level.rs:453-500`. `defaultFuel = 10^4` is the literal fuel word
`10000`, the bias of `diff = 0` the literal `2^32`.

* `lv_leq_top(l, r)`: `leq`;
* `lv_equiv(l, r)`: `isEquiv` (it simplifies each side once; con-leche's `leq` simplifies again,
  to the same levels);
* `lv_equivs(a, n, b, k)`: `isEquivList` on two lists of level pointers, the words
  `POOL[a .. a + n)` and `POOL[b .. b + k)` (a level list's slice, `LsStore.lean`), recursive in
  the list.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## `lv_leq_top(l, r)`: `leq` -/

/-- con-leche: ConLeche/Kernel/Level.lean:144-146 ConLeche.Level.leq
con-leche: ConLeche/Kernel/Level.lean:139-142 ConLeche.Level.defaultFuel -/
@[no_expose, l_impl ConLeche.Level.leq ConLeche.Level.defaultFuel]
def lvLeqTop : FunDecl := lfn (l, r) locals (x, y) {
  x := call lv_simp(l);
  y := call lv_simp(r);
  x := call lv_leq(10000, x, y, 4294967296);
  return x
}

/-! ## `lv_equiv(l, r)`: `isEquiv` -/

/-- con-leche: ConLeche/Kernel/Level.lean:148-167 ConLeche.Level.isEquiv -/
@[no_expose, l_impl ConLeche.Level.isEquiv]
def lvEquiv : FunDecl := lfn (l, r) locals (x, y, z) {
  z := call lv_eq(l, r);
  if z != 0 { return 2 };
  x := call lv_simp(l);
  y := call lv_simp(r);
  z := call lv_eq(x, y);
  if z != 0 { return 2 };
  z := call lv_leq(10000, x, y, 4294967296);
  if z != 2 { return z };
  z := call lv_leq(10000, y, x, 4294967296);
  return z
}

/-! ## `lv_equivs(a, n, b, k)`: `isEquivList` -/

/-- con-leche: ConLeche/Kernel/Level.lean:169-175 ConLeche.Level.isEquivList -/
@[no_expose, l_impl ConLeche.Level.isEquivList]
def lvEquivs : FunDecl := lfn (a, n, b, k) locals (z) {
  if n == 0 || k == 0 { if n == k { return 2 }; return 1 };
  z := call lv_equiv(POOL⦃a⦄, POOL⦃b⦄);
  if z != 2 { return z };
  z := call lv_equivs(a + 1, n - 1, b + 1, k - 1);
  return z
}

/-! ## The specs -/

/-- **`lv_leq_top`** (generated): `leqTopW`. -/
l_model lvLeqTop_spec (p : Prog) (hp : LevelProg p) (hpt : p.lookup "lv_leq_top" = some lvLeqTop)
  fns [hpt ↦ leqTopW]
  specs [lvSimp_spec p hp.node hp.alloc hp.comb hp.simp n, (leqSpecs p hp n).1]
  grind [arena_grind, level_grind]

/-- **`lv_equiv`** (generated): `equivW`. -/
l_model lvEquiv_spec (p : Prog) (hp : LevelProg p) (hpe : p.lookup "lv_equiv" = some lvEquiv)
  fns [hpe ↦ equivW]
  specs [lvEq_spec p hp.node hp.eq n, lvSimp_spec p hp.node hp.alloc hp.comb hp.simp n,
    (leqSpecs p hp n).1]
  grind [arena_grind, level_grind]

/-- **`lv_equivs`** (generated): `equivsW`. -/
l_model lvEquivs_spec (p : Prog) (hp : LevelProg p) (hpe : p.lookup "lv_equiv" = some lvEquiv)
    (hps : p.lookup "lv_equivs" = some lvEquivs)
  fns [hps ↦ equivsW]
  specs [lvEquiv_spec p hp hpe n]
  grind [arena_grind, level_grind]

/-! ## `lvl_eq(u, v)`: the twin's `lvlEq?`, without its cache -/

/-- con-ron's `lvlEq?` (`Arena/Core.lean:129`) on two level handles: the level algorithm on a
fresh heap (the top reset to `0`). The verdict cache `lvlEqC` is `lvl_eq_c`'s, in front of this
function (`CoreLevels.lean`); this is the uncached computation (`LevelArena.lean`,
`lvlEq_refines`). -/
-- con-ron: ConRon/Arena/Core.lean:137-154 ConRon.Arena.lvlEq?
@[no_expose, l_impl ConRon.Arena.lvlEq?]
def lvlEqL : FunDecl := lfn (u, v) locals (z) {
  CTL.u64[192] := 0;
  z := call lv_equiv(u, v);
  return z
}

/-- **`lvl_eq`** (generated): `lvlEqW`, the heap reset, then `lv_equiv`. -/
l_model lvlEq_spec (p : Prog) (hp : LevelProg p) (hpe : p.lookup "lv_equiv" = some lvEquiv)
    (hpl : p.lookup "lvl_eq" = some lvlEqL)
  fns [hpl ↦ lvlEqW]
  specs [lvEquiv_spec p hp hpe n]
  grind [arena_grind, level_grind]

/-! ## `lvls_eq(us, vs)`: the twin's `lvlsEq?`, without its cache -/

/-- **The model of `ls_node`**: the slice `[offset, length]` of a level-list handle, `[]` where the
L code aborts (a tag other than `0`, a closed scratch tier, an index past the count). -/
def lsNodeW (m : Mem) (h : Word) : List Word :=
  if tagW h ≠ 0 then []
  else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then []
  else if tcnt m LVLS (tierW h) ≤ idxW h then []
  else [tfld m LVLS (tierW h) (idxW h) 0, tfld m LVLS (tierW h) (idxW h) 1]

/-- con-ron: ConRon/Arena/Monad.lean:494-500 ConRon.Arena.viewLs -/
@[no_expose] def lsNode : FunDecl := lfn (h) locals (t, i) {
  if ⟦h⟧.tag != 0 { abort };
  (t, i) := node LVLS⟦h⟧;
  return (LVLS⟨t, i⟩.o, LVLS⟨t, i⟩.l)
}

theorem lsNode_spec (p : Prog) (hp : p.lookup "ls_node" = some lsNode) (n : Nat) (s₀ : St)
    (q : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "ls_node" [q]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧ r = lsNodeW s₀.mem q; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, lsNode]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, level_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld,
        evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] <;>
      finish [lsNodeW, tierW, idxW]

/-- con-ron's `lvlsEq?` (`Arena/Core.lean:155`) on two level-list handles: `isEquivList` on their
slices, on a fresh heap; the verdict cache `lvlsEqC` is not represented (as for `lvl_eq`). -/
-- con-ron: ConRon/Arena/Core.lean:156-173 ConRon.Arena.lvlsEq?
@[no_expose, l_impl ConRon.Arena.lvlsEq?]
def lvlsEqL : FunDecl := lfn (us, vs) locals (a, n, b, k, z) {
  (a, n) := call ls_node(us);
  (b, k) := call ls_node(vs);
  CTL.u64[192] := 0;
  z := call lv_equivs(a, n, b, k);
  return z
}

/-- **`lvls_eq`** (generated): `lvlsEqW`, the two slices (none on a handle `ls_node` aborts on),
the heap reset, `lv_equivs`. -/
l_model lvlsEq_spec (p : Prog) (hp : LevelProg p) (hpe : p.lookup "lv_equiv" = some lvEquiv)
    (hps : p.lookup "lv_equivs" = some lvEquivs) (hpn : p.lookup "ls_node" = some lsNode)
    (hpl : p.lookup "lvls_eq" = some lvlsEqL)
  fns [hpl ↦ lvlsEqW]
  specs [lsNode_spec p hpn n, lvEquivs_spec p hp hpe hps n]
  grind [arena_grind, level_grind]

/-! ## The program -/

/-- The level functions, as one program. -/
def levelProg : Prog :=
  [("lv_node", lvNode), ("lh_mk", lhMk), ("lv_eq", lvEq), ("lv_comb", lvComb), ("lv_simp", lvSimp),
    ("lv_nz", lvNz), ("lv_subst", lvSubst), ("lv_subsimp", lvSubsimp), ("lv_dist1", lvDist1),
    ("lv_dist2", lvDist2), ("lv_leq", lvLeq), ("lv_rest", lvRest), ("lv_imax", lvImax),
    ("lv_imax_l", lvImaxL), ("lv_imax_r", lvImaxR), ("lv_cases", lvCases),
    ("lv_cases_at", lvCasesAt), ("lv_leq_top", lvLeqTop), ("lv_equiv", lvEquiv),
    ("lv_equivs", lvEquivs), ("lvl_eq", lvlEqL), ("ls_node", lsNode), ("lvls_eq", lvlsEqL)]

end L.Arena
