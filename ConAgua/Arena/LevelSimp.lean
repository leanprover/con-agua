module

meta import ConAgua.L.Semantics
public import ConAgua.Arena.LevelHeap
import ConAgua.Census.Attr
import ConAgua.Arena.LevelGrindAttr
import ConAgua.L.GrindAttr
public import ConAgua.L.ModelGen
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# `combining`, `simplify` and `isNeverZero` on level pointers

con-leche's `Level.combining`, `Level.simplify`, `Level.isNeverZero` (`Kernel/Level.lean`; Rust
`kernel/level.rs:238-284`) over level pointers (`LevelHeap.lean`): the views by `lv_node`, the
nodes they build by `lh_mk` on the scratch heap. A `zero` or `param` level simplifies to itself
(the same pointer); `succ`, `max` and `imax` build fresh nodes, as the Rust allocates.

* `lv_comb(l, r)`: `combining`;
* `lv_simp(p)`: `simplify` (the `imax` arm's tests `ls = zero`, `ls = succ zero` and the match on
  `rs` read the views of the simplified children);
* `lv_nz(p)`: `isNeverZero`, `1`/`0`, reads only.

Models at L fuel `n` (`combW`, `simpW`, `nzW`): the result and the memory after, `none` where the
L code aborts (or runs out); generated with their continuations, guarded equations and specs by
`l_model` (`L/ModelGen.lean`). The refinements are in `LevelSimpRel.lean`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- After the first children of a `succ`: allocate the `succ` node (used by the substitution
models). -/
def succK : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => lhMkW m₁ 1 x 0

theorem succK_some (x : Word) (m₁ : Mem) : succK (some (x, m₁)) = lhMkW m₁ 1 x 0 := rfl

attribute [level_grind =] succK_some

/-! ## `lv_comb(l, r)`: `combining` -/

/-- con-leche: ConLeche/Kernel/Level.lean:62-67 ConLeche.Level.combining -/
@[l_impl ConLeche.Level.combining]
def lvComb : FunDecl := lfn (l, r) locals (g, a, b, h, c, d, x) {
  (g, a, b) := call lv_node(l);
  if g == 0 { return r };
  (h, c, d) := call lv_node(r);
  if h == 0 { return l };
  if g == 1 && h == 1 {
    x := call lv_comb(a, c);
    x := call lh_mk(1, x, 0);
    return x
  };
  x := call lh_mk(2, l, r);
  return x
}

/-- **`lv_comb` is its model `combW`** (generated). -/
l_model lvComb_spec (p : Prog) (hpn : p.lookup "lv_node" = some lvNode)
  (hpm : p.lookup "lh_mk" = some lhMk) (hp : p.lookup "lv_comb" = some lvComb)
  fns [hp ↦ combW]
  specs [lvNode_spec p hpn n, lhMk_spec p hpm n]
  grind [level_grind] fold [lvG, lvA, lvB] gen 20 noguard ["lv_node"]

/-! ## `lv_simp(p)`: `simplify` -/

/-- con-leche: ConLeche/Kernel/Level.lean:69-82 ConLeche.Level.simplify -/
@[l_impl ConLeche.Level.simplify]
def lvSimp : FunDecl := lfn (p) locals (g, a, b, x, y, h, c, d) {
  (g, a, b) := call lv_node(p);
  if g == 0 || g == 4 { return p };
  x := call lv_simp(a);
  if g == 1 { x := call lh_mk(1, x, 0); return x };
  y := call lv_simp(b);
  if g == 2 { x := call lv_comb(x, y); return x };
  (h, c, d) := call lv_node(x);
  if h == 0 { return y };
  if h == 1 { (h, c, d) := call lv_node(c); if h == 0 { return y } };
  (h, c, d) := call lv_node(y);
  if h == 0 { return y };
  if h == 1 { x := call lv_comb(x, y); return x };
  x := call lh_mk(3, x, y);
  return x
}

/-- **`lv_simp` is its model `simpW`** (generated). -/
l_model lvSimp_spec (p : Prog) (hpn : p.lookup "lv_node" = some lvNode)
  (hpm : p.lookup "lh_mk" = some lhMk) (hpc : p.lookup "lv_comb" = some lvComb)
  (hp : p.lookup "lv_simp" = some lvSimp)
  fns [hp ↦ simpW]
  specs [lvNode_spec p hpn n, lhMk_spec p hpm n, lvComb_spec p hpn hpm hpc n]
  grind [level_grind] fold [lvG, lvA, lvB] gen 20 noguard ["lv_node"]

/-! ## `lv_nz(p)`: `isNeverZero` -/

/-- con-leche: ConLeche/Kernel/Level.lean:51-60 ConLeche.Level.isNeverZero -/
@[l_impl ConLeche.Level.isNeverZero]
def lvNz : FunDecl := lfn (p) locals (g, a, b, x) {
  (g, a, b) := call lv_node(p);
  if g == 1 { return 1 };
  if g == 2 {
    x := call lv_nz(a);
    if x != 0 { return 1 };
    x := call lv_nz(b);
    return x
  };
  if g == 3 { x := call lv_nz(b); return x };
  return 0
}

/-- **`lv_nz` is its model `nzW`** (generated): `1` if never zero, else `0`; reads only. -/
l_model lvNz_spec (p : Prog) (hpn : p.lookup "lv_node" = some lvNode)
  (hp : p.lookup "lv_nz" = some lvNz)
  fns [hp ↦ nzW ro]
  specs [lvNode_spec p hpn n]
  grind [level_grind] fold [lvG, lvA, lvB] gen 20 noguard ["lv_node"]

end L.Arena
