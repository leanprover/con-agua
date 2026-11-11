module

meta import ConAgua.L.Semantics
public import ConAgua.Arena.LevelSimp
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.LevelGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# One-key substitution, and the helpers of the `imax` rules

* `lv_subst(l, k, v)`: con-leche's `Level.subst [k] [v] l` (`Kernel/Level.lean`, Rust
  `kernel/level.rs:201-224`) with one key, the case `byCases` needs: a `param` whose name word is
  `k` becomes `v`; `zero` and the other `param`s are returned as they are, `succ`/`max`/`imax`
  rebuilt on the heap.
* `lv_subsimp(l, k, v)`: `simplify (subst [k] [v] l)`, `byCases`' four operands.
* `lv_dist1(a, k, b)`: the node `max (imax a k) b` (`imaxRules`' third and fifth arms, where `b` is
  the `imax x y` being distributed over, so it is reused).
* `lv_dist2(a, j, k)`: `simplify (max (imax a j) (imax a k))` (the fourth and sixth arms).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## `lv_subst(l, k, v)` -/

/-- After both children of a `max`/`imax` (`g`): allocate (`lv_subst_l`'s model, `LevelSubstL.lean`). -/
def subK₂ (g x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) => lhMkW m₂ g x y

theorem subK₂_some (g x y : Word) (m₁ : Mem) : subK₂ g x (some (y, m₁)) = lhMkW m₁ g x y := rfl

grind_pattern [level_grind] subK₂_some => subK₂ g x (some (y, m₁))

/-- con-leche: ConLeche/Kernel/Level.lean:31-42 ConLeche.Level.subst
con-leche: ConLeche/Kernel/Level.lean:31-42 ConLeche.Level.subst.go -/
@[no_expose, l_impl ConLeche.Level.subst ConLeche.Level.subst.go]
def lvSubst : FunDecl := lfn (l, k, v) locals (g, a, b, x, y) {
  (g, a, b) := call lv_node(l);
  if g == 0 { return l };
  if g == 4 { if a == k { return v }; return l };
  x := call lv_subst(a, k, v);
  if g == 1 { x := call lh_mk(1, x, 0); return x };
  y := call lv_subst(b, k, v);
  x := call lh_mk(g, x, y);
  return x
}

/-- **`lv_subst` is its model `substW`** (generated). -/
l_model lvSubst_spec (p : Prog) (hpn : p.lookup "lv_node" = some lvNode)
  (hpm : p.lookup "lh_mk" = some lhMk) (hp : p.lookup "lv_subst" = some lvSubst)
  fns [hp ↦ substW]
  specs [lvNode_spec p hpn n, lhMk_spec p hpm n]
  grind [level_grind] fold [lvG, lvA, lvB] gen 20 noguard ["lv_node"]

/-! ## `lv_subsimp(l, k, v)`: `simplify (subst [k] [v] l)` -/

/-- con-leche: ConLeche/Kernel/Level.lean:127-135 ConLeche.Level.byCases -/
@[no_expose] def lvSubsimp : FunDecl := lfn (l, k, v) locals (x) {
  x := call lv_subst(l, k, v);
  x := call lv_simp(x);
  return x
}

/-- **`lv_subsimp` is its model `ssW`** (generated). -/
l_model lvSubsimp_spec (p : Prog) (hpn : p.lookup "lv_node" = some lvNode)
  (hpm : p.lookup "lh_mk" = some lhMk) (hpc : p.lookup "lv_comb" = some lvComb)
  (hps : p.lookup "lv_simp" = some lvSimp) (hpu : p.lookup "lv_subst" = some lvSubst)
  (hp : p.lookup "lv_subsimp" = some lvSubsimp)
  fns [hp ↦ ssW]
  specs [lvSubst_spec p hpn hpm hpu n, lvSimp_spec p hpn hpm hpc hps n]
  grind [level_grind]

/-! ## `lv_dist1(a, k, b)`: `max (imax a k) b` -/

/-- con-leche: ConLeche/Kernel/Level.lean:115-125 ConLeche.Level.imaxRules -/
@[no_expose] def lvDist1 : FunDecl := lfn (a, k, b) locals (x) {
  x := call lh_mk(3, a, k);
  x := call lh_mk(2, x, b);
  return x
}

/-- **`lv_dist1` is its model `dist1W`** (generated). -/
l_model lvDist1_spec (p : Prog) (hpm : p.lookup "lh_mk" = some lhMk)
  (hp : p.lookup "lv_dist1" = some lvDist1)
  fns [hp ↦ dist1W]
  specs [lhMk_spec p hpm n]
  grind [level_grind]

/-! ## `lv_dist2(a, j, k)`: `simplify (max (imax a j) (imax a k))` -/

/-- con-leche: ConLeche/Kernel/Level.lean:115-125 ConLeche.Level.imaxRules -/
@[no_expose] def lvDist2 : FunDecl := lfn (a, j, k) locals (x, y) {
  x := call lh_mk(3, a, j);
  y := call lh_mk(3, a, k);
  x := call lh_mk(2, x, y);
  x := call lv_simp(x);
  return x
}

/-- **`lv_dist2` is its model `dist2W`** (generated). -/
l_model lvDist2_spec (p : Prog) (hpn : p.lookup "lv_node" = some lvNode)
  (hpm : p.lookup "lh_mk" = some lhMk) (hpc : p.lookup "lv_comb" = some lvComb)
  (hps : p.lookup "lv_simp" = some lvSimp) (hp : p.lookup "lv_dist2" = some lvDist2)
  fns [hp ↦ dist2W]
  specs [lhMk_spec p hpm n, lvSimp_spec p hpn hpm hpc hps n]
  grind [level_grind]

end L.Arena
