module

public import ConAgua.Arena.LevelSimp
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.LevelGrindAttr
import ConAgua.L.GrindAttr
import Std.Data.DTreeMap.Internal.Operations
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

/-- After both children of a `max`/`imax` (`g`): allocate. -/
def subK₂ (g x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) => lhMkW m₂ g x y

mutual
/-- **The model of `lv_subst`.** -/
def substW : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, l, k, v =>
    if lvG m l = 0 then some (l, m)
    else if lvG m l = 4 then (if lvA m l = k then some (v, m) else some (l, m))
    else if lvG m l = 1 then succK (substW n m (lvA m l) k v)
    else subK₁ n k v (lvG m l) (lvB m l) (substW n m (lvA m l) k v)

/-- After the first child of a `max`/`imax`. -/
def subK₁ (n : Nat) (k v g b : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => subK₂ g x (substW n m₁ b k v)
end

section substArms
variable (n : Nat) (m m₁ : Mem) (l k v g b x y : Word)

theorem substW_zero (h : lvG m l = 0) : substW (n + 1) m l k v = some (l, m) := by
  rw [substW]; simp [h]
theorem substW_hit (h : lvG m l = 4) (hk : lvA m l = k) : substW (n + 1) m l k v = some (v, m) := by
  rw [substW]; simp [h, hk]
theorem substW_miss (h : lvG m l = 4) (hk : lvA m l ≠ k) :
    substW (n + 1) m l k v = some (l, m) := by
  rw [substW]; simp [h, hk]
theorem substW_succ (h : lvG m l = 1) :
    substW (n + 1) m l k v = succK (substW n m (lvA m l) k v) := by
  rw [substW]; simp [h]
theorem substW_bin (h0 : lvG m l ≠ 0) (h4 : lvG m l ≠ 4) (h1 : lvG m l ≠ 1) :
    substW (n + 1) m l k v = subK₁ n k v (lvG m l) (lvB m l) (substW n m (lvA m l) k v) := by
  rw [substW]; simp [h0, h4, h1]
theorem subK₁_some : subK₁ n k v g b (some (x, m₁)) = subK₂ g x (substW n m₁ b k v) := by
  simp [subK₁]
theorem subK₂_some : subK₂ g x (some (y, m₁)) = lhMkW m₁ g x y := rfl

end substArms

grind_pattern [level_grind] substW_zero => substW (n + 1) m l k v
grind_pattern [level_grind] substW_hit => substW (n + 1) m l k v
grind_pattern [level_grind] substW_miss => substW (n + 1) m l k v
grind_pattern [level_grind] substW_succ => substW (n + 1) m l k v
grind_pattern [level_grind] substW_bin => substW (n + 1) m l k v
grind_pattern [level_grind] subK₁_some => subK₁ n k v g b (some (x, m₁))
grind_pattern [level_grind] subK₂_some => subK₂ g x (some (y, m₁))

/-- con-leche: ConLeche/Kernel/Level.lean:31-42 ConLeche.Level.subst
con-leche: ConLeche/Kernel/Level.lean:31-42 ConLeche.Level.subst.go -/
@[l_impl ConLeche.Level.subst ConLeche.Level.subst.go]
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

section subst
variable (p : Prog) (hpn : p.lookup "lv_node" = some lvNode) (hpm : p.lookup "lh_mk" = some lhMk)
  (hp : p.lookup "lv_subst" = some lvSubst)

include hpn hpm hp in
theorem lvSubst_spec (n : Nat) : ∀ (s₀ : St) (l k v : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "lv_subst" [l, k, v]
    ⦃fun res s' => LocEq s' s₀ ∧ substW n s₀.mem l k v = some (res.headD 0, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ l k v; rw [invoke_eq _ hp]; simp only [callFn, lvSubst]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ l k v
    rw [invoke_eq _ hp]
    simp only [callFn, lvSubst]
    sym only [lang_grind, arena_grind, level_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, lvNode_spec p hpn n,
        lhMk_spec p hpm n, ih] <;>
      finish (gen := 20)

end subst

/-! ## `lv_subsimp(l, k, v)`: `simplify (subst [k] [v] l)` -/

/-- After the substitution: simplify. -/
def ssK (n : Nat) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => simpW n m₁ x

/-- **The model of `lv_subsimp`.** -/
def ssW : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, l, k, v => ssK n (substW n m l k v)

theorem ssK_some (n : Nat) (x : Word) (m₁ : Mem) : ssK n (some (x, m₁)) = simpW n m₁ x := rfl
theorem ssW_succ (n : Nat) (m : Mem) (l k v : Word) :
    ssW (n + 1) m l k v = ssK n (substW n m l k v) := rfl

grind_pattern [level_grind] ssK_some => ssK n (some (x, m₁))
grind_pattern [level_grind] ssW_succ => ssW (n + 1) m l k v

/-- con-leche: ConLeche/Kernel/Level.lean:127-135 ConLeche.Level.byCases -/
def lvSubsimp : FunDecl := lfn (l, k, v) locals (x) {
  x := call lv_subst(l, k, v);
  x := call lv_simp(x);
  return x
}

/-! ## `lv_dist1(a, k, b)`: `max (imax a k) b` -/

/-- After the inner node. -/
def d1K (b : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => lhMkW m₁ 2 x b

/-- **The model of `lv_dist1`** (no fuel: it calls only `lh_mk`, below any fuel `n + 1`). -/
def dist1W (m : Mem) (a k b : Word) : Option (Word × Mem) := d1K b (lhMkW m 3 a k)

theorem d1K_some (b x : Word) (m₁ : Mem) : d1K b (some (x, m₁)) = lhMkW m₁ 2 x b := rfl
theorem dist1W_eq (m : Mem) (a k b : Word) : dist1W m a k b = d1K b (lhMkW m 3 a k) := rfl

grind_pattern [level_grind] d1K_some => d1K b (some (x, m₁))
grind_pattern [level_grind] dist1W_eq => dist1W m a k b

/-- con-leche: ConLeche/Kernel/Level.lean:115-125 ConLeche.Level.imaxRules -/
def lvDist1 : FunDecl := lfn (a, k, b) locals (x) {
  x := call lh_mk(3, a, k);
  x := call lh_mk(2, x, b);
  return x
}

/-! ## `lv_dist2(a, j, k)`: `simplify (max (imax a j) (imax a k))` -/

/-- After the first `imax`, the second, the `max`. -/
def d2K₁ (n : Nat) (a k : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => d2K₂ n x (lhMkW m₁ 3 a k)
where
  d2K₂ (n : Nat) (x : Word) : Option (Word × Mem) → Option (Word × Mem)
    | none => none
    | some (y, m₂) => ssK n (lhMkW m₂ 2 x y)

/-- **The model of `lv_dist2`.** -/
def dist2W : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, a, j, k => d2K₁ n a k (lhMkW m 3 a j)

theorem d2K₁_some (n : Nat) (a k x : Word) (m₁ : Mem) :
    d2K₁ n a k (some (x, m₁)) = d2K₁.d2K₂ n x (lhMkW m₁ 3 a k) := rfl
theorem d2K₂_some (n : Nat) (x y : Word) (m₂ : Mem) :
    d2K₁.d2K₂ n x (some (y, m₂)) = ssK n (lhMkW m₂ 2 x y) := rfl
theorem dist2W_succ (n : Nat) (m : Mem) (a j k : Word) :
    dist2W (n + 1) m a j k = d2K₁ n a k (lhMkW m 3 a j) := rfl

grind_pattern [level_grind] d2K₁_some => d2K₁ n a k (some (x, m₁))
grind_pattern [level_grind] d2K₂_some => d2K₁.d2K₂ n x (some (y, m₂))
grind_pattern [level_grind] dist2W_succ => dist2W (n + 1) m a j k

/-- con-leche: ConLeche/Kernel/Level.lean:115-125 ConLeche.Level.imaxRules -/
def lvDist2 : FunDecl := lfn (a, j, k) locals (x, y) {
  x := call lh_mk(3, a, j);
  y := call lh_mk(3, a, k);
  x := call lh_mk(2, x, y);
  x := call lv_simp(x);
  return x
}

section helpers
variable (p : Prog) (hpn : p.lookup "lv_node" = some lvNode) (hpm : p.lookup "lh_mk" = some lhMk)
  (hpc : p.lookup "lv_comb" = some lvComb) (hps : p.lookup "lv_simp" = some lvSimp)
  (hpu : p.lookup "lv_subst" = some lvSubst)

include hpn hpm hpc hps hpu in
theorem lvSubsimp_spec (hp : p.lookup "lv_subsimp" = some lvSubsimp) (n : Nat) (s₀ : St)
    (l k v : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "lv_subsimp" [l, k, v]
    ⦃fun res s' => LocEq s' s₀ ∧ ssW n s₀.mem l k v = some (res.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, lvSubsimp]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, level_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, lvSubst_spec p hpn hpm hpu n,
        lvSimp_spec p hpn hpm hpc hps n] <;>
      finish (gen := 20)

include hpm in
theorem lvDist1_spec (hp : p.lookup "lv_dist1" = some lvDist1) (n : Nat) (s₀ : St) (a k b : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "lv_dist1" [a, k, b]
    ⦃fun res s' => LocEq s' s₀ ∧ dist1W s₀.mem a k b = some (res.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, lvDist1]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, level_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, lhMk_spec p hpm n] <;>
      finish (gen := 20)

include hpn hpm hpc hps in
theorem lvDist2_spec (hp : p.lookup "lv_dist2" = some lvDist2) (n : Nat) (s₀ : St) (a j k : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "lv_dist2" [a, j, k]
    ⦃fun res s' => LocEq s' s₀ ∧ dist2W n s₀.mem a j k = some (res.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, lvDist2]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, level_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, lhMk_spec p hpm n,
        lvSimp_spec p hpn hpm hpc hps n] <;>
      finish (gen := 20)

end helpers

end L.Arena
