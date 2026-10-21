module

public import ConAgua.Arena.LevelHeap
meta import ConAgua.L.Semantics
import ConAgua.Census.Attr

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
L code aborts (or runs out); the refinements are in `LevelSimpRel.lean`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- After the first children of a `succ`: allocate the `succ` node. -/
def succK : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => lhMkW m₁ 1 x 0

theorem succK_some (x : Word) (m₁ : Mem) : succK (some (x, m₁)) = lhMkW m₁ 1 x 0 := rfl

/-! ## `lv_comb(l, r)`: `combining` -/

/-- **The model of `lv_comb`.** -/
def combW : Nat → Mem → Word → Word → Option (Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, l, r =>
    if lvG m l = 0 then some (r, m)
    else if lvG m r = 0 then some (l, m)
    else if lvG m l = 1 ∧ lvG m r = 1 then succK (combW n m (lvA m l) (lvA m r))
    else lhMkW m 2 l r

section combArms
variable (n : Nat) (m : Mem) (l r : Word)

theorem combW_zl (h : lvG m l = 0) : combW (n + 1) m l r = some (r, m) := by simp [combW, h]
theorem combW_zr (h : lvG m l ≠ 0) (h' : lvG m r = 0) : combW (n + 1) m l r = some (l, m) := by
  simp [combW, h, h']
theorem combW_ss (h : lvG m l = 1) (h' : lvG m r = 1) :
    combW (n + 1) m l r = succK (combW n m (lvA m l) (lvA m r)) := by simp [combW, h, h']
theorem combW_mx (h : lvG m l ≠ 0) (h' : lvG m r ≠ 0) (h'' : ¬ (lvG m l = 1 ∧ lvG m r = 1)) :
    combW (n + 1) m l r = lhMkW m 2 l r := by simp only [combW, h, h', h'', ↓reduceIte]

end combArms

attribute [level_grind =] succK_some
grind_pattern [level_grind] combW_zl => combW (n + 1) m l r
grind_pattern [level_grind] combW_zr => combW (n + 1) m l r
grind_pattern [level_grind] combW_ss => combW (n + 1) m l r
grind_pattern [level_grind] combW_mx => combW (n + 1) m l r

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

section comb
variable (p : Prog) (hpn : p.lookup "lv_node" = some lvNode) (hpm : p.lookup "lh_mk" = some lhMk)
  (hp : p.lookup "lv_comb" = some lvComb)

include hpn hpm hp in
theorem lvComb_spec (n : Nat) : ∀ (s₀ : St) (l r : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "lv_comb" [l, r]
    ⦃fun res s' => LocEq s' s₀ ∧ combW n s₀.mem l r = some (res.headD 0, s'.mem); ⊤⦄ := by
  induction n with
  | zero => intro s₀ l r; rw [invoke_eq _ hp]; simp only [callFn, lvComb]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ l r
    rw [invoke_eq _ hp]
    simp only [callFn, lvComb]
    sym only [lang_grind, arena_grind, level_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, lvNode_spec p hpn n,
        lhMk_spec p hpm n, ih] <;>
      finish (gen := 20)

end comb

/-! ## `lv_simp(p)`: `simplify` -/

/-- The `imax` arm after both children `x`, `y` (simplified): con-leche's tests in order. -/
def imaxW (n : Nat) (m : Mem) (x y : Word) : Option (Word × Mem) :=
  if lvG m x = 0 then some (y, m)
  else if lvG m x = 1 ∧ lvG m (lvA m x) = 0 then some (y, m)
  else if lvG m y = 0 then some (y, m)
  else if lvG m y = 1 then combW n m x y
  else lhMkW m 3 x y

/-- After both children of a `max` (`g = 2`) or `imax`. -/
def simpK₂ (n : Nat) (g x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) => if g = 2 then combW n m₂ x y else imaxW n m₂ x y

mutual
/-- **The model of `lv_simp`.** -/
def simpW : Nat → Mem → Word → Option (Word × Mem)
  | 0, _, _ => none
  | n + 1, m, p =>
    if lvG m p = 0 ∨ lvG m p = 4 then some (p, m)
    else if lvG m p = 1 then succK (simpW n m (lvA m p))
    else simpK₁ n (lvG m p) (lvB m p) (simpW n m (lvA m p))

/-- After the first child of a `max`/`imax`. -/
def simpK₁ (n : Nat) (g b : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => simpK₂ n g x (simpW n m₁ b)
end

section simpArms
variable (n : Nat) (m m₁ : Mem) (p g b x y : Word)

theorem simpW_leaf (h : lvG m p = 0 ∨ lvG m p = 4) : simpW (n + 1) m p = some (p, m) := by
  rw [simpW]; simp only [h, ↓reduceIte]
theorem simpW_succ (h : lvG m p = 1) : simpW (n + 1) m p = succK (simpW n m (lvA m p)) := by
  rw [simpW]; simp [h]
theorem simpW_bin (h0 : lvG m p ≠ 0) (h4 : lvG m p ≠ 4) (h1 : lvG m p ≠ 1) :
    simpW (n + 1) m p = simpK₁ n (lvG m p) (lvB m p) (simpW n m (lvA m p)) := by
  rw [simpW]; simp [h0, h4, h1]
theorem simpK₁_some : simpK₁ n g b (some (x, m₁)) = simpK₂ n g x (simpW n m₁ b) := by
  simp [simpK₁]
theorem simpK₂_max (hg : g = 2) : simpK₂ n g x (some (y, m₁)) = combW n m₁ x y := by
  simp [simpK₂, hg]
theorem simpK₂_imax (hg : g ≠ 2) : simpK₂ n g x (some (y, m₁)) = imaxW n m₁ x y := by
  simp [simpK₂, hg]
theorem imaxW_z (h : lvG m x = 0) : imaxW n m x y = some (y, m) := by simp [imaxW, h]
theorem imaxW_one (h1 : lvG m x = 1) (h2 : lvG m (lvA m x) = 0) :
    imaxW n m x y = some (y, m) := by simp [imaxW, h1, h2]
theorem imaxW_rz (h : lvG m x ≠ 0) (h1 : ¬ (lvG m x = 1 ∧ lvG m (lvA m x) = 0))
    (h2 : lvG m y = 0) : imaxW n m x y = some (y, m) := by
  simp only [imaxW, h, h1, h2, ↓reduceIte]
theorem imaxW_rs (h : lvG m x ≠ 0) (h1 : ¬ (lvG m x = 1 ∧ lvG m (lvA m x) = 0))
    (h2 : lvG m y ≠ 0) (h3 : lvG m y = 1) : imaxW n m x y = combW n m x y := by
  simp [imaxW, h, h1, h2, h3]
theorem imaxW_mk (h : lvG m x ≠ 0) (h1 : ¬ (lvG m x = 1 ∧ lvG m (lvA m x) = 0))
    (h2 : lvG m y ≠ 0) (h3 : lvG m y ≠ 1) : imaxW n m x y = lhMkW m 3 x y := by
  simp only [imaxW, h, h1, h2, h3, ↓reduceIte]

end simpArms

grind_pattern [level_grind] simpW_leaf => simpW (n + 1) m p
grind_pattern [level_grind] simpW_succ => simpW (n + 1) m p
grind_pattern [level_grind] simpW_bin => simpW (n + 1) m p
grind_pattern [level_grind] simpK₁_some => simpK₁ n g b (some (x, m₁))
grind_pattern [level_grind] simpK₂_max => simpK₂ n g x (some (y, m₁))
grind_pattern [level_grind] simpK₂_imax => simpK₂ n g x (some (y, m₁))
grind_pattern [level_grind] imaxW_z => imaxW n m x y
grind_pattern [level_grind] imaxW_one => imaxW n m x y
grind_pattern [level_grind] imaxW_rz => imaxW n m x y
grind_pattern [level_grind] imaxW_rs => imaxW n m x y
grind_pattern [level_grind] imaxW_mk => imaxW n m x y

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

section simp
variable (p : Prog) (hpn : p.lookup "lv_node" = some lvNode) (hpm : p.lookup "lh_mk" = some lhMk)
  (hpc : p.lookup "lv_comb" = some lvComb) (hp : p.lookup "lv_simp" = some lvSimp)

include hpn hpm hpc hp in
theorem lvSimp_spec (n : Nat) : ∀ (s₀ : St) (q : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "lv_simp" [q]
    ⦃fun res s' => LocEq s' s₀ ∧ simpW n s₀.mem q = some (res.headD 0, s'.mem); ⊤⦄ := by
  induction n with
  | zero => intro s₀ q; rw [invoke_eq _ hp]; simp only [callFn, lvSimp]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ q
    rw [invoke_eq _ hp]
    simp only [callFn, lvSimp]
    sym only [lang_grind, arena_grind, level_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, lvNode_spec p hpn n,
        lhMk_spec p hpm n, lvComb_spec p hpn hpm hpc n, ih] <;>
      finish (gen := 20)

end simp

/-! ## `lv_nz(p)`: `isNeverZero` -/

/-- **The model of `lv_nz`**: `1` if never zero, else `0`. -/
def nzW : Nat → Mem → Word → Option Word
  | 0, _, _ => none
  | n + 1, m, p =>
    if lvG m p = 1 then some 1
    else if lvG m p = 2 then nzK n m (lvB m p) (nzW n m (lvA m p))
    else if lvG m p = 3 then nzW n m (lvB m p)
    else some 0
where
  /-- After the first child of a `max`. -/
  nzK (n : Nat) (m : Mem) (b : Word) : Option Word → Option Word
    | none => none
    | some x => if x ≠ 0 then some 1 else nzW n m b

section nzArms
variable (n : Nat) (m : Mem) (p b x : Word)

theorem nzW_succ (h : lvG m p = 1) : nzW (n + 1) m p = some 1 := by simp [nzW, h]
theorem nzW_max (h : lvG m p = 2) :
    nzW (n + 1) m p = nzW.nzK n m (lvB m p) (nzW n m (lvA m p)) := by simp [nzW, h]
theorem nzW_imax (h : lvG m p = 3) : nzW (n + 1) m p = nzW n m (lvB m p) := by simp [nzW, h]
theorem nzW_leaf (h1 : lvG m p ≠ 1) (h2 : lvG m p ≠ 2) (h3 : lvG m p ≠ 3) :
    nzW (n + 1) m p = some 0 := by simp [nzW, h1, h2, h3]
theorem nzK_one (hx : x ≠ 0) : nzW.nzK n m b (some x) = some 1 := by simp [nzW.nzK, hx]
theorem nzK_zero : nzW.nzK n m b (some 0) = nzW n m b := by simp [nzW.nzK]

end nzArms

grind_pattern [level_grind] nzW_succ => nzW (n + 1) m p
grind_pattern [level_grind] nzW_max => nzW (n + 1) m p
grind_pattern [level_grind] nzW_imax => nzW (n + 1) m p
grind_pattern [level_grind] nzW_leaf => nzW (n + 1) m p
grind_pattern [level_grind] nzK_one => nzW.nzK n m b (some x)
grind_pattern [level_grind] nzK_zero => nzW.nzK n m b (some 0)

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

section nz
variable (p : Prog) (hpn : p.lookup "lv_node" = some lvNode) (hp : p.lookup "lv_nz" = some lvNz)

include hpn hp in
theorem lvNz_spec (n : Nat) : ∀ (s₀ : St) (q : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "lv_nz" [q]
    ⦃fun res s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ nzW n s₀.mem q = some (res.headD 0); ⊤⦄ := by
  induction n with
  | zero => intro s₀ q; rw [invoke_eq _ hp]; simp only [callFn, lvNz]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ q
    rw [invoke_eq _ hp]
    simp only [callFn, lvNz]
    sym only [lang_grind, arena_grind, level_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, lvNode_spec p hpn n, ih] <;>
      finish (gen := 20)

end nz

end L.Arena
