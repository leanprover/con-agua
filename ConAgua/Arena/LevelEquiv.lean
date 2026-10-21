module

public import ConAgua.Arena.LevelLeqSpec
meta import ConAgua.L.Semantics
import ConAgua.Census.Attr

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
set_option linter.deprecated false

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## `lv_leq_top(l, r)`: `leq` -/

/-- After simplifying `l`, then `r`. -/
def ltK₁ (n : Nat) (r : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => ltK₂ n x (simpW n m₁ r)
where
  ltK₂ (n : Nat) (x : Word) : Option (Word × Mem) → Option (Word × Mem)
    | none => none
    | some (y, m₂) => leqW n m₂ 10000 x y 4294967296

/-- **The model of `lv_leq_top`.** -/
def leqTopW : Nat → Mem → Word → Word → Option (Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, l, r => ltK₁ n r (simpW n m l)

section ltArms
variable (n : Nat) (m m₁ : Mem) (l r x y : Word)
theorem leqTopW_succ : leqTopW (n + 1) m l r = ltK₁ n r (simpW n m l) := rfl
theorem ltK₁_some : ltK₁ n r (some (x, m₁)) = ltK₁.ltK₂ n x (simpW n m₁ r) := rfl
theorem ltK₂_some : ltK₁.ltK₂ n x (some (y, m₁)) = leqW n m₁ 10000 x y 4294967296 := rfl
end ltArms

grind_pattern [level_grind] leqTopW_succ => leqTopW (n + 1) m l r
grind_pattern [level_grind] ltK₁_some => ltK₁ n r (some (x, m₁))
grind_pattern [level_grind] ltK₂_some => ltK₁.ltK₂ n x (some (y, m₁))

@[l_impl ConLeche.Level.leq ConLeche.Level.defaultFuel]
def lvLeqTop : FunDecl := lfn (l, r) locals (x, y) {
  x := call lv_simp(l);
  y := call lv_simp(r);
  x := call lv_leq(10000, x, y, 4294967296);
  return x
}

/-! ## `lv_equiv(l, r)`: `isEquiv` -/

/-- After `lv_eq(l, r)`. -/
def evK₁ (n : Nat) (m : Mem) (l r : Word) : Option Word → Option (Word × Mem)
  | none => none
  | some z => if z ≠ 0 then some (2, m) else evK₂ n r (simpW n m l)
where
  /-- After simplifying `l`. -/
  evK₂ (n : Nat) (r : Word) : Option (Word × Mem) → Option (Word × Mem)
    | none => none
    | some (x, m₁) => evK₃ n x (simpW n m₁ r)
  /-- After simplifying `r`. -/
  evK₃ (n : Nat) (x : Word) : Option (Word × Mem) → Option (Word × Mem)
    | none => none
    | some (y, m₂) => evK₄ n m₂ x y (lvEqW n m₂ x y)
  /-- After comparing the simplified forms. -/
  evK₄ (n : Nat) (m₂ : Mem) (x y : Word) : Option Word → Option (Word × Mem)
    | none => none
    | some z => if z ≠ 0 then some (2, m₂) else evK₅ n x y (leqW n m₂ 10000 x y 4294967296)
  /-- After `leq l r`. -/
  evK₅ (n : Nat) (x y : Word) : Option (Word × Mem) → Option (Word × Mem)
    | none => none
    | some (z, m₃) => if z ≠ 2 then some (z, m₃) else leqW n m₃ 10000 y x 4294967296

/-- **The model of `lv_equiv`.** -/
def equivW : Nat → Mem → Word → Word → Option (Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, l, r => evK₁ n m l r (lvEqW n m l r)

section evArms
variable (n : Nat) (m m₁ : Mem) (l r x y z : Word)
theorem equivW_succ : equivW (n + 1) m l r = evK₁ n m l r (lvEqW n m l r) := rfl
theorem evK₁_ne (hz : z ≠ 0) : evK₁ n m l r (some z) = some (2, m) := by simp [evK₁, hz]
theorem evK₁_zero : evK₁ n m l r (some 0) = evK₁.evK₂ n r (simpW n m l) := by simp [evK₁]
theorem evK₂_some : evK₁.evK₂ n r (some (x, m₁)) = evK₁.evK₃ n x (simpW n m₁ r) := rfl
theorem evK₃_some : evK₁.evK₃ n x (some (y, m₁)) = evK₁.evK₄ n m₁ x y (lvEqW n m₁ x y) := rfl
theorem evK₄_ne (hz : z ≠ 0) : evK₁.evK₄ n m₁ x y (some z) = some (2, m₁) := by
  simp [evK₁.evK₄, hz]
theorem evK₄_zero : evK₁.evK₄ n m₁ x y (some 0) =
    evK₁.evK₅ n x y (leqW n m₁ 10000 x y 4294967296) := by simp [evK₁.evK₄]
theorem evK₅_stop (hz : z ≠ 2) : evK₁.evK₅ n x y (some (z, m₁)) = some (z, m₁) := by
  simp [evK₁.evK₅, hz]
theorem evK₅_go : evK₁.evK₅ n x y (some (2, m₁)) = leqW n m₁ 10000 y x 4294967296 := by
  simp [evK₁.evK₅]
end evArms

grind_pattern [level_grind] equivW_succ => equivW (n + 1) m l r
grind_pattern [level_grind] evK₁_ne => evK₁ n m l r (some z)
grind_pattern [level_grind] evK₁_zero => evK₁ n m l r (some 0)
grind_pattern [level_grind] evK₂_some => evK₁.evK₂ n r (some (x, m₁))
grind_pattern [level_grind] evK₃_some => evK₁.evK₃ n x (some (y, m₁))
grind_pattern [level_grind] evK₄_ne => evK₁.evK₄ n m₁ x y (some z)
grind_pattern [level_grind] evK₄_zero => evK₁.evK₄ n m₁ x y (some 0)
grind_pattern [level_grind] evK₅_stop => evK₁.evK₅ n x y (some (z, m₁))
grind_pattern [level_grind] evK₅_go => evK₁.evK₅ n x y (some (2, m₁))

@[l_impl ConLeche.Level.isEquiv]
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

mutual
/-- **The model of `lv_equivs`.** -/
def equivsW : Nat → Mem → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, a, ln, b, k =>
    if ln = 0 ∨ k = 0 then some (if ln = k then 2 else 1, m)
    else esK n a ln b k (equivW n m (rdW (m.arr64 POOL) a) (rdW (m.arr64 POOL) b))
termination_by n _ _ _ _ _ => (n, 0)

/-- After comparing the heads. -/
def esK (n : Nat) (a ln b k : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (z, m₁) => if z ≠ 2 then some (z, m₁) else equivsW n m₁ (a + 1) (ln - 1) (b + 1) (k - 1)
termination_by _ => (n, 1)
end

section esArms
variable (n : Nat) (m m₁ : Mem) (a ln b k z : Word)
theorem equivsW_end (h : ln = 0 ∨ k = 0) :
    equivsW (n + 1) m a ln b k = some (if ln = k then 2 else 1, m) := by
  rw [equivsW]; simp [h]
theorem equivsW_cons (h : ¬ (ln = 0 ∨ k = 0)) :
    equivsW (n + 1) m a ln b k =
      esK n a ln b k (equivW n m (rdW (m.arr64 POOL) a) (rdW (m.arr64 POOL) b)) := by
  rw [equivsW]; simp only [h, ↓reduceIte]
theorem esK_stop (hz : z ≠ 2) : esK n a ln b k (some (z, m₁)) = some (z, m₁) := by
  rw [esK]; simp [hz]
theorem esK_go : esK n a ln b k (some (2, m₁)) =
    equivsW n m₁ (a + 1) (ln - 1) (b + 1) (k - 1) := by rw [esK]; simp
end esArms

grind_pattern [level_grind] equivsW_end => equivsW (n + 1) m a ln b k
grind_pattern [level_grind] equivsW_cons => equivsW (n + 1) m a ln b k
grind_pattern [level_grind] esK_stop => esK n a ln b k (some (z, m₁))
grind_pattern [level_grind] esK_go => esK n a ln b k (some (2, m₁))

@[l_impl ConLeche.Level.isEquivList]
def lvEquivs : FunDecl := lfn (a, n, b, k) locals (z) {
  if n == 0 || k == 0 { if n == k { return 2 }; return 1 };
  z := call lv_equiv(POOL.u64[a], POOL.u64[b]);
  if z != 2 { return z };
  z := call lv_equivs(a + 1, n - 1, b + 1, k - 1);
  return z
}

/-! ## The specs -/

section specs
variable (p : Prog) (hp : LevelProg p)

include hp in
theorem lvLeqTop_spec (hpt : p.lookup "lv_leq_top" = some lvLeqTop) (n : Nat) (s₀ : St)
    (l r : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "lv_leq_top" [l, r]
    ⦃fun res s' => LocEq s' s₀ ∧ leqTopW n s₀.mem l r = some (res.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hpt]
  simp only [callFn, lvLeqTop]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, level_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        lvSimp_spec p hp.node hp.alloc hp.comb hp.simp n, (leqSpecs p hp n).1] <;>
      finish (gen := 20)

include hp in
theorem lvEquiv_spec (hpe : p.lookup "lv_equiv" = some lvEquiv) (n : Nat) (s₀ : St) (l r : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "lv_equiv" [l, r]
    ⦃fun res s' => LocEq s' s₀ ∧ equivW n s₀.mem l r = some (res.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hpe]
  simp only [callFn, lvEquiv]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, level_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, lvEq_spec p hp.node hp.eq n,
        lvSimp_spec p hp.node hp.alloc hp.comb hp.simp n, (leqSpecs p hp n).1] <;>
      finish (gen := 20)

include hp in
theorem lvEquivs_spec (hpe : p.lookup "lv_equiv" = some lvEquiv)
    (hps : p.lookup "lv_equivs" = some lvEquivs) (n : Nat) : ∀ (s₀ : St) (a ln b k : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "lv_equivs" [a, ln, b, k]
    ⦃fun res s' => LocEq s' s₀ ∧ equivsW n s₀.mem a ln b k = some (res.headD 0, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ a ln b k; rw [invoke_eq _ hps]; simp only [callFn, lvEquivs]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ a ln b k
    rw [invoke_eq _ hps]
    simp only [callFn, lvEquivs]
    sym only [lang_grind, arena_grind, level_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        lvEquiv_spec p hp hpe n, ih] <;>
      finish (gen := 20)

end specs

end L.Arena
