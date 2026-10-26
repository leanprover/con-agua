module

public import ConAgua.Arena.LevelSubst
meta import ConAgua.L.Semantics
import ConAgua.Census.Attr

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

The model is one mutual block over the L fuel `n` (the continuations at the same `n` ranked by a
second component of the measure).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order


namespace L.Arena

mutual
/-- **The model of `lv_leq`** (`leqCore`). -/
def leqW : Nat → Mem → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, f, l, r, d =>
    if f = 0 then some (0, m)
    else if lvG m l = 0 ∧ 4294967296 ≤ d then some (2, m)
    else if lvG m r = 0 ∧ d < 4294967296 then some (1, m)
    else restW n m (f - 1) l r d
termination_by n _ _ _ _ _ => (n, 0)

/-- **The model of `lv_rest`** (`rest`). -/
def restW : Nat → Mem → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, f, l, r, d =>
    if lvG m l = 4 ∧ lvG m r = 4 then
      some (if lvA m l = lvA m r ∧ 4294967296 ≤ d then 2 else 1, m)
    else if lvG m l = 4 ∧ lvG m r = 0 then some (1, m)
    else if lvG m l = 0 ∧ lvG m r = 4 then some (if 4294967296 ≤ d then 2 else 1, m)
    else if lvG m l = 1 then leqW n m f (lvA m l) r (d - 1)
    else if lvG m r = 1 then leqW n m f l (lvA m r) (d + 1)
    else if lvG m l = 2 then andK n f (lvB m l) r d (leqW n m f (lvA m l) r d)
    else if lvG m r = 2 ∧ (lvG m l = 4 ∨ lvG m l = 0) then
      orK n f l (lvB m r) d (leqW n m f l (lvA m r) d)
    else if lvG m l = 3 ∧ lvG m r = 3 ∧ 4294967296 ≤ d then
      eqK₁ n m f l r d (lvEqW n m (lvA m l) (lvA m r))
    else imaxRW n m f l r d
termination_by n _ _ _ _ _ => (n, 0)

/-- After `max a b ≤ r`'s first comparison: `a ≤ r` must hold, then `b ≤ r` decides. -/
def andK (n : Nat) (f b r d : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => if x ≠ 2 then some (x, m₁) else leqW n m₁ f b r d
termination_by _ => (n, 1)

/-- After `l ≤ max x y`'s first comparison: `l ≤ x` suffices, else `l ≤ y` decides. -/
def orK (n : Nat) (f l e d : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => if x ≠ 1 then some (x, m₁) else leqW n m₁ f l e d
termination_by _ => (n, 1)

/-- The `imax`/`imax` arm after comparing the first children. -/
def eqK₁ (n : Nat) (m : Mem) (f l r d : Word) : Option Word → Option (Word × Mem)
  | none => none
  | some x => if x = 0 then imaxRW n m f l r d else eqK₂ n m f l r d (lvEqW n m (lvB m l) (lvB m r))
termination_by _ => (n, 2)

/-- … and the second children. -/
def eqK₂ (n : Nat) (m : Mem) (f l r d : Word) : Option Word → Option (Word × Mem)
  | none => none
  | some y => if y = 0 then imaxRW n m f l r d else some (2, m)
termination_by _ => (n, 1)

/-- **The model of `lv_imax`** (`imaxRules`): the two `byCases` arms, then `lv_imax_l`. -/
def imaxRW : Nat → Mem → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, f, l, r, d =>
    if lvG m l = 3 ∧ lvG m (lvB m l) = 4 then casesW n m f (lvA m (lvB m l)) l r d
    else if lvG m r = 3 ∧ lvG m (lvB m r) = 4 then casesW n m f (lvA m (lvB m r)) l r d
    else imaxLW n m f l r d
termination_by n _ _ _ _ _ => (n, 0)

/-- **The model of `lv_imax_l`**: the arms that distribute on the left, then `lv_imax_r`. -/
def imaxLW : Nat → Mem → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, f, l, r, d =>
    if lvG m l = 3 ∧ lvG m (lvB m l) = 3 then
      leqLK n f r d (dist1W m (lvA m l) (lvB m (lvB m l)) (lvB m l))
    else if lvG m l = 3 ∧ lvG m (lvB m l) = 2 then
      leqLK n f r d (dist2W n m (lvA m l) (lvA m (lvB m l)) (lvB m (lvB m l)))
    else imaxRrW n m f l r d
termination_by n _ _ _ _ _ => (n, 0)

/-- **The model of `lv_imax_r`**: the arms that distribute on the right, else `none`. -/
def imaxRrW : Nat → Mem → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, f, l, r, d =>
    if lvG m r = 3 ∧ lvG m (lvB m r) = 3 then
      leqRK n f l d (dist1W m (lvA m r) (lvB m (lvB m r)) (lvB m r))
    else if lvG m r = 3 ∧ lvG m (lvB m r) = 2 then
      leqRK n f l d (dist2W n m (lvA m r) (lvA m (lvB m r)) (lvB m (lvB m r)))
    else some (0, m)
termination_by n _ _ _ _ _ => (n, 0)

/-- Compare the built level `z` (left) with `r`. -/
def leqLK (n : Nat) (f r d : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (z, m₁) => leqW n m₁ f z r d
termination_by _ => (n, 1)

/-- Compare `l` with the built level `z` (right). -/
def leqRK (n : Nat) (f l d : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (z, m₁) => leqW n m₁ f l z d
termination_by _ => (n, 1)

/-- **The model of `lv_cases`** (`byCases`). -/
def casesW : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, f, p, l, r, d => csK₁ n f p l r d (lhMkW m 0 0 0)
termination_by n _ _ _ _ _ _ => (n, 0)

/-- After allocating `zero`: the case `p = 0`. -/
def csK₁ (n : Nat) (f p l r d : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (z, m₁) => csK₂ n f p l r d (caW n m₁ f p l r d z)
termination_by _ => (n, 4)

/-- After the case `p = 0`: unless it held, its answer; else allocate `param p`. -/
def csK₂ (n : Nat) (f p l r d : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₂) => if x ≠ 2 then some (x, m₂) else csK₃ n f p l r d (lhMkW m₂ 4 p 0)
termination_by _ => (n, 3)

/-- … allocate `succ (param p)`. -/
def csK₃ (n : Nat) (f p l r d : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (s, m₃) => csK₄ n f p l r d (lhMkW m₃ 1 s 0)
termination_by _ => (n, 2)

/-- … the case `p = succ p`. -/
def csK₄ (n : Nat) (f p l r d : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (s, m₄) => caW n m₄ f p l r d s
termination_by _ => (n, 1)

/-- **The model of `lv_cases_at`**: one case of `byCases`. -/
def caW : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, f, p, l, r, d, v => caK₁ n f p r d v (ssW n m l p v)
termination_by n _ _ _ _ _ _ _ => (n, 0)

/-- After the left operand. -/
def caK₁ (n : Nat) (f p r d v : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => caK₂ n f d x (ssW n m₁ r p v)
termination_by _ => (n, 2)

/-- After the right operand: compare. -/
def caK₂ (n : Nat) (f d x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) => leqW n m₂ f x y d
termination_by _ => (n, 1)
end

/-! ### The guarded equations -/

section arms
variable (n : Nat) (m m₁ : Mem) (f l r d b e x y z p v : Word)

theorem leqW_f0 (hf : f = 0) : leqW (n + 1) m f l r d = some (0, m) := by rw [leqW]; simp [hf]
theorem leqW_lz (hf : f ≠ 0) (hl : lvG m l = 0) (hd : 4294967296 ≤ d) :
    leqW (n + 1) m f l r d = some (2, m) := by rw [leqW]; simp [hf, hl, hd]
theorem leqW_rz (hf : f ≠ 0) (hl : ¬ (lvG m l = 0 ∧ 4294967296 ≤ d)) (hr : lvG m r = 0)
    (hd : d < 4294967296) : leqW (n + 1) m f l r d = some (1, m) := by
  rw [leqW]; simp only [hf, hl, hr, hd, ↓reduceIte, and_self]
theorem leqW_rest (hf : f ≠ 0) (hl : ¬ (lvG m l = 0 ∧ 4294967296 ≤ d))
    (hr : ¬ (lvG m r = 0 ∧ d < 4294967296)) :
    leqW (n + 1) m f l r d = restW n m (f - 1) l r d := by
  rw [leqW]; simp only [hf, hl, hr, ↓reduceIte]

theorem restW_pp (h : lvG m l = 4 ∧ lvG m r = 4) :
    restW (n + 1) m f l r d = some (if lvA m l = lvA m r ∧ 4294967296 ≤ d then 2 else 1, m) := by
  rw [restW, if_pos h]
theorem restW_pz (h1 : ¬ (lvG m l = 4 ∧ lvG m r = 4)) (h : lvG m l = 4 ∧ lvG m r = 0) :
    restW (n + 1) m f l r d = some (1, m) := by
  rw [restW, if_neg h1, if_pos h]
theorem restW_zp (h1 : ¬ (lvG m l = 4 ∧ lvG m r = 4)) (h2 : ¬ (lvG m l = 4 ∧ lvG m r = 0))
    (h : lvG m l = 0 ∧ lvG m r = 4) :
    restW (n + 1) m f l r d = some (if 4294967296 ≤ d then 2 else 1, m) := by
  rw [restW, if_neg h1, if_neg h2, if_pos h]
theorem restW_sl (h1 : ¬ (lvG m l = 4 ∧ lvG m r = 4)) (h2 : ¬ (lvG m l = 4 ∧ lvG m r = 0))
    (h3 : ¬ (lvG m l = 0 ∧ lvG m r = 4)) (h : lvG m l = 1) :
    restW (n + 1) m f l r d = leqW n m f (lvA m l) r (d - 1) := by
  rw [restW, if_neg h1, if_neg h2, if_neg h3, if_pos h]
theorem restW_sr (h1 : ¬ (lvG m l = 4 ∧ lvG m r = 4)) (h2 : ¬ (lvG m l = 4 ∧ lvG m r = 0))
    (h3 : ¬ (lvG m l = 0 ∧ lvG m r = 4)) (h4 : lvG m l ≠ 1) (h : lvG m r = 1) :
    restW (n + 1) m f l r d = leqW n m f l (lvA m r) (d + 1) := by
  rw [restW, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h]
theorem restW_ml (h1 : ¬ (lvG m l = 4 ∧ lvG m r = 4)) (h2 : ¬ (lvG m l = 4 ∧ lvG m r = 0))
    (h3 : ¬ (lvG m l = 0 ∧ lvG m r = 4)) (h4 : lvG m l ≠ 1) (h5 : lvG m r ≠ 1) (h : lvG m l = 2) :
    restW (n + 1) m f l r d = andK n f (lvB m l) r d (leqW n m f (lvA m l) r d) := by
  rw [restW, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_pos h]
theorem restW_mr (h1 : ¬ (lvG m l = 4 ∧ lvG m r = 4)) (h2 : ¬ (lvG m l = 4 ∧ lvG m r = 0))
    (h3 : ¬ (lvG m l = 0 ∧ lvG m r = 4)) (h4 : lvG m l ≠ 1) (h5 : lvG m r ≠ 1) (h6 : lvG m l ≠ 2)
    (h : lvG m r = 2 ∧ (lvG m l = 4 ∨ lvG m l = 0)) :
    restW (n + 1) m f l r d = orK n f l (lvB m r) d (leqW n m f l (lvA m r) d) := by
  rw [restW, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_pos h]
theorem restW_ii (h1 : ¬ (lvG m l = 4 ∧ lvG m r = 4)) (h2 : ¬ (lvG m l = 4 ∧ lvG m r = 0))
    (h3 : ¬ (lvG m l = 0 ∧ lvG m r = 4)) (h4 : lvG m l ≠ 1) (h5 : lvG m r ≠ 1) (h6 : lvG m l ≠ 2)
    (h7 : ¬ (lvG m r = 2 ∧ (lvG m l = 4 ∨ lvG m l = 0)))
    (h : lvG m l = 3 ∧ lvG m r = 3 ∧ 4294967296 ≤ d) :
    restW (n + 1) m f l r d = eqK₁ n m f l r d (lvEqW n m (lvA m l) (lvA m r)) := by
  rw [restW, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_pos h]
theorem restW_im (h1 : ¬ (lvG m l = 4 ∧ lvG m r = 4)) (h2 : ¬ (lvG m l = 4 ∧ lvG m r = 0))
    (h3 : ¬ (lvG m l = 0 ∧ lvG m r = 4)) (h4 : lvG m l ≠ 1) (h5 : lvG m r ≠ 1) (h6 : lvG m l ≠ 2)
    (h7 : ¬ (lvG m r = 2 ∧ (lvG m l = 4 ∨ lvG m l = 0)))
    (h8 : ¬ (lvG m l = 3 ∧ lvG m r = 3 ∧ 4294967296 ≤ d)) :
    restW (n + 1) m f l r d = imaxRW n m f l r d := by
  rw [restW, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8]

theorem andK_stop (hx : x ≠ 2) : andK n f b r d (some (x, m₁)) = some (x, m₁) := by
  rw [andK]; simp [hx]
theorem andK_go : andK n f b r d (some (2, m₁)) = leqW n m₁ f b r d := by rw [andK]; simp
theorem orK_stop (hx : x ≠ 1) : orK n f l e d (some (x, m₁)) = some (x, m₁) := by
  rw [orK]; simp [hx]
theorem orK_go : orK n f l e d (some (1, m₁)) = leqW n m₁ f l e d := by rw [orK]; simp
theorem eqK₁_zero : eqK₁ n m f l r d (some 0) = imaxRW n m f l r d := by rw [eqK₁]; simp
theorem eqK₁_ne (hx : x ≠ 0) :
    eqK₁ n m f l r d (some x) = eqK₂ n m f l r d (lvEqW n m (lvB m l) (lvB m r)) := by
  rw [eqK₁]; simp [hx]
theorem eqK₂_zero : eqK₂ n m f l r d (some 0) = imaxRW n m f l r d := by rw [eqK₂]; simp
theorem eqK₂_ne (hx : x ≠ 0) : eqK₂ n m f l r d (some x) = some (2, m) := by rw [eqK₂]; simp [hx]

theorem imaxRW_cl (h : lvG m l = 3 ∧ lvG m (lvB m l) = 4) :
    imaxRW (n + 1) m f l r d = casesW n m f (lvA m (lvB m l)) l r d := by
  rw [imaxRW, if_pos h]
theorem imaxRW_cr (h1 : ¬ (lvG m l = 3 ∧ lvG m (lvB m l) = 4))
    (h : lvG m r = 3 ∧ lvG m (lvB m r) = 4) :
    imaxRW (n + 1) m f l r d = casesW n m f (lvA m (lvB m r)) l r d := by
  rw [imaxRW, if_neg h1, if_pos h]
theorem imaxRW_l (h1 : ¬ (lvG m l = 3 ∧ lvG m (lvB m l) = 4))
    (h2 : ¬ (lvG m r = 3 ∧ lvG m (lvB m r) = 4)) :
    imaxRW (n + 1) m f l r d = imaxLW n m f l r d := by
  rw [imaxRW, if_neg h1, if_neg h2]
theorem imaxLW_i (h : lvG m l = 3 ∧ lvG m (lvB m l) = 3) :
    imaxLW (n + 1) m f l r d = leqLK n f r d (dist1W m (lvA m l) (lvB m (lvB m l)) (lvB m l)) := by
  rw [imaxLW, if_pos h]
theorem imaxLW_m (h3 : ¬ (lvG m l = 3 ∧ lvG m (lvB m l) = 3))
    (h : lvG m l = 3 ∧ lvG m (lvB m l) = 2) :
    imaxLW (n + 1) m f l r d =
      leqLK n f r d (dist2W n m (lvA m l) (lvA m (lvB m l)) (lvB m (lvB m l))) := by
  rw [imaxLW, if_neg h3, if_pos h]
theorem imaxLW_r (h3 : ¬ (lvG m l = 3 ∧ lvG m (lvB m l) = 3))
    (h4 : ¬ (lvG m l = 3 ∧ lvG m (lvB m l) = 2)) :
    imaxLW (n + 1) m f l r d = imaxRrW n m f l r d := by
  rw [imaxLW, if_neg h3, if_neg h4]
theorem imaxRrW_i (h : lvG m r = 3 ∧ lvG m (lvB m r) = 3) :
    imaxRrW (n + 1) m f l r d = leqRK n f l d (dist1W m (lvA m r) (lvB m (lvB m r)) (lvB m r)) := by
  rw [imaxRrW, if_pos h]
theorem imaxRrW_m (h5 : ¬ (lvG m r = 3 ∧ lvG m (lvB m r) = 3))
    (h : lvG m r = 3 ∧ lvG m (lvB m r) = 2) :
    imaxRrW (n + 1) m f l r d =
      leqRK n f l d (dist2W n m (lvA m r) (lvA m (lvB m r)) (lvB m (lvB m r))) := by
  rw [imaxRrW, if_neg h5, if_pos h]
theorem imaxRrW_none (h5 : ¬ (lvG m r = 3 ∧ lvG m (lvB m r) = 3))
    (h6 : ¬ (lvG m r = 3 ∧ lvG m (lvB m r) = 2)) : imaxRrW (n + 1) m f l r d = some (0, m) := by
  rw [imaxRrW, if_neg h5, if_neg h6]

theorem leqLK_some : leqLK n f r d (some (z, m₁)) = leqW n m₁ f z r d := by rw [leqLK]
theorem leqRK_some : leqRK n f l d (some (z, m₁)) = leqW n m₁ f l z d := by rw [leqRK]

theorem casesW_succ : casesW (n + 1) m f p l r d = csK₁ n f p l r d (lhMkW m 0 0 0) := by
  rw [casesW]
theorem csK₁_some : csK₁ n f p l r d (some (z, m₁)) = csK₂ n f p l r d (caW n m₁ f p l r d z) := by
  rw [csK₁]
theorem csK₂_stop (hx : x ≠ 2) : csK₂ n f p l r d (some (x, m₁)) = some (x, m₁) := by
  rw [csK₂]; simp [hx]
theorem csK₂_go : csK₂ n f p l r d (some (2, m₁)) = csK₃ n f p l r d (lhMkW m₁ 4 p 0) := by
  rw [csK₂]; simp
theorem csK₃_some : csK₃ n f p l r d (some (z, m₁)) = csK₄ n f p l r d (lhMkW m₁ 1 z 0) := by
  rw [csK₃]
theorem csK₄_some : csK₄ n f p l r d (some (z, m₁)) = caW n m₁ f p l r d z := by rw [csK₄]
theorem caW_succ : caW (n + 1) m f p l r d v = caK₁ n f p r d v (ssW n m l p v) := by rw [caW]
theorem caK₁_some : caK₁ n f p r d v (some (x, m₁)) = caK₂ n f d x (ssW n m₁ r p v) := by
  rw [caK₁]
theorem caK₂_some : caK₂ n f d x (some (y, m₁)) = leqW n m₁ f x y d := by rw [caK₂]

end arms

grind_pattern [level_grind] leqW_f0 => leqW (n + 1) m f l r d
grind_pattern [level_grind] leqW_lz => leqW (n + 1) m f l r d
grind_pattern [level_grind] leqW_rz => leqW (n + 1) m f l r d
grind_pattern [level_grind] leqW_rest => leqW (n + 1) m f l r d
grind_pattern [level_grind] restW_pp => restW (n + 1) m f l r d
grind_pattern [level_grind] restW_pz => restW (n + 1) m f l r d
grind_pattern [level_grind] restW_zp => restW (n + 1) m f l r d
grind_pattern [level_grind] restW_sl => restW (n + 1) m f l r d
grind_pattern [level_grind] restW_sr => restW (n + 1) m f l r d
grind_pattern [level_grind] restW_ml => restW (n + 1) m f l r d
grind_pattern [level_grind] restW_mr => restW (n + 1) m f l r d
grind_pattern [level_grind] restW_ii => restW (n + 1) m f l r d
grind_pattern [level_grind] restW_im => restW (n + 1) m f l r d
grind_pattern [level_grind] andK_stop => andK n f b r d (some (x, m₁))
grind_pattern [level_grind] andK_go => andK n f b r d (some (2, m₁))
grind_pattern [level_grind] orK_stop => orK n f l e d (some (x, m₁))
grind_pattern [level_grind] orK_go => orK n f l e d (some (1, m₁))
grind_pattern [level_grind] eqK₁_zero => eqK₁ n m f l r d (some 0)
grind_pattern [level_grind] eqK₁_ne => eqK₁ n m f l r d (some x)
grind_pattern [level_grind] eqK₂_zero => eqK₂ n m f l r d (some 0)
grind_pattern [level_grind] eqK₂_ne => eqK₂ n m f l r d (some x)
grind_pattern [level_grind] imaxRW_cl => imaxRW (n + 1) m f l r d
grind_pattern [level_grind] imaxRW_cr => imaxRW (n + 1) m f l r d
grind_pattern [level_grind] imaxRW_l => imaxRW (n + 1) m f l r d
grind_pattern [level_grind] imaxLW_i => imaxLW (n + 1) m f l r d
grind_pattern [level_grind] imaxLW_m => imaxLW (n + 1) m f l r d
grind_pattern [level_grind] imaxLW_r => imaxLW (n + 1) m f l r d
grind_pattern [level_grind] imaxRrW_i => imaxRrW (n + 1) m f l r d
grind_pattern [level_grind] imaxRrW_m => imaxRrW (n + 1) m f l r d
grind_pattern [level_grind] imaxRrW_none => imaxRrW (n + 1) m f l r d
grind_pattern [level_grind] leqLK_some => leqLK n f r d (some (z, m₁))
grind_pattern [level_grind] leqRK_some => leqRK n f l d (some (z, m₁))
grind_pattern [level_grind] casesW_succ => casesW (n + 1) m f p l r d
grind_pattern [level_grind] csK₁_some => csK₁ n f p l r d (some (z, m₁))
grind_pattern [level_grind] csK₂_stop => csK₂ n f p l r d (some (x, m₁))
grind_pattern [level_grind] csK₂_go => csK₂ n f p l r d (some (2, m₁))
grind_pattern [level_grind] csK₃_some => csK₃ n f p l r d (some (z, m₁))
grind_pattern [level_grind] csK₄_some => csK₄ n f p l r d (some (z, m₁))
grind_pattern [level_grind] caW_succ => caW (n + 1) m f p l r d v
grind_pattern [level_grind] caK₁_some => caK₁ n f p r d v (some (x, m₁))
grind_pattern [level_grind] caK₂_some => caK₂ n f d x (some (y, m₁))

/-! ## The L code -/

/-- con-leche: ConLeche/Kernel/Level.lean:86-93 ConLeche.Level.leqCore -/
@[l_impl ConLeche.Level.leqCore]
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
@[l_impl ConLeche.Level.rest]
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
@[l_impl ConLeche.Level.imaxRules]
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
@[l_impl ConLeche.Level.imaxRules]
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
@[l_impl ConLeche.Level.imaxRules]
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
@[l_impl ConLeche.Level.byCases]
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
@[l_impl ConLeche.Level.byCases]
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


end L.Arena
