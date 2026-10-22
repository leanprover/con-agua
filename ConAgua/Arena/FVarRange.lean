module

public import ConAgua.Arena.MemoLib
public import ConAgua.Arena.ViewL
public import ConAgua.Arena.AppStore
public import ConAgua.Arena.LetStore
public import ConAgua.Arena.BVarStore
public import ConAgua.Arena.FVarStore
public import ConAgua.Arena.LamStore
public import ConAgua.Arena.ForallStore
public import ConAgua.Arena.ProjStore
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
import ConAgua.Census.Attr

@[expose] public section

/-!
# `fvarRange`: the memoized exact free-variable range

con-ron's `fvar_range_go`/`fvar_range_memo` (`arena/expr_ops.rs:2075,2146`, Lean twin
`fvarRangeGo`/`fvarRangeMemo`, `Arena/ExprOps.lean:1483-1563`): `1 +` the largest free-variable
index under a handle (`0` if there is none), memoized per node in `fvarBC`
(`MemoLib.lean`'s `frSch`, array 48). `Walk.lean`'s `bvarBoundGo`/`Memo` shape exactly, with three
differences: the `bvar` arm returns `0` (not `i + 1`: a bound variable is not free), the `fvar` arm
returns `idx + 1` (not `0`), and the binder/`letE` arms do **not** truncate the last child (the
cursor does not move: a binder's own `fvar` annotations are read by `wscopedB`'s refinement, not
descended into, so the whole subterm's fvar range is the plain `max` of its children, unlike
`bvarBound`'s `satPred` on the body). `abstract1`'s cutoff reads it the way
`instantiate1Lift`/`liftLooseBVars` read `der_b`: `fvarB ≤ d` skips the walk (ROADMAP §1, `expr_ops.rs`).

`fr_go(h)`: probe the memo (`fm_find`, `memoFindG frSch`); on a hit return the value. Otherwise
decode the handle and dispatch on the tag:

* `bvar i` (tag 0): `0`;
* `fvar idx _` (tag 1): `idx + 1` (an `abort` where it wraps);
* `sort`, `const`, `lit` (tags 2, 3, 8): `0`;
* `app f a` (tag 4): `max (fr_go f) (fr_go a)`;
* `lam ty body`, `forallE ty body` (tags 5, 6): `max (fr_go ty) (fr_go body)`;
* `letE ty val body` (tag 7): `max (max (fr_go ty) (fr_go val)) (fr_go body)`;
* `proj n i e` (tag 9): `fr_go e`;
* any other tag: `abort` (the arena's `view` fails there too).

then record the result (probe again, `fm_put`). `fr_memo(h)` is `fm_clear(); r := fr_go(h); fm_clear()`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- Record the result `r` at `h` and return it. -/
def frSet (m : Mem) (h r : Word) : Option (Word × Mem) :=
  match msetG frSch m h 0 r with
  | none => none
  | some m' => some (r, m')

mutual
/-- **The model of `fr_go`** at L fuel `n`: the result and the memory after, `none` where the L
code aborts. -/
def frW : Nat → Mem → Word → Option (Word × Mem)
  | 0, _, _ => none
  | n + 1, m, h =>
    if mfindG frSch m h 0 = [] then none
    else if (mfindG frSch m h 0).headD 0 ≠ 0 then
      some (rdW (m.arr64 FRMEMO) ((mfindG frSch m h 0).tail.headD 0 * 4 + 3), m)
    else
      match frNodeW n m h with
      | none => none
      | some (r, m₁) => frSet m₁ h r

/-- **The model of `fr_node`**: the view and the dispatch on the tag. -/
def frNodeW : Nat → Mem → Word → Option (Word × Mem)
  | 0, _, _ => none
  | n + 1, m, h =>
    if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if h >>> 28 = 0 then
      if rdW (m.arr64 CTL) (22 + tierW h) ≤ idxW h then none else some (0, m)
    else if h >>> 28 = 1 then
      if rdW (m.arr64 CTL) (26 + tierW h) ≤ idxW h then none
      else if rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2) + 1 = 0 then none
      else some (rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2) + 1, m)
    else if h >>> 28 = 4 then
      if rdW (m.arr64 CTL) (4 + tierW h) ≤ idxW h then none
      else
        match frW n m (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2)) with
        | none => none
        | some (x, m₁) =>
          match frW n m₁ (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2 + 1)) with
          | none => none
          | some (y, m₂) => some (maxW x y, m₂)
    else if h >>> 28 = 5 then
      if rdW (m.arr64 CTL) (28 + tierW h) ≤ idxW h then none
      else
        match frW n m (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2)) with
        | none => none
        | some (x, m₁) =>
          match frW n m₁ (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2 + 1)) with
          | none => none
          | some (y, m₂) => some (maxW x y, m₂)
    else if h >>> 28 = 6 then
      if rdW (m.arr64 CTL) (30 + tierW h) ≤ idxW h then none
      else
        match frW n m (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2)) with
        | none => none
        | some (x, m₁) =>
          match frW n m₁ (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2 + 1)) with
          | none => none
          | some (y, m₂) => some (maxW x y, m₂)
    else if h >>> 28 = 9 then
      if rdW (m.arr64 CTL) (32 + tierW h) ≤ idxW h then none
      else frW n m (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 2))
    else if h >>> 28 = 7 then
      if rdW (m.arr64 CTL) (20 + tierW h) ≤ idxW h then none
      else
        match frW n m (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3)) with
        | none => none
        | some (x, m₁) =>
          match frW n m₁ (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 1)) with
          | none => none
          | some (y, m₂) =>
            match frW n m₂ (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 2)) with
            | none => none
            | some (z, m₃) => some (maxW (maxW x y) z, m₃)
    else if h >>> 28 = 2 then
      if rdW (m.arr64 CTL) (16 + tierW h) ≤ idxW h then none else some (0, m)
    else if h >>> 28 = 3 then
      if rdW (m.arr64 CTL) (18 + tierW h) ≤ idxW h then none else some (0, m)
    else if h >>> 28 = 8 then
      if rdW (m.arr64 CTL) (2 + tierW h) ≤ idxW h then none else some (0, m)
    else none
end

/-! ### The guarded equations, one per reachable arm -/

/-- After `fr_node`: record the result. -/
def frK (h : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m₁) => frSet m₁ h r

/-- After `fm_put`. -/
def frSetK (r : Word) : Option Mem → Option (Word × Mem)
  | none => none
  | some m' => some (r, m')

/-- The `app` arm after the first child, and after the second. -/
def frAppK₁ (n : Nat) (a : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => frAppK₂ x (frW n m₁ a)
where frAppK₂ (x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) => some (maxW x y, m₂)

/-- The binder arm (`lam`, `forallE`) after the type, and after the body: no truncation. -/
def frBindK₁ (n : Nat) (b : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => frBindK₂ x (frW n m₁ b)
where frBindK₂ (x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) => some (maxW x y, m₂)

/-- The `letE` arm after each child: no truncation. -/
def frLetK₁ (n : Nat) (a b : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => frLetK₂ x (frW n m₁ a)
where
  frLetK₂ (x : Word) : Option (Word × Mem) → Option (Word × Mem)
    | none => none
    | some (y, m₂) => frLetK₃ x y (frW n m₂ b)
  frLetK₃ (x y : Word) : Option (Word × Mem) → Option (Word × Mem)
    | none => none
    | some (z, m₃) => some (maxW (maxW x y) z, m₃)

section arms
variable (n : Nat) (m m₁ m₂ m₃ : Mem) (h r x y z f a b : Word)

theorem frK_some : frK h (some (r, m₁)) = frSet m₁ h r := rfl
theorem frSetK_some : frSetK r (some m₁) = some (r, m₁) := rfl
theorem frAppK₁_some : frAppK₁ n a (some (x, m₁)) = frAppK₁.frAppK₂ x (frW n m₁ a) := rfl
theorem frAppK₂_some : frAppK₁.frAppK₂ x (some (y, m₂)) = some (maxW x y, m₂) := rfl
theorem frBindK₁_some : frBindK₁ n b (some (x, m₁)) = frBindK₁.frBindK₂ x (frW n m₁ b) := rfl
theorem frBindK₂_some : frBindK₁.frBindK₂ x (some (y, m₂)) = some (maxW x y, m₂) := rfl
theorem frLetK₁_some : frLetK₁ n a b (some (x, m₁)) = frLetK₁.frLetK₂ n b x (frW n m₁ a) := rfl
theorem frLetK₂_some : frLetK₁.frLetK₂ n b x (some (y, m₂)) = frLetK₁.frLetK₃ x y (frW n m₂ b) := rfl
theorem frLetK₃_some :
    frLetK₁.frLetK₃ x y (some (z, m₃)) = some (maxW (maxW x y) z, m₃) := rfl

theorem frSet_eq : frSet m h r = frSetK r (msetG frSch m h 0 r) := by
  simp only [frSet, frSetK]

theorem frW_hit (hr : mfindG frSch m h 0 ≠ []) (hh : (mfindG frSch m h 0).headD 0 ≠ 0) :
    frW (n + 1) m h = some (rdW (m.arr64 FRMEMO) ((mfindG frSch m h 0).tail.headD 0 * 4 + 3), m) := by
  rw [frW]; simp only [hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]

theorem frW_miss (hr : mfindG frSch m h 0 ≠ []) (hh : (mfindG frSch m h 0).headD 0 = 0) :
    frW (n + 1) m h = frK h (frNodeW n m h) := by
  rw [frW]; simp only [hr, hh, ↓reduceIte, ne_eq, not_true_eq_false, frK]

theorem frNodeW_bvar (hg : h >>> 28 = 0) (hv : viewOK m h 22) : frNodeW (n + 1) m h = some (0, m) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [frNodeW]; simp [hv1, hg, UInt64.not_le.mpr hv2]

theorem frNodeW_fvar (hv : viewOK m h 26) (hg : h >>> 28 = 1)
    (h1 : rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2) + 1 ≠ 0) :
    frNodeW (n + 1) m h = some (rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2) + 1, m) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [frNodeW]; simp only [hv1, hg, ↓reduceIte, h1]; simp [UInt64.not_le.mpr hv2]

theorem frNodeW_sort (hg : h >>> 28 = 2) (hv : viewOK m h 16) : frNodeW (n + 1) m h = some (0, m) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [frNodeW]; simp [hv1, hg, UInt64.not_le.mpr hv2]

theorem frNodeW_const (hg : h >>> 28 = 3) (hv : viewOK m h 18) : frNodeW (n + 1) m h = some (0, m) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [frNodeW]; simp [hv1, hg, UInt64.not_le.mpr hv2]

theorem frNodeW_lit (hg : h >>> 28 = 8) (hv : viewOK m h 2) : frNodeW (n + 1) m h = some (0, m) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [frNodeW]; simp [hv1, hg, UInt64.not_le.mpr hv2]

theorem frNodeW_app (hv : viewOK m h 4) (hg : h >>> 28 = 4) :
    frNodeW (n + 1) m h = frAppK₁ n (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2 + 1))
      (frW n m (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2))) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [frNodeW]; simp only [hv1, hg, ↓reduceIte, UInt64.not_le.mpr hv2, frAppK₁, frAppK₁.frAppK₂]
  simp

theorem frNodeW_lam (hv : viewOK m h 28) (hg : h >>> 28 = 5) :
    frNodeW (n + 1) m h = frBindK₁ n (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2 + 1))
      (frW n m (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2))) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [frNodeW]; simp only [hv1, hg, ↓reduceIte, UInt64.not_le.mpr hv2, frBindK₁, frBindK₁.frBindK₂]
  simp

theorem frNodeW_forall (hv : viewOK m h 30) (hg : h >>> 28 = 6) :
    frNodeW (n + 1) m h = frBindK₁ n (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2 + 1))
      (frW n m (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2))) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [frNodeW]; simp only [hv1, hg, ↓reduceIte, UInt64.not_le.mpr hv2, frBindK₁, frBindK₁.frBindK₂]
  simp

theorem frNodeW_proj (hv : viewOK m h 32) (hg : h >>> 28 = 9) :
    frNodeW (n + 1) m h = frW n m (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 2)) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [frNodeW]; simp [hv1, hg, UInt64.not_le.mpr hv2]

theorem frNodeW_let (hv : viewOK m h 20) (hg : h >>> 28 = 7) :
    frNodeW (n + 1) m h = frLetK₁ n (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 1))
      (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 2))
      (frW n m (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3))) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [frNodeW]; simp only [hv1, hg, ↓reduceIte, UInt64.not_le.mpr hv2, frLetK₁, frLetK₁.frLetK₂,
    frLetK₁.frLetK₃]
  simp

end arms

attribute [arena_grind =] frK_some frSetK_some frAppK₁_some frAppK₂_some frBindK₁_some
  frBindK₂_some frLetK₁_some frLetK₂_some frLetK₃_some frSet_eq
grind_pattern [arena_grind] frW_hit => frW (n + 1) m h
grind_pattern [arena_grind] frW_miss => frW (n + 1) m h
grind_pattern [arena_grind] frNodeW_bvar => frNodeW (n + 1) m h
grind_pattern [arena_grind] frNodeW_sort => frNodeW (n + 1) m h
grind_pattern [arena_grind] frNodeW_const => frNodeW (n + 1) m h
grind_pattern [arena_grind] frNodeW_lit => frNodeW (n + 1) m h
grind_pattern [arena_grind] frNodeW_fvar => frNodeW (n + 1) m h
grind_pattern [arena_grind] frNodeW_lam => frNodeW (n + 1) m h
grind_pattern [arena_grind] frNodeW_forall => frNodeW (n + 1) m h
grind_pattern [arena_grind] frNodeW_proj => frNodeW (n + 1) m h
grind_pattern [arena_grind] frNodeW_app => frNodeW (n + 1) m h
grind_pattern [arena_grind] frNodeW_let => frNodeW (n + 1) m h

/-- con-ron: ConRon/Arena/ExprOps.lean:1483-1505 ConRon.Arena.fvarRangeGo -/
@[l_impl ConRon.Arena.fvarRangeGo]
def frGo : FunDecl := lfn (h) locals (fd, j, d, r, u) {
  (fd, j, d) := call fm_find(h, 0);
  if fd != 0 { return FRMEMO.u64[j * 4 + 3] };
  r := call fr_node(h);
  (fd, j, d) := call fm_find(h, 0);
  u := call fm_put(h, 0, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1483-1505 ConRon.Arena.fvarRangeGo -/
@[l_impl ConRon.Arena.fvarRangeGo]
def frNode : FunDecl := lfn (h) locals (g, t, i, f, a, b, x, y, z) {
  g := h >> 28;
  t := (h >> 27) & 1;
  i := h & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if g == 0 { if CTL.u64[22 + t] <= i { abort }; return 0 };
  if g == 1 {
    if CTL.u64[26 + t] <= i { abort };
    x := FVREC.u64[i * 4 + t * 2] + 1;
    if x == 0 { abort };
    return x
  };
  if g == 4 {
    if CTL.u64[4 + t] <= i { abort };
    f := AREC.u64[i * 4 + t * 2];
    a := AREC.u64[i * 4 + t * 2 + 1];
    x := call fr_go(f);
    y := call fr_go(a);
    return x + (y - x) * u64(x < y)
  };
  if g == 5 {
    if CTL.u64[28 + t] <= i { abort };
    f := LAREC.u64[i * 4 + t * 2];
    a := LAREC.u64[i * 4 + t * 2 + 1];
    x := call fr_go(f);
    y := call fr_go(a);
    return x + (y - x) * u64(x < y)
  };
  if g == 6 {
    if CTL.u64[30 + t] <= i { abort };
    f := FAREC.u64[i * 4 + t * 2];
    a := FAREC.u64[i * 4 + t * 2 + 1];
    x := call fr_go(f);
    y := call fr_go(a);
    return x + (y - x) * u64(x < y)
  };
  if g == 9 {
    if CTL.u64[32 + t] <= i { abort };
    f := PJREC.u64[i * 6 + t * 3 + 2];
    x := call fr_go(f);
    return x
  };
  if g == 7 {
    if CTL.u64[20 + t] <= i { abort };
    f := LEREC.u64[i * 6 + t * 3];
    a := LEREC.u64[i * 6 + t * 3 + 1];
    b := LEREC.u64[i * 6 + t * 3 + 2];
    x := call fr_go(f);
    y := call fr_go(a);
    z := call fr_go(b);
    x := x + (y - x) * u64(x < y);
    return x + (z - x) * u64(x < z)
  };
  if g == 2 { if CTL.u64[16 + t] <= i { abort }; return 0 };
  if g == 3 { if CTL.u64[18 + t] <= i { abort }; return 0 };
  if g == 8 { if CTL.u64[2 + t] <= i { abort }; return 0 };
  abort
}

section go
variable (p : Prog) (hpf : p.lookup "fm_find" = some (memoFindG frSch))
  (hps : p.lookup "fm_put" = some (memoPutG frSch)) (hp : p.lookup "fr_go" = some frGo)
  (hpn : p.lookup "fr_node" = some frNode)

/-- The spec of `fr_go` at fuel `n`. -/
def FrGoSpec (n : Nat) : Prop := ∀ (s₀ : St) (h : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "fr_go" [h]
    ⦃fun r s' => LocEq s' s₀ ∧ frW n s₀.mem h = some (r.headD 0, s'.mem); ⊤⦄

/-- The spec of `fr_node` at fuel `n`. -/
def FrNodeSpec (n : Nat) : Prop := ∀ (s₀ : St) (h : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "fr_node" [h]
    ⦃fun r s' => LocEq s' s₀ ∧ frNodeW n s₀.mem h = some (r.headD 0, s'.mem); ⊤⦄

include hpf hps hp in
theorem frGo_step (n : Nat) (ih : FrNodeSpec p n) : FrGoSpec p (n + 1) := by
  unfold FrNodeSpec at ih
  intro s₀ h
  rw [invoke_eq _ hp]
  simp only [callFn, frGo]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec frSch p _ hpf n, memoPutG_spec frSch p _ hps n, ih] <;>
    finish

set_option maxHeartbeats 1000000 in
include hpn in
theorem frNode_step (n : Nat) (ih : FrGoSpec p n) : FrNodeSpec p (n + 1) := by
  unfold FrGoSpec at ih
  intro s₀ h
  rw [invoke_eq _ hpn]
  simp only [callFn, frNode]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
    finish [viewOK, tierW, idxW, maxW]

include hpf hps hp hpn in
/-- **`fr_go` and `fr_node` are their models**, at every fuel. -/
theorem frGo_spec (n : Nat) : FrGoSpec p n ∧ FrNodeSpec p n := by
  induction n with
  | zero =>
    constructor
    · intro s₀ h; rw [invoke_eq _ hp]; simp only [callFn, frGo]; vcgen [exec] <;> grind
    · intro s₀ h; rw [invoke_eq _ hpn]; simp only [callFn, frNode]; vcgen [exec] <;> grind
  | succ n ih => exact ⟨frGo_step p hpf hps hp n ih.2, frNode_step p hpn n ih.1⟩

/-! ## `fr_memo(h)`: the entry, between two clears -/

/-- After the walk: clear the memo again. -/
def frClrK : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m₁) => if rdW (m₁.arr64 CTL) 46 + 2 = 0 then none else some (r, mclearG frSch m₁)

/-- **The model of `fr_memo`.** -/
def frMemoW (n : Nat) (m : Mem) (h : Word) : Option (Word × Mem) :=
  if rdW (m.arr64 CTL) 46 + 2 = 0 then none else frClrK (frW n (mclearG frSch m) h)

theorem frMemoW_eq (n : Nat) (m : Mem) (h : Word) (h0 : rdW (m.arr64 CTL) 46 + 2 ≠ 0) :
    frMemoW n m h = frClrK (frW n (mclearG frSch m) h) := by simp [frMemoW, h0]

theorem frClrK_some (r : Word) (m₁ : Mem) (h0 : rdW (m₁.arr64 CTL) 46 + 2 ≠ 0) :
    frClrK (some (r, m₁)) = some (r, mclearG frSch m₁) := by simp [frClrK, h0]

grind_pattern [arena_grind] frMemoW_eq => frMemoW n m h
grind_pattern [arena_grind] frClrK_some => frClrK (some (r, m₁))

/-- con-ron: ConRon/Arena/ExprOps.lean:1557-1563 ConRon.Arena.fvarRangeMemo -/
@[l_impl ConRon.Arena.fvarRangeMemo]
def frMemo : FunDecl := lfn (h) locals (r, u) {
  u := call fm_clear();
  r := call fr_go(h);
  u := call fm_clear();
  return r
}

include hpf hps hp hpn in
theorem frMemo_spec (hpc : p.lookup "fm_clear" = some (memoClearG frSch))
    (hpm : p.lookup "fr_memo" = some frMemo) (n : Nat) (s₀ : St) (h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "fr_memo" [h]
    ⦃fun r s' => LocEq s' s₀ ∧ frMemoW n s₀.mem h = some (r.headD 0, s'.mem); ⊤⦄ := by
  have ih := (frGo_spec p hpf hps hp hpn n).1
  unfold FrGoSpec at ih
  rw [invoke_eq _ hpm]
  simp only [callFn, frMemo]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, memoClearG_spec frSch p _ hpc n, ih] <;>
    finish

end go

/-- The walk and the memo, as one program. -/
def fvarRangeProg : Prog :=
  [("fm_find", memoFindG frSch), ("fm_put", memoPutG frSch), ("fm_clear", memoClearG frSch),
    ("fr_go", frGo), ("fr_node", frNode), ("fr_memo", frMemo)]

end L.Arena
