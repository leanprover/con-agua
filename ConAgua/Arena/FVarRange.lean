module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
public import ConAgua.Arena.MemoLib
public import ConAgua.Arena.ViewL
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

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
`instantiate1Lift`/`liftLooseBVars` read `der_b`: `fvarB ≤ d` skips the walk (con-ron's `expr_ops.rs`).

`fr_go(h, c)`: `abort` at `c = 0` (the twin's `fuel` exhausted: it throws), else probe the memo
(`fm_find`, `memoFindG frSch`); on a hit return the value. Otherwise `fr_node(h, c - 1)` decodes
the handle and dispatches on the tag, every child at the same `c - 1` (the twin's depth counter,
`fvarRangeGo (fuel + 1)` runs its arms at `fuel`):

* `bvar i` (tag 0): `0`;
* `fvar idx _` (tag 1): `idx + 1` (an `abort` where it wraps);
* `sort`, `const`, `lit` (tags 2, 3, 8): `0`;
* `app f a` (tag 4): `max (fr_go f) (fr_go a)`;
* `lam ty body`, `forallE ty body` (tags 5, 6): `max (fr_go ty) (fr_go body)`;
* `letE ty val body` (tag 7): `max (max (fr_go ty) (fr_go val)) (fr_go body)`;
* `proj n i e` (tag 9): `fr_go e`;
* any other tag: `abort` (the arena's `view` fails there too).

then record the result (probe again, `fm_put`). `fr_memo(h, c)` is `fm_clear(); r := fr_go(h, c); fm_clear()`.
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
def frW : Nat → Mem → Word → Word → Option (Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, h, c =>
    if c = 0 then none
    else if mfindG frSch m h 0 = [] then none
    else if (mfindG frSch m h 0).headD 0 ≠ 0 then
      some (rdW (m.arr64 FRMEMO) ((mfindG frSch m h 0).tail.headD 0 * 4 + 3), m)
    else
      match frNodeW n m h (c - 1) with
      | none => none
      | some (r, m₁) => frSet m₁ h r

/-- **The model of `fr_node`**: the view and the dispatch on the tag. -/
def frNodeW : Nat → Mem → Word → Word → Option (Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, h, c =>
    if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if h >>> 28 = 0 then
      if tcnt m BVAR (tierW h) ≤ idxW h then none else some (0, m)
    else if h >>> 28 = 1 then
      if tcnt m FVAR (tierW h) ≤ idxW h then none
      else if tfld m FVAR (tierW h) (idxW h) 0 + 1 = 0 then none
      else some (tfld m FVAR (tierW h) (idxW h) 0 + 1, m)
    else if h >>> 28 = 4 then
      if tcnt m APP (tierW h) ≤ idxW h then none
      else
        match frW n m (tfld m APP (tierW h) (idxW h) 0) c with
        | none => none
        | some (x, m₁) =>
          match frW n m₁ (tfld m APP (tierW h) (idxW h) 1) c with
          | none => none
          | some (y, m₂) => some (maxW x y, m₂)
    else if h >>> 28 = 5 then
      if tcnt m LAM (tierW h) ≤ idxW h then none
      else
        match frW n m (tfld m LAM (tierW h) (idxW h) 0) c with
        | none => none
        | some (x, m₁) =>
          match frW n m₁ (tfld m LAM (tierW h) (idxW h) 1) c with
          | none => none
          | some (y, m₂) => some (maxW x y, m₂)
    else if h >>> 28 = 6 then
      if tcnt m FORALL (tierW h) ≤ idxW h then none
      else
        match frW n m (tfld m FORALL (tierW h) (idxW h) 0) c with
        | none => none
        | some (x, m₁) =>
          match frW n m₁ (tfld m FORALL (tierW h) (idxW h) 1) c with
          | none => none
          | some (y, m₂) => some (maxW x y, m₂)
    else if h >>> 28 = 9 then
      if tcnt m PROJ (tierW h) ≤ idxW h then none
      else frW n m (tfld m PROJ (tierW h) (idxW h) 2) c
    else if h >>> 28 = 7 then
      if tcnt m LET (tierW h) ≤ idxW h then none
      else
        match frW n m (tfld m LET (tierW h) (idxW h) 0) c with
        | none => none
        | some (x, m₁) =>
          match frW n m₁ (tfld m LET (tierW h) (idxW h) 1) c with
          | none => none
          | some (y, m₂) =>
            match frW n m₂ (tfld m LET (tierW h) (idxW h) 2) c with
            | none => none
            | some (z, m₃) => some (maxW (maxW x y) z, m₃)
    else if h >>> 28 = 2 then
      if tcnt m SORT (tierW h) ≤ idxW h then none else some (0, m)
    else if h >>> 28 = 3 then
      if tcnt m CONST (tierW h) ≤ idxW h then none else some (0, m)
    else if h >>> 28 = 8 then
      if tcnt m LIT (tierW h) ≤ idxW h then none else some (0, m)
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
def frAppK₁ (n : Nat) (c a : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => frAppK₂ x (frW n m₁ a c)
where frAppK₂ (x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) => some (maxW x y, m₂)

/-- The binder arm (`lam`, `forallE`) after the type, and after the body: no truncation. -/
def frBindK₁ (n : Nat) (c b : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => frBindK₂ x (frW n m₁ b c)
where frBindK₂ (x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) => some (maxW x y, m₂)

/-- The `letE` arm after each child: no truncation. -/
def frLetK₁ (n : Nat) (c a b : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => frLetK₂ x (frW n m₁ a c)
where
  frLetK₂ (x : Word) : Option (Word × Mem) → Option (Word × Mem)
    | none => none
    | some (y, m₂) => frLetK₃ x y (frW n m₂ b c)
  frLetK₃ (x y : Word) : Option (Word × Mem) → Option (Word × Mem)
    | none => none
    | some (z, m₃) => some (maxW (maxW x y) z, m₃)

section arms
variable (n : Nat) (m m₁ m₂ m₃ : Mem) (h r x y z f a b c : Word)

theorem frK_some : frK h (some (r, m₁)) = frSet m₁ h r := rfl
theorem frSetK_some : frSetK r (some m₁) = some (r, m₁) := rfl
theorem frAppK₁_some : frAppK₁ n c a (some (x, m₁)) = frAppK₁.frAppK₂ x (frW n m₁ a c) := rfl
theorem frAppK₂_some : frAppK₁.frAppK₂ x (some (y, m₂)) = some (maxW x y, m₂) := rfl
theorem frBindK₁_some : frBindK₁ n c b (some (x, m₁)) = frBindK₁.frBindK₂ x (frW n m₁ b c) := rfl
theorem frBindK₂_some : frBindK₁.frBindK₂ x (some (y, m₂)) = some (maxW x y, m₂) := rfl
theorem frLetK₁_some : frLetK₁ n c a b (some (x, m₁)) = frLetK₁.frLetK₂ n c b x (frW n m₁ a c) := rfl
theorem frLetK₂_some : frLetK₁.frLetK₂ n c b x (some (y, m₂)) = frLetK₁.frLetK₃ x y (frW n m₂ b c) := rfl
theorem frLetK₃_some :
    frLetK₁.frLetK₃ x y (some (z, m₃)) = some (maxW (maxW x y) z, m₃) := rfl

theorem frSet_eq : frSet m h r = frSetK r (msetG frSch m h 0 r) := by
  simp only [frSet, frSetK]

theorem frW_hit (hc : c ≠ 0) (hr : mfindG frSch m h 0 ≠ []) (hh : (mfindG frSch m h 0).headD 0 ≠ 0) :
    frW (n + 1) m h c = some (rdW (m.arr64 FRMEMO) ((mfindG frSch m h 0).tail.headD 0 * 4 + 3), m) := by
  rw [frW]; simp only [hc, hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]

theorem frW_miss (hc : c ≠ 0) (hr : mfindG frSch m h 0 ≠ []) (hh : (mfindG frSch m h 0).headD 0 = 0) :
    frW (n + 1) m h c = frK h (frNodeW n m h (c - 1)) := by
  rw [frW]; simp only [hc, hr, hh, ↓reduceIte, ne_eq, not_true_eq_false, frK]

theorem frNodeW_bvar (hg : h >>> 28 = 0) (hv : viewOK m h BVAR) : frNodeW (n + 1) m h c = some (0, m) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [frNodeW]; simp [hv1, hg, UInt64.not_le.mpr hv2]

theorem frNodeW_fvar (hv : viewOK m h FVAR) (hg : h >>> 28 = 1)
    (h1 : tfld m FVAR (tierW h) (idxW h) 0 + 1 ≠ 0) :
    frNodeW (n + 1) m h c = some (tfld m FVAR (tierW h) (idxW h) 0 + 1, m) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [frNodeW]; simp only [hv1, hg, ↓reduceIte, h1]; simp [UInt64.not_le.mpr hv2]

theorem frNodeW_sort (hg : h >>> 28 = 2) (hv : viewOK m h SORT) : frNodeW (n + 1) m h c = some (0, m) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [frNodeW]; simp [hv1, hg, UInt64.not_le.mpr hv2]

theorem frNodeW_const (hg : h >>> 28 = 3) (hv : viewOK m h CONST) : frNodeW (n + 1) m h c = some (0, m) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [frNodeW]; simp [hv1, hg, UInt64.not_le.mpr hv2]

theorem frNodeW_lit (hg : h >>> 28 = 8) (hv : viewOK m h LIT) : frNodeW (n + 1) m h c = some (0, m) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [frNodeW]; simp [hv1, hg, UInt64.not_le.mpr hv2]

theorem frNodeW_app (hv : viewOK m h APP) (hg : h >>> 28 = 4) :
    frNodeW (n + 1) m h c = frAppK₁ n c (tfld m APP (tierW h) (idxW h) 1)
      (frW n m (tfld m APP (tierW h) (idxW h) 0) c) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [frNodeW]; simp only [hv1, hg, ↓reduceIte, UInt64.not_le.mpr hv2, frAppK₁, frAppK₁.frAppK₂]
  simp

theorem frNodeW_lam (hv : viewOK m h LAM) (hg : h >>> 28 = 5) :
    frNodeW (n + 1) m h c = frBindK₁ n c (tfld m LAM (tierW h) (idxW h) 1)
      (frW n m (tfld m LAM (tierW h) (idxW h) 0) c) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [frNodeW]; simp only [hv1, hg, ↓reduceIte, UInt64.not_le.mpr hv2, frBindK₁, frBindK₁.frBindK₂]
  simp

theorem frNodeW_forall (hv : viewOK m h FORALL) (hg : h >>> 28 = 6) :
    frNodeW (n + 1) m h c = frBindK₁ n c (tfld m FORALL (tierW h) (idxW h) 1)
      (frW n m (tfld m FORALL (tierW h) (idxW h) 0) c) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [frNodeW]; simp only [hv1, hg, ↓reduceIte, UInt64.not_le.mpr hv2, frBindK₁, frBindK₁.frBindK₂]
  simp

theorem frNodeW_proj (hv : viewOK m h PROJ) (hg : h >>> 28 = 9) :
    frNodeW (n + 1) m h c = frW n m (tfld m PROJ (tierW h) (idxW h) 2) c := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [frNodeW]; simp [hv1, hg, UInt64.not_le.mpr hv2]

theorem frNodeW_let (hv : viewOK m h LET) (hg : h >>> 28 = 7) :
    frNodeW (n + 1) m h c = frLetK₁ n c (tfld m LET (tierW h) (idxW h) 1)
      (tfld m LET (tierW h) (idxW h) 2)
      (frW n m (tfld m LET (tierW h) (idxW h) 0) c) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [frNodeW]; simp only [hv1, hg, ↓reduceIte, UInt64.not_le.mpr hv2, frLetK₁, frLetK₁.frLetK₂,
    frLetK₁.frLetK₃]
  simp

end arms

attribute [arena_grind =] frK_some frSetK_some frAppK₁_some frAppK₂_some frBindK₁_some
  frBindK₂_some frLetK₁_some frLetK₂_some frLetK₃_some frSet_eq
grind_pattern [arena_grind] frW_hit => frW (n + 1) m h c
grind_pattern [arena_grind] frW_miss => frW (n + 1) m h c
grind_pattern [arena_grind] frNodeW_bvar => frNodeW (n + 1) m h c
grind_pattern [arena_grind] frNodeW_sort => frNodeW (n + 1) m h c
grind_pattern [arena_grind] frNodeW_const => frNodeW (n + 1) m h c
grind_pattern [arena_grind] frNodeW_lit => frNodeW (n + 1) m h c
grind_pattern [arena_grind] frNodeW_fvar => frNodeW (n + 1) m h c
grind_pattern [arena_grind] frNodeW_lam => frNodeW (n + 1) m h c
grind_pattern [arena_grind] frNodeW_forall => frNodeW (n + 1) m h c
grind_pattern [arena_grind] frNodeW_proj => frNodeW (n + 1) m h c
grind_pattern [arena_grind] frNodeW_app => frNodeW (n + 1) m h c
grind_pattern [arena_grind] frNodeW_let => frNodeW (n + 1) m h c

/-- con-ron: ConRon/Arena/ExprOps.lean:1483-1505 ConRon.Arena.fvarRangeGo -/
@[l_impl ConRon.Arena.fvarRangeGo]
def frGo : FunDecl := lfn (h, c) locals (fd, j, d, r, u) {
  if c == 0 { abort };
  (fd, j, d) := call fm_find(h, 0);
  if fd != 0 { return FRMEMO.u64[j * 4 + 3] };
  r := call fr_node(h, c - 1);
  (fd, j, d) := call fm_find(h, 0);
  u := call fm_put(h, 0, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1483-1505 ConRon.Arena.fvarRangeGo -/
@[l_impl ConRon.Arena.fvarRangeGo]
def frNode : FunDecl := lfn (h, c) locals (g, t, i, f, a, b, x, y, z) {
  g := h >> 28;
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if g == 0 { if BVAR⟨t⟩.count <= i { abort }; return 0 };
  if g == 1 {
    if FVAR⟨t⟩.count <= i { abort };
    x := FVAR⟨t, i⟩.i + 1;
    if x == 0 { abort };
    return x
  };
  if g == 4 {
    if APP⟨t⟩.count <= i { abort };
    f := APP⟨t, i⟩.f;
    a := APP⟨t, i⟩.a;
    x := call fr_go(f, c);
    y := call fr_go(a, c);
    return x + (y - x) * u64(x < y)
  };
  if g == 5 {
    if LAM⟨t⟩.count <= i { abort };
    f := LAM⟨t, i⟩.ty;
    a := LAM⟨t, i⟩.b;
    x := call fr_go(f, c);
    y := call fr_go(a, c);
    return x + (y - x) * u64(x < y)
  };
  if g == 6 {
    if FORALL⟨t⟩.count <= i { abort };
    f := FORALL⟨t, i⟩.ty;
    a := FORALL⟨t, i⟩.b;
    x := call fr_go(f, c);
    y := call fr_go(a, c);
    return x + (y - x) * u64(x < y)
  };
  if g == 9 {
    if PROJ⟨t⟩.count <= i { abort };
    f := PROJ⟨t, i⟩.e;
    x := call fr_go(f, c);
    return x
  };
  if g == 7 {
    if LET⟨t⟩.count <= i { abort };
    f := LET⟨t, i⟩.ty;
    a := LET⟨t, i⟩.v;
    b := LET⟨t, i⟩.b;
    x := call fr_go(f, c);
    y := call fr_go(a, c);
    z := call fr_go(b, c);
    x := x + (y - x) * u64(x < y);
    return x + (z - x) * u64(x < z)
  };
  if g == 2 { if SORT⟨t⟩.count <= i { abort }; return 0 };
  if g == 3 { if CONST⟨t⟩.count <= i { abort }; return 0 };
  if g == 8 { if LIT⟨t⟩.count <= i { abort }; return 0 };
  abort
}

section go
variable (p : Prog) (hpf : p.lookup "fm_find" = some (memoFindG frSch))
  (hps : p.lookup "fm_put" = some (memoPutG frSch)) (hp : p.lookup "fr_go" = some frGo)
  (hpn : p.lookup "fr_node" = some frNode)

/-- The spec of `fr_go` at fuel `n`. -/
def FrGoSpec (n : Nat) : Prop := ∀ (s₀ : St) (h c : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "fr_go" [h, c]
    ⦃fun r s' => LocEq s' s₀ ∧ frW n s₀.mem h c = some (r.headD 0, s'.mem); ⊤⦄

/-- The spec of `fr_node` at fuel `n`. -/
def FrNodeSpec (n : Nat) : Prop := ∀ (s₀ : St) (h c : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "fr_node" [h, c]
    ⦃fun r s' => LocEq s' s₀ ∧ frNodeW n s₀.mem h c = some (r.headD 0, s'.mem); ⊤⦄

include hpf hps hp in
theorem frGo_step (n : Nat) (ih : FrNodeSpec p n) : FrGoSpec p (n + 1) := by
  unfold FrNodeSpec at ih
  intro s₀ h c
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
  intro s₀ h c
  rw [invoke_eq _ hpn]
  simp only [callFn, frNode]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt,
      tcntM, evalE_tierE, evalE_idxE, ih] <;>
    finish [viewOK, tierW, idxW, maxW]

include hpf hps hp hpn in
/-- **`fr_go` and `fr_node` are their models**, at every fuel. -/
theorem frGo_spec (n : Nat) : FrGoSpec p n ∧ FrNodeSpec p n := by
  induction n with
  | zero =>
    constructor
    · intro s₀ h c; rw [invoke_eq _ hp]; simp only [callFn, frGo]; vcgen [exec] <;> grind
    · intro s₀ h c; rw [invoke_eq _ hpn]; simp only [callFn, frNode]; vcgen [exec] <;> grind
  | succ n ih => exact ⟨frGo_step p hpf hps hp n ih.2, frNode_step p hpn n ih.1⟩

/-! ## `fr_memo(h, c)`: the entry, between two clears -/

/-- After the walk: clear the memo again. -/
def frClrK : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m₁) => if rdW (m₁.arr64 CTL) 46 + 2 = 0 then none else some (r, mclearG frSch m₁)

/-- **The model of `fr_memo`.** -/
def frMemoW (n : Nat) (m : Mem) (h c : Word) : Option (Word × Mem) :=
  if rdW (m.arr64 CTL) 46 + 2 = 0 then none else frClrK (frW n (mclearG frSch m) h c)

theorem frMemoW_eq (n : Nat) (m : Mem) (h c : Word) (h0 : rdW (m.arr64 CTL) 46 + 2 ≠ 0) :
    frMemoW n m h c = frClrK (frW n (mclearG frSch m) h c) := by simp [frMemoW, h0]

theorem frClrK_some (r : Word) (m₁ : Mem) (h0 : rdW (m₁.arr64 CTL) 46 + 2 ≠ 0) :
    frClrK (some (r, m₁)) = some (r, mclearG frSch m₁) := by simp [frClrK, h0]

grind_pattern [arena_grind] frMemoW_eq => frMemoW n m h c
grind_pattern [arena_grind] frClrK_some => frClrK (some (r, m₁))

/-- con-ron: ConRon/Arena/ExprOps.lean:1557-1563 ConRon.Arena.fvarRangeMemo -/
@[l_impl ConRon.Arena.fvarRangeMemo]
def frMemo : FunDecl := lfn (h, c) locals (r, u) {
  u := call fm_clear();
  r := call fr_go(h, c);
  u := call fm_clear();
  return r
}

include hpf hps hp hpn in
theorem frMemo_spec (hpc : p.lookup "fm_clear" = some (memoClearG frSch))
    (hpm : p.lookup "fr_memo" = some frMemo) (n : Nat) (s₀ : St) (h c : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "fr_memo" [h, c]
    ⦃fun r s' => LocEq s' s₀ ∧ frMemoW n s₀.mem h c = some (r.headD 0, s'.mem); ⊤⦄ := by
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
