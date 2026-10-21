module

public import ConAgua.Arena.MemoLib
public import ConAgua.Arena.AppStore
public import ConAgua.Arena.LetStore
public import ConAgua.Arena.BVarStore
public import ConAgua.Arena.FVarStore
public import ConAgua.Arena.LamStore
public import ConAgua.Arena.ForallStore
public import ConAgua.Arena.ProjStore
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store

@[expose] public section

/-!
# The first recursive walk: the memoized loose-bvar bound

con-ron's `bvar_bound_go` (`arena/expr_ops.rs:1981`, Lean twin `bvarBoundGo`,
`Arena/ExprOps.lean:1404`) and its entry `bvar_bound_memo` (`:2054`, `bvarBoundMemo`): the exact
loose-bvar bound of an expression handle, memoized per node in `bvarBC`, recursive (not an
explicit work stack, as in con-ron). The checker calls it on the saturated branch of `bvarB`
(`looseBVarsBoundedFast`, `instantiate1Lift`'s cutoff).

`bb_go(h)`: probe the memo (`bm_find`, the memo library's `memoFindG bmSch`); on a hit return the
value. Otherwise decode the handle
word (tag `h >> 28`, tier bit 27, index `h & (2^27 - 1)`), refuse a scratch handle while the
scratch tier is closed and an index at or past the tier's count (the arena's `view` fails there:
a dangling handle), and dispatch on the tag:

* `bvar i` (tag 0): `i + 1` (an `abort` where `i + 1` wraps);
* `fvar`, `sort`, `const`, `lit` (tags 1, 2, 3, 8): `0`;
* `app f a` (tag 4): `max (bb_go f) (bb_go a)`;
* `lam ty body`, `forallE ty body` (tags 5, 6): `max (bb_go ty) (bb_go body - 1)`, truncating;
* `letE ty val body` (tag 7): `max (max (bb_go ty) (bb_go val)) (bb_go body - 1)`;
* `proj n i e` (tag 9): `bb_go e`;
* any other tag: `abort` (the arena's `view` fails there too).

then record the result (probe again, `bm_put`). `bb_memo(h)` is
`bm_clear(); r := bb_go(h); bm_clear()`.

The model `bbW n m h` follows the code with L's fuel `n` (each call one level).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The larger of two words (branch-free in L: `x + (y - x) * u64(x < y)`). -/
def maxW (x y : Word) : Word := x + (y - x) * (if x < y then 1 else 0)

/-- Truncating `z - 1` (branch-free in L: `z - u64(0 < z)`). -/
def predW (z : Word) : Word := z - (if 0 < z then 1 else 0)

/-- The tier bit and the index of a handle word. -/
def tierW (h : Word) : Word := (h >>> 27) &&& 1
def idxW (h : Word) : Word := h &&& 134217727

/-- Record the result `r` at `h` and return it. -/
def bbSet (m : Mem) (h r : Word) : Option (Word × Mem) :=
  match msetG bmSch m h 0 r with
  | none => none
  | some m' => some (r, m')

/-- The view checks of `bb_node`: a scratch handle needs the scratch tier open, and the index
must be below the tier's count `CTL[c + t]`. -/
def viewOK (m : Mem) (h c : Word) : Prop :=
  ¬ (tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) ∧ idxW h < rdW (m.arr64 CTL) (c + tierW h)

mutual
/-- **The model of `bb_go`** at L fuel `n`: the result and the memory after, `none` where the L
code aborts. -/
def bbW : Nat → Mem → Word → Option (Word × Mem)
  | 0, _, _ => none
  | n + 1, m, h =>
    if mfindG bmSch m h 0 = [] then none
    else if (mfindG bmSch m h 0).headD 0 ≠ 0 then
      some (rdW (m.arr64 BMEMO) ((mfindG bmSch m h 0).tail.headD 0 * 4 + 3), m)
    else
      match bbNodeW n m h with
      | none => none
      | some (r, m₁) => bbSet m₁ h r

/-- **The model of `bb_node`**: the view and the dispatch on the tag. -/
def bbNodeW : Nat → Mem → Word → Option (Word × Mem)
  | 0, _, _ => none
  | n + 1, m, h =>
    if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if h >>> 28 = 0 then
      if rdW (m.arr64 CTL) (22 + tierW h) ≤ idxW h then none
      else if rdW (m.arr64 BREC) (idxW h * 2 + tierW h) + 1 = 0 then none
      else some (rdW (m.arr64 BREC) (idxW h * 2 + tierW h) + 1, m)
    else if h >>> 28 = 4 then
      if rdW (m.arr64 CTL) (4 + tierW h) ≤ idxW h then none
      else
        match bbW n m (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2)) with
        | none => none
        | some (x, m₁) =>
          match bbW n m₁ (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2 + 1)) with
          | none => none
          | some (y, m₂) => some (maxW x y, m₂)
    else if h >>> 28 = 5 then
      if rdW (m.arr64 CTL) (28 + tierW h) ≤ idxW h then none
      else
        match bbW n m (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2)) with
        | none => none
        | some (x, m₁) =>
          match bbW n m₁ (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2 + 1)) with
          | none => none
          | some (y, m₂) => some (maxW x (predW y), m₂)
    else if h >>> 28 = 6 then
      if rdW (m.arr64 CTL) (30 + tierW h) ≤ idxW h then none
      else
        match bbW n m (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2)) with
        | none => none
        | some (x, m₁) =>
          match bbW n m₁ (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2 + 1)) with
          | none => none
          | some (y, m₂) => some (maxW x (predW y), m₂)
    else if h >>> 28 = 9 then
      if rdW (m.arr64 CTL) (32 + tierW h) ≤ idxW h then none
      else bbW n m (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 2))
    else if h >>> 28 = 7 then
      if rdW (m.arr64 CTL) (20 + tierW h) ≤ idxW h then none
      else
        match bbW n m (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3)) with
        | none => none
        | some (x, m₁) =>
          match bbW n m₁ (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 1)) with
          | none => none
          | some (y, m₂) =>
            match bbW n m₂ (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 2)) with
            | none => none
            | some (z, m₃) => some (maxW (maxW x y) (predW z), m₃)
    else if h >>> 28 = 1 then
      if rdW (m.arr64 CTL) (26 + tierW h) ≤ idxW h then none else some (0, m)
    else if h >>> 28 = 2 then
      if rdW (m.arr64 CTL) (16 + tierW h) ≤ idxW h then none else some (0, m)
    else if h >>> 28 = 3 then
      if rdW (m.arr64 CTL) (18 + tierW h) ≤ idxW h then none else some (0, m)
    else if h >>> 28 = 8 then
      if rdW (m.arr64 CTL) (2 + tierW h) ≤ idxW h then none else some (0, m)
    else none
end

/-! ### The guarded equations, one per reachable arm

Each arm is an equation whose right side names the continuation (`bbK`, `appK₁`, …): an equation
`bbW n m f = some (x, m₁)` from a callee spec then rewrites the continuation's argument, and the
continuation's own equation fires on `some`. -/

/-- After `bb_node`: record the result. -/
def bbK (h : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m₁) => bbSet m₁ h r

/-- After `bm_put`. -/
def setK (r : Word) : Option Mem → Option (Word × Mem)
  | none => none
  | some m' => some (r, m')

/-- The `app` arm after the first child, and after the second. -/
def appK₁ (n : Nat) (a : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => appK₂ x (bbW n m₁ a)
where appK₂ (x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) => some (maxW x y, m₂)

/-- The binder arm (`lam`, `forallE`) after the type, and after the body. -/
def bindK₁ (n : Nat) (b : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => bindK₂ x (bbW n m₁ b)
where bindK₂ (x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) => some (maxW x (predW y), m₂)

/-- The `letE` arm after each child. -/
def letK₁ (n : Nat) (a b : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => letK₂ x (bbW n m₁ a)
where
  letK₂ (x : Word) : Option (Word × Mem) → Option (Word × Mem)
    | none => none
    | some (y, m₂) => letK₃ x y (bbW n m₂ b)
  letK₃ (x y : Word) : Option (Word × Mem) → Option (Word × Mem)
    | none => none
    | some (z, m₃) => some (maxW (maxW x y) (predW z), m₃)

section arms
variable (n : Nat) (m m₁ m₂ m₃ : Mem) (h r x y z f a b : Word)

theorem bbK_some : bbK h (some (r, m₁)) = bbSet m₁ h r := rfl
theorem setK_some : setK r (some m₁) = some (r, m₁) := rfl
theorem appK₁_some : appK₁ n a (some (x, m₁)) = appK₁.appK₂ x (bbW n m₁ a) := rfl
theorem appK₂_some : appK₁.appK₂ x (some (y, m₂)) = some (maxW x y, m₂) := rfl
theorem bindK₁_some : bindK₁ n b (some (x, m₁)) = bindK₁.bindK₂ x (bbW n m₁ b) := rfl
theorem bindK₂_some : bindK₁.bindK₂ x (some (y, m₂)) = some (maxW x (predW y), m₂) := rfl
theorem letK₁_some : letK₁ n a b (some (x, m₁)) = letK₁.letK₂ n b x (bbW n m₁ a) := rfl
theorem letK₂_some : letK₁.letK₂ n b x (some (y, m₂)) = letK₁.letK₃ x y (bbW n m₂ b) := rfl
theorem letK₃_some :
    letK₁.letK₃ x y (some (z, m₃)) = some (maxW (maxW x y) (predW z), m₃) := rfl

theorem bbSet_eq : bbSet m h r = setK r (msetG bmSch m h 0 r) := by
  simp only [bbSet, setK]

theorem bbW_hit (hr : mfindG bmSch m h 0 ≠ []) (hh : (mfindG bmSch m h 0).headD 0 ≠ 0) :
    bbW (n + 1) m h = some (rdW (m.arr64 BMEMO) ((mfindG bmSch m h 0).tail.headD 0 * 4 + 3), m) := by
  rw [bbW]; simp only [hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]

theorem bbW_miss (hr : mfindG bmSch m h 0 ≠ []) (hh : (mfindG bmSch m h 0).headD 0 = 0) :
    bbW (n + 1) m h = bbK h (bbNodeW n m h) := by
  rw [bbW]; simp only [hr, hh, ↓reduceIte, ne_eq, not_true_eq_false, bbK]

theorem bbNodeW_bvar (hv : viewOK m h 22) (hg : h >>> 28 = 0)
    (h1 : rdW (m.arr64 BREC) (idxW h * 2 + tierW h) + 1 ≠ 0) :
    bbNodeW (n + 1) m h = some (rdW (m.arr64 BREC) (idxW h * 2 + tierW h) + 1, m) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [bbNodeW]; simp only [hv1, hg, ↓reduceIte, h1]; simp [UInt64.not_le.mpr hv2]

theorem bbNodeW_sort (hg : h >>> 28 = 2) (hv : viewOK m h 16) : bbNodeW (n + 1) m h = some (0, m) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [bbNodeW]; simp [hv1, hg, UInt64.not_le.mpr hv2]

theorem bbNodeW_const (hg : h >>> 28 = 3) (hv : viewOK m h 18) : bbNodeW (n + 1) m h = some (0, m) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [bbNodeW]; simp [hv1, hg, UInt64.not_le.mpr hv2]

theorem bbNodeW_fvar (hg : h >>> 28 = 1) (hv : viewOK m h 26) : bbNodeW (n + 1) m h = some (0, m) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [bbNodeW]; simp [hv1, hg, UInt64.not_le.mpr hv2]

theorem bbNodeW_lit (hg : h >>> 28 = 8) (hv : viewOK m h 2) : bbNodeW (n + 1) m h = some (0, m) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [bbNodeW]; simp [hv1, hg, UInt64.not_le.mpr hv2]

theorem bbNodeW_app (hv : viewOK m h 4) (hg : h >>> 28 = 4) :
    bbNodeW (n + 1) m h = appK₁ n (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2 + 1))
      (bbW n m (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2))) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [bbNodeW]; simp only [hv1, hg, ↓reduceIte, UInt64.not_le.mpr hv2, appK₁, appK₁.appK₂]
  simp

theorem bbNodeW_lam (hv : viewOK m h 28) (hg : h >>> 28 = 5) :
    bbNodeW (n + 1) m h = bindK₁ n (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2 + 1))
      (bbW n m (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2))) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [bbNodeW]; simp only [hv1, hg, ↓reduceIte, UInt64.not_le.mpr hv2, bindK₁, bindK₁.bindK₂]
  simp

theorem bbNodeW_forall (hv : viewOK m h 30) (hg : h >>> 28 = 6) :
    bbNodeW (n + 1) m h = bindK₁ n (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2 + 1))
      (bbW n m (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2))) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [bbNodeW]; simp only [hv1, hg, ↓reduceIte, UInt64.not_le.mpr hv2, bindK₁, bindK₁.bindK₂]
  simp

theorem bbNodeW_proj (hv : viewOK m h 32) (hg : h >>> 28 = 9) :
    bbNodeW (n + 1) m h = bbW n m (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 2)) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [bbNodeW]; simp [hv1, hg, UInt64.not_le.mpr hv2]

theorem bbNodeW_let (hv : viewOK m h 20) (hg : h >>> 28 = 7) :
    bbNodeW (n + 1) m h = letK₁ n (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 1))
      (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 2))
      (bbW n m (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3))) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [bbNodeW]; simp only [hv1, hg, ↓reduceIte, UInt64.not_le.mpr hv2, letK₁, letK₁.letK₂,
    letK₁.letK₃]
  simp

end arms

attribute [arena_grind =] bbK_some setK_some appK₁_some appK₂_some bindK₁_some bindK₂_some
  letK₁_some letK₂_some letK₃_some bbSet_eq
grind_pattern [arena_grind] bbW_hit => bbW (n + 1) m h
grind_pattern [arena_grind] bbW_miss => bbW (n + 1) m h
grind_pattern [arena_grind] bbNodeW_bvar => bbNodeW (n + 1) m h
grind_pattern [arena_grind] bbNodeW_sort => bbNodeW (n + 1) m h
grind_pattern [arena_grind] bbNodeW_const => bbNodeW (n + 1) m h
grind_pattern [arena_grind] bbNodeW_lit => bbNodeW (n + 1) m h
grind_pattern [arena_grind] bbNodeW_fvar => bbNodeW (n + 1) m h
grind_pattern [arena_grind] bbNodeW_lam => bbNodeW (n + 1) m h
grind_pattern [arena_grind] bbNodeW_forall => bbNodeW (n + 1) m h
grind_pattern [arena_grind] bbNodeW_proj => bbNodeW (n + 1) m h
grind_pattern [arena_grind] bbNodeW_app => bbNodeW (n + 1) m h
grind_pattern [arena_grind] bbNodeW_let => bbNodeW (n + 1) m h

def bbGo : FunDecl := lfn (h) locals (fd, j, d, r, u) {
  (fd, j, d) := call bm_find(h, 0);
  if fd != 0 { return BMEMO.u64[j * 4 + 3] };
  r := call bb_node(h);
  (fd, j, d) := call bm_find(h, 0);
  u := call bm_put(h, 0, r, fd, j);
  return r
}

def bbNode : FunDecl := lfn (h) locals (g, t, i, f, a, b, x, y, z) {
  g := h >> 28;
  t := (h >> 27) & 1;
  i := h & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if g == 0 {
    if CTL.u64[22 + t] <= i { abort };
    x := BREC.u64[i * 2 + t] + 1;
    if x == 0 { abort };
    return x
  };
  if g == 4 {
    if CTL.u64[4 + t] <= i { abort };
    f := AREC.u64[i * 4 + t * 2];
    a := AREC.u64[i * 4 + t * 2 + 1];
    x := call bb_go(f);
    y := call bb_go(a);
    return x + (y - x) * u64(x < y)
  };
  if g == 5 {
    if CTL.u64[28 + t] <= i { abort };
    f := LAREC.u64[i * 4 + t * 2];
    a := LAREC.u64[i * 4 + t * 2 + 1];
    x := call bb_go(f);
    y := call bb_go(a);
    y := y - u64(0 < y);
    return x + (y - x) * u64(x < y)
  };
  if g == 6 {
    if CTL.u64[30 + t] <= i { abort };
    f := FAREC.u64[i * 4 + t * 2];
    a := FAREC.u64[i * 4 + t * 2 + 1];
    x := call bb_go(f);
    y := call bb_go(a);
    y := y - u64(0 < y);
    return x + (y - x) * u64(x < y)
  };
  if g == 9 {
    if CTL.u64[32 + t] <= i { abort };
    f := PJREC.u64[i * 6 + t * 3 + 2];
    x := call bb_go(f);
    return x
  };
  if g == 7 {
    if CTL.u64[20 + t] <= i { abort };
    f := LEREC.u64[i * 6 + t * 3];
    a := LEREC.u64[i * 6 + t * 3 + 1];
    b := LEREC.u64[i * 6 + t * 3 + 2];
    x := call bb_go(f);
    y := call bb_go(a);
    z := call bb_go(b);
    x := x + (y - x) * u64(x < y);
    z := z - u64(0 < z);
    return x + (z - x) * u64(x < z)
  };
  if g == 1 { if CTL.u64[26 + t] <= i { abort }; return 0 };
  if g == 2 { if CTL.u64[16 + t] <= i { abort }; return 0 };
  if g == 3 { if CTL.u64[18 + t] <= i { abort }; return 0 };
  if g == 8 { if CTL.u64[2 + t] <= i { abort }; return 0 };
  abort
}

section go
variable (p : Prog) (hpf : p.lookup "bm_find" = some (memoFindG bmSch))
  (hps : p.lookup "bm_put" = some (memoPutG bmSch)) (hp : p.lookup "bb_go" = some bbGo)
  (hpn : p.lookup "bb_node" = some bbNode)

/-- The spec of `bb_go` at fuel `n`. -/
def BbGoSpec (n : Nat) : Prop := ∀ (s₀ : St) (h : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "bb_go" [h]
    ⦃fun r s' => LocEq s' s₀ ∧ bbW n s₀.mem h = some (r.headD 0, s'.mem); ⊤⦄

/-- The spec of `bb_node` at fuel `n`. -/
def BbNodeSpec (n : Nat) : Prop := ∀ (s₀ : St) (h : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "bb_node" [h]
    ⦃fun r s' => LocEq s' s₀ ∧ bbNodeW n s₀.mem h = some (r.headD 0, s'.mem); ⊤⦄

include hpf hps hp in
theorem bbGo_step (n : Nat) (ih : BbNodeSpec p n) : BbGoSpec p (n + 1) := by
  unfold BbNodeSpec at ih
  intro s₀ h
  rw [invoke_eq _ hp]
  simp only [callFn, bbGo]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec bmSch p _ hpf n, memoPutG_spec bmSch p _ hps n, ih] <;>
    finish

set_option maxHeartbeats 1000000 in
include hpn in
theorem bbNode_step (n : Nat) (ih : BbGoSpec p n) : BbNodeSpec p (n + 1) := by
  unfold BbGoSpec at ih
  intro s₀ h
  rw [invoke_eq _ hpn]
  simp only [callFn, bbNode]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
    finish [viewOK, tierW, idxW, maxW, predW]

include hpf hps hp hpn in
/-- **`bb_go` and `bb_node` are their models**, at every fuel: by induction on the fuel, the
recursive calls by the induction hypothesis. -/
theorem bbGo_spec (n : Nat) : BbGoSpec p n ∧ BbNodeSpec p n := by
  induction n with
  | zero =>
    constructor
    · intro s₀ h; rw [invoke_eq _ hp]; simp only [callFn, bbGo]; vcgen [exec] <;> grind
    · intro s₀ h; rw [invoke_eq _ hpn]; simp only [callFn, bbNode]; vcgen [exec] <;> grind
  | succ n ih => exact ⟨bbGo_step p hpf hps hp n ih.2, bbNode_step p hpn n ih.1⟩

/-! ## `bb_memo(h)`: the entry, between two clears -/

/-- After the walk: clear the memo again. -/
def clrK : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m₁) => if rdW (m₁.arr64 CTL) 24 + 2 = 0 then none else some (r, mclearG bmSch m₁)

/-- **The model of `bb_memo`.** -/
def bbMemoW (n : Nat) (m : Mem) (h : Word) : Option (Word × Mem) :=
  if rdW (m.arr64 CTL) 24 + 2 = 0 then none else clrK (bbW n (mclearG bmSch m) h)

theorem bbMemoW_eq (n : Nat) (m : Mem) (h : Word) (h0 : rdW (m.arr64 CTL) 24 + 2 ≠ 0) :
    bbMemoW n m h = clrK (bbW n (mclearG bmSch m) h) := by simp [bbMemoW, h0]

theorem clrK_some (r : Word) (m₁ : Mem) (h0 : rdW (m₁.arr64 CTL) 24 + 2 ≠ 0) :
    clrK (some (r, m₁)) = some (r, mclearG bmSch m₁) := by simp [clrK, h0]

grind_pattern [arena_grind] bbMemoW_eq => bbMemoW n m h
grind_pattern [arena_grind] clrK_some => clrK (some (r, m₁))

def bbMemo : FunDecl := lfn (h) locals (r, u) {
  u := call bm_clear();
  r := call bb_go(h);
  u := call bm_clear();
  return r
}

include hpf hps hp hpn in
theorem bbMemo_spec (hpc : p.lookup "bm_clear" = some (memoClearG bmSch))
    (hpm : p.lookup "bb_memo" = some bbMemo) (n : Nat) (s₀ : St) (h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "bb_memo" [h]
    ⦃fun r s' => LocEq s' s₀ ∧ bbMemoW n s₀.mem h = some (r.headD 0, s'.mem); ⊤⦄ := by
  have ih := (bbGo_spec p hpf hps hp hpn n).1
  unfold BbGoSpec at ih
  rw [invoke_eq _ hpm]
  simp only [callFn, bbMemo]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, memoClearG_spec bmSch p _ hpc n, ih] <;>
    finish

end go

/-- The walk and the memo, as one program. -/
def walkProg : Prog :=
  [("bm_find", memoFindG bmSch), ("bm_put", memoPutG bmSch), ("bm_clear", memoClearG bmSch),
    ("bb_go", bbGo), ("bb_node", bbNode), ("bb_memo", bbMemo)]

end L.Arena
