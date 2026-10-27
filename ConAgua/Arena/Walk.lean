module

public import ConAgua.Arena.MemoLib
public import ConAgua.Arena.ViewL
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Data.DTreeMap.Internal.Operations
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# The first recursive walk: the memoized loose-bvar bound

con-ron's `bvar_bound_go` (`arena/expr_ops.rs:1981`, Lean twin `bvarBoundGo`,
`Arena/ExprOps.lean:1404`) and its entry `bvar_bound_memo` (`:2054`, `bvarBoundMemo`): the exact
loose-bvar bound of an expression handle, memoized per node in `bvarBC`, recursive (not an
explicit work stack, as in con-ron). The checker calls it on the saturated branch of `bvarB`
(`looseBVarsBoundedFast`, `instantiate1Lift`'s cutoff).

`bb_go(h, c)`: `abort` at `c = 0` (the twin's depth counter `fuel` exhausted: it throws), else
probe the memo (`bm_find`, the memo library's `memoFindG bmSch`); on a hit return the
value. Otherwise `bb_node(h, c - 1)` (every child at the same `c - 1`, as the twin's `fuel + 1`
clause runs its arms at `fuel`) decodes the handle
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

then record the result (probe again, `bm_put`). `bb_memo(h, c)` is
`bm_clear(); r := bb_go(h, c); bm_clear()`.

The model `bbW n m h c` follows the code with L's fuel `n` (each call one level).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- Record the result `r` at `h` and return it. -/
def bbSet (m : Mem) (h r : Word) : Option (Word × Mem) :=
  match msetG bmSch m h 0 r with
  | none => none
  | some m' => some (r, m')

mutual
/-- **The model of `bb_go`** at L fuel `n`: the result and the memory after, `none` where the L
code aborts. -/
def bbW : Nat → Mem → Word → Word → Option (Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, h, c =>
    if c = 0 then none
    else if mfindG bmSch m h 0 = [] then none
    else if (mfindG bmSch m h 0).headD 0 ≠ 0 then
      some (rdW (m.arr64 BMEMO) ((mfindG bmSch m h 0).tail.headD 0 * 4 + 3), m)
    else
      match bbNodeW n m h (c - 1) with
      | none => none
      | some (r, m₁) => bbSet m₁ h r

/-- **The model of `bb_node`**: the view and the dispatch on the tag. -/
def bbNodeW : Nat → Mem → Word → Word → Option (Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, h, c =>
    if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if h >>> 28 = 0 then
      if tcnt m BVAR (tierW h) ≤ idxW h then none
      else if tfld m BVAR (tierW h) (idxW h) 0 + 1 = 0 then none
      else some (tfld m BVAR (tierW h) (idxW h) 0 + 1, m)
    else if h >>> 28 = 4 then
      if tcnt m APP (tierW h) ≤ idxW h then none
      else
        match bbW n m (tfld m APP (tierW h) (idxW h) 0) c with
        | none => none
        | some (x, m₁) =>
          match bbW n m₁ (tfld m APP (tierW h) (idxW h) 1) c with
          | none => none
          | some (y, m₂) => some (maxW x y, m₂)
    else if h >>> 28 = 5 then
      if tcnt m LAM (tierW h) ≤ idxW h then none
      else
        match bbW n m (tfld m LAM (tierW h) (idxW h) 0) c with
        | none => none
        | some (x, m₁) =>
          match bbW n m₁ (tfld m LAM (tierW h) (idxW h) 1) c with
          | none => none
          | some (y, m₂) => some (maxW x (predW y), m₂)
    else if h >>> 28 = 6 then
      if tcnt m FORALL (tierW h) ≤ idxW h then none
      else
        match bbW n m (tfld m FORALL (tierW h) (idxW h) 0) c with
        | none => none
        | some (x, m₁) =>
          match bbW n m₁ (tfld m FORALL (tierW h) (idxW h) 1) c with
          | none => none
          | some (y, m₂) => some (maxW x (predW y), m₂)
    else if h >>> 28 = 9 then
      if tcnt m PROJ (tierW h) ≤ idxW h then none
      else bbW n m (tfld m PROJ (tierW h) (idxW h) 2) c
    else if h >>> 28 = 7 then
      if tcnt m LET (tierW h) ≤ idxW h then none
      else
        match bbW n m (tfld m LET (tierW h) (idxW h) 0) c with
        | none => none
        | some (x, m₁) =>
          match bbW n m₁ (tfld m LET (tierW h) (idxW h) 1) c with
          | none => none
          | some (y, m₂) =>
            match bbW n m₂ (tfld m LET (tierW h) (idxW h) 2) c with
            | none => none
            | some (z, m₃) => some (maxW (maxW x y) (predW z), m₃)
    else if h >>> 28 = 1 then
      if tcnt m FVAR (tierW h) ≤ idxW h then none else some (0, m)
    else if h >>> 28 = 2 then
      if tcnt m SORT (tierW h) ≤ idxW h then none else some (0, m)
    else if h >>> 28 = 3 then
      if tcnt m CONST (tierW h) ≤ idxW h then none else some (0, m)
    else if h >>> 28 = 8 then
      if tcnt m LIT (tierW h) ≤ idxW h then none else some (0, m)
    else none
end

/-! ### The guarded equations, one per reachable arm

Each arm is an equation whose right side names the continuation (`bbK`, `bbAppK₁`, …): an equation
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
def bbAppK₁ (n : Nat) (c a : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => bbAppK₂ x (bbW n m₁ a c)
where bbAppK₂ (x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) => some (maxW x y, m₂)

/-- The binder arm (`lam`, `forallE`) after the type, and after the body. -/
def bbBindK₁ (n : Nat) (c b : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => bbBindK₂ x (bbW n m₁ b c)
where bbBindK₂ (x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) => some (maxW x (predW y), m₂)

/-- The `letE` arm after each child. -/
def bbLetK₁ (n : Nat) (c a b : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => bbLetK₂ x (bbW n m₁ a c)
where
  bbLetK₂ (x : Word) : Option (Word × Mem) → Option (Word × Mem)
    | none => none
    | some (y, m₂) => bbLetK₃ x y (bbW n m₂ b c)
  bbLetK₃ (x y : Word) : Option (Word × Mem) → Option (Word × Mem)
    | none => none
    | some (z, m₃) => some (maxW (maxW x y) (predW z), m₃)

section arms
variable (n : Nat) (m m₁ m₂ m₃ : Mem) (h r x y z f a b c : Word)

theorem bbK_some : bbK h (some (r, m₁)) = bbSet m₁ h r := rfl
theorem setK_some : setK r (some m₁) = some (r, m₁) := rfl
theorem bbAppK₁_some : bbAppK₁ n c a (some (x, m₁)) = bbAppK₁.bbAppK₂ x (bbW n m₁ a c) := rfl
theorem bbAppK₂_some : bbAppK₁.bbAppK₂ x (some (y, m₂)) = some (maxW x y, m₂) := rfl
theorem bbBindK₁_some : bbBindK₁ n c b (some (x, m₁)) = bbBindK₁.bbBindK₂ x (bbW n m₁ b c) := rfl
theorem bbBindK₂_some : bbBindK₁.bbBindK₂ x (some (y, m₂)) = some (maxW x (predW y), m₂) := rfl
theorem bbLetK₁_some : bbLetK₁ n c a b (some (x, m₁)) = bbLetK₁.bbLetK₂ n c b x (bbW n m₁ a c) := rfl
theorem bbLetK₂_some : bbLetK₁.bbLetK₂ n c b x (some (y, m₂)) = bbLetK₁.bbLetK₃ x y (bbW n m₂ b c) := rfl
theorem bbLetK₃_some :
    bbLetK₁.bbLetK₃ x y (some (z, m₃)) = some (maxW (maxW x y) (predW z), m₃) := rfl

theorem bbSet_eq : bbSet m h r = setK r (msetG bmSch m h 0 r) := by
  simp only [bbSet, setK]

theorem bbW_hit (hc : c ≠ 0) (hr : mfindG bmSch m h 0 ≠ []) (hh : (mfindG bmSch m h 0).headD 0 ≠ 0) :
    bbW (n + 1) m h c = some (rdW (m.arr64 BMEMO) ((mfindG bmSch m h 0).tail.headD 0 * 4 + 3), m) := by
  rw [bbW]; simp only [hc, hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]

theorem bbW_miss (hc : c ≠ 0) (hr : mfindG bmSch m h 0 ≠ []) (hh : (mfindG bmSch m h 0).headD 0 = 0) :
    bbW (n + 1) m h c = bbK h (bbNodeW n m h (c - 1)) := by
  rw [bbW]; simp only [hc, hr, hh, ↓reduceIte, ne_eq, not_true_eq_false, bbK]

theorem bbNodeW_bvar (hv : viewOK m h BVAR) (hg : h >>> 28 = 0)
    (h1 : tfld m BVAR (tierW h) (idxW h) 0 + 1 ≠ 0) :
    bbNodeW (n + 1) m h c = some (tfld m BVAR (tierW h) (idxW h) 0 + 1, m) := by
  rw [bbNodeW]; simp only [hv.1, hg, ↓reduceIte, h1]; simp [UInt64.not_le.mpr hv.2]

theorem bbNodeW_sort (hg : h >>> 28 = 2) (hv : viewOK m h SORT) : bbNodeW (n + 1) m h c = some (0, m) := by
  rw [bbNodeW]; simp [hv.1, hg, UInt64.not_le.mpr hv.2]

theorem bbNodeW_const (hg : h >>> 28 = 3) (hv : viewOK m h CONST) : bbNodeW (n + 1) m h c = some (0, m) := by
  rw [bbNodeW]; simp [hv.1, hg, UInt64.not_le.mpr hv.2]

theorem bbNodeW_fvar (hg : h >>> 28 = 1) (hv : viewOK m h FVAR) : bbNodeW (n + 1) m h c = some (0, m) := by
  rw [bbNodeW]; simp [hv.1, hg, UInt64.not_le.mpr hv.2]

theorem bbNodeW_lit (hg : h >>> 28 = 8) (hv : viewOK m h LIT) : bbNodeW (n + 1) m h c = some (0, m) := by
  rw [bbNodeW]; simp [hv.1, hg, UInt64.not_le.mpr hv.2]

theorem bbNodeW_app (hv : viewOK m h APP) (hg : h >>> 28 = 4) :
    bbNodeW (n + 1) m h c = bbAppK₁ n c (tfld m APP (tierW h) (idxW h) 1)
      (bbW n m (tfld m APP (tierW h) (idxW h) 0) c) := by
  rw [bbNodeW]; simp only [hv.1, hg, ↓reduceIte, UInt64.not_le.mpr hv.2, bbAppK₁, bbAppK₁.bbAppK₂]
  simp

theorem bbNodeW_lam (hv : viewOK m h LAM) (hg : h >>> 28 = 5) :
    bbNodeW (n + 1) m h c = bbBindK₁ n c (tfld m LAM (tierW h) (idxW h) 1)
      (bbW n m (tfld m LAM (tierW h) (idxW h) 0) c) := by
  rw [bbNodeW]; simp only [hv.1, hg, ↓reduceIte, UInt64.not_le.mpr hv.2, bbBindK₁, bbBindK₁.bbBindK₂]
  simp

theorem bbNodeW_forall (hv : viewOK m h FORALL) (hg : h >>> 28 = 6) :
    bbNodeW (n + 1) m h c = bbBindK₁ n c (tfld m FORALL (tierW h) (idxW h) 1)
      (bbW n m (tfld m FORALL (tierW h) (idxW h) 0) c) := by
  rw [bbNodeW]; simp only [hv.1, hg, ↓reduceIte, UInt64.not_le.mpr hv.2, bbBindK₁, bbBindK₁.bbBindK₂]
  simp

theorem bbNodeW_proj (hv : viewOK m h PROJ) (hg : h >>> 28 = 9) :
    bbNodeW (n + 1) m h c = bbW n m (tfld m PROJ (tierW h) (idxW h) 2) c := by
  rw [bbNodeW]; simp [hv.1, hg, UInt64.not_le.mpr hv.2]

theorem bbNodeW_let (hv : viewOK m h LET) (hg : h >>> 28 = 7) :
    bbNodeW (n + 1) m h c = bbLetK₁ n c (tfld m LET (tierW h) (idxW h) 1)
      (tfld m LET (tierW h) (idxW h) 2)
      (bbW n m (tfld m LET (tierW h) (idxW h) 0) c) := by
  rw [bbNodeW]; simp only [hv.1, hg, ↓reduceIte, UInt64.not_le.mpr hv.2, bbLetK₁, bbLetK₁.bbLetK₂,
    bbLetK₁.bbLetK₃]
  simp

end arms

attribute [arena_grind =] bbK_some setK_some bbAppK₁_some bbAppK₂_some bbBindK₁_some bbBindK₂_some
  bbLetK₁_some bbLetK₂_some bbLetK₃_some bbSet_eq
grind_pattern [arena_grind] bbW_hit => bbW (n + 1) m h c
grind_pattern [arena_grind] bbW_miss => bbW (n + 1) m h c
grind_pattern [arena_grind] bbNodeW_bvar => bbNodeW (n + 1) m h c
grind_pattern [arena_grind] bbNodeW_sort => bbNodeW (n + 1) m h c
grind_pattern [arena_grind] bbNodeW_const => bbNodeW (n + 1) m h c
grind_pattern [arena_grind] bbNodeW_lit => bbNodeW (n + 1) m h c
grind_pattern [arena_grind] bbNodeW_fvar => bbNodeW (n + 1) m h c
grind_pattern [arena_grind] bbNodeW_lam => bbNodeW (n + 1) m h c
grind_pattern [arena_grind] bbNodeW_forall => bbNodeW (n + 1) m h c
grind_pattern [arena_grind] bbNodeW_proj => bbNodeW (n + 1) m h c
grind_pattern [arena_grind] bbNodeW_app => bbNodeW (n + 1) m h c
grind_pattern [arena_grind] bbNodeW_let => bbNodeW (n + 1) m h c

/-- con-ron: ConRon/Arena/ExprOps.lean:1396-1421 ConRon.Arena.bvarBoundGo -/
@[l_impl ConRon.Arena.bvarBoundGo]
def bbGo : FunDecl := lfn (h, c) locals (fd, j, d, r, u) {
  if c == 0 { abort };
  (fd, j, d) := call bm_find(h, 0);
  if fd != 0 { return BMEMO.u64[j * 4 + 3] };
  r := call bb_node(h, c - 1);
  (fd, j, d) := call bm_find(h, 0);
  u := call bm_put(h, 0, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1396-1421 ConRon.Arena.bvarBoundGo -/
@[l_impl ConRon.Arena.bvarBoundGo]
def bbNode : FunDecl := lfn (h, c) locals (g, t, i, f, a, b, x, y, z) {
  g := h >> 28;
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if g == 0 {
    if BVAR⟨t⟩.count <= i { abort };
    x := BVAR⟨t, i⟩.i + 1;
    if x == 0 { abort };
    return x
  };
  if g == 4 {
    if APP⟨t⟩.count <= i { abort };
    f := APP⟨t, i⟩.f;
    a := APP⟨t, i⟩.a;
    x := call bb_go(f, c);
    y := call bb_go(a, c);
    return x + (y - x) * u64(x < y)
  };
  if g == 5 {
    if LAM⟨t⟩.count <= i { abort };
    f := LAM⟨t, i⟩.ty;
    a := LAM⟨t, i⟩.b;
    x := call bb_go(f, c);
    y := call bb_go(a, c);
    y := y - u64(0 < y);
    return x + (y - x) * u64(x < y)
  };
  if g == 6 {
    if FORALL⟨t⟩.count <= i { abort };
    f := FORALL⟨t, i⟩.ty;
    a := FORALL⟨t, i⟩.b;
    x := call bb_go(f, c);
    y := call bb_go(a, c);
    y := y - u64(0 < y);
    return x + (y - x) * u64(x < y)
  };
  if g == 9 {
    if PROJ⟨t⟩.count <= i { abort };
    f := PROJ⟨t, i⟩.e;
    x := call bb_go(f, c);
    return x
  };
  if g == 7 {
    if LET⟨t⟩.count <= i { abort };
    f := LET⟨t, i⟩.ty;
    a := LET⟨t, i⟩.v;
    b := LET⟨t, i⟩.b;
    x := call bb_go(f, c);
    y := call bb_go(a, c);
    z := call bb_go(b, c);
    x := x + (y - x) * u64(x < y);
    z := z - u64(0 < z);
    return x + (z - x) * u64(x < z)
  };
  if g == 1 { if FVAR⟨t⟩.count <= i { abort }; return 0 };
  if g == 2 { if SORT⟨t⟩.count <= i { abort }; return 0 };
  if g == 3 { if CONST⟨t⟩.count <= i { abort }; return 0 };
  if g == 8 { if LIT⟨t⟩.count <= i { abort }; return 0 };
  abort
}

section go
variable (p : Prog) (hpf : p.lookup "bm_find" = some (memoFindG bmSch))
  (hps : p.lookup "bm_put" = some (memoPutG bmSch)) (hp : p.lookup "bb_go" = some bbGo)
  (hpn : p.lookup "bb_node" = some bbNode)

/-- The spec of `bb_go` at fuel `n`. -/
def BbGoSpec (n : Nat) : Prop := ∀ (s₀ : St) (h c : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "bb_go" [h, c]
    ⦃fun r s' => LocEq s' s₀ ∧ bbW n s₀.mem h c = some (r.headD 0, s'.mem); ⊤⦄

/-- The spec of `bb_node` at fuel `n`. -/
def BbNodeSpec (n : Nat) : Prop := ∀ (s₀ : St) (h c : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "bb_node" [h, c]
    ⦃fun r s' => LocEq s' s₀ ∧ bbNodeW n s₀.mem h c = some (r.headD 0, s'.mem); ⊤⦄

include hpf hps hp in
theorem bbGo_step (n : Nat) (ih : BbNodeSpec p n) : BbGoSpec p (n + 1) := by
  unfold BbNodeSpec at ih
  intro s₀ h c
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
  intro s₀ h c
  rw [invoke_eq _ hpn]
  simp only [callFn, bbNode]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt,
      tcntM, evalE_tierE, evalE_idxE, ih] <;>
    finish [viewOK, tierW, idxW, maxW, predW]

include hpf hps hp hpn in
/-- **`bb_go` and `bb_node` are their models**, at every fuel: by induction on the fuel, the
recursive calls by the induction hypothesis. -/
theorem bbGo_spec (n : Nat) : BbGoSpec p n ∧ BbNodeSpec p n := by
  induction n with
  | zero =>
    constructor
    · intro s₀ h c; rw [invoke_eq _ hp]; simp only [callFn, bbGo]; vcgen [exec] <;> grind
    · intro s₀ h c; rw [invoke_eq _ hpn]; simp only [callFn, bbNode]; vcgen [exec] <;> grind
  | succ n ih => exact ⟨bbGo_step p hpf hps hp n ih.2, bbNode_step p hpn n ih.1⟩

/-! ## `bb_memo(h, c)`: the entry, between two clears -/

/-- After the walk: clear the memo again. -/
def clrK : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m₁) => if rdW (m₁.arr64 CTL) 24 + 2 = 0 then none else some (r, mclearG bmSch m₁)

/-- **The model of `bb_memo`.** -/
def bbMemoW (n : Nat) (m : Mem) (h c : Word) : Option (Word × Mem) :=
  if rdW (m.arr64 CTL) 24 + 2 = 0 then none else clrK (bbW n (mclearG bmSch m) h c)

theorem bbMemoW_eq (n : Nat) (m : Mem) (h c : Word) (h0 : rdW (m.arr64 CTL) 24 + 2 ≠ 0) :
    bbMemoW n m h c = clrK (bbW n (mclearG bmSch m) h c) := by simp [bbMemoW, h0]

theorem clrK_some (r : Word) (m₁ : Mem) (h0 : rdW (m₁.arr64 CTL) 24 + 2 ≠ 0) :
    clrK (some (r, m₁)) = some (r, mclearG bmSch m₁) := by simp [clrK, h0]

grind_pattern [arena_grind] bbMemoW_eq => bbMemoW n m h c
grind_pattern [arena_grind] clrK_some => clrK (some (r, m₁))

/-- con-ron: ConRon/Arena/ExprOps.lean:1473-1479 ConRon.Arena.bvarBoundMemo -/
@[l_impl ConRon.Arena.bvarBoundMemo]
def bbMemo : FunDecl := lfn (h, c) locals (r, u) {
  u := call bm_clear();
  r := call bb_go(h, c);
  u := call bm_clear();
  return r
}

include hpf hps hp hpn in
theorem bbMemo_spec (hpc : p.lookup "bm_clear" = some (memoClearG bmSch))
    (hpm : p.lookup "bb_memo" = some bbMemo) (n : Nat) (s₀ : St) (h c : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "bb_memo" [h, c]
    ⦃fun r s' => LocEq s' s₀ ∧ bbMemoW n s₀.mem h c = some (r.headD 0, s'.mem); ⊤⦄ := by
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
