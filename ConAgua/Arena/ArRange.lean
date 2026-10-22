module

public import ConAgua.Arena.Abs1Spec
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
import ConAgua.Census.Attr

@[expose] public section

/-!
# `abstractRange`: close `k` free variables at once, on `Abs1.lean`'s scaffolding

con-ron's executed `abstractRangeGo d k` (Lean twin `Arena/ExprOps.lean`, con-leche's
`abstractRangeC`) and its entry `abstractRangeFast`: replace `fvar i`, `d ≤ i < d + k`, by
`bvar (c + (d + k - 1 - i))`, the cursor `c` bumped under binders. It is `abstract1Go` with the
range `(d, k)` for the single `d` and the cursor `c` for `k`: the same cut-off (`ab_fvb`, `fvarB ≤
d`), the same memo `abs1C` keyed `(h, c)` (`Abs1.lean`; the two walks never nest, each entry clears
it), the same rebuild on change (`rbAppW` …). The new pieces: the `fvar` arm's range test, the
entry's `k = 0` identity, and two capacity checks the twin (over `Nat`) does not need: `d + k` and
`c + (d + k - 1 - i)` must not wrap.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

mutual
/-- **The model of `abs_go`** at L fuel `n`: the cut-off, then `ab_node`. -/
def arW : Nat → Mem → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, h, c, d, k =>
    match fvbW n m h with
    | none => none
    | some (x, m₁) => if x ≤ d then some (h, m₁) else arNodeW n m₁ h c d k

/-- **The model of `ab_node`**: the dispatch on the tag (the leaves and unknown tags return `h`
without reading the store; `fvar` inline). -/
def arNodeW : Nat → Mem → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, h, c, d, k =>
    if h >>> 28 = 4 then arAppW n m h c d k
    else if h >>> 28 = 5 then arLamW n m h c d k
    else if h >>> 28 = 6 then arForallW n m h c d k
    else if h >>> 28 = 1 then
      if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
      else if rdW (m.arr64 CTL) (26 + tierW h) ≤ idxW h then none
      else if d ≤ rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2) ∧ rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2) < d + k then
        if c + (d + k - 1 - rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2)) < c then none
        else binternW m (c + (d + k - 1 - rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2)))
      else some (h, m)
    else if h >>> 28 = 7 then arLetW n m h c d k
    else if h >>> 28 = 9 then arProjW n m h c d k
    else some (h, m)

/-- **The model of `abs_app`.** -/
def arAppW : Nat → Mem → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, h, c, d, k =>
    if mfindG abSch m h c = [] then none
    else if (mfindG abSch m h c).headD 0 ≠ 0 then
      some (rdW (m.arr64 ABMEMO) ((mfindG abSch m h c).tail.headD 0 * 4 + 3), m)
    else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if rdW (m.arr64 CTL) (4 + tierW h) ≤ idxW h then none
    else
      match arW n m (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2)) c d k with
      | none => none
      | some (x, m₁) =>
        match arW n m₁ (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2 + 1)) c d k with
        | none => none
        | some (y, m₂) =>
          asetK h c (rbAppW m₂ h (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2))
            (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2 + 1)) x y)

/-- **The model of `abs_lam`.** -/
def arLamW : Nat → Mem → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, h, c, d, k =>
    if c + 1 = 0 then none
    else if mfindG abSch m h c = [] then none
    else if (mfindG abSch m h c).headD 0 ≠ 0 then
      some (rdW (m.arr64 ABMEMO) ((mfindG abSch m h c).tail.headD 0 * 4 + 3), m)
    else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if rdW (m.arr64 CTL) (28 + tierW h) ≤ idxW h then none
    else
      match arW n m (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2)) c d k with
      | none => none
      | some (x, m₁) =>
        match arW n m₁ (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2 + 1)) (c + 1) d k with
        | none => none
        | some (y, m₂) =>
          asetK h c (rbLamW m₂ h (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2))
            (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2 + 1)) x y)

/-- **The model of `abs_forall`.** -/
def arForallW : Nat → Mem → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, h, c, d, k =>
    if c + 1 = 0 then none
    else if mfindG abSch m h c = [] then none
    else if (mfindG abSch m h c).headD 0 ≠ 0 then
      some (rdW (m.arr64 ABMEMO) ((mfindG abSch m h c).tail.headD 0 * 4 + 3), m)
    else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if rdW (m.arr64 CTL) (30 + tierW h) ≤ idxW h then none
    else
      match arW n m (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2)) c d k with
      | none => none
      | some (x, m₁) =>
        match arW n m₁ (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2 + 1)) (c + 1) d k with
        | none => none
        | some (y, m₂) =>
          asetK h c (rbForallW m₂ h (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2))
            (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2 + 1)) x y)

/-- **The model of `abs_let`.** -/
def arLetW : Nat → Mem → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, h, c, d, k =>
    if c + 1 = 0 then none
    else if mfindG abSch m h c = [] then none
    else if (mfindG abSch m h c).headD 0 ≠ 0 then
      some (rdW (m.arr64 ABMEMO) ((mfindG abSch m h c).tail.headD 0 * 4 + 3), m)
    else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if rdW (m.arr64 CTL) (20 + tierW h) ≤ idxW h then none
    else
      match arW n m (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3)) c d k with
      | none => none
      | some (x, m₁) =>
        match arW n m₁ (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 1)) c d k with
        | none => none
        | some (y, m₂) =>
          match arW n m₂ (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 2)) (c + 1) d k with
          | none => none
          | some (z, m₃) =>
            asetK h c (rbLetW m₃ h (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3))
              (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 1))
              (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 2)) x y z)

/-- **The model of `abs_proj`.** -/
def arProjW : Nat → Mem → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, h, c, d, k =>
    if mfindG abSch m h c = [] then none
    else if (mfindG abSch m h c).headD 0 ≠ 0 then
      some (rdW (m.arr64 ABMEMO) ((mfindG abSch m h c).tail.headD 0 * 4 + 3), m)
    else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if rdW (m.arr64 CTL) (32 + tierW h) ≤ idxW h then none
    else
      match arW n m (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 2)) c d k with
      | none => none
      | some (x, m₁) =>
        asetK h c (rbProjW m₁ h (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3))
          (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 1))
          (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 2)) x)
end


/-! ### Continuations and guarded equations -/

/-- After the cut-off. -/
def rcutK (n : Nat) (h c d k : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => if x ≤ d then some (h, m₁) else arNodeW n m₁ h c d k

/-- The arms after each child. -/
def rappK₁ (n : Nat) (h c d k fw aw : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => rappK₂ h c fw aw x (arW n m₁ aw c d k)
where rappK₂ (h c fw aw x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) => asetK h c (rbAppW m₂ h fw aw x y)

def rlamK₁ (n : Nat) (h c d k fw bw : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => rlamK₂ h c fw bw x (arW n m₁ bw (c + 1) d k)
where rlamK₂ (h c fw bw x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) => asetK h c (rbLamW m₂ h fw bw x y)

def rfaK₁ (n : Nat) (h c d k fw bw : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => rfaK₂ h c fw bw x (arW n m₁ bw (c + 1) d k)
where rfaK₂ (h c fw bw x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) => asetK h c (rbForallW m₂ h fw bw x y)

def rleK₁ (n : Nat) (h c d k fw vw bw : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => rleK₂ n h c d k fw vw bw x (arW n m₁ vw c d k)
where
  rleK₂ (n : Nat) (h c d k fw vw bw x : Word) : Option (Word × Mem) → Option (Word × Mem)
    | none => none
    | some (y, m₂) => rleK₃ h c fw vw bw x y (arW n m₂ bw (c + 1) d k)
  rleK₃ (h c fw vw bw x y : Word) : Option (Word × Mem) → Option (Word × Mem)
    | none => none
    | some (z, m₃) => asetK h c (rbLetW m₃ h fw vw bw x y z)

def rpjK₁ (h c nw iw ew : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => asetK h c (rbProjW m₁ h nw iw ew x)


section aks
variable (n : Nat) (h c d k fw aw bw vw nw iw ew x y z : Word) (m₁ m₂ m₃ : Mem)
theorem rcutK_some : rcutK n h c d k (some (x, m₁)) =
    if x ≤ d then some (h, m₁) else arNodeW n m₁ h c d k := rfl
theorem rappK₁_some : rappK₁ n h c d k fw aw (some (x, m₁)) =
    rappK₁.rappK₂ h c fw aw x (arW n m₁ aw c d k) := rfl
theorem rappK₂_some : rappK₁.rappK₂ h c fw aw x (some (y, m₂)) = asetK h c (rbAppW m₂ h fw aw x y) :=
  rfl
theorem rlamK₁_some : rlamK₁ n h c d k fw bw (some (x, m₁)) =
    rlamK₁.rlamK₂ h c fw bw x (arW n m₁ bw (c + 1) d k) := rfl
theorem rlamK₂_some : rlamK₁.rlamK₂ h c fw bw x (some (y, m₂)) = asetK h c (rbLamW m₂ h fw bw x y) :=
  rfl
theorem rfaK₁_some : rfaK₁ n h c d k fw bw (some (x, m₁)) =
    rfaK₁.rfaK₂ h c fw bw x (arW n m₁ bw (c + 1) d k) := rfl
theorem rfaK₂_some : rfaK₁.rfaK₂ h c fw bw x (some (y, m₂)) =
    asetK h c (rbForallW m₂ h fw bw x y) := rfl
theorem rleK₁_some : rleK₁ n h c d k fw vw bw (some (x, m₁)) =
    rleK₁.rleK₂ n h c d k fw vw bw x (arW n m₁ vw c d k) := rfl
theorem rleK₂_some : rleK₁.rleK₂ n h c d k fw vw bw x (some (y, m₂)) =
    rleK₁.rleK₃ h c fw vw bw x y (arW n m₂ bw (c + 1) d k) := rfl
theorem rleK₃_some : rleK₁.rleK₃ h c fw vw bw x y (some (z, m₃)) =
    asetK h c (rbLetW m₃ h fw vw bw x y z) := rfl
theorem rpjK₁_some : rpjK₁ h c nw iw ew (some (x, m₁)) = asetK h c (rbProjW m₁ h nw iw ew x) := rfl
end aks

attribute [arena_grind =] rcutK_some rappK₁_some rappK₂_some rlamK₁_some rlamK₂_some rfaK₁_some
  rfaK₂_some rleK₁_some rleK₂_some rleK₃_some rpjK₁_some

section arms
variable (n : Nat) (m : Mem) (h c d k : Word)

theorem arW_eq : arW (n + 1) m h c d k = rcutK n h c d k (fvbW n m h) := by
  rw [arW]; cases fvbW n m h <;> rfl

theorem arNodeW_app (hg : h >>> 28 = 4) : arNodeW (n + 1) m h c d k = arAppW n m h c d k := by
  rw [arNodeW]; simp [hg]

theorem arNodeW_lam (hg : h >>> 28 = 5) : arNodeW (n + 1) m h c d k = arLamW n m h c d k := by
  rw [arNodeW]; simp [hg]

theorem arNodeW_forall (hg : h >>> 28 = 6) : arNodeW (n + 1) m h c d k = arForallW n m h c d k := by
  rw [arNodeW]; simp [hg]

theorem arNodeW_let (hg : h >>> 28 = 7) : arNodeW (n + 1) m h c d k = arLetW n m h c d k := by
  rw [arNodeW]; simp [hg]

theorem arNodeW_proj (hg : h >>> 28 = 9) : arNodeW (n + 1) m h c d k = arProjW n m h c d k := by
  rw [arNodeW]; simp [hg]

theorem arNodeW_fvar_in (hv : viewOK m h 26) (hg : h >>> 28 = 1)
    (hi : d ≤ rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2) ∧ rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2) < d + k)
    (ho : ¬ c + (d + k - 1 - rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2)) < c) :
    arNodeW (n + 1) m h c d k = binternW m (c + (d + k - 1 - rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2))) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [arNodeW]; simp only [hv1, hg, ↓reduceIte, UInt64.not_le.mpr hv2, hi, ho]; simp

theorem arNodeW_fvar_out (hv : viewOK m h 26) (hg : h >>> 28 = 1)
    (hi : ¬ (d ≤ rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2) ∧ rdW (m.arr64 FVREC) (idxW h * 4 + tierW h * 2) < d + k)) :
    arNodeW (n + 1) m h c d k = some (h, m) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [arNodeW]; simp only [hv1, hg, ↓reduceIte, UInt64.not_le.mpr hv2, hi]; simp

theorem arNodeW_leaf (h1 : h >>> 28 ≠ 1)
    (h4 : h >>> 28 ≠ 4) (h5 : h >>> 28 ≠ 5) (h6 : h >>> 28 ≠ 6) (h7 : h >>> 28 ≠ 7)
    (h9 : h >>> 28 ≠ 9) : arNodeW (n + 1) m h c d k = some (h, m) := by
  rw [arNodeW]; simp [h1, h4, h5, h6, h7, h9]

theorem arAppW_hit (hr : mfindG abSch m h c ≠ []) (hh : (mfindG abSch m h c).headD 0 ≠ 0) :
    arAppW (n + 1) m h c d k =
      some (rdW (m.arr64 ABMEMO) ((mfindG abSch m h c).tail.headD 0 * 4 + 3), m) := by
  rw [arAppW]; simp only [hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]

theorem arAppW_miss (hr : mfindG abSch m h c ≠ []) (hh : (mfindG abSch m h c).headD 0 = 0)
    (hvk : viewOK m h 4) :
    arAppW (n + 1) m h c d k =
      rappK₁ n h c d k (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2))
        (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2 + 1))
        (arW n m (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2)) c d k) := by
  rw [arAppW]; simp only [hr, hh, ↓reduceIte, ne_eq, not_true_eq_false, hvk.1, ↓reduceIte, UInt64.not_le.mpr hvk.2]
  cases arW n m (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2)) c d k <;> rfl

theorem arLamW_hit (h1 : c + 1 ≠ 0) (hr : mfindG abSch m h c ≠ [])
    (hh : (mfindG abSch m h c).headD 0 ≠ 0) :
    arLamW (n + 1) m h c d k =
      some (rdW (m.arr64 ABMEMO) ((mfindG abSch m h c).tail.headD 0 * 4 + 3), m) := by
  rw [arLamW]; simp only [h1, hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]

theorem arLamW_miss (h1 : c + 1 ≠ 0) (hr : mfindG abSch m h c ≠ [])
    (hh : (mfindG abSch m h c).headD 0 = 0) (hvk : viewOK m h 28) :
    arLamW (n + 1) m h c d k =
      rlamK₁ n h c d k (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2))
        (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2 + 1))
        (arW n m (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2)) c d k) := by
  rw [arLamW]; simp only [h1, hr, hh, ↓reduceIte, ne_eq, not_true_eq_false, hvk.1, ↓reduceIte, UInt64.not_le.mpr hvk.2]
  cases arW n m (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2)) c d k <;> rfl

theorem arForallW_hit (h1 : c + 1 ≠ 0) (hr : mfindG abSch m h c ≠ [])
    (hh : (mfindG abSch m h c).headD 0 ≠ 0) :
    arForallW (n + 1) m h c d k =
      some (rdW (m.arr64 ABMEMO) ((mfindG abSch m h c).tail.headD 0 * 4 + 3), m) := by
  rw [arForallW]; simp only [h1, hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]

theorem arForallW_miss (h1 : c + 1 ≠ 0) (hr : mfindG abSch m h c ≠ [])
    (hh : (mfindG abSch m h c).headD 0 = 0) (hvk : viewOK m h 30) :
    arForallW (n + 1) m h c d k =
      rfaK₁ n h c d k (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2))
        (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2 + 1))
        (arW n m (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2)) c d k) := by
  rw [arForallW]; simp only [h1, hr, hh, ↓reduceIte, ne_eq, not_true_eq_false, hvk.1, ↓reduceIte, UInt64.not_le.mpr hvk.2]
  cases arW n m (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2)) c d k <;> rfl

theorem arLetW_hit (h1 : c + 1 ≠ 0) (hr : mfindG abSch m h c ≠ [])
    (hh : (mfindG abSch m h c).headD 0 ≠ 0) :
    arLetW (n + 1) m h c d k =
      some (rdW (m.arr64 ABMEMO) ((mfindG abSch m h c).tail.headD 0 * 4 + 3), m) := by
  rw [arLetW]; simp only [h1, hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]

theorem arLetW_miss (h1 : c + 1 ≠ 0) (hr : mfindG abSch m h c ≠ [])
    (hh : (mfindG abSch m h c).headD 0 = 0) (hvk : viewOK m h 20) :
    arLetW (n + 1) m h c d k =
      rleK₁ n h c d k (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3))
        (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 1))
        (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 2))
        (arW n m (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3)) c d k) := by
  rw [arLetW]; simp only [h1, hr, hh, ↓reduceIte, ne_eq, not_true_eq_false, hvk.1, ↓reduceIte, UInt64.not_le.mpr hvk.2]
  cases arW n m (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3)) c d k with
  | none => rfl
  | some p =>
    obtain ⟨x, m₁⟩ := p
    cases arW n m₁ (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 1)) c d k <;> rfl

theorem arProjW_hit (hr : mfindG abSch m h c ≠ []) (hh : (mfindG abSch m h c).headD 0 ≠ 0) :
    arProjW (n + 1) m h c d k =
      some (rdW (m.arr64 ABMEMO) ((mfindG abSch m h c).tail.headD 0 * 4 + 3), m) := by
  rw [arProjW]; simp only [hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]

theorem arProjW_miss (hr : mfindG abSch m h c ≠ []) (hh : (mfindG abSch m h c).headD 0 = 0)
    (hvk : viewOK m h 32) :
    arProjW (n + 1) m h c d k =
      rpjK₁ h c (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3))
        (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 1))
        (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 2))
        (arW n m (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 2)) c d k) := by
  rw [arProjW]; simp only [hr, hh, ↓reduceIte, ne_eq, not_true_eq_false, hvk.1, ↓reduceIte, UInt64.not_le.mpr hvk.2]
  cases arW n m (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 2)) c d k <;> rfl

end arms

grind_pattern [arena_grind] arW_eq => arW (n + 1) m h c d k
grind_pattern [arena_grind] arNodeW_app => arNodeW (n + 1) m h c d k
grind_pattern [arena_grind] arNodeW_lam => arNodeW (n + 1) m h c d k
grind_pattern [arena_grind] arNodeW_forall => arNodeW (n + 1) m h c d k
grind_pattern [arena_grind] arNodeW_let => arNodeW (n + 1) m h c d k
grind_pattern [arena_grind] arNodeW_proj => arNodeW (n + 1) m h c d k
grind_pattern [arena_grind] arNodeW_fvar_in => arNodeW (n + 1) m h c d k
grind_pattern [arena_grind] arNodeW_fvar_out => arNodeW (n + 1) m h c d k
grind_pattern [arena_grind] arNodeW_leaf => arNodeW (n + 1) m h c d k
grind_pattern [arena_grind] arAppW_hit => arAppW (n + 1) m h c d k
grind_pattern [arena_grind] arAppW_miss => arAppW (n + 1) m h c d k
grind_pattern [arena_grind] arLamW_hit => arLamW (n + 1) m h c d k
grind_pattern [arena_grind] arLamW_miss => arLamW (n + 1) m h c d k
grind_pattern [arena_grind] arForallW_hit => arForallW (n + 1) m h c d k
grind_pattern [arena_grind] arForallW_miss => arForallW (n + 1) m h c d k
grind_pattern [arena_grind] arLetW_hit => arLetW (n + 1) m h c d k
grind_pattern [arena_grind] arLetW_miss => arLetW (n + 1) m h c d k
grind_pattern [arena_grind] arProjW_hit => arProjW (n + 1) m h c d k
grind_pattern [arena_grind] arProjW_miss => arProjW (n + 1) m h c d k

/-- con-ron: ConRon/Arena/ExprOps.lean:1758-1779 ConRon.Arena.abstractRangeGo -/
@[l_impl ConRon.Arena.abstractRangeGo]
def arGo : FunDecl := lfn (h, c, d, k) locals (x, r) {
  x := call ab_fvb(h);
  if x <= d { return h };
  r := call ar_node(h, c, d, k);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1758-1779 ConRon.Arena.abstractRangeGo
con-ron: ConRon/Arena/ExprOps.lean:1747-1754 ConRon.Arena.absRangeArmFVar -/
@[l_impl ConRon.Arena.absRangeArmFVar]
def arNode : FunDecl := lfn (h, c, d, k) locals (x, g, t, i, v, r) {
  g := h >> 28;
  if g == 4 { r := call ar_app(h, c, d, k); return r };
  if g == 5 { r := call ar_lam(h, c, d, k); return r };
  if g == 6 { r := call ar_forall(h, c, d, k); return r };
  if g == 1 {
    t := (h >> 27) & 1;
    i := h & 134217727;
    if t != 0 && CTL.u64[1] == 0 { abort };
    if CTL.u64[26 + t] <= i { abort };
    x := FVREC.u64[i * 4 + t * 2];
    if d <= x && x < d + k {
      v := c + (d + k - 1 - x);
      if v < c { abort };
      r := call intern_bvar(v);
      return r
    };
    return h
  };
  if g == 7 { r := call ar_let(h, c, d, k); return r };
  if g == 9 { r := call ar_proj(h, c, d, k); return r };
  return h
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1781-1796 ConRon.Arena.absRangeGoArmApp -/
@[l_impl ConRon.Arena.absRangeGoArmApp]
def arApp : FunDecl := lfn (h, c, d, k) locals (fd, j, e0, t, i, f, a, x, y, r, u) {
  (fd, j, e0) := call ab_find(h, c);
  if fd != 0 { return ABMEMO.u64[j * 4 + 3] };
  t := (h >> 27) & 1;
  i := h & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[4 + t] <= i { abort };
  f := AREC.u64[i * 4 + t * 2];
  a := AREC.u64[i * 4 + t * 2 + 1];
  x := call ar_go(f, c, d, k);
  y := call ar_go(a, c, d, k);
  if x == f && y == a { r := h } else { r := call mk_app(x, y) };
  (fd, j, e0) := call ab_find(h, c);
  u := call ab_put(h, c, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1798-1813 ConRon.Arena.absRangeGoArmBind -/
@[l_impl ConRon.Arena.absRangeGoArmBind]
def arLam : FunDecl := lfn (h, c, d, k) locals (fd, j, e0, t, i, f, a, x, y, r, u) {
  if c + 1 == 0 { abort };
  (fd, j, e0) := call ab_find(h, c);
  if fd != 0 { return ABMEMO.u64[j * 4 + 3] };
  t := (h >> 27) & 1;
  i := h & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[28 + t] <= i { abort };
  f := LAREC.u64[i * 4 + t * 2];
  a := LAREC.u64[i * 4 + t * 2 + 1];
  x := call ar_go(f, c, d, k);
  y := call ar_go(a, c + 1, d, k);
  if x == f && y == a { r := h } else { r := call mk_lam(x, y) };
  (fd, j, e0) := call ab_find(h, c);
  u := call ab_put(h, c, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1798-1813 ConRon.Arena.absRangeGoArmBind -/
@[l_impl ConRon.Arena.absRangeGoArmBind]
def arForall : FunDecl := lfn (h, c, d, k) locals (fd, j, e0, t, i, f, a, x, y, r, u) {
  if c + 1 == 0 { abort };
  (fd, j, e0) := call ab_find(h, c);
  if fd != 0 { return ABMEMO.u64[j * 4 + 3] };
  t := (h >> 27) & 1;
  i := h & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[30 + t] <= i { abort };
  f := FAREC.u64[i * 4 + t * 2];
  a := FAREC.u64[i * 4 + t * 2 + 1];
  x := call ar_go(f, c, d, k);
  y := call ar_go(a, c + 1, d, k);
  if x == f && y == a { r := h } else { r := call mk_forall(x, y) };
  (fd, j, e0) := call ab_find(h, c);
  u := call ab_put(h, c, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1815-1831 ConRon.Arena.absRangeGoArmLet -/
@[l_impl ConRon.Arena.absRangeGoArmLet]
def arLet : FunDecl := lfn (h, c, d, k) locals (fd, j, e0, t, i, f, a, b, x, y, z, r, u) {
  if c + 1 == 0 { abort };
  (fd, j, e0) := call ab_find(h, c);
  if fd != 0 { return ABMEMO.u64[j * 4 + 3] };
  t := (h >> 27) & 1;
  i := h & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[20 + t] <= i { abort };
  f := LEREC.u64[i * 6 + t * 3];
  a := LEREC.u64[i * 6 + t * 3 + 1];
  b := LEREC.u64[i * 6 + t * 3 + 2];
  x := call ar_go(f, c, d, k);
  y := call ar_go(a, c, d, k);
  z := call ar_go(b, c + 1, d, k);
  if x == f && y == a && z == b { r := h } else { r := call mk_let(x, y, z) };
  (fd, j, e0) := call ab_find(h, c);
  u := call ab_put(h, c, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1833-1847 ConRon.Arena.absRangeGoArmProj -/
@[l_impl ConRon.Arena.absRangeGoArmProj]
def arProj : FunDecl := lfn (h, c, d, k) locals (fd, j, e0, t, i, nm, ix, e, x, r, u) {
  (fd, j, e0) := call ab_find(h, c);
  if fd != 0 { return ABMEMO.u64[j * 4 + 3] };
  t := (h >> 27) & 1;
  i := h & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[32 + t] <= i { abort };
  nm := PJREC.u64[i * 6 + t * 3];
  ix := PJREC.u64[i * 6 + t * 3 + 1];
  e := PJREC.u64[i * 6 + t * 3 + 2];
  x := call ar_go(e, c, d, k);
  if x == e { r := h } else { r := call mk_proj(nm, ix, x) };
  (fd, j, e0) := call ab_find(h, c);
  u := call ab_put(h, c, r, fd, j);
  return r
}



/-! ## The program and its specs -/

/-- What the specs need of the program. -/
structure ArProg (p : Prog) : Prop where
  base : AbsProg p
  go : p.lookup "ar_go" = some arGo
  node : p.lookup "ar_node" = some arNode
  app : p.lookup "ar_app" = some arApp
  lam : p.lookup "ar_lam" = some arLam
  fa : p.lookup "ar_forall" = some arForall
  le : p.lookup "ar_let" = some arLet
  pj : p.lookup "ar_proj" = some arProj

section specs
variable (p : Prog) (hp : ArProg p)

/-- The spec of `abs_go` at fuel `n`. -/
def ArGoSpec (n : Nat) : Prop := ∀ (s₀ : St) (h c d k : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "ar_go" [h, c, d, k]
    ⦃fun r s' => LocEq s' s₀ ∧ arW n s₀.mem h c d k = some (r.headD 0, s'.mem); ⊤⦄

/-- The spec of `ab_node` at fuel `n`. -/
def ArNodeSpec (n : Nat) : Prop := ∀ (s₀ : St) (h c d k : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "ar_node" [h, c, d, k]
    ⦃fun r s' => LocEq s' s₀ ∧ arNodeW n s₀.mem h c d k = some (r.headD 0, s'.mem); ⊤⦄

/-- The specs of the five arms at fuel `n`. -/
def ArArmSpec (n : Nat) : Prop := ∀ (s₀ : St) (h c d k : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ar_app" [h, c, d, k]
    ⦃fun r s' => LocEq s' s₀ ∧ arAppW n s₀.mem h c d k = some (r.headD 0, s'.mem); ⊤⦄ ∧
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ar_lam" [h, c, d, k]
    ⦃fun r s' => LocEq s' s₀ ∧ arLamW n s₀.mem h c d k = some (r.headD 0, s'.mem); ⊤⦄ ∧
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ar_forall" [h, c, d, k]
    ⦃fun r s' => LocEq s' s₀ ∧ arForallW n s₀.mem h c d k = some (r.headD 0, s'.mem); ⊤⦄ ∧
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ar_let" [h, c, d, k]
    ⦃fun r s' => LocEq s' s₀ ∧ arLetW n s₀.mem h c d k = some (r.headD 0, s'.mem); ⊤⦄ ∧
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ar_proj" [h, c, d, k]
    ⦃fun r s' => LocEq s' s₀ ∧ arProjW n s₀.mem h c d k = some (r.headD 0, s'.mem); ⊤⦄

include hp in
theorem arGo_step (n : Nat) (ih : ArNodeSpec p n) : ArGoSpec p (n + 1) := by
  unfold ArNodeSpec at ih
  intro s₀ h c d k
  rw [invoke_eq _ hp.go]
  simp only [callFn, arGo]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, abFvb_spec p hp.base n, ih] <;>
    finish

include hp in
theorem arNode_step (n : Nat) (ih : ArArmSpec p n) : ArNodeSpec p (n + 1) := by
  intro s₀ h c d k
  have ihA := fun s h c d k => (ih s h c d k).1
  have ihL := fun s h c d k => (ih s h c d k).2.1
  have ihF := fun s h c d k => (ih s h c d k).2.2.1
  have ihE := fun s h c d k => (ih s h c d k).2.2.2.1
  have ihP := fun s h c d k => (ih s h c d k).2.2.2.2
  rw [invoke_eq _ hp.node]
  simp only [callFn, arNode]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      internBVar_spec p hp.base.base.bvf hp.base.base.bvp hp.base.base.bvi n, ihA, ihL, ihF, ihE, ihP] <;>
    finish [viewOK, tierW, idxW]

end specs

end L.Arena
