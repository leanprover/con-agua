module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
import ConAgua.Census.Attr
public import ConAgua.Arena.Abs1
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# `abstractRange`: close `k` free variables at once, on `Abs1.lean`'s scaffolding

con-ron's executed `abstractRangeGo d k` (Lean twin `Arena/ExprOps.lean`, con-leche's
`abstractRangeC`) and its entry `abstractRangeFast`: replace `fvar i`, `d ≤ i < d + k`, by
`bvar (c + (d + k - 1 - i))`, the cursor `c` bumped under binders. It is `abstract1Go` with the
range `(d, k)` for the single `d` and the cursor `c` for `k`: the same cut-off (`ab_fvb`, `fvarB ≤
d`), the same memo `abs1C` keyed `(h, c)` (`Abs1.lean`; the two walks never nest, each entry clears
it), the same rebuild on change (`rbAppW` …). The new pieces: the `fvar` arm's range test, the
entry's `k = 0` identity, and two capacity checks in the `fvar` arm the twin (over `Nat`) does not
need: `d + k` and `c + (d + k - 1 - i)` must not wrap. The depth counter `fu` (last argument) is
`Abs1.lean`'s: the twin's `fuel` exactly, `abort` at `0`, `ab_fvb(h, fu - 1)` and
the arms at `fu - 1`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

mutual
/-- **The model of `abs_go`** at L fuel `n`: the cut-off, then `ab_node`. -/
def arW : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, h, c, d, k, fu =>
    if fu = 0 then none
    else match fvbW n m h (fu - 1) with
    | none => none
    | some (x, m₁) => if x ≤ d then some (h, m₁) else arNodeW n m₁ h c d k (fu - 1)

/-- **The model of `ab_node`**: the dispatch on the tag (the leaves and unknown tags return `h`
without reading the store; `fvar` inline). -/
def arNodeW : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, h, c, d, k, fu =>
    if h >>> 28 = 4 then arAppW n m h c d k fu
    else if h >>> 28 = 5 then arLamW n m h c d k fu
    else if h >>> 28 = 6 then arForallW n m h c d k fu
    else if h >>> 28 = 1 then
      if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
      else if tcnt m FVAR (tierW h) ≤ idxW h then none
      else if d + k < d then none
      else if d ≤ tfld m FVAR (tierW h) (idxW h) 0 ∧ tfld m FVAR (tierW h) (idxW h) 0 < d + k then
        if c + (d + k - 1 - tfld m FVAR (tierW h) (idxW h) 0) < c then none
        else binternW m (c + (d + k - 1 - tfld m FVAR (tierW h) (idxW h) 0))
      else some (h, m)
    else if h >>> 28 = 7 then arLetW n m h c d k fu
    else if h >>> 28 = 9 then arProjW n m h c d k fu
    else some (h, m)

/-- **The model of `abs_app`.** -/
def arAppW : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, h, c, d, k, fu =>
    if mfindG abSch m h c = [] then none
    else if (mfindG abSch m h c).headD 0 ≠ 0 then
      some (rdW (m.arr64 ABMEMO) ((mfindG abSch m h c).tail.headD 0 * 4 + 3), m)
    else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if tcnt m APP (tierW h) ≤ idxW h then none
    else
      match arW n m (tfld m APP (tierW h) (idxW h) 0) c d k fu with
      | none => none
      | some (x, m₁) =>
        match arW n m₁ (tfld m APP (tierW h) (idxW h) 1) c d k fu with
        | none => none
        | some (y, m₂) =>
          asetK h c (rbAppW m₂ h (tfld m APP (tierW h) (idxW h) 0)
            (tfld m APP (tierW h) (idxW h) 1) x y)

/-- **The model of `abs_lam`.** -/
def arLamW : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, h, c, d, k, fu =>
    if c + 1 = 0 then none
    else if mfindG abSch m h c = [] then none
    else if (mfindG abSch m h c).headD 0 ≠ 0 then
      some (rdW (m.arr64 ABMEMO) ((mfindG abSch m h c).tail.headD 0 * 4 + 3), m)
    else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if tcnt m LAM (tierW h) ≤ idxW h then none
    else
      match arW n m (tfld m LAM (tierW h) (idxW h) 0) c d k fu with
      | none => none
      | some (x, m₁) =>
        match arW n m₁ (tfld m LAM (tierW h) (idxW h) 1) (c + 1) d k fu with
        | none => none
        | some (y, m₂) =>
          asetK h c (rbLamW m₂ h (tfld m LAM (tierW h) (idxW h) 0)
            (tfld m LAM (tierW h) (idxW h) 1) x y)

/-- **The model of `abs_forall`.** -/
def arForallW : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, h, c, d, k, fu =>
    if c + 1 = 0 then none
    else if mfindG abSch m h c = [] then none
    else if (mfindG abSch m h c).headD 0 ≠ 0 then
      some (rdW (m.arr64 ABMEMO) ((mfindG abSch m h c).tail.headD 0 * 4 + 3), m)
    else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if tcnt m FORALL (tierW h) ≤ idxW h then none
    else
      match arW n m (tfld m FORALL (tierW h) (idxW h) 0) c d k fu with
      | none => none
      | some (x, m₁) =>
        match arW n m₁ (tfld m FORALL (tierW h) (idxW h) 1) (c + 1) d k fu with
        | none => none
        | some (y, m₂) =>
          asetK h c (rbForallW m₂ h (tfld m FORALL (tierW h) (idxW h) 0)
            (tfld m FORALL (tierW h) (idxW h) 1) x y)

/-- **The model of `abs_let`.** -/
def arLetW : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, h, c, d, k, fu =>
    if c + 1 = 0 then none
    else if mfindG abSch m h c = [] then none
    else if (mfindG abSch m h c).headD 0 ≠ 0 then
      some (rdW (m.arr64 ABMEMO) ((mfindG abSch m h c).tail.headD 0 * 4 + 3), m)
    else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if tcnt m LET (tierW h) ≤ idxW h then none
    else
      match arW n m (tfld m LET (tierW h) (idxW h) 0) c d k fu with
      | none => none
      | some (x, m₁) =>
        match arW n m₁ (tfld m LET (tierW h) (idxW h) 1) c d k fu with
        | none => none
        | some (y, m₂) =>
          match arW n m₂ (tfld m LET (tierW h) (idxW h) 2) (c + 1) d k fu with
          | none => none
          | some (z, m₃) =>
            asetK h c (rbLetW m₃ h (tfld m LET (tierW h) (idxW h) 0)
              (tfld m LET (tierW h) (idxW h) 1)
              (tfld m LET (tierW h) (idxW h) 2) x y z)

/-- **The model of `abs_proj`.** -/
def arProjW : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, h, c, d, k, fu =>
    if mfindG abSch m h c = [] then none
    else if (mfindG abSch m h c).headD 0 ≠ 0 then
      some (rdW (m.arr64 ABMEMO) ((mfindG abSch m h c).tail.headD 0 * 4 + 3), m)
    else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if tcnt m PROJ (tierW h) ≤ idxW h then none
    else
      match arW n m (tfld m PROJ (tierW h) (idxW h) 2) c d k fu with
      | none => none
      | some (x, m₁) =>
        asetK h c (rbProjW m₁ h (tfld m PROJ (tierW h) (idxW h) 0)
          (tfld m PROJ (tierW h) (idxW h) 1)
          (tfld m PROJ (tierW h) (idxW h) 2) x)
end


/-! ### Continuations and guarded equations -/

/-- After the cut-off. -/
def rcutK (n : Nat) (h c d k fu : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => if x ≤ d then some (h, m₁) else arNodeW n m₁ h c d k fu

/-- The arms after each child. -/
def rappK₁ (n : Nat) (h c d k fu fw aw : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => rappK₂ h c fw aw x (arW n m₁ aw c d k fu)
where rappK₂ (h c fw aw x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) => asetK h c (rbAppW m₂ h fw aw x y)

def rlamK₁ (n : Nat) (h c d k fu fw bw : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => rlamK₂ h c fw bw x (arW n m₁ bw (c + 1) d k fu)
where rlamK₂ (h c fw bw x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) => asetK h c (rbLamW m₂ h fw bw x y)

def rfaK₁ (n : Nat) (h c d k fu fw bw : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => rfaK₂ h c fw bw x (arW n m₁ bw (c + 1) d k fu)
where rfaK₂ (h c fw bw x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) => asetK h c (rbForallW m₂ h fw bw x y)

def rleK₁ (n : Nat) (h c d k fu fw vw bw : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => rleK₂ n h c d k fu fw vw bw x (arW n m₁ vw c d k fu)
where
  rleK₂ (n : Nat) (h c d k fu fw vw bw x : Word) : Option (Word × Mem) → Option (Word × Mem)
    | none => none
    | some (y, m₂) => rleK₃ h c fw vw bw x y (arW n m₂ bw (c + 1) d k fu)
  rleK₃ (h c fw vw bw x y : Word) : Option (Word × Mem) → Option (Word × Mem)
    | none => none
    | some (z, m₃) => asetK h c (rbLetW m₃ h fw vw bw x y z)

def rpjK₁ (h c nw iw ew : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => asetK h c (rbProjW m₁ h nw iw ew x)


section aks
variable (n : Nat) (h c d k fu fw aw bw vw nw iw ew x y z : Word) (m₁ m₂ m₃ : Mem)
theorem rcutK_some : rcutK n h c d k fu (some (x, m₁)) =
    if x ≤ d then some (h, m₁) else arNodeW n m₁ h c d k fu := rfl
theorem rappK₁_some : rappK₁ n h c d k fu fw aw (some (x, m₁)) =
    rappK₁.rappK₂ h c fw aw x (arW n m₁ aw c d k fu) := rfl
theorem rappK₂_some : rappK₁.rappK₂ h c fw aw x (some (y, m₂)) = asetK h c (rbAppW m₂ h fw aw x y) :=
  rfl
theorem rlamK₁_some : rlamK₁ n h c d k fu fw bw (some (x, m₁)) =
    rlamK₁.rlamK₂ h c fw bw x (arW n m₁ bw (c + 1) d k fu) := rfl
theorem rlamK₂_some : rlamK₁.rlamK₂ h c fw bw x (some (y, m₂)) = asetK h c (rbLamW m₂ h fw bw x y) :=
  rfl
theorem rfaK₁_some : rfaK₁ n h c d k fu fw bw (some (x, m₁)) =
    rfaK₁.rfaK₂ h c fw bw x (arW n m₁ bw (c + 1) d k fu) := rfl
theorem rfaK₂_some : rfaK₁.rfaK₂ h c fw bw x (some (y, m₂)) =
    asetK h c (rbForallW m₂ h fw bw x y) := rfl
theorem rleK₁_some : rleK₁ n h c d k fu fw vw bw (some (x, m₁)) =
    rleK₁.rleK₂ n h c d k fu fw vw bw x (arW n m₁ vw c d k fu) := rfl
theorem rleK₂_some : rleK₁.rleK₂ n h c d k fu fw vw bw x (some (y, m₂)) =
    rleK₁.rleK₃ h c fw vw bw x y (arW n m₂ bw (c + 1) d k fu) := rfl
theorem rleK₃_some : rleK₁.rleK₃ h c fw vw bw x y (some (z, m₃)) =
    asetK h c (rbLetW m₃ h fw vw bw x y z) := rfl
theorem rpjK₁_some : rpjK₁ h c nw iw ew (some (x, m₁)) = asetK h c (rbProjW m₁ h nw iw ew x) := rfl
end aks

attribute [arena_grind =] rcutK_some rappK₁_some rappK₂_some rlamK₁_some rlamK₂_some rfaK₁_some
  rfaK₂_some rleK₁_some rleK₂_some rleK₃_some rpjK₁_some

section arms
variable (n : Nat) (m : Mem) (h c d k fu : Word)

theorem arW_eq (hf : fu ≠ 0) :
    arW (n + 1) m h c d k fu = rcutK n h c d k (fu - 1) (fvbW n m h (fu - 1)) := by
  rw [arW]; simp only [hf, ↓reduceIte]; cases fvbW n m h (fu - 1) <;> rfl

theorem arNodeW_app (hg : h >>> 28 = 4) : arNodeW (n + 1) m h c d k fu = arAppW n m h c d k fu := by
  rw [arNodeW]; simp [hg]

theorem arNodeW_lam (hg : h >>> 28 = 5) : arNodeW (n + 1) m h c d k fu = arLamW n m h c d k fu := by
  rw [arNodeW]; simp [hg]

theorem arNodeW_forall (hg : h >>> 28 = 6) : arNodeW (n + 1) m h c d k fu = arForallW n m h c d k fu := by
  rw [arNodeW]; simp [hg]

theorem arNodeW_let (hg : h >>> 28 = 7) : arNodeW (n + 1) m h c d k fu = arLetW n m h c d k fu := by
  rw [arNodeW]; simp [hg]

theorem arNodeW_proj (hg : h >>> 28 = 9) : arNodeW (n + 1) m h c d k fu = arProjW n m h c d k fu := by
  rw [arNodeW]; simp [hg]

theorem arNodeW_fvar_in (hv : viewOK m h FVAR) (hg : h >>> 28 = 1)
    (hdk : ¬ d + k < d) (hi : d ≤ tfld m FVAR (tierW h) (idxW h) 0 ∧ tfld m FVAR (tierW h) (idxW h) 0 < d + k)
    (ho : ¬ c + (d + k - 1 - tfld m FVAR (tierW h) (idxW h) 0) < c) :
    arNodeW (n + 1) m h c d k fu = binternW m (c + (d + k - 1 - tfld m FVAR (tierW h) (idxW h) 0)) := by
  rw [arNodeW]; simp only [hv.1, hg, ↓reduceIte, UInt64.not_le.mpr hv.2, hdk, hi, ho]; simp

theorem arNodeW_fvar_out (hv : viewOK m h FVAR) (hg : h >>> 28 = 1)
    (hdk : ¬ d + k < d) (hi : ¬ (d ≤ tfld m FVAR (tierW h) (idxW h) 0 ∧ tfld m FVAR (tierW h) (idxW h) 0 < d + k)) :
    arNodeW (n + 1) m h c d k fu = some (h, m) := by
  rw [arNodeW]; simp only [hv.1, hg, ↓reduceIte, UInt64.not_le.mpr hv.2, hdk, hi]; simp

theorem arNodeW_leaf (h1 : h >>> 28 ≠ 1)
    (h4 : h >>> 28 ≠ 4) (h5 : h >>> 28 ≠ 5) (h6 : h >>> 28 ≠ 6) (h7 : h >>> 28 ≠ 7)
    (h9 : h >>> 28 ≠ 9) : arNodeW (n + 1) m h c d k fu = some (h, m) := by
  rw [arNodeW]; simp [h1, h4, h5, h6, h7, h9]

theorem arAppW_hit (hr : mfindG abSch m h c ≠ []) (hh : (mfindG abSch m h c).headD 0 ≠ 0) :
    arAppW (n + 1) m h c d k fu =
      some (rdW (m.arr64 ABMEMO) ((mfindG abSch m h c).tail.headD 0 * 4 + 3), m) := by
  rw [arAppW]; simp only [hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]

theorem arAppW_miss (hr : mfindG abSch m h c ≠ []) (hh : (mfindG abSch m h c).headD 0 = 0)
    (hvk : viewOK m h APP) :
    arAppW (n + 1) m h c d k fu =
      rappK₁ n h c d k fu (tfld m APP (tierW h) (idxW h) 0)
        (tfld m APP (tierW h) (idxW h) 1)
        (arW n m (tfld m APP (tierW h) (idxW h) 0) c d k fu) := by
  rw [arAppW]; simp only [hr, hh, ↓reduceIte, ne_eq, not_true_eq_false, hvk.1, ↓reduceIte, UInt64.not_le.mpr hvk.2]
  cases arW n m (tfld m APP (tierW h) (idxW h) 0) c d k fu <;> rfl

theorem arLamW_hit (h1 : c + 1 ≠ 0) (hr : mfindG abSch m h c ≠ [])
    (hh : (mfindG abSch m h c).headD 0 ≠ 0) :
    arLamW (n + 1) m h c d k fu =
      some (rdW (m.arr64 ABMEMO) ((mfindG abSch m h c).tail.headD 0 * 4 + 3), m) := by
  rw [arLamW]; simp only [h1, hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]

theorem arLamW_miss (h1 : c + 1 ≠ 0) (hr : mfindG abSch m h c ≠ [])
    (hh : (mfindG abSch m h c).headD 0 = 0) (hvk : viewOK m h LAM) :
    arLamW (n + 1) m h c d k fu =
      rlamK₁ n h c d k fu (tfld m LAM (tierW h) (idxW h) 0)
        (tfld m LAM (tierW h) (idxW h) 1)
        (arW n m (tfld m LAM (tierW h) (idxW h) 0) c d k fu) := by
  rw [arLamW]; simp only [h1, hr, hh, ↓reduceIte, ne_eq, not_true_eq_false, hvk.1, ↓reduceIte, UInt64.not_le.mpr hvk.2]
  cases arW n m (tfld m LAM (tierW h) (idxW h) 0) c d k fu <;> rfl

theorem arForallW_hit (h1 : c + 1 ≠ 0) (hr : mfindG abSch m h c ≠ [])
    (hh : (mfindG abSch m h c).headD 0 ≠ 0) :
    arForallW (n + 1) m h c d k fu =
      some (rdW (m.arr64 ABMEMO) ((mfindG abSch m h c).tail.headD 0 * 4 + 3), m) := by
  rw [arForallW]; simp only [h1, hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]

theorem arForallW_miss (h1 : c + 1 ≠ 0) (hr : mfindG abSch m h c ≠ [])
    (hh : (mfindG abSch m h c).headD 0 = 0) (hvk : viewOK m h FORALL) :
    arForallW (n + 1) m h c d k fu =
      rfaK₁ n h c d k fu (tfld m FORALL (tierW h) (idxW h) 0)
        (tfld m FORALL (tierW h) (idxW h) 1)
        (arW n m (tfld m FORALL (tierW h) (idxW h) 0) c d k fu) := by
  rw [arForallW]; simp only [h1, hr, hh, ↓reduceIte, ne_eq, not_true_eq_false, hvk.1, ↓reduceIte, UInt64.not_le.mpr hvk.2]
  cases arW n m (tfld m FORALL (tierW h) (idxW h) 0) c d k fu <;> rfl

theorem arLetW_hit (h1 : c + 1 ≠ 0) (hr : mfindG abSch m h c ≠ [])
    (hh : (mfindG abSch m h c).headD 0 ≠ 0) :
    arLetW (n + 1) m h c d k fu =
      some (rdW (m.arr64 ABMEMO) ((mfindG abSch m h c).tail.headD 0 * 4 + 3), m) := by
  rw [arLetW]; simp only [h1, hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]

theorem arLetW_miss (h1 : c + 1 ≠ 0) (hr : mfindG abSch m h c ≠ [])
    (hh : (mfindG abSch m h c).headD 0 = 0) (hvk : viewOK m h LET) :
    arLetW (n + 1) m h c d k fu =
      rleK₁ n h c d k fu (tfld m LET (tierW h) (idxW h) 0)
        (tfld m LET (tierW h) (idxW h) 1)
        (tfld m LET (tierW h) (idxW h) 2)
        (arW n m (tfld m LET (tierW h) (idxW h) 0) c d k fu) := by
  rw [arLetW]; simp only [h1, hr, hh, ↓reduceIte, ne_eq, not_true_eq_false, hvk.1, ↓reduceIte, UInt64.not_le.mpr hvk.2]
  cases arW n m (tfld m LET (tierW h) (idxW h) 0) c d k fu with
  | none => rfl
  | some p =>
    obtain ⟨x, m₁⟩ := p
    cases arW n m₁ (tfld m LET (tierW h) (idxW h) 1) c d k fu <;> rfl

theorem arProjW_hit (hr : mfindG abSch m h c ≠ []) (hh : (mfindG abSch m h c).headD 0 ≠ 0) :
    arProjW (n + 1) m h c d k fu =
      some (rdW (m.arr64 ABMEMO) ((mfindG abSch m h c).tail.headD 0 * 4 + 3), m) := by
  rw [arProjW]; simp only [hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]

theorem arProjW_miss (hr : mfindG abSch m h c ≠ []) (hh : (mfindG abSch m h c).headD 0 = 0)
    (hvk : viewOK m h PROJ) :
    arProjW (n + 1) m h c d k fu =
      rpjK₁ h c (tfld m PROJ (tierW h) (idxW h) 0)
        (tfld m PROJ (tierW h) (idxW h) 1)
        (tfld m PROJ (tierW h) (idxW h) 2)
        (arW n m (tfld m PROJ (tierW h) (idxW h) 2) c d k fu) := by
  rw [arProjW]; simp only [hr, hh, ↓reduceIte, ne_eq, not_true_eq_false, hvk.1, ↓reduceIte, UInt64.not_le.mpr hvk.2]
  cases arW n m (tfld m PROJ (tierW h) (idxW h) 2) c d k fu <;> rfl

end arms

grind_pattern [arena_grind] arW_eq => arW (n + 1) m h c d k fu
grind_pattern [arena_grind] arNodeW_app => arNodeW (n + 1) m h c d k fu
grind_pattern [arena_grind] arNodeW_lam => arNodeW (n + 1) m h c d k fu
grind_pattern [arena_grind] arNodeW_forall => arNodeW (n + 1) m h c d k fu
grind_pattern [arena_grind] arNodeW_let => arNodeW (n + 1) m h c d k fu
grind_pattern [arena_grind] arNodeW_proj => arNodeW (n + 1) m h c d k fu
grind_pattern [arena_grind] arNodeW_fvar_in => arNodeW (n + 1) m h c d k fu
grind_pattern [arena_grind] arNodeW_fvar_out => arNodeW (n + 1) m h c d k fu
grind_pattern [arena_grind] arNodeW_leaf => arNodeW (n + 1) m h c d k fu
grind_pattern [arena_grind] arAppW_hit => arAppW (n + 1) m h c d k fu
grind_pattern [arena_grind] arAppW_miss => arAppW (n + 1) m h c d k fu
grind_pattern [arena_grind] arLamW_hit => arLamW (n + 1) m h c d k fu
grind_pattern [arena_grind] arLamW_miss => arLamW (n + 1) m h c d k fu
grind_pattern [arena_grind] arForallW_hit => arForallW (n + 1) m h c d k fu
grind_pattern [arena_grind] arForallW_miss => arForallW (n + 1) m h c d k fu
grind_pattern [arena_grind] arLetW_hit => arLetW (n + 1) m h c d k fu
grind_pattern [arena_grind] arLetW_miss => arLetW (n + 1) m h c d k fu
grind_pattern [arena_grind] arProjW_hit => arProjW (n + 1) m h c d k fu
grind_pattern [arena_grind] arProjW_miss => arProjW (n + 1) m h c d k fu

/-- con-ron: ConRon/Arena/ExprOps.lean:1758-1779 ConRon.Arena.abstractRangeGo -/
@[l_impl ConRon.Arena.abstractRangeGo]
def arGo : FunDecl := lfn (h, c, d, k, fu) locals (x, r) {
  if fu == 0 { abort };
  x := call ab_fvb(h, fu - 1);
  if x <= d { return h };
  r := call ar_node(h, c, d, k, fu - 1);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1758-1779 ConRon.Arena.abstractRangeGo
con-ron: ConRon/Arena/ExprOps.lean:1747-1754 ConRon.Arena.absRangeArmFVar -/
@[l_impl ConRon.Arena.absRangeArmFVar]
def arNode : FunDecl := lfn (h, c, d, k, fu) locals (x, g, t, i, v, r) {
  g := h >> 28;
  if g == 4 { r := call ar_app(h, c, d, k, fu); return r };
  if g == 5 { r := call ar_lam(h, c, d, k, fu); return r };
  if g == 6 { r := call ar_forall(h, c, d, k, fu); return r };
  if g == 1 {
    t := ⟦h⟧.tier;
    i := ⟦h⟧.idx;
    if t != 0 && CTL.u64[1] == 0 { abort };
    if FVAR⟨t⟩.count <= i { abort };
    if d + k < d { abort };
    x := FVAR⟨t, i⟩.i;
    if d <= x && x < d + k {
      v := c + (d + k - 1 - x);
      if v < c { abort };
      r := call intern_bvar(v);
      return r
    };
    return h
  };
  if g == 7 { r := call ar_let(h, c, d, k, fu); return r };
  if g == 9 { r := call ar_proj(h, c, d, k, fu); return r };
  return h
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1781-1796 ConRon.Arena.absRangeGoArmApp -/
@[l_impl ConRon.Arena.absRangeGoArmApp]
def arApp : FunDecl := lfn (h, c, d, k, fu) locals (fd, j, e0, t, i, f, a, x, y, r, u) {
  (fd, j, e0) := call ab_find(h, c);
  if fd != 0 { return ABMEMO.u64[j * 4 + 3] };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if APP⟨t⟩.count <= i { abort };
  f := APP⟨t, i⟩.f;
  a := APP⟨t, i⟩.a;
  x := call ar_go(f, c, d, k, fu);
  y := call ar_go(a, c, d, k, fu);
  if x == f && y == a { r := h } else { r := call mk_app(x, y) };
  (fd, j, e0) := call ab_find(h, c);
  u := call ab_put(h, c, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1798-1813 ConRon.Arena.absRangeGoArmBind -/
@[l_impl ConRon.Arena.absRangeGoArmBind]
def arLam : FunDecl := lfn (h, c, d, k, fu) locals (fd, j, e0, t, i, f, a, x, y, r, u) {
  if c + 1 == 0 { abort };
  (fd, j, e0) := call ab_find(h, c);
  if fd != 0 { return ABMEMO.u64[j * 4 + 3] };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if LAM⟨t⟩.count <= i { abort };
  f := LAM⟨t, i⟩.ty;
  a := LAM⟨t, i⟩.b;
  x := call ar_go(f, c, d, k, fu);
  y := call ar_go(a, c + 1, d, k, fu);
  if x == f && y == a { r := h } else { r := call mk_lam(x, y) };
  (fd, j, e0) := call ab_find(h, c);
  u := call ab_put(h, c, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1798-1813 ConRon.Arena.absRangeGoArmBind -/
@[l_impl ConRon.Arena.absRangeGoArmBind]
def arForall : FunDecl := lfn (h, c, d, k, fu) locals (fd, j, e0, t, i, f, a, x, y, r, u) {
  if c + 1 == 0 { abort };
  (fd, j, e0) := call ab_find(h, c);
  if fd != 0 { return ABMEMO.u64[j * 4 + 3] };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if FORALL⟨t⟩.count <= i { abort };
  f := FORALL⟨t, i⟩.ty;
  a := FORALL⟨t, i⟩.b;
  x := call ar_go(f, c, d, k, fu);
  y := call ar_go(a, c + 1, d, k, fu);
  if x == f && y == a { r := h } else { r := call mk_forall(x, y) };
  (fd, j, e0) := call ab_find(h, c);
  u := call ab_put(h, c, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1815-1831 ConRon.Arena.absRangeGoArmLet -/
@[l_impl ConRon.Arena.absRangeGoArmLet]
def arLet : FunDecl := lfn (h, c, d, k, fu) locals (fd, j, e0, t, i, f, a, b, x, y, z, r, u) {
  if c + 1 == 0 { abort };
  (fd, j, e0) := call ab_find(h, c);
  if fd != 0 { return ABMEMO.u64[j * 4 + 3] };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if LET⟨t⟩.count <= i { abort };
  f := LET⟨t, i⟩.ty;
  a := LET⟨t, i⟩.v;
  b := LET⟨t, i⟩.b;
  x := call ar_go(f, c, d, k, fu);
  y := call ar_go(a, c, d, k, fu);
  z := call ar_go(b, c + 1, d, k, fu);
  if x == f && y == a && z == b { r := h } else { r := call mk_let(x, y, z) };
  (fd, j, e0) := call ab_find(h, c);
  u := call ab_put(h, c, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1833-1847 ConRon.Arena.absRangeGoArmProj -/
@[l_impl ConRon.Arena.absRangeGoArmProj]
def arProj : FunDecl := lfn (h, c, d, k, fu) locals (fd, j, e0, t, i, nm, ix, e, x, r, u) {
  (fd, j, e0) := call ab_find(h, c);
  if fd != 0 { return ABMEMO.u64[j * 4 + 3] };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if PROJ⟨t⟩.count <= i { abort };
  nm := PROJ⟨t, i⟩.n;
  ix := PROJ⟨t, i⟩.i;
  e := PROJ⟨t, i⟩.e;
  x := call ar_go(e, c, d, k, fu);
  if x == e { r := h } else { r := call mk_proj(nm, ix, x) };
  (fd, j, e0) := call ab_find(h, c);
  u := call ab_put(h, c, r, fd, j);
  return r
}



/-! ## The program and its specs -/

/-- The walk without its entry, over `absWalkProg`. -/
def arWalkProg : Prog :=
  [("ar_go", arGo), ("ar_node", arNode), ("ar_app", arApp), ("ar_lam", arLam),
    ("ar_forall", arForall), ("ar_let", arLet), ("ar_proj", arProj)] ++ absWalkProg

/-- What the specs need of the program: `arWalkProg`'s functions. -/
def ArProg (p : Prog) : Prop := ProgHas p arWalkProg

theorem ArProg.base {p : Prog} (hp : ArProg p) : AbsProg p := hp.right

section specs
variable (p : Prog) (hp : ArProg p)

/-- The spec of `abs_go` at fuel `n`. -/
def ArGoSpec (n : Nat) : Prop := ∀ (s₀ : St) (h c d k fu : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "ar_go" [h, c, d, k, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ arW n s₀.mem h c d k fu = some (r.headD 0, s'.mem); ⊤⦄

/-- The spec of `ab_node` at fuel `n`. -/
def ArNodeSpec (n : Nat) : Prop := ∀ (s₀ : St) (h c d k fu : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "ar_node" [h, c, d, k, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ arNodeW n s₀.mem h c d k fu = some (r.headD 0, s'.mem); ⊤⦄

/-- The specs of the five arms at fuel `n`. -/
def ArArmSpec (n : Nat) : Prop := ∀ (s₀ : St) (h c d k fu : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ar_app" [h, c, d, k, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ arAppW n s₀.mem h c d k fu = some (r.headD 0, s'.mem); ⊤⦄ ∧
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ar_lam" [h, c, d, k, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ arLamW n s₀.mem h c d k fu = some (r.headD 0, s'.mem); ⊤⦄ ∧
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ar_forall" [h, c, d, k, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ arForallW n s₀.mem h c d k fu = some (r.headD 0, s'.mem); ⊤⦄ ∧
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ar_let" [h, c, d, k, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ arLetW n s₀.mem h c d k fu = some (r.headD 0, s'.mem); ⊤⦄ ∧
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ar_proj" [h, c, d, k, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ arProjW n s₀.mem h c d k fu = some (r.headD 0, s'.mem); ⊤⦄

include hp in
theorem arGo_step (n : Nat) (ih : ArNodeSpec p n) : ArGoSpec p (n + 1) := by
  unfold ArNodeSpec at ih
  intro s₀ h c d k fu
  rw [invoke_eq _ (hp.get "ar_go")]
  simp only [callFn, arGo]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, abFvb_spec p hp.base n, ih] <;>
    finish

include hp in
theorem arNode_step (n : Nat) (ih : ArArmSpec p n) : ArNodeSpec p (n + 1) := by
  intro s₀ h c d k fu
  have ihA := fun s h c d k fu => (ih s h c d k fu).1
  have ihL := fun s h c d k fu => (ih s h c d k fu).2.1
  have ihF := fun s h c d k fu => (ih s h c d k fu).2.2.1
  have ihE := fun s h c d k fu => (ih s h c d k fu).2.2.2.1
  have ihP := fun s h c d k fu => (ih s h c d k fu).2.2.2.2
  rw [invoke_eq _ (hp.get "ar_node")]
  simp only [callFn, arNode]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt,
      tcntM, evalE_tierE, evalE_idxE,
      internBVar_spec p (hp.get "bvar_find") (hp.get "bvar_push") (hp.get "intern_bvar") n, ihA,
          ihL, ihF, ihE, ihP] <;>
    finish [viewOK, tierW, idxW]

end specs

end L.Arena
