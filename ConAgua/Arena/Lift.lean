module

public import ConAgua.Arena.MemoLib
public import ConAgua.Arena.ExprMk
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
import ConAgua.Census.Attr

@[expose] public section

/-!
# `liftLooseBVars`: the first walk that interns its results

con-ron's `lift_loose_bvars_go` (Lean twin `liftLooseBVarsGo`, `Arena/ExprOps.lean:668`) and its
entry `lift_loose_bvars_fast` (`liftLooseBVarsFast`): bump every loose bound variable `≥ c` by
`amount`, memoized per `(node, cutoff)` in `liftC`, rebuilding the term through the store.

`lift_go(h, c, k)` (`k` the amount), as the twin's dispatcher:
* the **cutoff**: `der_b(h)` (the range field of the derived word, `ExprMk.lean`); if it is below
  `satRange` and at most `c`, return `h`;
* the **view** checks (scratch tier, the tier's count; the twin's `view` fails there), then per tag:
  `bvar i`: `i < c` returns `h`, else `intern_bvar(i + k)` (an `abort` where `i + k` wraps);
  `fvar`, `sort`, `const`, `lit`: `h`; the compound tags call their arm.
* the **arms** `lift_app`, `lift_lam`, `lift_forall`, `lift_let`, `lift_proj` (the twin's
  `liftArmApp`, …): probe the memo `lf_find(h, c)`; on a hit return the value; else walk the
  children (a binder's body and `letE`'s body at `c + 1`), rebuild with `mk_*`, probe again and
  `lf_put`.

`lift_entry(h, k, c)` is `liftLooseBVarsFast`: `lf_clear(); r := lift_go(h, c, k); lf_clear()`.
The memo is the library's (`lfSch`: array 41, `CTL[42]`, `CTL[43]`), keys `(h, c)`.

The models `liftW`/`lift*W` follow the code with L's fuel (one level per call).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- Record `r` at `(h, c)` in the lift memo and return it. -/
def lsetK (h c : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m₁) =>
    match msetG lfSch m₁ h c r with
    | none => none
    | some m₂ => some (r, m₂)

mutual
/-- **The model of `lift_go`** at L fuel `n`. -/
def liftW : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, h, c, k =>
    if derBW m h < 32767 ∧ derBW m h ≤ c then some (h, m)
    else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if h >>> 28 = 0 then
      if rdW (m.arr64 CTL) (22 + tierW h) ≤ idxW h then none
      else if rdW (m.arr64 BREC) (idxW h * 2 + tierW h) < c then some (h, m)
      else if rdW (m.arr64 BREC) (idxW h * 2 + tierW h) + k <
          rdW (m.arr64 BREC) (idxW h * 2 + tierW h) then none
      else binternW m (rdW (m.arr64 BREC) (idxW h * 2 + tierW h) + k)
    else if h >>> 28 = 4 then
      if rdW (m.arr64 CTL) (4 + tierW h) ≤ idxW h then none else liftAppW n m h c k
    else if h >>> 28 = 5 then
      if rdW (m.arr64 CTL) (28 + tierW h) ≤ idxW h then none else liftLamW n m h c k
    else if h >>> 28 = 6 then
      if rdW (m.arr64 CTL) (30 + tierW h) ≤ idxW h then none else liftForallW n m h c k
    else if h >>> 28 = 7 then
      if rdW (m.arr64 CTL) (20 + tierW h) ≤ idxW h then none else liftLetW n m h c k
    else if h >>> 28 = 9 then
      if rdW (m.arr64 CTL) (32 + tierW h) ≤ idxW h then none else liftProjW n m h c k
    else if h >>> 28 = 1 then
      if rdW (m.arr64 CTL) (26 + tierW h) ≤ idxW h then none else some (h, m)
    else if h >>> 28 = 2 then
      if rdW (m.arr64 CTL) (16 + tierW h) ≤ idxW h then none else some (h, m)
    else if h >>> 28 = 3 then
      if rdW (m.arr64 CTL) (18 + tierW h) ≤ idxW h then none else some (h, m)
    else if h >>> 28 = 8 then
      if rdW (m.arr64 CTL) (2 + tierW h) ≤ idxW h then none else some (h, m)
    else none

/-- **The model of `lift_app`.** -/
def liftAppW : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, h, c, k =>
    if mfindG lfSch m h c = [] then none
    else if (mfindG lfSch m h c).headD 0 ≠ 0 then
      some (rdW (m.arr64 LMEMO) ((mfindG lfSch m h c).tail.headD 0 * 4 + 3), m)
    else
      match liftW n m (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2)) c k with
      | none => none
      | some (x, m₁) =>
        match liftW n m₁ (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2 + 1)) c k with
        | none => none
        | some (y, m₂) => lsetK h c (mkAppW m₂ x y)

/-- **The model of `lift_lam`.** -/
def liftLamW : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, h, c, k =>
    if c + 1 = 0 then none
    else if mfindG lfSch m h c = [] then none
    else if (mfindG lfSch m h c).headD 0 ≠ 0 then
      some (rdW (m.arr64 LMEMO) ((mfindG lfSch m h c).tail.headD 0 * 4 + 3), m)
    else
      match liftW n m (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2)) c k with
      | none => none
      | some (x, m₁) =>
        match liftW n m₁ (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2 + 1)) (c + 1) k with
        | none => none
        | some (y, m₂) => lsetK h c (mkLamW m₂ x y)

/-- **The model of `lift_forall`.** -/
def liftForallW : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, h, c, k =>
    if c + 1 = 0 then none
    else if mfindG lfSch m h c = [] then none
    else if (mfindG lfSch m h c).headD 0 ≠ 0 then
      some (rdW (m.arr64 LMEMO) ((mfindG lfSch m h c).tail.headD 0 * 4 + 3), m)
    else
      match liftW n m (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2)) c k with
      | none => none
      | some (x, m₁) =>
        match liftW n m₁ (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2 + 1)) (c + 1) k with
        | none => none
        | some (y, m₂) => lsetK h c (mkForallW m₂ x y)

/-- **The model of `lift_let`.** -/
def liftLetW : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, h, c, k =>
    if c + 1 = 0 then none
    else if mfindG lfSch m h c = [] then none
    else if (mfindG lfSch m h c).headD 0 ≠ 0 then
      some (rdW (m.arr64 LMEMO) ((mfindG lfSch m h c).tail.headD 0 * 4 + 3), m)
    else
      match liftW n m (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3)) c k with
      | none => none
      | some (x, m₁) =>
        match liftW n m₁ (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 1)) c k with
        | none => none
        | some (y, m₂) =>
          match liftW n m₂ (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 2)) (c + 1) k with
          | none => none
          | some (z, m₃) => lsetK h c (mkLetW m₃ x y z)

/-- **The model of `lift_proj`.** -/
def liftProjW : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, h, c, k =>
    if mfindG lfSch m h c = [] then none
    else if (mfindG lfSch m h c).headD 0 ≠ 0 then
      some (rdW (m.arr64 LMEMO) ((mfindG lfSch m h c).tail.headD 0 * 4 + 3), m)
    else
      match liftW n m (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 2)) c k with
      | none => none
      | some (x, m₁) =>
        lsetK h c (mkProjW m₁ (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3))
          (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 1)) x)
end

/-! ### Continuations and guarded equations -/

/-- The arms after each child (first-order continuations: `grind` instantiates their equations
by matching, which a continuation given as a `fun` defeats). -/
def appK₁ (n : Nat) (h c k aw : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => appK₂ h c x (liftW n m₁ aw c k)
where appK₂ (h c x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) => lsetK h c (mkAppW m₂ x y)

def lamK₁ (n : Nat) (h c k bw : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => lamK₂ h c x (liftW n m₁ bw (c + 1) k)
where lamK₂ (h c x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) => lsetK h c (mkLamW m₂ x y)

def faK₁ (n : Nat) (h c k bw : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => faK₂ h c x (liftW n m₁ bw (c + 1) k)
where faK₂ (h c x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) => lsetK h c (mkForallW m₂ x y)

def leK₁ (n : Nat) (h c k vw bw : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => leK₂ n h c k bw x (liftW n m₁ vw c k)
where
  leK₂ (n : Nat) (h c k bw x : Word) : Option (Word × Mem) → Option (Word × Mem)
    | none => none
    | some (y, m₂) => leK₃ h c x y (liftW n m₂ bw (c + 1) k)
  leK₃ (h c x y : Word) : Option (Word × Mem) → Option (Word × Mem)
    | none => none
    | some (z, m₃) => lsetK h c (mkLetW m₃ x y z)

def pjK₁ (h c nw iw : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => lsetK h c (mkProjW m₁ nw iw x)

section ks
variable (n : Nat) (h c k aw bw vw nw iw x y z : Word) (m₁ m₂ m₃ : Mem)
theorem appK₁_some' : appK₁ n h c k aw (some (x, m₁)) = appK₁.appK₂ h c x (liftW n m₁ aw c k) := rfl
theorem appK₂_some' : appK₁.appK₂ h c x (some (y, m₂)) = lsetK h c (mkAppW m₂ x y) := rfl
theorem lamK₁_some : lamK₁ n h c k bw (some (x, m₁)) = lamK₁.lamK₂ h c x (liftW n m₁ bw (c + 1) k) :=
  rfl
theorem lamK₂_some : lamK₁.lamK₂ h c x (some (y, m₂)) = lsetK h c (mkLamW m₂ x y) := rfl
theorem faK₁_some : faK₁ n h c k bw (some (x, m₁)) = faK₁.faK₂ h c x (liftW n m₁ bw (c + 1) k) :=
  rfl
theorem faK₂_some : faK₁.faK₂ h c x (some (y, m₂)) = lsetK h c (mkForallW m₂ x y) := rfl
theorem leK₁_some : leK₁ n h c k vw bw (some (x, m₁)) = leK₁.leK₂ n h c k bw x (liftW n m₁ vw c k) :=
  rfl
theorem leK₂_some :
    leK₁.leK₂ n h c k bw x (some (y, m₂)) = leK₁.leK₃ h c x y (liftW n m₂ bw (c + 1) k) := rfl
theorem leK₃_some : leK₁.leK₃ h c x y (some (z, m₃)) = lsetK h c (mkLetW m₃ x y z) := rfl
theorem pjK₁_some : pjK₁ h c nw iw (some (x, m₁)) = lsetK h c (mkProjW m₁ nw iw x) := rfl
theorem lsetK_some (r : Word) :
    lsetK h c (some (r, m₁)) =
      (match msetG lfSch m₁ h c r with | none => none | some m₂ => some (r, m₂)) := rfl
end ks

attribute [arena_grind =] appK₁_some' appK₂_some' lamK₁_some lamK₂_some faK₁_some faK₂_some
  leK₁_some leK₂_some leK₃_some pjK₁_some lsetK_some

section arms
variable (n : Nat) (m : Mem) (h c k : Word)

theorem liftW_cut (hc : derBW m h < 32767 ∧ derBW m h ≤ c) :
    liftW (n + 1) m h c k = some (h, m) := by
  rw [liftW]; simp only [hc, and_self, ↓reduceIte]

theorem liftW_bvar_lt (hc : ¬ (derBW m h < 32767 ∧ derBW m h ≤ c)) (hv : viewOK m h 22)
    (hg : h >>> 28 = 0) (hl : rdW (m.arr64 BREC) (idxW h * 2 + tierW h) < c) :
    liftW (n + 1) m h c k = some (h, m) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [liftW]; simp only [hc, hv1, hg, ↓reduceIte, hl]; simp [UInt64.not_le.mpr hv2]

theorem liftW_bvar_ge (hc : ¬ (derBW m h < 32767 ∧ derBW m h ≤ c)) (hv : viewOK m h 22)
    (hg : h >>> 28 = 0) (hl : ¬ rdW (m.arr64 BREC) (idxW h * 2 + tierW h) < c)
    (ho : ¬ rdW (m.arr64 BREC) (idxW h * 2 + tierW h) + k <
      rdW (m.arr64 BREC) (idxW h * 2 + tierW h)) :
    liftW (n + 1) m h c k = binternW m (rdW (m.arr64 BREC) (idxW h * 2 + tierW h) + k) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [liftW]; simp only [hc, hv1, hg, ↓reduceIte, hl, ho]; simp [UInt64.not_le.mpr hv2]

theorem liftW_fvar (hc : ¬ (derBW m h < 32767 ∧ derBW m h ≤ c)) (hv : viewOK m h 26)
    (hg : h >>> 28 = 1) : liftW (n + 1) m h c k = some (h, m) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [liftW]; simp [hc, hv1, hg, UInt64.not_le.mpr hv2]

theorem liftW_sort (hc : ¬ (derBW m h < 32767 ∧ derBW m h ≤ c)) (hv : viewOK m h 16)
    (hg : h >>> 28 = 2) : liftW (n + 1) m h c k = some (h, m) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [liftW]; simp [hc, hv1, hg, UInt64.not_le.mpr hv2]

theorem liftW_const (hc : ¬ (derBW m h < 32767 ∧ derBW m h ≤ c)) (hv : viewOK m h 18)
    (hg : h >>> 28 = 3) : liftW (n + 1) m h c k = some (h, m) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [liftW]; simp [hc, hv1, hg, UInt64.not_le.mpr hv2]

theorem liftW_lit (hc : ¬ (derBW m h < 32767 ∧ derBW m h ≤ c)) (hv : viewOK m h 2)
    (hg : h >>> 28 = 8) : liftW (n + 1) m h c k = some (h, m) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [liftW]; simp [hc, hv1, hg, UInt64.not_le.mpr hv2]

theorem liftW_app (hc : ¬ (derBW m h < 32767 ∧ derBW m h ≤ c)) (hv : viewOK m h 4)
    (hg : h >>> 28 = 4) : liftW (n + 1) m h c k = liftAppW n m h c k := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [liftW]; simp [hc, hv1, hg, UInt64.not_le.mpr hv2]

theorem liftW_lam (hc : ¬ (derBW m h < 32767 ∧ derBW m h ≤ c)) (hv : viewOK m h 28)
    (hg : h >>> 28 = 5) : liftW (n + 1) m h c k = liftLamW n m h c k := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [liftW]; simp [hc, hv1, hg, UInt64.not_le.mpr hv2]

theorem liftW_forall (hc : ¬ (derBW m h < 32767 ∧ derBW m h ≤ c)) (hv : viewOK m h 30)
    (hg : h >>> 28 = 6) : liftW (n + 1) m h c k = liftForallW n m h c k := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [liftW]; simp [hc, hv1, hg, UInt64.not_le.mpr hv2]

theorem liftW_let (hc : ¬ (derBW m h < 32767 ∧ derBW m h ≤ c)) (hv : viewOK m h 20)
    (hg : h >>> 28 = 7) : liftW (n + 1) m h c k = liftLetW n m h c k := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [liftW]; simp [hc, hv1, hg, UInt64.not_le.mpr hv2]

theorem liftW_proj (hc : ¬ (derBW m h < 32767 ∧ derBW m h ≤ c)) (hv : viewOK m h 32)
    (hg : h >>> 28 = 9) : liftW (n + 1) m h c k = liftProjW n m h c k := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [liftW]; simp [hc, hv1, hg, UInt64.not_le.mpr hv2]

/-- An arm's memo hit (the same for every arm: `c + 1 ≠ 0` for the binders). -/
theorem liftAppW_hit (hr : mfindG lfSch m h c ≠ []) (hh : (mfindG lfSch m h c).headD 0 ≠ 0) :
    liftAppW (n + 1) m h c k =
      some (rdW (m.arr64 LMEMO) ((mfindG lfSch m h c).tail.headD 0 * 4 + 3), m) := by
  rw [liftAppW]; simp only [hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]

theorem liftAppW_miss (hr : mfindG lfSch m h c ≠ []) (hh : (mfindG lfSch m h c).headD 0 = 0) :
    liftAppW (n + 1) m h c k =
      appK₁ n h c k (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2 + 1))
        (liftW n m (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2)) c k) := by
  rw [liftAppW]; simp only [hr, hh, ↓reduceIte, ne_eq, not_true_eq_false]
  cases liftW n m (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2)) c k <;> rfl

theorem liftLamW_hit (h1 : c + 1 ≠ 0) (hr : mfindG lfSch m h c ≠ [])
    (hh : (mfindG lfSch m h c).headD 0 ≠ 0) :
    liftLamW (n + 1) m h c k =
      some (rdW (m.arr64 LMEMO) ((mfindG lfSch m h c).tail.headD 0 * 4 + 3), m) := by
  rw [liftLamW]; simp only [h1, hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]

theorem liftLamW_miss (h1 : c + 1 ≠ 0) (hr : mfindG lfSch m h c ≠ [])
    (hh : (mfindG lfSch m h c).headD 0 = 0) :
    liftLamW (n + 1) m h c k =
      lamK₁ n h c k (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2 + 1))
        (liftW n m (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2)) c k) := by
  rw [liftLamW]; simp only [h1, hr, hh, ↓reduceIte, ne_eq, not_true_eq_false]
  cases liftW n m (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2)) c k <;> rfl

theorem liftForallW_hit (h1 : c + 1 ≠ 0) (hr : mfindG lfSch m h c ≠ [])
    (hh : (mfindG lfSch m h c).headD 0 ≠ 0) :
    liftForallW (n + 1) m h c k =
      some (rdW (m.arr64 LMEMO) ((mfindG lfSch m h c).tail.headD 0 * 4 + 3), m) := by
  rw [liftForallW]; simp only [h1, hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]

theorem liftForallW_miss (h1 : c + 1 ≠ 0) (hr : mfindG lfSch m h c ≠ [])
    (hh : (mfindG lfSch m h c).headD 0 = 0) :
    liftForallW (n + 1) m h c k =
      faK₁ n h c k (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2 + 1))
        (liftW n m (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2)) c k) := by
  rw [liftForallW]; simp only [h1, hr, hh, ↓reduceIte, ne_eq, not_true_eq_false]
  cases liftW n m (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2)) c k <;> rfl

theorem liftLetW_hit (h1 : c + 1 ≠ 0) (hr : mfindG lfSch m h c ≠ [])
    (hh : (mfindG lfSch m h c).headD 0 ≠ 0) :
    liftLetW (n + 1) m h c k =
      some (rdW (m.arr64 LMEMO) ((mfindG lfSch m h c).tail.headD 0 * 4 + 3), m) := by
  rw [liftLetW]; simp only [h1, hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]

theorem liftLetW_miss (h1 : c + 1 ≠ 0) (hr : mfindG lfSch m h c ≠ [])
    (hh : (mfindG lfSch m h c).headD 0 = 0) :
    liftLetW (n + 1) m h c k =
      leK₁ n h c k (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 1))
        (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 2))
        (liftW n m (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3)) c k) := by
  rw [liftLetW]; simp only [h1, hr, hh, ↓reduceIte, ne_eq, not_true_eq_false]
  cases liftW n m (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3)) c k with
  | none => rfl
  | some p =>
    obtain ⟨x, m₁⟩ := p
    cases liftW n m₁ (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 1)) c k <;> rfl

theorem liftProjW_hit (hr : mfindG lfSch m h c ≠ []) (hh : (mfindG lfSch m h c).headD 0 ≠ 0) :
    liftProjW (n + 1) m h c k =
      some (rdW (m.arr64 LMEMO) ((mfindG lfSch m h c).tail.headD 0 * 4 + 3), m) := by
  rw [liftProjW]; simp only [hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]

theorem liftProjW_miss (hr : mfindG lfSch m h c ≠ []) (hh : (mfindG lfSch m h c).headD 0 = 0) :
    liftProjW (n + 1) m h c k =
      pjK₁ h c (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3))
        (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 1))
        (liftW n m (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 2)) c k) := by
  rw [liftProjW]; simp only [hr, hh, ↓reduceIte, ne_eq, not_true_eq_false]
  cases liftW n m (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 2)) c k <;> rfl

end arms

grind_pattern [arena_grind] liftW_cut => liftW (n + 1) m h c k
grind_pattern [arena_grind] liftW_bvar_lt => liftW (n + 1) m h c k
grind_pattern [arena_grind] liftW_bvar_ge => liftW (n + 1) m h c k
grind_pattern [arena_grind] liftW_fvar => liftW (n + 1) m h c k
grind_pattern [arena_grind] liftW_sort => liftW (n + 1) m h c k
grind_pattern [arena_grind] liftW_const => liftW (n + 1) m h c k
grind_pattern [arena_grind] liftW_lit => liftW (n + 1) m h c k
grind_pattern [arena_grind] liftW_app => liftW (n + 1) m h c k
grind_pattern [arena_grind] liftW_lam => liftW (n + 1) m h c k
grind_pattern [arena_grind] liftW_forall => liftW (n + 1) m h c k
grind_pattern [arena_grind] liftW_let => liftW (n + 1) m h c k
grind_pattern [arena_grind] liftW_proj => liftW (n + 1) m h c k
grind_pattern [arena_grind] liftAppW_hit => liftAppW (n + 1) m h c k
grind_pattern [arena_grind] liftAppW_miss => liftAppW (n + 1) m h c k
grind_pattern [arena_grind] liftLamW_hit => liftLamW (n + 1) m h c k
grind_pattern [arena_grind] liftLamW_miss => liftLamW (n + 1) m h c k
grind_pattern [arena_grind] liftForallW_hit => liftForallW (n + 1) m h c k
grind_pattern [arena_grind] liftForallW_miss => liftForallW (n + 1) m h c k
grind_pattern [arena_grind] liftLetW_hit => liftLetW (n + 1) m h c k
grind_pattern [arena_grind] liftLetW_miss => liftLetW (n + 1) m h c k
grind_pattern [arena_grind] liftProjW_hit => liftProjW (n + 1) m h c k
grind_pattern [arena_grind] liftProjW_miss => liftProjW (n + 1) m h c k

/-! ## The L code -/

@[l_impl ConRon.Arena.liftLooseBVarsGo]
def liftGo : FunDecl := lfn (h, c, k) locals (x, g, t, i, r) {
  x := call der_b(h);
  if x < 32767 && x <= c { return h };
  g := h >> 28;
  t := (h >> 27) & 1;
  i := h & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if g == 0 {
    if CTL.u64[22 + t] <= i { abort };
    x := BREC.u64[i * 2 + t];
    if x < c { return h };
    if x + k < x { abort };
    r := call intern_bvar(x + k);
    return r
  };
  if g == 4 { if CTL.u64[4 + t] <= i { abort }; r := call lift_app(h, c, k); return r };
  if g == 5 { if CTL.u64[28 + t] <= i { abort }; r := call lift_lam(h, c, k); return r };
  if g == 6 { if CTL.u64[30 + t] <= i { abort }; r := call lift_forall(h, c, k); return r };
  if g == 7 { if CTL.u64[20 + t] <= i { abort }; r := call lift_let(h, c, k); return r };
  if g == 9 { if CTL.u64[32 + t] <= i { abort }; r := call lift_proj(h, c, k); return r };
  if g == 1 { if CTL.u64[26 + t] <= i { abort }; return h };
  if g == 2 { if CTL.u64[16 + t] <= i { abort }; return h };
  if g == 3 { if CTL.u64[18 + t] <= i { abort }; return h };
  if g == 8 { if CTL.u64[2 + t] <= i { abort }; return h };
  abort
}

@[l_impl ConRon.Arena.liftArmApp]
def liftApp : FunDecl := lfn (h, c, k) locals (fd, j, d, t, i, f, a, x, y, r, u) {
  (fd, j, d) := call lf_find(h, c);
  if fd != 0 { return LMEMO.u64[j * 4 + 3] };
  t := (h >> 27) & 1;
  i := h & 134217727;
  f := AREC.u64[i * 4 + t * 2];
  a := AREC.u64[i * 4 + t * 2 + 1];
  x := call lift_go(f, c, k);
  y := call lift_go(a, c, k);
  r := call mk_app(x, y);
  (fd, j, d) := call lf_find(h, c);
  u := call lf_put(h, c, r, fd, j);
  return r
}

@[l_impl ConRon.Arena.liftArmLam]
def liftLam : FunDecl := lfn (h, c, k) locals (fd, j, d, t, i, f, a, x, y, r, u) {
  if c + 1 == 0 { abort };
  (fd, j, d) := call lf_find(h, c);
  if fd != 0 { return LMEMO.u64[j * 4 + 3] };
  t := (h >> 27) & 1;
  i := h & 134217727;
  f := LAREC.u64[i * 4 + t * 2];
  a := LAREC.u64[i * 4 + t * 2 + 1];
  x := call lift_go(f, c, k);
  y := call lift_go(a, c + 1, k);
  r := call mk_lam(x, y);
  (fd, j, d) := call lf_find(h, c);
  u := call lf_put(h, c, r, fd, j);
  return r
}

@[l_impl ConRon.Arena.liftArmForallE]
def liftForall : FunDecl := lfn (h, c, k) locals (fd, j, d, t, i, f, a, x, y, r, u) {
  if c + 1 == 0 { abort };
  (fd, j, d) := call lf_find(h, c);
  if fd != 0 { return LMEMO.u64[j * 4 + 3] };
  t := (h >> 27) & 1;
  i := h & 134217727;
  f := FAREC.u64[i * 4 + t * 2];
  a := FAREC.u64[i * 4 + t * 2 + 1];
  x := call lift_go(f, c, k);
  y := call lift_go(a, c + 1, k);
  r := call mk_forall(x, y);
  (fd, j, d) := call lf_find(h, c);
  u := call lf_put(h, c, r, fd, j);
  return r
}

@[l_impl ConRon.Arena.liftArmLet]
def liftLet : FunDecl := lfn (h, c, k) locals (fd, j, d, t, i, f, a, b, x, y, z, r, u) {
  if c + 1 == 0 { abort };
  (fd, j, d) := call lf_find(h, c);
  if fd != 0 { return LMEMO.u64[j * 4 + 3] };
  t := (h >> 27) & 1;
  i := h & 134217727;
  f := LEREC.u64[i * 6 + t * 3];
  a := LEREC.u64[i * 6 + t * 3 + 1];
  b := LEREC.u64[i * 6 + t * 3 + 2];
  x := call lift_go(f, c, k);
  y := call lift_go(a, c, k);
  z := call lift_go(b, c + 1, k);
  r := call mk_let(x, y, z);
  (fd, j, d) := call lf_find(h, c);
  u := call lf_put(h, c, r, fd, j);
  return r
}

@[l_impl ConRon.Arena.liftArmProj]
def liftProj : FunDecl := lfn (h, c, k) locals (fd, j, d, t, i, nm, ix, e, x, r, u) {
  (fd, j, d) := call lf_find(h, c);
  if fd != 0 { return LMEMO.u64[j * 4 + 3] };
  t := (h >> 27) & 1;
  i := h & 134217727;
  nm := PJREC.u64[i * 6 + t * 3];
  ix := PJREC.u64[i * 6 + t * 3 + 1];
  e := PJREC.u64[i * 6 + t * 3 + 2];
  x := call lift_go(e, c, k);
  r := call mk_proj(nm, ix, x);
  (fd, j, d) := call lf_find(h, c);
  u := call lf_put(h, c, r, fd, j);
  return r
}

/-! ## The program and its specs -/

/-- What the specs need of the program: every function the walk calls, by name. -/
structure LiftProg (p : Prog) : Prop where
  derb : p.lookup "der_b" = some derB
  bvf : p.lookup "bvar_find" = some bvarFind
  bvp : p.lookup "bvar_push" = some bvarPush
  bvi : p.lookup "intern_bvar" = some internBVar
  lff : p.lookup "lf_find" = some (memoFindG lfSch)
  lfp : p.lookup "lf_put" = some (memoPutG lfSch)
  lfc : p.lookup "lf_clear" = some (memoClearG lfSch)
  go : p.lookup "lift_go" = some liftGo
  app : p.lookup "lift_app" = some liftApp
  lam : p.lookup "lift_lam" = some liftLam
  fa : p.lookup "lift_forall" = some liftForall
  le : p.lookup "lift_let" = some liftLet
  pj : p.lookup "lift_proj" = some liftProj
  mkapp : p.lookup "mk_app" = some mkApp
  appf : p.lookup "app_find" = some appFind
  appp : p.lookup "app_push" = some appPush
  appi : p.lookup "intern_app" = some internApp
  mklam : p.lookup "mk_lam" = some mkLam
  lamf : p.lookup "lam_find" = some lamFind
  lamp : p.lookup "lam_push" = some lamPush
  lami : p.lookup "intern_lam" = some internLamL
  mkfa : p.lookup "mk_forall" = some mkForall
  faf : p.lookup "forall_find" = some forallFind
  fap : p.lookup "forall_push" = some forallPush
  fai : p.lookup "intern_forall" = some internForallL
  mklet : p.lookup "mk_let" = some mkLet
  lef : p.lookup "letE_find" = some letFind
  lep : p.lookup "letE_push" = some letPush
  lei : p.lookup "intern_letE" = some internLet
  mkpj : p.lookup "mk_proj" = some mkProj
  pjf : p.lookup "proj_find" = some projFind
  pjp : p.lookup "proj_push" = some projPush
  pji : p.lookup "intern_proj" = some internProj

section specs
variable (p : Prog) (hp : LiftProg p)

/-- The spec of `lift_go` at fuel `n`. -/
def LiftGoSpec (n : Nat) : Prop := ∀ (s₀ : St) (h c k : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "lift_go" [h, c, k]
    ⦃fun r s' => LocEq s' s₀ ∧ liftW n s₀.mem h c k = some (r.headD 0, s'.mem); ⊤⦄

/-- The specs of the five arms at fuel `n`. -/
def LiftArmSpec (n : Nat) : Prop := ∀ (s₀ : St) (h c k : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "lift_app" [h, c, k]
    ⦃fun r s' => LocEq s' s₀ ∧ liftAppW n s₀.mem h c k = some (r.headD 0, s'.mem); ⊤⦄ ∧
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "lift_lam" [h, c, k]
    ⦃fun r s' => LocEq s' s₀ ∧ liftLamW n s₀.mem h c k = some (r.headD 0, s'.mem); ⊤⦄ ∧
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "lift_forall" [h, c, k]
    ⦃fun r s' => LocEq s' s₀ ∧ liftForallW n s₀.mem h c k = some (r.headD 0, s'.mem); ⊤⦄ ∧
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "lift_let" [h, c, k]
    ⦃fun r s' => LocEq s' s₀ ∧ liftLetW n s₀.mem h c k = some (r.headD 0, s'.mem); ⊤⦄ ∧
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "lift_proj" [h, c, k]
    ⦃fun r s' => LocEq s' s₀ ∧ liftProjW n s₀.mem h c k = some (r.headD 0, s'.mem); ⊤⦄

include hp in
set_option maxHeartbeats 1000000 in
theorem liftGo_step (n : Nat) (ih : LiftArmSpec p n) : LiftGoSpec p (n + 1) := by
  intro s₀ h c k
  have ihA := fun s h c k => (ih s h c k).1
  have ihL := fun s h c k => (ih s h c k).2.1
  have ihF := fun s h c k => (ih s h c k).2.2.1
  have ihE := fun s h c k => (ih s h c k).2.2.2.1
  have ihP := fun s h c k => (ih s h c k).2.2.2.2
  rw [invoke_eq _ hp.go]
  simp only [callFn, liftGo]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, derB_spec p hp.derb n,
      internBVar_spec p hp.bvf hp.bvp hp.bvi n, ihA, ihL, ihF, ihE, ihP] <;>
    finish [viewOK, tierW, idxW]

end specs

end L.Arena
