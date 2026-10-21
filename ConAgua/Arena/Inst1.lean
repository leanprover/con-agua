module

public import ConAgua.Arena.Lift
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store

@[expose] public section

/-!
# `instantiate1`: the second interning walk, on the same scaffolding

con-ron's `instantiate1_go` (Lean twin `instantiate1Go`, `Arena/ExprOps.lean`) and its entry
`instantiate1Fast`: replace `bvar d` by `v`, lowering loose `bvar`s above `d` by one, memoized per
`(node, depth)` in `inst1C`, rebuilding through the store. `inst_go(h, d, v)`, as the twin's
dispatcher: the derived-range cut-off (`der_b`), then the **tag** (not the view: the leaves and
unknown tags return `h` without reading the store), the `bvar` arm inline (`i = d`: `v`;
`i > d`: `intern_bvar(i - 1)`; else `h`), the compound tags call their arm. The arms
(`inst_app`, `inst_lam`, `inst_forall`, `inst_let`, `inst_proj`; the twin's `lam`/`forallE` share
`instantiate1ArmBind`) probe the memo **before** the view checks, as the twin does. The memo is
`imSch` (array 47, `CTL[44]`). Everything else is `Lift.lean`'s, renamed.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- Record `r` at `(h, d)` in the `instantiate1` memo and return it. -/
def isetK (h d : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m₁) =>
    match msetG imSch m₁ h d r with
    | none => none
    | some m₂ => some (r, m₂)

mutual
/-- **The model of `inst_go`** at L fuel `n`. -/
def instW : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, h, d, v =>
    if derBW m h < 32767 ∧ derBW m h ≤ d then some (h, m)
    else if h >>> 28 = 4 then instAppW n m h d v
    else if h >>> 28 = 5 then instLamW n m h d v
    else if h >>> 28 = 6 then instForallW n m h d v
    else if h >>> 28 = 0 then
      if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
      else if rdW (m.arr64 CTL) (22 + tierW h) ≤ idxW h then none
      else if rdW (m.arr64 BREC) (idxW h * 2 + tierW h) = d then some (v, m)
      else if d < rdW (m.arr64 BREC) (idxW h * 2 + tierW h) then
        binternW m (rdW (m.arr64 BREC) (idxW h * 2 + tierW h) - 1)
      else some (h, m)
    else if h >>> 28 = 7 then instLetW n m h d v
    else if h >>> 28 = 9 then instProjW n m h d v
    else some (h, m)
/-- **The model of `inst_app`.** -/
def instAppW : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, h, d, v =>
    if mfindG imSch m h d = [] then none
    else if (mfindG imSch m h d).headD 0 ≠ 0 then
      some (rdW (m.arr64 IMEMO) ((mfindG imSch m h d).tail.headD 0 * 4 + 3), m)
    else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if rdW (m.arr64 CTL) (4 + tierW h) ≤ idxW h then none
    else
      match instW n m (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2)) d v with
      | none => none
      | some (x, m₁) =>
        match instW n m₁ (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2 + 1)) d v with
        | none => none
        | some (y, m₂) => isetK h d (mkAppW m₂ x y)

/-- **The model of `inst_lam`.** -/
def instLamW : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, h, d, v =>
    if d + 1 = 0 then none
    else if mfindG imSch m h d = [] then none
    else if (mfindG imSch m h d).headD 0 ≠ 0 then
      some (rdW (m.arr64 IMEMO) ((mfindG imSch m h d).tail.headD 0 * 4 + 3), m)
    else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if rdW (m.arr64 CTL) (28 + tierW h) ≤ idxW h then none
    else
      match instW n m (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2)) d v with
      | none => none
      | some (x, m₁) =>
        match instW n m₁ (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2 + 1)) (d + 1) v with
        | none => none
        | some (y, m₂) => isetK h d (mkLamW m₂ x y)

/-- **The model of `inst_forall`.** -/
def instForallW : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, h, d, v =>
    if d + 1 = 0 then none
    else if mfindG imSch m h d = [] then none
    else if (mfindG imSch m h d).headD 0 ≠ 0 then
      some (rdW (m.arr64 IMEMO) ((mfindG imSch m h d).tail.headD 0 * 4 + 3), m)
    else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if rdW (m.arr64 CTL) (30 + tierW h) ≤ idxW h then none
    else
      match instW n m (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2)) d v with
      | none => none
      | some (x, m₁) =>
        match instW n m₁ (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2 + 1)) (d + 1) v with
        | none => none
        | some (y, m₂) => isetK h d (mkForallW m₂ x y)

/-- **The model of `inst_let`.** -/
def instLetW : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, h, d, v =>
    if d + 1 = 0 then none
    else if mfindG imSch m h d = [] then none
    else if (mfindG imSch m h d).headD 0 ≠ 0 then
      some (rdW (m.arr64 IMEMO) ((mfindG imSch m h d).tail.headD 0 * 4 + 3), m)
    else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if rdW (m.arr64 CTL) (20 + tierW h) ≤ idxW h then none
    else
      match instW n m (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3)) d v with
      | none => none
      | some (x, m₁) =>
        match instW n m₁ (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 1)) d v with
        | none => none
        | some (y, m₂) =>
          match instW n m₂ (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 2)) (d + 1) v with
          | none => none
          | some (z, m₃) => isetK h d (mkLetW m₃ x y z)

/-- **The model of `inst_proj`.** -/
def instProjW : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, h, d, v =>
    if mfindG imSch m h d = [] then none
    else if (mfindG imSch m h d).headD 0 ≠ 0 then
      some (rdW (m.arr64 IMEMO) ((mfindG imSch m h d).tail.headD 0 * 4 + 3), m)
    else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if rdW (m.arr64 CTL) (32 + tierW h) ≤ idxW h then none
    else
      match instW n m (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 2)) d v with
      | none => none
      | some (x, m₁) =>
        isetK h d (mkProjW m₁ (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3))
          (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 1)) x)
end

/-! ### Continuations and guarded equations -/

/-- The arms after each child (first-order continuations: `grind` instantiates their equations
by matching, which a continuation given as a `fun` defeats). -/
def iappK₁ (n : Nat) (h d v aw : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => iappK₂ h d x (instW n m₁ aw d v)
where iappK₂ (h d x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) => isetK h d (mkAppW m₂ x y)

def ilamK₁ (n : Nat) (h d v bw : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => ilamK₂ h d x (instW n m₁ bw (d + 1) v)
where ilamK₂ (h d x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) => isetK h d (mkLamW m₂ x y)

def ifaK₁ (n : Nat) (h d v bw : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => ifaK₂ h d x (instW n m₁ bw (d + 1) v)
where ifaK₂ (h d x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) => isetK h d (mkForallW m₂ x y)

def ileK₁ (n : Nat) (h d v vw bw : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => ileK₂ n h d v bw x (instW n m₁ vw d v)
where
  ileK₂ (n : Nat) (h d v bw x : Word) : Option (Word × Mem) → Option (Word × Mem)
    | none => none
    | some (y, m₂) => ileK₃ h d x y (instW n m₂ bw (d + 1) v)
  ileK₃ (h d x y : Word) : Option (Word × Mem) → Option (Word × Mem)
    | none => none
    | some (z, m₃) => isetK h d (mkLetW m₃ x y z)

def ipjK₁ (h d nw iw : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => isetK h d (mkProjW m₁ nw iw x)

section iks
variable (n : Nat) (h d v aw bw vw nw iw x y z : Word) (m₁ m₂ m₃ : Mem)
theorem iiappK₁_some : iappK₁ n h d v aw (some (x, m₁)) = iappK₁.iappK₂ h d x (instW n m₁ aw d v) := rfl
theorem iiappK₂_some : iappK₁.iappK₂ h d x (some (y, m₂)) = isetK h d (mkAppW m₂ x y) := rfl
theorem ilamK₁_some : ilamK₁ n h d v bw (some (x, m₁)) = ilamK₁.ilamK₂ h d x (instW n m₁ bw (d + 1) v) :=
  rfl
theorem ilamK₂_some : ilamK₁.ilamK₂ h d x (some (y, m₂)) = isetK h d (mkLamW m₂ x y) := rfl
theorem ifaK₁_some : ifaK₁ n h d v bw (some (x, m₁)) = ifaK₁.ifaK₂ h d x (instW n m₁ bw (d + 1) v) :=
  rfl
theorem ifaK₂_some : ifaK₁.ifaK₂ h d x (some (y, m₂)) = isetK h d (mkForallW m₂ x y) := rfl
theorem ileK₁_some : ileK₁ n h d v vw bw (some (x, m₁)) = ileK₁.ileK₂ n h d v bw x (instW n m₁ vw d v) :=
  rfl
theorem ileK₂_some :
    ileK₁.ileK₂ n h d v bw x (some (y, m₂)) = ileK₁.ileK₃ h d x y (instW n m₂ bw (d + 1) v) := rfl
theorem ileK₃_some : ileK₁.ileK₃ h d x y (some (z, m₃)) = isetK h d (mkLetW m₃ x y z) := rfl
theorem ipjK₁_some : ipjK₁ h d nw iw (some (x, m₁)) = isetK h d (mkProjW m₁ nw iw x) := rfl
theorem isetK_some (r : Word) :
    isetK h d (some (r, m₁)) =
      (match msetG imSch m₁ h d r with | none => none | some m₂ => some (r, m₂)) := rfl
end iks

attribute [arena_grind =] iiappK₁_some iiappK₂_some ilamK₁_some ilamK₂_some ifaK₁_some ifaK₂_some
  ileK₁_some ileK₂_some ileK₃_some ipjK₁_some isetK_some


section arms
variable (n : Nat) (m : Mem) (h d v : Word)

theorem instW_cut (hc : derBW m h < 32767 ∧ derBW m h ≤ d) :
    instW (n + 1) m h d v = some (h, m) := by
  rw [instW]; simp only [hc, and_self, ↓reduceIte]

theorem instW_app (hc : ¬ (derBW m h < 32767 ∧ derBW m h ≤ d)) (hg : h >>> 28 = 4) :
    instW (n + 1) m h d v = instAppW n m h d v := by
  rw [instW]; simp [hc, hg]

theorem instW_lam (hc : ¬ (derBW m h < 32767 ∧ derBW m h ≤ d)) (hg : h >>> 28 = 5) :
    instW (n + 1) m h d v = instLamW n m h d v := by
  rw [instW]; simp [hc, hg]

theorem instW_forall (hc : ¬ (derBW m h < 32767 ∧ derBW m h ≤ d)) (hg : h >>> 28 = 6) :
    instW (n + 1) m h d v = instForallW n m h d v := by
  rw [instW]; simp [hc, hg]

theorem instW_let (hc : ¬ (derBW m h < 32767 ∧ derBW m h ≤ d)) (hg : h >>> 28 = 7) :
    instW (n + 1) m h d v = instLetW n m h d v := by
  rw [instW]; simp [hc, hg]

theorem instW_proj (hc : ¬ (derBW m h < 32767 ∧ derBW m h ≤ d)) (hg : h >>> 28 = 9) :
    instW (n + 1) m h d v = instProjW n m h d v := by
  rw [instW]; simp [hc, hg]

theorem instW_bvar_eq (hc : ¬ (derBW m h < 32767 ∧ derBW m h ≤ d)) (hv : viewOK m h 22)
    (hg : h >>> 28 = 0) (he : rdW (m.arr64 BREC) (idxW h * 2 + tierW h) = d) :
    instW (n + 1) m h d v = some (v, m) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [instW]; simp [hc, hv1, hg, UInt64.not_le.mpr hv2, he]

theorem instW_bvar_gt (hc : ¬ (derBW m h < 32767 ∧ derBW m h ≤ d)) (hv : viewOK m h 22)
    (hg : h >>> 28 = 0) (he : rdW (m.arr64 BREC) (idxW h * 2 + tierW h) ≠ d)
    (hl : d < rdW (m.arr64 BREC) (idxW h * 2 + tierW h)) :
    instW (n + 1) m h d v = binternW m (rdW (m.arr64 BREC) (idxW h * 2 + tierW h) - 1) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [instW]; simp [hc, hv1, hg, UInt64.not_le.mpr hv2, he, hl]

theorem instW_bvar_lt (hc : ¬ (derBW m h < 32767 ∧ derBW m h ≤ d)) (hv : viewOK m h 22)
    (hg : h >>> 28 = 0) (he : rdW (m.arr64 BREC) (idxW h * 2 + tierW h) ≠ d)
    (hl : ¬ d < rdW (m.arr64 BREC) (idxW h * 2 + tierW h)) :
    instW (n + 1) m h d v = some (h, m) := by
  obtain ⟨hv1, hv2⟩ := hv
  rw [instW]; simp [hc, hv1, hg, UInt64.not_le.mpr hv2, he, hl]

theorem instW_leaf (hc : ¬ (derBW m h < 32767 ∧ derBW m h ≤ d)) (h0 : h >>> 28 ≠ 0)
    (h4 : h >>> 28 ≠ 4) (h5 : h >>> 28 ≠ 5) (h6 : h >>> 28 ≠ 6) (h7 : h >>> 28 ≠ 7)
    (h9 : h >>> 28 ≠ 9) : instW (n + 1) m h d v = some (h, m) := by
  rw [instW]; simp [hc, h0, h4, h5, h6, h7, h9]

/-- An arm's memo hit (the same for every arm: `d + 1 ≠ 0` for the binders). -/
theorem instAppW_hit (hr : mfindG imSch m h d ≠ []) (hh : (mfindG imSch m h d).headD 0 ≠ 0) :
    instAppW (n + 1) m h d v =
      some (rdW (m.arr64 IMEMO) ((mfindG imSch m h d).tail.headD 0 * 4 + 3), m) := by
  rw [instAppW]; simp only [hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]

theorem instAppW_miss (hr : mfindG imSch m h d ≠ []) (hh : (mfindG imSch m h d).headD 0 = 0)
    (hvk : viewOK m h 4) :
    instAppW (n + 1) m h d v =
      iappK₁ n h d v (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2 + 1))
        (instW n m (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2)) d v) := by
  rw [instAppW]; simp only [hr, hh, ↓reduceIte, ne_eq, not_true_eq_false, hvk.1, ↓reduceIte, UInt64.not_le.mpr hvk.2]
  cases instW n m (rdW (m.arr64 AREC) (idxW h * 4 + tierW h * 2)) d v <;> rfl

theorem instLamW_hit (h1 : d + 1 ≠ 0) (hr : mfindG imSch m h d ≠ [])
    (hh : (mfindG imSch m h d).headD 0 ≠ 0) :
    instLamW (n + 1) m h d v =
      some (rdW (m.arr64 IMEMO) ((mfindG imSch m h d).tail.headD 0 * 4 + 3), m) := by
  rw [instLamW]; simp only [h1, hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]

theorem instLamW_miss (h1 : d + 1 ≠ 0) (hr : mfindG imSch m h d ≠ [])
    (hh : (mfindG imSch m h d).headD 0 = 0)
    (hvk : viewOK m h 28) :
    instLamW (n + 1) m h d v =
      ilamK₁ n h d v (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2 + 1))
        (instW n m (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2)) d v) := by
  rw [instLamW]; simp only [h1, hr, hh, ↓reduceIte, ne_eq, not_true_eq_false, hvk.1, ↓reduceIte, UInt64.not_le.mpr hvk.2]
  cases instW n m (rdW (m.arr64 LAREC) (idxW h * 4 + tierW h * 2)) d v <;> rfl

theorem instForallW_hit (h1 : d + 1 ≠ 0) (hr : mfindG imSch m h d ≠ [])
    (hh : (mfindG imSch m h d).headD 0 ≠ 0) :
    instForallW (n + 1) m h d v =
      some (rdW (m.arr64 IMEMO) ((mfindG imSch m h d).tail.headD 0 * 4 + 3), m) := by
  rw [instForallW]; simp only [h1, hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]

theorem instForallW_miss (h1 : d + 1 ≠ 0) (hr : mfindG imSch m h d ≠ [])
    (hh : (mfindG imSch m h d).headD 0 = 0)
    (hvk : viewOK m h 30) :
    instForallW (n + 1) m h d v =
      ifaK₁ n h d v (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2 + 1))
        (instW n m (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2)) d v) := by
  rw [instForallW]; simp only [h1, hr, hh, ↓reduceIte, ne_eq, not_true_eq_false, hvk.1, ↓reduceIte, UInt64.not_le.mpr hvk.2]
  cases instW n m (rdW (m.arr64 FAREC) (idxW h * 4 + tierW h * 2)) d v <;> rfl

theorem instLetW_hit (h1 : d + 1 ≠ 0) (hr : mfindG imSch m h d ≠ [])
    (hh : (mfindG imSch m h d).headD 0 ≠ 0) :
    instLetW (n + 1) m h d v =
      some (rdW (m.arr64 IMEMO) ((mfindG imSch m h d).tail.headD 0 * 4 + 3), m) := by
  rw [instLetW]; simp only [h1, hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]

theorem instLetW_miss (h1 : d + 1 ≠ 0) (hr : mfindG imSch m h d ≠ [])
    (hh : (mfindG imSch m h d).headD 0 = 0)
    (hvk : viewOK m h 20) :
    instLetW (n + 1) m h d v =
      ileK₁ n h d v (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 1))
        (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 2))
        (instW n m (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3)) d v) := by
  rw [instLetW]; simp only [h1, hr, hh, ↓reduceIte, ne_eq, not_true_eq_false, hvk.1, ↓reduceIte, UInt64.not_le.mpr hvk.2]
  cases instW n m (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3)) d v with
  | none => rfl
  | some p =>
    obtain ⟨x, m₁⟩ := p
    cases instW n m₁ (rdW (m.arr64 LEREC) (idxW h * 6 + tierW h * 3 + 1)) d v <;> rfl

theorem instProjW_hit (hr : mfindG imSch m h d ≠ []) (hh : (mfindG imSch m h d).headD 0 ≠ 0) :
    instProjW (n + 1) m h d v =
      some (rdW (m.arr64 IMEMO) ((mfindG imSch m h d).tail.headD 0 * 4 + 3), m) := by
  rw [instProjW]; simp only [hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]

theorem instProjW_miss (hr : mfindG imSch m h d ≠ []) (hh : (mfindG imSch m h d).headD 0 = 0)
    (hvk : viewOK m h 32) :
    instProjW (n + 1) m h d v =
      ipjK₁ h d (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3))
        (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 1))
        (instW n m (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 2)) d v) := by
  rw [instProjW]; simp only [hr, hh, ↓reduceIte, ne_eq, not_true_eq_false, hvk.1, ↓reduceIte, UInt64.not_le.mpr hvk.2]
  cases instW n m (rdW (m.arr64 PJREC) (idxW h * 6 + tierW h * 3 + 2)) d v <;> rfl

end arms

grind_pattern [arena_grind] instW_cut => instW (n + 1) m h d v
grind_pattern [arena_grind] instW_app => instW (n + 1) m h d v
grind_pattern [arena_grind] instW_lam => instW (n + 1) m h d v
grind_pattern [arena_grind] instW_forall => instW (n + 1) m h d v
grind_pattern [arena_grind] instW_let => instW (n + 1) m h d v
grind_pattern [arena_grind] instW_proj => instW (n + 1) m h d v
grind_pattern [arena_grind] instW_bvar_eq => instW (n + 1) m h d v
grind_pattern [arena_grind] instW_bvar_gt => instW (n + 1) m h d v
grind_pattern [arena_grind] instW_bvar_lt => instW (n + 1) m h d v
grind_pattern [arena_grind] instW_leaf => instW (n + 1) m h d v
grind_pattern [arena_grind] instAppW_hit => instAppW (n + 1) m h d v
grind_pattern [arena_grind] instAppW_miss => instAppW (n + 1) m h d v
grind_pattern [arena_grind] instLamW_hit => instLamW (n + 1) m h d v
grind_pattern [arena_grind] instLamW_miss => instLamW (n + 1) m h d v
grind_pattern [arena_grind] instForallW_hit => instForallW (n + 1) m h d v
grind_pattern [arena_grind] instForallW_miss => instForallW (n + 1) m h d v
grind_pattern [arena_grind] instLetW_hit => instLetW (n + 1) m h d v
grind_pattern [arena_grind] instLetW_miss => instLetW (n + 1) m h d v
grind_pattern [arena_grind] instProjW_hit => instProjW (n + 1) m h d v
grind_pattern [arena_grind] instProjW_miss => instProjW (n + 1) m h d v

/-! ## The L code -/

def instGo : FunDecl := lfn (h, d, v) locals (x, g, t, i, r) {
  x := call der_b(h);
  if x < 32767 && x <= d { return h };
  g := h >> 28;
  if g == 4 { r := call inst_app(h, d, v); return r };
  if g == 5 { r := call inst_lam(h, d, v); return r };
  if g == 6 { r := call inst_forall(h, d, v); return r };
  if g == 0 {
    t := (h >> 27) & 1;
    i := h & 134217727;
    if t != 0 && CTL.u64[1] == 0 { abort };
    if CTL.u64[22 + t] <= i { abort };
    x := BREC.u64[i * 2 + t];
    if x == d { return v };
    if d < x { r := call intern_bvar(x - 1); return r };
    return h
  };
  if g == 7 { r := call inst_let(h, d, v); return r };
  if g == 9 { r := call inst_proj(h, d, v); return r };
  return h
}

def instApp : FunDecl := lfn (h, d, v) locals (fd, j, e0, t, i, f, a, x, y, r, u) {
  (fd, j, e0) := call if_find(h, d);
  if fd != 0 { return IMEMO.u64[j * 4 + 3] };
  t := (h >> 27) & 1;
  i := h & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[4 + t] <= i { abort };
  f := AREC.u64[i * 4 + t * 2];
  a := AREC.u64[i * 4 + t * 2 + 1];
  x := call inst_go(f, d, v);
  y := call inst_go(a, d, v);
  r := call mk_app(x, y);
  (fd, j, e0) := call if_find(h, d);
  u := call if_put(h, d, r, fd, j);
  return r
}

def instLam : FunDecl := lfn (h, d, v) locals (fd, j, e0, t, i, f, a, x, y, r, u) {
  if d + 1 == 0 { abort };
  (fd, j, e0) := call if_find(h, d);
  if fd != 0 { return IMEMO.u64[j * 4 + 3] };
  t := (h >> 27) & 1;
  i := h & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[28 + t] <= i { abort };
  f := LAREC.u64[i * 4 + t * 2];
  a := LAREC.u64[i * 4 + t * 2 + 1];
  x := call inst_go(f, d, v);
  y := call inst_go(a, d + 1, v);
  r := call mk_lam(x, y);
  (fd, j, e0) := call if_find(h, d);
  u := call if_put(h, d, r, fd, j);
  return r
}

def instForall : FunDecl := lfn (h, d, v) locals (fd, j, e0, t, i, f, a, x, y, r, u) {
  if d + 1 == 0 { abort };
  (fd, j, e0) := call if_find(h, d);
  if fd != 0 { return IMEMO.u64[j * 4 + 3] };
  t := (h >> 27) & 1;
  i := h & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[30 + t] <= i { abort };
  f := FAREC.u64[i * 4 + t * 2];
  a := FAREC.u64[i * 4 + t * 2 + 1];
  x := call inst_go(f, d, v);
  y := call inst_go(a, d + 1, v);
  r := call mk_forall(x, y);
  (fd, j, e0) := call if_find(h, d);
  u := call if_put(h, d, r, fd, j);
  return r
}

def instLet : FunDecl := lfn (h, d, v) locals (fd, j, e0, t, i, f, a, b, x, y, z, r, u) {
  if d + 1 == 0 { abort };
  (fd, j, e0) := call if_find(h, d);
  if fd != 0 { return IMEMO.u64[j * 4 + 3] };
  t := (h >> 27) & 1;
  i := h & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[20 + t] <= i { abort };
  f := LEREC.u64[i * 6 + t * 3];
  a := LEREC.u64[i * 6 + t * 3 + 1];
  b := LEREC.u64[i * 6 + t * 3 + 2];
  x := call inst_go(f, d, v);
  y := call inst_go(a, d, v);
  z := call inst_go(b, d + 1, v);
  r := call mk_let(x, y, z);
  (fd, j, e0) := call if_find(h, d);
  u := call if_put(h, d, r, fd, j);
  return r
}

def instProj : FunDecl := lfn (h, d, v) locals (fd, j, e0, t, i, nm, ix, e, x, r, u) {
  (fd, j, e0) := call if_find(h, d);
  if fd != 0 { return IMEMO.u64[j * 4 + 3] };
  t := (h >> 27) & 1;
  i := h & 134217727;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CTL.u64[32 + t] <= i { abort };
  nm := PJREC.u64[i * 6 + t * 3];
  ix := PJREC.u64[i * 6 + t * 3 + 1];
  e := PJREC.u64[i * 6 + t * 3 + 2];
  x := call inst_go(e, d, v);
  r := call mk_proj(nm, ix, x);
  (fd, j, e0) := call if_find(h, d);
  u := call if_put(h, d, r, fd, j);
  return r
}

/-! ## The program and its specs -/

/-- What the specs need of the program. -/
structure InstProg (p : Prog) : Prop where
  base : LiftProg p
  iff : p.lookup "if_find" = some (memoFindG imSch)
  ifp : p.lookup "if_put" = some (memoPutG imSch)
  ifc : p.lookup "if_clear" = some (memoClearG imSch)
  go : p.lookup "inst_go" = some instGo
  app : p.lookup "inst_app" = some instApp
  lam : p.lookup "inst_lam" = some instLam
  fa : p.lookup "inst_forall" = some instForall
  le : p.lookup "inst_let" = some instLet
  pj : p.lookup "inst_proj" = some instProj

section specs
variable (p : Prog) (hp : InstProg p)

/-- The spec of `inst_go` at fuel `n`. -/
def InstGoSpec (n : Nat) : Prop := ∀ (s₀ : St) (h d v : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "inst_go" [h, d, v]
    ⦃fun r s' => LocEq s' s₀ ∧ instW n s₀.mem h d v = some (r.headD 0, s'.mem); ⊤⦄

/-- The specs of the five arms at fuel `n`. -/
def InstArmSpec (n : Nat) : Prop := ∀ (s₀ : St) (h d v : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "inst_app" [h, d, v]
    ⦃fun r s' => LocEq s' s₀ ∧ instAppW n s₀.mem h d v = some (r.headD 0, s'.mem); ⊤⦄ ∧
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "inst_lam" [h, d, v]
    ⦃fun r s' => LocEq s' s₀ ∧ instLamW n s₀.mem h d v = some (r.headD 0, s'.mem); ⊤⦄ ∧
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "inst_forall" [h, d, v]
    ⦃fun r s' => LocEq s' s₀ ∧ instForallW n s₀.mem h d v = some (r.headD 0, s'.mem); ⊤⦄ ∧
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "inst_let" [h, d, v]
    ⦃fun r s' => LocEq s' s₀ ∧ instLetW n s₀.mem h d v = some (r.headD 0, s'.mem); ⊤⦄ ∧
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "inst_proj" [h, d, v]
    ⦃fun r s' => LocEq s' s₀ ∧ instProjW n s₀.mem h d v = some (r.headD 0, s'.mem); ⊤⦄

include hp in
theorem instGo_step (n : Nat) (ih : InstArmSpec p n) : InstGoSpec p (n + 1) := by
  intro s₀ h d v
  have ihA := fun s h d v => (ih s h d v).1
  have ihL := fun s h d v => (ih s h d v).2.1
  have ihF := fun s h d v => (ih s h d v).2.2.1
  have ihE := fun s h d v => (ih s h d v).2.2.2.1
  have ihP := fun s h d v => (ih s h d v).2.2.2.2
  rw [invoke_eq _ hp.go]
  simp only [callFn, instGo]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, derB_spec p hp.base.derb n,
      internBVar_spec p hp.base.bvf hp.base.bvp hp.base.bvi n, ihA, ihL, ihF, ihE, ihP] <;>
    finish [viewOK, tierW, idxW]

end specs

end L.Arena
