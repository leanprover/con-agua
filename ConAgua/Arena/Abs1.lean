module

public import ConAgua.Arena.Inst1Spec
public import ConAgua.Arena.FVarRange
public import ConAgua.L.ProgHas
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
import ConAgua.Census.Attr

@[expose] public section

/-!
# `abstract1`: close a binder body, on `Inst1.lean`'s scaffolding

con-ron's `abstract1Go` (Lean twin `Arena/ExprOps.lean`) and its entry `abstract1Fast`: replace
`fvar d` by `bvar k`, bumping `k` under binders, memoized per `(node, k)` in `abs1C`, rebuilding
through the store. Differences from `instantiate1` (`Inst1.lean`, with `d ↦ k`, `v ↦ d`):

* **The cut-off is `fvarB ≤ d`** (`ab_fvb`): the packed fvar range (`der_b`'s second result,
  `derFW`), or, on the saturated branch alone (`= 32767`), the exact memoized `fr_memo`
  (`fvarRangeMemo`, `FVarRange.lean`), which clears and refills its own memo `fvarBC`.
* **The dispatch is its own function** (`ab_node`), because the cut-off's model has a memory
  effect (`fr_memo`): `abs_go(h, k, d, fu)` is `if fu == 0 { abort }; x := ab_fvb(h, fu - 1);
  if x <= d { return h }; return ab_node(h, k, d, fu - 1)`.
* **The depth counter `fu`** is the twin's `fuel` exactly: `abstract1Go` fails at
  `0`, else reads `fvarB fuel h` and runs its arms at the decremented `fuel`; every arm passes the
  same `fu` to its children, `ab_fvb(h, fu)` passes it to `fr_memo`.
* **The `fvar` arm** reads the record's index word (`viewFVarIdx`): `idx = d` gives
  `intern_bvar(k)`, else `h`.
* **The arms rebuild only on change** (`internRebuilt*`: `h` itself when every child came back
  equal), `rbAppW` … below.
* **The memo `abs1C`** is a new table: array 49 `ABMEMO`, stamp `CTL[48]`, count `CTL[49]`,
  `lfKey`'s two-word key codec. It is not in `MemosR` (`scratch_enter` clears the memos of
  `MemosR` by name, `abs1C` is not one of them; DESIGN.md, lane `exprops3`): the refinement keeps
  it in a tier of its own (`Abs1Refine.lean`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The slots of `abstract1`'s memo (`abs1C`, keys `(handle, k)`). -/
abbrev ABMEMO : ArrId := 49

/-- `abs1C`: array 49, stamp `CTL[48]`, count `CTL[49]`. -/
abbrev abSch : MemoSch := ⟨ABMEMO, 48⟩

/-! ## The models -/

/-- **The model of `fr_memo` at L fuel `n`** (the call's own fuel; `frMemo_spec` is at `n + 1`). -/
def fvbN : Nat → Mem → Word → Word → Option (Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, h, fu => frMemoW n m h fu

/-- **The model of `ab_fvb`** (con-ron's `fvarB`): the packed fvar range, or `fr_memo` on the
saturated branch. -/
def fvbW : Nat → Mem → Word → Word → Option (Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, h, fu => if derFW m h = 32767 then fvbN n m h fu else some (derFW m h, m)

/-- Record `r` at `(h, k)` in the `abstract1` memo and return it. -/
def asetK (h k : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m₁) =>
    match msetG abSch m₁ h k r with
    | none => none
    | some m₂ => some (r, m₂)

/-- `internRebuiltApp`: `h` itself when both children came back equal, else `mk_app`. -/
def rbAppW (m : Mem) (h f a x y : Word) : Option (Word × Mem) :=
  if x = f ∧ y = a then some (h, m) else mkAppW m x y
def rbLamW (m : Mem) (h f a x y : Word) : Option (Word × Mem) :=
  if x = f ∧ y = a then some (h, m) else mkLamW m x y
def rbForallW (m : Mem) (h f a x y : Word) : Option (Word × Mem) :=
  if x = f ∧ y = a then some (h, m) else mkForallW m x y
def rbLetW (m : Mem) (h f a b x y z : Word) : Option (Word × Mem) :=
  if x = f ∧ y = a ∧ z = b then some (h, m) else mkLetW m x y z
def rbProjW (m : Mem) (h nw iw e x : Word) : Option (Word × Mem) :=
  if x = e then some (h, m) else mkProjW m nw iw x

mutual
/-- **The model of `abs_go`** at L fuel `n`: the cut-off, then `ab_node`. -/
def absW : Nat → Mem → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, h, k, d, fu =>
    if fu = 0 then none
    else match fvbW n m h (fu - 1) with
    | none => none
    | some (x, m₁) => if x ≤ d then some (h, m₁) else absNodeW n m₁ h k d (fu - 1)

/-- **The model of `ab_node`**: the dispatch on the tag (the leaves and unknown tags return `h`
without reading the store; `fvar` inline). -/
def absNodeW : Nat → Mem → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, h, k, d, fu =>
    if h >>> 28 = 4 then absAppW n m h k d fu
    else if h >>> 28 = 5 then absLamW n m h k d fu
    else if h >>> 28 = 6 then absForallW n m h k d fu
    else if h >>> 28 = 1 then
      if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
      else if tcnt m FVAR (tierW h) ≤ idxW h then none
      else if tfld m FVAR (tierW h) (idxW h) 0 = d then binternW m k
      else some (h, m)
    else if h >>> 28 = 7 then absLetW n m h k d fu
    else if h >>> 28 = 9 then absProjW n m h k d fu
    else some (h, m)

/-- **The model of `abs_app`.** -/
def absAppW : Nat → Mem → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, h, k, d, fu =>
    if mfindG abSch m h k = [] then none
    else if (mfindG abSch m h k).headD 0 ≠ 0 then
      some (rdW (m.arr64 ABMEMO) ((mfindG abSch m h k).tail.headD 0 * 4 + 3), m)
    else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if tcnt m APP (tierW h) ≤ idxW h then none
    else
      match absW n m (tfld m APP (tierW h) (idxW h) 0) k d fu with
      | none => none
      | some (x, m₁) =>
        match absW n m₁ (tfld m APP (tierW h) (idxW h) 1) k d fu with
        | none => none
        | some (y, m₂) =>
          asetK h k (rbAppW m₂ h (tfld m APP (tierW h) (idxW h) 0)
            (tfld m APP (tierW h) (idxW h) 1) x y)

/-- **The model of `abs_lam`.** -/
def absLamW : Nat → Mem → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, h, k, d, fu =>
    if k + 1 = 0 then none
    else if mfindG abSch m h k = [] then none
    else if (mfindG abSch m h k).headD 0 ≠ 0 then
      some (rdW (m.arr64 ABMEMO) ((mfindG abSch m h k).tail.headD 0 * 4 + 3), m)
    else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if tcnt m LAM (tierW h) ≤ idxW h then none
    else
      match absW n m (tfld m LAM (tierW h) (idxW h) 0) k d fu with
      | none => none
      | some (x, m₁) =>
        match absW n m₁ (tfld m LAM (tierW h) (idxW h) 1) (k + 1) d fu with
        | none => none
        | some (y, m₂) =>
          asetK h k (rbLamW m₂ h (tfld m LAM (tierW h) (idxW h) 0)
            (tfld m LAM (tierW h) (idxW h) 1) x y)

/-- **The model of `abs_forall`.** -/
def absForallW : Nat → Mem → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, h, k, d, fu =>
    if k + 1 = 0 then none
    else if mfindG abSch m h k = [] then none
    else if (mfindG abSch m h k).headD 0 ≠ 0 then
      some (rdW (m.arr64 ABMEMO) ((mfindG abSch m h k).tail.headD 0 * 4 + 3), m)
    else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if tcnt m FORALL (tierW h) ≤ idxW h then none
    else
      match absW n m (tfld m FORALL (tierW h) (idxW h) 0) k d fu with
      | none => none
      | some (x, m₁) =>
        match absW n m₁ (tfld m FORALL (tierW h) (idxW h) 1) (k + 1) d fu with
        | none => none
        | some (y, m₂) =>
          asetK h k (rbForallW m₂ h (tfld m FORALL (tierW h) (idxW h) 0)
            (tfld m FORALL (tierW h) (idxW h) 1) x y)

/-- **The model of `abs_let`.** -/
def absLetW : Nat → Mem → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, h, k, d, fu =>
    if k + 1 = 0 then none
    else if mfindG abSch m h k = [] then none
    else if (mfindG abSch m h k).headD 0 ≠ 0 then
      some (rdW (m.arr64 ABMEMO) ((mfindG abSch m h k).tail.headD 0 * 4 + 3), m)
    else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if tcnt m LET (tierW h) ≤ idxW h then none
    else
      match absW n m (tfld m LET (tierW h) (idxW h) 0) k d fu with
      | none => none
      | some (x, m₁) =>
        match absW n m₁ (tfld m LET (tierW h) (idxW h) 1) k d fu with
        | none => none
        | some (y, m₂) =>
          match absW n m₂ (tfld m LET (tierW h) (idxW h) 2) (k + 1) d fu with
          | none => none
          | some (z, m₃) =>
            asetK h k (rbLetW m₃ h (tfld m LET (tierW h) (idxW h) 0)
              (tfld m LET (tierW h) (idxW h) 1)
              (tfld m LET (tierW h) (idxW h) 2) x y z)

/-- **The model of `abs_proj`.** -/
def absProjW : Nat → Mem → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _ => none
  | n + 1, m, h, k, d, fu =>
    if mfindG abSch m h k = [] then none
    else if (mfindG abSch m h k).headD 0 ≠ 0 then
      some (rdW (m.arr64 ABMEMO) ((mfindG abSch m h k).tail.headD 0 * 4 + 3), m)
    else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if tcnt m PROJ (tierW h) ≤ idxW h then none
    else
      match absW n m (tfld m PROJ (tierW h) (idxW h) 2) k d fu with
      | none => none
      | some (x, m₁) =>
        asetK h k (rbProjW m₁ h (tfld m PROJ (tierW h) (idxW h) 0)
          (tfld m PROJ (tierW h) (idxW h) 1)
          (tfld m PROJ (tierW h) (idxW h) 2) x)
end

/-! ### Continuations and guarded equations -/

/-- After the cut-off. -/
def acutK (n : Nat) (h k d fu : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => if x ≤ d then some (h, m₁) else absNodeW n m₁ h k d fu

/-- The arms after each child. -/
def aappK₁ (n : Nat) (h k d fu fw aw : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => aappK₂ h k fw aw x (absW n m₁ aw k d fu)
where aappK₂ (h k fw aw x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) => asetK h k (rbAppW m₂ h fw aw x y)

def alamK₁ (n : Nat) (h k d fu fw bw : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => alamK₂ h k fw bw x (absW n m₁ bw (k + 1) d fu)
where alamK₂ (h k fw bw x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) => asetK h k (rbLamW m₂ h fw bw x y)

def afaK₁ (n : Nat) (h k d fu fw bw : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => afaK₂ h k fw bw x (absW n m₁ bw (k + 1) d fu)
where afaK₂ (h k fw bw x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) => asetK h k (rbForallW m₂ h fw bw x y)

def aleK₁ (n : Nat) (h k d fu fw vw bw : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => aleK₂ n h k d fu fw vw bw x (absW n m₁ vw k d fu)
where
  aleK₂ (n : Nat) (h k d fu fw vw bw x : Word) : Option (Word × Mem) → Option (Word × Mem)
    | none => none
    | some (y, m₂) => aleK₃ h k fw vw bw x y (absW n m₂ bw (k + 1) d fu)
  aleK₃ (h k fw vw bw x y : Word) : Option (Word × Mem) → Option (Word × Mem)
    | none => none
    | some (z, m₃) => asetK h k (rbLetW m₃ h fw vw bw x y z)

def apjK₁ (h k nw iw ew : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => asetK h k (rbProjW m₁ h nw iw ew x)

section aks
variable (n : Nat) (h k d fu fw aw bw vw nw iw ew x y z : Word) (m₁ m₂ m₃ : Mem)
theorem acutK_some : acutK n h k d fu (some (x, m₁)) =
    if x ≤ d then some (h, m₁) else absNodeW n m₁ h k d fu := rfl
theorem aappK₁_some : aappK₁ n h k d fu fw aw (some (x, m₁)) =
    aappK₁.aappK₂ h k fw aw x (absW n m₁ aw k d fu) := rfl
theorem aappK₂_some : aappK₁.aappK₂ h k fw aw x (some (y, m₂)) = asetK h k (rbAppW m₂ h fw aw x y) :=
  rfl
theorem alamK₁_some : alamK₁ n h k d fu fw bw (some (x, m₁)) =
    alamK₁.alamK₂ h k fw bw x (absW n m₁ bw (k + 1) d fu) := rfl
theorem alamK₂_some : alamK₁.alamK₂ h k fw bw x (some (y, m₂)) = asetK h k (rbLamW m₂ h fw bw x y) :=
  rfl
theorem afaK₁_some : afaK₁ n h k d fu fw bw (some (x, m₁)) =
    afaK₁.afaK₂ h k fw bw x (absW n m₁ bw (k + 1) d fu) := rfl
theorem afaK₂_some : afaK₁.afaK₂ h k fw bw x (some (y, m₂)) =
    asetK h k (rbForallW m₂ h fw bw x y) := rfl
theorem aleK₁_some : aleK₁ n h k d fu fw vw bw (some (x, m₁)) =
    aleK₁.aleK₂ n h k d fu fw vw bw x (absW n m₁ vw k d fu) := rfl
theorem aleK₂_some : aleK₁.aleK₂ n h k d fu fw vw bw x (some (y, m₂)) =
    aleK₁.aleK₃ h k fw vw bw x y (absW n m₂ bw (k + 1) d fu) := rfl
theorem aleK₃_some : aleK₁.aleK₃ h k fw vw bw x y (some (z, m₃)) =
    asetK h k (rbLetW m₃ h fw vw bw x y z) := rfl
theorem apjK₁_some : apjK₁ h k nw iw ew (some (x, m₁)) = asetK h k (rbProjW m₁ h nw iw ew x) := rfl
theorem asetK_some (r : Word) :
    asetK h k (some (r, m₁)) =
      (match msetG abSch m₁ h k r with | none => none | some m₂ => some (r, m₂)) := rfl
theorem rbAppW_same (hx : x = fw) (hy : y = aw) : rbAppW m₁ h fw aw x y = some (h, m₁) := by
  simp [rbAppW, hx, hy]
theorem rbAppW_new (hn : ¬ (x = fw ∧ y = aw)) : rbAppW m₁ h fw aw x y = mkAppW m₁ x y := by
  simp only [rbAppW, hn, ↓reduceIte]
theorem rbLamW_same (hx : x = fw) (hy : y = aw) : rbLamW m₁ h fw aw x y = some (h, m₁) := by
  simp [rbLamW, hx, hy]
theorem rbLamW_new (hn : ¬ (x = fw ∧ y = aw)) : rbLamW m₁ h fw aw x y = mkLamW m₁ x y := by
  simp only [rbLamW, hn, ↓reduceIte]
theorem rbForallW_same (hx : x = fw) (hy : y = aw) : rbForallW m₁ h fw aw x y = some (h, m₁) := by
  simp [rbForallW, hx, hy]
theorem rbForallW_new (hn : ¬ (x = fw ∧ y = aw)) : rbForallW m₁ h fw aw x y = mkForallW m₁ x y := by
  simp only [rbForallW, hn, ↓reduceIte]
theorem rbLetW_same (hx : x = fw) (hy : y = vw) (hz : z = bw) :
    rbLetW m₁ h fw vw bw x y z = some (h, m₁) := by
  simp [rbLetW, hx, hy, hz]
theorem rbLetW_new (hn : ¬ (x = fw ∧ y = vw ∧ z = bw)) :
    rbLetW m₁ h fw vw bw x y z = mkLetW m₁ x y z := by
  simp only [rbLetW, hn, ↓reduceIte]
theorem rbProjW_same (hx : x = ew) : rbProjW m₁ h nw iw ew x = some (h, m₁) := by
  simp [rbProjW, hx]
theorem rbProjW_new (hn : ¬ x = ew) : rbProjW m₁ h nw iw ew x = mkProjW m₁ nw iw x := by
  simp only [rbProjW, hn, ↓reduceIte]
end aks

attribute [arena_grind =] acutK_some aappK₁_some aappK₂_some alamK₁_some alamK₂_some afaK₁_some
  afaK₂_some aleK₁_some aleK₂_some aleK₃_some apjK₁_some asetK_some

grind_pattern [arena_grind] rbAppW_same => rbAppW m₁ h fw aw x y
grind_pattern [arena_grind] rbAppW_new => rbAppW m₁ h fw aw x y
grind_pattern [arena_grind] rbLamW_same => rbLamW m₁ h fw aw x y
grind_pattern [arena_grind] rbLamW_new => rbLamW m₁ h fw aw x y
grind_pattern [arena_grind] rbForallW_same => rbForallW m₁ h fw aw x y
grind_pattern [arena_grind] rbForallW_new => rbForallW m₁ h fw aw x y
grind_pattern [arena_grind] rbLetW_same => rbLetW m₁ h fw vw bw x y z
grind_pattern [arena_grind] rbLetW_new => rbLetW m₁ h fw vw bw x y z
grind_pattern [arena_grind] rbProjW_same => rbProjW m₁ h nw iw ew x
grind_pattern [arena_grind] rbProjW_new => rbProjW m₁ h nw iw ew x

section arms
variable (n : Nat) (m : Mem) (h k d fu : Word)

theorem fvbN_succ : fvbN (n + 1) m h fu = frMemoW n m h fu := rfl

theorem fvbW_sat (hs : derFW m h = 32767) : fvbW (n + 1) m h fu = fvbN n m h fu := by
  simp [fvbW, hs]

theorem fvbW_pk (hs : derFW m h ≠ 32767) : fvbW (n + 1) m h fu = some (derFW m h, m) := by
  simp [fvbW, hs]

theorem absW_eq (hf : fu ≠ 0) :
    absW (n + 1) m h k d fu = acutK n h k d (fu - 1) (fvbW n m h (fu - 1)) := by
  rw [absW]; simp only [hf, ↓reduceIte]; cases fvbW n m h (fu - 1) <;> rfl

theorem absNodeW_app (hg : h >>> 28 = 4) : absNodeW (n + 1) m h k d fu = absAppW n m h k d fu := by
  rw [absNodeW]; simp [hg]

theorem absNodeW_lam (hg : h >>> 28 = 5) : absNodeW (n + 1) m h k d fu = absLamW n m h k d fu := by
  rw [absNodeW]; simp [hg]

theorem absNodeW_forall (hg : h >>> 28 = 6) : absNodeW (n + 1) m h k d fu = absForallW n m h k d fu := by
  rw [absNodeW]; simp [hg]

theorem absNodeW_let (hg : h >>> 28 = 7) : absNodeW (n + 1) m h k d fu = absLetW n m h k d fu := by
  rw [absNodeW]; simp [hg]

theorem absNodeW_proj (hg : h >>> 28 = 9) : absNodeW (n + 1) m h k d fu = absProjW n m h k d fu := by
  rw [absNodeW]; simp [hg]

theorem absNodeW_fvar_eq (hv : viewOK m h FVAR) (hg : h >>> 28 = 1)
    (he : tfld m FVAR (tierW h) (idxW h) 0 = d) :
    absNodeW (n + 1) m h k d fu = binternW m k := by
  rw [absNodeW]; simp [hv.1, hg, UInt64.not_le.mpr hv.2, he]

theorem absNodeW_fvar_ne (hv : viewOK m h FVAR) (hg : h >>> 28 = 1)
    (he : tfld m FVAR (tierW h) (idxW h) 0 ≠ d) :
    absNodeW (n + 1) m h k d fu = some (h, m) := by
  rw [absNodeW]; simp [hv.1, hg, UInt64.not_le.mpr hv.2, he]

theorem absNodeW_leaf (h1 : h >>> 28 ≠ 1)
    (h4 : h >>> 28 ≠ 4) (h5 : h >>> 28 ≠ 5) (h6 : h >>> 28 ≠ 6) (h7 : h >>> 28 ≠ 7)
    (h9 : h >>> 28 ≠ 9) : absNodeW (n + 1) m h k d fu = some (h, m) := by
  rw [absNodeW]; simp [h1, h4, h5, h6, h7, h9]

theorem absAppW_hit (hr : mfindG abSch m h k ≠ []) (hh : (mfindG abSch m h k).headD 0 ≠ 0) :
    absAppW (n + 1) m h k d fu =
      some (rdW (m.arr64 ABMEMO) ((mfindG abSch m h k).tail.headD 0 * 4 + 3), m) := by
  rw [absAppW]; simp only [hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]

theorem absAppW_miss (hr : mfindG abSch m h k ≠ []) (hh : (mfindG abSch m h k).headD 0 = 0)
    (hvk : viewOK m h APP) :
    absAppW (n + 1) m h k d fu =
      aappK₁ n h k d fu (tfld m APP (tierW h) (idxW h) 0)
        (tfld m APP (tierW h) (idxW h) 1)
        (absW n m (tfld m APP (tierW h) (idxW h) 0) k d fu) := by
  rw [absAppW]; simp only [hr, hh, ↓reduceIte, ne_eq, not_true_eq_false, hvk.1, ↓reduceIte, UInt64.not_le.mpr hvk.2]
  cases absW n m (tfld m APP (tierW h) (idxW h) 0) k d fu <;> rfl

theorem absLamW_hit (h1 : k + 1 ≠ 0) (hr : mfindG abSch m h k ≠ [])
    (hh : (mfindG abSch m h k).headD 0 ≠ 0) :
    absLamW (n + 1) m h k d fu =
      some (rdW (m.arr64 ABMEMO) ((mfindG abSch m h k).tail.headD 0 * 4 + 3), m) := by
  rw [absLamW]; simp only [h1, hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]

theorem absLamW_miss (h1 : k + 1 ≠ 0) (hr : mfindG abSch m h k ≠ [])
    (hh : (mfindG abSch m h k).headD 0 = 0) (hvk : viewOK m h LAM) :
    absLamW (n + 1) m h k d fu =
      alamK₁ n h k d fu (tfld m LAM (tierW h) (idxW h) 0)
        (tfld m LAM (tierW h) (idxW h) 1)
        (absW n m (tfld m LAM (tierW h) (idxW h) 0) k d fu) := by
  rw [absLamW]; simp only [h1, hr, hh, ↓reduceIte, ne_eq, not_true_eq_false, hvk.1, ↓reduceIte, UInt64.not_le.mpr hvk.2]
  cases absW n m (tfld m LAM (tierW h) (idxW h) 0) k d fu <;> rfl

theorem absForallW_hit (h1 : k + 1 ≠ 0) (hr : mfindG abSch m h k ≠ [])
    (hh : (mfindG abSch m h k).headD 0 ≠ 0) :
    absForallW (n + 1) m h k d fu =
      some (rdW (m.arr64 ABMEMO) ((mfindG abSch m h k).tail.headD 0 * 4 + 3), m) := by
  rw [absForallW]; simp only [h1, hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]

theorem absForallW_miss (h1 : k + 1 ≠ 0) (hr : mfindG abSch m h k ≠ [])
    (hh : (mfindG abSch m h k).headD 0 = 0) (hvk : viewOK m h FORALL) :
    absForallW (n + 1) m h k d fu =
      afaK₁ n h k d fu (tfld m FORALL (tierW h) (idxW h) 0)
        (tfld m FORALL (tierW h) (idxW h) 1)
        (absW n m (tfld m FORALL (tierW h) (idxW h) 0) k d fu) := by
  rw [absForallW]; simp only [h1, hr, hh, ↓reduceIte, ne_eq, not_true_eq_false, hvk.1, ↓reduceIte, UInt64.not_le.mpr hvk.2]
  cases absW n m (tfld m FORALL (tierW h) (idxW h) 0) k d fu <;> rfl

theorem absLetW_hit (h1 : k + 1 ≠ 0) (hr : mfindG abSch m h k ≠ [])
    (hh : (mfindG abSch m h k).headD 0 ≠ 0) :
    absLetW (n + 1) m h k d fu =
      some (rdW (m.arr64 ABMEMO) ((mfindG abSch m h k).tail.headD 0 * 4 + 3), m) := by
  rw [absLetW]; simp only [h1, hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]

theorem absLetW_miss (h1 : k + 1 ≠ 0) (hr : mfindG abSch m h k ≠ [])
    (hh : (mfindG abSch m h k).headD 0 = 0) (hvk : viewOK m h LET) :
    absLetW (n + 1) m h k d fu =
      aleK₁ n h k d fu (tfld m LET (tierW h) (idxW h) 0)
        (tfld m LET (tierW h) (idxW h) 1)
        (tfld m LET (tierW h) (idxW h) 2)
        (absW n m (tfld m LET (tierW h) (idxW h) 0) k d fu) := by
  rw [absLetW]; simp only [h1, hr, hh, ↓reduceIte, ne_eq, not_true_eq_false, hvk.1, ↓reduceIte, UInt64.not_le.mpr hvk.2]
  cases absW n m (tfld m LET (tierW h) (idxW h) 0) k d fu with
  | none => rfl
  | some p =>
    obtain ⟨x, m₁⟩ := p
    cases absW n m₁ (tfld m LET (tierW h) (idxW h) 1) k d fu <;> rfl

theorem absProjW_hit (hr : mfindG abSch m h k ≠ []) (hh : (mfindG abSch m h k).headD 0 ≠ 0) :
    absProjW (n + 1) m h k d fu =
      some (rdW (m.arr64 ABMEMO) ((mfindG abSch m h k).tail.headD 0 * 4 + 3), m) := by
  rw [absProjW]; simp only [hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]

theorem absProjW_miss (hr : mfindG abSch m h k ≠ []) (hh : (mfindG abSch m h k).headD 0 = 0)
    (hvk : viewOK m h PROJ) :
    absProjW (n + 1) m h k d fu =
      apjK₁ h k (tfld m PROJ (tierW h) (idxW h) 0)
        (tfld m PROJ (tierW h) (idxW h) 1)
        (tfld m PROJ (tierW h) (idxW h) 2)
        (absW n m (tfld m PROJ (tierW h) (idxW h) 2) k d fu) := by
  rw [absProjW]; simp only [hr, hh, ↓reduceIte, ne_eq, not_true_eq_false, hvk.1, ↓reduceIte, UInt64.not_le.mpr hvk.2]
  cases absW n m (tfld m PROJ (tierW h) (idxW h) 2) k d fu <;> rfl

end arms

grind_pattern [arena_grind] fvbN_succ => fvbN (n + 1) m h fu
grind_pattern [arena_grind] fvbW_sat => fvbW (n + 1) m h fu
grind_pattern [arena_grind] fvbW_pk => fvbW (n + 1) m h fu
grind_pattern [arena_grind] absW_eq => absW (n + 1) m h k d fu
grind_pattern [arena_grind] absNodeW_app => absNodeW (n + 1) m h k d fu
grind_pattern [arena_grind] absNodeW_lam => absNodeW (n + 1) m h k d fu
grind_pattern [arena_grind] absNodeW_forall => absNodeW (n + 1) m h k d fu
grind_pattern [arena_grind] absNodeW_let => absNodeW (n + 1) m h k d fu
grind_pattern [arena_grind] absNodeW_proj => absNodeW (n + 1) m h k d fu
grind_pattern [arena_grind] absNodeW_fvar_eq => absNodeW (n + 1) m h k d fu
grind_pattern [arena_grind] absNodeW_fvar_ne => absNodeW (n + 1) m h k d fu
grind_pattern [arena_grind] absNodeW_leaf => absNodeW (n + 1) m h k d fu
grind_pattern [arena_grind] absAppW_hit => absAppW (n + 1) m h k d fu
grind_pattern [arena_grind] absAppW_miss => absAppW (n + 1) m h k d fu
grind_pattern [arena_grind] absLamW_hit => absLamW (n + 1) m h k d fu
grind_pattern [arena_grind] absLamW_miss => absLamW (n + 1) m h k d fu
grind_pattern [arena_grind] absForallW_hit => absForallW (n + 1) m h k d fu
grind_pattern [arena_grind] absForallW_miss => absForallW (n + 1) m h k d fu
grind_pattern [arena_grind] absLetW_hit => absLetW (n + 1) m h k d fu
grind_pattern [arena_grind] absLetW_miss => absLetW (n + 1) m h k d fu
grind_pattern [arena_grind] absProjW_hit => absProjW (n + 1) m h k d fu
grind_pattern [arena_grind] absProjW_miss => absProjW (n + 1) m h k d fu

/-! ## The L code -/

/-- con-ron: ConRon/Arena/ExprOps.lean:1574-1580 ConRon.Arena.fvarB -/
@[l_impl ConRon.Arena.fvarB]
def abFvb : FunDecl := lfn (h, fu) locals (x, xf, r) {
  (x, xf) := call der_b(h);
  if xf == 32767 { r := call fr_memo(h, fu); return r };
  return xf
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1608-1628 ConRon.Arena.abstract1Go -/
@[l_impl ConRon.Arena.abstract1Go]
def absGo : FunDecl := lfn (h, k, d, fu) locals (x, r) {
  if fu == 0 { abort };
  x := call ab_fvb(h, fu - 1);
  if x <= d { return h };
  r := call ab_node(h, k, d, fu - 1);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1608-1628 ConRon.Arena.abstract1Go
con-ron: ConRon/Arena/ExprOps.lean:1599-1604 ConRon.Arena.abstract1ArmFVar -/
@[l_impl ConRon.Arena.abstract1ArmFVar]
def absNode : FunDecl := lfn (h, k, d, fu) locals (x, g, t, i, r) {
  g := h >> 28;
  if g == 4 { r := call abs_app(h, k, d, fu); return r };
  if g == 5 { r := call abs_lam(h, k, d, fu); return r };
  if g == 6 { r := call abs_forall(h, k, d, fu); return r };
  if g == 1 {
    t := ⟦h⟧.tier;
    i := ⟦h⟧.idx;
    if t != 0 && CTL.u64[1] == 0 { abort };
    if FVAR⟨t⟩.count <= i { abort };
    x := FVAR⟨t, i⟩.i;
    if x == d { r := call intern_bvar(k); return r };
    return h
  };
  if g == 7 { r := call abs_let(h, k, d, fu); return r };
  if g == 9 { r := call abs_proj(h, k, d, fu); return r };
  return h
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1630-1644 ConRon.Arena.abstract1ArmApp -/
@[l_impl ConRon.Arena.abstract1ArmApp]
def absApp : FunDecl := lfn (h, k, d, fu) locals (fd, j, e0, t, i, f, a, x, y, r, u) {
  (fd, j, e0) := call ab_find(h, k);
  if fd != 0 { return ABMEMO.u64[j * 4 + 3] };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if APP⟨t⟩.count <= i { abort };
  f := APP⟨t, i⟩.f;
  a := APP⟨t, i⟩.a;
  x := call abs_go(f, k, d, fu);
  y := call abs_go(a, k, d, fu);
  if x == f && y == a { r := h } else { r := call mk_app(x, y) };
  (fd, j, e0) := call ab_find(h, k);
  u := call ab_put(h, k, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1646-1661 ConRon.Arena.abstract1ArmBind -/
@[l_impl ConRon.Arena.abstract1ArmBind]
def absLam : FunDecl := lfn (h, k, d, fu) locals (fd, j, e0, t, i, f, a, x, y, r, u) {
  if k + 1 == 0 { abort };
  (fd, j, e0) := call ab_find(h, k);
  if fd != 0 { return ABMEMO.u64[j * 4 + 3] };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if LAM⟨t⟩.count <= i { abort };
  f := LAM⟨t, i⟩.ty;
  a := LAM⟨t, i⟩.b;
  x := call abs_go(f, k, d, fu);
  y := call abs_go(a, k + 1, d, fu);
  if x == f && y == a { r := h } else { r := call mk_lam(x, y) };
  (fd, j, e0) := call ab_find(h, k);
  u := call ab_put(h, k, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1646-1661 ConRon.Arena.abstract1ArmBind -/
@[l_impl ConRon.Arena.abstract1ArmBind]
def absForall : FunDecl := lfn (h, k, d, fu) locals (fd, j, e0, t, i, f, a, x, y, r, u) {
  if k + 1 == 0 { abort };
  (fd, j, e0) := call ab_find(h, k);
  if fd != 0 { return ABMEMO.u64[j * 4 + 3] };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if FORALL⟨t⟩.count <= i { abort };
  f := FORALL⟨t, i⟩.ty;
  a := FORALL⟨t, i⟩.b;
  x := call abs_go(f, k, d, fu);
  y := call abs_go(a, k + 1, d, fu);
  if x == f && y == a { r := h } else { r := call mk_forall(x, y) };
  (fd, j, e0) := call ab_find(h, k);
  u := call ab_put(h, k, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1663-1678 ConRon.Arena.abstract1ArmLet -/
@[l_impl ConRon.Arena.abstract1ArmLet]
def absLet : FunDecl := lfn (h, k, d, fu) locals (fd, j, e0, t, i, f, a, b, x, y, z, r, u) {
  if k + 1 == 0 { abort };
  (fd, j, e0) := call ab_find(h, k);
  if fd != 0 { return ABMEMO.u64[j * 4 + 3] };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if LET⟨t⟩.count <= i { abort };
  f := LET⟨t, i⟩.ty;
  a := LET⟨t, i⟩.v;
  b := LET⟨t, i⟩.b;
  x := call abs_go(f, k, d, fu);
  y := call abs_go(a, k, d, fu);
  z := call abs_go(b, k + 1, d, fu);
  if x == f && y == a && z == b { r := h } else { r := call mk_let(x, y, z) };
  (fd, j, e0) := call ab_find(h, k);
  u := call ab_put(h, k, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1680-1694 ConRon.Arena.abstract1ArmProj -/
@[l_impl ConRon.Arena.abstract1ArmProj]
def absProj : FunDecl := lfn (h, k, d, fu) locals (fd, j, e0, t, i, nm, ix, e, x, r, u) {
  (fd, j, e0) := call ab_find(h, k);
  if fd != 0 { return ABMEMO.u64[j * 4 + 3] };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if PROJ⟨t⟩.count <= i { abort };
  nm := PROJ⟨t, i⟩.n;
  ix := PROJ⟨t, i⟩.i;
  e := PROJ⟨t, i⟩.e;
  x := call abs_go(e, k, d, fu);
  if x == e { r := h } else { r := call mk_proj(nm, ix, x) };
  (fd, j, e0) := call ab_find(h, k);
  u := call ab_put(h, k, r, fd, j);
  return r
}

/-! ## The program and its specs -/

/-- The walk without its entry, `fvarRangeProg` and `liftProg` (the `mk_*`, the stores). -/
def absWalkProg : Prog :=
  [("ab_find", memoFindG abSch), ("ab_put", memoPutG abSch), ("ab_clear", memoClearG abSch),
    ("ab_fvb", abFvb), ("abs_go", absGo), ("ab_node", absNode), ("abs_app", absApp),
    ("abs_lam", absLam), ("abs_forall", absForall), ("abs_let", absLet), ("abs_proj", absProj)] ++
  fvarRangeProg ++ liftProg

/-- What the specs need of the program: `absWalkProg`'s functions. -/
def AbsProg (p : Prog) : Prop := ProgHas p absWalkProg

theorem AbsProg.base {p : Prog} (hp : AbsProg p) : LiftProg p := by
  have h : ProgHas p liftProg := hp.right
  unfold LiftProg liftProgFns; repeat (first | exact ProgHas.nil | refine ProgHas.cons (h.get _) ?_)

section specs
variable (p : Prog) (hp : AbsProg p)

include hp in
/-- `fr_memo` at every fuel (`fvbN`: `frMemo_spec`, and fuel `0` aborts). -/
theorem fvbN_spec (n : Nat) (s₀ : St) (h fu : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "fr_memo" [h, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ fvbN n s₀.mem h fu = some (r.headD 0, s'.mem); ⊤⦄ := by
  cases n with
  | zero => rw [invoke_eq _ (hp.get "fr_memo")]; simp only [callFn, frMemo]; vcgen [exec] <;> grind
  | succ n =>
    exact frMemo_spec p (hp.get "fm_find") (hp.get "fm_put") (hp.get "fr_go")
      (hp.get "fr_node") (hp.get "fm_clear") (hp.get "fr_memo") n s₀ h fu

include hp in
theorem abFvb_spec (n : Nat) (s₀ : St) (h fu : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "ab_fvb" [h, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ fvbW n s₀.mem h fu = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ (hp.get "ab_fvb")]
  simp only [callFn, abFvb]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, derB_spec p (hp.get "der_b") n,
        fvbN_spec p hp n] <;>
      finish

/-- The spec of `abs_go` at fuel `n`. -/
def AbsGoSpec (n : Nat) : Prop := ∀ (s₀ : St) (h k d fu : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "abs_go" [h, k, d, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ absW n s₀.mem h k d fu = some (r.headD 0, s'.mem); ⊤⦄

/-- The spec of `ab_node` at fuel `n`. -/
def AbsNodeSpec (n : Nat) : Prop := ∀ (s₀ : St) (h k d fu : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "ab_node" [h, k, d, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ absNodeW n s₀.mem h k d fu = some (r.headD 0, s'.mem); ⊤⦄

/-- The specs of the five arms at fuel `n`. -/
def AbsArmSpec (n : Nat) : Prop := ∀ (s₀ : St) (h k d fu : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "abs_app" [h, k, d, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ absAppW n s₀.mem h k d fu = some (r.headD 0, s'.mem); ⊤⦄ ∧
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "abs_lam" [h, k, d, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ absLamW n s₀.mem h k d fu = some (r.headD 0, s'.mem); ⊤⦄ ∧
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "abs_forall" [h, k, d, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ absForallW n s₀.mem h k d fu = some (r.headD 0, s'.mem); ⊤⦄ ∧
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "abs_let" [h, k, d, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ absLetW n s₀.mem h k d fu = some (r.headD 0, s'.mem); ⊤⦄ ∧
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "abs_proj" [h, k, d, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ absProjW n s₀.mem h k d fu = some (r.headD 0, s'.mem); ⊤⦄

include hp in
theorem absGo_step (n : Nat) (ih : AbsNodeSpec p n) : AbsGoSpec p (n + 1) := by
  unfold AbsNodeSpec at ih
  intro s₀ h k d fu
  rw [invoke_eq _ (hp.get "abs_go")]
  simp only [callFn, absGo]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, abFvb_spec p hp n, ih] <;>
    finish

include hp in
theorem absNode_step (n : Nat) (ih : AbsArmSpec p n) : AbsNodeSpec p (n + 1) := by
  intro s₀ h k d fu
  have ihA := fun s h k d fu => (ih s h k d fu).1
  have ihL := fun s h k d fu => (ih s h k d fu).2.1
  have ihF := fun s h k d fu => (ih s h k d fu).2.2.1
  have ihE := fun s h k d fu => (ih s h k d fu).2.2.2.1
  have ihP := fun s h k d fu => (ih s h k d fu).2.2.2.2
  rw [invoke_eq _ (hp.get "ab_node")]
  simp only [callFn, absNode]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt,
      tcntM, evalE_tierE, evalE_idxE,
      internBVar_spec p (hp.get "bvar_find") (hp.get "bvar_push") (hp.get "intern_bvar") n, ihA,
          ihL, ihF, ihE, ihP] <;>
    finish [viewOK, tierW, idxW]

end specs

end L.Arena
