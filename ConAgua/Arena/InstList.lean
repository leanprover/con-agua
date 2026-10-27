module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
import ConAgua.Census.Attr
public import ConAgua.Arena.LiftSpec
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Layout

@[expose] public section

/-!
# `instantiateList`: the bulk instantiation, over a slice of the spine stack

con-ron's two walks (Lean twins in `Arena/ExprOps.lean`): the pure `instantiateList vs` and the
memoized `instantiateListGo vs` (memo `instLC`, key `(node, depth)`), entry
`instantiateListFast`. The substitution `vs : Array EIdx` (push order: the innermost binder's
argument is the LAST entry) is a slice `(o, l)` of the spine stack, word array 144 (`SPN` of
`WhnfBase.lean`, here `ILSPN`: the caller's `inst_list(e, off, cnt, d)` interface; `SpineR`
relates it). Each walk is `Inst1.lean`'s shape with `v` replaced by the slice, except:

* **The pure walk's `bvar` arm** (`il_bvar`): `j < d` is `h`; for `q = j - d < l` the
  replacement `v` is the slice's entry `l - 1 - q`; if `v` passes the cut-off it is the answer,
  else the walk recurses into `v` over the slice's **last `q` entries** (`lastEidx vs q`):
  `(o + (l - q), q)`, an `O(1)` adjustment, no copy. Past the slice: `intern_bvar(j - l)`.
* **The memo walk's `bvar` case** calls the pure walk on the whole slice (`il_go`), as the twin
  calls `instantiateList vs`.
* No arm rebuilds on change (the twin interns unconditionally).
* **The depth counter `fu`** (last argument) is the twin's `fuel` exactly: both
  dispatchers `abort` at `fu = 0` and run their arms (and `ilg_go`'s `bvar` call of `il_go`) at
  `fu - 1`; the arms pass their `fu` to their children, `il_bvar` to the replacement's walk.

The memo `instLC` is new: array 50 `ILMEMO`, stamp `CTL[50]`, count `CTL[51]`, `lfKey`'s codec;
like `abs1C` (`Abs1.lean`) it is kept out of `MemosR`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- `instLC`: array 50, stamp `CTL[50]`, count `CTL[51]`. -/
abbrev ilSch : MemoSch := ⟨ILMEMO, 50⟩

/-- The slice's word at `i`. -/
def slW (m : Mem) (i : Word) : Word := rdW (m.arr64 ILSPN) i

/-! ## The pure walk's models -/

mutual
/-- **The model of `il_go`** (`instantiateList vs`) at L fuel `n`. -/
def ilW : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, h, d, o, l, fu =>
    if fu = 0 then none
    else if derBW m h < 32767 ∧ derBW m h ≤ d then some (h, m)
    else if h >>> 28 = 4 then ilAppW n m h d o l (fu - 1)
    else if h >>> 28 = 5 then ilLamW n m h d o l (fu - 1)
    else if h >>> 28 = 6 then ilForallW n m h d o l (fu - 1)
    else if h >>> 28 = 7 then ilLetW n m h d o l (fu - 1)
    else if h >>> 28 = 9 then ilProjW n m h d o l (fu - 1)
    else if h >>> 28 = 0 then ilBVarW n m h d o l (fu - 1)
    else some (h, m)

/-- **The model of `il_app`.** -/
def ilAppW : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, h, d, o, l, fu =>
    if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if tcnt m APP (tierW h) ≤ idxW h then none
    else
      match ilW n m (tfld m APP (tierW h) (idxW h) 0) d o l fu with
      | none => none
      | some (x, m₁) =>
        match ilW n m₁ (tfld m APP (tierW h) (idxW h) 1) d o l fu with
        | none => none
        | some (y, m₂) => mkAppW m₂ x y

/-- **The model of `il_lam`.** -/
def ilLamW : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, h, d, o, l, fu =>
    if d + 1 = 0 then none
    else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if tcnt m LAM (tierW h) ≤ idxW h then none
    else
      match ilW n m (tfld m LAM (tierW h) (idxW h) 0) d o l fu with
      | none => none
      | some (x, m₁) =>
        match ilW n m₁ (tfld m LAM (tierW h) (idxW h) 1) (d + 1) o l fu with
        | none => none
        | some (y, m₂) => mkLamW m₂ x y

/-- **The model of `il_forall`.** -/
def ilForallW : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, h, d, o, l, fu =>
    if d + 1 = 0 then none
    else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if tcnt m FORALL (tierW h) ≤ idxW h then none
    else
      match ilW n m (tfld m FORALL (tierW h) (idxW h) 0) d o l fu with
      | none => none
      | some (x, m₁) =>
        match ilW n m₁ (tfld m FORALL (tierW h) (idxW h) 1) (d + 1) o l fu with
        | none => none
        | some (y, m₂) => mkForallW m₂ x y

/-- **The model of `il_let`.** -/
def ilLetW : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, h, d, o, l, fu =>
    if d + 1 = 0 then none
    else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if tcnt m LET (tierW h) ≤ idxW h then none
    else
      match ilW n m (tfld m LET (tierW h) (idxW h) 0) d o l fu with
      | none => none
      | some (x, m₁) =>
        match ilW n m₁ (tfld m LET (tierW h) (idxW h) 1) d o l fu with
        | none => none
        | some (y, m₂) =>
          match ilW n m₂ (tfld m LET (tierW h) (idxW h) 2) (d + 1) o l fu with
          | none => none
          | some (z, m₃) => mkLetW m₃ x y z

/-- **The model of `il_proj`.** -/
def ilProjW : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, h, d, o, l, fu =>
    if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if tcnt m PROJ (tierW h) ≤ idxW h then none
    else
      match ilW n m (tfld m PROJ (tierW h) (idxW h) 2) d o l fu with
      | none => none
      | some (x, m₁) =>
        mkProjW m₁ (tfld m PROJ (tierW h) (idxW h) 0)
          (tfld m PROJ (tierW h) (idxW h) 1) x

/-- **The model of `il_bvar`**: below `d` the handle; inside the slice its entry (cut off, or
instantiated over the slice's last `j - d` entries); past it `bvar (j - l)`. -/
def ilBVarW : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, h, d, o, l, fu =>
    if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if tcnt m BVAR (tierW h) ≤ idxW h then none
    else if tfld m BVAR (tierW h) (idxW h) 0 < d then some (h, m)
    else if tfld m BVAR (tierW h) (idxW h) 0 - d < l then
      if derBW m (slW m (o + (l - 1 - (tfld m BVAR (tierW h) (idxW h) 0 - d)))) < 32767 ∧ derBW m (slW m (o + (l - 1 - (tfld m BVAR (tierW h) (idxW h) 0 - d)))) ≤ d then some (slW m (o + (l - 1 - (tfld m BVAR (tierW h) (idxW h) 0 - d))), m)
      else ilW n m (slW m (o + (l - 1 - (tfld m BVAR (tierW h) (idxW h) 0 - d)))) d (o + (l - (tfld m BVAR (tierW h) (idxW h) 0 - d))) (tfld m BVAR (tierW h) (idxW h) 0 - d) fu
    else binternW m (tfld m BVAR (tierW h) (idxW h) 0 - l)
end

/-- The `bvar` arm's replacement `v`: cut off, or instantiated over the shorter slice. -/
def ilVW (n : Nat) (m : Mem) (v d o l fu : Word) : Option (Word × Mem) :=
  if derBW m v < 32767 ∧ derBW m v ≤ d then some (v, m) else ilW n m v d o l fu

/-! ## The memo walk's models -/

/-- Record `r` at `(h, d)` in the `instantiateList` memo and return it. -/
def ilsetK (h d : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m₁) =>
    match msetG ilSch m₁ h d r with
    | none => none
    | some m₂ => some (r, m₂)

mutual
/-- **The model of `ilg_go`** (`instantiateListGo vs`) at L fuel `n`. -/
def ilgW : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, h, d, o, l, fu =>
    if fu = 0 then none
    else if derBW m h < 32767 ∧ derBW m h ≤ d then some (h, m)
    else if h >>> 28 = 4 then ilgAppW n m h d o l (fu - 1)
    else if h >>> 28 = 5 then ilgLamW n m h d o l (fu - 1)
    else if h >>> 28 = 6 then ilgForallW n m h d o l (fu - 1)
    else if h >>> 28 = 7 then ilgLetW n m h d o l (fu - 1)
    else if h >>> 28 = 9 then ilgProjW n m h d o l (fu - 1)
    else if h >>> 28 = 0 then ilW n m h d o l (fu - 1)
    else some (h, m)

/-- **The model of `ilg_app`.** -/
def ilgAppW : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, h, d, o, l, fu =>
    if mfindG ilSch m h d = [] then none
    else if (mfindG ilSch m h d).headD 0 ≠ 0 then
      some (rdW (m.arr64 ILMEMO) ((mfindG ilSch m h d).tail.headD 0 * 4 + 3), m)
    else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if tcnt m APP (tierW h) ≤ idxW h then none
    else
      match ilgW n m (tfld m APP (tierW h) (idxW h) 0) d o l fu with
      | none => none
      | some (x, m₁) =>
        match ilgW n m₁ (tfld m APP (tierW h) (idxW h) 1) d o l fu with
        | none => none
        | some (y, m₂) => ilsetK h d (mkAppW m₂ x y)

/-- **The model of `ilg_lam`.** -/
def ilgLamW : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, h, d, o, l, fu =>
    if d + 1 = 0 then none
    else if mfindG ilSch m h d = [] then none
    else if (mfindG ilSch m h d).headD 0 ≠ 0 then
      some (rdW (m.arr64 ILMEMO) ((mfindG ilSch m h d).tail.headD 0 * 4 + 3), m)
    else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if tcnt m LAM (tierW h) ≤ idxW h then none
    else
      match ilgW n m (tfld m LAM (tierW h) (idxW h) 0) d o l fu with
      | none => none
      | some (x, m₁) =>
        match ilgW n m₁ (tfld m LAM (tierW h) (idxW h) 1) (d + 1) o l fu with
        | none => none
        | some (y, m₂) => ilsetK h d (mkLamW m₂ x y)

/-- **The model of `ilg_forall`.** -/
def ilgForallW : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, h, d, o, l, fu =>
    if d + 1 = 0 then none
    else if mfindG ilSch m h d = [] then none
    else if (mfindG ilSch m h d).headD 0 ≠ 0 then
      some (rdW (m.arr64 ILMEMO) ((mfindG ilSch m h d).tail.headD 0 * 4 + 3), m)
    else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if tcnt m FORALL (tierW h) ≤ idxW h then none
    else
      match ilgW n m (tfld m FORALL (tierW h) (idxW h) 0) d o l fu with
      | none => none
      | some (x, m₁) =>
        match ilgW n m₁ (tfld m FORALL (tierW h) (idxW h) 1) (d + 1) o l fu with
        | none => none
        | some (y, m₂) => ilsetK h d (mkForallW m₂ x y)

/-- **The model of `ilg_let`.** -/
def ilgLetW : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, h, d, o, l, fu =>
    if d + 1 = 0 then none
    else if mfindG ilSch m h d = [] then none
    else if (mfindG ilSch m h d).headD 0 ≠ 0 then
      some (rdW (m.arr64 ILMEMO) ((mfindG ilSch m h d).tail.headD 0 * 4 + 3), m)
    else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if tcnt m LET (tierW h) ≤ idxW h then none
    else
      match ilgW n m (tfld m LET (tierW h) (idxW h) 0) d o l fu with
      | none => none
      | some (x, m₁) =>
        match ilgW n m₁ (tfld m LET (tierW h) (idxW h) 1) d o l fu with
        | none => none
        | some (y, m₂) =>
          match ilgW n m₂ (tfld m LET (tierW h) (idxW h) 2) (d + 1) o l fu with
          | none => none
          | some (z, m₃) => ilsetK h d (mkLetW m₃ x y z)

/-- **The model of `ilg_proj`.** -/
def ilgProjW : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, h, d, o, l, fu =>
    if mfindG ilSch m h d = [] then none
    else if (mfindG ilSch m h d).headD 0 ≠ 0 then
      some (rdW (m.arr64 ILMEMO) ((mfindG ilSch m h d).tail.headD 0 * 4 + 3), m)
    else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if tcnt m PROJ (tierW h) ≤ idxW h then none
    else
      match ilgW n m (tfld m PROJ (tierW h) (idxW h) 2) d o l fu with
      | none => none
      | some (x, m₁) =>
        ilsetK h d (mkProjW m₁ (tfld m PROJ (tierW h) (idxW h) 0)
          (tfld m PROJ (tierW h) (idxW h) 1) x)
end

/-! ### Continuations and guarded equations -/

def lappK₁ (n : Nat) (d o l fu aw : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => lappK₂ x (ilW n m₁ aw d o l fu)
where lappK₂ (x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) => mkAppW m₂ x y

def llamK₁ (n : Nat) (d o l fu bw : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => llamK₂ x (ilW n m₁ bw (d + 1) o l fu)
where llamK₂ (x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) => mkLamW m₂ x y

def lfaK₁ (n : Nat) (d o l fu bw : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => lfaK₂ x (ilW n m₁ bw (d + 1) o l fu)
where lfaK₂ (x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) => mkForallW m₂ x y

def lleK₁ (n : Nat) (d o l fu vw bw : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => lleK₂ n d o l fu bw x (ilW n m₁ vw d o l fu)
where
  lleK₂ (n : Nat) (d o l fu bw x : Word) : Option (Word × Mem) → Option (Word × Mem)
    | none => none
    | some (y, m₂) => lleK₃ x y (ilW n m₂ bw (d + 1) o l fu)
  lleK₃ (x y : Word) : Option (Word × Mem) → Option (Word × Mem)
    | none => none
    | some (z, m₃) => mkLetW m₃ x y z

def lpjK₁ (nw iw : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => mkProjW m₁ nw iw x

def gappK₁ (n : Nat) (h d o l fu aw : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => gappK₂ h d x (ilgW n m₁ aw d o l fu)
where gappK₂ (h d x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) => ilsetK h d (mkAppW m₂ x y)

def glamK₁ (n : Nat) (h d o l fu bw : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => glamK₂ h d x (ilgW n m₁ bw (d + 1) o l fu)
where glamK₂ (h d x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) => ilsetK h d (mkLamW m₂ x y)

def gfaK₁ (n : Nat) (h d o l fu bw : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => gfaK₂ h d x (ilgW n m₁ bw (d + 1) o l fu)
where gfaK₂ (h d x : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (y, m₂) => ilsetK h d (mkForallW m₂ x y)

def gleK₁ (n : Nat) (h d o l fu vw bw : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => gleK₂ n h d o l fu bw x (ilgW n m₁ vw d o l fu)
where
  gleK₂ (n : Nat) (h d o l fu bw x : Word) : Option (Word × Mem) → Option (Word × Mem)
    | none => none
    | some (y, m₂) => gleK₃ h d x y (ilgW n m₂ bw (d + 1) o l fu)
  gleK₃ (h d x y : Word) : Option (Word × Mem) → Option (Word × Mem)
    | none => none
    | some (z, m₃) => ilsetK h d (mkLetW m₃ x y z)

def gpjK₁ (h d nw iw : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => ilsetK h d (mkProjW m₁ nw iw x)

section lks
variable (n : Nat) (h d o l fu aw bw vw nw iw x y z : Word) (m₁ m₂ m₃ : Mem)
theorem lappK₁_some : lappK₁ n d o l fu aw (some (x, m₁)) = lappK₁.lappK₂ x (ilW n m₁ aw d o l fu) := rfl
theorem lappK₂_some : lappK₁.lappK₂ x (some (y, m₂)) = mkAppW m₂ x y := rfl
theorem llamK₁_some : llamK₁ n d o l fu bw (some (x, m₁)) = llamK₁.llamK₂ x (ilW n m₁ bw (d + 1) o l fu) :=
  rfl
theorem llamK₂_some : llamK₁.llamK₂ x (some (y, m₂)) = mkLamW m₂ x y := rfl
theorem lfaK₁_some : lfaK₁ n d o l fu bw (some (x, m₁)) = lfaK₁.lfaK₂ x (ilW n m₁ bw (d + 1) o l fu) := rfl
theorem lfaK₂_some : lfaK₁.lfaK₂ x (some (y, m₂)) = mkForallW m₂ x y := rfl
theorem lleK₁_some : lleK₁ n d o l fu vw bw (some (x, m₁)) = lleK₁.lleK₂ n d o l fu bw x (ilW n m₁ vw d o l fu) :=
  rfl
theorem lleK₂_some :
    lleK₁.lleK₂ n d o l fu bw x (some (y, m₂)) = lleK₁.lleK₃ x y (ilW n m₂ bw (d + 1) o l fu) := rfl
theorem lleK₃_some : lleK₁.lleK₃ x y (some (z, m₃)) = mkLetW m₃ x y z := rfl
theorem lpjK₁_some : lpjK₁ nw iw (some (x, m₁)) = mkProjW m₁ nw iw x := rfl
theorem gappK₁_some : gappK₁ n h d o l fu aw (some (x, m₁)) = gappK₁.gappK₂ h d x (ilgW n m₁ aw d o l fu) :=
  rfl
theorem gappK₂_some : gappK₁.gappK₂ h d x (some (y, m₂)) = ilsetK h d (mkAppW m₂ x y) := rfl
theorem glamK₁_some :
    glamK₁ n h d o l fu bw (some (x, m₁)) = glamK₁.glamK₂ h d x (ilgW n m₁ bw (d + 1) o l fu) := rfl
theorem glamK₂_some : glamK₁.glamK₂ h d x (some (y, m₂)) = ilsetK h d (mkLamW m₂ x y) := rfl
theorem gfaK₁_some :
    gfaK₁ n h d o l fu bw (some (x, m₁)) = gfaK₁.gfaK₂ h d x (ilgW n m₁ bw (d + 1) o l fu) := rfl
theorem gfaK₂_some : gfaK₁.gfaK₂ h d x (some (y, m₂)) = ilsetK h d (mkForallW m₂ x y) := rfl
theorem gleK₁_some :
    gleK₁ n h d o l fu vw bw (some (x, m₁)) = gleK₁.gleK₂ n h d o l fu bw x (ilgW n m₁ vw d o l fu) := rfl
theorem gleK₂_some :
    gleK₁.gleK₂ n h d o l fu bw x (some (y, m₂)) = gleK₁.gleK₃ h d x y (ilgW n m₂ bw (d + 1) o l fu) := rfl
theorem gleK₃_some : gleK₁.gleK₃ h d x y (some (z, m₃)) = ilsetK h d (mkLetW m₃ x y z) := rfl
theorem gpjK₁_some : gpjK₁ h d nw iw (some (x, m₁)) = ilsetK h d (mkProjW m₁ nw iw x) := rfl
theorem ilsetK_some (r : Word) :
    ilsetK h d (some (r, m₁)) =
      (match msetG ilSch m₁ h d r with | none => none | some m₂ => some (r, m₂)) := rfl
end lks

attribute [arena_grind =] lappK₁_some lappK₂_some llamK₁_some llamK₂_some lfaK₁_some lfaK₂_some
  lleK₁_some lleK₂_some lleK₃_some lpjK₁_some gappK₁_some gappK₂_some glamK₁_some glamK₂_some
  gfaK₁_some gfaK₂_some gleK₁_some gleK₂_some gleK₃_some gpjK₁_some ilsetK_some

section arms
variable (n : Nat) (m : Mem) (h d o l fu : Word)

/-- The cut-off (shared by both dispatchers and the `bvar` arm's replacement). -/
abbrev ilCut (m : Mem) (h d : Word) : Prop := derBW m h < 32767 ∧ derBW m h ≤ d

theorem ilW_cut (hf : fu ≠ 0) (hc : ilCut m h d) : ilW (n + 1) m h d o l fu = some (h, m) := by
  rw [ilW]; simp only [hf, hc, and_self, ↓reduceIte]
theorem ilW_app (hf : fu ≠ 0) (hc : ¬ ilCut m h d) (hg : h >>> 28 = 4) : ilW (n + 1) m h d o l fu = ilAppW n m h d o l (fu - 1) := by
  rw [ilW]; simp [hf, hc, hg]
theorem ilW_lam (hf : fu ≠ 0) (hc : ¬ ilCut m h d) (hg : h >>> 28 = 5) : ilW (n + 1) m h d o l fu = ilLamW n m h d o l (fu - 1) := by
  rw [ilW]; simp [hf, hc, hg]
theorem ilW_forall (hf : fu ≠ 0) (hc : ¬ ilCut m h d) (hg : h >>> 28 = 6) :
    ilW (n + 1) m h d o l fu = ilForallW n m h d o l (fu - 1) := by
  rw [ilW]; simp [hf, hc, hg]
theorem ilW_let (hf : fu ≠ 0) (hc : ¬ ilCut m h d) (hg : h >>> 28 = 7) : ilW (n + 1) m h d o l fu = ilLetW n m h d o l (fu - 1) := by
  rw [ilW]; simp [hf, hc, hg]
theorem ilW_proj (hf : fu ≠ 0) (hc : ¬ ilCut m h d) (hg : h >>> 28 = 9) :
    ilW (n + 1) m h d o l fu = ilProjW n m h d o l (fu - 1) := by
  rw [ilW]; simp [hf, hc, hg]
theorem ilW_bvar (hf : fu ≠ 0) (hc : ¬ ilCut m h d) (hg : h >>> 28 = 0) :
    ilW (n + 1) m h d o l fu = ilBVarW n m h d o l (fu - 1) := by
  rw [ilW]; simp [hf, hc, hg]
theorem ilW_leaf (hf : fu ≠ 0) (hc : ¬ ilCut m h d) (h0 : h >>> 28 ≠ 0) (h4 : h >>> 28 ≠ 4) (h5 : h >>> 28 ≠ 5)
    (h6 : h >>> 28 ≠ 6) (h7 : h >>> 28 ≠ 7) (h9 : h >>> 28 ≠ 9) :
    ilW (n + 1) m h d o l fu = some (h, m) := by
  rw [ilW]; simp [hf, hc, h0, h4, h5, h6, h7, h9]

theorem ilgW_cut (hf : fu ≠ 0) (hc : ilCut m h d) : ilgW (n + 1) m h d o l fu = some (h, m) := by
  rw [ilgW]; simp only [hf, hc, and_self, ↓reduceIte]
theorem ilgW_app (hf : fu ≠ 0) (hc : ¬ ilCut m h d) (hg : h >>> 28 = 4) :
    ilgW (n + 1) m h d o l fu = ilgAppW n m h d o l (fu - 1) := by
  rw [ilgW]; simp [hf, hc, hg]
theorem ilgW_lam (hf : fu ≠ 0) (hc : ¬ ilCut m h d) (hg : h >>> 28 = 5) :
    ilgW (n + 1) m h d o l fu = ilgLamW n m h d o l (fu - 1) := by
  rw [ilgW]; simp [hf, hc, hg]
theorem ilgW_forall (hf : fu ≠ 0) (hc : ¬ ilCut m h d) (hg : h >>> 28 = 6) :
    ilgW (n + 1) m h d o l fu = ilgForallW n m h d o l (fu - 1) := by
  rw [ilgW]; simp [hf, hc, hg]
theorem ilgW_let (hf : fu ≠ 0) (hc : ¬ ilCut m h d) (hg : h >>> 28 = 7) :
    ilgW (n + 1) m h d o l fu = ilgLetW n m h d o l (fu - 1) := by
  rw [ilgW]; simp [hf, hc, hg]
theorem ilgW_proj (hf : fu ≠ 0) (hc : ¬ ilCut m h d) (hg : h >>> 28 = 9) :
    ilgW (n + 1) m h d o l fu = ilgProjW n m h d o l (fu - 1) := by
  rw [ilgW]; simp [hf, hc, hg]
theorem ilgW_bvar (hf : fu ≠ 0) (hc : ¬ ilCut m h d) (hg : h >>> 28 = 0) :
    ilgW (n + 1) m h d o l fu = ilW n m h d o l (fu - 1) := by
  rw [ilgW]; simp [hf, hc, hg]
theorem ilgW_leaf (hf : fu ≠ 0) (hc : ¬ ilCut m h d) (h0 : h >>> 28 ≠ 0) (h4 : h >>> 28 ≠ 4) (h5 : h >>> 28 ≠ 5)
    (h6 : h >>> 28 ≠ 6) (h7 : h >>> 28 ≠ 7) (h9 : h >>> 28 ≠ 9) :
    ilgW (n + 1) m h d o l fu = some (h, m) := by
  rw [ilgW]; simp [hf, hc, h0, h4, h5, h6, h7, h9]

theorem ilAppW_miss (hvk : viewOK m h APP) :
    ilAppW (n + 1) m h d o l fu =
      lappK₁ n d o l fu (tfld m APP (tierW h) (idxW h) 1)
        (ilW n m (tfld m APP (tierW h) (idxW h) 0) d o l fu) := by
  rw [ilAppW]; simp only [hvk.1, ↓reduceIte, UInt64.not_le.mpr hvk.2]
  cases ilW n m (tfld m APP (tierW h) (idxW h) 0) d o l fu <;> rfl
theorem ilLamW_miss (h1 : d + 1 ≠ 0) (hvk : viewOK m h LAM) :
    ilLamW (n + 1) m h d o l fu =
      llamK₁ n d o l fu (tfld m LAM (tierW h) (idxW h) 1)
        (ilW n m (tfld m LAM (tierW h) (idxW h) 0) d o l fu) := by
  rw [ilLamW]; simp only [h1, hvk.1, ↓reduceIte, UInt64.not_le.mpr hvk.2]
  cases ilW n m (tfld m LAM (tierW h) (idxW h) 0) d o l fu <;> rfl
theorem ilForallW_miss (h1 : d + 1 ≠ 0) (hvk : viewOK m h FORALL) :
    ilForallW (n + 1) m h d o l fu =
      lfaK₁ n d o l fu (tfld m FORALL (tierW h) (idxW h) 1)
        (ilW n m (tfld m FORALL (tierW h) (idxW h) 0) d o l fu) := by
  rw [ilForallW]; simp only [h1, hvk.1, ↓reduceIte, UInt64.not_le.mpr hvk.2]
  cases ilW n m (tfld m FORALL (tierW h) (idxW h) 0) d o l fu <;> rfl
theorem ilLetW_miss (h1 : d + 1 ≠ 0) (hvk : viewOK m h LET) :
    ilLetW (n + 1) m h d o l fu =
      lleK₁ n d o l fu (tfld m LET (tierW h) (idxW h) 1)
        (tfld m LET (tierW h) (idxW h) 2)
        (ilW n m (tfld m LET (tierW h) (idxW h) 0) d o l fu) := by
  rw [ilLetW]; simp only [h1, hvk.1, ↓reduceIte, UInt64.not_le.mpr hvk.2]
  cases ilW n m (tfld m LET (tierW h) (idxW h) 0) d o l fu with
  | none => rfl
  | some p =>
    obtain ⟨x, m₁⟩ := p
    cases ilW n m₁ (tfld m LET (tierW h) (idxW h) 1) d o l fu <;> rfl
theorem ilProjW_miss (hvk : viewOK m h PROJ) :
    ilProjW (n + 1) m h d o l fu =
      lpjK₁ (tfld m PROJ (tierW h) (idxW h) 0)
        (tfld m PROJ (tierW h) (idxW h) 1)
        (ilW n m (tfld m PROJ (tierW h) (idxW h) 2) d o l fu) := by
  rw [ilProjW]; simp only [hvk.1, ↓reduceIte, UInt64.not_le.mpr hvk.2]
  cases ilW n m (tfld m PROJ (tierW h) (idxW h) 2) d o l fu <;> rfl

theorem ilBVarW_lt (hvk : viewOK m h BVAR) (hj : tfld m BVAR (tierW h) (idxW h) 0 < d) :
    ilBVarW (n + 1) m h d o l fu = some (h, m) := by
  rw [ilBVarW]; simp only [hvk.1, ↓reduceIte, UInt64.not_le.mpr hvk.2, hj]
theorem ilBVarW_in (hvk : viewOK m h BVAR) (hj : ¬ tfld m BVAR (tierW h) (idxW h) 0 < d)
    (hq : tfld m BVAR (tierW h) (idxW h) 0 - d < l) :
    ilBVarW (n + 1) m h d o l fu =
      ilVW n m (slW m (o + (l - 1 - (tfld m BVAR (tierW h) (idxW h) 0 - d)))) d
        (o + (l - (tfld m BVAR (tierW h) (idxW h) 0 - d)))
        (tfld m BVAR (tierW h) (idxW h) 0 - d) fu := by
  rw [ilBVarW]; simp only [hvk.1, ↓reduceIte, UInt64.not_le.mpr hvk.2, hj, hq]; rfl
theorem ilBVarW_out (hvk : viewOK m h BVAR) (hj : ¬ tfld m BVAR (tierW h) (idxW h) 0 < d)
    (hq : ¬ tfld m BVAR (tierW h) (idxW h) 0 - d < l) :
    ilBVarW (n + 1) m h d o l fu = binternW m (tfld m BVAR (tierW h) (idxW h) 0 - l) := by
  rw [ilBVarW]; simp only [hvk.1, ↓reduceIte, UInt64.not_le.mpr hvk.2, hj, hq]
theorem ilVW_cut (hc : ilCut m h d) : ilVW n m h d o l fu = some (h, m) := by
  rw [ilVW]; simp only [hc, and_self, ↓reduceIte]
theorem ilVW_go (hc : ¬ ilCut m h d) : ilVW n m h d o l fu = ilW n m h d o l fu := by
  rw [ilVW]; simp only [hc, ↓reduceIte]

theorem ilgAppW_hit (hr : mfindG ilSch m h d ≠ []) (hh : (mfindG ilSch m h d).headD 0 ≠ 0) :
    ilgAppW (n + 1) m h d o l fu =
      some (rdW (m.arr64 ILMEMO) ((mfindG ilSch m h d).tail.headD 0 * 4 + 3), m) := by
  rw [ilgAppW]; simp only [hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]
theorem ilgAppW_miss (hr : mfindG ilSch m h d ≠ []) (hh : (mfindG ilSch m h d).headD 0 = 0)
    (hvk : viewOK m h APP) :
    ilgAppW (n + 1) m h d o l fu =
      gappK₁ n h d o l fu (tfld m APP (tierW h) (idxW h) 1)
        (ilgW n m (tfld m APP (tierW h) (idxW h) 0) d o l fu) := by
  rw [ilgAppW]; simp only [hr, hh, ↓reduceIte, ne_eq, not_true_eq_false, hvk.1, ↓reduceIte, UInt64.not_le.mpr hvk.2]
  cases ilgW n m (tfld m APP (tierW h) (idxW h) 0) d o l fu <;> rfl
theorem ilgLamW_hit (h1 : d + 1 ≠ 0) (hr : mfindG ilSch m h d ≠ [])
    (hh : (mfindG ilSch m h d).headD 0 ≠ 0) :
    ilgLamW (n + 1) m h d o l fu =
      some (rdW (m.arr64 ILMEMO) ((mfindG ilSch m h d).tail.headD 0 * 4 + 3), m) := by
  rw [ilgLamW]; simp only [h1, hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]
theorem ilgLamW_miss (h1 : d + 1 ≠ 0) (hr : mfindG ilSch m h d ≠ [])
    (hh : (mfindG ilSch m h d).headD 0 = 0) (hvk : viewOK m h LAM) :
    ilgLamW (n + 1) m h d o l fu =
      glamK₁ n h d o l fu (tfld m LAM (tierW h) (idxW h) 1)
        (ilgW n m (tfld m LAM (tierW h) (idxW h) 0) d o l fu) := by
  rw [ilgLamW]; simp only [h1, hr, hh, ↓reduceIte, ne_eq, not_true_eq_false, hvk.1, ↓reduceIte, UInt64.not_le.mpr hvk.2]
  cases ilgW n m (tfld m LAM (tierW h) (idxW h) 0) d o l fu <;> rfl
theorem ilgForallW_hit (h1 : d + 1 ≠ 0) (hr : mfindG ilSch m h d ≠ [])
    (hh : (mfindG ilSch m h d).headD 0 ≠ 0) :
    ilgForallW (n + 1) m h d o l fu =
      some (rdW (m.arr64 ILMEMO) ((mfindG ilSch m h d).tail.headD 0 * 4 + 3), m) := by
  rw [ilgForallW]; simp only [h1, hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]
theorem ilgForallW_miss (h1 : d + 1 ≠ 0) (hr : mfindG ilSch m h d ≠ [])
    (hh : (mfindG ilSch m h d).headD 0 = 0) (hvk : viewOK m h FORALL) :
    ilgForallW (n + 1) m h d o l fu =
      gfaK₁ n h d o l fu (tfld m FORALL (tierW h) (idxW h) 1)
        (ilgW n m (tfld m FORALL (tierW h) (idxW h) 0) d o l fu) := by
  rw [ilgForallW]; simp only [h1, hr, hh, ↓reduceIte, ne_eq, not_true_eq_false, hvk.1, ↓reduceIte, UInt64.not_le.mpr hvk.2]
  cases ilgW n m (tfld m FORALL (tierW h) (idxW h) 0) d o l fu <;> rfl
theorem ilgLetW_hit (h1 : d + 1 ≠ 0) (hr : mfindG ilSch m h d ≠ [])
    (hh : (mfindG ilSch m h d).headD 0 ≠ 0) :
    ilgLetW (n + 1) m h d o l fu =
      some (rdW (m.arr64 ILMEMO) ((mfindG ilSch m h d).tail.headD 0 * 4 + 3), m) := by
  rw [ilgLetW]; simp only [h1, hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]
theorem ilgLetW_miss (h1 : d + 1 ≠ 0) (hr : mfindG ilSch m h d ≠ [])
    (hh : (mfindG ilSch m h d).headD 0 = 0) (hvk : viewOK m h LET) :
    ilgLetW (n + 1) m h d o l fu =
      gleK₁ n h d o l fu (tfld m LET (tierW h) (idxW h) 1)
        (tfld m LET (tierW h) (idxW h) 2)
        (ilgW n m (tfld m LET (tierW h) (idxW h) 0) d o l fu) := by
  rw [ilgLetW]; simp only [h1, hr, hh, ↓reduceIte, ne_eq, not_true_eq_false, hvk.1, ↓reduceIte, UInt64.not_le.mpr hvk.2]
  cases ilgW n m (tfld m LET (tierW h) (idxW h) 0) d o l fu with
  | none => rfl
  | some p =>
    obtain ⟨x, m₁⟩ := p
    cases ilgW n m₁ (tfld m LET (tierW h) (idxW h) 1) d o l fu <;> rfl
theorem ilgProjW_hit (hr : mfindG ilSch m h d ≠ []) (hh : (mfindG ilSch m h d).headD 0 ≠ 0) :
    ilgProjW (n + 1) m h d o l fu =
      some (rdW (m.arr64 ILMEMO) ((mfindG ilSch m h d).tail.headD 0 * 4 + 3), m) := by
  rw [ilgProjW]; simp only [hr, hh, ↓reduceIte, ne_eq, not_false_eq_true]
theorem ilgProjW_miss (hr : mfindG ilSch m h d ≠ []) (hh : (mfindG ilSch m h d).headD 0 = 0)
    (hvk : viewOK m h PROJ) :
    ilgProjW (n + 1) m h d o l fu =
      gpjK₁ h d (tfld m PROJ (tierW h) (idxW h) 0)
        (tfld m PROJ (tierW h) (idxW h) 1)
        (ilgW n m (tfld m PROJ (tierW h) (idxW h) 2) d o l fu) := by
  rw [ilgProjW]; simp only [hr, hh, ↓reduceIte, ne_eq, not_true_eq_false, hvk.1, ↓reduceIte, UInt64.not_le.mpr hvk.2]
  cases ilgW n m (tfld m PROJ (tierW h) (idxW h) 2) d o l fu <;> rfl

end arms

grind_pattern [arena_grind] ilW_cut => ilW (n + 1) m h d o l fu
grind_pattern [arena_grind] ilW_app => ilW (n + 1) m h d o l fu
grind_pattern [arena_grind] ilW_lam => ilW (n + 1) m h d o l fu
grind_pattern [arena_grind] ilW_forall => ilW (n + 1) m h d o l fu
grind_pattern [arena_grind] ilW_let => ilW (n + 1) m h d o l fu
grind_pattern [arena_grind] ilW_proj => ilW (n + 1) m h d o l fu
grind_pattern [arena_grind] ilW_bvar => ilW (n + 1) m h d o l fu
grind_pattern [arena_grind] ilW_leaf => ilW (n + 1) m h d o l fu
grind_pattern [arena_grind] ilgW_cut => ilgW (n + 1) m h d o l fu
grind_pattern [arena_grind] ilgW_app => ilgW (n + 1) m h d o l fu
grind_pattern [arena_grind] ilgW_lam => ilgW (n + 1) m h d o l fu
grind_pattern [arena_grind] ilgW_forall => ilgW (n + 1) m h d o l fu
grind_pattern [arena_grind] ilgW_let => ilgW (n + 1) m h d o l fu
grind_pattern [arena_grind] ilgW_proj => ilgW (n + 1) m h d o l fu
grind_pattern [arena_grind] ilgW_bvar => ilgW (n + 1) m h d o l fu
grind_pattern [arena_grind] ilgW_leaf => ilgW (n + 1) m h d o l fu
grind_pattern [arena_grind] ilAppW_miss => ilAppW (n + 1) m h d o l fu
grind_pattern [arena_grind] ilLamW_miss => ilLamW (n + 1) m h d o l fu
grind_pattern [arena_grind] ilForallW_miss => ilForallW (n + 1) m h d o l fu
grind_pattern [arena_grind] ilLetW_miss => ilLetW (n + 1) m h d o l fu
grind_pattern [arena_grind] ilProjW_miss => ilProjW (n + 1) m h d o l fu
grind_pattern [arena_grind] ilBVarW_lt => ilBVarW (n + 1) m h d o l fu
grind_pattern [arena_grind] ilBVarW_in => ilBVarW (n + 1) m h d o l fu
grind_pattern [arena_grind] ilBVarW_out => ilBVarW (n + 1) m h d o l fu
grind_pattern [arena_grind] ilVW_cut => ilVW n m h d o l fu
grind_pattern [arena_grind] ilVW_go => ilVW n m h d o l fu
grind_pattern [arena_grind] ilgAppW_hit => ilgAppW (n + 1) m h d o l fu
grind_pattern [arena_grind] ilgAppW_miss => ilgAppW (n + 1) m h d o l fu
grind_pattern [arena_grind] ilgLamW_hit => ilgLamW (n + 1) m h d o l fu
grind_pattern [arena_grind] ilgLamW_miss => ilgLamW (n + 1) m h d o l fu
grind_pattern [arena_grind] ilgForallW_hit => ilgForallW (n + 1) m h d o l fu
grind_pattern [arena_grind] ilgForallW_miss => ilgForallW (n + 1) m h d o l fu
grind_pattern [arena_grind] ilgLetW_hit => ilgLetW (n + 1) m h d o l fu
grind_pattern [arena_grind] ilgLetW_miss => ilgLetW (n + 1) m h d o l fu
grind_pattern [arena_grind] ilgProjW_hit => ilgProjW (n + 1) m h d o l fu
grind_pattern [arena_grind] ilgProjW_miss => ilgProjW (n + 1) m h d o l fu

/-! ## The L code: the pure walk -/

/-- con-ron: ConRon/Arena/ExprOps.lean:394-420 ConRon.Arena.instantiateList -/
@[l_impl ConRon.Arena.instantiateList]
def ilGo : FunDecl := lfn (h, d, o, l, fu) locals (x, g, r) {
  if fu == 0 { abort };
  x := call der_b(h);
  if x < 32767 && x <= d { return h };
  g := h >> 28;
  if g == 4 { r := call il_app(h, d, o, l, fu - 1); return r };
  if g == 5 { r := call il_lam(h, d, o, l, fu - 1); return r };
  if g == 6 { r := call il_forall(h, d, o, l, fu - 1); return r };
  if g == 7 { r := call il_let(h, d, o, l, fu - 1); return r };
  if g == 9 { r := call il_proj(h, d, o, l, fu - 1); return r };
  if g == 0 { r := call il_bvar(h, d, o, l, fu - 1); return r };
  return h
}

/-- con-ron: ConRon/Arena/ExprOps.lean:422-432 ConRon.Arena.instListArmApp -/
@[l_impl ConRon.Arena.instListArmApp]
def ilApp : FunDecl := lfn (h, d, o, l, fu) locals (t, i, f, a, x, y, r) {
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if APP⟨t⟩.count <= i { abort };
  f := APP⟨t, i⟩.f;
  a := APP⟨t, i⟩.a;
  x := call il_go(f, d, o, l, fu);
  y := call il_go(a, d, o, l, fu);
  r := call mk_app(x, y);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:434-444 ConRon.Arena.instListArmBind -/
@[l_impl ConRon.Arena.instListArmBind]
def ilLam : FunDecl := lfn (h, d, o, l, fu) locals (t, i, f, a, x, y, r) {
  if d + 1 == 0 { abort };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if LAM⟨t⟩.count <= i { abort };
  f := LAM⟨t, i⟩.ty;
  a := LAM⟨t, i⟩.b;
  x := call il_go(f, d, o, l, fu);
  y := call il_go(a, d + 1, o, l, fu);
  r := call mk_lam(x, y);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:434-444 ConRon.Arena.instListArmBind -/
@[l_impl ConRon.Arena.instListArmBind]
def ilForall : FunDecl := lfn (h, d, o, l, fu) locals (t, i, f, a, x, y, r) {
  if d + 1 == 0 { abort };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if FORALL⟨t⟩.count <= i { abort };
  f := FORALL⟨t, i⟩.ty;
  a := FORALL⟨t, i⟩.b;
  x := call il_go(f, d, o, l, fu);
  y := call il_go(a, d + 1, o, l, fu);
  r := call mk_forall(x, y);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:446-457 ConRon.Arena.instListArmLet -/
@[l_impl ConRon.Arena.instListArmLet]
def ilLet : FunDecl := lfn (h, d, o, l, fu) locals (t, i, f, a, b, x, y, z, r) {
  if d + 1 == 0 { abort };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if LET⟨t⟩.count <= i { abort };
  f := LET⟨t, i⟩.ty;
  a := LET⟨t, i⟩.v;
  b := LET⟨t, i⟩.b;
  x := call il_go(f, d, o, l, fu);
  y := call il_go(a, d, o, l, fu);
  z := call il_go(b, d + 1, o, l, fu);
  r := call mk_let(x, y, z);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:459-468 ConRon.Arena.instListArmProj -/
@[l_impl ConRon.Arena.instListArmProj]
def ilProj : FunDecl := lfn (h, d, o, l, fu) locals (t, i, nm, ix, e, x, r) {
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if PROJ⟨t⟩.count <= i { abort };
  nm := PROJ⟨t, i⟩.n;
  ix := PROJ⟨t, i⟩.i;
  e := PROJ⟨t, i⟩.e;
  x := call il_go(e, d, o, l, fu);
  r := call mk_proj(nm, ix, x);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:470-495 ConRon.Arena.instListArmBVar -/
@[l_impl ConRon.Arena.instListArmBVar]
def ilBVar : FunDecl := lfn (h, d, o, l, fu) locals (t, i, j, q, v, x, r) {
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if BVAR⟨t⟩.count <= i { abort };
  j := BVAR⟨t, i⟩.i;
  if j < d { return h };
  q := j - d;
  if q < l {
    v := ILSPN.u64[o + (l - 1 - q)];
    x := call der_b(v);
    if x < 32767 && x <= d { return v };
    r := call il_go(v, d, o + (l - q), q, fu);
    return r
  };
  r := call intern_bvar(j - l);
  return r
}

/-! ## The L code: the memo walk -/

/-- con-ron: ConRon/Arena/ExprOps.lean:524-547 ConRon.Arena.instantiateListGo -/
@[l_impl ConRon.Arena.instantiateListGo]
def ilgGo : FunDecl := lfn (h, d, o, l, fu) locals (x, g, r) {
  if fu == 0 { abort };
  x := call der_b(h);
  if x < 32767 && x <= d { return h };
  g := h >> 28;
  if g == 4 { r := call ilg_app(h, d, o, l, fu - 1); return r };
  if g == 5 { r := call ilg_lam(h, d, o, l, fu - 1); return r };
  if g == 6 { r := call ilg_forall(h, d, o, l, fu - 1); return r };
  if g == 7 { r := call ilg_let(h, d, o, l, fu - 1); return r };
  if g == 9 { r := call ilg_proj(h, d, o, l, fu - 1); return r };
  if g == 0 { r := call il_go(h, d, o, l, fu - 1); return r };
  return h
}

/-- con-ron: ConRon/Arena/ExprOps.lean:549-564 ConRon.Arena.instListGoArmApp -/
@[l_impl ConRon.Arena.instListGoArmApp]
def ilgApp : FunDecl := lfn (h, d, o, l, fu) locals (fd, j, e0, t, i, f, a, x, y, r, u) {
  (fd, j, e0) := call ilm_find(h, d);
  if fd != 0 { return ILMEMO.u64[j * 4 + 3] };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if APP⟨t⟩.count <= i { abort };
  f := APP⟨t, i⟩.f;
  a := APP⟨t, i⟩.a;
  x := call ilg_go(f, d, o, l, fu);
  y := call ilg_go(a, d, o, l, fu);
  r := call mk_app(x, y);
  (fd, j, e0) := call ilm_find(h, d);
  u := call ilm_put(h, d, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:566-581 ConRon.Arena.instListGoArmBind -/
@[l_impl ConRon.Arena.instListGoArmBind]
def ilgLam : FunDecl := lfn (h, d, o, l, fu) locals (fd, j, e0, t, i, f, a, x, y, r, u) {
  if d + 1 == 0 { abort };
  (fd, j, e0) := call ilm_find(h, d);
  if fd != 0 { return ILMEMO.u64[j * 4 + 3] };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if LAM⟨t⟩.count <= i { abort };
  f := LAM⟨t, i⟩.ty;
  a := LAM⟨t, i⟩.b;
  x := call ilg_go(f, d, o, l, fu);
  y := call ilg_go(a, d + 1, o, l, fu);
  r := call mk_lam(x, y);
  (fd, j, e0) := call ilm_find(h, d);
  u := call ilm_put(h, d, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:566-581 ConRon.Arena.instListGoArmBind -/
@[l_impl ConRon.Arena.instListGoArmBind]
def ilgForall : FunDecl := lfn (h, d, o, l, fu) locals (fd, j, e0, t, i, f, a, x, y, r, u) {
  if d + 1 == 0 { abort };
  (fd, j, e0) := call ilm_find(h, d);
  if fd != 0 { return ILMEMO.u64[j * 4 + 3] };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if FORALL⟨t⟩.count <= i { abort };
  f := FORALL⟨t, i⟩.ty;
  a := FORALL⟨t, i⟩.b;
  x := call ilg_go(f, d, o, l, fu);
  y := call ilg_go(a, d + 1, o, l, fu);
  r := call mk_forall(x, y);
  (fd, j, e0) := call ilm_find(h, d);
  u := call ilm_put(h, d, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:583-599 ConRon.Arena.instListGoArmLet -/
@[l_impl ConRon.Arena.instListGoArmLet]
def ilgLet : FunDecl := lfn (h, d, o, l, fu) locals (fd, j, e0, t, i, f, a, b, x, y, z, r, u) {
  if d + 1 == 0 { abort };
  (fd, j, e0) := call ilm_find(h, d);
  if fd != 0 { return ILMEMO.u64[j * 4 + 3] };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if LET⟨t⟩.count <= i { abort };
  f := LET⟨t, i⟩.ty;
  a := LET⟨t, i⟩.v;
  b := LET⟨t, i⟩.b;
  x := call ilg_go(f, d, o, l, fu);
  y := call ilg_go(a, d, o, l, fu);
  z := call ilg_go(b, d + 1, o, l, fu);
  r := call mk_let(x, y, z);
  (fd, j, e0) := call ilm_find(h, d);
  u := call ilm_put(h, d, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:601-615 ConRon.Arena.instListGoArmProj -/
@[l_impl ConRon.Arena.instListGoArmProj]
def ilgProj : FunDecl := lfn (h, d, o, l, fu) locals (fd, j, e0, t, i, nm, ix, e, x, r, u) {
  (fd, j, e0) := call ilm_find(h, d);
  if fd != 0 { return ILMEMO.u64[j * 4 + 3] };
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if PROJ⟨t⟩.count <= i { abort };
  nm := PROJ⟨t, i⟩.n;
  ix := PROJ⟨t, i⟩.i;
  e := PROJ⟨t, i⟩.e;
  x := call ilg_go(e, d, o, l, fu);
  r := call mk_proj(nm, ix, x);
  (fd, j, e0) := call ilm_find(h, d);
  u := call ilm_put(h, d, r, fd, j);
  return r
}

/-! ## The program and the dispatchers' steps -/

/-- The two walks without the entry, over `liftProg`. -/
def instListWalkProg : Prog :=
  [("ilm_find", memoFindG ilSch), ("ilm_put", memoPutG ilSch), ("ilm_clear", memoClearG ilSch),
    ("il_go", ilGo), ("il_app", ilApp), ("il_lam", ilLam), ("il_forall", ilForall),
    ("il_let", ilLet), ("il_proj", ilProj), ("il_bvar", ilBVar), ("ilg_go", ilgGo),
    ("ilg_app", ilgApp), ("ilg_lam", ilgLam), ("ilg_forall", ilgForall), ("ilg_let", ilgLet),
    ("ilg_proj", ilgProj)] ++ liftProg

/-- What the specs need of the program: `instListWalkProg`'s functions. -/
def InstListProg (p : Prog) : Prop := ProgHas p instListWalkProg

theorem InstListProg.base {p : Prog} (hp : InstListProg p) : LiftProg p := by
  have h : ProgHas p liftProg := hp.right
  unfold LiftProg liftProgFns; repeat (first | exact ProgHas.nil | refine ProgHas.cons (h.get _) ?_)

section specs
variable (p : Prog) (hp : InstListProg p)

/-- The spec of `il_go` at fuel `n`. -/
def IlGoSpec (n : Nat) : Prop := ∀ (s₀ : St) (h d o l fu : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "il_go" [h, d, o, l, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ ilW n s₀.mem h d o l fu = some (r.headD 0, s'.mem); ⊤⦄

/-- The specs of the pure walk's six arms at fuel `n`. -/
def IlArmSpec (n : Nat) : Prop := ∀ (s₀ : St) (h d o l fu : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "il_app" [h, d, o, l, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ ilAppW n s₀.mem h d o l fu = some (r.headD 0, s'.mem); ⊤⦄ ∧
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "il_lam" [h, d, o, l, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ ilLamW n s₀.mem h d o l fu = some (r.headD 0, s'.mem); ⊤⦄ ∧
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "il_forall" [h, d, o, l, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ ilForallW n s₀.mem h d o l fu = some (r.headD 0, s'.mem); ⊤⦄ ∧
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "il_let" [h, d, o, l, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ ilLetW n s₀.mem h d o l fu = some (r.headD 0, s'.mem); ⊤⦄ ∧
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "il_proj" [h, d, o, l, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ ilProjW n s₀.mem h d o l fu = some (r.headD 0, s'.mem); ⊤⦄ ∧
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "il_bvar" [h, d, o, l, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ ilBVarW n s₀.mem h d o l fu = some (r.headD 0, s'.mem); ⊤⦄

/-- The spec of `ilg_go` at fuel `n`. -/
def IlgGoSpec (n : Nat) : Prop := ∀ (s₀ : St) (h d o l fu : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "ilg_go" [h, d, o, l, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ ilgW n s₀.mem h d o l fu = some (r.headD 0, s'.mem); ⊤⦄

/-- The specs of the memo walk's five arms at fuel `n`. -/
def IlgArmSpec (n : Nat) : Prop := ∀ (s₀ : St) (h d o l fu : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ilg_app" [h, d, o, l, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ ilgAppW n s₀.mem h d o l fu = some (r.headD 0, s'.mem); ⊤⦄ ∧
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ilg_lam" [h, d, o, l, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ ilgLamW n s₀.mem h d o l fu = some (r.headD 0, s'.mem); ⊤⦄ ∧
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ilg_forall" [h, d, o, l, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ ilgForallW n s₀.mem h d o l fu = some (r.headD 0, s'.mem); ⊤⦄ ∧
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ilg_let" [h, d, o, l, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ ilgLetW n s₀.mem h d o l fu = some (r.headD 0, s'.mem); ⊤⦄ ∧
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ilg_proj" [h, d, o, l, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ ilgProjW n s₀.mem h d o l fu = some (r.headD 0, s'.mem); ⊤⦄

include hp in
theorem ilGo_step (n : Nat) (ih : IlArmSpec p n) : IlGoSpec p (n + 1) := by
  intro s₀ h d o l fu
  have ihA := fun s h d o l fu => (ih s h d o l fu).1
  have ihL := fun s h d o l fu => (ih s h d o l fu).2.1
  have ihF := fun s h d o l fu => (ih s h d o l fu).2.2.1
  have ihE := fun s h d o l fu => (ih s h d o l fu).2.2.2.1
  have ihP := fun s h d o l fu => (ih s h d o l fu).2.2.2.2.1
  have ihB := fun s h d o l fu => (ih s h d o l fu).2.2.2.2.2
  rw [invoke_eq _ (hp.get "il_go")]
  simp only [callFn, ilGo]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, derB_spec p (hp.get "der_b") n,
      ihA, ihL, ihF, ihE, ihP, ihB] <;>
    finish

include hp in
theorem ilgGo_step (n : Nat) (ih : IlgArmSpec p n) (ihl : IlGoSpec p n) : IlgGoSpec p (n + 1) := by
  intro s₀ h d o l fu
  unfold IlGoSpec at ihl
  have ihA := fun s h d o l fu => (ih s h d o l fu).1
  have ihL := fun s h d o l fu => (ih s h d o l fu).2.1
  have ihF := fun s h d o l fu => (ih s h d o l fu).2.2.1
  have ihE := fun s h d o l fu => (ih s h d o l fu).2.2.2.1
  have ihP := fun s h d o l fu => (ih s h d o l fu).2.2.2.2
  rw [invoke_eq _ (hp.get "ilg_go")]
  simp only [callFn, ilgGo]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, derB_spec p (hp.get "der_b") n,
      ihA, ihL, ihF, ihE, ihP, ihl] <;>
    finish

end specs

end L.Arena
