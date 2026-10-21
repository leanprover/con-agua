module

public import ConLeche.Verify.Abstract

public section

/-!
# Projection nodes and their table slots (task #175 wiring, W4c S6)

The tower-cons transport's syntactic side condition.  Consing a
tower-backed entry `(T, i)` changes the reading of exactly one node
shape — `.proj T i e` with *no* entry stored (the pair fallback) —
so a prefix reading survives the cons whenever the subject has **no
`.proj T i` node** (`Expr.NoProjAt`).  Two sources discharge it for
every stored expression:

* `noProjAt_of_constsResolve` — a resolving expression names only
  stored structures in its `.proj` nodes (`constsResolve`'s clause
  reads `find? s`), so when `T` is not stored there is no `.proj T _`
  node at all: the pre-block constants;
* `inferTypeCore_projSlotsOk` (`Verify/InferProjSlots.lean`) — full-grade
  inference types a `.proj`
  node only where a *tower* table entry types it, hereditarily through
  the fvar types it threads (`Expr.ProjSlotsOk`).  So an expression
  whose inference succeeded has no `.proj T i` node when the slot
  `(T, i)` was empty at that time (`ProjSlotsOk.noProjAt`): the
  block's own constants, checked before their entries exist.

Both predicates are hereditary through `.fvar` type annotations, as
`ConstsBound` is, because `denote` opens binders at fvars.
-/

namespace ConLeche

open ConLeche.Expr

/-! ## `NoProjAt` -/

/-- No `.proj T i` node, hereditarily (through fvar types). -/
@[expose] def Expr.NoProjAt (T : Name) (i : Nat) : Expr → Prop
  | .proj s j e => ¬ (s = T ∧ j = i) ∧ NoProjAt T i e
  | .app f a => NoProjAt T i f ∧ NoProjAt T i a
  | .lam ty b => NoProjAt T i ty ∧ NoProjAt T i b
  | .forallE ty b => NoProjAt T i ty ∧ NoProjAt T i b
  | .letE t v b => NoProjAt T i t ∧ NoProjAt T i v ∧ NoProjAt T i b
  | .fvar _ ty => NoProjAt T i ty
  | _ => True
termination_by e => e.sizeF
decreasing_by all_goals first
  | (simp [Expr.sizeF]; omega)
  | simp [Expr.sizeF]

namespace Expr

variable {T : Name} {i : Nat}

@[simp] theorem noProjAt_proj {s : Name} {j : Nat} {e : Expr} :
    NoProjAt T i (.proj s j e) ↔ ¬ (s = T ∧ j = i) ∧ NoProjAt T i e := by
  rw [NoProjAt]
@[simp] theorem noProjAt_app {f a : Expr} :
    NoProjAt T i (.app f a) ↔ NoProjAt T i f ∧ NoProjAt T i a := by
  rw [NoProjAt]
@[simp] theorem noProjAt_lam {ty b : Expr} :
    NoProjAt T i (.lam ty b) ↔ NoProjAt T i ty ∧ NoProjAt T i b := by
  rw [NoProjAt]
@[simp] theorem noProjAt_forallE {ty b : Expr} :
    NoProjAt T i (.forallE ty b) ↔ NoProjAt T i ty ∧ NoProjAt T i b := by
  rw [NoProjAt]
@[simp] theorem noProjAt_letE {t v b : Expr} :
    NoProjAt T i (.letE t v b) ↔
      NoProjAt T i t ∧ NoProjAt T i v ∧ NoProjAt T i b := by
  rw [NoProjAt]
@[simp] theorem noProjAt_fvar {idx : Nat} {ty : Expr} :
    NoProjAt T i (.fvar idx ty) ↔ NoProjAt T i ty := by
  rw [NoProjAt]
@[simp] theorem noProjAt_bvar {j : Nat} : NoProjAt T i (.bvar j) := by
  rw [NoProjAt] <;> simp
@[simp] theorem noProjAt_sort {u : Level} : NoProjAt T i (.sort u) := by
  rw [NoProjAt] <;> simp
@[simp] theorem noProjAt_const {n : Name} {us : List Level} :
    NoProjAt T i (.const n us) := by
  rw [NoProjAt] <;> simp
@[simp] theorem noProjAt_lit {l : Literal} : NoProjAt T i (.lit l) := by
  rw [NoProjAt] <;> simp

/-- Instantiation preserves the absence: every node of the result is a
node of the body or of the substituted term. -/
theorem NoProjAt.instantiate1 {v : Expr} (hv : NoProjAt T i v) :
    ∀ (e : Expr) (d : Nat), NoProjAt T i e →
      NoProjAt T i (e.instantiate1 v d) := by
  intro e
  induction e with
  | bvar j =>
    intro d _
    rw [Expr.instantiate1]
    split
    · exact hv
    · split <;> simp
  | sort u => intro d _; rw [Expr.instantiate1]; simp
  | const n us => intro d h; rw [Expr.instantiate1]; exact h
  | fvar idx ty => intro d h; rw [Expr.instantiate1]; exact h
  | lit l => intro d _; rw [Expr.instantiate1]; simp
  | app f a ihf iha =>
    intro d h
    rw [noProjAt_app] at h
    rw [Expr.instantiate1, noProjAt_app]
    exact ⟨ihf d h.1, iha d h.2⟩
  | lam ty b ihty ihb =>
    intro d h
    rw [noProjAt_lam] at h
    rw [Expr.instantiate1, noProjAt_lam]
    exact ⟨ihty d h.1, ihb (d + 1) h.2⟩
  | forallE ty b ihty ihb =>
    intro d h
    rw [noProjAt_forallE] at h
    rw [Expr.instantiate1, noProjAt_forallE]
    exact ⟨ihty d h.1, ihb (d + 1) h.2⟩
  | letE t val b iht ihval ihb =>
    intro d h
    rw [noProjAt_letE] at h
    rw [Expr.instantiate1, noProjAt_letE]
    exact ⟨iht d h.1, ihval d h.2.1, ihb (d + 1) h.2.2⟩
  | proj s j e ihe =>
    intro d h
    rw [noProjAt_proj] at h
    rw [Expr.instantiate1, noProjAt_proj]
    exact ⟨h.1, ihe d h.2⟩

/-- Lifting the loose variables moves no node. -/
theorem NoProjAt.liftLooseBVars {k : Nat} :
    ∀ {e : Expr} {c : Nat}, NoProjAt T i e → NoProjAt T i (e.liftLooseBVars k c) := by
  intro e
  induction e with
  | bvar j => intro c _; simp only [Expr.liftLooseBVars]; split <;> simp
  | fvar idx ty ih => intro c h; simpa [Expr.liftLooseBVars] using h
  | sort u => intro c _; simp [Expr.liftLooseBVars]
  | const n us => intro c _; simp [Expr.liftLooseBVars]
  | lit l => intro c _; simp [Expr.liftLooseBVars]
  | app f a ihf iha =>
    intro c h
    rw [noProjAt_app] at h
    simp only [Expr.liftLooseBVars, noProjAt_app]
    exact ⟨ihf h.1, iha h.2⟩
  | lam ty b ihty ihb =>
    intro c h
    rw [noProjAt_lam] at h
    simp only [Expr.liftLooseBVars, noProjAt_lam]
    exact ⟨ihty h.1, ihb h.2⟩
  | forallE ty b ihty ihb =>
    intro c h
    rw [noProjAt_forallE] at h
    simp only [Expr.liftLooseBVars, noProjAt_forallE]
    exact ⟨ihty h.1, ihb h.2⟩
  | letE t v b iht ihv ihb =>
    intro c h
    rw [noProjAt_letE] at h
    simp only [Expr.liftLooseBVars, noProjAt_letE]
    exact ⟨iht h.1, ihv h.2.1, ihb h.2.2⟩
  | proj s j e ih =>
    intro c h
    rw [noProjAt_proj] at h
    simp only [Expr.liftLooseBVars, noProjAt_proj]
    exact ⟨h.1, ih h.2⟩

/-- Level instantiation moves no node. -/
theorem NoProjAt.instantiateLevelParams (ks : List Name) (us : List Level) :
    ∀ e : Expr, NoProjAt T i e →
      NoProjAt T i (e.instantiateLevelParams ks us) := by
  intro e
  induction e with
  | bvar j => intro _; simp [Expr.instantiateLevelParams]
  | sort u => intro _; simp [Expr.instantiateLevelParams]
  | const n vs => intro _; simp [Expr.instantiateLevelParams]
  | lit l => intro _; simp [Expr.instantiateLevelParams]
  | fvar idx ty ih =>
    intro h
    rw [noProjAt_fvar] at h
    rw [Expr.instantiateLevelParams, noProjAt_fvar]
    exact ih h
  | app f a ihf iha =>
    intro h
    rw [noProjAt_app] at h
    rw [Expr.instantiateLevelParams, noProjAt_app]
    exact ⟨ihf h.1, iha h.2⟩
  | lam ty b ihty ihb =>
    intro h
    rw [noProjAt_lam] at h
    rw [Expr.instantiateLevelParams, noProjAt_lam]
    exact ⟨ihty h.1, ihb h.2⟩
  | forallE ty b ihty ihb =>
    intro h
    rw [noProjAt_forallE] at h
    rw [Expr.instantiateLevelParams, noProjAt_forallE]
    exact ⟨ihty h.1, ihb h.2⟩
  | letE t val b iht ihval ihb =>
    intro h
    rw [noProjAt_letE] at h
    rw [Expr.instantiateLevelParams, noProjAt_letE]
    exact ⟨iht h.1, ihval h.2.1, ihb h.2.2⟩
  | proj s j e ihe =>
    intro h
    rw [noProjAt_proj] at h
    rw [Expr.instantiateLevelParams, noProjAt_proj]
    exact ⟨h.1, ihe h.2⟩

/-- **The pre-block source**: a resolving expression names only stored
structures in its `.proj` nodes, so an unstored `T` occurs in none. -/
theorem noProjAt_of_constsResolve {env : Env} (hT : env.find? T = none) :
    ∀ e : Expr, e.constsResolve env = true → NoProjAt T i e := by
  intro e
  induction e with
  | bvar j => intro _; simp
  | sort u => intro _; simp
  | lit l => intro _; simp
  | const n us => intro _; simp
  | fvar idx ty ih =>
    intro h
    rw [noProjAt_fvar]
    exact ih (by simpa [Expr.constsResolve] using h)
  | app f a ihf iha =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    exact noProjAt_app.mpr ⟨ihf h.1, iha h.2⟩
  | lam ty b ihty ihb =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    exact noProjAt_lam.mpr ⟨ihty h.1, ihb h.2⟩
  | forallE ty b ihty ihb =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    exact noProjAt_forallE.mpr ⟨ihty h.1, ihb h.2⟩
  | letE ty v b ihty ihv ihb =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    exact noProjAt_letE.mpr ⟨ihty h.1.1, ihv h.1.2, ihb h.2⟩
  | proj s j e ihe =>
    intro h
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    refine noProjAt_proj.mpr ⟨?_, ihe h.2⟩
    rintro ⟨rfl, -⟩
    rw [hT] at h
    exact nomatch h.1

/-! ## `ProjSlotsOk` and `FvarTysOk` -/

/-- Every `.proj s j` node's slot holds a projection-table entry,
hereditarily (through fvar types). -/
def ProjSlotsOk (env : Env) : Expr → Prop
  | .proj s j e => (∃ entry : ProjEntry, env.findProj? s j = some entry) ∧
      ProjSlotsOk env e
  | .app f a => ProjSlotsOk env f ∧ ProjSlotsOk env a
  | .lam ty b => ProjSlotsOk env ty ∧ ProjSlotsOk env b
  | .forallE ty b => ProjSlotsOk env ty ∧ ProjSlotsOk env b
  | .letE t v b => ProjSlotsOk env t ∧ ProjSlotsOk env v ∧ ProjSlotsOk env b
  | .fvar _ ty => ProjSlotsOk env ty
  | _ => True
termination_by e => e.sizeF
decreasing_by all_goals first
  | (simp [Expr.sizeF]; omega)
  | simp [Expr.sizeF]

/-- Every fvar node's type annotation is `ProjSlotsOk` (vacuous at a
closed term; inference opens binders at fvars typed by the binders'
own domains and copies fvar nodes verbatim). -/
def FvarTysOk (env : Env) : Expr → Prop
  | .fvar _ ty => ProjSlotsOk env ty
  | .proj _ _ e => FvarTysOk env e
  | .app f a => FvarTysOk env f ∧ FvarTysOk env a
  | .lam ty b => FvarTysOk env ty ∧ FvarTysOk env b
  | .forallE ty b => FvarTysOk env ty ∧ FvarTysOk env b
  | .letE t v b => FvarTysOk env t ∧ FvarTysOk env v ∧ FvarTysOk env b
  | _ => True
termination_by e => e.sizeF
decreasing_by all_goals first
  | (simp [Expr.sizeF]; omega)
  | simp [Expr.sizeF]

variable {env : Env}

@[simp] theorem projSlotsOk_proj {s : Name} {j : Nat} {e : Expr} :
    ProjSlotsOk env (.proj s j e) ↔
      (∃ entry : ProjEntry, env.findProj? s j = some entry) ∧
        ProjSlotsOk env e := by
  rw [ProjSlotsOk]
@[simp] theorem projSlotsOk_app {f a : Expr} :
    ProjSlotsOk env (.app f a) ↔ ProjSlotsOk env f ∧ ProjSlotsOk env a := by
  rw [ProjSlotsOk]
@[simp] theorem projSlotsOk_lam {ty b : Expr} :
    ProjSlotsOk env (.lam ty b) ↔
      ProjSlotsOk env ty ∧ ProjSlotsOk env b := by
  rw [ProjSlotsOk]
@[simp] theorem projSlotsOk_forallE {ty b : Expr}
    :
    ProjSlotsOk env (.forallE ty b) ↔
      ProjSlotsOk env ty ∧ ProjSlotsOk env b := by
  rw [ProjSlotsOk]
@[simp] theorem projSlotsOk_letE {t v b : Expr} :
    ProjSlotsOk env (.letE t v b) ↔
      ProjSlotsOk env t ∧ ProjSlotsOk env v ∧ ProjSlotsOk env b := by
  rw [ProjSlotsOk]
@[simp] theorem projSlotsOk_fvar {idx : Nat} {ty : Expr} :
    ProjSlotsOk env (.fvar idx ty) ↔ ProjSlotsOk env ty := by
  rw [ProjSlotsOk]
@[simp] theorem projSlotsOk_bvar {j : Nat} : ProjSlotsOk env (.bvar j) := by
  rw [ProjSlotsOk] <;> simp
@[simp] theorem projSlotsOk_sort {u : Level} : ProjSlotsOk env (.sort u) := by
  rw [ProjSlotsOk] <;> simp
@[simp] theorem projSlotsOk_const {n : Name} {us : List Level} :
    ProjSlotsOk env (.const n us) := by
  rw [ProjSlotsOk] <;> simp
@[simp] theorem projSlotsOk_lit {l : Literal} : ProjSlotsOk env (.lit l) := by
  rw [ProjSlotsOk] <;> simp

@[simp] theorem fvarTysOk_fvar {idx : Nat} {ty : Expr} :
    FvarTysOk env (.fvar idx ty) ↔ ProjSlotsOk env ty := by
  rw [FvarTysOk]
@[simp] theorem fvarTysOk_proj {s : Name} {j : Nat} {e : Expr} :
    FvarTysOk env (.proj s j e) ↔ FvarTysOk env e := by
  rw [FvarTysOk]
@[simp] theorem fvarTysOk_app {f a : Expr} :
    FvarTysOk env (.app f a) ↔ FvarTysOk env f ∧ FvarTysOk env a := by
  rw [FvarTysOk]
@[simp] theorem fvarTysOk_lam {ty b : Expr} :
    FvarTysOk env (.lam ty b) ↔ FvarTysOk env ty ∧ FvarTysOk env b := by
  rw [FvarTysOk]
@[simp] theorem fvarTysOk_forallE {ty b : Expr} :
    FvarTysOk env (.forallE ty b) ↔
      FvarTysOk env ty ∧ FvarTysOk env b := by
  rw [FvarTysOk]
@[simp] theorem fvarTysOk_letE {t v b : Expr} :
    FvarTysOk env (.letE t v b) ↔
      FvarTysOk env t ∧ FvarTysOk env v ∧ FvarTysOk env b := by
  rw [FvarTysOk]
@[simp] theorem fvarTysOk_bvar {j : Nat} : FvarTysOk env (.bvar j) := by
  rw [FvarTysOk] <;> simp
@[simp] theorem fvarTysOk_sort {u : Level} : FvarTysOk env (.sort u) := by
  rw [FvarTysOk] <;> simp
@[simp] theorem fvarTysOk_const {n : Name} {us : List Level} :
    FvarTysOk env (.const n us) := by
  rw [FvarTysOk] <;> simp
@[simp] theorem fvarTysOk_lit {l : Literal} : FvarTysOk env (.lit l) := by
  rw [FvarTysOk] <;> simp

/-- A closed (fvar-free) expression satisfies the input discipline
vacuously. -/
theorem FvarTysOk.of_not_hasFvar :
    ∀ e : Expr, e.hasFvar = false → FvarTysOk env e := by
  intro e
  induction e with
  | bvar j => intro _; simp
  | sort u => intro _; simp
  | const n us => intro _; simp
  | lit l => intro _; simp
  | fvar idx ty => intro h; simp [Expr.hasFvar] at h
  | app f a ihf iha =>
    intro h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    exact fvarTysOk_app.mpr ⟨ihf h.1, iha h.2⟩
  | lam ty b ihty ihb =>
    intro h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    exact fvarTysOk_lam.mpr ⟨ihty h.1, ihb h.2⟩
  | forallE ty b ihty ihb =>
    intro h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    exact fvarTysOk_forallE.mpr ⟨ihty h.1, ihb h.2⟩
  | letE t v b iht ihv ihb =>
    intro h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    exact fvarTysOk_letE.mpr ⟨iht h.1.1, ihv h.1.2, ihb h.2⟩
  | proj s j e ihe =>
    intro h
    exact fvarTysOk_proj.mpr (ihe (by simpa [Expr.hasFvar] using h))

/-- Instantiation keeps the input discipline when the substituted term
has it. -/
theorem FvarTysOk.instantiate1 {v : Expr} (hv : FvarTysOk env v) :
    ∀ (e : Expr) (d : Nat), FvarTysOk env e →
      FvarTysOk env (e.instantiate1 v d) := by
  intro e
  induction e with
  | bvar j =>
    intro d _
    rw [Expr.instantiate1]
    split
    · exact hv
    · split <;> simp
  | sort u => intro d _; rw [Expr.instantiate1]; simp
  | const n us => intro d h; rw [Expr.instantiate1]; exact h
  | fvar idx ty => intro d h; rw [Expr.instantiate1]; exact h
  | lit l => intro d _; rw [Expr.instantiate1]; simp
  | app f a ihf iha =>
    intro d h
    rw [fvarTysOk_app] at h
    rw [Expr.instantiate1, fvarTysOk_app]
    exact ⟨ihf d h.1, iha d h.2⟩
  | lam ty b ihty ihb =>
    intro d h
    rw [fvarTysOk_lam] at h
    rw [Expr.instantiate1, fvarTysOk_lam]
    exact ⟨ihty d h.1, ihb (d + 1) h.2⟩
  | forallE ty b ihty ihb =>
    intro d h
    rw [fvarTysOk_forallE] at h
    rw [Expr.instantiate1, fvarTysOk_forallE]
    exact ⟨ihty d h.1, ihb (d + 1) h.2⟩
  | letE t val b iht ihval ihb =>
    intro d h
    rw [fvarTysOk_letE] at h
    rw [Expr.instantiate1, fvarTysOk_letE]
    exact ⟨iht d h.1, ihval d h.2.1, ihb (d + 1) h.2.2⟩
  | proj s j e ihe =>
    intro d h
    rw [fvarTysOk_proj] at h
    rw [Expr.instantiate1, fvarTysOk_proj]
    exact ihe d h

/-- **The `NoProjAt` source**: an occupied slot at every `.proj` node
means an *empty* slot's node is absent. -/
theorem ProjSlotsOk.noProjAt (hslot : env.findProj? T i = none) :
    ∀ e : Expr, ProjSlotsOk env e → NoProjAt T i e := by
  intro e
  induction e with
  | bvar j => intro _; simp
  | sort u => intro _; simp
  | const n us => intro _; simp
  | lit l => intro _; simp
  | fvar idx ty ih =>
    intro h
    rw [projSlotsOk_fvar] at h
    exact noProjAt_fvar.mpr (ih h)
  | app f a ihf iha =>
    intro h
    rw [projSlotsOk_app] at h
    exact noProjAt_app.mpr ⟨ihf h.1, iha h.2⟩
  | lam ty b ihty ihb =>
    intro h
    rw [projSlotsOk_lam] at h
    exact noProjAt_lam.mpr ⟨ihty h.1, ihb h.2⟩
  | forallE ty b ihty ihb =>
    intro h
    rw [projSlotsOk_forallE] at h
    exact noProjAt_forallE.mpr ⟨ihty h.1, ihb h.2⟩
  | letE t v b iht ihv ihb =>
    intro h
    rw [projSlotsOk_letE] at h
    exact noProjAt_letE.mpr ⟨iht h.1, ihv h.2.1, ihb h.2.2⟩
  | proj s j e ihe =>
    intro h
    rw [projSlotsOk_proj] at h
    obtain ⟨⟨entry, hfe⟩, he⟩ := h
    refine noProjAt_proj.mpr ⟨?_, ihe he⟩
    rintro ⟨rfl, rfl⟩
    rw [hslot] at hfe
    exact nomatch hfe

end Expr

end ConLeche
