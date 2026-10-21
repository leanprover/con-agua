module

public import ConLeche.Semantics.Tower.TowerKit
public import ConLeche.Model.Env.EnvModel
public import ConLeche.Semantics.Sat
public import ConLeche.Verify.Shift

public section

/-!
# The P currency — the truthfulness predicate and the context discipline

A module whose imports are what the two definitions need and nothing
else, so that the rules tier (`Model/Rules/*`) can state its motives
without importing the run-stated claims (task #305).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (CheckMode Env Expr Name whnf whnfCore inferTypeCore)

universe w

variable {V : Type w} [SetTheory V]

/-- **A graded type** (task #342, L5): a graded reading whose
denotation is a type (`IsTy`: a truth value or a strict set).  The
currency of the context's entries (`CtxOk`) and of inferred types
(`InferSem`), the fragment's `Sat`/`InferSem` typing clause. -/
@[expose] def WellDenotedTy (V : Type w) [SetTheory V] (ρ : Nat → V) (e : Term) :
    Prop :=
  WellDenoted V ρ e ∧ IsTy (interp V ρ e)

/-- The P-tier context discipline over `denote`
— scope bound, leaf types annotate, their interpretations read the
telescope, and they are graded types (`WellDenotedTy`) under every
satisfying valuation.  No fuel parameter. -/
@[expose] def CtxOk {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (d : Nat) (Δa : List Term) (e : Expr) : Prop :=
  Δa.length = d ∧
  ∀ l ∈ e.fvarLeaves, l.1 < d ∧ Expr.fvarsBelow l.1 l.2 ∧
    ∃ tya Aa,
      denote m.acval env φ d l.2 = some tya ∧
      Δa[d - 1 - l.1]? = some Aa ∧
      (∀ ρ : Nat → V, Sat V Δa ρ →
        interp V ρ tya
          = interp V (fun j => ρ (j + (d - 1 - l.1) + 1)) Aa) ∧
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedTy V ρ tya)

/-- **The context discipline without its grading** (task #342, L9): `CtxOk`'s
scope bound, leaf readings and links to the telescope, but not the leaf
types' grading.  The per-valuation motives of the rules tier
(`Model/Rules/Motive.lean`) take this and the grading at the one valuation
they speak about (`LeavesGr`): a reduct is graded only where its subject is
not the point, so a binder opened inside it has a domain graded at that
valuation and no other. -/
@[expose] def CtxOkS {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (d : Nat) (Δa : List Term) (e : Expr) : Prop :=
  Δa.length = d ∧
  ∀ l ∈ e.fvarLeaves, l.1 < d ∧ Expr.fvarsBelow l.1 l.2 ∧
    ∃ tya Aa,
      denote m.acval env φ d l.2 = some tya ∧
      Δa[d - 1 - l.1]? = some Aa ∧
      (∀ ρ : Nat → V, Sat V Δa ρ →
        interp V ρ tya
          = interp V (fun j => ρ (j + (d - 1 - l.1) + 1)) Aa)

/-- **The leaf types are graded types at one valuation** (task #342, L9):
`CtxOk`'s fourth conjunct, at `ρ` only. -/
@[expose] def LeavesGr {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (d : Nat) (e : Expr) (ρ : Nat → V) : Prop :=
  ∀ l ∈ e.fvarLeaves, ∀ tya : Term,
    denote m.acval env φ d l.2 = some tya → WellDenotedTy V ρ tya
