module

public import ConLeche.Verify.Denote.Lemmas
public import ConLeche.Verify.Subst

public section

/-!
# The reading's blindness to erasure (task #161, IND TIER)

**`denote_erasedEq`** — the reading is blind to exactly what
`Expr.ErasedEq` ignores: `fvar` type annotations.  `denote`'s
binder clauses instantiate with the binder's own type, so the
recursive step goes through `Expr.ErasedEq.instantiate1` at two
`fvar`s with the same index.
-/

namespace ConLeche.Verify

open ConLeche.Term ConLeche.Verify

open ConLeche (Env Expr Name Level ConstantInfo)

variable {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → Term}

/-- **Erasure-equal expressions read equally**. -/
theorem denote_erasedEq {acval : Name → (Name → Nat) → Term}
    {env : Env} {φ : Name → Nat} :
    ∀ {e₁ e₂ : Expr}, Expr.ErasedEq e₁ e₂ →
      ∀ d : Nat, denote acval env φ d e₁ = denote acval env φ d e₂
  | .bvar i, e₂, he, _ => by
    match e₂, he with
    | .bvar j, he => obtain rfl : i = j := he; rfl
  | .fvar i ty, e₂, he, d => by
    match e₂, he with
    | .fvar j ty', he =>
      obtain rfl : i = j := he
      simp [denote_fvar]
  | .sort u, e₂, he, _ => by
    match e₂, he with
    | .sort u', he => obtain rfl : u = u' := he; rfl
  | .const n us, e₂, he, _ => by
    match e₂, he with
    | .const n' us', he =>
      obtain ⟨rfl, rfl⟩ : n = n' ∧ us = us' := he
      rfl
  | .app f a, e₂, he, d => by
    match e₂, he with
    | .app g b, he =>
      obtain ⟨h1, h2⟩ : Expr.ErasedEq f g ∧ Expr.ErasedEq a b := he
      simp only [denote_app, denote_erasedEq h1 d,
        denote_erasedEq h2 d]
  | .forallE ty body, e₂, he, d => by
    match e₂, he with
    | .forallE ty' body', he =>
      obtain ⟨h1, h2⟩ :
          Expr.ErasedEq ty ty' ∧ Expr.ErasedEq body body' := he
      simp only [denote_forallE, denote_erasedEq h1 d,
        denote_erasedEq (Expr.ErasedEq.instantiate1 h2
          (show Expr.ErasedEq (.fvar d ty) (.fvar d ty') from rfl))
          (d + 1)]
  | .lam ty body, e₂, he, d => by
    match e₂, he with
    | .lam ty' body', he =>
      obtain ⟨h1, h2⟩ :
          Expr.ErasedEq ty ty' ∧ Expr.ErasedEq body body' := he
      simp only [denote_lam, denote_erasedEq h1 d,
        denote_erasedEq (Expr.ErasedEq.instantiate1 h2
          (show Expr.ErasedEq (.fvar d ty) (.fvar d ty') from rfl))
          (d + 1)]
  | .letE ty vl body, e₂, he, d => by
    match e₂, he with
    | .letE ty' vl' body', he =>
      obtain ⟨h0, h1, h2⟩ :
          Expr.ErasedEq ty ty' ∧ Expr.ErasedEq vl vl' ∧ Expr.ErasedEq body body' := he
      simp only [denote_letE, denote_erasedEq h0 d, denote_erasedEq h1 d,
        denote_erasedEq (Expr.ErasedEq.instantiate1 h2
          (show Expr.ErasedEq (.fvar d ty) (.fvar d ty') from rfl))
          (d + 1)]
  | .lit l, e₂, he, _ => by
    match e₂, he with
    | .lit l', he => obtain rfl : l = l' := he; rfl
  | .proj sn i pe, e₂, he, d => by
    match e₂, he with
    | .proj sn' i' pe', he =>
      obtain ⟨rfl, rfl, h⟩ :
          sn = sn' ∧ i = i' ∧ Expr.ErasedEq pe pe' := he
      simp only [denote_proj, denote_erasedEq h d]
termination_by e₁ => e₁.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

end ConLeche.Verify
