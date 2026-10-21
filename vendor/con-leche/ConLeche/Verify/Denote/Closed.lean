module

public import ConLeche.Verify.Denote.Depth
import ConLeche.Verify.Denote.Shift
public import ConLeche.Verify.Denote.VClosed

public section

/-!
# `denote`, closed and depth-independent (task #161, P3.2)

**Closedness is not an induction**: it is `denote_closed`
(`Verify/Denote/Shift.lean`) composed with `Term.liftN_eq_self`.

**The depth statement drops `EnvWF`**, following the shift it is built
on (see `Verify/Denote/Depth.lean`).
-/

namespace ConLeche.Verify

open ConLeche.Term ConLeche.Verify

open ConLeche (Env Expr Name Level PropWhen)

/-- **`denote`'s closedness law.**  A closed subject's reading
is closed, in the lifting form `EnvModel.acval_closed`
states it. -/
theorem denote_liftN_eq_self {acval : Name → (Name → Nat) → Term}
    {env : Env} {φ : Name → Nat}
    (hcl : ∀ n ψ, Term.Closed (acval n ψ))
    {e : Expr} {ea : Term} (hnf : e.hasFvar = false)
    (hb : e.looseBVarsBounded 0 = true)
    (h : denote acval env φ 0 e = some ea) (n k : Nat) :
    ea.liftN n k = ea :=
  Term.liftN_eq_self
    (Term.bvarsBelow.mono (Nat.zero_le k) (denote_closed hcl hnf hb h)) n

/-- **A closed term's reading does not depend on the depth**,
provided the reading itself is lift-invariant. -/
theorem denote_depth_of_closed {env : Env} {φ : Name → Nat}
    {acval : Name → (Name → Nat) → Term}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    {e : Expr} {ea : Term} (hfv : e.hasFvar = false)
    (hcl : ∀ k : Nat, ea.liftN 1 k = ea)
    (h : denote acval env φ 0 e = some ea) :
    ∀ d : Nat, denote acval env φ d e = some ea := by
  intro d
  induction d with
  | zero => exact h
  | succ d ih =>
    have hs := denote_shiftFrom (env := env) (acval := acval) (φ := φ)
      (p := 0) hacl e d (Nat.zero_le d)
      (Expr.WScoped.of_not_hasFvar hfv)
    rw [Expr.shiftFrom_eq_self_of_not_hasFvar hfv, ih] at hs
    rw [hs]
    simp [hcl]

end ConLeche.Verify
