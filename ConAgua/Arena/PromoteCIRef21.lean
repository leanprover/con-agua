import ConAgua.Arena.PromoteCIRef20

/-!
# The six `decCI` shapes, both directions
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

section mk
variable {A : Array Word} {dn : NIdx → Option ConLeche.Name} {d : Nat} {cv : IConstantVal}

theorem decCI_ax (hk : nat? A d = some 0) (hcv : decCV A (d + 1) = some cv) :
    decCI A dn d = some (.axiomInfo cv) := by
  unfold decCI; simp [hk, hcv]

theorem decCI_df {e : EIdx} {h : ConLeche.ReducibilityHint} (hk : nat? A d = some 1)
    (hcv : decCV A (d + 1) = some cv) (he : hd? A (d + 5) = some e)
    (hh : decHint A (d + 6) = some h) : decCI A dn d = some (.defnInfo cv e h) := by
  unfold decCI; simp [hk, hcv, he, hh]

theorem decCI_th (hk : nat? A d = some 2) (hcv : decCV A (d + 1) = some cv) :
    decCI A dn d = some (.thmInfo cv) := by
  unfold decCI; simp [hk, hcv]

theorem decCI_in {caps : IIndCaps} (hk : nat? A d = some 3) (hcv : decCV A (d + 1) = some cv)
    (hc : decCaps A dn (d + 5) = some caps) : decCI A dn d = some (.indInfo cv caps) := by
  unfold decCI; simp [hk, hcv, hc]

theorem decCI_ct {np nf : Nat} (hk : nat? A d = some 4) (hcv : decCV A (d + 1) = some cv)
    (h5 : nat? A (d + 5) = some np) (h6 : nat? A (d + 6) = some nf) :
    decCI A dn d = some (.ctorInfo cv np nf) := by
  unfold decCI; simp [hk, hcv, h5, h6]

theorem decCI_rc {mi rp ro rc : Nat} {rls : List IRecRule} (hk : nat? A d = some 5)
    (hcv : decCV A (d + 1) = some cv) (h5 : nat? A (d + 5) = some mi)
    (h6 : nat? A (d + 6) = some rp) (h7 : nat? A (d + 7) = some ro)
    (h8 : nat? A (d + 8) = some rc) (hr : decRules A ro rc = some rls) :
    decCI A dn d = some (.recInfo cv mi rp rls) := by
  unfold decCI; simp [hk, hcv, h5, h6, h7, h8, hr]

end mk

/-- The shapes of a decoded constant record. -/
theorem decCI_cases {A : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Nat}
    {ci : IConstantInfo} (h : decCI A dn q = some ci) :
    (∃ cv, nat? A q = some 0 ∧ decCV A (q + 1) = some cv ∧ ci = .axiomInfo cv) ∨
    (∃ cv e hh, nat? A q = some 1 ∧ decCV A (q + 1) = some cv ∧ hd? A (q + 5) = some e ∧
      decHint A (q + 6) = some hh ∧ ci = .defnInfo cv e hh) ∨
    (∃ cv, nat? A q = some 2 ∧ decCV A (q + 1) = some cv ∧ ci = .thmInfo cv) ∨
    (∃ cv caps, nat? A q = some 3 ∧ decCV A (q + 1) = some cv ∧ decCaps A dn (q + 5) = some caps ∧
      ci = .indInfo cv caps) ∨
    (∃ cv np nf, nat? A q = some 4 ∧ decCV A (q + 1) = some cv ∧ nat? A (q + 5) = some np ∧
      nat? A (q + 6) = some nf ∧ ci = .ctorInfo cv np nf) ∨
    (∃ cv mi rp ro rc rls, nat? A q = some 5 ∧ decCV A (q + 1) = some cv ∧
      nat? A (q + 5) = some mi ∧ nat? A (q + 6) = some rp ∧ nat? A (q + 7) = some ro ∧
      nat? A (q + 8) = some rc ∧ decRules A ro rc = some rls ∧ ci = .recInfo cv mi rp rls) := by
  unfold decCI at h
  cases hk : nat? A q with
  | none => simp [hk] at h
  | some k =>
    simp only [hk, Option.bind_eq_bind, Option.bind_some] at h
    rcases k with _ | _ | _ | _ | _ | _ | k
    · left
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨cv, hcv, rfl⟩ := h
      exact ⟨cv, rfl, hcv, rfl⟩
    · right; left
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨cv, hcv, e, he, hh, hhh, rfl⟩ := h
      exact ⟨cv, e, hh, rfl, hcv, he, hhh, rfl⟩
    · right; right; left
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨cv, hcv, rfl⟩ := h
      exact ⟨cv, rfl, hcv, rfl⟩
    · right; right; right; left
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨cv, hcv, caps, hc, rfl⟩ := h
      exact ⟨cv, caps, rfl, hcv, hc, rfl⟩
    · right; right; right; right; left
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨cv, hcv, np, hnp, nf, hnf, rfl⟩ := h
      exact ⟨cv, np, nf, rfl, hcv, hnp, hnf, rfl⟩
    · right; right; right; right; right
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨cv, hcv, mi, hmi, rp, hrp, ro, hro, rc, hrc, rls, hr, rfl⟩ := h
      exact ⟨cv, mi, rp, ro, rc, rls, rfl, hcv, hmi, hrp, hro, hrc, hr, rfl⟩
    · simp at h

end L.Arena
