module

public import ConAgua.Arena.ErecRd

@[expose] public section

/-!
# The record words the η readers read

A constructor record's level parameters (`decCI_ctorLp`) and an inductive record's level
parameters and η cap (`decCI_indCaps`), as words L reads (`RdOK`).
-/

open ConRon.Arena

namespace L.Arena

/-! ## The records -/

/-- **A constructor record's level parameters**: the slice at `p + 2`, `p + 3`. -/
theorem decCI_ctorLp {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd) {q : Word}
    {cv : IConstantVal} {np nf : Nat} {fam : NIdx} (h : decCI R q.toNat = some (.ctorInfo cv np nf fam)) :
    hslice? R (rd (q + 2)).toNat (rd (q + 3)).toNat = some cv.levelParams := by
  sorry

/-- **An inductive record's level parameters and η cap.** -/
structure IndRecR (R : Nat → Option Word) (rd : Word → Word) (q : Word) (cv : IConstantVal) (caps : IIndCaps) :
    Prop where
  lp : hslice? R (rd (q + 2)).toNat (rd (q + 3)).toNat = some cv.levelParams
  eta : caps.eta = (rd (q + 5) != 0)

/-- An inductive record decodes to `IndRecR`. -/
theorem decCI_indCaps {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd) {q : Word}
    {cv : IConstantVal} {caps : IIndCaps} (h : decCI R q.toNat = some (.indInfo cv caps))  :
    IndRecR R rd q cv caps := by
  cases hq : R q.toNat with
  | none => simp [decCI, nat?, hq] at h
  | some w =>
  simp only [decCI, nat?, hq, Option.map_some, Option.bind_eq_bind, Option.bind_some] at h
  rcases hk : w.toNat with _ | _ | _ | _ | _ | _ | _ | k
  all_goals (rw [hk] at h)
  all_goals simp only [Option.bind_eq_some_iff, Option.some.injEq, reduceCtorEq,
    and_false, exists_false, Option.pure_def] at h
  obtain ⟨cv', hcv, caps', hcaps, hc⟩ := h
  cases hc
  simp only [decCV, hlist?, nat?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.map_eq_some_iff, Option.some.injEq] at hcv
  obtain ⟨nm, -, ls, ⟨o, ⟨wo, hwo, rfl⟩, c, ⟨wc, hwc, rfl⟩, hs⟩, ty, -, rfl⟩ := hcv
  have h2 : rd (q + 2) = wo := hR.offN (k := 2) (hk := by decide) (by simpa [Nat.add_assoc] using hwo)
  have h3 : rd (q + 3) = wc := hR.offN (k := 3) (hk := by decide) (by simpa [Nat.add_assoc] using hwc)
  simp only [decCaps, bool?, nat?, hlist?, Option.bind_eq_bind, Option.pure_def,
    Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.some.injEq] at hcaps
  obtain ⟨e, ⟨we, hwe, rfl⟩, -, -, -, -, -, -, -, -, -, -, rfl⟩ := hcaps
  have h5 : rd (q + 5) = we := hR.offN (k := 5) (hk := by decide) (by simpa [Nat.add_assoc] using hwe)
  exact ⟨by rw [h2, h3]; exact hs, by rw [h5]⟩

end L.Arena
