module

public import ConLeche.SetModel.TaggedSum

@[expose] public section

/-!
# Countable unions (task #188)

The countable union `natUnion f = ⋃ₙ f n`, a member of `univ w` at
`w ≥ 1` when every `f n` is (`ω ∈ univ w`, `omega_mem_univ_succ`).

Everything here is over the bare `SetTheory` interface; no syntax.
-/

namespace ConLeche.SetTheory.Tower

universe u

variable {V : Type u} [SetTheory V]

/-- The union of a countable family `f 0 ∪ f 1 ∪ …` (the ω-indexed union
through the tag fibre). -/
noncomputable def natUnion (f : Nat → V) : V :=
  sUnion (image (natFibre f) omega)

theorem mem_natUnion {f : Nat → V} {x : V} : x ∈ˢ natUnion f ↔ ∃ n, x ∈ˢ f n := by
  unfold natUnion
  rw [mem_sUnion]
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hy
    obtain ⟨n, rfl, hfib⟩ := natFibre_of_mem f hk
    rw [hfib] at hxy
    exact ⟨n, hxy⟩
  · rintro ⟨n, hn⟩
    exact ⟨natFibre f (vnat n), mem_image.mpr ⟨vnat n, vnat_mem_omega n, rfl⟩,
      by rw [natFibre_vnat]; exact hn⟩

/-- A countable union of members of a positive axiomatic level is a
member (a size bound). -/
theorem natUnion_mem_tg_pos {w : Nat} (hw : w ≠ 0) {f : Nat → V}
    (h : ∀ n, f n ∈ˢ (tg w : V)) : natUnion f ∈ˢ (tg w : V) := by
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  unfold natUnion
  refine (tg_isTGUniverse (Nat.succ_ne_zero w')).famUnion_mem (omega_mem_tg_succ w') ?_
  intro k hk
  obtain ⟨n, rfl, hfib⟩ := natFibre_of_mem f hk
  rw [hfib]
  exact h n

end ConLeche.SetTheory.Tower
