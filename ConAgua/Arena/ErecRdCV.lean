module

public import ConAgua.Arena.ErecRd
public import ConAgua.Arena.WhnfBase
public import ConAgua.Arena.Env
import ConAgua.Arena.IndLibSpec

@[expose] public section

/-!
# Reading a constant record by word: its constant value and a recursor record

The constant value at `q + 1` and a recursor record (kind word `5`), word by word through any
reader (`RdOK`); shared by the `iota_target` refinement (the `whnfCore` chain) and the ι step's.
-/

open ConRon.Arena

namespace L.Arena

/-- The words of a `ConstantVal` decoded at `q + 1`. -/
theorem decCV_rd1 {R : Nat → Option Word} {rd : Word → Word} {q : Word} {cv : IConstantVal} (hR : RdOK R rd)
    (h : decCV R (q.toNat + 1) = some cv) :
    HW (rd (q + 1)) ∧ cv.name = decI (rd (q + 1)) ∧
      hslice? R (rd (q + 2)).toNat (rd (q + 3)).toNat = some cv.levelParams ∧
      cv.levelParams.length = (rd (q + 3)).toNat ∧
      HW (rd (q + 4)) ∧ cv.type = decI (rd (q + 4)) := by
  simp only [decCV, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨nm, hn, ls, hl, ty, ht, rfl⟩ := h
  obtain ⟨w1, hw1, hl1, rfl⟩ := hd?_some hn
  obtain ⟨w4, hw4, hl4, rfl⟩ := hd?_some ht
  simp only [hlist?, nat?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hl
  obtain ⟨o, ⟨w2, hw2, rfl⟩, c, ⟨w3, hw3, rfl⟩, hs⟩ := hl
  have e1 : rd (q + 1) = w1 := hR.at 1 rfl hw1
  have e2 : rd (q + 2) = w2 := hR.at 2 rfl (by rw [← hw2]; congr 1)
  have e3 : rd (q + 3) = w3 := hR.at 3 rfl (by rw [← hw3]; congr 1)
  have e4 : rd (q + 4) = w4 := hR.at 4 rfl (by rw [← hw4]; congr 1)
  rw [e1, e2, e3, e4]
  exact ⟨hl1, rfl, hs, (by simpa using L.Ind.mapM_opt_length _ _ _ hs), hl4, rfl⟩

/-- A recursor record by its kind word `5`. -/
theorem decCI_rec_rd {R : Nat → Option Word} {rd : Word → Word} {q : Word}
    {ci : IConstantInfo} (hR : RdOK R rd) (h : decCI R q.toNat = some ci) :
    (rd q = 5 → ∃ cv rules, ci = .recInfo cv (rd (q + 5)).toNat (rd (q + 6)).toNat (rd (q + 9) != 0)
      rules ∧ decCV R (q.toNat + 1) = some cv ∧
      decRules R (rd (q + 7)).toNat (rd (q + 8)).toNat = some rules) ∧
    (rd q ≠ 5 → ∀ cv mI rP isK rules, ci ≠ .recInfo cv mI rP isK rules) := by
  cases hq : R q.toNat with
  | none => simp [decCI, nat?, hq] at h
  | some w =>
  have hrd : rd q = w := hR.rd _ _ hq
  rw [hrd]
  simp only [decCI, nat?, hq, Option.map_some, Option.bind_eq_bind, Option.bind_some] at h
  constructor
  · intro hw; subst hw
    simp only [show UInt64.toNat 5 = 5 from rfl, bool?, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at h
    obtain ⟨cv, hcv, mI, ⟨w5, hw5, rfl⟩, rP, ⟨w6, hw6, rfl⟩, k, ⟨w9, hw9, rfl⟩, o, ⟨w7, hw7, rfl⟩,
      c, ⟨w8, hw8, rfl⟩, rules, hrules, hc⟩ := h
    cases hc
    have h5 : rd (q + 5) = w5 := hR.offN (k := 5) (hk := by decide) hw5
    have h6 : rd (q + 6) = w6 := hR.offN (k := 6) (hk := by decide) hw6
    have h7 : rd (q + 7) = w7 := hR.offN (k := 7) (hk := by decide) hw7
    have h8 : rd (q + 8) = w8 := hR.offN (k := 8) (hk := by decide) hw8
    have h9 : rd (q + 9) = w9 := hR.offN (k := 9) (hk := by decide) hw9
    exact ⟨cv, rules, by rw [h5, h6, h9], hcv, by rw [h7, h8]; exact hrules⟩
  · intro hw cv mI rP isK rules hc
    subst hc
    have hne : w.toNat ≠ 5 := fun e => hw (UInt64.toNat_inj.mp (by rw [e]; rfl))
    rcases hk : w.toNat with _ | _ | _ | _ | _ | _ | _ | k
    all_goals (rw [hk] at h hne; simp [Option.bind_eq_some_iff] at h hne)

end L.Arena
