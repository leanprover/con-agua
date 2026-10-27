import ConAgua.Arena.IndPartsSpec5

/-!
# DecHLTake

`decHL_take`, `map_decI_inj`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem decHL_take {k : IdxKind} {m : Mem} {o l : Nat} {xs : List (Idx k)}
    (h : decHL m o l = some xs) (j : Nat) (hj : j ≤ l) : decHL m o j = some (xs.take j) := by
  have hl := decHL_length m h
  simp only [decHL, hslice?] at h ⊢
  have hr : List.range l = List.range j ++ (List.range (l - j)).map (j + ·) := by
    rw [show l = j + (l - j) by omega, List.range_add]; simp
  rw [hr, List.mapM_append] at h
  cases e1 : (List.range j).mapM (fun i => (hd? (iwA m) (o + i) : Option (Idx k))) with
  | none => rw [e1] at h; simp at h
  | some ys =>
  cases e2 : ((List.range (l - j)).map (j + ·)).mapM (fun i => (hd? (iwA m) (o + i) : Option (Idx k))) with
  | none => rw [e1, e2] at h; simp at h
  | some zs =>
  rw [e1, e2] at h
  simp at h
  have hy := mapM_opt_length _ _ _ e1
  simp at hy
  rw [← h]; simp [hy]

theorem map_decI_inj {k : IdxKind} : ∀ (ws vs : List Word), (∀ w ∈ ws, w.toNat < 2 ^ 32) →
    (∀ w ∈ vs, w.toNat < 2 ^ 32) → (ws.map (decI (k := k)) = vs.map decI ↔ ws = vs)
  | [], [], _, _ => by simp
  | [], _ :: _, _, _ => by simp
  | _ :: _, [], _, _ => by simp
  | w :: ws, v :: vs, hw, hv => by
    simp only [List.map_cons, List.cons.injEq]
    rw [map_decI_inj ws vs (fun x hx => hw x (by simp [hx])) (fun x hx => hv x (by simp [hx]))]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨decI_inj (hw w (by simp)) (hv v (by simp)) h1, h2⟩
    · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩

end L.Ind

end
