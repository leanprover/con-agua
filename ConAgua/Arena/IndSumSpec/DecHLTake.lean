import ConAgua.Arena.IndLibSpec
import ConAgua.Arena.PinsNatOp
import Std.Tactic.BVDecide.Normalize.Prop

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

end L.Ind

end
