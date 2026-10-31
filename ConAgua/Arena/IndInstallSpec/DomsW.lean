module

public import ConAgua.Arena.IndRealSpine
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr

@[expose] public section

/-!
# DomsW

Slice lemmas: `decHL` along the pool's growth (`decHL_grow`) and its elements as word reads
(`decHL_getI`, `decHL_get'`), and the `getD` readings `agGetD0–2`.
-/

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

theorem mapM_opt_congr {α β : Type} (f g : α → Option β) :
    ∀ (xs : List α), (∀ x ∈ xs, f x = g x) → xs.mapM f = xs.mapM g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.mapM_cons]
    rw [h x (List.mem_cons_self ..), mapM_opt_congr f g xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem decHL_grow {k : IdxKind} {m m' : Mem} (hg : IWGrow m m') {o l : Nat}
    (h : o + l ≤ iwTop m) : (decHL m' o l : Option (List (Idx k))) = decHL m o l := by
  simp only [decHL, hslice?]
  apply mapM_opt_congr
  intro j hj
  have hj' : j < l := List.mem_range.mp hj
  simp only [hd?, iwA]
  rw [hg.iwGet (o + j) (by omega)]

theorem decHL_getI {k : IdxKind} {m : Mem} {o l : Nat} {xs : List (Idx k)}
    (h : decHL m o l = some xs) (j : Nat) (hj : j < l) :
    iwH m (o + j) = some (xs[j]'(by rw [decHL_length m h]; exact hj)) := by
  have hl := decHL_length m h
  simp only [decHL, hslice?] at h
  have hget := mapM_opt_get (fun j => hd? (iwA m) (o + j)) (List.range l) xs h j (by simpa using hj)
  simpa [iwH] using hget

theorem decHL_get' {k : IdxKind} {m : Mem} {o l : Nat} {xs : List (Idx k)}
    (h : decHL m o l = some xs) (j : Nat) (hj : j < l) (hb : o + l < 2 ^ 64) :
    ∃ w, rdW (m.arr64 IW) (UInt64.ofNat (o + j)) = w ∧ w.toNat < 2 ^ 32 ∧
      xs[j]'(by rw [decHL_length m h]; exact hj) = decI w := by
  obtain ⟨w, h1, h2, h3⟩ := iwH_rdW (decHL_getI h j hj) (by omega)
  exact ⟨w, h1, h2, h3.symm⟩

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

theorem agGetD1 (r : List Word) : r.getD 1 0 = r.tail.headD 0 := by
  rcases r with _ | ⟨a, _ | ⟨b, c⟩⟩ <;> rfl
theorem agGetD2 (r : List Word) : r.getD 2 0 = r.tail.tail.headD 0 := by
  rcases r with _ | ⟨a, _ | ⟨b, _ | ⟨c, d⟩⟩⟩ <;> rfl
theorem agGetD0 (r : List Word) : r.getD 0 0 = r.headD 0 := by
  rcases r with _ | ⟨a, b⟩ <;> rfl

end L.Ind

end

end
