module

public import ConAgua.Arena.IndRealSpine
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.Arena.IndLibSpec
import ConAgua.Arena.IndMaster

@[expose] public section

/-!
# DomsW

Slice lemmas: `decHL` along the pool's growth (`decHL_grow`) and its elements as word reads
(`decHL_getI`, `decHL_get'`).
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

theorem decHL_grow {k : IdxKind} {m m' : Mem} (hg : IWGrow m m') {o l : Nat}
    (h : o + l ≤ iwTop m) : (decHL m' o l : Option (List (Idx k))) = decHL m o l := by
  simp only [decHL, hslice?]
  apply L.Ind.mapM_congr_of
  intro j hj
  have hj' : j < l := List.mem_range.mp hj
  simp only [hd?, iwA, aread_apply, aread_apply]
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

end L.Ind

end

end
