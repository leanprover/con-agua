module

public import ConAgua.Checker.C1Switch
public import ConAgua.Checker.C1Keep
import ConAgua.Arena.FreezeFreshBase
import ConAgua.Arena.FreezeTruncBase
import ConAgua.Arena.IndexRel

@[expose] public section

/-!
# Back to the challenge's view after the solution's calls, on one region (lane compare2, H7)

The solution's jobs' witness `X` (from `freshMem mS`, header S's fresh memory, with `c1Q`) patched
with `freshMem m9`'s stream index (`c1Patch`) holds the challenge's jobs' memory half
(`c1_back`, through `JobM.csBack`), given both views of the same extents.
-/

namespace L.Checker

open L L.Arena ConRon.Arena ConRon.Bridge

section views
variable {mS m9 : Mem} (hfr : MemFrame csA csC m9 mS)
  (hext : ∀ i < frozen.length, fzExt mS (fzAt i) = fzExt m9 (fzAt i))
include hfr hext

/-- Off the stream index's arrays, both views cut alike. -/
theorem c1_trunc_eq {b : TieredArray} (hb : b ∉ csA) (hc : b ≠ CTL) :
    (truncFrozen mS).arr64 b = (truncFrozen m9).arr64 b := by
  by_cases hs : b ∈ fzSrcs
  · rw [← frozen_srcs, List.mem_map] at hs
    obtain ⟨e, he, rfl⟩ := hs
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    have hi' : i + 1 < frozen.length := by simp at hi; omega
    have hz : (frozen.drop 1)[i] = (frozen[i + 1].1, fzAt (i + 1)) := by
      simp only [List.getElem_drop, fzAt, List.getElem?_eq_getElem hi', Option.map_some, Option.getD_some]
      simp only [Nat.add_comm 1 i]
    rw [hz] at he ⊢
    rw [truncFrozen_mem mS he, truncFrozen_mem m9 he, hext _ hi', hfr.arr _ (by rwa [hz] at hb) (by rwa [hz] at hc)]
  · rw [truncFrozen_other _ _ hs, truncFrozen_other _ _ hs, hfr.arr _ hb hc]

/-- The cut stream index's arrays have the same sizes under both views. -/
theorem c1_trunc_size (b : TieredArray) :
    ((truncFrozen mS).arr64 b).size = ((truncFrozen m9).arr64 b).size := by
  by_cases hs : b ∈ fzSrcs
  · rw [← frozen_srcs, List.mem_map] at hs
    obtain ⟨e, he, rfl⟩ := hs
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    have hi' : i + 1 < frozen.length := by simp at hi; omega
    have hz : (frozen.drop 1)[i] = (frozen[i + 1].1, fzAt (i + 1)) := by
      simp only [List.getElem_drop, fzAt, List.getElem?_eq_getElem hi', Option.map_some, Option.getD_some]
      simp only [Nat.add_comm 1 i]
    rw [hz] at he ⊢
    rw [truncFrozen_mem mS he, truncFrozen_mem m9 he, hext _ hi', size_extract0, size_extract0, hfr.size]
  · rw [truncFrozen_other _ _ hs, truncFrozen_other _ _ hs, hfr.size]

/-- **The fresh memories of both views are a frame of the stream index's arrays and words.** -/
theorem c1_fresh_frame : MemFrame csA csC (freshMem m9) (freshMem mS) := by
  refine ⟨fun b hb hc => ?_, fun x hx => ?_, fun b => ?_⟩
  · rw [freshMem_arr, freshMem_arr, ite_eq_right hc, ite_eq_right hc]
    split
    · rw [c1_trunc_size hfr hext]
    · exact c1_trunc_eq hfr hext hb hc
  · rw [freshMem_arr, freshMem_arr, ite_eq_left rfl, ite_eq_left rfl, truncFrozen_ctl, truncFrozen_ctl]
    simp only [rdW, ← Array.getD_eq_getD_getElem?]
    rw [getD_freshCtl, getD_freshCtl]
    split
    · simp only [Array.getD_eq_getD_getElem?]; exact hfr.ctl x hx
    · rfl
  · rw [freshMem_arr, freshMem_arr]
    split
    · simp [freshCtl, truncFrozen_ctl, hfr.size]
    · split <;> simp [zeros, c1_trunc_size hfr hext]

end views

end L.Checker
