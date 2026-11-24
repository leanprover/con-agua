module

public import ConAgua.Checker.CmpSPhaseThr
public import ConAgua.Arena.FreezeView
import ConAgua.Arena.FreezeFreshBase

@[expose] public section

/-!
# A header's view gives the threads' first call (lane compare2, H7)

`csFirst_of_hdrView`, `csFirst_hdrView`: a buffer `B` that shows a memory `m` (`HdrView B m`, the compaction's view of
a header) starts every fresh thread at `freshMem m` (`CsFirst B m`), as `thr_first` does for the
flat buffer `bufOf m`.
-/

namespace L.Checker

open L L.Arena

/-- **A view's frozen entries but the seed are `truncFrozen m`'s arrays.** -/
theorem c1_hdr_trunc {B : Array Word} {m : Mem} (hV : HdrView B m) {i : Nat} (hi : i < frozen.length)
    (h1 : 1 ≤ i) : bufImg B (i + 1) = (truncFrozen m).arr64 (frozen[i].1) := by
  have hmem : (frozen[i].1, fzAt i) ∈ frozen.drop 1 := by
    have e : frozen[i] = (frozen.drop 1)[i - 1]'(by simp; omega) := by
      simp only [List.getElem_drop]; congr 1; omega
    have hz : fzAt i = frozen[i].2 := by
      simp only [fzAt, List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]
    rw [hz, e]; exact List.getElem_mem _
  have hsrc : (fzAt i).src = frozen[i].1 := by
    have := List.all_eq_true.mp frozen_src_self _ hmem
    simpa using this
  rw [hV.img i hi, ← hsrc, truncFrozen_mem m hmem]

/-- **A view's seed is `CTL[0‥256)`**, of 256 words. -/
theorem c1_hdr_seed {B : Array Word} {m : Mem} (hV : HdrView B m) :
    bufImg B 1 = (m.arr64 CTL).extract 0 256 ∧ 256 ≤ (m.arr64 CTL).size := by
  have h0 : (0 : Nat) < frozen.length := by rw [frozen_length]; decide
  have hz : fzAt 0 = ⟨CTL, fzC 256⟩ := rfl
  have hx : fzExt m (fzAt 0) = 256 := by rw [hz]; rfl
  have h := hV.img 0 h0
  have hs := hV.ext 0 h0
  rw [hx, hz] at h hs
  exact ⟨h, hs⟩

/-- **A header's view starts the threads** (`thr_first` for any buffer showing `m`). -/
theorem csFirst_of_hdrView {B : Array Word} {m : Mem} (hV : HdrView B m)
    (r : Mem) (j : Word) (hz : ∀ b ∈ parOwnedL, r.arr64 b = zeros (m.arr64 b).size)
    (hI : r.glob INIT = 0) :
    ∀ t, thrS t = true → (seedMem (bufMem (B) r j)).arr64 t = (freshMem m).arr64 t := by
  have hI' : (bufMem (B) r j).glob INIT = 0 := hI
  simp only [seedMem, ite_eq_left hI']
  generalize hW : bufMem (B) r j = W
  obtain ⟨hseed, h256⟩ := c1_hdr_seed hV
  have hctlf : W.arr64 CTLF = (m.arr64 CTL).extract 0 256 := by
    rw [← hW, bufMem_ctlf, hseed]
  have hlen : (W.len64 CTLF).toNat = 256 := by
    simp only [Mem.len64, hctlf, size_extract0, Nat.min_eq_left h256]; rfl
  have hctl : W.arr64 CTL = zeros (m.arr64 CTL).size := by
    rw [← hW, bufMem_ctl]; exact hz CTL (by decide)
  rw [hlen]
  have hsz : 256 ≤ (W.arr64 CTL).size := by rw [hctl]; simp [zeros, h256]
  have hnoop : ∀ k ∈ rrWs, ((W.copy64 CTL 0 CTLF 0 256).arr64 CTL).getD k 0 =
      ((W.copy64 CTL 0 CTLF 0 256).arr64 CTLF).getD k 0 := by
    intro k hk
    have hk' : k < 256 := (by decide : ∀ k ∈ rrWs, k < 256) k hk
    rw [getD_copy64 (by decide) 256 W 0 0 (by simp) (by simp) k, arr64_copy64_ne _ _ _ _ _ _ (by decide)]
    simp only [UInt64.toNat_zero, Nat.zero_le, true_and, Nat.zero_add, Nat.sub_zero]
    rw [ite_eq_left ⟨hk', by omega⟩]
  intro b hb
  have hrr := rereadMem_arr ((W.copy64 CTL 0 CTLF 0 256).setG INIT 1) (fun _ k hk => by
    rw [L.Mem.setG_arr64, L.Mem.setG_arr64]; exact hnoop k hk)
  rw [hrr]
  rw [show ∀ M : Mem, (M.setG INIT 1).arr64 b = M.arr64 b from fun _ => rfl]
  by_cases hbc : b = CTL
  · subst hbc
    rw [freshMem_arr, ite_eq_left rfl, truncFrozen_ctl]
    apply arr_eq_of_getD
    · rw [size_copy64, hctl, freshCtl_size]; simp [zeros]
    · intro k hk
      rw [size_copy64, hctl] at hk
      simp only [zeros, Array.size_replicate] at hk
      rw [getD_copy64 (by decide) 256 W 0 0 (by simp) (by simp) k, getD_freshCtl, hctl, hctlf]
      simp only [UInt64.toNat_zero, Nat.zero_le, true_and, Nat.zero_add, Nat.sub_zero, zeros,
        Array.size_replicate]
      by_cases h1 : k < 256
      · rw [ite_eq_left ⟨h1, hk⟩, ite_eq_left h1, getD_extract_lt _ _ _ _ (by rw [size_extract0]; omega),
          Nat.zero_add]
      · rw [ite_eq_right (by omega), ite_eq_right h1]
        simp [Array.getD_eq_getD_getElem?, hk]
  · rw [arr64_copy64_ne _ _ _ _ _ _ hbc, ← hW]
    rcases thrS_cases hb with ⟨k, hk, h1, rfl⟩ | ho
    · obtain ⟨-, hz', hc⟩ := frozen_facts hk h1
      rw [bufMem_frozen _ r j hk h1, c1_hdr_trunc hV hk h1, freshMem_arr,
        ite_eq_right (TieredArray.t0_ne hc), ite_eq_right hz']
    · obtain ⟨-, hsrc⟩ := owned_facts ho
      rw [bufMem_owned _ r j ho, hz b ho, freshMem_arr, ite_eq_right hbc,
        ite_eq_left (show b ∈ freshZ from List.mem_cons_of_mem _ ho), truncFrozen_other m b hsrc]

/-- `CsFirst` from a header's view. -/
theorem csFirst_hdrView {B : Array Word} {m : Mem} (hV : HdrView B m) : ConAgua.Final.CsFirst B m :=
  fun r j hz hI => csFirst_of_hdrView hV r j hz hI

end L.Checker
