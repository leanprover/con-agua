module

public import ConAgua.Arena.FreezeBuf

@[expose] public section

/-!
# A header's view (lane compare, design (i))

Phase B reads a frozen buffer only through its header: `bufMem B r j` (`Arena/FreezeRel.lean`)
maps frozen id `i` to the words of header entry `i` (`bufImg B i`). `HdrView B m`: the buffer `B`
(the words from a header's start) shows the memory `m`: every frozen entry's image is the prefix of
its source in `m` with its extent in `m`, the header's own entry is `(0, hdrW)`, the header's words
`2`, `3` are `m`'s count `DECL[0]` and counter `CTL[128]`, and every entry lies inside `B`.

* `hdrView_of`: after `par_compact(1, b)` on `m`, any `B` that has the words of
  `OUT[b‥b+len)` (`len` the header's word `1`) shows `m`;
* `hdrView_flat`: the flat buffer `bufOf m` shows `m` and has word `5` (the next phase) `0`.
-/

namespace L.Arena

open L

/-- **The buffer `B` (from a header's start) shows the memory `m`.** -/
structure HdrView (B : Array Word) (m : Mem) : Prop where
  img : ∀ i (_ : i < frozen.length),
    bufImg B (i + 1) = (m.arr64 (fzAt i).src).extract 0 (fzExt m (fzAt i))
  ext : ∀ i (_ : i < frozen.length), fzExt m (fzAt i) ≤ (m.arr64 (fzAt i).src).size
  hdr0 : bufEntry B 0 = (0, hdrW)
  cnt : (bufImg B 0).getD 2 0 = rd64 m L.Front.DECL 0 ∧ (bufImg B 0).getD 3 0 = rd64 m CTL 128
  inside : ∀ i < frozenIdsL.length, (bufEntry B i).1 + (bufEntry B i).2 ≤ B.size

section
variable {m : Mem} {b : Word}

theorem getD_of_agree {B A : Array Word} {o L : Nat} (hB : ∀ k < L, B.getD k 0 = A.getD (o + k) 0) {k : Nat}
    (hk : k < L) : B.getD k 0 = A.getD (o + k) 0 := hB k hk

/-- **The entries of a buffer with the words of `OUT[b‥b+len)` after `par_compact(1, b)`**: the
header's own, then each frozen image at `hdrW` plus the extents before it, apart in order. -/
theorem hdrEnt_of (B : Array Word) (hok : parCompactOK m 1 b = true) (hb : b.toNat + hdrW < 2 ^ 64)
    (hlt : (m.arr64 OUT).size < 2 ^ 64)
    (hB : ∀ k < (fzOff m frozen.length).toNat,
      B.getD k 0 = ((parCompactMem m 1 b).arr64 OUT).getD (b.toNat + k) 0) :
    bufEntry B 0 = (0, hdrW) ∧
    (∀ i (_ : i < frozen.length), bufEntry B (i + 1) = ((fzOff m i).toNat, fzExt m (fzAt i))) ∧
    (∀ i < frozenIdsL.length, ∀ i' < frozenIdsL.length, i < i' →
      (bufEntry B i).1 + (bufEntry B i).2 ≤ (bufEntry B i').1) := by
  have hW := parCompactOK_hdr_b hok hb
  have hfl := frozen_length
  have hhw := hdrW_eq
  have hg : (∀ j ≤ frozen.length, (fzOff m j).toNat = hdrW + fzSum m j) ∧
      b.toNat + hdrW + fzSum m frozen.length ≤ (m.arr64 OUT).size := by
    have h' := hok
    simp only [parCompactOK, Bool.and_eq_true] at h'
    exact (pcGo_good m 1 b hW hb (fun _ => hlt) frozen.length (Nat.le_refl _) h'.1.1.1).1 one_ne_zero'
  have hlen : (fzOff m frozen.length).toNat = hdrW + fzSum m frozen.length := hg.1 _ (Nat.le_refl _)
  have hH := parCompactMem_hdr_b hok hb
  have hrd : ∀ k, k < hdrW → B.getD k 0 = ((parCompactMem m 1 b).arr64 OUT).getD (b.toNat + k) 0 :=
    fun k hk => hB k (by omega)
  have hE0 : bufEntry B 0 = (0, hdrW) := by
    simp only [bufEntry, Nat.mul_zero, Nat.add_zero, hrd 8 (by omega), hrd 9 (by omega), hH.2.2.2.2.2.2.1,
      hH.2.2.2.2.2.2.2]
    simp [hhw]
  have hEs : ∀ i (hi : i < frozen.length), bufEntry B (i + 1) = ((fzOff m i).toNat, fzExt m (fzAt i)) := by
    intro i hi
    have he := parCompactMem_entry_b hok hb (fun _ => hlt) hi
    simp only [bufEntry, show 8 + 2 * (i + 1) = 10 + 2 * i by omega, show 9 + 2 * (i + 1) = 11 + 2 * i by omega]
    rw [hrd (10 + 2 * i) (by omega), hrd (11 + 2 * i) (by omega), he.1, he.2,
      UInt64.toNat_ofNat_of_lt' (by rw [fzExt_eq]; exact UInt64.toNat_lt_size _)]
  refine ⟨hE0, hEs, fun i hi i' hi' hii => ?_⟩
  have hL := frozenIdsL_length
  obtain ⟨c, rfl⟩ : ∃ c, i' = c + 1 := ⟨i' - 1, by omega⟩
  rw [hEs c (by omega), hg.1 c (by omega)]
  rcases i with _ | a
  · rw [hE0]; simp only; omega
  · rw [hEs a (by omega), hg.1 a (by omega)]
    have := fzSum_mono m (j := a + 1) (n := c) (by omega)
    rw [fzSum_succ, ← fzExt_eq] at this
    simp only; omega

/-- **After `par_compact(1, b)`, a buffer with the words of `OUT[b‥b+len)` shows `m`.** -/
theorem hdrView_of (B : Array Word) (hok : parCompactOK m 1 b = true) (hb : b.toNat + hdrW < 2 ^ 64)
    (hlt : (m.arr64 OUT).size < 2 ^ 64)
    (hB : ∀ k < (fzOff m frozen.length).toNat,
      B.getD k 0 = ((parCompactMem m 1 b).arr64 OUT).getD (b.toNat + k) 0)
    (hsz : (fzOff m frozen.length).toNat ≤ B.size) : HdrView B m := by
  have hW := parCompactOK_hdr_b hok hb
  have hfl := frozen_length
  have hhw := hdrW_eq
  have hg : (∀ j ≤ frozen.length, (fzOff m j).toNat = hdrW + fzSum m j) ∧
      b.toNat + hdrW + fzSum m frozen.length ≤ (m.arr64 OUT).size := by
    have h' := hok
    simp only [parCompactOK, Bool.and_eq_true] at h'
    exact (pcGo_good m 1 b hW hb (fun _ => hlt) frozen.length (Nat.le_refl _) h'.1.1.1).1 one_ne_zero'
  have hlen : (fzOff m frozen.length).toNat = hdrW + fzSum m frozen.length := hg.1 _ (Nat.le_refl _)
  have hH := parCompactMem_hdr_b hok hb
  have hrd : ∀ k, k < hdrW → B.getD k 0 = ((parCompactMem m 1 b).arr64 OUT).getD (b.toNat + k) 0 :=
    fun k hk => hB k (by omega)
  have hE0 : bufEntry B 0 = (0, hdrW) := by
    simp only [bufEntry, Nat.mul_zero, Nat.add_zero, hrd 8 (by omega), hrd 9 (by omega), hH.2.2.2.2.2.2.1,
      hH.2.2.2.2.2.2.2]
    simp [hhw]
  have hEs : ∀ i (hi : i < frozen.length),
      bufEntry B (i + 1) = ((fzOff m i).toNat, fzExt m (fzAt i)) ∧ (fzOff m i).toNat = hdrW + fzSum m i := by
    intro i hi
    have he := parCompactMem_entry_b hok hb (fun _ => hlt) hi
    refine ⟨?_, hg.1 i (by omega)⟩
    simp only [bufEntry, show 8 + 2 * (i + 1) = 10 + 2 * i by omega, show 9 + 2 * (i + 1) = 11 + 2 * i by omega]
    rw [hrd (10 + 2 * i) (by omega), hrd (11 + 2 * i) (by omega), he.1, he.2,
      UInt64.toNat_ofNat_of_lt' (by rw [fzExt_eq]; exact UInt64.toNat_lt_size _)]
  have hext : ∀ i (hi : i < frozen.length), fzExt m (fzAt i) ≤ (m.arr64 (fzAt i).src).size :=
    fun i hi => fzExt_le_src hok hi
  have hin : ∀ i < frozenIdsL.length, (bufEntry B i).1 + (bufEntry B i).2 ≤ (fzOff m frozen.length).toNat := by
    intro i hi
    have h64 := frozenIdsL_length
    rcases i with _ | i
    · rw [hE0, hlen]; simp only; omega
    · obtain ⟨he, ho⟩ := hEs i (by omega)
      rw [he, hlen, ho]
      have := fzSum_mono m (j := i + 1) (n := frozen.length) (by omega)
      rw [fzSum_succ, ← fzExt_eq] at this
      simp only; omega
  refine ⟨fun i hi => ?_, hext, hE0, ?_, fun i hi => Nat.le_trans (hin i hi) hsz⟩
  · have hin' := hin (i + 1) (by have := frozenIdsL_length; omega)
    obtain ⟨he, ho⟩ := hEs i hi
    have himg := (parCompactMem_img_b hok one_ne_zero' hb hlt hi).2
    rw [he] at hin'
    simp only [bufImg, he]
    apply arr_eq_of_getD
    · simp only [Array.size_extract]; simp only at hin'; have := hext i hi; omega
    · intro k hk
      simp only [Array.size_extract] at hk
      have hk' : k < fzExt m (fzAt i) := by simp only at hin'; omega
      rw [getD_extract_lt _ _ _ _ (by simp only [Array.size_extract]; omega),
        getD_extract_lt _ _ _ _ (by simp only [Array.size_extract]; have := hext i hi; omega),
        hB _ (by simp only at hin'; omega), Nat.zero_add, ← Nat.add_assoc, himg k hk']
  · simp only [bufImg, hE0, Nat.zero_add]
    rw [getD_extract_lt _ _ _ _ (by simp only [Array.size_extract]; omega), Nat.zero_add,
      getD_extract_lt _ _ _ _ (by simp only [Array.size_extract]; omega), Nat.zero_add,
      hrd 2 (by omega), hrd 3 (by omega)]
    exact ⟨hH.2.2.1, hH.2.2.2.1⟩

/-- **The flat buffer shows `m`**, with no next phase (word `5`). -/
theorem hdrView_flat (hok : parCompactOK m 1 = true) (hlt : (m.arr64 OUT).size < 2 ^ 64) :
    HdrView (bufOf m) m ∧ (bufOf m).getD 5 0 = 0 := by
  have hs := bufOf_size hok hlt
  have hhw := hdrW_eq
  refine ⟨hdrView_of (bufOf m) hok (by simp; omega) hlt (fun k hk => ?_) (by rw [hs.1]; exact Nat.le_refl _), ?_⟩
  · rw [bufOf_getD hok hlt hk]; simp
  · rw [bufOf_getD hok hlt (by omega)]; exact parCompactMem_w5 hok

end

end L.Arena
