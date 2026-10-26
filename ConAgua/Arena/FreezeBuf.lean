import ConAgua.Arena.FreezeSpec
import ConAgua.Arena.FreezeTruncBase

/-!
# The buffer is the images (lane parmode, the threads)

docs/design/parmode.md, "Step 4". After entry 1 in mode `1` the memory is `parCompactMem m v 1`
(`Checker/CheckARun.lean`). The harness hands every thread the first `len` words of `OUT`, `len`
the header's word `1` (`fzOff m 61`): `bufOf m v`. Here, for a run of `par_compact` that stayed in
bounds (`parCompactOK m 1`) with `OUT` below `2^64` words:

* `bufOf_size`: the buffer has `len = hdrW + fzSum m 61` words, the header's word `1`
  (`bufOf_len`);
* `bufEntry_zero`, `bufEntry_succ`: header entry `0` is the header `(0, hdrW)`, entry `i + 1`
  frozen entry `i`'s `(fzOff m i, fzExt m (fzAt i))`;
* `buf_entries_inside`: **every header entry lies inside the buffer** (the threaded harness
  protects only the buffer, route A);
* `bufImg_succ`: entry `i + 1`'s words are the prefix of its source array with the extent;
  `bufImg_trunc`: for the frozen arrays but the seed, what `truncFrozen m` has; `bufImg_seed`:
  the seed `CTLF` is `CTL[0‥256)`; `bufImg_hdr`: the header's word `3` is the view `v`.
-/

namespace L.Arena

open L

/-- **The buffer a thread reads**: the first `len` words of `OUT` after entry 1 (mode `1`), `len`
the header's word `1`. -/
def bufOf (m : Mem) (v : Word) : Array Word :=
  ((parCompactMem m v 1).arr64 OUT).extract 0 (fzOff m frozen.length).toNat

/-! ## Arrays read through `getD` -/

theorem arr_eq_of_getD {a b : Array Word} (hs : a.size = b.size)
    (h : ∀ k < a.size, a.getD k 0 = b.getD k 0) : a = b := by
  refine Array.ext hs fun k h1 h2 => ?_
  have := h k h1
  simp only [Array.getD, h1, h2, dite_true] at this
  exact this

theorem getD_extract_lt (a : Array Word) (s e k : Nat) (h : k < (a.extract s e).size) :
    (a.extract s e).getD k 0 = a.getD (s + k) 0 := by
  simp only [Array.size_extract] at h
  have h' : k < min e a.size - s := h
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_extract, h', ↓reduceIte]

section buf
variable {m : Mem} {v : Word}

theorem one_ne_zero' : (1 : Word) ≠ 0 := by decide

/-- The offsets and the buffer's length, after a run in bounds. -/
theorem buf_offs (hok : parCompactOK m 1 = true) (hlt : (m.arr64 OUT).size < 2 ^ 64) :
    (∀ j ≤ frozen.length, (fzOff m j).toNat = hdrW + fzSum m j) ∧
      hdrW + fzSum m frozen.length ≤ (m.arr64 OUT).size := by
  have hW := parCompactOK_hdr hok
  simp only [parCompactOK, Bool.and_eq_true] at hok
  exact (pcGo_good m 1 hW (fun _ => hlt) frozen.length (Nat.le_refl _) hok.1.1).1 one_ne_zero'

/-- **The buffer's length** is `hdrW` plus the extents. -/
theorem bufOf_size (hok : parCompactOK m 1 = true) (hlt : (m.arr64 OUT).size < 2 ^ 64) :
    (bufOf m v).size = (fzOff m frozen.length).toNat ∧
      (fzOff m frozen.length).toNat = hdrW + fzSum m frozen.length := by
  obtain ⟨h1, h2⟩ := buf_offs hok hlt
  have e := h1 _ (Nat.le_refl _)
  have hs := (parCompactMem_out m v 1).size OUT
  refine ⟨?_, e⟩
  simp only [bufOf, Array.size_extract, hs]
  omega

/-- The buffer's length is the header's word `1`. -/
theorem bufOf_len (hok : parCompactOK m 1 = true) (hlt : (m.arr64 OUT).size < 2 ^ 64) :
    (bufOf m v).size = ((parCompactMem m v 1).arr64 OUT |>.getD 1 0).toNat := by
  rw [(parCompactMem_hdr hok).2.1, (bufOf_size hok hlt).1]

theorem bufOf_getD (hok : parCompactOK m 1 = true) (hlt : (m.arr64 OUT).size < 2 ^ 64) {k : Nat}
    (hk : k < (fzOff m frozen.length).toNat) :
    (bufOf m v).getD k 0 = ((parCompactMem m v 1).arr64 OUT).getD k 0 := by
  have := getD_extract_lt ((parCompactMem m v 1).arr64 OUT) 0 (fzOff m frozen.length).toNat k
    (by rw [← bufOf]; rw [(bufOf_size hok hlt).1]; exact hk)
  rw [Nat.zero_add] at this
  exact this

theorem hdrW_le_len (hok : parCompactOK m 1 = true) (hlt : (m.arr64 OUT).size < 2 ^ 64) :
    hdrW ≤ (fzOff m frozen.length).toNat := by
  rw [(bufOf_size (v := 0) hok hlt).2]; omega

/-- **The header's word `3` is the view.** -/
theorem bufOf_view (hok : parCompactOK m 1 = true) (hlt : (m.arr64 OUT).size < 2 ^ 64) :
    (bufOf m v).getD 3 0 = v := by
  have := hdrW_le_len hok hlt
  have h132 : hdrW = 132 := by decide
  rw [bufOf_getD hok hlt (by omega), (parCompactMem_hdr hok).2.2.2.1]

/-- **Header entry `0` is the header itself.** -/
theorem bufEntry_zero (hok : parCompactOK m 1 = true) (hlt : (m.arr64 OUT).size < 2 ^ 64) :
    bufEntry (bufOf m v) 0 = (0, hdrW) := by
  have := hdrW_le_len hok hlt
  have h132 : hdrW = 132 := by decide
  have h8 := (parCompactMem_hdr (vis := v) hok).2.2.2.2.2.1
  have h9 := (parCompactMem_hdr (vis := v) hok).2.2.2.2.2.2
  simp only [bufEntry, Nat.mul_zero, Nat.add_zero]
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  rw [← Array.getD_eq_getD_getElem?, ← Array.getD_eq_getD_getElem?,
    bufOf_getD hok hlt (by omega), bufOf_getD hok hlt (by omega), h8, h9]
  simp [h132]

/-- **Header entry `i + 1` is frozen entry `i`'s offset and extent** (the offset `hdrW` plus the
extents before it). -/
theorem bufEntry_succ (hok : parCompactOK m 1 = true) (hlt : (m.arr64 OUT).size < 2 ^ 64) {i : Nat}
    (hi : i < frozen.length) :
    bufEntry (bufOf m v) (i + 1) = ((fzOff m i).toNat, fzExt m (fzAt i)) ∧
      (fzOff m i).toNat = hdrW + fzSum m i := by
  have := hdrW_le_len hok hlt
  have h132 : hdrW = 132 := by decide
  have h61 : frozen.length = 61 := frozen_length
  have he := parCompactMem_entry (vis := v) hok (fun _ => hlt) hi
  refine ⟨?_, (buf_offs hok hlt).1 i (by omega)⟩
  simp only [bufEntry]
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  rw [← Array.getD_eq_getD_getElem?, ← Array.getD_eq_getD_getElem?,
    bufOf_getD hok hlt (by omega), bufOf_getD hok hlt (by omega),
    show 8 + 2 * (i + 1) = 10 + 2 * i by omega, show 9 + 2 * (i + 1) = 11 + 2 * i by omega,
    he.1, he.2, UInt64.toNat_ofNat_of_lt' (by rw [fzExt_eq]; exact UInt64.toNat_lt_size _)]

/-- The extent of frozen entry `i` fits its source array. -/
theorem fzExt_le_src (hok : parCompactOK m 1 = true) {i : Nat} (hi : i < frozen.length) :
    fzExt m (fzAt i) ≤ (m.arr64 (fzAt i).src).size := by
  simp only [parCompactOK, Bool.and_eq_true] at hok
  have h1 := hok.1.1
  obtain ⟨k, hk⟩ : ∃ k, frozen.length = i + 1 + k := ⟨frozen.length - (i + 1), by omega⟩
  rw [hk, List.range_add, pcOK_append, Bool.and_eq_true, pcOK_range_succ, Bool.and_eq_true] at h1
  have h2 := h1.1.2
  have hF := OutFrame.pcGo 1 (List.range i) m (UInt64.ofNat hdrW)
  have hz := fzAt_ok hi
  have he := fzEv_congr hF.arr _ hz.1
  simp only [fzOK, he.1, hF.size, hF.arr _ hz.2, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h2
  rcases h2.1.1.2 with h | h
  · exact absurd h one_ne_zero'
  · rw [fzExt_eq]; exact h.2

/-- **Every header entry lies inside the buffer.** -/
theorem buf_entries_inside (hok : parCompactOK m 1 = true) (hlt : (m.arr64 OUT).size < 2 ^ 64)
    {i : Nat} (hi : i < frozenIdsL.length) :
    (bufEntry (bufOf m v) i).1 + (bufEntry (bufOf m v) i).2 ≤ (bufOf m v).size := by
  have hs := bufOf_size (v := v) hok hlt
  have h61 : frozen.length = 61 := frozen_length
  have h62 : frozenIdsL.length = 62 := rfl
  rcases i with _ | i
  · rw [bufEntry_zero hok hlt, hs.1]; have := hdrW_le_len hok hlt; simpa using this
  · obtain ⟨he, ho⟩ := bufEntry_succ (v := v) hok hlt (i := i) (by omega)
    rw [he, hs.1, hs.2, ho]
    have := fzSum_mono m (j := i + 1) (n := frozen.length) (by omega)
    rw [fzSum_succ, ← fzExt_eq] at this
    simp only; omega

/-- **Entry `i + 1`'s words are the prefix of its source with the extent.** -/
theorem bufImg_succ (hok : parCompactOK m 1 = true) (hlt : (m.arr64 OUT).size < 2 ^ 64) {i : Nat}
    (hi : i < frozen.length) :
    bufImg (bufOf m v) (i + 1) = (m.arr64 (fzAt i).src).extract 0 (fzExt m (fzAt i)) := by
  have hin := buf_entries_inside (v := v) hok hlt (i := i + 1) (by
    have : frozenIdsL.length = 62 := rfl
    have : frozen.length = 61 := frozen_length
    omega)
  obtain ⟨he, ho⟩ := bufEntry_succ (v := v) hok hlt hi
  have hsrc := fzExt_le_src hok hi
  have hs := bufOf_size (v := v) hok hlt
  have himg := (parCompactMem_img (vis := v) hok one_ne_zero' hlt hi).2
  rw [he] at hin
  simp only [bufImg, he]
  apply arr_eq_of_getD
  · simp only [Array.size_extract]; simp only at hin; omega
  · intro k hk
    simp only [Array.size_extract] at hk
    have hk' : k < fzExt m (fzAt i) := by simp only at hin; omega
    rw [getD_extract_lt _ _ _ _ (by simp only [Array.size_extract]; omega),
      getD_extract_lt _ _ _ _ (by simp only [Array.size_extract]; omega),
      bufOf_getD hok hlt (by simp only at hin; rw [← hs.1]; omega), Nat.zero_add, himg k hk']

/-- The frozen list's ids are the buffer ids after the header. -/
theorem frozenIdsL_eq : frozenIdsL = HDRF :: frozen.map (·.1) := by decide +kernel

/-- Every frozen entry but the seed is its own source. -/
theorem frozen_src_self : (frozen.drop 1).all (fun e => e.2.src == e.1) = true := by decide +kernel

theorem fzAt_mem {i : Nat} (hi : i < frozen.length) : (frozen[i].1, fzAt i) ∈ frozen := by
  simp only [fzAt, List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]
  exact List.getElem_mem hi

theorem frozenIdsL_get {i : Nat} (hi : i < frozen.length) :
    frozenIdsL[i + 1]'(by rw [frozenIdsL_eq]; simp; omega) = frozen[i].1 := by
  simp only [frozenIdsL_eq, List.getElem_cons_succ, List.getElem_map]

/-- **Entry `i + 1` (`1 ≤ i`, the frozen arrays but the seed) is what `truncFrozen m` has.** -/
theorem bufImg_trunc (hok : parCompactOK m 1 = true) (hlt : (m.arr64 OUT).size < 2 ^ 64) {i : Nat}
    (hi : i < frozen.length) (h1 : 1 ≤ i) :
    bufImg (bufOf m v) (i + 1) = (truncFrozen m).arr64 (frozen[i].1) := by
  have hmem : (frozen[i].1, fzAt i) ∈ frozen.drop 1 := by
    have e : frozen[i] = (frozen.drop 1)[i - 1]'(by simp; omega) := by
      simp only [List.getElem_drop]; congr 1; omega
    have hz : fzAt i = frozen[i].2 := by
      simp only [fzAt, List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]
    rw [hz, e]; exact List.getElem_mem _
  have hsrc : (fzAt i).src = frozen[i].1 := by
    have := List.all_eq_true.mp frozen_src_self _ hmem
    simpa using this
  rw [bufImg_succ hok hlt hi, ← hsrc, truncFrozen_mem m hmem]

/-- **The seed `CTLF` (entry `1`) is `CTL[0‥256)`**, of 256 words. -/
theorem bufImg_seed (hok : parCompactOK m 1 = true) (hlt : (m.arr64 OUT).size < 2 ^ 64) :
    bufImg (bufOf m v) 1 = (m.arr64 CTL).extract 0 256 ∧ 256 ≤ (m.arr64 CTL).size := by
  have h0 : (0 : Nat) < frozen.length := by rw [frozen_length]; decide
  have hz : fzAt 0 = ⟨CTL, fzC 256⟩ := rfl
  have hx : fzExt m (fzAt 0) = 256 := by rw [hz]; rfl
  have := bufImg_succ (v := v) hok hlt h0
  have hs := fzExt_le_src hok h0
  rw [hx, hz] at hs
  rw [hx, hz] at this
  exact ⟨this, hs⟩

/-- The header's entry `0` holds the view at word `3`. -/
theorem bufImg_hdr (hok : parCompactOK m 1 = true) (hlt : (m.arr64 OUT).size < 2 ^ 64) :
    (bufImg (bufOf m v) 0).getD 3 0 = v := by
  have := hdrW_le_len hok hlt
  have h132 : hdrW = 132 := by decide
  have hs := bufOf_size (v := v) hok hlt
  simp only [bufImg, bufEntry_zero hok hlt, Nat.zero_add]
  rw [getD_extract_lt _ _ _ _ (by simp only [Array.size_extract]; omega), Nat.zero_add,
    bufOf_view hok hlt]

end buf

/-! ## The thread's memory `bufMem` -/

theorem bufMem_arr (B : Array Word) (r : Mem) (j : Word) (b : ArrId) :
    (bufMem B r j).arr64 b = if b < r.words.size then
      (match frozenIdsL.idxOf? b with
       | some i => bufImg B i
       | none => if parOwnedL.contains b then r.arr64 b else #[]) else #[] := by
  by_cases h : b < r.words.size
  · simp only [bufMem, Mem.arr64, Array.getD_eq_getD_getElem?, Array.getElem?_map,
      Array.getElem?_range, h, ↓reduceIte, Option.map_some, Option.getD_some]
    rfl
  · simp only [h, ↓reduceIte]
    simp only [bufMem, Mem.arr64, Array.getD_eq_getD_getElem?, Array.getElem?_map,
      Array.getElem?_range, h, ↓reduceIte, Option.map_none, Option.getD_none]

theorem bufMem_glob_init (B : Array Word) (r : Mem) (j : Word) :
    (bufMem B r j).glob INIT = r.glob INIT := rfl
theorem bufMem_glob_mode (B : Array Word) (r : Mem) (j : Word) : (bufMem B r j).glob MODE = 2 := rfl
theorem bufMem_glob_plo (B : Array Word) (r : Mem) (j : Word) : (bufMem B r j).glob PLO = j := rfl
theorem bufMem_glob_phi (B : Array Word) (r : Mem) (j : Word) :
    (bufMem B r j).glob PHI = j + 1 := rfl

/-- The frozen entries but the header and the seed: their position in `frozenIdsL`, not `CTL`,
not zeroed by `freshMem`, below `320`. -/
theorem frozen_facts_all : (List.range 61).all (fun k => k == 0 ||
    (frozenIdsL.idxOf? (frozen.map (·.1))[k]! == some (k + 1) &&
      !(freshZ.contains (frozen.map (·.1))[k]!) &&
      (frozen.map (·.1))[k]! != CTL && decide ((frozen.map (·.1))[k]! < 388))) = true := by
  decide +kernel

theorem frozen_facts {k : Nat} (hk : k < frozen.length) (h1 : 1 ≤ k) :
    frozenIdsL.idxOf? frozen[k].1 = some (k + 1) ∧ frozen[k].1 ∉ freshZ ∧ frozen[k].1 ≠ CTL ∧
      frozen[k].1 < 388 := by
  have := List.all_eq_true.mp frozen_facts_all k (List.mem_range.mpr (by rwa [frozen_length] at hk))
  rw [getElem!_pos (frozen.map (·.1)) k (by simpa using hk), List.getElem_map] at this
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq,
    decide_eq_true_eq] at this
  rcases this with h | ⟨⟨⟨h2, h3⟩, h4⟩, h5⟩
  · omega
  · refine ⟨h2, fun h => ?_, h4, h5⟩
    simp [h] at h3

/-- The owned arrays: not frozen, not truncated. -/
theorem owned_facts_all : parOwnedL.all (fun b => frozenIdsL.idxOf? b == none &&
    !(fzSrcs.contains b)) = true := by decide +kernel

theorem owned_facts {b : ArrId} (hb : b ∈ parOwnedL) :
    frozenIdsL.idxOf? b = none ∧ b ∉ fzSrcs := by
  have := List.all_eq_true.mp owned_facts_all b hb
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at this
  refine ⟨this.1, fun h => ?_⟩
  simp [h] at this

/-- **A frozen array (not the header or the seed) of the thread's memory** is the buffer's image. -/
theorem bufMem_frozen (B : Array Word) (r : Mem) (j : Word) {k : Nat} (hk : k < frozen.length)
    (h1 : 1 ≤ k) : (bufMem B r j).arr64 frozen[k].1 =
      if frozen[k].1 < r.words.size then bufImg B (k + 1) else #[] := by
  rw [bufMem_arr, (frozen_facts hk h1).1]

/-- **An owned array of the thread's memory** is the region's. -/
theorem bufMem_owned (B : Array Word) (r : Mem) (j : Word) {b : ArrId} (hb : b ∈ parOwnedL) :
    (bufMem B r j).arr64 b = r.arr64 b := by
  rw [bufMem_arr, (owned_facts hb).1]
  simp only [List.contains_iff_mem, hb, ↓reduceIte]
  split
  · rfl
  · rename_i h; rw [Mem.arr64_oob _ _ h]

theorem bufMem_hdr (B : Array Word) (r : Mem) (j : Word) :
    (bufMem B r j).arr64 HDRF = if HDRF < r.words.size then bufImg B 0 else #[] := by
  rw [bufMem_arr]; rfl

theorem bufMem_ctlf (B : Array Word) (r : Mem) (j : Word) :
    (bufMem B r j).arr64 CTLF = if CTLF < r.words.size then bufImg B 1 else #[] := by
  rw [bufMem_arr]; rfl

theorem bufMem_ctl (B : Array Word) (r : Mem) (j : Word) :
    (bufMem B r j).arr64 CTL = r.arr64 CTL :=
  bufMem_owned B r j (by decide)

theorem bufMem_words (B : Array Word) (r : Mem) (j : Word) :
    (bufMem B r j).words.size = r.words.size := by simp [bufMem]

/-- `freshCtl` word by word. -/
theorem getD_freshCtl (c : Array Word) (k : Nat) :
    (freshCtl c).getD k 0 = if k < 256 then c.getD k 0 else 0 := by
  simp only [freshCtl, zeros, Array.getD_eq_getD_getElem?, Array.getElem?_append, size_extract0]
  split
  · rename_i h
    rw [if_pos (by omega), get?_extract c (by omega : k < 256)]
  · rename_i h
    rw [Array.getElem?_replicate]
    split
    · split
      · rename_i h1 h2; omega
      · rfl
    · split
      · rename_i h1 h2
        have : c.size ≤ k := by omega
        simp [Array.getElem?_eq_none this]
      · rfl

end L.Arena
