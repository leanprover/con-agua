module

public import ConAgua.Checker.C1Hdr
public import ConAgua.Checker.CmpSeqView
import ConAgua.Arena.FreezeFreshBase
import ConAgua.Arena.FreezeTruncBase

@[expose] public section

/-!
# A thread's switch from header S to header C (lane compare2, H7)

A thread runs its solution calls on `bufMem B r j` (header S, showing `mS`) and then its challenge
calls on `bufMem BC r j` (header C, showing `m9`), on the same region `r`. With both headers of the
same extents (`hext`) and `mS` a frame of `m9` off the stream index's arrays and words (`csA`,
`csC`), the memory after `check_b`'s first block and re-read under header C is the one under
header S with `csA` and the words `csC` of `CTL` replaced by `freshMem m9`'s (`c1Patch`):
`c1_switch`.
-/

namespace L.Checker

open L L.Arena

/-- `c` with the seed words `rrWs` replaced by `d`'s. -/
def c1CtlP (c d : Array Word) : Array Word := c.mapIdx fun i v => if i ∈ rrWs then d.getD i 0 else v

/-- **`X` with the stream index's arrays `csA` and `CTL`'s words `csC` replaced by `C`'s.** -/
def c1Patch (C X : Mem) : Mem :=
  { X with words := fun s => if s ∈ csA then C.arr64 s else if s = CTL then c1CtlP (X.arr64 CTL) (C.arr64 CTL)
      else X.arr64 s }

theorem rrWs_iff (k : Nat) : k ∈ rrWs ↔ k = 128 ∨ (162 ≤ k ∧ k < 174) ∨ k = 224 := by
  simp [rrWs]

theorem csC_iff (x : Word) : x ∈ csC ↔ x.toNat ∈ rrWs := by
  rw [rrWs_iff]
  constructor
  · intro h; have := csC_val h; omega
  · intro h
    have e : x = UInt64.ofNat x.toNat := (UInt64.ofNat_toNat).symm
    rcases h with h | ⟨h1, h2⟩ | h
    · rw [e, h]; decide
    · rw [e]
      have : x.toNat = 162 ∨ x.toNat = 163 ∨ x.toNat = 164 ∨ x.toNat = 165 ∨ x.toNat = 166 ∨ x.toNat = 167 ∨
          x.toNat = 168 ∨ x.toNat = 169 ∨ x.toNat = 170 ∨ x.toNat = 171 ∨ x.toNat = 172 ∨ x.toNat = 173 := by omega
      rcases this with h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> decide
    · rw [e, h]; decide

theorem getD_c1CtlP (c d : Array Word) (k : Nat) :
    (c1CtlP c d).getD k 0 = if k < c.size then (if k ∈ rrWs then d.getD k 0 else c.getD k 0) else 0 := by
  simp only [c1CtlP, Array.getD_eq_getD_getElem?, Array.getElem?_mapIdx]
  by_cases h : k < c.size
  · simp [h]
  · simp [h]

theorem size_c1CtlP (c d : Array Word) : (c1CtlP c d).size = c.size := by simp [c1CtlP]

theorem c1Patch_arr (C X : Mem) (s : TieredArray) : (c1Patch C X).arr64 s =
    if s ∈ csA then C.arr64 s else if s = CTL then c1CtlP (X.arr64 CTL) (C.arr64 CTL) else X.arr64 s := rfl

/-- The re-read keeps `CTL`'s words but the seed's. -/
theorem rereadMem_off (x : Mem) {k : Nat} (hk : k ∉ rrWs) :
    ((rereadMem x).arr64 CTL).getD k 0 = (x.arr64 CTL).getD k 0 := by
  rw [rrWs_iff] at hk
  unfold rereadMem
  split
  · rfl
  rw [getD_set64_same, getD_copy64 (by decide) 12 _ 162 162 (by simp) (by simp), getD_set64_same]
  simp only [L.Mem.size64_set64, show UInt64.toNat 224 = 224 from rfl, show UInt64.toNat 162 = 162 from rfl,
    show UInt64.toNat 128 = 128 from rfl]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

/-- **`CTL` after `check_b`'s first block and re-read**, word by word: the seed's at its words
`rrWs`, and below `256` on a first call; the region's elsewhere. -/
theorem seedCtl_getD (B : Array Word) (r : Mem) (j : Word) (hs : (bufImg B 1).size = 256)
    (hsz : 256 ≤ (r.arr64 CTL).size) (k : Nat) :
    ((seedMem (bufMem B r j)).arr64 CTL).getD k 0 =
      if k ∈ rrWs ∨ (r.glob INIT = 0 ∧ k < 256) then (bufImg B 1).getD k 0 else (r.arr64 CTL).getD k 0 := by
  unfold seedMem
  generalize hx : (if (bufMem B r j).glob INIT = 0 then ((bufMem B r j).copy64 CTL 0 CTLF 0
    ((bufMem B r j).len64 CTLF).toNat).setG INIT 1 else bufMem B r j) = x
  have hn : ((bufMem B r j).len64 CTLF).toNat = 256 := by
    simp only [Mem.len64, bufMem_ctlf, hs]; rfl
  have hxf : x.arr64 CTLF = bufImg B 1 := by
    rw [← hx]; split
    · rw [L.Mem.setG_arr64, arr64_copy64_ne _ _ _ _ _ _ (by decide), bufMem_ctlf]
    · rw [bufMem_ctlf]
  have hxs : (x.arr64 CTL).size = (r.arr64 CTL).size := by
    rw [← hx]; split
    · rw [L.Mem.setG_arr64, size_copy64, bufMem_ctl]
    · rw [bufMem_ctl]
  by_cases hk : k ∈ rrWs
  · rw [ite_eq_left (.inl hk), rereadMem_rr x (by simp only [Mem.len64, hxf, hs]; decide) (by omega) k hk, hxf]
  rw [rereadMem_off x hk]
  have hI : (bufMem B r j).glob INIT = r.glob INIT := bufMem_glob_init B r j
  by_cases h0 : r.glob INIT = 0
  · rw [← hx, ite_eq_left (by rw [hI]; exact h0), L.Mem.setG_arr64, hn,
      getD_copy64 (by decide) 256 _ 0 0 (by simp) (by simp) k, bufMem_ctl, bufMem_ctlf]
    simp only [UInt64.toNat_zero, Nat.zero_le, true_and, Nat.zero_add, Nat.sub_zero, hk, false_or, h0]
    by_cases h1 : k < 256
    · by_cases h2 : k < (r.arr64 CTL).size
      · simp [h1, h2]
      · omega
    · simp [h1]
  · rw [← hx, ite_eq_right (by rw [hI]; exact h0), bufMem_ctl]
    simp [hk, h0]

theorem seedMem_arr_ne (w : Mem) {t : TieredArray} (ht : t ≠ CTL) : (seedMem w).arr64 t = w.arr64 t := by
  unfold seedMem
  rw [rereadMem_ne _ ht]
  split
  · rw [L.Mem.setG_arr64, arr64_copy64_ne _ _ _ _ _ _ ht]
  · rfl

theorem seedMem_ctl_size (w : Mem) : ((seedMem w).arr64 CTL).size = (w.arr64 CTL).size := by
  unfold seedMem
  rw [rereadMem_size]
  split
  · rw [L.Mem.setG_arr64, size_copy64]
  · rfl

theorem c1_fzAt_src {i : Nat} (hi : i < frozen.length) (h1 : 1 ≤ i) : (fzAt i).src = frozen[i].1 := by
  have hmem : (frozen[i].1, fzAt i) ∈ frozen.drop 1 := by
    have e : frozen[i] = (frozen.drop 1)[i - 1]'(by simp; omega) := by
      simp only [List.getElem_drop]; congr 1; omega
    have hz : fzAt i = frozen[i].2 := by
      simp only [fzAt, List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]
    rw [hz, e]; exact List.getElem_mem _
  have := List.all_eq_true.mp frozen_src_self _ hmem
  simpa using this

theorem csA_not_owned : ∀ b ∈ csA, b ∉ parOwnedL := by decide

theorem getD_of_rdW {a b : Array Word} {k : Nat} (hk : k < 2 ^ 64)
    (h : rdW a (UInt64.ofNat k) = rdW b (UInt64.ofNat k)) : a.getD k 0 = b.getD k 0 := by
  have e : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
  simp only [rdW, e] at h
  simpa only [Array.getD_eq_getD_getElem?] using h

/-- **The switch from header S to header C on one region.** -/
theorem c1_switch {B BC : Array Word} {mS m9 : Mem} (hB : HdrView B mS) (hC : HdrView BC m9)
    (hfr : MemFrame csA csC m9 mS) (hext : ∀ i < frozen.length, fzExt mS (fzAt i) = fzExt m9 (fzAt i))
    (r : Mem) (j : Word) (hsz : 256 ≤ (r.arr64 CTL).size) :
    ∀ t, thrS t = true →
      (seedMem (bufMem BC r j)).arr64 t = (c1Patch (freshMem m9) (seedMem (bufMem B r j))).arr64 t := by
  intro t ht
  rw [c1Patch_arr]
  by_cases hA : t ∈ csA
  · rw [ite_eq_left hA]
    rcases thrS_cases ht with ⟨k, hk, h1, rfl⟩ | ho
    · obtain ⟨-, hz, hc⟩ := frozen_facts hk h1
      rw [seedMem_arr_ne _ (TieredArray.t0_ne hc), bufMem_frozen _ r j hk h1, c1_hdr_trunc hC hk h1, freshMem_arr,
        ite_eq_right (TieredArray.t0_ne hc), ite_eq_right hz]
    · exact absurd ho (csA_not_owned t hA)
  rw [ite_eq_right hA]
  by_cases hc : t = CTL
  · subst hc
    rw [ite_eq_left rfl]
    obtain ⟨hsB, h256B⟩ := c1_hdr_seed hB
    obtain ⟨hsC, h256C⟩ := c1_hdr_seed hC
    have hB1 : (bufImg B 1).size = 256 := by rw [hsB, size_extract0]; omega
    have hC1 : (bufImg BC 1).size = 256 := by rw [hsC, size_extract0]; omega
    apply arr_eq_of_getD
    · rw [size_c1CtlP, seedMem_ctl_size, seedMem_ctl_size, bufMem_ctl, bufMem_ctl]
    intro k hk
    rw [seedMem_ctl_size, bufMem_ctl] at hk
    rw [getD_c1CtlP, seedMem_ctl_size, bufMem_ctl, ite_eq_left hk, seedCtl_getD BC r j hC1 hsz,
      seedCtl_getD B r j hB1 hsz]
    have hrr : ∀ k ∈ rrWs, k < 256 := by decide
    by_cases hkr : k ∈ rrWs
    · rw [ite_eq_left (.inl hkr), ite_eq_left hkr, freshMem_arr, ite_eq_left rfl, truncFrozen_ctl, getD_freshCtl,
        ite_eq_left (hrr k hkr), hsC, getD_extract_lt _ _ _ _ (by rw [size_extract0]; have := hrr k hkr; omega),
        Nat.zero_add]
    · rw [ite_eq_right hkr]
      simp only [hkr, false_or]
      split
      · rename_i h
        rw [hsB, hsC, getD_extract_lt _ _ _ _ (by rw [size_extract0]; omega),
          getD_extract_lt _ _ _ _ (by rw [size_extract0]; omega), Nat.zero_add]
        exact getD_of_rdW (by omega) (hfr.ctl _ (fun hm => hkr (by
          have := (csC_iff _).mp hm
          rwa [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)] at this))).symm
      · rfl
  rw [ite_eq_right hc, seedMem_arr_ne _ hc, seedMem_arr_ne _ hc]
  rcases thrS_cases ht with ⟨k, hk, h1, rfl⟩ | ho
  · rw [bufMem_frozen _ r j hk h1, bufMem_frozen _ r j hk h1, hB.img k hk, hC.img k hk, hext k hk,
      c1_fzAt_src hk h1, hfr.arr _ hA hc]
  · rw [bufMem_owned _ r j ho, bufMem_owned _ r j ho]

end L.Checker
