import ConAgua.Checker.HoistOrderRef3
import ConAgua.Arena.DeclNatBase

/-!
# The hoist's reorder refines `applyHoist`'s sort (lane `front4`)

`hoist_apply` (buckets per target, then for each position `p` the records moved to `p` in
position order and `p` itself unless it moved) against `applyHoist`'s
`(List.range ds.size).mergeSort (fun a b => !hoistLt target b a)`: the keys `hoistKey` are pairwise
distinct, so the sorted order is the unique sorted permutation, and L's order is sorted and a
permutation. `hoist_any` is `target.isEmpty`. `reorder` is the map of the order through `ds`.
-/

open ConRon.Arena ConRon.Arena.Frontend
open L.Arena L.Ind L.Front L.Front.Ind

namespace L.Checker

/-- The sorted order of `applyHoist`. -/
def hoistOrder (T : Std.HashMap Nat Nat) (c : Nat) : List Nat :=
  (List.range c).mergeSort (fun a b => !hoistLt T b a)

/-- **`hoist_any` is "the map has an entry"** (from position `k` on). -/
theorem hoistAny_ok (n : Nat) (m m' : Mem) (tg c k r : Word) (T : Std.HashMap Nat Nat)
    (hT : TgtR m tg c.toNat T) (_hc : tg.toNat + c.toNat < 2 ^ 64)
    (hlt : ∀ (k t : Nat), T[k]? = some t → t < k)
    (h : hAnyW n m tg c k = some (r, m')) :
    m' = m ∧ (r = 0 ↔ ∀ j, k.toNat ≤ j → j < c.toNat → T[j]? = none) :=
  hAny_ok n m tg c T hT hlt k r m' h

/-- No entry below `c` and none at or beyond it: the map is empty. -/
theorem tgt_isEmpty (T : Std.HashMap Nat Nat) (c : Nat) (hc : ∀ k, c ≤ k → T[k]? = none)
    (h : ∀ j, 0 ≤ j → j < c → T[j]? = none) : T.isEmpty = true := by
  rw [Std.HashMap.isEmpty_iff_forall_not_mem]
  intro a ha
  rw [Std.HashMap.mem_iff_isSome_getElem?] at ha
  have : T[a]? = none := if hac : a < c then h a (Nat.zero_le _) hac else hc a (by omega)
  rw [this] at ha
  cases ha

theorem iwok_alloc {m m1 : Mem} {k q : Word} (h : allocW m k = some (q, m1)) (hI : IWOK m) :
    IWOK m1 := by
  obtain ⟨_, rfl, _, hroom, htop⟩ := allocW_post h hI
  have hf := allocMem_frame m k
  obtain ⟨_, h2, h3, h4, h5⟩ := hI
  have hE : (allocMem m k).arr64 EREC = m.arr64 EREC := hf.1 EREC (by decide) (by decide)
  have h129 : erTop (allocMem m k) = erTop m := by
    simp only [erTop]; rw [hf.2.1 129 (by decide)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [htop, allocMem_IW]; exact hroom
  · rw [h129, hE]; exact h2
  · rw [allocMem_IW]; exact h3
  · rw [hE]; exact h4
  · rw [hf.2.2.1 CTL]; exact h5

theorem iwok_frame {m m' : Mem} (hf : MemFrame [IW] [] m m') (hI : IWOK m) : IWOK m' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hI
  have ht : iwTop m' = iwTop m := by simp only [iwTop]; rw [hf.2.1 200 (by simp)]
  have he : erTop m' = erTop m := by simp only [erTop]; rw [hf.2.1 129 (by simp)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [ht, hf.2.2.1]; exact h1
  · rw [he, hf.2.2.1]; exact h2
  · rw [hf.2.2.1]; exact h3
  · rw [hf.2.2.1]; exact h4
  · rw [hf.2.2.1]; exact h5

theorem getElem?_of_rd {m m' : Mem} (i : Nat) (hs : (m'.arr64 IW).size = (m.arr64 IW).size)
    (hi : i < (m.arr64 IW).size) (hl : (m.arr64 IW).size < 2 ^ 64) (h : rd m' i = rd m i) :
    (m'.arr64 IW)[i]? = (m.arr64 IW)[i]? := by
  simp only [rd, rdW, UInt64.toNat_ofNat_of_lt' (show i < UInt64.size by
    simp [UInt64.size]; omega)] at h
  rw [Array.getElem?_eq_getElem (by omega), Array.getElem?_eq_getElem hi] at h ⊢
  simpa using h

/-- **`hoist_apply` writes `hoistOrder`** (through `ord`) to a fresh slice `out` of `c` words, every
moved record's target being before it. -/
theorem hoistApply_ok (n : Nat) (m m' : Mem) (ord c tg out : Word) (T : Std.HashMap Nat Nat)
    (hI : IWOK m) (hord : ord.toNat + c.toNat ≤ iwTop m) (htg : tg.toNat + c.toNat ≤ iwTop m)
    (hT : TgtR m tg c.toNat T) (hlt : ∀ (k t : Nat), T[k]? = some t → t < k)
    (h : hApplyW n m ord c tg = some (out, m')) :
    IWOK m' ∧ IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧ iwTop m ≤ out.toNat ∧
      out.toNat + c.toNat ≤ iwTop m' ∧
      ∀ j (hj : j < c.toNat), rdW (m'.arr64 IW) (out + UInt64.ofNat j) =
        rdW (m.arr64 IW) (ord + UInt64.ofNat ((hoistOrder T c.toNat)[j]'(by
          simp [hoistOrder, List.length_mergeSort]; exact hj))) := by
  cases n with
  | zero => simp [hApplyW.eq_1] at h
  | succ n =>
  have hsz := hI.2.2.1
  rw [hApplyW.arm1] at h
  rcases ha1 : allocW m c with _ | ⟨hd, m1⟩ <;> rw [ha1] at h
  · rw [hApplyW.k_iw_alloc.eq_1] at h; cases h
  rw [hApplyW.k_iw_alloc.arm1] at h
  obtain ⟨hq1, rfl, _, hr1, ht1⟩ := allocW_post ha1 hI
  have hI1 := iwok_alloc ha1 hI
  rcases ha2 : allocW (allocMem m c) c with _ | ⟨tl, m2⟩ <;> rw [ha2] at h
  · rw [hApplyW.k_iw_alloc_2.eq_1] at h; cases h
  rw [hApplyW.k_iw_alloc_2.arm1] at h
  obtain ⟨hq2, rfl, _, hr2, ht2⟩ := allocW_post ha2 hI1
  have hI2 := iwok_alloc ha2 hI1
  rcases ha3 : allocW (allocMem (allocMem m c) c) c with _ | ⟨nx, m3⟩ <;> rw [ha3] at h
  · rw [hApplyW.k_iw_alloc_3.eq_1] at h; cases h
  rw [hApplyW.k_iw_alloc_3.arm1] at h
  obtain ⟨hq3, rfl, _, hr3, ht3⟩ := allocW_post ha3 hI2
  have hI3 := iwok_alloc ha3 hI2
  rcases ha4 : allocW (allocMem (allocMem (allocMem m c) c) c) c with _ | ⟨out', m4⟩ <;> rw [ha4] at h
  · rw [hApplyW.k_iw_alloc_4.eq_1] at h; cases h
  rw [hApplyW.k_iw_alloc_4.arm1] at h
  obtain ⟨hq4, rfl, _, hr4, ht4⟩ := allocW_post ha4 hI3
  have hI4 := iwok_alloc ha4 hI3
  -- the four slices
  obtain ⟨m4, hm4⟩ : ∃ m4, m4 = allocMem (allocMem (allocMem (allocMem m c) c) c) c := ⟨_, rfl⟩
  rw [← hm4] at h hI4 ht4
  have hIW4 : m4.arr64 IW = m.arr64 IW := by simp only [hm4, allocMem_IW]
  have hIW3 : (allocMem (allocMem (allocMem m c) c) c).arr64 IW = m.arr64 IW := by
    simp only [allocMem_IW]
  have hIW2 : (allocMem (allocMem m c) c).arr64 IW = m.arr64 IW := by simp only [allocMem_IW]
  have hhd : hd.toNat = iwTop m := by rw [hq1]; rfl
  have htl : tl.toNat = iwTop m + c.toNat := by rw [hq2]; exact ht1
  have hnx : nx.toNat = iwTop m + 2 * c.toNat := by
    rw [hq3]; show iwTop _ = _; rw [ht2, ht1]; omega
  have hout : out'.toNat = iwTop m + 3 * c.toNat := by
    rw [hq4]; show iwTop _ = _; rw [ht3, ht2, ht1]; omega
  have htop4 : iwTop m4 = iwTop m + 4 * c.toNat := by rw [ht4, ht3, ht2, ht1]; omega
  rw [hIW3, ht3, ht2, ht1] at hr4
  have hs : (m.arr64 IW).size < 2 ^ 64 := hsz
  -- zero `hd`, zero `nx`
  rcases hz1 : hZeroW n m4 hd c 0 with _ | ⟨z5, m5⟩ <;> rw [hz1] at h
  · rw [hApplyW.k_hoist_zero.eq_1] at h; cases h
  rw [hApplyW.k_hoist_zero.arm1] at h
  obtain ⟨hf5, hv5⟩ := hZero_ok n m4 m5 hd c 0 z5 (by rw [hIW4]; omega) (by rw [hIW4]; omega) hz1
  have hs5 : (m5.arr64 IW).size = (m.arr64 IW).size := by rw [frame_size hf5, hIW4]
  rcases hz2 : hZeroW n m5 nx c 0 with _ | ⟨z6, m6⟩ <;> rw [hz2] at h
  · rw [hApplyW.k_hoist_zero_2.eq_1] at h; cases h
  rw [hApplyW.k_hoist_zero_2.arm1] at h
  obtain ⟨hf6, hv6⟩ := hZero_ok n m5 m6 nx c 0 z6 (by rw [hs5]; omega) (by rw [hs5]; omega) hz2
  have hs6 : (m6.arr64 IW).size = (m.arr64 IW).size := by rw [frame_size hf6, hs5]
  have hrd4 : ∀ i, rd m4 i = rd m i := fun i => by simp only [rd, hIW4]
  have hlow6 : ∀ i < iwTop m, rd m6 i = rd m i := fun i hi => by
    rw [hv6 i (by omega), iteF (by simp; omega), hv5 i (by omega), iteF (by simp; omega), hrd4]
  -- buckets
  rcases hb : hBucketW n m6 tg c hd tl nx 0 with _ | ⟨z7, m7⟩ <;> rw [hb] at h
  · rw [hApplyW.k_hoist_bucket.eq_1] at h; cases h
  rw [hApplyW.k_hoist_bucket.arm1] at h
  have htg6 : ∀ j < c.toNat, rd m6 (tg.toNat + j) = tgW T[j]? := fun j hj => by
    rw [hlow6 _ (by omega)]; show rdW _ _ = _; rw [← addrN]; exact hT.1 j hj
  obtain ⟨hf7, hlow7, hB7⟩ := hBucket_ok T tg c hd tl nx (by omega) (by omega) (by omega) hlt n
    m6 m7 0 z7 (by rw [hs6]; omega) (by rw [hs6]; omega) (by simp) htg6
    ⟨fun t ht => by
      rw [hv6 _ (by omega), iteF (by simp; omega), hv5 _ (by omega), iteT (by simp; omega),
        UInt64.toNat_zero, posT_empty _ _ _ _ (Nat.le_refl 0)]; rfl,
     fun t _ hne => by simp [UInt64.toNat_zero, posT_empty _ _ _ _ (Nat.le_refl 0)] at hne,
     fun j hj => by
      rw [hv6 _ (by omega), iteT (by simp; omega), UInt64.toNat_zero, nxW_zero]⟩ hb
  have hs7 : (m7.arr64 IW).size = (m.arr64 IW).size := by rw [frame_size hf7, hs6]
  -- the emission
  rcases he : hEmitW n m7 ord c tg hd nx out' 0 0 with _ | ⟨z8, m8⟩ <;> rw [he] at h
  · rw [hApplyW.k_hoist_emit.eq_1] at h; cases h
  rw [hApplyW.k_hoist_emit.arm1] at h
  cases h
  have hE := emitL_eq_sort T c.toNat hlt
  have hEl := emitL_length T c.toNat hlt
  obtain ⟨hf8, hv8, hfr8⟩ := hEmit_ok T ord c tg hd nx out (fun y => rd m (ord.toNat + y))
    (by omega) (by omega) (by omega) (by omega) hlt n m7 m' 0 0 z8 (by rw [hs7]; omega)
    (by rw [hs7]; omega) (by simp)
    (fun j hj => by rw [hlow7 _ (by omega)]; exact htg6 j hj)
    (fun t ht => by rw [hB7.hd t ht])
    (fun j hj => hB7.nx j hj)
    (fun y hy => by rw [hlow7 _ (by omega), hlow6 _ (by omega)])
    (by simp only [UInt64.toNat_zero]; omega) he
  have hs8 : (m'.arr64 IW).size = (m.arr64 IW).size := by rw [frame_size hf8, hs7]
  have hF : MemFrame [IW] [] m4 m' := ((hf5.trans hf6).trans hf7).trans hf8
  have hF4 : MemFrame [IW] [200] m m4 := hm4 ▸
    (((allocMem_frame _ _).trans (allocMem_frame _ _)).trans (allocMem_frame _ _)).trans
      (allocMem_frame _ _)
  have hFall : MemFrame [IW] [200] m m' := hF4.trans (hF.mono (by simp) (by simp))
  have htop8 : iwTop m' = iwTop m + 4 * c.toNat := by
    rw [← htop4]; simp only [iwTop]; rw [hF.2.1 200 (by simp)]
  have hlow8 : ∀ i < iwTop m, rd m' i = rd m i := fun i hi => by
    rw [hfr8 i (by omega) (Or.inl (by simp; omega)), hlow7 i (by omega), hlow6 i hi]
  refine ⟨iwok_frame hF hI4, ⟨by omega, ?_, fun i hi => ?_, fun i hi => ?_⟩, hFall, by omega,
    by omega, fun j hj => ?_⟩
  · have := hFall.2.1 129 (by decide)
    simp only [erTop, this]; exact Nat.le_refl _
  · exact getElem?_of_rd i hs8 (by have := hI.1; omega) hs (hlow8 i hi)
  · rw [hFall.1 EREC (by decide) (by decide)]
  · rw [addrN, addrN]
    have hj' : (emitL T c.toNat 0)[j]? = some ((hoistOrder T c.toNat)[j]'(by
        simp [hoistOrder, List.length_mergeSort]; exact hj)) := by
      simp only [hoistOrder] at *
      rw [hE]; exact List.getElem?_eq_getElem _
    have := hv8 j _ (by simpa using hj')
    simp only [UInt64.toNat_zero, Nat.add_zero] at this
    exact this

theorem reorder_go (ds : Array IDeclaration) : ∀ (order : List Nat) (acc : Array IDeclaration),
    (∀ k ∈ order, k < ds.size) →
    order.foldl (fun acc k => acc ++ (ds[k]?.toArray)) acc = acc ++ (order.map fun k => ds[k]!).toArray
  | [], acc, _ => by simp
  | k :: rest, acc, h => by
    rw [List.foldl_cons, reorder_go ds rest _ (fun k' hk' => h k' (List.mem_cons_of_mem _ hk'))]
    have hk := h k List.mem_cons_self
    simp [hk]

/-- **`reorder` is the order mapped through the records.** -/
theorem reorder_eq (ds : Array IDeclaration) (order : List Nat) (h : ∀ k ∈ order, k < ds.size) :
    reorder ds order = (order.map fun k => ds[k]!).toArray := by
  simp only [reorder]
  rw [reorder_go ds order #[] h, Array.empty_append]

end L.Checker
