import ConAgua.Checker.HoistOrderRef2

/-!
# The hoist's reorder loops, on memory (lane `front4`)

The memory side of `hoistApply_ok` (`HoistOrderRef.lean`): `IW` read at `Nat` indices (`rd`), and
what each of `hZeroW`, `hBucketW`, `hChainW`, `hEmitW` leaves there (by induction on the fuel).
-/

open ConRon.Arena ConRon.Arena.Frontend
open L.Arena L.Ind L.Front L.Front.Ind

namespace L.Checker

/-! ## `IW` at `Nat` indices -/

/-- Word `i` of `IW`. -/
def rd (m : Mem) (i : Nat) : Word := rdW (m.arr64 IW) (UInt64.ofNat i)

theorem addrW (b k : Word) : b + k = UInt64.ofNat (b.toNat + k.toNat) := by
  rw [UInt64.ofNat_add, UInt64.ofNat_toNat, UInt64.ofNat_toNat]

theorem addrN (b : Word) (j : Nat) : b + UInt64.ofNat j = UInt64.ofNat (b.toNat + j) := by
  rw [UInt64.ofNat_add, UInt64.ofNat_toNat]

theorem addr1 (b : Word) (x : Nat) : b + UInt64.ofNat (x + 1) - 1 = UInt64.ofNat (b.toNat + x) := by
  simp only [UInt64.ofNat_add, UInt64.ofNat_toNat]; grind

theorem tgW_some (x : Nat) : tgW (some x) = UInt64.ofNat (x + 1) := rfl

theorem tgW_some_ne (x : Nat) (h : x + 1 < 2 ^ 64) : tgW (some x) ≠ 0 := by
  rw [tgW_some]; intro e
  have := congrArg UInt64.toNat e
  rw [UInt64.toNat_ofNat_of_lt' h] at this; simp at this

theorem tgW_eq_zero (o : Option Nat) (h : ∀ x, o = some x → x + 1 < 2 ^ 64) :
    tgW o = 0 ↔ o = none := by
  cases o with
  | none => simp [tgW]
  | some x => simp only [reduceCtorEq, iff_false]; exact tgW_some_ne x (h x rfl)

theorem toNat_succ (k : Word) (h : k.toNat + 1 < 2 ^ 64) : (k + 1).toNat = k.toNat + 1 := by
  rw [UInt64.toNat_add]; simp; omega

theorem word_succ (k : Word) : k + 1 = UInt64.ofNat (k.toNat + 1) := by
  rw [UInt64.ofNat_add, UInt64.ofNat_toNat]; rfl

theorem iteT {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

theorem iteF {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) : (if c then a else b) = b := by
  simp [h]

theorem word_le (a b : Word) : a ≤ b ↔ a.toNat ≤ b.toNat := UInt64.le_iff_toNat_le

theorem rd_set (m : Mem) (i j : Nat) (v : Word) (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) :
    rd (m.set64 IW (UInt64.ofNat i) v) j = if i = j ∧ i < (m.arr64 IW).size then v else rd m j := by
  simp only [rd, rdW_set64, true_and, UInt64.toNat_ofNat_of_lt' hi]
  have : (UInt64.ofNat i = UInt64.ofNat j) ↔ i = j := by
    constructor
    · intro e; have := congrArg UInt64.toNat e
      rwa [UInt64.toNat_ofNat_of_lt' hi, UInt64.toNat_ofNat_of_lt' hj] at this
    · intro e; rw [e]
  simp only [this]

theorem rd_set_eq (m : Mem) (i : Nat) (v : Word) (hi : i < (m.arr64 IW).size)
    (hs : (m.arr64 IW).size < 2 ^ 64) : rd (m.set64 IW (UInt64.ofNat i) v) i = v := by
  rw [rd_set _ _ _ _ (by omega) (by omega)]; simp [hi]

theorem rd_set_ne (m : Mem) (i j : Nat) (v : Word) (hi : i < 2 ^ 64) (hj : j < 2 ^ 64)
    (h : i ≠ j) : rd (m.set64 IW (UInt64.ofNat i) v) j = rd m j := by
  rw [rd_set _ _ _ _ hi hj]; simp [h]

theorem frame_set (m : Mem) (i v : Word) : MemFrame [IW] [] m (m.set64 IW i v) :=
  MemFrame.set64 m IW (by decide) i v

theorem frame_size {m m' : Mem} (h : MemFrame [IW] [] m m') :
    (m'.arr64 IW).size = (m.arr64 IW).size := h.2.2.1 IW

/-! ## `hoist_zero` -/

theorem hZero_ok (n : Nat) : ∀ (m m' : Mem) (o c k r : Word),
    o.toNat + c.toNat ≤ (m.arr64 IW).size → (m.arr64 IW).size < 2 ^ 64 →
    hZeroW n m o c k = some (r, m') →
    MemFrame [IW] [] m m' ∧ ∀ i < 2 ^ 64,
      rd m' i = if o.toNat + k.toNat ≤ i ∧ i < o.toNat + c.toNat then 0 else rd m i := by
  induction n with
  | zero => intro m m' o c k r _ _ h; simp [hZeroW.eq_1] at h
  | succ n ih =>
    intro m m' o c k r hb hs h
    by_cases hck : c ≤ k
    · rw [hZeroW.arm1 n m o c k hck] at h
      cases h
      refine ⟨MemFrame.refl _ _ _, fun i _ => ?_⟩
      rw [word_le] at hck
      rw [iteF (by omega)]
    · rw [hZeroW.arm2 n m o c k hck] at h
      rw [word_le] at hck
      have hk1 := toNat_succ k (by omega)
      have hs1 : ((m.set64 IW (o + k) 0).arr64 IW).size = (m.arr64 IW).size := size_set64 _ _ _ _ _
      obtain ⟨hf, hr⟩ := ih _ _ o c (k + 1) r (by rw [hs1]; omega) (by rw [hs1]; omega) h
      refine ⟨(frame_set m _ _).trans hf, fun i hi => ?_⟩
      rw [hr i hi, hk1, addrW, rd_set _ _ _ _ (by omega) hi]
      by_cases e : o.toNat + k.toNat = i
      · subst e; rw [iteF (by omega), iteT ⟨rfl, by omega⟩, iteT (by omega)]
      · simp only [e, false_and, ite_false]
        by_cases h1 : o.toNat + (k.toNat + 1) ≤ i ∧ i < o.toNat + c.toNat
        · rw [iteT h1, iteT (by omega)]
        · rw [iteF h1, iteF (by omega)]

/-! ## `hoist_any` -/

theorem hAny_ok (n : Nat) (m : Mem) (tg c : Word) (T : Std.HashMap Nat Nat)
    (hT : TgtR m tg c.toNat T) (hlt : ∀ (k t : Nat), T[k]? = some t → t < k) :
    ∀ (k r : Word) (m' : Mem), hAnyW n m tg c k = some (r, m') →
    m' = m ∧ (r = 0 ↔ ∀ j, k.toNat ≤ j → j < c.toNat → T[j]? = none) := by
  induction n with
  | zero => intro k r m' h; simp [hAnyW.eq_1] at h
  | succ n ih =>
    intro k r m' h
    by_cases hck : c ≤ k
    · rw [hAnyW.arm1 n m tg c k hck] at h
      cases h
      rw [word_le] at hck
      exact ⟨rfl, by simp only [true_iff]; intro j h1 h2; omega⟩
    · rw [word_le] at hck
      have hc64 : c.toNat < 2 ^ 64 := c.toNat_lt
      have hrd : rdW (m.arr64 IW) (tg + k) = tgW T[k.toNat]? := by
        rw [← hT.1 k.toNat (by omega), UInt64.ofNat_toNat]
      have hz : tgW T[k.toNat]? = 0 ↔ T[k.toNat]? = none :=
        tgW_eq_zero _ (fun x hx => by have := hlt _ _ hx; omega)
      by_cases hne : rdW (m.arr64 IW) (tg + k) ≠ 0
      · rw [hAnyW.arm2 n m tg c k (by rw [word_le]; omega) hne] at h
        cases h
        refine ⟨rfl, ?_⟩
        refine ⟨fun h => absurd h (by decide), fun hall => ?_⟩
        exact (hne (by rw [hrd, hz]; exact hall _ (Nat.le_refl _) (by omega))).elim
      · rw [hAnyW.arm3 n m tg c k (by rw [word_le]; omega) hne] at h
        obtain ⟨rfl, hr⟩ := ih (k + 1) r m' h
        refine ⟨rfl, ?_⟩
        rw [hr, toNat_succ k (by omega)]
        have hk : T[k.toNat]? = none := by rw [← hz, ← hrd]; exact Decidable.of_not_not hne
        constructor
        · intro h j h1 h2
          by_cases e : j = k.toNat
          · subst e; exact hk
          · exact h j (by omega) h2
        · intro h j h1 h2; exact h j (by omega) h2

/-! ## `hoist_bucket` -/

theorem rd_set2 (m : Mem) (i1 i2 j : Nat) (v1 v2 : Word) (h1 : i1 < (m.arr64 IW).size)
    (h2 : i2 < (m.arr64 IW).size) (hs : (m.arr64 IW).size < 2 ^ 64) (hj : j < 2 ^ 64) :
    rd ((m.set64 IW (UInt64.ofNat i1) v1).set64 IW (UInt64.ofNat i2) v2) j =
      if j = i2 then v2 else if j = i1 then v1 else rd m j := by
  rw [rd_set _ _ _ _ (by omega) hj, size_set64, rd_set _ _ _ _ (by omega) hj]
  by_cases e2 : j = i2
  · subst e2; simp [h2]
  · by_cases e1 : j = i1
    · subst e1; simp [h1, Ne.symm e2, e2]
    · simp [Ne.symm e2, Ne.symm e1, e2, e1]

/-- What `hoist_bucket` leaves after positions `0 ‥ k`: the heads (`hd`), the lasts (`tl`, where
the bucket is not empty) and the links (`nx`) of the buckets. -/
structure BInv (T : Std.HashMap Nat Nat) (C H TL NX k : Nat) (m : Mem) : Prop where
  hd : ∀ t < C, rd m (H + t) = tgW (posT T t 0 k).head?
  tl : ∀ t < C, posT T t 0 k ≠ [] → rd m (TL + t) = tgW (posT T t 0 k).getLast?
  nx : ∀ j < C, rd m (NX + j) = nxW T j k

theorem hBucket_ok (T : Std.HashMap Nat Nat) (tg c hd tl nx : Word)
    (l1 : tg.toNat + c.toNat ≤ hd.toNat) (l2 : hd.toNat + c.toNat ≤ tl.toNat)
    (l3 : tl.toNat + c.toNat ≤ nx.toNat) (hlt : ∀ (k t : Nat), T[k]? = some t → t < k) (n : Nat) :
    ∀ (m m' : Mem) (k r : Word), nx.toNat + c.toNat ≤ (m.arr64 IW).size →
    (m.arr64 IW).size < 2 ^ 64 → k.toNat ≤ c.toNat →
    (∀ j < c.toNat, rd m (tg.toNat + j) = tgW T[j]?) →
    BInv T c.toNat hd.toNat tl.toNat nx.toNat k.toNat m →
    hBucketW n m tg c hd tl nx k = some (r, m') →
    MemFrame [IW] [] m m' ∧ (∀ i < hd.toNat, rd m' i = rd m i) ∧
      BInv T c.toNat hd.toNat tl.toNat nx.toNat c.toNat m' := by
  induction n with
  | zero => intro m m' k r _ _ _ _ _ h; simp [hBucketW.eq_1] at h
  | succ n ih =>
    intro m m' k r hb hs hkc htg hB h
    by_cases hck : c ≤ k
    · rw [hBucketW.arm1 n m tg c hd tl nx k hck] at h
      cases h
      rw [word_le] at hck
      have : k.toNat = c.toNat := by omega
      rw [this] at hB
      exact ⟨MemFrame.refl _ _ _, fun _ _ => rfl, hB⟩
    · have hck' := hck
      rw [word_le] at hck'
      have hk1 := toNat_succ k (by omega)
      have hrd : rdW (m.arr64 IW) (tg + k) = tgW T[k.toNat]? := by
        rw [addrW]; exact htg _ (by omega)
      cases hT : T[k.toNat]? with
      | none =>
        rw [hT] at hrd
        rw [hBucketW.arm4 n m tg c hd tl nx k hck (by rw [hrd]; simp [tgW]),
          hBucketW.k1.arm1] at h
        have hB' : BInv T c.toNat hd.toNat tl.toNat nx.toNat (k + 1).toNat m := by
          rw [hk1]
          refine ⟨fun t ht => ?_, fun t ht hne => ?_, fun j hj => ?_⟩
          · rw [head_step T t _ (Or.inl (by rw [hT]; simp))]; exact hB.hd t ht
          · rw [posT_succ_ne T t _ _ (by rw [hT]; simp)] at hne ⊢; exact hB.tl t ht hne
          · rw [nxW_step T j _ (fun t h1 => by rw [hT] at h1; cases h1)]; exact hB.nx j hj
        exact ih m m' (k + 1) r hb hs (by omega) htg hB' h
      | some t =>
        have htk := hlt _ _ hT
        rw [hT, tgW_some] at hrd
        have hne : rdW (m.arr64 IW) (tg + k) ≠ 0 := by
          rw [hrd, ← tgW_some]; exact tgW_some_ne t (by omega)
        have hhd : rdW (m.arr64 IW) (hd + rdW (m.arr64 IW) (tg + k) - 1) =
            tgW (posT T t 0 k.toNat).head? := by
          rw [hrd, addr1]; exact hB.hd t (by omega)
        have hsz : ∀ (i v : Word), ((m.set64 IW i v).arr64 IW).size = (m.arr64 IW).size :=
          fun i v => size_set64 _ _ _ _ _
        by_cases h0 : posT T t 0 k.toNat = []
        · rw [h0] at hhd
          rw [hBucketW.arm2 n m tg c hd tl nx k hck hne hhd, hBucketW.k2.arm1,
            hBucketW.k1.arm1, hrd, addr1, addr1] at h
          have hr2 := fun j hj => rd_set2 m (hd.toNat + t) (tl.toNat + t) j
            (k + 1) (k + 1) (by omega) (by omega) hs hj
          have hB' : BInv T c.toNat hd.toNat tl.toNat nx.toNat (k + 1).toNat
              ((m.set64 IW (UInt64.ofNat (hd.toNat + t)) (k + 1)).set64 IW
                (UInt64.ofNat (tl.toNat + t)) (k + 1)) := by
            rw [hk1]
            refine ⟨fun t' ht' => ?_, fun t' ht' hne' => ?_, fun j hj => ?_⟩
            · rw [hr2 _ (by omega), iteF (by omega)]
              by_cases e : t' = t
              · subst e; rw [iteT rfl, head_new T t' _ hT h0]; exact word_succ k
              · rw [iteF (by omega), head_step T t' _ (Or.inl (by rw [hT]; simpa using Ne.symm e))]
                exact hB.hd t' ht'
            · rw [hr2 _ (by omega)]
              by_cases e : t' = t
              · subst e; rw [iteT rfl, last_step_eq T t' _ hT]; exact word_succ k
              · rw [iteF (by omega), iteF (by omega)]
                have hne'' : T[k.toNat]? ≠ some t' := by rw [hT]; simpa using Ne.symm e
                rw [posT_succ_ne T t' _ _ hne''] at hne' ⊢
                exact hB.tl t' ht' hne'
            · rw [hr2 _ (by omega), iteF (by omega), iteF (by omega)]
              rw [nxW_step T j _ (fun t'' h1 _ _ => by
                rw [hT] at h1; cases h1; rw [h0]; simp)]
              exact hB.nx j hj
          obtain ⟨hf, hlow, hB2⟩ := ih _ m' (k + 1) r (by simp only [size_set64]; omega)
            (by simp only [size_set64]; omega) (by omega)
            (fun j hj => by rw [hr2 _ (by omega), iteF (by omega), iteF (by omega)]; exact htg j hj)
            hB' h
          refine ⟨((frame_set _ _ _).trans (frame_set _ _ _)).trans hf, fun i hi => ?_, hB2⟩
          rw [hlow i hi, hr2 _ (by omega), iteF (by omega), iteF (by omega)]
        · cases hl : (posT T t 0 k.toNat).getLast? with
          | none => exact absurd (List.getLast?_eq_none_iff.1 hl) h0
          | some l =>
            have hlm := mem_posT.1 (List.mem_of_getLast? hl)
            have hnz : ¬ rdW (m.arr64 IW) (hd + rdW (m.arr64 IW) (tg + k) - 1) = 0 := by
              rw [hhd]; intro e
              cases hh : (posT T t 0 k.toNat).head? with
              | none => simp at hh; exact h0 hh
              | some x =>
                rw [hh] at e
                have := (mem_posT.1 (List.mem_of_head? hh)).2.1
                exact tgW_some_ne x (by omega) e
            have htl : rdW (m.arr64 IW) (UInt64.ofNat (tl.toNat + t)) = UInt64.ofNat (l + 1) := by
              have := hB.tl t (by omega) h0
              rw [hl, tgW_some] at this; exact this
            rw [hBucketW.arm3 n m tg c hd tl nx k hck hne hnz, hBucketW.k2.arm1,
              hBucketW.k1.arm1, hrd, addr1, htl, addr1] at h
            have hr2 := fun j hj => rd_set2 m (nx.toNat + l) (tl.toNat + t) j
              (k + 1) (k + 1) (by omega) (by omega) hs hj
            have hB' : BInv T c.toNat hd.toNat tl.toNat nx.toNat (k + 1).toNat
                ((m.set64 IW (UInt64.ofNat (nx.toNat + l)) (k + 1)).set64 IW
                  (UInt64.ofNat (tl.toNat + t)) (k + 1)) := by
              rw [hk1]
              refine ⟨fun t' ht' => ?_, fun t' ht' hne' => ?_, fun j hj => ?_⟩
              · rw [hr2 _ (by omega), iteF (by omega), iteF (by omega)]
                by_cases e : t' = t
                · subst e; rw [head_step T t' _ (Or.inr h0)]; exact hB.hd t' ht'
                · rw [head_step T t' _ (Or.inl (by rw [hT]; simpa using Ne.symm e))]
                  exact hB.hd t' ht'
              · rw [hr2 _ (by omega)]
                by_cases e : t' = t
                · subst e; rw [iteT rfl, last_step_eq T t' _ hT]; exact word_succ k
                · rw [iteF (by omega), iteF (by omega)]
                  have hne'' : T[k.toNat]? ≠ some t' := by rw [hT]; simpa using Ne.symm e
                  rw [posT_succ_ne T t' _ _ hne''] at hne' ⊢
                  exact hB.tl t' ht' hne'
              · rw [hr2 _ (by omega), iteF (by omega)]
                by_cases e : j = l
                · subst e; rw [iteT rfl, nxW_last T _ t j hT hl]; exact word_succ k
                · rw [iteF (by omega)]
                  rw [nxW_step T j _ (fun t'' h1 _ _ => by
                    rw [hT] at h1; cases h1; rw [hl]; simpa using Ne.symm e)]
                  exact hB.nx j hj
            obtain ⟨hf, hlow, hB2⟩ := ih _ m' (k + 1) r (by simp only [size_set64]; omega)
              (by simp only [size_set64]; omega) (by omega)
              (fun j hj => by rw [hr2 _ (by omega), iteF (by omega), iteF (by omega)]; exact htg j hj)
              hB' h
            refine ⟨((frame_set _ _ _).trans (frame_set _ _ _)).trans hf, fun i hi => ?_, hB2⟩
            rw [hlow i hi, hr2 _ (by omega), iteF (by omega), iteF (by omega)]

end L.Checker
