import ConAgua.Arena.SlotRehash

/-!
# The store library: the growth keeps the relation (lane kstp)

`SlotGrowSpec.lean`'s `kgrowM` (the KSTP growth of one tier: the doubled table at the tier's other
offset, zeroed, then every live slot of the old table re-inserted with its key word from the
home of `G` of the key word), read as the table relation: if `G` of every admissible key word is
the node's hash (`hGh`), the relation holds after the growth (`storeR_kgrow`).
-/

open ConRon.Arena

set_option linter.unusedSimpArgs false

namespace L.Arena

/-! ## Zeroing -/

theorem rdW_oob (a : Array Word) (x : Word) (h : a.size ≤ x.toNat) : rdW a x = 0 := by
  simp [rdW, h]

theorem rdW_set64_zero (m : Mem) (a b : ArrId) (k x : Word) :
    rdW ((m.set64 a k 0).arr64 b) x = if b = a ∧ k = x then 0 else rdW (m.arr64 b) x := by
  rw [rdW_set64]
  by_cases h : b = a
  · subst h
    by_cases hk : k = x
    · subst hk
      by_cases hs : k.toNat < (m.arr64 b).size
      · simp [hs]
      · simp [hs, rdW_oob (m.arr64 b) k (by omega)]
    · simp [hk]
  · simp [h]

theorem zero8_rd (sa : ArrId) (k : Word) (m : Mem) (x : Word) (hk : k.toNat + 8 < 2 ^ 64) :
    rdW ((zero8 sa k m).arr64 sa) x =
      if k.toNat ≤ x.toNat ∧ x.toNat < k.toNat + 8 then 0 else rdW (m.arr64 sa) x := by
  simp only [zero8, rdW_set64_zero, true_and]
  have e : ∀ i : Nat, i < 8 → (k + UInt64.ofNat i).toNat = k.toNat + i := fun i hi => by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat']; omega
  have e1 := e 1 (by omega); have e2 := e 2 (by omega); have e3 := e 3 (by omega)
  have e4 := e 4 (by omega); have e5 := e 5 (by omega); have e6 := e 6 (by omega)
  have e7 := e 7 (by omega)
  simp only [UInt64.ofNat_one] at e1
  simp only [show UInt64.ofNat 2 = 2 from rfl, show UInt64.ofNat 3 = 3 from rfl,
    show UInt64.ofNat 4 = 4 from rfl, show UInt64.ofNat 5 = 5 from rfl,
    show UInt64.ofNat 6 = 6 from rfl, show UInt64.ofNat 7 = 7 from rfl] at *
  have hx : ∀ y : Word, (y = x) = (y.toNat = x.toNat) := fun y => by
    simp [UInt64.toNat_inj]
  simp only [hx, e1, e2, e3, e4, e5, e6, e7]
  grind (splits := 20)

/-- **The zero loop** zeroes the `8 e` words from `x` (no wrap) and changes no other word. -/
theorem kzeroW_rd (sa : ArrId) : ∀ (e : Nat) (x : Word) (m : Mem), x.toNat + 8 * e < 2 ^ 64 →
    ∀ y, rdW ((kzeroW sa x e m).arr64 sa) y =
      if x.toNat ≤ y.toNat ∧ y.toNat < x.toNat + 8 * e then 0 else rdW (m.arr64 sa) y
  | 0, x, m, _, y => by
    simp only [kzeroW, Nat.mul_zero, Nat.add_zero]
    split
    · omega
    · rfl
  | e + 1, x, m, hx, y => by
    have e8 : (x + 8).toNat = x.toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
    simp only [kzeroW]
    rw [kzeroW_rd sa e (x + 8) _ (by omega) y, zero8_rd sa x m y (by omega)]
    simp only [e8]
    by_cases hA : x.toNat + 8 ≤ y.toNat ∧ y.toNat < x.toNat + 8 + 8 * e <;>
      by_cases hB : x.toNat ≤ y.toNat ∧ y.toNat < x.toNat + 8 <;>
      by_cases hC : x.toNat ≤ y.toNat ∧ y.toNat < x.toNat + 8 * (e + 1) <;>
      simp only [hA, hB, hC, ↓reduceIte] <;> first | rfl | (exfalso; omega)

/-! ## Marking -/

/-- **The mark loop** adds `MARK` to the live value words of its `e` slots from `x` (no wrap) and
changes no other word. -/
theorem kmarkW_rd (sa : ArrId) (bt : Word) : ∀ (e : Nat) (x : Word) (m : Mem),
    x.toNat + 2 * e ≤ (m.arr64 sa).size → (m.arr64 sa).size < 2 ^ 61 →
    ∀ y, rdW ((kmarkW sa bt e x m).arr64 sa) y =
      if x.toNat ≤ y.toNat ∧ y.toNat < x.toNat + 2 * e ∧ (y.toNat - x.toNat) % 2 = 0 ∧
        bt < rdW (m.arr64 sa) y
      then rdW (m.arr64 sa) y + MARK else rdW (m.arr64 sa) y
  | 0, x, m, _, _, y => by simp only [kmarkW]; rw [if_neg (by omega)]
  | e + 1, x, m, hx, hL, y => by
    have e2 : (x + 2).toNat = x.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
    simp only [kmarkW]
    generalize hm' : (if bt < rdW (m.arr64 sa) x then m.set64 sa x (rdW (m.arr64 sa) x + MARK) else m) = m'
    have hsz : (m'.arr64 sa).size = (m.arr64 sa).size := by
      rw [← hm']; split
      · exact size_set64 _ _ _ _ _
      · rfl
    have hrd : ∀ y, rdW (m'.arr64 sa) y =
        if x = y ∧ bt < rdW (m.arr64 sa) x then rdW (m.arr64 sa) x + MARK else rdW (m.arr64 sa) y := by
      intro y; rw [← hm']
      by_cases hb : bt < rdW (m.arr64 sa) x
      · simp only [hb, ↓reduceIte, and_true]
        rw [rdW_set64]; simp only [true_and]
        have : x.toNat < (m.arr64 sa).size := by omega
        simp [this]
      · simp [hb]
    rw [kmarkW_rd sa bt e (x + 2) m' (by rw [hsz, e2]; omega) (by rw [hsz]; exact hL) y, e2]
    simp only [hrd]
    by_cases hy : x = y
    · subst hy
      simp only [true_and]
      by_cases hb : bt < rdW (m.arr64 sa) x <;> simp [hb] <;> omega
    · have hy' : x.toNat ≠ y.toNat := fun h => hy (UInt64.toNat_inj.mp h)
      simp only [hy, false_and, ↓reduceIte]
      by_cases hA : x.toNat + 2 ≤ y.toNat ∧ y.toNat < x.toNat + 2 + 2 * e ∧ (y.toNat - (x.toNat + 2)) % 2 = 0
        ∧ bt < rdW (m.arr64 sa) y
      · obtain ⟨a1, a2, a3, a4⟩ := hA
        rw [if_pos ⟨a1, a2, a3, a4⟩, if_pos ⟨by omega, by omega, by omega, a4⟩]
      · rw [if_neg hA, if_neg]
        rintro ⟨a1, a2, a3, a4⟩
        exact hA ⟨by omega, by omega, by omega, a4⟩

/-! ## The growth keeps the relation -/

theorem word_ne_of_toNat {x y : Word} (h : x.toNat ≠ y.toNat) : x ≠ y := fun e => h (by rw [e])

section grow
variable {α δ : Type} {k : IdxKind} [BEq α] [Hashable α]
variable (S : Schema) (R : Mem → Word → Word → α → Prop) (hs : Mem → Word → Word → Word)
  (KP : Mem → Word → Word → Word → Prop)

/-- **The growth keeps the relation**: if `G` of every key word a slot of tier `t` may hold is the
node's hash, the memory after `kgrowM` represents the same tables. -/
theorem storeR_kgrow (hS : S.WF) (hfr : RFrame S R hs) (hkf : KFrame S hs KP)
    (G : Mem → Word → Word) (m m' : Mem) (t : Word) (ht : t ≤ 1)
    (hGh : ∀ mi : Mem, (∀ a, a ≠ tierA S.sa t → mi.arr64 a = m.arr64 a) →
      ∀ i K, KP m t i K → G mi K = hs m t i)
    (on : Bool) (tbP tbS : Tbl α (Idx k) δ) (hR : StoreR S R hs KP m on tbP tbS)
    (h : kgrowM S.sa G t m = some m') : StoreR S R hs KP m' on tbP tbS := by
  obtain ⟨⟨hctl, hb⟩, hfl, hT0, hT1, hG⟩ := hR
  -- the numbers
  generalize hsa : tierA S.sa t = sa at *
  generalize hn : knW S.sa m t = n at *
  generalize ho : koW S.sa m t = o at *
  generalize hbt : rdW (m.arr64 CTL) SCB * t = bt at *
  obtain ⟨hL, hn8, hn8m, hlay⟩ := hG.tier S m t ht
  try simp only [hsa, hn, ho] at hL hlay hn8 hn8m
  have hlen : (m.len64 sa).toNat = (m.arr64 sa).size := by
    rw [len64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have hroom : ¬ m.len64 sa - 2 < o + n * 2 * 2 := fun hc => by
    simp [kgrowM, hsa, hn, ho, hc] at h
  have e4 : (o + n * 2 * 2).toNat = o.toNat + 4 * n.toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_mul]; simp; omega
  have hroom' : o.toNat + 4 * n.toNat ≤ (m.arr64 sa).size - 2 := by
    have := UInt64.not_lt.mp hroom
    rw [UInt64.le_iff_toNat_le, e4, UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le, hlen]; simp; omega), hlen] at this
    simpa using this
  simp only [kgrowM, hsa, hn, ho, hbt, if_neg hroom] at h
  generalize hob : o + 2 = ob at h
  have hobN : ob.toNat = o.toNat + 2 := by rw [← hob, UInt64.toNat_add]; simp; omega
  have e2n : (n * 2).toNat = 2 * n.toNat := by rw [UInt64.toNat_mul]; simp; omega
  -- the memories
  generalize hm1 : m.set64 sa 0 (n * 2 - SN0) = m1 at h
  generalize hm2 : kzeroW sa (ob + n * 2) (n >>> 2).toNat m1 = m2 at h
  generalize hm3 : kmarkW sa bt n.toNat ob m2 = m3 at h
  have fr1 : GFr sa m m1 := by rw [← hm1]; exact GFr.set64 _ _ _ _
  have fr2 : GFr sa m1 m2 := by rw [← hm2]; exact kzeroW_fr _ _ _ _
  have fr3 : GFr sa m2 m3 := by rw [← hm3]; exact kmarkW_fr _ _ _ _ _
  have fr13 := (fr1.trans fr2).trans fr3
  have hsz3 : (m3.arr64 sa).size = (m.arr64 sa).size := fr13.2.1 sa
  have hsz2 : (m2.arr64 sa).size = (m.arr64 sa).size := (fr1.trans fr2).2.1 sa
  have eob2n : (ob + n * 2).toNat = ob.toNat + 2 * n.toNat := by
    rw [UInt64.toNat_add, e2n]; omega
  have eh : (n >>> 2).toNat * 8 = 2 * n.toNat := by rw [UInt64.toNat_shiftRight]; simp; omega
  have rd1 : ∀ y : Word, rdW (m1.arr64 sa) y = if y = 0 then n * 2 - SN0 else rdW (m.arr64 sa) y := by
    intro y; rw [← hm1, rdW_set64]
    by_cases hy : y = 0
    · subst hy
      have : (0 : Word).toNat < (m.arr64 sa).size := by simp; omega
      simp [this]; intro h'; rw [h'] at this; simp at this
    · simp [hy, Ne.symm hy]
  have rd2 : ∀ y : Word, rdW (m2.arr64 sa) y =
      if ob.toNat + 2 * n.toNat ≤ y.toNat ∧ y.toNat < ob.toNat + 4 * n.toNat then 0
      else rdW (m1.arr64 sa) y := by
    intro y
    rw [← hm2, kzeroW_rd _ _ _ _ (by rw [eob2n, Nat.mul_comm 8, eh]; omega) y, eob2n,
      Nat.mul_comm 8, eh]
    congr 1; apply propext; omega
  have rd3 : ∀ y : Word, rdW (m3.arr64 sa) y =
      if ob.toNat ≤ y.toNat ∧ y.toNat < ob.toNat + 2 * n.toNat ∧ (y.toNat - ob.toNat) % 2 = 0 ∧
        bt < rdW (m2.arr64 sa) y
      then rdW (m2.arr64 sa) y + MARK else rdW (m2.arr64 sa) y := by
    intro y; rw [← hm3]; exact kmarkW_rd sa bt n.toNat ob m2 (by rw [hsz2]; omega) (by rw [hsz2]; omega) y
  have r2m : ∀ y : Word, 2 ≤ y.toNat → y.toNat < ob.toNat + 2 * n.toNat →
      rdW (m2.arr64 sa) y = rdW (m.arr64 sa) y := fun y h1 h2 => by
    rw [rd2, if_neg (by omega), rd1, if_neg (word_ne_of_toNat (by simp; omega))]
  -- the tier and its numbers
  have hTt : TierR S R hs KP m t (if t = 0 then tbP else tbS) := by
    rcases le_one_cases t ht with rfl | rfl
    · simpa using hT0
    · simpa using hT1
  generalize htb : (if t = 0 then tbP else tbS) = tb at hTt
  obtain ⟨hc', hcap, hrs, hrec, hsome, hback, hsl, hkp, hrun⟩ := hTt
  have hc27 : (cntW S m t).toNat ≤ 2 ^ 27 := by rw [hc']; exact hcap
  have hbt63 : bt.toNat + (cntW S m t).toNat + 1 < 2 ^ 63 := by
    rw [← hbt]
    rcases le_one_cases t ht with rfl | rfl
    · simp; omega
    · simp; omega
  have hN0 : (0 : Word) < n * 2 := UInt64.lt_iff_toNat_lt.mpr (by rw [e2n]; simp; omega)
  have hnN : n ≤ n * 2 := UInt64.le_iff_toNat_le.mpr (by rw [e2n]; omega)
  have hNL : ob.toNat + 2 * (n * 2).toNat ≤ (m3.arr64 sa).size := by rw [hsz3, e2n]; omega
  have hL3 : (m3.arr64 sa).size < 2 ^ 61 := by rw [hsz3]; exact hL
  have hob2 : 2 ≤ ob.toNat := by omega
  have hkr : krW S.sa m t = ob := by simp only [krW, hsa, ho, hob]
  have hnS : nSl S m t = n := by simp only [nSl, hn]
  have adr := fun j (hj : j < n * 2) => adr_toNat sa ob (n * 2) m3 hob2 hNL hL3 j hj
  have V3 : ∀ j : Word, j < n * 2 → VW sa ob m3 j =
      if j < n then (if bt < VW sa ob m j then VW sa ob m j + MARK else VW sa ob m j) else 0 := by
    intro j hj
    have a := (adr j hj).1
    have hjN := UInt64.lt_iff_toNat_lt.mp hj; rw [e2n] at hjN
    simp only [VW]
    by_cases hjn : j < n
    · have := UInt64.lt_iff_toNat_lt.mp hjn
      rw [rd3, r2m _ (by rw [a]; omega) (by rw [a]; omega)]
      simp only [hjn, ↓reduceIte]
      by_cases hb' : bt < rdW (m.arr64 sa) (ob + j * 2)
      · rw [if_pos ⟨by rw [a]; omega, by rw [a]; omega, by rw [a]; omega, hb'⟩]; simp [VW, hb']
      · rw [if_neg (fun h' => hb' h'.2.2.2)]; simp [VW, hb']
    · have := UInt64.not_lt.mp hjn; have := UInt64.le_iff_toNat_le.mp this
      simp only [hjn, ↓reduceIte]
      rw [rd3, if_neg (fun h' => by have := h'.2.1; rw [a] at this; omega), rd2,
        if_pos ⟨by rw [a]; omega, by rw [a]; omega⟩]
  have K3 : ∀ j : Word, j < n → KW sa ob m3 j = KW sa ob m j := by
    intro j hj
    have hjN : j < n * 2 := UInt64.lt_iff_toNat_lt.mpr (by
      have := UInt64.lt_iff_toNat_lt.mp hj; rw [e2n]; omega)
    have a := (adr j hjN).2
    have := UInt64.lt_iff_toNat_lt.mp hj
    simp only [KW]
    rw [rd3, if_neg (fun h' => by have := h'.2.2.1; rw [a] at this; omega),
      r2m _ (by rw [a]; omega) (by rw [a]; omega)]
  -- the old table's facts, as value words
  have oldv : ∀ j : Word, j < n → bt < VW sa ob m j →
      (VW sa ob m j).toNat ≤ bt.toNat + (cntW S m t).toNat ∧
      KP m t (VW sa ob m j - bt - 1) (KW sa ob m j) := by
    intro j hj hv
    have hjs : j < nSl S m t := by rw [hnS]; exact hj
    have e : slotW S m t j = VW sa ob m j - bt := by
      have hv' : ¬ rdW (m.arr64 sa) (ob + j * 2) ≤ bt := UInt64.not_le.mpr hv
      simp only [slotW, slotV, slotRd, baseW, hsa, hkr, hbt, VW, hv', ↓reduceIte]
    have hne : slotW S m t j ≠ 0 := by
      rw [e]; intro h0; have := UInt64.lt_iff_toNat_lt.mp hv; have := congrArg UInt64.toNat h0
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt hv)] at this; simp at this; omega
    refine ⟨?_, ?_⟩
    · have := hsl j hjs
      rw [e, UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt hv)] at this
      rw [hc']; omega
    · have := hkp j hjs hne
      rw [e] at this
      simpa only [slotK, hsa, hkr, KW] using this
  -- the invariant at the start
  have hI0 : RInv sa ob (n * 2) n bt (cntW S m t) (KP m t) (hs m t) m3 m3 0 := by
    refine ⟨GFr.refl _ _, rfl, rfl, fun j hj => ?_, fun x hx => ?_⟩
    · rw [SlotOK, V3 j hj]
      by_cases hjn : j < n
      · simp only [hjn, ↓reduceIte]
        by_cases hv : bt < VW sa ob m j
        · simp only [hv, ↓reduceIte]
          obtain ⟨hle, hK⟩ := oldv j hjn hv
          have hlt : (VW sa ob m j).toNat < 2 ^ 63 := by omega
          have hsub : VW sa ob m j + MARK - MARK = VW sa ob m j := UInt64.add_sub_cancel _ _
          refine .inr (.inr ⟨(mark_le_iff _).mpr (by rw [add_mark_toNat _ hlt]; omega), by rw [hsub]; exact hv,
            by rw [hsub]; exact hle, by rw [hsub, K3 j hjn]; exact hK, (by simp [UInt64.le_iff_toNat_le]), trivial⟩)
        · simp only [hv, ↓reduceIte]; exact .inl (UInt64.not_lt.mp hv)
      · simp only [hjn, ↓reduceIte]; exact .inl ((by simp [UInt64.le_iff_toNat_le]))
    · left
      have hxi : x.toNat < tb.nodes.size := by rw [← hc']; exact hx
      obtain ⟨d, hd1, hd2⟩ := hrun x hxi
      have hn0 : 0 < nSl S m t := UInt64.lt_iff_toNat_lt.mpr (by rw [hnS]; simp; omega)
      have hjo := walkW_lt (nSl S m t) (homeS S m t (hs m t x)) d (homeW_lt _ _ hn0)
      generalize walkW (nSl S m t) (homeS S m t (hs m t x)) d = jo at hd1 hjo
      rw [hnS] at hjo
      have hx1 : (x + 1).toNat = x.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have sw : slotW S m t jo = slotRd (VW sa ob m jo) bt := by
        simp only [slotW, slotV, baseW, hsa, hkr, hbt, VW]
      rw [sw] at hd1
      unfold slotRd at hd1
      have hv : bt < VW sa ob m jo := by
        apply Classical.byContradiction; intro hle
        rw [if_pos (UInt64.not_lt.mp hle)] at hd1
        have := congrArg UInt64.toNat hd1; rw [hx1] at this; simp at this
      rw [if_neg (UInt64.not_le.mpr hv)] at hd1
      have hvx : VW sa ob m jo = bt + x + 1 := by
        rw [← UInt64.sub_add_cancel (VW sa ob m jo) bt, hd1]; grind
      have hjoN : jo < n * 2 := UInt64.lt_iff_toNat_lt.mpr (by
        have := UInt64.lt_iff_toNat_lt.mp hjo; rw [e2n]; omega)
      refine ⟨jo, hjoN, ?_⟩
      rw [V3 jo hjoN, if_pos hjo, if_pos hv, hvx]
  -- the invariant at the end
  have hGh' : ∀ mi : Mem, GFr sa m3 mi → ∀ x K, KP m t x K → G mi K = hs m t x :=
    fun mi hmi x K hK => hGh mi (fun a ha => (hmi.1 a ha).trans (fr13.1 a ha)) x K hK
  have hIf := krehashW_inv sa ob (n * 2) n bt (cntW S m t) (KP m t) (hs m t) m3 hob2 hNL hL3 hbt63 hnN G
    hGh' hN0 0 n m3 m' ((by simp [UInt64.le_iff_toNat_le])) hI0 h
  obtain ⟨frf, hw0, hw1, hslf, hnodef⟩ := hIf
  sorry

end grow

end L.Arena
