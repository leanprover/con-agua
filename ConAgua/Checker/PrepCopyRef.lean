import ConAgua.Checker.HoistOrderRef3
import ConAgua.Checker.HoistTargetsRef
import ConAgua.Checker.Prelude

/-!
# `prepare_prelude`'s rewrite of `DECL` (lane `front4`)

`prep_copy` copies the records `ord[0 ‥ c)` (eight words each) to the slice `t`, `prep_back` copies
the slice back to `DECL[1 ..]`: record `i` of `DECL` after is record `ord[i]` before.
-/

open ConRon.Arena ConRon.Arena.Frontend
open L.Arena L.Ind L.Front L.Front.Ind

namespace L.Checker

/-! ## The four loops, on memory -/

theorem pc_get_set64 (m : Mem) (a b : ArrId) (k v : Word) (x : Nat) :
    ((m.set64 a k v).arr64 b)[x]? =
      if b = a ∧ k.toNat = x ∧ k.toNat < (m.arr64 a).size then some v else (m.arr64 b)[x]? := by
  by_cases h : b = a
  · subst h; rw [Mem.arr64_set64_same]
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]; grind
  · rw [Mem.arr64_set64_ne _ _ _ _ _ h]; simp [h]

theorem pc_toNat3 (a b c : Word) (h : a.toNat + 8 * b.toNat + c.toNat < 2 ^ 64) :
    (a + 8 * b + c).toNat = a.toNat + 8 * b.toNat + c.toNat := by
  rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul]
  have h8 : (8 : Word).toNat = 8 := rfl
  rw [h8]
  rw [Nat.mod_eq_of_lt (by omega : 8 * b.toNat < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : a.toNat + 8 * b.toNat < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : a.toNat + 8 * b.toNat + c.toNat < 2 ^ 64)]

theorem pc_ofNat_toNat (a : Word) (j : Nat) (h : a.toNat = j) : UInt64.ofNat j = a := by
  subst h; exact UInt64.ofNat_toNat

theorem pCopyRec_ok (t q i : Word) (n : Nat) : ∀ (m m' : Mem) (k z : Word), k.toNat ≤ 8 →
    t.toNat + 8 * i.toNat + 8 ≤ (m.arr64 IW).size → (m.arr64 IW).size < 2 ^ 64 →
    pCopyRecW n m t q i k = some (z, m') →
    MemFrame [IW] [] m m' ∧ ∀ x : Nat, (m'.arr64 IW)[x]? =
      if t.toNat + 8 * i.toNat + k.toNat ≤ x ∧ x < t.toNat + 8 * i.toNat + 8 then
        some (rdW (m.arr64 DECL) (q + UInt64.ofNat (x - (t.toNat + 8 * i.toNat))))
      else (m.arr64 IW)[x]? := by
  induction n with
  | zero => intro m m' k z _ _ _ h; simp [pCopyRecW.eq_1] at h
  | succ n ih =>
    intro m m' k z hk hb hs h
    by_cases h8 : 8 ≤ k
    · rw [pCopyRecW.arm1 n m t q i k h8] at h
      cases h
      rw [word_le] at h8
      have h8' : (8 : Word).toNat = 8 := rfl
      exact ⟨MemFrame.refl _ _ _, fun x => by rw [iteF (by omega)]⟩
    · rw [pCopyRecW.arm2 n m t q i k h8] at h
      rw [word_le] at h8
      have h8' : (8 : Word).toNat = 8 := rfl
      have hk1 := toNat_succ k (by omega)
      have hs1 := size_set64 m IW IW (t + 8 * i + k) (rdW (m.arr64 DECL) (q + k))
      obtain ⟨hf, hr⟩ := ih _ _ (k + 1) z (by omega) (by rw [hs1]; omega) (by rw [hs1]; omega) h
      refine ⟨(MemFrame.set64 m IW (by decide) _ _).trans hf, fun x => ?_⟩
      have hD : ((m.set64 IW (t + 8 * i + k) (rdW (m.arr64 DECL) (q + k))).arr64 DECL) = m.arr64 DECL :=
        Mem.arr64_set64_ne _ _ _ _ _ (by decide)
      rw [hr x, hD, hk1, pc_get_set64, pc_toNat3 _ _ _ (by omega)]
      by_cases e : t.toNat + 8 * i.toNat + k.toNat = x
      · subst e
        rw [iteF (by omega), iteT ⟨rfl, rfl, by omega⟩, iteT (by omega)]
        congr 3
        rw [pc_ofNat_toNat k _ (by omega)]
      · simp only [e, false_and, and_false, ite_false]
        by_cases h1 : t.toNat + 8 * i.toNat + (k.toNat + 1) ≤ x ∧ x < t.toNat + 8 * i.toNat + 8
        · rw [iteT h1, iteT (by omega)]
        · rw [iteF h1, iteF (by omega)]

theorem pBackRec_ok (t i : Word) (n : Nat) : ∀ (m m' : Mem) (k z : Word), k.toNat ≤ 8 →
    1 + 8 * i.toNat + 8 ≤ (m.arr64 DECL).size → (m.arr64 DECL).size < 2 ^ 64 →
    pBackRecW n m t i k = some (z, m') →
    MemFrame [DECL] [] m m' ∧ ∀ x : Nat, (m'.arr64 DECL)[x]? =
      if 1 + 8 * i.toNat + k.toNat ≤ x ∧ x < 1 + 8 * i.toNat + 8 then
        some (rdW (m.arr64 IW) (t + 8 * i + UInt64.ofNat (x - (1 + 8 * i.toNat))))
      else (m.arr64 DECL)[x]? := by
  induction n with
  | zero => intro m m' k z _ _ _ h; simp [pBackRecW.eq_1] at h
  | succ n ih =>
    intro m m' k z hk hb hs h
    by_cases h8 : 8 ≤ k
    · rw [pBackRecW.arm1 n m t i k h8] at h
      cases h
      rw [word_le] at h8
      have h8' : (8 : Word).toNat = 8 := rfl
      exact ⟨MemFrame.refl _ _ _, fun x => by rw [iteF (by omega)]⟩
    · rw [pBackRecW.arm2 n m t i k h8] at h
      rw [word_le] at h8
      have h8' : (8 : Word).toNat = 8 := rfl
      have hk1 := toNat_succ k (by omega)
      have hs1 := size_set64 m DECL DECL (1 + 8 * i + k) (rdW (m.arr64 IW) (t + 8 * i + k))
      obtain ⟨hf, hr⟩ := ih _ _ (k + 1) z (by omega) (by rw [hs1]; omega) (by rw [hs1]; omega) h
      refine ⟨(MemFrame.set64 m DECL (by decide) _ _).trans hf, fun x => ?_⟩
      have hD : ((m.set64 DECL (1 + 8 * i + k) (rdW (m.arr64 IW) (t + 8 * i + k))).arr64 IW) = m.arr64 IW :=
        Mem.arr64_set64_ne _ _ _ _ _ (by decide)
      have h1' : (1 : Word).toNat = 1 := rfl
      rw [hr x, hD, hk1, pc_get_set64, pc_toNat3 _ _ _ (by omega), h1']
      by_cases e : 1 + 8 * i.toNat + k.toNat = x
      · subst e
        rw [iteF (by omega), iteT ⟨rfl, rfl, by omega⟩, iteT (by omega)]
        congr 2
        rw [pc_ofNat_toNat k _ (by omega)]
      · simp only [e, false_and, and_false, ite_false]
        by_cases h1 : 1 + 8 * i.toNat + (k.toNat + 1) ≤ x ∧ x < 1 + 8 * i.toNat + 8
        · rw [iteT h1, iteT (by omega)]
        · rw [iteF h1, iteF (by omega)]


theorem pCopy_ok (ord c t : Word) (n : Nat) : ∀ (m m' : Mem) (i z : Word), i.toNat ≤ c.toNat →
    ord.toNat + c.toNat ≤ t.toNat → t.toNat + 8 * c.toNat ≤ (m.arr64 IW).size →
    (m.arr64 IW).size < 2 ^ 64 → pCopyW n m ord c t i = some (z, m') →
    MemFrame [IW] [] m m' ∧ ∀ x : Nat, (m'.arr64 IW)[x]? =
      if t.toNat + 8 * i.toNat ≤ x ∧ x < t.toNat + 8 * c.toNat then
        some (rdW (m.arr64 DECL) (1 + 8 * rdW (m.arr64 IW) (ord + UInt64.ofNat ((x - t.toNat) / 8)) +
          UInt64.ofNat ((x - t.toNat) % 8)))
      else (m.arr64 IW)[x]? := by
  induction n with
  | zero => intro m m' i z _ _ _ _ h; simp [pCopyW.eq_1] at h
  | succ n ih =>
    intro m m' i z hi ho hb hs h
    by_cases hci : c ≤ i
    · rw [pCopyW.arm1 n m ord c t i hci] at h
      cases h
      rw [word_le] at hci
      exact ⟨MemFrame.refl _ _ _, fun x => by rw [iteF (by omega)]⟩
    · rw [pCopyW.arm2 n m ord c t i hci] at h
      rw [word_le] at hci
      have hi1 := toNat_succ i (by omega)
      cases hrc : pCopyRecW n m t (1 + 8 * rdW (m.arr64 IW) (ord + i)) i 0 with
      | none => rw [hrc] at h; simp [pCopyW.k_prep_copy_rec] at h
      | some p =>
        obtain ⟨z₁, m₁⟩ := p
        rw [hrc, pCopyW.k_prep_copy_rec.arm1] at h
        obtain ⟨hf1, hr1⟩ := pCopyRec_ok t _ i n m m₁ 0 z₁ (by decide) (by omega) hs hrc
        have h0 : (0 : Word).toNat = 0 := rfl
        rw [h0] at hr1
        have hs1 : (m₁.arr64 IW).size = (m.arr64 IW).size := hf1.2.2.1 IW
        obtain ⟨hf2, hr2⟩ := ih m₁ m' (i + 1) z (by omega) ho (by omega) (by omega) h
        refine ⟨hf1.trans hf2, fun x => ?_⟩
        have hD : m₁.arr64 DECL = m.arr64 DECL := hf1.1 DECL (by decide) (by decide)
        have hO : ∀ j < c.toNat, rdW (m₁.arr64 IW) (ord + UInt64.ofNat j) =
            rdW (m.arr64 IW) (ord + UInt64.ofNat j) := by
          intro j hj
          rw [rdW_addr _ _ _ (by omega), rdW_addr _ _ _ (by omega), hr1, iteF (by omega)]
        rw [hr2 x, hi1, hD]
        by_cases e1 : t.toNat + 8 * (i.toNat + 1) ≤ x ∧ x < t.toNat + 8 * c.toNat
        · rw [iteT e1, iteT (by omega), hO _ (by omega)]
        · rw [iteF e1, hr1]
          by_cases e2 : t.toNat + 8 * i.toNat ≤ x ∧ x < t.toNat + 8 * i.toNat + 8
          · rw [iteT (by omega), iteT (by omega)]
            have q1 : (x - t.toNat) / 8 = i.toNat := by omega
            have q2 : x - (t.toNat + 8 * i.toNat) = (x - t.toNat) % 8 := by omega
            rw [q1, q2, UInt64.ofNat_toNat]
          · rw [iteF (by omega), iteF (by omega)]

theorem pBack_ok (t c : Word) (n : Nat) : ∀ (m m' : Mem) (i z : Word), i.toNat ≤ c.toNat →
    1 + 8 * c.toNat ≤ (m.arr64 DECL).size → (m.arr64 DECL).size < 2 ^ 64 →
    pBackW n m t c i = some (z, m') →
    MemFrame [DECL] [] m m' ∧ ∀ x : Nat, (m'.arr64 DECL)[x]? =
      if 1 + 8 * i.toNat ≤ x ∧ x < 1 + 8 * c.toNat then
        some (rdW (m.arr64 IW) (t + 8 * UInt64.ofNat ((x - 1) / 8) + UInt64.ofNat ((x - 1) % 8)))
      else (m.arr64 DECL)[x]? := by
  induction n with
  | zero => intro m m' i z _ _ _ h; simp [pBackW.eq_1] at h
  | succ n ih =>
    intro m m' i z hi hb hs h
    by_cases hci : c ≤ i
    · rw [pBackW.arm1 n m t c i hci] at h
      cases h
      rw [word_le] at hci
      exact ⟨MemFrame.refl _ _ _, fun x => by rw [iteF (by omega)]⟩
    · rw [pBackW.arm2 n m t c i hci] at h
      rw [word_le] at hci
      have hi1 := toNat_succ i (by omega)
      cases hrc : pBackRecW n m t i 0 with
      | none => rw [hrc] at h; simp [pBackW.k_prep_back_rec] at h
      | some p =>
        obtain ⟨z₁, m₁⟩ := p
        rw [hrc, pBackW.k_prep_back_rec.arm1] at h
        obtain ⟨hf1, hr1⟩ := pBackRec_ok t i n m m₁ 0 z₁ (by decide) (by omega) hs hrc
        have h0 : (0 : Word).toNat = 0 := rfl
        rw [h0] at hr1
        have hs1 : (m₁.arr64 DECL).size = (m.arr64 DECL).size := hf1.2.2.1 DECL
        obtain ⟨hf2, hr2⟩ := ih m₁ m' (i + 1) z (by omega) (by omega) (by omega) h
        refine ⟨hf1.trans hf2, fun x => ?_⟩
        have hI : m₁.arr64 IW = m.arr64 IW := hf1.1 IW (by decide) (by decide)
        rw [hr2 x, hi1, hI]
        by_cases e1 : 1 + 8 * (i.toNat + 1) ≤ x ∧ x < 1 + 8 * c.toNat
        · rw [iteT e1, iteT (by omega)]
        · rw [iteF e1, hr1]
          by_cases e2 : 1 + 8 * i.toNat ≤ x ∧ x < 1 + 8 * i.toNat + 8
          · rw [iteT (by omega), iteT (by omega)]
            have q1 : (x - 1) / 8 = i.toNat := by omega
            have q2 : x - (1 + 8 * i.toNat) = (x - 1) % 8 := by omega
            rw [q1, q2, UInt64.ofNat_toNat]
          · rw [iteF (by omega), iteF (by omega)]

/-- **The rewrite**: after `prep_copy` and `prep_back`, the eight words of record `i < c` are
those of record `ord[i]` before; nothing else but `IW[t ‥ t + 8 c)` and `DECL[1 ‥ 1 + 8 c)`
changes. -/
theorem pCopyBack_ok (fuel₁ fuel₂ : Nat) (m m₁ m₂ : Mem) (ord c t z₁ z₂ : Word)
    (hrec : ∀ i < c.toNat, (rdW (m.arr64 IW) (ord + UInt64.ofNat i)).toNat < 2 ^ 59)
    (hc : 1 + 8 * c.toNat ≤ (m.arr64 DECL).size)
    (hord : ord.toNat + c.toNat ≤ t.toNat) (ht : t.toNat + 8 * c.toNat ≤ (m.arr64 IW).size)
    (hsz : (m.arr64 IW).size < 2 ^ 64) (hDsz : (m.arr64 DECL).size < 2 ^ 64)
    (h₁ : pCopyW fuel₁ m ord c t 0 = some (z₁, m₁)) (h₂ : pBackW fuel₂ m₁ t c 0 = some (z₂, m₂)) :
    (∀ i < c.toNat, ∀ k < 8,
      dw (m₂.arr64 DECL) i k = dw (m.arr64 DECL) (rdW (m.arr64 IW) (ord + UInt64.ofNat i)).toNat k) ∧
    MemFrame [IW, DECL] [] m m₂ ∧
    (m₂.arr64 DECL)[0]? = (m.arr64 DECL)[0]? ∧
    (∀ x : Nat, (x < 1 ∨ 1 + 8 * c.toNat ≤ x) → (m₂.arr64 DECL)[x]? = (m.arr64 DECL)[x]?) ∧
    ∀ x : Nat, (x < t.toNat ∨ t.toNat + 8 * c.toNat ≤ x) → (m₂.arr64 IW)[x]? = (m.arr64 IW)[x]? := by
  have h0 : (0 : Word).toNat = 0 := rfl
  obtain ⟨hf1, hr1⟩ := pCopy_ok ord c t fuel₁ m m₁ 0 z₁ (by omega) hord ht hsz h₁
  have hD1 : m₁.arr64 DECL = m.arr64 DECL := hf1.1 DECL (by decide) (by decide)
  obtain ⟨hf2, hr2⟩ := pBack_ok t c fuel₂ m₁ m₂ 0 z₂ (by omega) (by rw [hD1]; omega)
    (by rw [hD1]; omega) h₂
  have hI2 : m₂.arr64 IW = m₁.arr64 IW := hf2.1 IW (by decide) (by decide)
  rw [h0] at hr1 hr2
  have hD : ∀ x, (x < 1 ∨ 1 + 8 * c.toNat ≤ x) → (m₂.arr64 DECL)[x]? = (m.arr64 DECL)[x]? := by
    intro x hx; rw [hr2 x, iteF (by omega), hD1]
  refine ⟨fun i hi k hk => ?_,
    (hf1.mono (by simp) (by simp)).trans (hf2.mono (by simp) (by simp)),
    hD 0 (by omega), hD, fun x hx => by rw [hI2, hr1 x, iteF (by omega)]⟩
  have hd : dw (m₂.arr64 DECL) i k = (m₂.arr64 DECL)[1 + 8 * i + k]?.getD 0 := rfl
  rw [hd, hr2, iteT (by omega)]
  have q1 : (1 + 8 * i + k - 1) / 8 = i := by omega
  have q2 : (1 + 8 * i + k - 1) % 8 = k := by omega
  simp only [q1, q2, Option.getD_some]
  have ha : (t + 8 * UInt64.ofNat i + UInt64.ofNat k).toNat = t.toNat + 8 * i + k := by
    have hi' : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
    have hk' : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
    rw [pc_toNat3 _ _ _ (by omega), hi', hk']
  rw [rdW, ha, hr1, iteT (by omega)]
  have q3 : (t.toNat + 8 * i + k - t.toNat) / 8 = i := by omega
  have q4 : (t.toNat + 8 * i + k - t.toNat) % 8 = k := by omega
  simp only [q3, q4, Option.getD_some]
  exact dw_rdW _ _ k (hrec i hi) hk


end L.Checker
