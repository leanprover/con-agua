import ConAgua.Checker.PrepCopyRef

/-!
# `prelude_join` (lane `front4`)

`DECL` := the prelude's records (`PDECL`, `np` of them), then the stream's (`DECL`'s `ns`): the
stream's records shifted up by `np` (the last first), `PDECL`'s copied below them, the count
`np + ns`.
-/

open ConRon.Arena ConRon.Arena.Frontend
open L.Arena L.Ind L.Front L.Front.Ind

namespace L.Checker

/-! ## The loops, on memory -/

theorem pj_sub1 (k : Word) (h : 1 ≤ k.toNat) : (k - 1).toNat = k.toNat - 1 := by
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; exact h)]; rfl

theorem pj_add (a b : Word) (h : a.toNat + b.toNat < 2 ^ 64) : (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt h]

theorem pShiftRec_ok (np k : Word) (n : Nat) : ∀ (m m' : Mem) (w z : Word), w.toNat ≤ 8 →
    1 ≤ np.toNat → 1 ≤ k.toNat → np.toNat + k.toNat < 2 ^ 60 →
    1 + 8 * (np.toNat + k.toNat) ≤ (m.arr64 DECL).size →
    pShiftRecW n m np k w = some (z, m') →
    MemFrame [DECL] [] m m' ∧ ∀ x : Nat, (m'.arr64 DECL)[x]? =
      if 1 + 8 * (np.toNat + k.toNat - 1) + w.toNat ≤ x ∧ x < 1 + 8 * (np.toNat + k.toNat) then
        some ((m.arr64 DECL)[x - 8 * np.toNat]?.getD 0)
      else (m.arr64 DECL)[x]? := by
  induction n with
  | zero => intro m m' w z _ _ _ _ _ h; simp [pShiftRecW.eq_1] at h
  | succ n ih =>
    intro m m' w z hw hnp hk hb hs h
    by_cases h8 : 8 ≤ w
    · rw [pShiftRecW.arm1 n m np k w h8] at h
      cases h
      rw [word_le] at h8
      have h8' : (8 : Word).toNat = 8 := rfl
      exact ⟨MemFrame.refl _ _ _, fun x => by rw [iteF (by omega)]⟩
    · rw [pShiftRecW.arm2 n m np k w h8] at h
      rw [word_le] at h8
      have h8' : (8 : Word).toNat = 8 := rfl
      have h1' : (1 : Word).toNat = 1 := rfl
      have hw1 := toNat_succ w (by omega)
      have hs1 := size_set64 m DECL DECL (1 + 8 * (np + k - 1) + w)
        (rdW (m.arr64 DECL) (1 + 8 * (k - 1) + w))
      obtain ⟨hf, hr⟩ := ih _ _ (w + 1) z (by omega) hnp hk hb (by rw [hs1]; omega) h
      refine ⟨(MemFrame.set64 m DECL (by decide) _ _).trans hf, fun x => ?_⟩
      have hnk : (np + k - 1).toNat = np.toNat + k.toNat - 1 := by
        rw [pj_sub1 _ (by rw [pj_add _ _ (by omega)]; omega), pj_add _ _ (by omega)]
      have hk1 : (k - 1).toNat = k.toNat - 1 := pj_sub1 _ hk
      have hA : (1 + 8 * (np + k - 1) + w).toNat = 1 + 8 * (np.toNat + k.toNat - 1) + w.toNat := by
        rw [pc_toNat3 _ _ _ (by omega), hnk, h1']
      have hB : (1 + 8 * (k - 1) + w).toNat = 1 + 8 * (k.toNat - 1) + w.toNat := by
        rw [pc_toNat3 _ _ _ (by omega), hk1, h1']
      rw [hr x, hw1, pc_get_set64, pc_get_set64, hA]
      by_cases e : 1 + 8 * (np.toNat + k.toNat - 1) + w.toNat = x
      · subst e
        rw [iteF (by omega), iteT ⟨rfl, rfl, by omega⟩, iteT (by omega), rdW, hB]
        congr 3; omega
      · simp only [e, false_and, and_false, ite_false]
        by_cases h1 : 1 + 8 * (np.toNat + k.toNat - 1) + (w.toNat + 1) ≤ x ∧
            x < 1 + 8 * (np.toNat + k.toNat)
        · have e' : ¬ 1 + 8 * (np.toNat + k.toNat - 1) + w.toNat = x - 8 * np.toNat := by omega
          simp only [e', false_and, and_false, ite_false]
          rw [iteT h1, iteT (by omega)]
        · rw [iteF h1, iteF (by omega)]

theorem pShift_ok (np : Word) (n : Nat) : ∀ (m m' : Mem) (k z : Word),
    1 ≤ np.toNat → np.toNat + k.toNat < 2 ^ 60 →
    1 + 8 * (np.toNat + k.toNat) ≤ (m.arr64 DECL).size →
    pShiftW n m np k = some (z, m') →
    MemFrame [DECL] [] m m' ∧ ∀ x : Nat, (m'.arr64 DECL)[x]? =
      if 1 + 8 * np.toNat ≤ x ∧ x < 1 + 8 * (np.toNat + k.toNat) then
        some ((m.arr64 DECL)[x - 8 * np.toNat]?.getD 0)
      else (m.arr64 DECL)[x]? := by
  induction n with
  | zero => intro m m' k z _ _ _ h; simp [pShiftW.eq_1] at h
  | succ n ih =>
    intro m m' k z hnp hb hs h
    by_cases hk0 : k = 0
    · rw [pShiftW.arm1 n m np k hk0] at h
      cases h
      subst hk0
      have h0 : (0 : Word).toNat = 0 := rfl
      exact ⟨MemFrame.refl _ _ _, fun x => by rw [iteF (by omega)]⟩
    · rw [pShiftW.arm2 n m np k hk0] at h
      have hk : 1 ≤ k.toNat := by
        rcases Nat.eq_zero_or_pos k.toNat with e | e
        · exact absurd (UInt64.toNat_inj.mp (by rw [e]; rfl)) hk0
        · exact e
      cases hrc : pShiftRecW n m np k 0 with
      | none => rw [hrc] at h; simp [pShiftW.k1] at h
      | some p =>
        obtain ⟨z₁, m₁⟩ := p
        rw [hrc, pShiftW.k1.arm1] at h
        obtain ⟨hf1, hr1⟩ := pShiftRec_ok np k n m m₁ 0 z₁ (by decide) hnp hk hb hs hrc
        have h0 : (0 : Word).toNat = 0 := rfl
        rw [h0] at hr1
        have hs1 : (m₁.arr64 DECL).size = (m.arr64 DECL).size := hf1.2.2.1 DECL
        have hk1 : (k - 1).toNat = k.toNat - 1 := pj_sub1 _ hk
        obtain ⟨hf2, hr2⟩ := ih m₁ m' (k - 1) z hnp (by omega) (by omega) h
        refine ⟨hf1.trans hf2, fun x => ?_⟩
        rw [hr2 x, hk1]
        by_cases e1 : 1 + 8 * np.toNat ≤ x ∧ x < 1 + 8 * (np.toNat + (k.toNat - 1))
        · rw [iteT e1, iteT (by omega), hr1, iteF (by omega)]
        · rw [iteF e1, hr1]
          by_cases e2 : 1 + 8 * (np.toNat + k.toNat - 1) ≤ x ∧ x < 1 + 8 * (np.toNat + k.toNat)
          · rw [iteT (by omega), iteT (by omega)]
          · rw [iteF (by omega), iteF (by omega)]

theorem pJoinRec_ok (i : Word) (n : Nat) : ∀ (m m' : Mem) (w z : Word), w.toNat ≤ 8 →
    i.toNat < 2 ^ 59 → 1 + 8 * i.toNat + 8 ≤ (m.arr64 DECL).size →
    pJoinRecW n m i w = some (z, m') →
    MemFrame [DECL] [] m m' ∧ ∀ x : Nat, (m'.arr64 DECL)[x]? =
      if 1 + 8 * i.toNat + w.toNat ≤ x ∧ x < 1 + 8 * i.toNat + 8 then
        some ((m.arr64 PDECL)[x]?.getD 0)
      else (m.arr64 DECL)[x]? := by
  induction n with
  | zero => intro m m' w z _ _ _ h; simp [pJoinRecW.eq_1] at h
  | succ n ih =>
    intro m m' w z hw hi hs h
    by_cases h8 : 8 ≤ w
    · rw [pJoinRecW.arm1 n m i w h8] at h
      cases h
      rw [word_le] at h8
      have h8' : (8 : Word).toNat = 8 := rfl
      exact ⟨MemFrame.refl _ _ _, fun x => by rw [iteF (by omega)]⟩
    · rw [pJoinRecW.arm2 n m i w h8] at h
      rw [word_le] at h8
      have h8' : (8 : Word).toNat = 8 := rfl
      have h1' : (1 : Word).toNat = 1 := rfl
      have hw1 := toNat_succ w (by omega)
      have hs1 := size_set64 m DECL DECL (1 + 8 * i + w) (rdW (m.arr64 PDECL) (1 + 8 * i + w))
      obtain ⟨hf, hr⟩ := ih _ _ (w + 1) z (by omega) hi (by rw [hs1]; omega) h
      refine ⟨(MemFrame.set64 m DECL (by decide) _ _).trans hf, fun x => ?_⟩
      have hP : ((m.set64 DECL (1 + 8 * i + w) (rdW (m.arr64 PDECL) (1 + 8 * i + w))).arr64 PDECL) =
          m.arr64 PDECL := Mem.arr64_set64_ne _ _ _ _ _ (by decide)
      have hA : (1 + 8 * i + w).toNat = 1 + 8 * i.toNat + w.toNat := by
        rw [pc_toNat3 _ _ _ (by omega), h1']
      rw [hr x, hw1, hP, pc_get_set64, hA]
      by_cases e : 1 + 8 * i.toNat + w.toNat = x
      · subst e
        rw [iteF (by omega), iteT ⟨rfl, rfl, by omega⟩, iteT (by omega), rdW, hA]
      · simp only [e, false_and, and_false, ite_false]
        by_cases h1 : 1 + 8 * i.toNat + (w.toNat + 1) ≤ x ∧ x < 1 + 8 * i.toNat + 8
        · rw [iteT h1, iteT (by omega)]
        · rw [iteF h1, iteF (by omega)]

theorem pJoin_ok (np : Word) (n : Nat) : ∀ (m m' : Mem) (i z : Word), i.toNat ≤ np.toNat →
    np.toNat < 2 ^ 59 → 1 + 8 * np.toNat ≤ (m.arr64 DECL).size →
    pJoinW n m np i = some (z, m') →
    MemFrame [DECL] [] m m' ∧ ∀ x : Nat, (m'.arr64 DECL)[x]? =
      if 1 + 8 * i.toNat ≤ x ∧ x < 1 + 8 * np.toNat then
        some ((m.arr64 PDECL)[x]?.getD 0)
      else (m.arr64 DECL)[x]? := by
  induction n with
  | zero => intro m m' i z _ _ _ h; simp [pJoinW.eq_1] at h
  | succ n ih =>
    intro m m' i z hi hnp hs h
    by_cases hci : np ≤ i
    · rw [pJoinW.arm1 n m np i hci] at h
      cases h
      rw [word_le] at hci
      exact ⟨MemFrame.refl _ _ _, fun x => by rw [iteF (by omega)]⟩
    · rw [pJoinW.arm2 n m np i hci] at h
      rw [word_le] at hci
      have hi1 := toNat_succ i (by omega)
      cases hrc : pJoinRecW n m i 0 with
      | none => rw [hrc] at h; simp [pJoinW.k1] at h
      | some p =>
        obtain ⟨z₁, m₁⟩ := p
        rw [hrc, pJoinW.k1.arm1] at h
        obtain ⟨hf1, hr1⟩ := pJoinRec_ok i n m m₁ 0 z₁ (by decide) (by omega) (by omega) hrc
        have h0 : (0 : Word).toNat = 0 := rfl
        rw [h0] at hr1
        have hs1 : (m₁.arr64 DECL).size = (m.arr64 DECL).size := hf1.2.2.1 DECL
        obtain ⟨hf2, hr2⟩ := ih m₁ m' (i + 1) z (by omega) hnp (by omega) h
        refine ⟨hf1.trans hf2, fun x => ?_⟩
        have hP : m₁.arr64 PDECL = m.arr64 PDECL := hf1.1 PDECL (by decide) (by decide)
        rw [hr2 x, hi1, hP]
        by_cases e1 : 1 + 8 * (i.toNat + 1) ≤ x ∧ x < 1 + 8 * np.toNat
        · rw [iteT e1, iteT (by omega)]
        · rw [iteF e1, hr1]
          by_cases e2 : 1 + 8 * i.toNat ≤ x ∧ x < 1 + 8 * i.toNat + 8
          · rw [iteT (by omega), iteT (by omega)]
          · rw [iteF (by omega), iteF (by omega)]


/-- **`prelude_join`**: returns `np = PDECL[0]`; record `r < np` of `DECL` after is record `r` of
`PDECL`, record `np + r` (`r < ns`) is record `r` of `DECL` before; `DECL[0] = np + ns`; only
`DECL` changes, and it keeps its size. -/
theorem pPJoin_ok (n : Nat) (m m' : Mem) (np : Word) (h : pPJoinW n m = some (np, m')) :
    np = rdW (m.arr64 PDECL) 0 ∧ np.toNat < 2 ^ 59 ∧ (rdW (m.arr64 DECL) 0).toNat < 2 ^ 59 ∧
    1 + 8 * (np.toNat + (rdW (m.arr64 DECL) 0).toNat) ≤ (m.arr64 DECL).size ∧
    (∀ r < np.toNat, ∀ k < 8, dw (m'.arr64 DECL) r k = dw (m.arr64 PDECL) r k) ∧
    (∀ r < (rdW (m.arr64 DECL) 0).toNat, ∀ k < 8,
      dw (m'.arr64 DECL) (np.toNat + r) k = dw (m.arr64 DECL) r k) ∧
    (rdW (m'.arr64 DECL) 0).toNat = np.toNat + (rdW (m.arr64 DECL) 0).toNat ∧
    MemFrame [DECL] [] m m' := by
  cases n with
  | zero => simp [pPJoinW] at h
  | succ n =>
  have c59 : (576460752303423488 : Word).toNat = 2 ^ 59 := rfl
  have h0 : (0 : Word).toNat = 0 := rfl
  have h1' : (1 : Word).toNat = 1 := rfl
  have h8' : (8 : Word).toNat = 8 := rfl
  by_cases g1 : 576460752303423488 ≤ rdW (m.arr64 PDECL) 0
  · rw [pPJoinW] at h; simp only [g1, ite_true] at h; cases h
  by_cases g2 : 576460752303423488 ≤ rdW (m.arr64 DECL) 0
  · rw [pPJoinW] at h; simp only [g1, g2, ite_true, ite_false] at h; cases h
  by_cases g3 : m.len64 DECL < 1 + 8 * (rdW (m.arr64 PDECL) 0 + rdW (m.arr64 DECL) 0)
  · rw [pPJoinW] at h; simp only [g1, g2, g3, ite_true, ite_false] at h; cases h
  have b1 : (rdW (m.arr64 PDECL) 0).toNat < 2 ^ 59 := by rw [word_le, c59] at g1; omega
  have b2 : (rdW (m.arr64 DECL) 0).toNat < 2 ^ 59 := by rw [word_le, c59] at g2; omega
  have b3 : 1 + 8 * ((rdW (m.arr64 PDECL) 0).toNat + (rdW (m.arr64 DECL) 0).toNat) ≤
      (m.arr64 DECL).size := by
    rw [UInt64.lt_iff_toNat_lt, len64_eq, UInt64.toNat_ofNat', UInt64.toNat_add, UInt64.toNat_mul,
      UInt64.toNat_add, h1', h8'] at g3
    have := Nat.mod_le (m.arr64 DECL).size (2 ^ 64)
    simp only [Nat.reducePow] at g3 this ⊢
    omega
  -- after the (optional) shift
  have key : ∃ m₁, MemFrame [DECL] [] m m₁ ∧ m₁.arr64 PDECL = m.arr64 PDECL ∧
      (∀ x, 1 + 8 * (rdW (m.arr64 PDECL) 0).toNat ≤ x →
        x < 1 + 8 * ((rdW (m.arr64 PDECL) 0).toNat + (rdW (m.arr64 DECL) 0).toNat) →
        (m₁.arr64 DECL)[x]? = some ((m.arr64 DECL)[x - 8 * (rdW (m.arr64 PDECL) 0).toNat]?.getD 0)) ∧
      pPJoinW.k2 n (rdW (m.arr64 PDECL) 0) (rdW (m.arr64 DECL) 0) m₁ = some (np, m') := by
    by_cases g4 : rdW (m.arr64 PDECL) 0 ≠ 0
    · rw [pPJoinW.arm1 n m g1 g2 g3 g4] at h
      have g4' : 1 ≤ (rdW (m.arr64 PDECL) 0).toNat := by
        rcases Nat.eq_zero_or_pos (rdW (m.arr64 PDECL) 0).toNat with e | e
        · exact absurd (UInt64.toNat_inj.mp (by rw [e]; rfl)) g4
        · exact e
      cases hs : pShiftW n m (rdW (m.arr64 PDECL) 0) (rdW (m.arr64 DECL) 0) with
      | none => rw [hs] at h; simp [pPJoinW.k3] at h
      | some p =>
        obtain ⟨z₁, m₁⟩ := p
        rw [hs, pPJoinW.k3.arm1] at h
        obtain ⟨hf, hr⟩ := pShift_ok _ n m m₁ _ z₁ g4' (by omega) b3 hs
        refine ⟨m₁, hf, hf.1 PDECL (by decide) (by decide), fun x hx1 hx2 => ?_, h⟩
        rw [hr x, iteT ⟨hx1, hx2⟩]
    · rw [pPJoinW.arm2 n m g1 g2 g3 g4] at h
      have g4' : (rdW (m.arr64 PDECL) 0).toNat = 0 := by
        have : rdW (m.arr64 PDECL) 0 = 0 := by simpa using g4
        rw [this]; rfl
      refine ⟨m, MemFrame.refl _ _ _, rfl, fun x hx1 hx2 => ?_, h⟩
      rw [g4', Nat.mul_zero, Nat.sub_zero]
      rw [Array.getElem?_eq_getElem (by omega)]; rfl
  obtain ⟨m₁, hf1, hP1, hr1, h⟩ := key
  have hs1 : (m₁.arr64 DECL).size = (m.arr64 DECL).size := hf1.2.2.1 DECL
  rw [pPJoinW.k2.arm1] at h
  cases hj : pJoinW n m₁ (rdW (m.arr64 PDECL) 0) 0 with
  | none => rw [hj] at h; simp [pPJoinW.k1] at h
  | some p =>
  obtain ⟨z₂, m₂⟩ := p
  rw [hj, pPJoinW.k1.arm1] at h
  cases h
  obtain ⟨hf2, hr2⟩ := pJoin_ok _ n m₁ m₂ 0 z₂ (by rw [h0]; omega) b1 (by omega) hj
  rw [h0, hP1] at hr2
  have hs2 : (m₂.arr64 DECL).size = (m.arr64 DECL).size := (hf2.2.2.1 DECL).trans hs1
  have hD : ∀ x, x ≠ 0 → ((m₂.set64 DECL 0 (rdW (m.arr64 PDECL) 0 + rdW (m.arr64 DECL) 0)).arr64 DECL)[x]? =
      (m₂.arr64 DECL)[x]? := by
    intro x hx; rw [pc_get_set64, h0, iteF (by omega)]
  refine ⟨rfl, b1, b2, b3, fun r hr k hk => ?_, fun r hr k hk => ?_, ?_,
    (hf1.trans hf2).trans (MemFrame.set64 _ DECL (by decide) _ _)⟩
  · simp only [dw]; rw [hD _ (by omega), hr2, iteT (by omega), Option.getD_some]
  · simp only [dw]
    rw [hD _ (by omega), hr2, iteF (by omega), hr1 _ (by omega) (by omega)]
    simp only [Option.getD_some]; congr 2; omega
  · rw [rdW, h0, pc_get_set64, h0, iteT ⟨rfl, rfl, by omega⟩, Option.getD_some]
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]

end L.Checker
