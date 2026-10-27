import ConAgua.Front.ApplyDeclRefine
import ConAgua.Front.Line
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The frontend's records, word by word, I: what one line writes to `DECL`/`DLP` (lane `pipeline`)

The checker's later stages read the records of `DECL` with two facts the frontend's refinement
(`StateDR`) does not keep: a one-constant record's handle words `1`, `4`, `5` are below `2 ^ 32`,
an inductive record's block offset (word `2`) and pointer words are nonzero (`L.Checker.RecOK`).
This file and the next two show what one applied line does to `DECL` and `DLP` (`DGrow`): the old
records' words and the pool below its old top stay, and a new record (at most one) has such words.
A name, level or expression line leaves both arrays alone (`DK`, `lineRecW_dk`, `applyExprW_dk`); a
declaration line appends one record of table handles (`applyDeclW_grow`).
-/

open L.Arena
open ConRon.Arena ConRon.Arena.Frontend

namespace L.Front

/-- The number of records of `DECL` (its word `0`). -/
def dcnt (m : Mem) : Nat := ((m.arr64 DECL)[0]?.getD 0).toNat

/-- The top of `DLP` (its word `0`). -/
def dtop (m : Mem) : Nat := ((m.arr64 DLP)[0]?.getD 0).toNat

/-- A record as a line writes it: a one-constant record's handle words are below `2 ^ 32`, an
inductive record's block offset is nonzero. -/
def NewOK (D : Array Word) (x : Nat) : Prop :=
  (dw D x 0 ≠ 6 → (dw D x 1).toNat < 2 ^ 32 ∧ (dw D x 4).toNat < 2 ^ 32 ∧ (dw D x 5).toNat < 2 ^ 32) ∧
  (dw D x 0 = 6 → dw D x 2 ≠ 0)

/-- **What a line does to the records**: the words of the old records and of the pool up to its
old top stay, the new records are `NewOK`. -/
structure DGrow (m m' : Mem) : Prop where
  decl : ∀ j, 0 < j → j < 1 + 8 * dcnt m → (m'.arr64 DECL)[j]? = (m.arr64 DECL)[j]?
  dlp : ∀ j, 0 < j → j ≤ dtop m → (m'.arr64 DLP)[j]? = (m.arr64 DLP)[j]?
  new : ∀ x, dcnt m ≤ x → x < dcnt m' → NewOK (m'.arr64 DECL) x

/-- `DECL` and `DLP` unchanged. -/
def DK (m m' : Mem) : Prop := m'.arr64 DECL = m.arr64 DECL ∧ m'.arr64 DLP = m.arr64 DLP

theorem DK.refl (m : Mem) : DK m m := ⟨rfl, rfl⟩

theorem DK.trans {m₁ m₂ m₃ : Mem} (h₁ : DK m₁ m₂) (h₂ : DK m₂ m₃) : DK m₁ m₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩

theorem DK.grow {m m' : Mem} (h : DK m m') : DGrow m m' :=
  ⟨fun j _ _ => by rw [h.1], fun j _ _ => by rw [h.2],
    fun x h1 h2 => by simp only [dcnt, h.1] at h1 h2; omega⟩

theorem DK.ofFrame {A : List ArrId} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hd : DECL ∉ A := by tapart) (hq : DLP ∉ A := by tapart) : DK m m' :=
  ⟨hf.1 DECL hd (by decide), hf.1 DLP hq (by decide)⟩

theorem DK.set64 (m : Mem) (b : ArrId) (hd : b ≠ DECL) (hq : b ≠ DLP) (i v : Word) :
    DK m (m.set64 b i v) :=
  ⟨Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm hd), Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm hq)⟩

theorem DK.tset64 (m : Mem) (t i v : Word) : DK m (m.set64 (tierA 0 t) i v) :=
  ⟨arr64_set64_tier_ne _ _ _ _ _ (by decide), arr64_set64_tier_ne _ _ _ _ _ (by decide)⟩

theorem DK.ofAbove {m m' : Mem} (h : Above64 m m') : DK m m' :=
  DK.ofFrame h (not_low_tier _ (by simp [DECL])) (not_low_tier _ (by simp [DLP]))

theorem DK.putK {b : ArrId} (hb : TblIx b) {i : Word} {x : Option (Word × Mem)} {m m' : Mem}
    (hx : ∀ w m₁, x = some (w, m₁) → DK m m₁) (h : putK b i x = some m') : DK m m' := by
  obtain ⟨w, m₁, h1, -, hp⟩ := putK_eq h
  refine (hx w m₁ h1).trans (DK.ofFrame (tblPutW_frame hb hp) ?_ ?_) <;>
    rcases hb with rfl | rfl | rfl <;> decide

section loops
variable (b : Array UInt8)

theorem wrs_dk : ∀ (m : Mem) (t q c : Word) (xs : List Word), DK m (L.Front.Unescape.wrs m t q c xs)
  | m, _, _, _, [] => DK.refl m
  | m, t, q, c, x :: xs => (DK.tset64 m t (q - c) x).trans (wrs_dk _ t (q + 1) c xs)

theorem u8PutW_dk {m m' : Mem} {top k cp k' : Word}
    (h : L.Front.Unescape.u8PutW m top k cp = some (k', m')) : DK m m' := by
  unfold L.Front.Unescape.u8PutW at h
  repeat' split at h
  all_goals (cases h; try exact wrs_dk _ _ _ _ _)

theorem escLoopW_dk (top e : Word) : ∀ (m : Mem) (j k k' : Word) (m' : Mem),
    L.Front.Unescape.escLoopW b m top e j k = some (k', m') → DK m m' := by
  intro m j k
  fun_induction L.Front.Unescape.escLoopW b m top e j k
  all_goals intro k' m' h
  all_goals first
    | (cases h; done)
    | (cases h; exact DK.refl _)
    | (rename_i ih; exact (DK.tset64 _ _ _ _).trans (ih _ _ h))
    | (rename_i hu _ ih; exact (u8PutW_dk hu).trans (ih _ _ h))

end loops

theorem strPutEscW_dk {b : Array UInt8} {m m' : Mem} {vs ve l : Word}
    (h : L.Front.Unescape.strPutEscW b m vs ve = some (l, m')) : DK m m' := by
  unfold L.Front.Unescape.strPutEscW at h
  split at h; cases h
  cases hL : L.Front.Unescape.escLoopW b m m.top ve vs 0 with
  | none => rw [hL] at h; cases h
  | some q =>
    obtain ⟨k, m₁⟩ := q
    rw [hL, L.Front.Unescape.finK_some] at h
    cases h
    exact (escLoopW_dk b _ _ _ _ _ _ _ hL).trans (DK.set64 _ CTL (by decide) (by decide) _ _)

theorem applyNStrW_dk {m m' : Mem} {i pre o l : Word} (h : applyNStrW m i pre o l = some m') :
    DK m m' := by
  unfold applyNStrW at h
  split at h
  · refine DK.putK (.inl rfl) (fun w m₁ hI => ?_) h
    exact DK.ofFrame (consInternM_frame nstrCS_wf hI)
  · cases h

theorem applyNNumW_dk {m m' : Mem} {i pre x : Word} (h : applyNNumW m i pre x = some m') :
    DK m m' := by
  unfold applyNNumW at h
  split at h
  · refine DK.putK (.inl rfl) (fun w m₁ hI => ?_) h
    exact DK.ofFrame (consInternM_frame nnumCS_wf hI)
  · cases h

theorem levelW_dk {m m₁ : Mem} {k a c w : Word} (h : levelW m k a c = some (w, m₁)) : DK m m₁ := by
  unfold levelW at h
  repeat' split at h
  all_goals first
    | exact DK.ofFrame (sinternW_frame _ _ _ _ h)
    | exact DK.ofFrame (minternW_frame _ _ _ _ _ h)
    | exact DK.ofFrame (iminternW_frame _ _ _ _ _ h)
    | (exact DK.ofFrame (consInternM_frame paramCS_wf h))
    | cases h

theorem applyLevelW_dk {m m' : Mem} {i k a c : Word} (h : applyLevelW m i k a c = some m') :
    DK m m' := by
  unfold applyLevelW at h
  split at h
  · exact DK.putK (.inr (.inl rfl)) (fun w m₁ hI => levelW_dk hI) h
  · cases h

/-- **A name or level line leaves `DECL`, `DLP` alone.** -/
theorem lineRecW_dk (b : Array UInt8) (m m' : Mem) (pl idx a c d : Word)
    (h : lineRecW b m pl idx a c d = some m') : DK m m' := by
  unfold lineRecW at h
  split at h; cases h
  split at h
  · cases h; exact DK.refl _
  split at h; cases h
  split at h
  · unfold applyStrW at h
    split at h; cases h
    rcases hP : L.Front.Unescape.strPutEscW b m c d with _ | ⟨l, m₁⟩ <;> simp only [hP, strK, reduceCtorEq] at h
    split at h; cases h
    split at h; cases h
    exact (strPutEscW_dk hP).trans (applyNStrW_dk h)
  split at h; cases h
  split at h
  · exact applyNNumW_dk h
  · exact applyLevelW_dk h

theorem madW_dk : ∀ (m : Mem) (o n w y i : Word), DK m (madW m o n w y i).1 := by
  intro m o n w y i
  fun_induction madW m o n w y i
  all_goals first
    | exact DK.refl _
    | (rename_i ih; exact (DK.tset64 _ _ _ _).trans ih)

theorem decW_dk (b : Array UInt8) (top : Word) : ∀ (m : Mem) (n i d : Word) (m' : Mem) (n' : Word),
    decW b m top n i d = some (m', n') → DK m m' := by
  intro m n i d
  fun_induction decW b m top n i d
  all_goals intro m' n' h
  all_goals first
    | (cases h; done)
    | (cases h; exact DK.refl _)
    | (rename_i ih; exact ((madW_dk _ _ _ _ _ _).trans
        (DK.tset64 _ _ _ _)).trans (ih _ _ h))
    | (rename_i ih; exact (madW_dk _ _ _ _ _ _).trans (ih _ _ h))

theorem natDecW_dk {b : Array UInt8} {m m' : Mem} {c d : Word} {r : List Word}
    (h : natDecW b m c d = some (r, m')) : DK m m' := by
  unfold natDecW at h
  split at h; cases h
  rcases hL : decW b m (rdW (m.arr64 CTL) 0) 0 c d with _ | ⟨m₁, k⟩ <;> simp only [hL, finK, reduceCtorEq] at h
  cases h
  exact (decW_dk b _ _ _ _ _ _ _ hL).trans (DK.set64 _ CTL (by decide) (by decide) _ _)

theorem lsLoopM_dk (b : Array UInt8) (top : Word) : ∀ (m : Mem) (i cnt : Word) (m' : Mem),
    lsLoopM b m top i cnt = some m' → DK m m' := by
  intro m i cnt
  fun_induction lsLoopM b m top i cnt
  all_goals intro m' h
  all_goals first
    | (cases h; done)
    | (cases h; exact DK.set64 _ CTL (by decide) (by decide) _ _)
    | (rename_i ih; exact (DK.tset64 _ _ _ _).trans (ih _ h))
    | (rename_i ih; exact ih _ h)

theorem nodeW_dk {b : Array UInt8} {m m₁ : Mem} {pl a c d w : Word}
    (h : nodeW b m pl a c d = some (w, m₁)) : DK m m₁ := by
  unfold nodeW at h
  repeat' split at h
  all_goals try (cases h; done)
  · exact DK.ofFrame (consInternM_frame bvarCS_wf h)
  · exact DK.ofFrame (sointernW_frame _ _ _ _ h)
  · unfold binW at h
    repeat' split at h
    all_goals try (cases h; done)
    · exact DK.ofAbove (mkAppW_above h)
    · exact DK.ofAbove (mkLamW_above h)
    · exact DK.ofAbove (mkForallW_above h)
  · unfold letW at h
    split at h
    · exact DK.ofAbove (mkLetW_above h)
    · cases h
  · unfold projW at h
    split at h
    · exact DK.ofAbove (mkProjW_above h)
    · cases h
  · unfold constW at h
    split at h
    · cases hP : lsPutW b m c with
      | none => rw [hP, constK_none] at h; cases h
      | some m₂ =>
        rw [hP, constK_some] at h
        have hk2 : DK m m₂ := by
          unfold lsPutW at hP
          split at hP; cases hP
          · exact lsLoopM_dk b _ _ _ _ _ hP
        rcases hL : lsinternW m₂ m.top (lsPutL b c) with _ | ⟨g, m₃⟩ <;> simp only [hL, constK2, reduceCtorEq] at h
        split at h
        · exact (hk2.trans (DK.ofFrame (lsinternW_frame _ _ _ _ _ hL))).trans
            (DK.ofFrame (ceinternW_frame _ _ _ _ _ h))
        · cases h
    · cases h
  · unfold litW at h
    rcases hN : natDecW b m c d with _ | ⟨r, m₂⟩ <;> simp only [hN, litK, reduceCtorEq] at h
    split at h; cases h
    split at h; cases h
    exact (natDecW_dk hN).trans (DK.ofFrame (consInternM_frame litCS_wf h))
  · unfold litStrW at h
    split at h; cases h
    rcases hP : L.Front.Unescape.strPutEscW b m c d with _ | ⟨l, m₂⟩ <;> simp only [hP, litStrK, reduceCtorEq] at h
    split at h; cases h
    split at h; cases h
    exact (strPutEscW_dk hP).trans (DK.ofFrame (consInternM_frame litStrCS_wf h : MemFrame [litSch.ra, tier1 litSch.ra, litSch.sa, tier1 litSch.sa] [litSch.ca, litSch.ca + 1] _ _))

/-- **An expression line leaves `DECL`, `DLP` alone.** -/
theorem applyExprW_dk (b : Array UInt8) (m m' : Mem) (pl idx a c d : Word)
    (h : applyExprW b m pl idx a c d = some m') : DK m m' := by
  unfold applyExprW at h
  split at h
  · exact DK.putK (.inr (.inr rfl)) (fun w m₁ hI => nodeW_dk hI) h
  · cases h

/-- **A declaration line appends one record of table handles.** -/
theorem applyDeclW_grow (b : Array UInt8) (m m' : Mem) (st : StateD) (hD : StateDR m st)
    (pl name lps type value hk hn flag : Word)
    (h : applyDeclW b m pl name lps type value hk hn flag = some m') : DGrow m m' := by
  unfold applyDeclW at h
  rcases hK : declKindW pl hk hn flag with _ | ⟨k, q⟩ <;> simp only [hK, declK0, reduceCtorEq] at h
  have hk5 : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by
    rcases declKindW_some _ _ _ _ _ _ hK with ⟨-, -, h⟩ | ⟨-, -, h, -⟩ | ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, h, -⟩ <;>
      simp [h]
  have hk6 : k ≠ 6 := by rcases hk5 with rfl | rfl | rfl | rfl | rfl <;> decide
  unfold declCvW at h
  have hok : tblOK m NID name = true ∧ tblOK m EID type = true :=
    Classical.byContradiction fun hok => by simp [hok] at h
  simp only [hok, and_self, ↓reduceIte] at h
  have hwn := (hD.names.read _ _ _ _ hok.1).2
  have hwt := (hD.exprs.read _ _ _ _ hok.2).2
  rcases hP : lpPutW b m lps with _ | m₁ <;> simp only [hP, declK1, reduceCtorEq] at h
  have hDR := hD.decls
  unfold lpPutW at hP
  split at hP; cases hP
  have hps := hDR.psize
  have hptop := hDR.ptop
  have hrd : rdW (m.arr64 DLP) 0 = (m.arr64 DLP)[0]?.getD 0 := rfl
  obtain ⟨-, F2, -, F4, -, -, -⟩ := lpLoopM_facts b (rdW (m.arr64 DLP) 0) m (lps + 1) 0 m₁
    hP (by rw [hrd]; simp; omega) hps
  have hm'D : m₁.arr64 DECL = m.arr64 DECL := F2.1 DECL (by decide) (by decide)
  have hE₁ : TblR m₁ EID st.exprs :=
    hD.exprs.frame F2 (.inr (.inr rfl)) (by simp [DLP, idArrs]) (by simp)
  -- the push, with its value word
  have hpush : ∃ v, pushW m₁ k (tblW m NID name) (rdW (m.arr64 DLP) 0) (lsCntN b (lps + 1) 0)
      (tblW m EID type) v q hn = some m' ∧ v.toNat < 2 ^ 32 := by
    split at h
    · split at h
      · rename_i hv
        exact ⟨_, h, (hE₁.read _ _ _ _ hv).2⟩
      · cases h
    · exact ⟨0, h, by decide⟩
  obtain ⟨v, hpu, hv⟩ := hpush
  have hds : (m₁.arr64 DECL).size < 2 ^ 63 := by rw [hm'D]; exact hDR.dsize
  obtain ⟨G1, G2, -, G4, G5, w0, w1, -, -, w4, w5, -, -⟩ :=
    pushW_facts m₁ m' _ _ _ _ _ _ _ _ _ rfl hpu hds
  have hc1 : (rdW (m₁.arr64 DECL) 0 + 1).toNat = (rdW (m₁.arr64 DECL) 0).toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  have hcnt : dcnt m = (rdW (m₁.arr64 DECL) 0).toNat := by rw [hm'D]; rfl
  have hcnt' : dcnt m' = dcnt m + 1 := by
    rw [show dcnt m' = (rdW (m₁.arr64 DECL) 0 + 1).toNat by unfold dcnt; rw [G4]; rfl, hc1, hcnt]
  have hm'P : m'.arr64 DLP = m₁.arr64 DLP := G1.1 DLP (by decide) (by decide)
  refine ⟨fun j h1 h2 => ?_, fun j h1 h2 => ?_, fun x h1 h2 => ?_⟩
  · rw [G5 j h1 (by omega), hm'D]
  · rw [hm'P]; exact F4 j h1 (by simp only [dtop] at h2; rw [hrd]; omega)
  · have hx : x = (rdW (m₁.arr64 DECL) 0).toNat := by omega
    subst hx
    refine ⟨fun _ => ⟨by rw [w1]; exact hwn, by rw [w4]; exact hwt, by rw [w5]; exact hv⟩,
      fun h6 => absurd (w0.symm.trans h6) hk6⟩

end L.Front
