import ConAgua.Arena.IndPosSpec4

/-! # `nestCrest` (lane `indproofs2`, helper `pos`)

The banked `replaceFVars` memo across `nest_canon_crest`: its pieces leave the memo alone
(`RfFr`): `nest_phs`, `inst_pis_with` (a stub), `replace_apps` (its own memo, `RAM`). -/

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem RfFr.of_frame {m m' : Mem} {A : List ArrId} {C : List Word} (hf : MemFrame A C m m') (hA : RFM ∉ A)
    (hC : (208 : Word) ∉ C ∧ (218 : Word) ∉ C ∧ (219 : Word) ∉ C) : RfFr m m' :=
  ⟨A, C, hf, hA, hC.1, hC.2.1, hC.2.2⟩

theorem phsGoW_fr (k : Nat) : ∀ (m m' : Mem) (q n i : Word), phsGoW k m q n i = some m' → RfFr m m' := by
  induction k with
  | zero => intro m m' q n i h; simp [phsGoW] at h
  | succ k ih =>
    intro m m' q n i h
    by_cases hd : n ≤ i
    · rw [phsGoW_done (h := hd)] at h; cases h; exact RfFr.refl _
    rw [phsGoW_step (h := hd)] at h
    cases hpw : pinWordV m 53 with
    | none => rw [hpw] at h; simp [phsK1] at h
    | some z =>
    rw [hpw] at h
    by_cases hz : 4294967296 ≤ z
    · rw [phsK1_big (h := hz)] at h; simp at h
    rw [phsK1_ok (h := hz)] at h
    cases hso : sointernW m z with
    | none => rw [hso] at h; simp [phsK2] at h
    | some p1 =>
    obtain ⟨s, m1⟩ := p1
    rw [hso] at h
    by_cases hs : 4294967296 ≤ s
    · rw [phsK2_big (h := hs)] at h; simp at h
    rw [phsK2_ok (h := hs)] at h
    cases hfv : fvinternW m1 i s with
    | none => rw [hfv] at h; simp [phsK3] at h
    | some p2 =>
    obtain ⟨v, m2⟩ := p2
    rw [hfv] at h
    by_cases hv : 4294967296 ≤ v
    · rw [phsK3_big (h := hv)] at h; simp at h
    rw [phsK3_ok (h := hv)] at h
    exact ((RfFr.of_low ((sointernW_low hso).trans (fvinternW_low hfv))).trans (RfFr.set_iw _ _ _)).trans
      (ih _ _ _ _ _ h)

theorem phsW_fr {k : Nat} {m m' : Mem} {nn : Word} {r : List Word} (h : phsW k m nn = some (r, m')) : RfFr m m' := by
  unfold phsW at h
  cases hal : allocW m nn with
  | none => rw [hal] at h; simp [phsA] at h
  | some pr =>
  obtain ⟨q, m1⟩ := pr
  rw [hal, phsA_some] at h
  cases hg : phsGoW k m1 q nn 0 with
  | none => rw [hg] at h; simp [phsB] at h
  | some m2 =>
  rw [hg, phsB_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact (allocW_fr hal).trans (phsGoW_fr k _ _ _ _ _ hg)

theorem instW_fr (n : Nat) : ∀ (m m' : Mem) (ao al e : Word) (r : List Word), instW n m ao al e = some (r, m') →
    RfFr m m' := by
  induction n with
  | zero => intro m m' ao al e r h; simp [instW] at h
  | succ n ih =>
    intro m m' ao al e r h
    by_cases h0 : al = 0
    · rw [instW_nil (h := h0)] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact RfFr.refl _
    by_cases h6 : e >>> 28 ≠ 6
    · rw [instW_nopi (h := h0) (h2 := h6)] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]; exact RfFr.refl _
    rw [instW_pi (h := h0) (h2 := h6)] at h
    by_cases hv : eViewW m e = []
    · rw [instK1_abort (h := hv)] at h; simp at h
    rw [instK1_ok (h := hv)] at h
    cases hst : stubM "instantiate1_fast" m [CWF, (eViewW m e).tail.tail.headD 0, rdW (m.arr64 IW) ao, 0] with
    | none => rw [hst] at h; simp [instK2] at h
    | some p1 =>
    obtain ⟨rb, m1⟩ := p1
    rw [hst, instK2_some] at h
    cases hi : instW n m1 (ao + 1) (al - 1) (rb.headD 0) with
    | none => rw [hi] at h; simp [instK3] at h
    | some p2 =>
    obtain ⟨r2, m2⟩ := p2
    rw [hi, instK3_some] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact (RfFr.stub (by decide) hst).trans (ih _ _ _ _ _ _ hi)

theorem rpMkW_fr {m m' : Mem} {g a2 x2 c2 y x r : Word} (h : rpMkW m g a2 x2 c2 y x = some (r, m')) : RfFr m m' := by
  unfold rpMkW at h
  split at h
  · exact RfFr.of_low (mkAppW_low h)
  split at h
  · exact RfFr.of_low (mkLamW_low h)
  split at h
  · exact RfFr.of_low (mkForallW_low h)
  split at h
  · exact RfFr.of_low (mkLetW_low h)
  · exact RfFr.of_low (mkProjW_low h)

theorem rpGoW_fr (n : Nat) :
    (∀ (m m' : Mem) (no nl us b nn f h r : Word), rpGoW n m no nl us b nn f h = some (r, m') → RfFr m m') ∧
    (∀ (m m' : Mem) (no nl us b nn f1 h g x y z r : Word),
      rpNodeW n m no nl us b nn f1 h g x y z = some (r, m') → RfFr m m') := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  cases n with
  | zero => exact ⟨fun _ _ _ _ _ _ _ _ _ _ h => by simp [rpGoW] at h,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => by simp [rpNodeW] at h⟩
  | succ j =>
  have ihG : ∀ (m m' : Mem) (no nl us b nn f h r : Word), rpGoW j m no nl us b nn f h = some (r, m') →
      RfFr m m' := (ih j (by omega)).1
  have ahF : ∀ {m m' : Mem} {no nl us b nn e : Word} {rr : List Word},
      ahWf j m no nl us b nn e = some (rr, m') → RfFr m m' := by
    intro m m' no nl us b nn e rr h
    cases j with
    | zero => simp [ahWf] at h
    | succ i => exact RfFr.of_low (ahW_low h)
  refine ⟨?_, ?_⟩
  · intro m m' no nl us b nn f h r hg
    by_cases hf : f = 0
    · rw [rpGoW_abort (hf := hf)] at hg; simp at hg
    rw [rpGoW_view (hf := hf)] at hg
    unfold rpG1 at hg
    split at hg; · simp at hg
    split at hg
    · simp only [Option.some.injEq, Prod.mk.injEq] at hg; rw [← hg.2]; exact RfFr.refl _
    split at hg
    · cases ha : ahWf j m no nl us b nn h with
      | none => rw [ha] at hg; simp [rpH] at hg
      | some pr =>
        obtain ⟨rr, m1⟩ := pr
        rw [ha, rpH_some] at hg
        simp only [Option.some.injEq, Prod.mk.injEq] at hg
        rw [← hg.2]; exact ahF ha
    unfold rpG3 at hg
    split at hg; · simp at hg
    split at hg
    · simp only [Option.some.injEq, Prod.mk.injEq] at hg; rw [← hg.2]; exact RfFr.refl _
    cases hn : rpNodeW j m no nl us b nn (f - 1) h _ _ _ _ with
    | none => rw [hn] at hg; simp [rpG4] at hg
    | some pr =>
      obtain ⟨rn, m1⟩ := pr
      rw [hn, rpG4_some] at hg
      cases hs : msetG raSch m1 h 0 rn with
      | none => rw [hs] at hg; simp [rpG5] at hg
      | some m2 =>
        rw [hs, rpG5_some] at hg
        simp only [Option.some.injEq, Prod.mk.injEq] at hg
        rw [← hg.2]
        cases j with
        | zero => simp [rpNodeW] at hn
        | succ i =>
          exact ((ih (i + 1) (by omega)).2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hn).trans
            (RfFr.of_frame (msetG_frame raSch raSch_wf m1 m2 h 0 rn hs) (by simp [raSch, RFM, RAM])
              (by simp [raSch]))
  · intro m m' no nl us b nn f1 h g x y z r hn
    have bin : ∀ {m m' : Mem} {g x y r : Word},
        rpB1 j no nl us b nn f1 g x y (rpGoW j m no nl us b nn f1 x) = some (r, m') → RfFr m m' := by
      intro m m' g x y r hb
      cases h1 : rpGoW j m no nl us b nn f1 x with
      | none => rw [h1] at hb; simp [rpB1] at hb
      | some p1 =>
        obtain ⟨a2, m1⟩ := p1
        rw [h1, rpB1_some] at hb
        cases h2 : rpGoW j m1 no nl us b nn f1 y with
        | none => rw [h2] at hb; simp [rpB2] at hb
        | some p2 =>
          obtain ⟨x2, m2⟩ := p2
          rw [h2, rpB2_some] at hb
          exact ((ihG _ _ _ _ _ _ _ _ _ _ h1).trans (ihG _ _ _ _ _ _ _ _ _ _ h2)).trans (rpMkW_fr hb)
    unfold rpNodeW at hn
    split at hn
    · cases ha : ahWf j m no nl us b nn h with
      | none => rw [ha] at hn; simp [rpA1] at hn
      | some pr =>
        obtain ⟨rr, m1⟩ := pr
        rw [ha] at hn
        unfold rpA1 at hn
        split at hn
        · simp only [Option.some.injEq, Prod.mk.injEq] at hn; rw [← hn.2]; exact ahF ha
        · exact (ahF ha).trans (bin hn)
    split at hn
    · exact bin hn
    split at hn
    · cases h1 : rpGoW j m no nl us b nn f1 x with
      | none => rw [h1] at hn; simp [rpL1] at hn
      | some p1 =>
        obtain ⟨a2, m1⟩ := p1
        rw [h1, rpL1_some] at hn
        cases h2 : rpGoW j m1 no nl us b nn f1 y with
        | none => rw [h2] at hn; simp [rpL2] at hn
        | some p2 =>
          obtain ⟨x2, m2⟩ := p2
          rw [h2, rpL2_some] at hn
          cases h3 : rpGoW j m2 no nl us b nn f1 z with
          | none => rw [h3] at hn; simp [rpL3] at hn
          | some p3 =>
            obtain ⟨c2, m3⟩ := p3
            rw [h3, rpL3_some] at hn
            exact (((ihG _ _ _ _ _ _ _ _ _ _ h1).trans (ihG _ _ _ _ _ _ _ _ _ _ h2)).trans
              (ihG _ _ _ _ _ _ _ _ _ _ h3)).trans (rpMkW_fr hn)
    · cases h1 : rpGoW j m no nl us b nn f1 z with
      | none => rw [h1] at hn; simp [rpP1] at hn
      | some p1 =>
        obtain ⟨a2, m1⟩ := p1
        rw [h1, rpP1_some] at hn
        exact (ihG _ _ _ _ _ _ _ _ _ _ h1).trans (rpMkW_fr hn)

theorem rpConstW_fr {n : Nat} {m m' : Mem} {no nl us b nn e r : Word}
    (h : rpConstW n m no nl us b nn e = some (r, m')) : RfFr m m' := by
  by_cases h0 : rdW (m.arr64 CTL) raSch.cs + 2 = 0
  · simp [rpConstW, h0] at h
  rw [rpConstW_eq n m no nl us b nn e h0] at h
  cases hg : rpGoW n (mclearG raSch m) no nl us b nn CWF e with
  | none => rw [hg] at h; simp [rpClrK] at h
  | some pr =>
    obtain ⟨r1, m1⟩ := pr
    rw [hg] at h
    by_cases h1 : rdW (m1.arr64 CTL) raSch.cs + 2 = 0
    · simp [rpClrK, h1] at h
    rw [rpClrK_some r1 m1 h1] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact ((RfFr.of_frame (mclearG_frame raSch m) (by simp) (by simp [raSch])).trans
      ((rpGoW_fr n).1 _ _ _ _ _ _ _ _ _ _ hg)).trans (RfFr.of_frame (mclearG_frame raSch m1) (by simp) (by simp [raSch]))

theorem pccW_fr {k : Nat} {m m' : Mem} {no nl us nn cty : Word} {r : List Word}
    (h : pccW k m no nl us nn cty = some (r, m')) : RfFr m m' := by
  unfold pccW at h
  cases hp : phsW k m nn with
  | none => rw [hp] at h; simp [pccA] at h
  | some p1 =>
  obtain ⟨r1, m1⟩ := p1
  rw [hp] at h
  simp only [pccA] at h
  cases hi : instW (k + 1) m1 (r1.headD 0) (r1.tail.headD 0) cty with
  | none => rw [hi] at h; simp [pccB] at h
  | some p2 =>
  obtain ⟨r2, m2⟩ := p2
  rw [hi] at h
  by_cases hz : r2.headD 0 = 0
  · rw [pccB_zero k no nl us nn r2 m2 hz] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]
    exact (phsW_fr hp).trans (instW_fr _ _ _ _ _ _ _ hi)
  rw [pccB_ok k no nl us nn r2 m2 hz] at h
  cases hr : rpConstW k m2 no nl us 0 nn (r2.tail.headD 0) with
  | none => rw [hr] at h; simp [pccC] at h
  | some p3 =>
  obtain ⟨r3, m3⟩ := p3
  rw [hr] at h
  by_cases hb : 4294967296 ≤ r3
  · rw [pccC_big 0 r3 m3 hb] at h; simp at h
  rw [pccC_some 0 r3 m3 hb] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]
  exact ((phsW_fr hp).trans (instW_fr _ _ _ _ _ _ _ hi)).trans (rpConstW_fr hr)

end L.Ind
