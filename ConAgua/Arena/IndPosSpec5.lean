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


/-! ## Memo frames of the pieces (lane `indproofs2`, helper `posmemo`)

`MFr S T` (`IndPos2SpecD`): the writers below leave every per-call memo outside `S` alone; the
banked memo's `RfFr` is a corollary (`RfFr.of_mfr`). -/

theorem RfFr.of_mfr {S : List ArrId} {T : List Word} {m m' : Mem} (h : MFr S T m m') (hS : RFM ∉ S)
    (hT : (208 : Word) ∉ T ∧ (218 : Word) ∉ T ∧ (219 : Word) ∉ T) : RfFr m m' := by
  obtain ⟨A, C, f, a, c⟩ := h
  refine ⟨A, C, f, fun hm => ?_, fun hm => ?_, fun hm => ?_, fun hm => ?_⟩
  · rcases a _ hm with h | h | h
    · simp [RFM] at h
    · simp [RFM] at h
    · exact hS h
  all_goals rcases c _ hm with h | h | h
  all_goals first | (simp at h; done) | skip
  · exact hT.1 h
  · exact hT.2.1 h
  · exact hT.2.2 h

theorem dpMR_mfr {S0 : List ArrId} {T0 : List Word} {m m' : Mem} (hf : MFr S0 T0 m m') (hS : DPM ∉ S0)
    (hT : (206 : Word) ∉ T0) {mp : Std.HashMap EIdx Nat} (h : dpMR m mp) : dpMR m' mp := by
  obtain ⟨A, C, f, hA, hC⟩ := hf.memo DPM 206 (by decide) (by decide) hS hT
  exact memoRG_frame dpSch dpSch_wf bmKey (fun w : Word => w.toNat) A C hA hC m m' f mp h

theorem RfInv.mfr {S : List ArrId} {T : List Word} {m m' : Mem} {M : Std.HashMap (EIdx × Word) EIdx} {G g : Word}
    (h : RfInv m M G g) (hf : MFr S T m m') (hS : RFM ∉ S)
    (hT : (208 : Word) ∉ T ∧ (218 : Word) ∉ T ∧ (219 : Word) ∉ T) : RfInv m' M G g :=
  h.frame (RfFr.of_mfr hf hS hT)

theorem allocW_mfr {m m' : Mem} {k q : Word} (h : allocW m k = some (q, m')) : MFr [] [] m m' := by
  simp only [allocW] at h
  split at h; · simp at h
  split at h; · simp at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact MFr.of_iw (allocMem_frame m k)

theorem posRecW_mfr {m m' : Mem} {ws : List Word} {q : Word} (h : posRecW m ws = some (q, m')) :
    MFr [] [] m m' := by
  simp only [posRecW] at h
  cases hal : allocW m (UInt64.ofNat ws.length) with
  | none => rw [hal] at h; simp at h
  | some pr =>
    obtain ⟨q1, m1⟩ := pr
    rw [hal] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (allocW_mfr hal).trans (MFr.of_iw (wrIW_frame _ _ _))

theorem posmemo_copyW_iw : ∀ (n : Nat) (m m' : Mem) (d s l : Word), copyW n m d s l = some m' →
    MemFrame [IW] [200] m m'
  | 0, _, _, _, _, _, h => by simp [copyW] at h
  | n + 1, m, m', d, s, l, h => by
    by_cases hl : l = 0
    · rw [copyW_nil n m d s l hl] at h; cases h; exact MemFrame.refl _ _ _
    · rw [copyW_step n m d s l hl] at h
      exact (set64IW_frame _ _ _).trans (posmemo_copyW_iw n _ _ _ _ _ h)

theorem snocW_mfr {n : Nat} {m m' : Mem} {o l x : Word} {r : List Word} (h : snocW n m o l x = some (r, m')) :
    MFr [] [] m m' := by
  unfold snocW at h
  split at h; · simp at h
  split at h; · simp at h
  rename_i q m1 hal
  split at h; · simp at h
  rename_i m2 hc
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact ((allocW_mfr hal).trans (MFr.of_iw (posmemo_copyW_iw _ _ _ _ _ _ hc))).trans (MFr.set_iw _ _ _)

theorem appendW_mfr {n : Nat} {m m' : Mem} {o1 l1 o2 l2 : Word} {r : List Word}
    (h : appendW n m o1 l1 o2 l2 = some (r, m')) : MFr [] [] m m' := by
  unfold appendW at h
  split at h; · simp at h
  split at h; · simp at h
  rename_i q m1 hal
  split at h; · simp at h
  rename_i m2 hc
  split at h; · simp at h
  rename_i m3 hc3
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact ((allocW_mfr hal).trans (MFr.of_iw (posmemo_copyW_iw _ _ _ _ _ _ hc))).trans
    (MFr.of_iw (posmemo_copyW_iw _ _ _ _ _ _ hc3))

theorem phsGoW_mfr (k : Nat) : ∀ (m m' : Mem) (q n i : Word), phsGoW k m q n i = some m' → MFr [] [] m m' := by
  induction k with
  | zero => intro m m' q n i h; simp [phsGoW] at h
  | succ k ih =>
    intro m m' q n i h
    by_cases hd : n ≤ i
    · rw [phsGoW_done (h := hd)] at h; cases h; exact MFr.refl _ _ _
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
    exact ((MFr.of_low ((sointernW_low hso).trans (fvinternW_low hfv))).trans (MFr.set_iw _ _ _)).trans
      (ih _ _ _ _ _ h)

theorem phsW_mfr {k : Nat} {m m' : Mem} {nn : Word} {r : List Word} (h : phsW k m nn = some (r, m')) : MFr [] [] m m' := by
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
  exact (allocW_mfr hal).trans (phsGoW_mfr k _ _ _ _ _ hg)

theorem instW_mfr (n : Nat) : ∀ (m m' : Mem) (ao al e : Word) (r : List Word), instW n m ao al e = some (r, m') →
    MFr [] [] m m' := by
  induction n with
  | zero => intro m m' ao al e r h; simp [instW] at h
  | succ n ih =>
    intro m m' ao al e r h
    by_cases h0 : al = 0
    · rw [instW_nil (h := h0)] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact MFr.refl _ _ _
    by_cases h6 : e >>> 28 ≠ 6
    · rw [instW_nopi (h := h0) (h2 := h6)] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]; exact MFr.refl _ _ _
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
    exact (MFr.stub (by decide) hst).trans (ih _ _ _ _ _ _ hi)

theorem rpMkW_mfr {m m' : Mem} {g a2 x2 c2 y x r : Word} (h : rpMkW m g a2 x2 c2 y x = some (r, m')) : MFr [] [] m m' := by
  unfold rpMkW at h
  split at h
  · exact MFr.of_low (mkAppW_low h)
  split at h
  · exact MFr.of_low (mkLamW_low h)
  split at h
  · exact MFr.of_low (mkForallW_low h)
  split at h
  · exact MFr.of_low (mkLetW_low h)
  · exact MFr.of_low (mkProjW_low h)

theorem rpGoW_mfr (n : Nat) :
    (∀ (m m' : Mem) (no nl us b nn f h r : Word), rpGoW n m no nl us b nn f h = some (r, m') → MFr [RAM] [210, 211] m m') ∧
    (∀ (m m' : Mem) (no nl us b nn f1 h g x y z r : Word),
      rpNodeW n m no nl us b nn f1 h g x y z = some (r, m') → MFr [RAM] [210, 211] m m') := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  cases n with
  | zero => exact ⟨fun _ _ _ _ _ _ _ _ _ _ h => by simp [rpGoW] at h,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => by simp [rpNodeW] at h⟩
  | succ j =>
  have ihG : ∀ (m m' : Mem) (no nl us b nn f h r : Word), rpGoW j m no nl us b nn f h = some (r, m') →
      MFr [RAM] [210, 211] m m' := (ih j (by omega)).1
  have ahF : ∀ {m m' : Mem} {no nl us b nn e : Word} {rr : List Word},
      ahWf j m no nl us b nn e = some (rr, m') → MFr [RAM] [210, 211] m m' := by
    intro m m' no nl us b nn e rr h
    cases j with
    | zero => simp [ahWf] at h
    | succ i => exact (MFr.of_low (ahW_low h)).up
  refine ⟨?_, ?_⟩
  · intro m m' no nl us b nn f h r hg
    by_cases hf : f = 0
    · rw [rpGoW_abort (hf := hf)] at hg; simp at hg
    rw [rpGoW_view (hf := hf)] at hg
    unfold rpG1 at hg
    split at hg; · simp at hg
    split at hg
    · simp only [Option.some.injEq, Prod.mk.injEq] at hg; rw [← hg.2]; exact MFr.refl _ _ _
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
    · simp only [Option.some.injEq, Prod.mk.injEq] at hg; rw [← hg.2]; exact MFr.refl _ _ _
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
            ⟨_, _, msetG_frame raSch raSch_wf m1 m2 h 0 rn hs, by simp [raSch, RAM], by simp [raSch]⟩
  · intro m m' no nl us b nn f1 h g x y z r hn
    have bin : ∀ {m m' : Mem} {g x y r : Word},
        rpB1 j no nl us b nn f1 g x y (rpGoW j m no nl us b nn f1 x) = some (r, m') → MFr [RAM] [210, 211] m m' := by
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
          exact ((ihG _ _ _ _ _ _ _ _ _ _ h1).trans (ihG _ _ _ _ _ _ _ _ _ _ h2)).trans (rpMkW_mfr hb).up
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
              (ihG _ _ _ _ _ _ _ _ _ _ h3)).trans (rpMkW_mfr hn).up
    · cases h1 : rpGoW j m no nl us b nn f1 z with
      | none => rw [h1] at hn; simp [rpP1] at hn
      | some p1 =>
        obtain ⟨a2, m1⟩ := p1
        rw [h1, rpP1_some] at hn
        exact (ihG _ _ _ _ _ _ _ _ _ _ h1).trans (rpMkW_mfr hn).up

theorem rpConstW_mfr {n : Nat} {m m' : Mem} {no nl us b nn e r : Word}
    (h : rpConstW n m no nl us b nn e = some (r, m')) : MFr [RAM] [210, 211] m m' := by
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
    exact (MFr.trans ⟨_, _, mclearG_frame raSch m, by simp, by simp [raSch]⟩
      ((rpGoW_mfr n).1 _ _ _ _ _ _ _ _ _ _ hg)).trans ⟨_, _, mclearG_frame raSch m1, by simp, by simp [raSch]⟩

theorem pccW_mfr {k : Nat} {m m' : Mem} {no nl us nn cty : Word} {r : List Word}
    (h : pccW k m no nl us nn cty = some (r, m')) : MFr [RAM] [210, 211] m m' := by
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
    exact ((phsW_mfr hp).trans (instW_mfr _ _ _ _ _ _ _ hi)).up
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
  exact ((phsW_mfr hp).trans (instW_mfr _ _ _ _ _ _ _ hi)).up.trans (rpConstW_mfr hr)


theorem rpConstW_fr {n : Nat} {m m' : Mem} {no nl us b nn e r : Word}
    (h : rpConstW n m no nl us b nn e = some (r, m')) : RfFr m m' :=
  RfFr.of_mfr (rpConstW_mfr h) (by decide) (by decide)

theorem pccW_fr {k : Nat} {m m' : Mem} {no nl us nn cty : Word} {r : List Word}
    (h : pccW k m no nl us nn cty = some (r, m')) : RfFr m m' :=
  RfFr.of_mfr (pccW_mfr h) (by decide) (by decide)

theorem pccW_ok (k : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
    (m m' : Mem) (a : AState) (no nl us nn cty : Word) (names : List NIdx) (r : List Word)
    (h : pccW k m no nl us nn cty = some (r, m')) (hS : StageR dn vis fe m a) (hcty : H cty) (hus : H us)
    (hdec : decHL m no.toNat nl.toNat = some names) (hno : no.toNat + nl.toNat < 2 ^ 64)
    (hit : no.toNat + nl.toNat ≤ iwTop m) (hnn : nn.toNat + names.length < 2 ^ 64)
    (mp0 : Std.HashMap EIdx EIdx) (hM : rpMR m mp0) :
    ∃ x a', (ConRon.Arena.nestCanonCrest names (decI us) nn.toNat (decI cty)).run a = .ok (x, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ decOE m' r x ∧ ∃ mp, rpMR m' mp := by
  unfold pccW at h
  cases hph : phsW k m nn with
  | none => rw [hph] at h; simp [pccA] at h
  | some p1 =>
    obtain ⟨r1, m1⟩ := p1
    rw [hph, pccA_some] at h
    obtain ⟨phs, a1, hrun1, hS1, hg1, hdec1, hbd1⟩ := phsW_ok k dn fe vis m m1 a nn r1 hph hS
    have hb1 : (r1.headD 0).toNat + (r1.tail.headD 0).toNat < 2 ^ 64 := by
      have : iwTop m1 < 2 ^ 64 := (rdW (m1.arr64 CTL) 200).toNat_lt
      omega
    cases hin : instW (k + 1) m1 (r1.headD 0) (r1.tail.headD 0) cty with
    | none => rw [hin] at h; simp [pccB] at h
    | some p2 =>
      obtain ⟨r2, m2⟩ := p2
      rw [hin] at h
      obtain ⟨x, a2, hrun2, hS2, hg2, hout2⟩ := instW_ok (k + 1) dn fe vis m1 m2 a1 (r1.headD 0) (r1.tail.headD 0)
        cty phs r2 hin hS1 hcty hdec1 hb1 hbd1
      have hM2 : rpMR m2 mp0 :=
        rpMR_mfr ((phsW_mfr hph).trans (instW_mfr _ _ _ _ _ _ _ hin)) (by decide) (by decide) hM
      by_cases hz : r2.headD 0 = 0
      · rw [pccB_zero k no nl us nn r2 m2 hz] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        cases x with
        | none =>
          refine ⟨none, a2, ?_, hS2, hg1.trans hg2, rfl, mp0, hM2⟩
          simp only [ConRon.Arena.nestCanonCrest, StateT.run_bind]
          rw [hrun1]
          simp only [except_ok_bind, StateT.run_bind]
          rw [hrun2]
          rfl
        | some t => simp only [decOE] at hout2; rw [hz] at hout2; simp at hout2
      · rw [pccB_ok k no nl us nn r2 m2 hz] at h
        cases x with
        | none => exact absurd hout2 hz
        | some t =>
          simp only [decOE, decW0E] at hout2
          obtain ⟨-, htlt, htd⟩ := hout2
          cases hrc : rpConstW k m2 no nl us 0 nn (r2.tail.headD 0) with
          | none => rw [hrc] at h; simp [pccC] at h
          | some p3 =>
            obtain ⟨r3, m3⟩ := p3
            rw [hrc] at h
            by_cases hb3 : 4294967296 ≤ r3
            · rw [pccC_big _ _ _ hb3] at h; simp at h
            rw [pccC_some _ _ _ hb3] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hg12 := hg1.trans hg2
            have hdec2 : decHL m2 no.toNat nl.toNat = some names := by rw [decHL_grow hg12 hit]; exact hdec
            obtain ⟨a3, hrun3, hM3, hS3, hg3⟩ := rpConstW_ok k dn fe vis m2 m3 a2 no nl us 0 nn (r2.tail.headD 0) r3
              nn.toNat names mp0 hrc hS2 htlt hus hdec2 hno (by have := hg12.1; omega) rfl hnn
              (by simp; omega) hM2
            refine ⟨some (decE r3), a3, ?_, hS3, hg12.trans hg3, ?_, ∅, hM3⟩
            · simp only [ConRon.Arena.nestCanonCrest, StateT.run_bind]
              rw [hrun1]
              simp only [except_ok_bind, StateT.run_bind]
              rw [hrun2]
              simp only [except_ok_bind, StateT.run_bind]
              have h3 : StateT.run (ConRon.Arena.replaceApps names (decI us) 0 nn.toNat (decI (r2.tail.headD 0))) a2 = .ok (decE r3, a3) := hrun3
              rw [← htd, h3]
              rfl
            · simp only [decOE, decW0E]
              exact ⟨rfl, lt_of_notbig hb3, rfl⟩


section census3
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc) (hl : AhLook p) (hk : MkLook p)
  (hng : p.lookup "nest_phs_go" = some nestPhsGo) (hnp : p.lookup "nest_phs" = some nestPhs)
  (hip : p.lookup "inst_pis_with" = some instPisWith)
  (hf : p.lookup "ra_find" = some (memoFindG raSch)) (hput : p.lookup "ra_put" = some (memoPutG raSch))
  (hgo : p.lookup "replace_apps_go" = some replaceAppsGo)
  (hnode : p.lookup "replace_apps_node" = some replaceAppsNode)
  (hcl : p.lookup "ra_clear" = some (memoClearG raSch))
  (hra : p.lookup "replace_apps" = some replaceApps)
  (hp : p.lookup "nest_canon_crest" = some nestCanonCrest)
include ha hl hk hng hnp hip hf hput hgo hnode hcl hra hp

/-- **`nest_canon_crest` refines `nestCanonCrest`**: instantiate the pis with the canonical parameter
variables, then rewrite the applications (result `[1, e]`, or `[0, 0]` for `none`). -/
@[refines ConRon.Arena.nestCanonCrest]
theorem nestCanonCrest_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis no nl us nn cty : Word) (names : List NIdx) (hS : StageR dn vis fe s₀.mem a₀)
    (hcty : H cty) (hus : H us) (hdec : decHL s₀.mem no.toNat nl.toNat = some names)
    (hno : no.toNat + nl.toNat < 2 ^ 64) (hit : no.toNat + nl.toNat ≤ iwTop s₀.mem)
    (hnn : nn.toNat + names.length < 2 ^ 64)
    (mp0 : Std.HashMap EIdx EIdx) (hM : rpMR s₀.mem mp0) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 2)) "nest_canon_crest" [no, nl, us, nn, cty]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.nestCanonCrest names (decI us) nn.toNat (decI cty)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.nestCanonCrest names (decI us) nn.toNat (decI cty)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decOE s'.mem r (AM.res (ConRon.Arena.nestCanonCrest names (decI us) nn.toNat (decI cty)) a₀) ∧
      ∃ mp, rpMR s'.mem mp; ⊤⦄ := by
  refine triple_post (nestCanonCrest_spec p ha hl hk hng hnp hip hf hput hgo hnode hcl hra hp n s₀ no nl us nn cty) ?_
  rintro r s' ⟨hl', hm⟩
  obtain ⟨x, a', hrun, hS', hgr, hout, hM'⟩ := pccW_ok n dn fe vis _ _ a₀ no nl us nn cty names r hm hS hcty hus hdec hno hit
    hnn mp0 hM
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl', hok, by rw [hst]; exact hS', hgr, by rw [hres]; exact hout, hM'⟩

end census3

/-! ### The banked walk `replace_fvars` writes only its own memo -/

/-- The banked walk's write set among the memos. -/
abbrev RxFr (m m' : Mem) : Prop := MFr [RFM] [208, 209, 218, 219] m m'

theorem posmemo_rpMk_rx {m m' : Mem} {g a2 x2 c2 y x r : Word} (h : rpMkW m g a2 x2 c2 y x = some (r, m')) :
    RxFr m m' := (rpMkW_mfr h).up

theorem posmemo_rx_mfr (n : Nat) :
    (∀ (m m' : Mem) (f i a b : Word), rxMapW n m f i = some (a, b, m') → RxFr m m') ∧
    (∀ (m m' : Mem) (ctx po pl nn i a b : Word), rxImgW n m ctx po pl nn i = some (a, b, m') → RxFr m m') ∧
    (∀ (m m' : Mem) (ctx po pl n1 i a b : Word), rxFrameW n m ctx po pl n1 i = some (a, b, m') → RxFr m m') ∧
    (∀ (m m' : Mem) (f o l a b : Word), rxDsW n m f o l = some (a, b, m') → RxFr m m') ∧
    (∀ (m m' : Mem) (f o l q j : Word), rxDsGoW n m f o l q j = some m' → RxFr m m') ∧
    (∀ (m m' : Mem) (f e r : Word), rxW n m f e = some (r, m') → RxFr m m') ∧
    (∀ (m m' : Mem) (f fu h r : Word), rxGoW n m f fu h = some (r, m') → RxFr m m') ∧
    (∀ (m m' : Mem) (f f1 g x y z r : Word), rxNodeW n m f f1 g x y z = some (r, m') → RxFr m m') := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
      simp_all [rxMapW, rxImgW, rxFrameW, rxDsW, rxDsGoW, rxW, rxGoW, rxNodeW]
  | succ n ih =>
  obtain ⟨iMap, iImg, iFr, iDs, iDsGo, iRx, iGo, iNode⟩ := ih
  -- the frame record's chain (`pfrK1`)
  have pfr : ∀ (m m' : Mem) (ctx po pl n1 h a b : Word),
      pfrK1 n ctx po pl n1 (some (h, m)) = some (a, b, m') → RxFr m m' := by
    intro m m' ctx po pl n1 h a b hh
    rw [pfrK1_some] at hh
    cases h1 : posRecW m [0, ctx, po, pl, n1] with
    | none => rw [h1] at hh; simp [pfrK2] at hh
    | some p1 =>
    obtain ⟨f, m1⟩ := p1
    rw [h1, pfrK2_some] at hh
    cases h2 : rxDsW n m1 f (rdW (m1.arr64 IW) (rdW (m.arr64 IW) h + 2))
        (rdW (m1.arr64 IW) (rdW (m.arr64 IW) h + 3)) with
    | none => rw [h2] at hh; simp [pfrK3] at hh
    | some p2 =>
    obtain ⟨q, l, m2⟩ := p2
    rw [h2, pfrK3_some] at hh
    cases h3 : ceinternW m2 (rdW (m2.arr64 IW) (rdW (m.arr64 IW) h))
        (rdW (m2.arr64 IW) (rdW (m.arr64 IW) h + 1)) with
    | none => rw [h3] at hh; simp [frK4] at hh
    | some p3 =>
    obtain ⟨hd, m3⟩ := p3
    rw [h3] at hh
    by_cases hb : 4294967296 ≤ hd
    · simp [frK4, hb] at hh
    rw [frK4_ok (hb := hb)] at hh
    cases h4 : stubM "mk_app_n_f" m3 [hd, q, l] with
    | none => rw [h4] at hh; simp [frK5] at hh
    | some p4 =>
    obtain ⟨rr, m4⟩ := p4
    rw [h4, frK5_some] at hh
    simp only [Option.some.injEq, Prod.mk.injEq] at hh
    obtain ⟨-, -, rfl⟩ := hh
    exact ((((posRecW_mfr h1).up.trans (iDs _ _ _ _ _ _ _ h2)).trans (MFr.of_low (ceinternW_low h3)).up).trans
      (MFr.stub (by decide) h4).up)
  have hMap : ∀ (m m' : Mem) (f i a b : Word), rxMapW (n + 1) m f i = some (a, b, m') → RxFr m m' := by
    intro m m' f i a b hh
    by_cases h0 : rdW (m.arr64 IW) f = 0
    · rw [rxMapW_img (ht := h0)] at hh; exact iImg _ _ _ _ _ _ _ _ _ hh
    by_cases h1 : rdW (m.arr64 IW) f = 1
    · rw [rxMapW_km (ht := h1)] at hh
      simp only [Option.some.injEq, Prod.mk.injEq] at hh; rw [← hh.2.2]; exact MFr.refl _ _ _
    by_cases h2 : rdW (m.arr64 IW) f = 2
    · rw [rxMapW_er (ht := h2)] at hh
      cases hp : pinWordV m 53 with
      | none => rw [hp] at hh; simp [erK1] at hh
      | some z =>
      rw [hp, erK1_some] at hh
      cases hs : sointernW m z with
      | none => rw [hs] at hh; simp [erK2] at hh
      | some p1 =>
      obtain ⟨s, m1⟩ := p1
      rw [hs] at hh
      by_cases hb : 4294967296 ≤ s
      · simp [erK2, hb] at hh
      rw [erK2_ok (h := hb)] at hh
      cases hv : fvinternW m1 i s with
      | none => rw [hv] at hh; simp [erK3] at hh
      | some p2 =>
      obtain ⟨v, m2⟩ := p2
      rw [hv, erK3_some] at hh
      simp only [Option.some.injEq, Prod.mk.injEq] at hh
      obtain ⟨-, -, rfl⟩ := hh
      exact (MFr.of_low ((sointernW_low hs).trans (fvinternW_low hv))).up
    by_cases hi : i < rdW (m.arr64 IW) (f + 2)
    · rw [rxMapW_cin (h0 := h0) (h1 := h1) (h2 := h2) (hi := hi)] at hh
      simp only [Option.some.injEq, Prod.mk.injEq] at hh; rw [← hh.2.2]; exact MFr.refl _ _ _
    · rw [rxMapW_cout (h0 := h0) (h1 := h1) (h2 := h2) (hi := hi)] at hh
      simp only [Option.some.injEq, Prod.mk.injEq] at hh; rw [← hh.2.2]; exact MFr.refl _ _ _
  have hGo : ∀ (m m' : Mem) (f fu h r : Word), rxGoW (n + 1) m f fu h = some (r, m') → RxFr m m' := by
    intro m m' f fu h r hh
    by_cases hf : fu = 0
    · rw [rxGoW_abort (hf := hf)] at hh; cases hh
    rw [rxGoW_view (hf := hf)] at hh
    by_cases hv : eViewW m h = []
    · rw [rxG1_abort (hv := hv)] at hh; cases hh
    by_cases hg : (eViewW m h).headD 0 = 0 ∨ (eViewW m h).headD 0 = 2 ∨ (eViewW m h).headD 0 = 8 ∨
        (eViewW m h).headD 0 = 3
    · rw [rxG1_leaf (hv := hv) (hg := hg)] at hh
      simp only [Option.some.injEq, Prod.mk.injEq] at hh; rw [← hh.2]; exact MFr.refl _ _ _
    by_cases h1 : (eViewW m h).headD 0 = 1
    · rw [rxG1_fvar (hv := hv) (hg := hg) (h1 := h1)] at hh
      cases hm : rxMapW n m f ((eViewW m h).tail.headD 0) with
      | none => rw [hm] at hh; simp [rxH] at hh
      | some p1 =>
      obtain ⟨ok, r1, m1⟩ := p1
      rw [hm, rxH_some] at hh
      simp only [Option.some.injEq, Prod.mk.injEq] at hh
      obtain ⟨-, rfl⟩ := hh
      exact iMap _ _ _ _ _ _ hm
    rw [rxG1_node (hv := hv) (hg := hg) (h1 := h1)] at hh
    by_cases hr : mfindG rfSch m h (rdW (m.arr64 CTL) 219 <<< 32) = []
    · rw [rxG3_abort (hr := hr)] at hh; cases hh
    by_cases hit : (mfindG rfSch m h (rdW (m.arr64 CTL) 219 <<< 32)).headD 0 ≠ 0
    · rw [rxG3_hit (hr := hr) (hh := hit)] at hh
      simp only [Option.some.injEq, Prod.mk.injEq] at hh; rw [← hh.2]; exact MFr.refl _ _ _
    rw [rxG3_miss (hr := hr) (hh := hit)] at hh
    cases hn : rxNodeW n m f (fu - 1) ((eViewW m h).headD 0) ((eViewW m h).tail.headD 0)
        ((eViewW m h).tail.tail.headD 0) ((eViewW m h).tail.tail.tail.headD 0) with
    | none => rw [hn] at hh; simp [rxG4] at hh
    | some p1 =>
    obtain ⟨r1, m1⟩ := p1
    rw [hn, rxG4_some] at hh
    cases hs : msetG rfSch m1 h (rdW (m1.arr64 CTL) 219 <<< 32) r1 with
    | none => rw [hs] at hh; simp [rxG5] at hh
    | some m2 =>
    rw [hs, rxG5_some] at hh
    simp only [Option.some.injEq, Prod.mk.injEq] at hh
    obtain ⟨-, rfl⟩ := hh
    exact (iNode _ _ _ _ _ _ _ _ _ hn).trans
      ⟨_, _, msetG_frame rfSch rfSch_wf m1 m2 _ _ _ hs, by simp [rfSch, RFM], by simp [rfSch]⟩
  refine ⟨hMap, ?_, ?_, ?_, ?_, ?_, hGo, ?_⟩
  · -- rxImgW
    intro m m' ctx po pl nn i a b hh
    by_cases h0 : nn = 0
    · rw [rxImgW_root (h0 := h0)] at hh
      by_cases hin : rdW (m.arr64 IW) (ctx + 4) ≤ i ∧ i < hiW m ctx 0
      · rw [rxRootW_in (h := hin)] at hh
        cases hc : ceinternW m (getDW m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1))
            (i - rdW (m.arr64 IW) (ctx + 4)) 0) (rdW (m.arr64 IW) (ctx + 10)) with
        | none => rw [hc] at hh; simp [rtK1] at hh
        | some p1 =>
        obtain ⟨hd, m1⟩ := p1
        rw [hc] at hh
        by_cases hb : 4294967296 ≤ hd
        · simp [rtK1, hb] at hh
        rw [rtK1_ok (h := hb)] at hh
        cases hst : stubM "mk_app_n_f" m1 [hd, rdW (m1.arr64 IW) (ctx + 7), rdW (m1.arr64 IW) (ctx + 8)] with
        | none => rw [hst] at hh; simp [rtK2] at hh
        | some p2 =>
        obtain ⟨rr, m2⟩ := p2
        rw [hst, rtK2_some] at hh
        simp only [Option.some.injEq, Prod.mk.injEq] at hh
        obtain ⟨-, -, rfl⟩ := hh
        exact ((MFr.of_low (ceinternW_low hc)).trans (MFr.stub (by decide) hst)).up
      · rw [rxRootW_out (h := hin)] at hh
        simp only [Option.some.injEq, Prod.mk.injEq] at hh; rw [← hh.2.2]; exact MFr.refl _ _ _
    by_cases hh2 : i = hiW m ctx (nn - 1)
    · rw [rxImgW_frame (h0 := h0) (hh := hh2)] at hh; exact iFr _ _ _ _ _ _ _ _ _ hh
    · rw [rxImgW_next (h0 := h0) (hh := hh2)] at hh; exact iImg _ _ _ _ _ _ _ _ _ hh
  · -- rxFrameW
    intro m m' ctx po pl n1 i a b hh
    by_cases hn : n1 < pl
    · rw [rxFrameW_in (hn := hn)] at hh; exact pfr _ _ _ _ _ _ _ _ _ hh
    rw [rxFrameW_def (hn := hn)] at hh
    cases h1 : posRecW m [0, 0, 0, 0] with
    | none => rw [h1] at hh; simp [frK0] at hh
    | some p1 =>
    obtain ⟨k, m1⟩ := p1
    rw [h1, frK0_some] at hh
    cases h2 : posRecW m1 [k, 0] with
    | none => rw [h2] at hh; simp [pfrK1] at hh
    | some p2 =>
    obtain ⟨hk, m2⟩ := p2
    rw [h2] at hh
    exact ((posRecW_mfr h1).trans (posRecW_mfr h2)).up.trans (pfr _ _ _ _ _ _ _ _ _ hh)
  · -- rxDsW
    intro m m' f o l a b hh
    rw [rxDsW_succ] at hh
    cases h1 : allocW m l with
    | none => rw [h1] at hh; simp [dsA] at hh
    | some p1 =>
    obtain ⟨q, m1⟩ := p1
    rw [h1, dsA_some] at hh
    cases h2 : rxDsGoW n m1 f o l q 0 with
    | none => rw [h2] at hh; simp [dsB] at hh
    | some m2 =>
    rw [h2, dsB_some] at hh
    simp only [Option.some.injEq, Prod.mk.injEq] at hh
    obtain ⟨-, -, rfl⟩ := hh
    exact (allocW_mfr h1).up.trans (iDsGo _ _ _ _ _ _ _ h2)
  · -- rxDsGoW
    intro m m' f o l q j hh
    by_cases hj : l ≤ j
    · rw [rxDsGoW_done (hj := hj)] at hh; cases hh; exact MFr.refl _ _ _
    rw [rxDsGoW_step (hj := hj)] at hh
    cases h1 : rxW n m f (rdW (m.arr64 IW) (o + j)) with
    | none => rw [h1] at hh; simp [dgK] at hh
    | some p1 =>
    obtain ⟨r, m1⟩ := p1
    rw [h1, dgK_some] at hh
    exact ((iRx _ _ _ _ _ h1).trans (MFr.set_iw _ _ _).up).trans (iDsGo _ _ _ _ _ _ _ hh)
  · -- rxW
    intro m m' f e r hh
    by_cases hb : 4294967296 ≤ rdW (m.arr64 CTL) 218 + 1
    · rw [rxW_big (hb := hb)] at hh; cases hh
    rw [rxW_ok (hb := hb)] at hh
    cases h1 : rxGoW n (benterG 218 m) f CWF e with
    | none => rw [h1] at hh; simp [rxK1] at hh
    | some p1 =>
    obtain ⟨r1, m1⟩ := p1
    rw [h1] at hh
    by_cases hb1 : 4294967296 ≤ r1
    · simp [rxK1, hb1] at hh
    rw [rxK1_ok (hb := hb1)] at hh
    simp only [Option.some.injEq, Prod.mk.injEq] at hh
    obtain ⟨-, rfl⟩ := hh
    exact (MFr.trans ⟨_, _, benterG_frame 218 m, by simp, by simp⟩ (iGo _ _ _ _ _ _ h1)).trans
      ⟨_, _, MemFrame.setCtl m1 219 _, by simp, by simp⟩
  · -- rxNodeW
    intro m m' f f1 g x y z r hh
    by_cases hg : g = 4 ∨ g = 5 ∨ g = 6
    · rw [rxNodeW_bin (hg := hg)] at hh
      cases h1 : rxGoW n m f f1 x with
      | none => rw [h1] at hh; simp [rxB1] at hh
      | some p1 =>
      obtain ⟨a2, m1⟩ := p1
      rw [h1, rxB1_some] at hh
      cases h2 : rxGoW n m1 f f1 y with
      | none => rw [h2] at hh; simp [rxB2] at hh
      | some p2 =>
      obtain ⟨x2, m2⟩ := p2
      rw [h2, rxB2_some] at hh
      exact ((iGo _ _ _ _ _ _ h1).trans (iGo _ _ _ _ _ _ h2)).trans (posmemo_rpMk_rx hh)
    by_cases h7 : g = 7
    · rw [rxNodeW_let (hg := hg) (h7 := h7)] at hh
      cases h1 : rxGoW n m f f1 x with
      | none => rw [h1] at hh; simp [rxL1] at hh
      | some p1 =>
      obtain ⟨a2, m1⟩ := p1
      rw [h1, rxL1_some] at hh
      cases h2 : rxGoW n m1 f f1 y with
      | none => rw [h2] at hh; simp [rxL2] at hh
      | some p2 =>
      obtain ⟨x2, m2⟩ := p2
      rw [h2, rxL2_some] at hh
      cases h3 : rxGoW n m2 f f1 z with
      | none => rw [h3] at hh; simp [rxL3] at hh
      | some p3 =>
      obtain ⟨c2, m3⟩ := p3
      rw [h3, rxL3_some] at hh
      exact (((iGo _ _ _ _ _ _ h1).trans (iGo _ _ _ _ _ _ h2)).trans (iGo _ _ _ _ _ _ h3)).trans
        (posmemo_rpMk_rx hh)
    rw [rxNodeW_proj (hg := hg) (h7 := h7)] at hh
    cases h1 : rxGoW n m f f1 z with
    | none => rw [h1] at hh; simp [rxP1] at hh
    | some p1 =>
    obtain ⟨a2, m1⟩ := p1
    rw [h1, rxP1_some] at hh
    exact (iGo _ _ _ _ _ _ h1).trans (posmemo_rpMk_rx hh)

theorem rxW_mfr {n : Nat} {m m' : Mem} {f e r : Word} (h : rxW n m f e = some (r, m')) : RxFr m m' :=
  (posmemo_rx_mfr n).2.2.2.2.2.1 _ _ _ _ _ h

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `nest_crest` refines `nestCrest` -/

def pcrK3 : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) => some ([1, r], m3)
def pcrK2 (k : Nat) (c : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (f, m2) => pcrK3 (rxW (k + 2) m2 f c)
def pcrK1 (k : Nat) (dO dL hO hL : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => if r1.headD 0 = 0 then some ([0, 0], m1)
      else pcrK2 k (r1.tail.headD 0) (posRecW m1 [1, dO, dL, hO, hL])
/-- The model of `nest_crest` at exec fuel `k + 3`. -/
def pcrW (k : Nat) (m : Mem) (no nl us dO dL hO hL cty : Word) : Option (List Word × Mem) :=
  pcrK1 k dO dL hO hL (pccW k m no nl us dL cty)

section arms
variable (k : Nat) (m1 m2 m3 : Mem) (dO dL hO hL c f r : Word) (r1 : List Word)
theorem pcrK3_some : pcrK3 (some (r, m3)) = some ([1, r], m3) := rfl
theorem pcrK2_some : pcrK2 k c (some (f, m2)) = pcrK3 (rxW (k + 2) m2 f c) := rfl
theorem pcrK1_zero (h : r1.headD 0 = 0) : pcrK1 k dO dL hO hL (some (r1, m1)) = some ([0, 0], m1) := by
  simp only [pcrK1]; rw [if_pos h]
theorem pcrK1_ok (h : ¬ r1.headD 0 = 0) : pcrK1 k dO dL hO hL (some (r1, m1)) =
    pcrK2 k (r1.tail.headD 0) (posRecW m1 [1, dO, dL, hO, hL]) := by simp only [pcrK1]; rw [if_neg h]
end arms
attribute [ind_grind] pcrK3_some pcrK2_some pcrK1_zero pcrK1_ok

/-- The lookups of `nest_crest`. -/
structure CrLook (p : Prog) : Prop where
  rx : RxLook p
  ng : p.lookup "nest_phs_go" = some nestPhsGo
  np : p.lookup "nest_phs" = some nestPhs
  ip : p.lookup "inst_pis_with" = some instPisWith
  raf : p.lookup "ra_find" = some (memoFindG raSch)
  rap : p.lookup "ra_put" = some (memoPutG raSch)
  rgo : p.lookup "replace_apps_go" = some replaceAppsGo
  rnd : p.lookup "replace_apps_node" = some replaceAppsNode
  rcl : p.lookup "ra_clear" = some (memoClearG raSch)
  ra : p.lookup "replace_apps" = some replaceApps
  cc : p.lookup "nest_canon_crest" = some nestCanonCrest
  cr : p.lookup "nest_crest" = some nestCrest

theorem nestCrest_spec (p : Prog) (L : CrLook p) (k : Nat) (s₀ : St) (no nl us dO dL hO hL cty : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 3)) "nest_crest" [no, nl, us, dO, dL, hO, hL, cty]
    ⦃fun r s' => LocEq s' s₀ ∧ pcrW k s₀.mem no nl us dO dL hO hL cty = some (r, s'.mem); ⊤⦄ := by
  have R := L.rx
  rw [invoke_eq _ L.cr]
  simp only [callFn, nestCrest]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      nestCanonCrest_spec p R.ha R.hl R.hk L.ng L.np L.ip L.raf L.rap L.rgo L.rnd L.rcl L.ra L.cc k,
      posRec5_specW p R.ha R.h5 (k + 2), (rxSpec_all p R (k + 2)).2.2.2.2.2.2.2] <;>
    finish (gen := 20) [pcrW]

section rel
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

theorem pcrW_ok (k : Nat) (m m' : Mem) (a : AState) (no nl us dO dL hO hL cty : Word) (r : List Word)
    (names : List NIdx) (ds holes : List EIdx) (M : Std.HashMap (EIdx × Word) EIdx) (G g : Word)
    (h : pcrW k m no nl us dO dL hO hL cty = some (r, m')) (hS : StageR dn vis fe m a) (hcty : H cty)
    (hus : H us) (hdec : decHL m no.toNat nl.toNat = some names) (hno : no.toNat + nl.toNat < 2 ^ 64)
    (hit : no.toNat + nl.toNat ≤ iwTop m) (hnn : dL.toNat + names.length < 2 ^ 64)
    (mp0 : Std.HashMap EIdx EIdx) (hMr : rpMR m mp0)
    (hds : decHL m dO.toNat dL.toNat = some ds) (hdsb : dO.toNat + dL.toNat ≤ iwTop m)
    (hho : decHL m hO.toNat hL.toNat = some holes) (hhob : hO.toNat + hL.toNat ≤ iwTop m)
    (hR : RfInv m M G g) :
    ∃ x a', (ConRon.Arena.nestCrest names (decI us) ds holes (decI cty)).run a = .ok (x, a') ∧
      decOE m' r x ∧ RxPost dn fe vis m m' a' M G g ∧ ∃ mp, rpMR m' mp := by
  unfold pcrW at h
  have hdl := decHL_length m hds
  cases hpc : pccW k m no nl us dL cty with
  | none => rw [hpc] at h; simp [pcrK1] at h
  | some p1 =>
  obtain ⟨r1, m1⟩ := p1
  rw [hpc] at h
  obtain ⟨x, a1, hrun1, hS1, hg1, hout1, mp1, hM1⟩ := pccW_ok k dn fe vis m m1 a no nl us dL cty names r1 hpc hS hcty
    hus hdec hno hit hnn mp0 hMr
  have hR1 := hR.frame (pccW_fr hpc)
  cases x with
  | none =>
    have hz : r1.headD 0 = 0 := hout1
    rw [pcrK1_zero (h := hz)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨none, a1, ?_, rfl, hR.post hS1 hg1 (pccW_fr hpc), mp1, hM1⟩
    simp only [ConRon.Arena.nestCrest, StateT.run_bind]
    rw [hdl, hrun1]; rfl
  | some c =>
    obtain ⟨h1, hcH, hcd⟩ := hout1
    rw [pcrK1_ok (h := by rw [h1]; decide)] at h
    cases hrec : posRecW m1 [1, dO, dL, hO, hL] with
    | none => rw [hrec] at h; simp [pcrK2] at h
    | some p2 =>
    obtain ⟨f, m2⟩ := p2
    rw [hrec, pcrK2_some] at h
    obtain ⟨hS2, hg2, hf2, ht2, hget2⟩ := posRecW_stage hrec hS1 (by simp)
    simp only [List.length_cons, List.length_nil] at ht2
    have hg12 := hg1.trans hg2
    have g0 := iwN_of_get (by simpa using hget2 0 (by simp))
    have g1 := iwN_of_get (by simpa using hget2 1 (by simp))
    have g2 := iwN_of_get (by simpa using hget2 2 (by simp))
    have g3 := iwN_of_get (by simpa using hget2 3 (by simp))
    have g4 := iwN_of_get (by simpa using hget2 4 (by simp))
    have hfm : FMOk m2 f.toNat (.keyMap ds holes) :=
      ⟨by simpa using g0, by omega, ⟨dO.toNat, dL.toNat, g1, g2, by rw [decHL_grow hg12 hdsb]; exact hds,
        by have := hg12.1; omega⟩, ⟨hO.toNat, hL.toNat, g3, g4, by rw [decHL_grow hg12 hhob]; exact hho,
        by have := hg12.1; omega⟩⟩
    cases hrx : rxW (k + 2) m2 f (r1.tail.headD 0) with
    | none => rw [hrx] at h; simp [pcrK3] at h
    | some p3 =>
    obtain ⟨rr, m3⟩ := p3
    rw [hrx, pcrK3_some] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨a3, hrun3, hH3, hpost3⟩ := (rxOK_all dn fe vis (k + 2)).2.2.2.2.2.2 m2 m3 a1 f _ _ rr M G g hrx hS2 hfm
      hcH (hR1.frame (posRecW_fr hrec))
    refine ⟨some (decE rr), a3, ?_, ⟨rfl, hH3, rfl⟩, RxPost.of_fr hR ((pccW_fr hpc).trans (posRecW_fr hrec)) hg12 hpost3,
      mp1, rpMR_mfr ((posRecW_mfr hrec).up.trans (rxW_mfr hrx)) (by decide) (by decide) hM1⟩
    simp only [ConRon.Arena.nestCrest, StateT.run_bind]
    rw [hdl, hrun1]
    simp only [except_ok_bind, StateT.run_bind]
    rw [← hcd, show (decI (r1.tail.headD 0) : EIdx) = decE (r1.tail.headD 0) from rfl, hrun3]
    rfl

end rel

section census
variable (p : Prog) (L : CrLook p)
include L

/-- **`nest_crest` refines `nestCrest`** (through the stubs below `nest_canon_crest` and `mk_app_n`;
`replace_apps`' memo well formed in the memory at hand, and again after). -/
@[refines ConRon.Arena.nestCrest]
theorem nestCrest_refines (k : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
    (vis no nl us dO dL hO hL cty : Word) (names : List NIdx) (ds holes : List EIdx)
    (M : Std.HashMap (EIdx × Word) EIdx) (G g : Word) (hS : StageR dn vis fe s₀.mem a₀) (hcty : H cty)
    (hus : H us) (hdec : decHL s₀.mem no.toNat nl.toNat = some names) (hno : no.toNat + nl.toNat < 2 ^ 64)
    (hit : no.toNat + nl.toNat ≤ iwTop s₀.mem) (hnn : dL.toNat + names.length < 2 ^ 64)
    (mp0 : Std.HashMap EIdx EIdx) (hMr : rpMR s₀.mem mp0)
    (hds : decHL s₀.mem dO.toNat dL.toNat = some ds) (hdsb : dO.toNat + dL.toNat ≤ iwTop s₀.mem)
    (hho : decHL s₀.mem hO.toNat hL.toNat = some holes) (hhob : hO.toNat + hL.toNat ≤ iwTop s₀.mem)
    (hR : RfInv s₀.mem M G g) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 3)) "nest_crest" [no, nl, us, dO, dL, hO, hL, cty]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.nestCrest names (decI us) ds holes (decI cty)) a₀ ∧
      decOE s'.mem r (AM.res (ConRon.Arena.nestCrest names (decI us) ds holes (decI cty)) a₀) ∧
      RxPost dn fe vis s₀.mem s'.mem (AM.st (ConRon.Arena.nestCrest names (decI us) ds holes (decI cty)) a₀) M G g ∧
      ∃ mp, rpMR s'.mem mp; ⊤⦄ := by
  refine triple_post (nestCrest_spec p L k s₀ no nl us dO dL hO hL cty) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨x, a', hrun, hout, hpost, hM'⟩ := pcrW_ok dn fe vis k _ _ a₀ no nl us dO dL hO hL cty r names ds holes M G g hm
    hS hcty hus hdec hno hit hnn mp0 hMr hds hdsb hho hhob hR
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hres]; exact hout, by rw [hst]; exact hpost, hM'⟩

end census

end L.Ind
