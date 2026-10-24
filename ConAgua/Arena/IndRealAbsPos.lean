import ConAgua.Arena.IndPos2SpecN
import ConAgua.Arena.IndRealAbsSim

/-!
# The `abstract1` memo across the positivity check's models (lane `indproofs4`, helper `abs`)

`AFr` (`IndRealAbs.lean`) for the models of the positivity check's callees, mirroring their `MFr`
frames (`IndPosSpec5`, `IndPos2SpecD`‥`M`, `IndPosMemo`), proved by `afr_auto` from the callees'.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem fvbF_afr {m m' : Mem} {args r : List Word} (h : fvbF m args = some (r, m')) : AFr m m' :=
  AFr.of_frame (fvbF_frame h)

theorem envFindW_afr {m m' : Mem} {w vis : Word} {r : List Word} (h : envFindW m w vis = some (r, m')) :
    AFr m m' := by rw [envFindW_mem h]; exact AFr.refl _

theorem cvLpsA_afr {n : Nat} {m m' : Mem} {q : Word} {r : List Word} (h : L.Arena.cvLpsW n m q = some (r, m')) :
    AFr m m' := by
  cases n with
  | zero => simp [L.Arena.cvLpsW] at h
  | succ n => exact erToIwW_afr h

theorem bvbW_afr {n : Nat} {m m' : Mem} {h f x : Word} (hb : bvbW n m h f = some (x, m')) : AFr m m' := by
  have hfr : BbFrame m m' := by
    match n, hb with
    | n + 1, hb =>
      by_cases hs : derBW m h = 32767
      · rw [bvbW_sat (n := n) (m := m) (h := h) (f := f) hs] at hb
        match n, hb with
        | k + 1, hb => rw [bbN_succ] at hb; exact bbMemoW_frame k m m' h f x hb
      · rw [bvbW_pk (n := n) (m := m) (h := h) (f := f) hs] at hb
        simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨-, rfl⟩ := hb
        exact MemFrame.refl _ _ _
  exact AFr.of_frame hfr

theorem canonW_afr (n : Nat) {m m' : Mem} {no nl us nn c v : Word} {r : List Word}
    (h : canonW n m no nl us nn c v = some (r, m')) : AFr m m' := by
  cases n with
  | zero => simp [canonW] at h
  | succ n =>
  by_cases hvu : v ≠ us
  · rw [canonW_ne n m no nl us nn c v hvu] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; exact AFr.refl _
  · rw [canonW_eq n m no nl us nn c v hvu] at h
    cases hfw : findW n m no nl c with
    | none => rw [hfw] at h; simp [canonK0] at h
    | some fr =>
      rw [hfw] at h
      by_cases hz : fr.headD 0 = 0
      · rw [canonK0_miss _ _ _ hz] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h; exact AFr.refl _
      · rw [canonK0_hit _ _ _ hz] at h
        cases hpw : pinWordV m 53 with
        | none => rw [hpw] at h; simp [canonK1] at h
        | some z =>
          rw [hpw] at h
          by_cases hzb : 4294967296 ≤ z
          · rw [canonK1_big _ _ _ _ hzb] at h; simp at h
          rw [canonK1_ok _ _ _ _ hzb] at h
          cases hso : sointernW m z with
          | none => rw [hso] at h; simp [canonK2] at h
          | some p1 =>
            obtain ⟨s1, m1⟩ := p1
            rw [hso] at h
            by_cases hsb : 4294967296 ≤ s1
            · rw [canonK2_big _ _ _ _ hsb] at h; simp at h
            rw [canonK2_ok _ _ _ _ hsb] at h
            cases hfv : fvinternW m1 (nn + (fr.tail.headD 0)) s1 with
            | none => rw [hfv] at h; simp [canonK3] at h
            | some p2 =>
              obtain ⟨rr, m2⟩ := p2
              rw [hfv] at h
              by_cases hrb : 4294967296 ≤ rr
              · rw [canonK3_big _ _ hrb] at h; simp at h
              rw [canonK3_ok _ _ hrb] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨-, rfl⟩ := h
              exact (sointernW_afr hso).trans (fvinternW_afr hfv)

theorem ahW_afr {n : Nat} {m m' : Mem} {no nl us b nn e : Word} {r : List Word}
    (h : ahW n m no nl us b nn e = some (r, m')) : AFr m m' := by
  unfold ahW at h
  cases hph : phW n m b e nn with
  | none => rw [hph] at h; simp [ahK] at h
  | some r0 =>
    rw [hph] at h
    by_cases hz : r0.headD 0 = 0
    · rw [ahK_none n m no nl us nn r0 hz] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h; exact AFr.refl _
    · rw [ahK_some n m no nl us nn r0 hz] at h
      cases hc : canonW n m no nl us nn (r0.tail.headD 0) (r0.tail.tail.headD 0) with
      | none => rw [hc] at h; simp [ahC] at h
      | some pc =>
        obtain ⟨rc, m1⟩ := pc
        rw [hc, ahC_some] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact canonW_afr n hc

-- from IndPosSpec5
theorem posRecW_afr {m m' : Mem} {ws : List Word} {q : Word} (h : posRecW m ws = some (q, m')) :
    AFr m m' := by
  simp only [posRecW] at h
  cases hal : allocW m (UInt64.ofNat ws.length) with
  | none => rw [hal] at h; simp at h
  | some pr =>
    obtain ⟨q1, m1⟩ := pr
    rw [hal] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (allocW_afr hal).trans (AFr.iw (wrIW_frame _ _ _))

-- from IndPosSpec5
theorem phsGoW_afr (k : Nat) : ∀ (m m' : Mem) (q n i : Word), phsGoW k m q n i = some m' → AFr m m' := by
  induction k with
  | zero => intro m m' q n i h; simp [phsGoW] at h
  | succ k ih =>
    intro m m' q n i h
    by_cases hd : n ≤ i
    · rw [phsGoW_done (h := hd)] at h; cases h; exact AFr.refl _
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
    exact ((((sointernW_afr hso).trans (fvinternW_afr hfv))).trans (set64IW_afr _ _ _)).trans
      (ih _ _ _ _ _ h)

-- from IndPosSpec5
theorem phsW_afr {k : Nat} {m m' : Mem} {nn : Word} {r : List Word} (h : phsW k m nn = some (r, m')) : AFr m m' := by
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
  exact (allocW_afr hal).trans (phsGoW_afr k _ _ _ _ _ hg)

-- from IndPosSpec5
theorem rpMkW_afr {m m' : Mem} {g a2 x2 c2 y x r : Word} (h : rpMkW m g a2 x2 c2 y x = some (r, m')) : AFr m m' := by
  unfold rpMkW at h
  split at h
  · exact mkAppW_afr h
  split at h
  · exact mkLamW_afr h
  split at h
  · exact mkForallW_afr h
  split at h
  · exact mkLetW_afr h
  · exact mkProjW_afr h

-- from IndPosSpec5
theorem rpGoW_afr (n : Nat) :
    (∀ (m m' : Mem) (no nl us b nn f h r : Word), rpGoW n m no nl us b nn f h = some (r, m') → AFr m m') ∧
    (∀ (m m' : Mem) (no nl us b nn f1 h g x y z r : Word),
      rpNodeW n m no nl us b nn f1 h g x y z = some (r, m') → AFr m m') := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  cases n with
  | zero => exact ⟨fun _ _ _ _ _ _ _ _ _ _ h => by simp [rpGoW] at h,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => by simp [rpNodeW] at h⟩
  | succ j =>
  have ihG : ∀ (m m' : Mem) (no nl us b nn f h r : Word), rpGoW j m no nl us b nn f h = some (r, m') →
      AFr m m' := (ih j (by omega)).1
  have ahF : ∀ {m m' : Mem} {no nl us b nn e : Word} {rr : List Word},
      ahWf j m no nl us b nn e = some (rr, m') → AFr m m' := by
    intro m m' no nl us b nn e rr h
    cases j with
    | zero => simp [ahWf] at h
    | succ i => exact (ahW_afr h)
  refine ⟨?_, ?_⟩
  · intro m m' no nl us b nn f h r hg
    by_cases hf : f = 0
    · rw [rpGoW_abort (hf := hf)] at hg; simp at hg
    rw [rpGoW_view (hf := hf)] at hg
    unfold rpG1 at hg
    split at hg; · simp at hg
    split at hg
    · simp only [Option.some.injEq, Prod.mk.injEq] at hg; rw [← hg.2]; exact AFr.refl _
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
    · simp only [Option.some.injEq, Prod.mk.injEq] at hg; rw [← hg.2]; exact AFr.refl _
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
            (AFr.of_frame (msetG_frame raSch raSch_wf m1 m2 h 0 rn hs))
  · intro m m' no nl us b nn f1 h g x y z r hn
    have bin : ∀ {m m' : Mem} {g x y r : Word},
        rpB1 j no nl us b nn f1 g x y (rpGoW j m no nl us b nn f1 x) = some (r, m') → AFr m m' := by
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
          exact ((ihG _ _ _ _ _ _ _ _ _ _ h1).trans (ihG _ _ _ _ _ _ _ _ _ _ h2)).trans (rpMkW_afr hb)
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
              (ihG _ _ _ _ _ _ _ _ _ _ h3)).trans (rpMkW_afr hn)
    · cases h1 : rpGoW j m no nl us b nn f1 z with
      | none => rw [h1] at hn; simp [rpP1] at hn
      | some p1 =>
        obtain ⟨a2, m1⟩ := p1
        rw [h1, rpP1_some] at hn
        exact (ihG _ _ _ _ _ _ _ _ _ _ h1).trans (rpMkW_afr hn)

-- from IndPosSpec5
theorem rpConstW_afr {n : Nat} {m m' : Mem} {no nl us b nn e r : Word}
    (h : rpConstW n m no nl us b nn e = some (r, m')) : AFr m m' := by
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
    exact (AFr.trans (AFr.of_frame (mclearG_frame raSch m))
      ((rpGoW_afr n).1 _ _ _ _ _ _ _ _ _ _ hg)).trans (AFr.of_frame (mclearG_frame raSch m1))

-- from IndPosSpec5
theorem pccW_afr {k : Nat} {m m' : Mem} {no nl us nn cty : Word} {r : List Word}
    (h : pccW k m no nl us nn cty = some (r, m')) : AFr m m' := by
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
    exact ((phsW_afr hp).trans (instW_afr _ _ _ _ _ _ _ hi))
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
  exact ((phsW_afr hp).trans (instW_afr _ _ _ _ _ _ _ hi)).trans (rpConstW_afr hr)

-- from IndPosSpec5
theorem posmemo_rx_afr (n : Nat) :
    (∀ (m m' : Mem) (f i a b : Word), rxMapW n m f i = some (a, b, m') → AFr m m') ∧
    (∀ (m m' : Mem) (ctx po pl nn i a b : Word), rxImgW n m ctx po pl nn i = some (a, b, m') → AFr m m') ∧
    (∀ (m m' : Mem) (ctx po pl n1 i a b : Word), rxFrameW n m ctx po pl n1 i = some (a, b, m') → AFr m m') ∧
    (∀ (m m' : Mem) (f o l a b : Word), rxDsW n m f o l = some (a, b, m') → AFr m m') ∧
    (∀ (m m' : Mem) (f o l q j : Word), rxDsGoW n m f o l q j = some m' → AFr m m') ∧
    (∀ (m m' : Mem) (f e r : Word), rxW n m f e = some (r, m') → AFr m m') ∧
    (∀ (m m' : Mem) (f fu h r : Word), rxGoW n m f fu h = some (r, m') → AFr m m') ∧
    (∀ (m m' : Mem) (f f1 g x y z r : Word), rxNodeW n m f f1 g x y z = some (r, m') → AFr m m') := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
      simp_all [rxMapW, rxImgW, rxFrameW, rxDsW, rxDsGoW, rxW, rxGoW, rxNodeW]
  | succ n ih =>
  obtain ⟨iMap, iImg, iFr, iDs, iDsGo, iRx, iGo, iNode⟩ := ih
  -- the frame record's chain (`pfrK1`)
  have pfr : ∀ (m m' : Mem) (ctx po pl n1 h a b : Word),
      pfrK1 n ctx po pl n1 (some (h, m)) = some (a, b, m') → AFr m m' := by
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
    cases h4 : mknF m3 [hd, q, l] with
    | none => rw [h4] at hh; simp [frK5] at hh
    | some p4 =>
    obtain ⟨rr, m4⟩ := p4
    rw [h4, frK5_some] at hh
    simp only [Option.some.injEq, Prod.mk.injEq] at hh
    obtain ⟨-, -, rfl⟩ := hh
    exact ((((posRecW_afr h1).trans (iDs _ _ _ _ _ _ _ h2)).trans (ceinternW_afr h3)).trans
      (mknF_afr h4))
  have hMap : ∀ (m m' : Mem) (f i a b : Word), rxMapW (n + 1) m f i = some (a, b, m') → AFr m m' := by
    intro m m' f i a b hh
    by_cases h0 : rdW (m.arr64 IW) f = 0
    · rw [rxMapW_img (ht := h0)] at hh; exact iImg _ _ _ _ _ _ _ _ _ hh
    by_cases h1 : rdW (m.arr64 IW) f = 1
    · rw [rxMapW_km (ht := h1)] at hh
      simp only [Option.some.injEq, Prod.mk.injEq] at hh; rw [← hh.2.2]; exact AFr.refl _
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
      exact (((sointernW_afr hs).trans (fvinternW_afr hv)))
    by_cases hi : i < rdW (m.arr64 IW) (f + 2)
    · rw [rxMapW_cin (h0 := h0) (h1 := h1) (h2 := h2) (hi := hi)] at hh
      simp only [Option.some.injEq, Prod.mk.injEq] at hh; rw [← hh.2.2]; exact AFr.refl _
    · rw [rxMapW_cout (h0 := h0) (h1 := h1) (h2 := h2) (hi := hi)] at hh
      simp only [Option.some.injEq, Prod.mk.injEq] at hh; rw [← hh.2.2]; exact AFr.refl _
  have hGo : ∀ (m m' : Mem) (f fu h r : Word), rxGoW (n + 1) m f fu h = some (r, m') → AFr m m' := by
    intro m m' f fu h r hh
    by_cases hf : fu = 0
    · rw [rxGoW_abort (hf := hf)] at hh; cases hh
    rw [rxGoW_view (hf := hf)] at hh
    by_cases hv : eViewW m h = []
    · rw [rxG1_abort (hv := hv)] at hh; cases hh
    by_cases hg : (eViewW m h).headD 0 = 0 ∨ (eViewW m h).headD 0 = 2 ∨ (eViewW m h).headD 0 = 8 ∨
        (eViewW m h).headD 0 = 3
    · rw [rxG1_leaf (hv := hv) (hg := hg)] at hh
      simp only [Option.some.injEq, Prod.mk.injEq] at hh; rw [← hh.2]; exact AFr.refl _
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
      simp only [Option.some.injEq, Prod.mk.injEq] at hh; rw [← hh.2]; exact AFr.refl _
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
      (AFr.of_frame (msetG_frame rfSch rfSch_wf m1 m2 _ _ _ hs))
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
        cases hst : mknF m1 [hd, rdW (m1.arr64 IW) (ctx + 7), rdW (m1.arr64 IW) (ctx + 8)] with
        | none => rw [hst] at hh; simp [rtK2] at hh
        | some p2 =>
        obtain ⟨rr, m2⟩ := p2
        rw [hst, rtK2_some] at hh
        simp only [Option.some.injEq, Prod.mk.injEq] at hh
        obtain ⟨-, -, rfl⟩ := hh
        exact ((ceinternW_afr hc).trans (mknF_afr hst))
      · rw [rxRootW_out (h := hin)] at hh
        simp only [Option.some.injEq, Prod.mk.injEq] at hh; rw [← hh.2.2]; exact AFr.refl _
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
    exact ((posRecW_afr h1).trans (posRecW_afr h2)).trans (pfr _ _ _ _ _ _ _ _ _ hh)
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
    exact (allocW_afr h1).trans (iDsGo _ _ _ _ _ _ _ h2)
  · -- rxDsGoW
    intro m m' f o l q j hh
    by_cases hj : l ≤ j
    · rw [rxDsGoW_done (hj := hj)] at hh; cases hh; exact AFr.refl _
    rw [rxDsGoW_step (hj := hj)] at hh
    cases h1 : rxW n m f (rdW (m.arr64 IW) (o + j)) with
    | none => rw [h1] at hh; simp [dgK] at hh
    | some p1 =>
    obtain ⟨r, m1⟩ := p1
    rw [h1, dgK_some] at hh
    exact ((iRx _ _ _ _ _ h1).trans (set64IW_afr _ _ _)).trans (iDsGo _ _ _ _ _ _ _ hh)
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
    exact (AFr.trans (AFr.of_frame (benterG_frame 218 m)) (iGo _ _ _ _ _ _ h1)).trans
      (AFr.of_frame (MemFrame.setCtl m1 219 _))
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
      exact ((iGo _ _ _ _ _ _ h1).trans (iGo _ _ _ _ _ _ h2)).trans (rpMkW_afr hh)
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
        (rpMkW_afr hh)
    rw [rxNodeW_proj (hg := hg) (h7 := h7)] at hh
    cases h1 : rxGoW n m f f1 z with
    | none => rw [h1] at hh; simp [rxP1] at hh
    | some p1 =>
    obtain ⟨a2, m1⟩ := p1
    rw [h1, rxP1_some] at hh
    exact (iGo _ _ _ _ _ _ h1).trans (rpMkW_afr hh)

-- from IndPosSpec5
theorem rxW_afr {n : Nat} {m m' : Mem} {f e r : Word} (h : rxW n m f e = some (r, m')) : AFr m m' :=
  (posmemo_rx_afr n).2.2.2.2.2.1 _ _ _ _ _ h

-- from IndPosSpec5
theorem rxDsW_afr {n : Nat} {m m' : Mem} {f o l a b : Word} (h : rxDsW n m f o l = some (a, b, m')) : AFr m m' :=
  (posmemo_rx_afr n).2.2.2.1 _ _ _ _ _ _ _ h

-- from IndPos2SpecI

-- from IndPos2SpecI

-- from IndPos2SpecL
theorem nagW_afr : ∀ (n : Nat) (m m' : Mem) (us dO dL gO gL kO kL : Word) (r : List Word),
    nagW n m us dO dL gO gL kO kL = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, _, _, _, h => by simp [nagW] at h
  | n + 1, m, m', us, dO, dL, gO, gL, kO, kL, r, h => by
    unfold nagW nagK1 nagK2 nagK3 at h
    afr_auto h [posRecW_afr, snocW_afr, nagW_afr n _ _ _ _ _ _ _ _ _ _]

-- from IndPos2SpecL
theorem matesW_afr : ∀ (n : Nat) (m m' : Mem) (c off l oO oL : Word) (r : List Word),
    matesW n m c off l oO oL = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, _, h => by simp [matesW] at h
  | n + 1, m, m', c, off, l, oO, oL, r, h => by
    unfold matesW matesK1 matesK2 matesK3 at h
    afr_auto h [snocW_afr, matesW_afr n _ _ _ _ _ _ _ _]

-- from IndPos2SpecL
theorem nboW_afr {n : Nat} {m m' : Mem} {vis c : Word} {r : List Word} (h : nboW n m vis c = some (r, m')) :
    AFr m m' := by
  cases n with
  | zero => simp [nboW] at h
  | succ n =>
  simp only [nboW] at h
  unfold nboK at h
  afr_auto h [envFindW_afr]

-- from IndPos2SpecL
theorem nfmW_afr {n : Nat} {m m' : Mem} {vis c : Word} {r : List Word} (h : nfmW n m vis c = some (r, m')) :
    AFr m m' := by
  cases n with
  | zero => simp [nfmW] at h
  | succ n =>
  simp only [nfmW] at h
  unfold nfmK matesK3 at h
  afr_auto h [nboW_afr, matesW_afr _ _ _ _ _ _ _ _ _]

-- from IndPos2SpecL
theorem fgW_afr : ∀ (n : Nat) (m m' : Mem) (hi us dO dL gO gL pO pL nO nL : Word) (r : List Word),
    fgW n m hi us dO dL gO gL pO pL nO nL = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, h => by simp [fgW] at h
  | n + 1, m, m', hi, us, dO, dL, gO, gL, pO, pL, nO, nL, r, h => by
    unfold fgW fgK1 fgK2 fgK3 fgK4 at h
    afr_auto h [posRecW_afr, snocW_afr, fgW_afr n _ _ _ _ _ _ _ _ _ _ _ _ _]

-- from IndPos2SpecL
theorem fhW_afr : ∀ (n : Nat) (m m' : Mem) (hi gO gL aO aL : Word) (r : List Word),
    fhW n m hi gO gL aO aL = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, _, h => by simp [fhW] at h
  | n + 1, m, m', hi, gO, gL, aO, aL, r, h => by
    unfold fhW fhK1 fhK2 at h
    afr_auto h [fvinternW_afr, snocW_afr, fhW_afr n _ _ _ _ _ _ _ _]

-- from IndPos2SpecL
theorem caW_afr : ∀ (n : Nat) (m m' : Mem) (us dO dL gO gL aO aL : Word) (r : List Word),
    caW n m us dO dL gO gL aO aL = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, _, _, _, h => by simp [caW] at h
  | n + 1, m, m', us, dO, dL, gO, gL, aO, aL, r, h => by
    unfold caW caK1 caK2 at h
    afr_auto h [posRecW_afr, snocW_afr, caW_afr n _ _ _ _ _ _ _ _ _ _]

-- from IndPos2SpecL
theorem new1W_afr {m m' : Mem} {x : Word} {r : List Word} (h : new1W m x = some (r, m')) : AFr m m' :=
  posRecW_afr (new1W_rec h).1

-- from IndPos2SpecL
theorem cpW_afr : ∀ (n : Nat) (m m' : Mem) (hp dO dL : Word) (r : List Word),
    cpW n m hp dO dL = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, h => by simp [cpW] at h
  | n + 1, m, m', hp, dO, dL, r, h => by
    unfold cpW cpK1 cpK2 at h
    afr_auto h [bvbW_afr, fvbF_afr, cpW_afr n _ _ _ _ _ _]

-- from IndPosMemo
theorem piBW_afr : ∀ (n : Nat) (m m' : Mem) (fuel h : Word) (r : List Word), piBW n m fuel h = some (r, m') →
    AFr m m'
  | 0, _, _, _, _, _, hh => by simp [piBW] at hh
  | n + 1, m, m', fuel, h, r, hh => by
    by_cases hf : fuel = 0
    · rw [piBW_fuel0 (hf := hf)] at hh; cases hh
    by_cases hg : h >>> 28 ≠ 6
    · rw [piBW_leaf (hf := hf) (hg := hg)] at hh
      simp only [Option.some.injEq, Prod.mk.injEq] at hh; rw [← hh.2]; exact AFr.refl _
    rw [piBW_node (hf := hf) (hg := hg)] at hh
    by_cases hr : eViewW m h = []
    · rw [hr, piBK1_nil] at hh; cases hh
    rw [piBK1_ne (hr := hr)] at hh
    cases h1 : piBW n m (fuel - 1) ((eViewW m h).getD 2 0) with
    | none => rw [h1] at hh; simp [piBK2] at hh
    | some p1 =>
    obtain ⟨rs, m1⟩ := p1
    rw [h1, piBK2_some] at hh
    cases h2 : consW n m1 ((eViewW m h).getD 1 0) (rs.headD 0) (rs.getD 1 0) with
    | none => rw [h2] at hh; simp [piBK3] at hh
    | some p2 =>
    obtain ⟨r2, m2⟩ := p2
    rw [h2, piBK3_some] at hh
    simp only [Option.some.injEq, Prod.mk.injEq] at hh
    obtain ⟨-, rfl⟩ := hh
    exact (piBW_afr n _ _ _ _ _ h1).trans (consW_afr h2)

-- from IndPosMemo
theorem stripW_afr {m m' : Mem} {ciq : Word} {r : List Word} (h : stripW m ciq = some (r, m')) : AFr m m' := by
  unfold stripW stripK at h
  afr_auto h [stripF_afr]

-- from IndPosMemo
theorem entryW_afr {m m' : Mem} {C ciq : Word} {r : List Word} (h : entryW m C ciq = some (r, m')) :
    AFr m m' := by
  unfold entryW entryK1 entryK2 entryK3 at h
  afr_auto h [stripW_afr, stub_afr, i1F_afr, gafF_afr]

-- from IndPosMemo
theorem ncGoW_afr : ∀ (k : Nat) (m m' : Mem) (vis C co cl cs ol fp : Word) (r : List Word),
    ncGoW k m vis C co cl cs ol fp = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, _, _, _, h => by simp [ncGoW] at h
  | k + 1, m, m', vis, C, co, cl, cs, ol, fp, r, h => by
    unfold ncGoW ncK1 ncK2 ncK3 at h
    afr_auto h [ncGoW_afr k _ _ _ _ _ _ _ _ _ _, envFindW_afr, entryW_afr, posRecW_afr,
      fun h => (set64IW_afr _ _ _).trans (ncGoW_afr k _ _ _ _ _ _ _ _ _ _ h)]

-- from IndPosMemo
theorem ncWf_afr {k : Nat} {m m' : Mem} {vis C co cl : Word} {r : List Word} (h : ncWf k m vis C co cl = some (r, m')) :
    AFr m m' := by
  cases k with
  | zero => simp [ncWf] at h
  | succ k =>
  simp only [ncWf] at h
  unfold ncW ncB at h
  afr_auto h [allocW_afr, ncGoW_afr _ _ _ _ _ _ _ _ _ _ _]

-- from IndPosMemo
theorem ntWf_afr {k : Nat} {m m' : Mem} {vis C : Word} {r : List Word} (h : ntWf k m vis C = some (r, m')) :
    AFr m m' := by
  cases k with
  | zero => simp [ntWf] at h
  | succ k =>
  simp only [ntWf] at h
  unfold ntW ntK1 ntK2 at h
  afr_auto h [envFindW_afr, ncWf_afr]

-- from IndPosMemo
theorem dcGoW_afr : ∀ (n : Nat) (m m' : Mem) (hi off l : Word) (r : List Word),
    dcGoW n m hi off l = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, h => by simp [dcGoW] at h
  | n + 1, m, m', hi, off, l, r, h => by
    unfold dcGoW dcK at h
    afr_auto h [fvbF_afr, dcGoW_afr n _ _ _ _ _ _]

-- from IndPosMemo
theorem dcWf_afr {n : Nat} {m m' : Mem} {ctx off l : Word} {r : List Word} (h : dcWf n m ctx off l = some (r, m')) :
    AFr m m' := by
  cases n with
  | zero => simp [dcWf] at h
  | succ n => exact dcGoW_afr _ _ _ _ _ _ _ h

-- from IndPos2SpecM
theorem cfW_afr {k : Nat} {m m' : Mem} {ctx us dO dL gO gL ns2 aO aL kb : Word} {r : List Word}
    (h : cfW k m ctx us dO dL gO gL ns2 aO aL kb = some (r, m')) : AFr m m' := by
  cases k with
  | zero => simp [cfW] at h
  | succ k =>
  simp only [cfW] at h
  cases h1 : dcWf k m ctx dO dL with
  | none => rw [h1] at h; simp [cfK1] at h
  | some p1 =>
  obtain ⟨r1, m1⟩ := p1
  rw [h1] at h
  refine (dcWf_afr h1).trans ?_
  simp only [cfK1] at h
  split at h
  · unfold cfK2 cfK3 at h
    afr_auto h [nagW_afr _ _ _ _ _ _ _ _ _ _ _, posRecW_afr]
  · simp only [cfK2] at h
    unfold cfK3 at h
    afr_auto h [posRecW_afr]

-- from IndPosMemo
theorem nwsW_afr {n : Nat} {m m' : Mem} {ctx off l po pl : Word} {r : List Word}
    (h : nwsW n m ctx off l po pl = some (r, m')) : AFr m m' := by
  unfold nwsW nwsK at h
  afr_auto h [dcWf_afr]

-- from IndPosMemo
theorem gcW_afr : ∀ (k : Nat) (m m' : Mem) (vis nPc off l oo ol : Word) (r : List Word),
    gcW k m vis nPc off l oo ol = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, _, _, h => by simp [gcW] at h
  | k + 1, m, m', vis, nPc, off, l, oo, ol, r, h => by
    unfold gcW gcK1 gcK2 at h
    afr_auto h [ntWf_afr, appendW_afr, gcW_afr k _ _ _ _ _ _ _ _ _]

-- from IndPosMemo
theorem rhGoW_afr : ∀ (k : Nat) (m m' : Mem) (no nl lv po pl nP q j : Word),
    rhGoW k m no nl lv po pl nP q j = some m' → AFr m m'
  | 0, _, _, _, _, _, _, _, _, _, _, h => by simp [rhGoW] at h
  | k + 1, m, m', no, nl, lv, po, pl, nP, q, j, h => by
    unfold rhGoW rhK1 rhK2 at h
    afr_auto h [posRecW_afr, fun h => (set64IW_afr _ _ _).trans (rhGoW_afr k _ _ _ _ _ _ _ _ _ _ h)]

-- from IndPosMemo
theorem haW_afr {k : Nat} {m m' : Mem} {ctx po pl i : Word} {r : List Word}
    (h : haW k m ctx po pl i = some (r, m')) : AFr m m' := by
  have rh : ∀ {m m' : Mem} {ctx : Word} {r : List Word}, rhWf k m ctx = some (r, m') → AFr m m' := by
    intro m m' ctx r h
    cases k with
    | zero => simp [rhWf] at h
    | succ k =>
    simp only [rhWf] at h
    unfold rhW rhA rhB at h
    afr_auto h [allocW_afr, rhGoW_afr _ _ _ _ _ _ _ _ _ _ _]
  unfold haW haK1 haK2 at h
  afr_auto h [rh, appendW_afr]

-- from IndPosMemo
theorem naW_afr {k : Nat} {m m' : Mem} {vis c : Word} {r : List Word} (h : naW k m vis c = some (r, m')) :
    AFr m m' := by
  unfold naW naK1 naK2 at h
  afr_auto h [envFindW_afr, piBW_afr _ _ _ _ _ _]

-- from IndPosMemo
theorem resHeadW_afr {m m' : Mem} {e : Word} {r : List Word} (h : resHeadW m e = some (r, m')) : AFr m m' := by
  unfold resHeadW resHeadK at h
  afr_auto h [stub_afr, i1F_afr, gafF_afr]

-- from IndPosMemo
theorem hbInsW_afr {m m' : Mem} {e i r x : Word} (h : hbInsW m e i r = some (x, m')) : AFr m m' := by
  unfold hbInsW at h
  cases hs : msetG hbSch m e i r with
  | none => rw [hs] at h; simp at h
  | some m2 =>
  rw [hs] at h
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact AFr.of_frame (msetG_frame hbSch hbSch_wf m m2 e i r hs)

-- from IndPosMemo
theorem hbGoW_afr : ∀ (n : Nat) (m m' : Mem) (f i h r : Word), hbGoW n m f i h = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, hh => by simp [hbGoW] at hh
  | n + 1, m, m', f, i, h, r, hh => by
    have node : ∀ {m m' : Mem} {f i g x y z r : Word}, hbNodeW n f m i g x y z = some (r, m') → AFr m m' := by
      intro m m' f i g x y z r h
      unfold hbNodeW hbO1 hbL1 hbL2 at h
      afr_auto h [hbGoW_afr n _ _ _ _ _ _]
    unfold hbGoW hbK1 hbK2 hbK3 hbK4 at hh
    afr_auto hh [bvbW_afr, node, hbInsW_afr]

-- from IndPosMemo
theorem hbFastW_afr {n : Nat} {m m' : Mem} {i e r : Word} (h : hbFastW n m i e = some (r, m')) : AFr m m' := by
  unfold hbFastW at h
  split at h
  · simp at h
  exact AFr.trans (AFr.of_frame (mclearG_frame hbSch m)) (hbGoW_afr _ _ _ _ _ _ _ h)

-- from IndPosMemo
theorem ncnW_afr {k : Nat} {m m' : Mem} {ctx po pl us dO dL cv closed r : Word}
    (h : ncnW k m ctx po pl us dO dL cv closed = some (r, m')) : AFr m m' := by
  unfold ncnW ncnK1 ncnK2 ncnK3 at h
  afr_auto h [posRecW_afr, rxDsW_afr, rxW_afr]

-- from IndPosMemo
theorem pcrW_afr {k : Nat} {m m' : Mem} {no nl us dO dL hO hL cty : Word} {r : List Word}
    (h : pcrW k m no nl us dO dL hO hL cty = some (r, m')) : AFr m m' := by
  unfold pcrW pcrK1 pcrK2 pcrK3 at h
  afr_auto h [pccW_afr, posRecW_afr, rxW_afr]

/-! ## The walks' memos -/

theorem msetG_afrS {S : MemoSch} (hS : S.WF) (ha : memoFreeA [S.arr] = true) (hc : memoFreeC [S.cs + 1] = true)
    {m m' : Mem} {k1 k2 v : Word} (h : msetG S m k1 k2 v = some m') : AFr m m' :=
  AFr.of_frame (msetG_frame S hS m m' k1 k2 v h) ha hc

theorem mclearG_afrS (S : MemoSch) (hc : memoFreeC [S.cs, S.cs + 1] = true) (m : Mem) :
    AFr m (mclearG S m) :=
  AFr.of_frame (mclearG_frame S m) rfl hc

theorem noW_afr (n : Nat) :
    (∀ (m m' : Mem) (no nl lo hi f h r : Word), noGoW n m no nl lo hi f h = some (r, m') → AFr m m') ∧
    (∀ (m m' : Mem) (no nl lo hi f1 g x y z r : Word), noNodeW n m no nl lo hi f1 g x y z = some (r, m') →
      AFr m m') := by
  induction n with
  | zero => exact ⟨fun _ _ _ _ _ _ _ _ _ h => by simp [noGoW] at h,
      fun _ _ _ _ _ _ _ _ _ _ _ _ h => by simp [noNodeW] at h⟩
  | succ n ih =>
    refine ⟨fun m m' no nl lo hi f h r hh => ?_, fun m m' no nl lo hi f1 g x y z r hh => ?_⟩
    · simp only [noGoW, noG1, noG3, noG4.eq_def, noG5.eq_def, noC.eq_def] at hh
      afr_auto hh [ih.2 _ _ _ _ _ _ _ _ _ _ _ _, msetG_afrS noSch_wf rfl rfl]
    · simp only [noNodeW, noB1.eq_def, noL1.eq_def, noL2.eq_def] at hh
      afr_auto hh [ih.1 _ _ _ _ _ _ _ _ _]

theorem noConstWf_afr {n : Nat} {m m' : Mem} {no nl lo hi e r : Word}
    (h : noConstWf n m no nl lo hi e = some (r, m')) : AFr m m' := by
  cases n with
  | zero => simp [noConstWf] at h
  | succ n =>
  simp only [noConstWf, noConstW] at h
  split at h; · cases h
  refine (mclearG_afrS noSch rfl m).trans ?_
  cases hg : noGoW n (mclearG noSch m) no nl lo hi CWF e with
  | none => rw [hg] at h; simp [noClrK] at h
  | some x =>
  obtain ⟨r1, m1⟩ := x
  rw [hg] at h; simp only [noClrK] at h
  split at h; · cases h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
  exact ((noW_afr n).1 _ _ _ _ _ _ _ _ _ hg).trans (mclearG_afrS noSch rfl m1)

/-- `pi_doms_occ` keeps `AbsOK`. -/
theorem pdoW_afr : ∀ (k : Nat) (m m' : Mem) (no nl lo hi n e : Word) (r : List Word),
    pdoW k m no nl lo hi n e = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, _, _, h => by simp [pdoW] at h
  | k + 1, m, m', no, nl, lo, hi, n, e, r, h => by
    simp only [pdoW, pdoK1.eq_def] at h
    afr_auto h [noConstWf_afr, pdoW_afr k _ _ _ _ _ _ _ _ _]

/-- **`AbsOK` across `nest_uniform_ok`'s callees** (`nuW_ok`'s last conclusion). -/
theorem nuAfr : NuAfr :=
  ⟨fun _ _ _ _ _ _ _ _ _ h => pccW_afr h, pdoW_afr, fun _ _ _ _ _ _ _ _ _ h => noConstWf_afr h⟩

theorem dpW_afr (n : Nat) :
    (∀ (m m' : Mem) (f h r : Word), dpGoW n m f h = some (r, m') → AFr m m') ∧
    (∀ (m m' : Mem) (f1 g x y z r : Word), dpNodeW n m f1 g x y z = some (r, m') → AFr m m') := by
  induction n with
  | zero => exact ⟨fun _ _ _ _ _ h => by simp [dpGoW] at h, fun _ _ _ _ _ _ _ _ h => by simp [dpNodeW] at h⟩
  | succ n ih =>
    refine ⟨fun m m' f h r hh => ?_, fun m m' f1 g x y z r hh => ?_⟩
    · simp only [dpGoW, dpG1, dpG3, dpG4.eq_def, dpG5.eq_def] at hh
      afr_auto hh [ih.2 _ _ _ _ _ _ _ _, msetG_afrS dpSch_wf rfl rfl]
    · simp only [dpNodeW, dpB1.eq_def, dpB2.eq_def, dpL1.eq_def, dpL2.eq_def, dpL3.eq_def, dpP1.eq_def, dpFin] at hh
      afr_auto hh [ih.1 _ _ _ _ _]

theorem wfW_afr {n : Nat} {m m' : Mem} {e r : Word} (h : wfW n m e = some (r, m')) : AFr m m' := by
  simp only [wfW, dpConstW] at h
  split at h; · cases h
  rename_i x heq
  split at heq; · cases heq
  revert heq
  cases hg : dpGoW n (mclearG dpSch m) CWF e with
  | none => simp [dpClrK]
  | some y =>
  obtain ⟨r1, m1⟩ := y
  simp only [dpClrK]
  intro heq
  split at heq; · cases heq
  simp only [Option.some.injEq, Prod.mk.injEq] at heq; obtain ⟨-, rfl⟩ := heq
  split at h; · cases h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
  exact ((mclearG_afrS dpSch rfl m).trans ((dpW_afr n).1 _ _ _ _ _ hg)).trans (mclearG_afrS dpSch rfl m1)

theorem noaW_afr : ∀ (k : Nat) (m m' : Mem) (no nl lo hi off l : Word) (r : List Word),
    noaW k m no nl lo hi off l = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, _, _, h => by simp [noaW] at h
  | k + 1, m, m', no, nl, lo, hi, off, l, r, h => by
    simp only [noaW, noaK.eq_def] at h
    afr_auto h [noConstWf_afr, noaW_afr k _ _ _ _ _ _ _ _ _]

theorem ustWf_afr {n : Nat} {m m' : Mem} {cty nP j r : Word} (h : ustWf n m cty nP j = some (r, m')) :
    AFr m m' := by
  match n, h with
  | n + 2, h =>
    simp only [ustWf, ustW, ustK1.eq_def] at h
    afr_auto h [stripF_afr, hbFastW_afr]

theorem u4W_afr : ∀ (n : Nat) (m m' : Mem) (ko nF cl i : Word) (r : List Word),
    u4W n m ko nF cl i = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, h => by simp [u4W] at h
  | n + 1, m, m', ko, nF, cl, i, r, h => by
    simp only [u4W, u4K.eq_def] at h
    afr_auto h [ustWf_afr, u4W_afr n _ _ _ _ _ _ _]

theorem roW_afr {k : Nat} {m m' : Mem} {ctx hi cur : Word} {r : List Word} (h : roW k m ctx hi cur = some (r, m')) :
    AFr m m' := by
  cases k with
  | zero => simp [roW] at h
  | succ k =>
  simp only [roW, roK0.eq_def, roK1.eq_def, roK2.eq_def] at h
  afr_auto h [resHeadW_afr, stub_afr, gaaF_afr, ftdF_afr, ftdsF_afr, noaW_afr _ _ _ _ _ _ _ _ _ _]

theorem pos2PinW_afr {m m' : Mem} {i : Word} {r : List Word} (h : pos2PinW m i = some (r, m')) : AFr m m' := by
  simp only [pos2PinW] at h
  afr_auto h []

theorem p2ccW_afr {k : Nat} {m m' : Mem} {ctx hp nn dO dL iO iL : Word} {r : List Word}
    (h : p2ccW k m ctx hp nn dO dL iO iL = some (r, m')) : AFr m m' := by
  cases k with
  | zero => simp [p2ccW] at h
  | succ k =>
  simp only [p2ccW, p2ccK1.eq_def, p2ccK2.eq_def] at h
  afr_auto h [noaW_afr _ _ _ _ _ _ _ _ _ _, pos2PinW_afr, cpW_afr _ _ _ _ _ _ _]

theorem pfW_afr {k : Nat} {m m' : Mem} {vis ctx po pl kb hi i aO aL : Word} {r : List Word}
    (h : pfW k m vis ctx po pl kb hi i aO aL = some (r, m')) : AFr m m' := by
  cases k with
  | zero => simp [pfW] at h
  | succ k =>
  simp only [pfW, p2pfK1.eq_def, p2pfK2.eq_def, p2pfK3.eq_def, haWf, naWf] at h
  cases k <;> simp only at h <;> afr_auto h [haW_afr, noaW_afr _ _ _ _ _ _ _ _ _ _, naW_afr]

end L.Ind
