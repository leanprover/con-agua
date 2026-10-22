import ConAgua.Arena.IndPosSpec3

/-! # `replaceFVars` and its maps, continued (lane `indproofs2`, helper `pos`): the frame, the
`ds` loop, the walk, the entry. -/

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem decNK_fields {m : Mem} {k : Nat} {key : NestKey} (h : decNK m k = some key) :
    iwH m k = some key.cname ∧ iwH m (k + 1) = some key.lvls ∧ decAt m (decHL m) (k + 2) = some key.ds := by
  simp only [decNK, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨c, hc, l, hl, ds, hds, h'⟩ := h
  obtain rfl := Option.some.inj h'
  exact ⟨hc, hl, hds⟩

theorem decNH_fields {m : Mem} {w : Nat} {hl : NestHole} (h : decNH m w = some hl) :
    ∃ k, iwN m w = some k ∧ decNK m k = some hl.key := by
  simp only [decNH, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
  obtain ⟨k, hk, key, hkey, b, hb, h'⟩ := h
  obtain rfl := Option.some.inj h'
  exact ⟨k, hk, hkey⟩

theorem iwN_of_get {m : Mem} {i : Nat} {w : Word} (h : (m.arr64 IW)[i]? = some w) : iwN m i = some w.toNat := by
  simp [iwN, nat?, iwA, h]

theorem RxPost.of_fr {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} {vis : Word} {m m1 m2 : Mem}
    {a2 : AState} {M : Std.HashMap (EIdx × Word) EIdx} {G g : Word} (hR : RfInv m M G g)
    (hf : RfFr m m1) (hg : IWGrow m m1) (h : RxPost dn fe vis m1 m2 a2 M G g) : RxPost dn fe vis m m2 a2 M G g := by
  obtain ⟨M2, G2, hS2, hg2, hR2, hk2, hG2⟩ := h
  exact ⟨M2, G2, hS2, hg.trans hg2, hR2, hk2, hG2⟩

theorem RxPost.then {dn : NIdx → Option ConLeche.Name} {fe : IFEnv} {vis : Word} {m m1 m2 : Mem}
    {a1 a2 : AState} {M : Std.HashMap (EIdx × Word) EIdx} {G g : Word} (h : RxPost dn fe vis m m1 a1 M G g)
    (hS : StageR dn vis fe m2 a2) (hg : IWGrow m1 m2) (hf : RfFr m1 m2) : RxPost dn fe vis m m2 a2 M G g := by
  obtain ⟨M1, G1, -, hg1, hR1, hk1, hG1⟩ := h
  exact ⟨M1, G1, hS, hg1.trans hg, hR1.frame hf, hk1, hG1⟩

/-! ### Entering and leaving a bank -/

theorem rfEnter {m : Mem} {M : Std.HashMap (EIdx × Word) EIdx} {G g : Word} (hR : RfInv m M G g)
    (hG : (G + 1).toNat < 2 ^ 32) :
    RfInv (benterG 218 m) M (G + 1) (G + 1) ∧ Bank M (G + 1) ∅ ∧ G.toNat < 2 ^ 32 ∧ g ≤ G := by
  obtain ⟨hMR, hB, hF⟩ := hR
  have hG1 : (G + 1).toNat = G.toNat + 1 := by
    rw [UInt64.toNat_add, show (1 : Word).toNat = 1 from rfl]; have := hB.2.2.2.1; omega
  -- `bank_enter` wants the caller's bank only for its last conjunct
  refine ⟨⟨?_, ?_, fresh_mono M G hF hG1⟩, bank_fresh M G hF hG1, hB.2.2.2.1, hB.2.2.1⟩
  · exact memoRV_frame rfSch rfSch_wf rfK rfV [] [218, 218 + 1] (by simp) (by simp [rfSch]) m _
      (benterG_frame 218 m) (fun _ _ h => h) M hMR
  · obtain ⟨hB1, hB2, hgG, hGl, hsz⟩ := hB
    have hf := benterG_frame 218 m
    have hne : (218 : Word) ≠ 218 + 1 := by decide
    refine ⟨?_, ?_, UInt64.le_refl _, hG, by rw [hf.2.2.1]; exact hsz⟩
    · have h218 : (218 : Word).toNat = 218 := rfl
      simp only [benterG, rdW_set64, size_set64, hB1]
      simp [Ne.symm hne]; omega
    · have h218 : (218 : Word).toNat = 218 := rfl
      simp only [benterG, rdW_set64, size_set64, hB1]
      simp; intro; omega

theorem rfLeave {m : Mem} {M : Std.HashMap (EIdx × Word) EIdx} {G g' g : Word} (hR : RfInv m M G g')
    (hg : g ≤ G) : RfInv (m.set64 CTL 219 g) M G g := by
  obtain ⟨hMR, ⟨hB1, hB2, hgG, hGl, hsz⟩, hF⟩ := hR
  have hf := MemFrame.setCtl m 219 g
  have h218 : (218 : Word).toNat = 218 := rfl
  refine ⟨memoRV_frame rfSch rfSch_wf rfK rfV [] [219] (by simp) (by simp [rfSch]) m _ hf (fun _ _ h => h) M hMR,
    ⟨by rw [hf.2.1 218 (by simp)]; exact hB1, ?_, hg, hGl, by rw [hf.2.2.1]; exact hsz⟩, hF⟩
  rw [show (218 : Word) + 1 = 219 from rfl, rdW_set64]
  have : (219 : Word).toNat < (m.arr64 CTL).size := by
    rw [show (219 : Word).toNat = 219 from rfl]; omega
  simp; intro; simp at this; omega

theorem uint_le_succ {G : Word} (h : G.toNat < 2 ^ 32) : G ≤ G + 1 := by
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_add, show (1 : Word).toNat = 1 from rfl]; omega

section steps
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

/-- **A frame's hole read back, from its hole record on**. -/
theorem frameTail (n : Nat) (hDs : DsOK dn fe vis n) (mh m' : Mem) (a : AState) (ctx po pl n1 h : Word)
    (c : NestCtx) (prog : List NestHole) (H0 : NestHole) (r0 r1 : Word)
    (M : Std.HashMap (EIdx × Word) EIdx) (G g : Word)
    (hk : frK2 n (rdW (mh.arr64 IW) h) (posRecW mh [0, ctx, po, pl, n1]) = some (r0, r1, m'))
    (hS : StageR dn vis fe mh a) (hc : decCtx mh ctx.toNat = some c) (hin : CtxIn mh ctx.toNat (· < iwTop mh))
    (hs : HSl mh po.toNat pl.toNat prog) (hb : c.nP + c.names.length + n1.toNat + 1 < 2 ^ 64)
    (hh : decNH mh h.toNat = some H0) (hhin : NHIn mh h.toNat (· < iwTop mh)) (hR : RfInv mh M G g) :
    ∃ x a', (do
        let ds ← H0.key.ds.mapM fun x => ConRon.Arena.replaceFVars (.holeImg c prog n1.toNat) x
        let hd ← internConstE H0.key.cname H0.key.lvls
        let r ← mkAppN hd ds
        pure (some r) : AM (Option EIdx)).run a = .ok (x, a') ∧ OptE r0 r1 x ∧
      RxPost dn fe vis mh m' a' M G g := by
  have htop : iwTop mh < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  obtain ⟨k, hk0, hkey⟩ := decNH_fields hh
  have hrk : (rdW (mh.arr64 IW) h).toNat = k := rdIW0 hk0
  have hNK := hhin.2.2 k hk0
  cases hrec : posRecW mh [0, ctx, po, pl, n1] with
  | none => rw [hrec] at hk; simp [frK2] at hk
  | some pr =>
  obtain ⟨f, m2⟩ := pr
  rw [hrec, frK2_some] at hk
  obtain ⟨hS2, hg2, hf2, ht2, hget2⟩ := posRecW_stage hrec hS (by simp)
  simp only [List.length_cons, List.length_nil] at ht2
  have hR2 := hR.frame (posRecW_fr hrec)
  -- the new map record
  have g0 := iwN_of_get (by simpa using hget2 0 (by simp))
  have g1 := iwN_of_get (by simpa using hget2 1 (by simp))
  have g2 := iwN_of_get (by simpa using hget2 2 (by simp))
  have g3 := iwN_of_get (by simpa using hget2 3 (by simp))
  have g4 := iwN_of_get (by simpa using hget2 4 (by simp))
  obtain ⟨ec, hci2⟩ := hin.grow hg2
  have hfm : FMOk m2 f.toNat (.holeImg c prog n1.toNat) :=
    ⟨by simpa using g0, by omega, ⟨ctx.toNat, g1, by rw [ec]; exact hc, hci2⟩,
      ⟨po.toNat, pl.toNat, g2, g3, hs.grow hg2⟩, g4, by omega⟩
  -- the key, in `m2`
  obtain ⟨ekey, hNK2⟩ := hNK.agree (RdS.of_grow hg2)
  rw [hkey] at ekey
  obtain ⟨hcn, hlv, hds⟩ := decNK_fields ekey
  obtain ⟨o, l, ho, hl, hdsl⟩ := decAt_some hds
  have htop2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1
  have hkb : k + 4 ≤ iwTop m2 := by have := hNK2.1 3 (by omega); have := hg2.1; omega
  have ro := rdIW (m := m2) (f := rdW (mh.arr64 IW) h) (i := 2) (by rw [hrk]; exact ho) (by omega) (by decide)
  have rl := rdIW (m := m2) (f := rdW (mh.arr64 IW) h) (i := 3) (by rw [hrk]; simpa using hl) (by omega) (by decide)
  simp only [show UInt64.ofNat 2 = (2 : Word) from rfl, show UInt64.ofNat 3 = (3 : Word) from rfl] at ro rl
  have hsl : ∀ j < l, o + j < iwTop m2 := fun j hj =>
    Nat.lt_of_lt_of_le (hNK2.2 o l ho (by simpa using hl) j hj) hg2.1
  cases hdsr : rxDsW n m2 f (rdW (m2.arr64 IW) (rdW (mh.arr64 IW) h + 2)) (rdW (m2.arr64 IW) (rdW (mh.arr64 IW) h + 3)) with
  | none => rw [hdsr] at hk; simp [frK3] at hk
  | some pr3 =>
  obtain ⟨q, l3, m3⟩ := pr3
  rw [hdsr, frK3_some] at hk
  obtain ⟨ys, a3, hrun3, hdec3, hq3, hpost3⟩ := hDs m2 m3 a f _ _ q l3 _ H0.key.ds M G g hdsr hS2 hfm
    (by rw [ro, rl]; exact hdsl) (by rw [ro, rl]; exact hsl) hR2
  obtain ⟨M3, G3, hS3, hg3, hR3, hk3, hG3⟩ := hpost3
  have htop3 : iwTop m3 < 2 ^ 64 := Nat.lt_of_le_of_lt hS3.2.1 hS3.2.2.2.1
  have := hg3.1
  -- the container's head, in `m3`
  have hg23 := hg3
  obtain ⟨hcnH, hcnd⟩ := rd_iwH (m := m3) (p := rdW (mh.arr64 IW) h) (i := 0)
    (by rw [hrk]; simp only [UInt64.toNat_zero, Nat.add_zero]; rw [iwH_agree (RdS.of_grow hg3) (by omega)]; exact hcn)
    (by simp; omega)
  obtain ⟨hlvH, hlvd⟩ := rd_iwH (m := m3) (p := rdW (mh.arr64 IW) h) (i := 1)
    (by rw [hrk]; rw [iwH_agree (RdS.of_grow hg3) (by simp; omega)]; simpa using hlv) (by simp; omega)
  simp only [UInt64.add_zero, show UInt64.ofNat 1 = (1 : Word) from rfl] at hcnH hcnd hlvH hlvd
  cases hci : ceinternW m3 (rdW (m3.arr64 IW) (rdW (mh.arr64 IW) h)) (rdW (m3.arr64 IW) (rdW (mh.arr64 IW) h + 1)) with
  | none => rw [hci] at hk; simp [frK4] at hk
  | some pr4 =>
  obtain ⟨hd, m4⟩ := pr4
  rw [hci] at hk
  by_cases hdb : 4294967296 ≤ hd
  · rw [frK4_big (hb := hdb)] at hk; simp at hk
  rw [frK4_ok (hb := hdb)] at hk
  obtain ⟨a4, hr4, hS4, hg4⟩ := internConst_stage hS3 _ _ hcnH hlvH hci
  have hiw4 : m4.arr64 IW = m3.arr64 IW := lowFr_iw (ceinternW_low hci)
  cases hst : stubM "mk_app_n" m4 [hd, q, l3] with
  | none => rw [hst] at hk; simp [frK5] at hk
  | some pr5 =>
  obtain ⟨rr, m5⟩ := pr5
  rw [hst, frK5_some] at hk
  simp only [Option.some.injEq, Prod.mk.injEq] at hk
  obtain ⟨rfl, rfl, rfl⟩ := hk
  obtain ⟨x, a5, hr5, hS5, hg5, hx1, hx2⟩ := mkAppN_spec dn vis fe hd q l3 (lt_of_notbig hdb) ys m4 m5 a4 rr hst
    ⟨hS4, by simp only [decHL, iwA, hiw4]; exact hdec3⟩
  refine ⟨some x, a5, ?_, ⟨by simp, by rw [← hx2]; rfl⟩, ?_⟩
  · simp only [StateT.run_bind]
    rw [hrun3]
    simp only [except_ok_bind, ConRon.Arena.internConstE, StateT.run_bind]
    rw [← hcnd, ← hlvd, hr4]
    simp only [except_ok_bind, StateT.run_bind]
    rw [show (decE hd : EIdx) = decI hd from rfl, hr5]
    rfl
  · exact ⟨M3, G3, hS5, ((hg2.trans hg3).trans hg4).trans hg5,
      (hR3.frame (RfFr.of_low (ceinternW_low hci))).frame (RfFr.stub (by decide) hst), hk3, hG3⟩

theorem default_hole : (default : NestHole) = ⟨⟨decI 0, decI 0, []⟩, 0⟩ := rfl

theorem frOK_step (n : Nat) (hDs : DsOK dn fe vis n) : FrOK dn fe vis (n + 1) := by
  intro m m' a ctx po pl n1 i c prog r0 r1 M G g h hS hc hin hs hb hR
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  obtain ⟨hpl, hpb, hH⟩ := hs
  unfold frameTwin
  by_cases hn : n1 < pl
  · rw [rxFrameW_in (hn := hn), frK1_some] at h
    have hn' : n1.toNat < pl.toNat := UInt64.lt_iff_toNat_lt.mp hn
    obtain ⟨w, hw, hd, hni⟩ := hH n1.toNat hn'
    have hrw : rdW (m.arr64 IW) (po + n1) = w := by
      simp [rdW, word_add_toNat (show po.toNat + n1.toNat < 2 ^ 64 by omega), hw]
    rw [hrw] at h
    rw [List.getElem?_eq_getElem (by omega)] at hd
    have hgd : prog.getD n1.toNat default = prog[n1.toNat]'(by omega) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    simp only [hgd]
    exact frameTail dn fe vis n hDs m m' a ctx po pl n1 w c prog _ r0 r1 M G g h hS hc hin ⟨hpl, hpb, hH⟩ hb hd
      hni hR
  · rw [rxFrameW_def (hn := hn)] at h
    have hn' : ¬ n1.toNat < pl.toNat := fun e => hn (UInt64.lt_iff_toNat_lt.mpr e)
    have hgd : prog.getD n1.toNat default = default := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    simp only [hgd]
    cases hr1 : posRecW m [0, 0, 0, 0] with
    | none => rw [hr1] at h; simp [frK0] at h
    | some p1 =>
    obtain ⟨k, m1⟩ := p1
    rw [hr1, frK0_some] at h
    obtain ⟨hS1, hg1, hk1, ht1, hget1⟩ := posRecW_stage hr1 hS (by simp)
    cases hr2 : posRecW m1 [k, 0] with
    | none => rw [hr2] at h; simp [frK1] at h
    | some p2 =>
    obtain ⟨hh, m2⟩ := p2
    rw [hr2, frK1_some] at h
    obtain ⟨hS2, hg2, hk2, ht2, hget2⟩ := posRecW_stage hr2 hS1 (by simp)
    simp only [List.length_cons, List.length_nil] at ht1 ht2
    have hkw : ∀ j < 4, (m2.arr64 IW)[k.toNat + j]? = some 0 := fun j hj => by
      rw [hg2.2.2.1 _ (by omega), hget1 j (by simpa using hj)]
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl
    have hdk : decNK m2 k.toNat = some ⟨decI 0, decI 0, []⟩ := by
      have := decNK_of_words (m := m2) (k := k.toNat) (c := 0) (u := 0) (o := 0) (l := 0) (ds := [])
        (by simpa using hkw 0 (by decide)) (by decide) (hkw 1 (by decide)) (by decide) (hkw 2 (by decide))
        (hkw 3 (by decide)) (by simp [decHL, hslice?])
      exact this
    have hdh : decNH m2 hh.toNat = some default := by
      rw [default_hole]
      exact decNH_of_words (by simpa using hget2 0 (by simp)) (hget2 1 (by simp)) hdk
    have hin2 : NHIn m2 hh.toNat (· < iwTop m2) := by
      refine ⟨by omega, by omega, fun k' hk' => ?_⟩
      have : k' = k.toNat := by
        have h0 := iwN_of_get (m := m2) (by simpa using hget2 0 (by simp)); rw [h0] at hk'; exact (Option.some.inj hk').symm
      subst this
      refine ⟨fun j hj => by omega, fun o l ho hl j hj => ?_⟩
      have : l = 0 := by
        have := iwN_of_get (m := m2) (hkw 3 (by decide)); rw [this] at hl; exact (Option.some.inj hl).symm
      omega
    have hg12 := hg1.trans hg2
    obtain ⟨ec, hci2⟩ := hin.grow hg12
    obtain ⟨x, a', hrun, hout, hpost⟩ := frameTail dn fe vis n hDs m2 m' a ctx po pl n1 hh c prog default r0 r1 M G g h
      hS2 (by rw [ec]; exact hc) hci2 (HSl.grow ⟨hpl, hpb, hH⟩ hg12) hb hdh hin2
      ((hR.frame (posRecW_fr hr1)).frame (posRecW_fr hr2))
    exact ⟨x, a', hrun, hout, RxPost.of_fr hR ((posRecW_fr hr1).trans (posRecW_fr hr2)) hg12 hpost⟩

theorem dsOK_step (n : Nat) (hDg : DsGoOK dn fe vis n) : DsOK dn fe vis (n + 1) := by
  intro m m' a f o l q l' fm xs M G g h hS hfm hxs hsl hR
  rw [rxDsW_succ] at h
  cases hal : allocW m l with
  | none => rw [hal] at h; simp [dsA] at h
  | some pr =>
  obtain ⟨q1, m1⟩ := pr
  rw [hal, dsA_some] at h
  obtain ⟨hS1, hg1, hqd, hroom, htop1⟩ := hS.alloc hal
  have hqt : q1.toNat = iwTop m := by simp only [iwTop, hqd]
  cases hgo : rxDsGoW n m1 f o l q1 0 with
  | none => rw [hgo] at h; simp [dsB] at h
  | some m2 =>
  rw [hgo, dsB_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  obtain ⟨ys, a', hrun, hdec, hS', hg', ht', M', G', hR', hk', hG'⟩ := hDg m m1 m2 a f o l q1 0 fm xs [] M G g hgo hS1
    hg1 (by omega) (by omega) hfm hxs hsl (by simp) (by simp [decHL, hslice?]) (hR.frame (allocW_fr hal))
  refine ⟨ys, a', by simpa using hrun, by simpa using hdec, by omega, M', G', hS', hg', hR', hk', hG'⟩

theorem dsGoOK_step (n : Nat) (hRf : RfOK dn fe vis n) (hDg : DsGoOK dn fe vis n) :
    DsGoOK dn fe vis (n + 1) := by
  intro m0 m m' a f o l q j fm xs acc M G g h hS hg0 hq0 hql hfm hxs hsl hj hacc hR
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  have hxl := decHL_length m0 hxs
  have hal := decHL_length m hacc
  by_cases hd : l ≤ j
  · rw [rxDsGoW_done (hj := hd)] at h
    cases h
    have hjl : j.toNat = l.toNat := by have := UInt64.le_iff_toNat_le.mp hd; omega
    refine ⟨[], a, ?_, by rw [← hjl]; simpa using hacc, hS, hg0, Nat.le_refl _, M, G, hR, GKeep.refl _ _,
      UInt64.le_refl _⟩
    rw [List.drop_eq_nil_of_le (by omega)]; rfl
  rw [rxDsGoW_step (hj := hd)] at h
  have hjl : j.toNat < l.toNat := by
    have : ¬ l.toNat ≤ j.toNat := fun e => hd (UInt64.le_iff_toNat_le.mpr e)
    omega
  have hoj := hsl j.toNat hjl
  obtain ⟨hxH, hxd⟩ := rd_iwH (m := m) (p := o) (i := j)
    (by rw [iwH_agree (RdS.of_grow hg0) hoj]; exact decHL_getI hxs _ hjl) (by omega)
  generalize rdW (m.arr64 IW) (o + j) = x at h hxH hxd
  cases hrf : rxW n m f x with
  | none => rw [hrf] at h; simp [dgK] at h
  | some pr =>
  obtain ⟨r, m1⟩ := pr
  rw [hrf, dgK_some] at h
  obtain ⟨a1, hr1, hrH, M1, G1, hS1, hg1, hR1, hk1, hG1⟩ := hRf m m1 a f x fm r M G g hrf hS (hfm.grow hg0) hxH hR
  have hqj : (q + j).toNat = q.toNat + j.toNat := word_add_toNat (by omega)
  have hj1 : (j + 1).toNat = j.toNat + 1 := word_add_toNat (show j.toNat + 1 < 2 ^ 64 by have := l.toNat_lt; omega)
  have hacc1 : decHL m1 q.toNat j.toNat = some acc := by rw [decHL_grow hg1 (by omega)]; exact hacc
  have hsz1 : (m1.arr64 IW).size < 2 ^ 64 := hS1.2.2.2.1
  have hdec2 := decHL_write m1 q j r acc hrH hsz1 (by have := hS1.2.1; have := hg1.1; omega) hacc1
  have hS2 := hS1.set_iw (q + j) r
  have hg02 : IWGrow m0 (m1.set64 IW (q + j) r) := (hg0.trans hg1).set_iw (q + j) r (by omega)
  have ht2 : iwTop (m1.set64 IW (q + j) r) = iwTop m1 := by
    simp only [iwTop]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  obtain ⟨ys, a', hrun, hdec', hS', hg', ht', M', G', hR', hk', hG'⟩ := hDg m0 _ m' a1 f o l q (j + 1) fm xs
    (acc ++ [decE r]) M1 G1 g h hS2 hg02 hq0 (by rw [ht2]; have := hg1.1; omega) hfm hxs hsl
    (by rw [hj1]; omega) (by rw [hj1]; exact hdec2) (hR1.frame (RfFr.set_iw _ _ _))
  refine ⟨decE r :: ys, a', ?_, by simpa using hdec', hS', hg', by have := hg1.1; omega, M', G', hR',
    hk1.trans hk' hG1, UInt64.le_trans hG1 hG'⟩
  rw [List.drop_eq_getElem_cons (show j.toNat < xs.length by omega), List.mapM_cons]
  simp only [StateT.run_bind]
  rw [← hxd, show (decI x : EIdx) = decE x from rfl, hr1]
  simp only [except_ok_bind, StateT.run_bind]
  rw [hj1] at hrun
  rw [hrun]
  rfl

theorem rfOK_step (n : Nat) (hGo : GoOK dn fe vis n) : RfOK dn fe vis (n + 1) := by
  intro m m' a f e fm r M G g h hS hfm he hR
  have hB1 : rdW (m.arr64 CTL) 218 = G := hR.2.1.1
  have hB2 : rdW (m.arr64 CTL) 219 = g := hR.2.1.2.1
  by_cases hb : 4294967296 ≤ rdW (m.arr64 CTL) 218 + 1
  · rw [rxW_big (hb := hb)] at h; simp at h
  rw [rxW_ok (hb := hb), hB2] at h
  have hG : (G + 1).toNat < 2 ^ 32 := by rw [← hB1]; exact lt_of_notbig hb
  obtain ⟨hR1, hbank, hGl, hgG⟩ := rfEnter hR hG
  obtain ⟨hS1, hg1⟩ := StageR.frame_hi hS (benterG_frame 218 m) (by simp) (by simp) (by simp) (by simp)
  cases hgo : rxGoW n (benterG 218 m) f CWF e with
  | none => rw [hgo] at h; simp [rxK1] at h
  | some pr =>
  obtain ⟨r1, m1⟩ := pr
  rw [hgo] at h
  by_cases hrb : 4294967296 ≤ r1
  · rw [rxK1_big (hb := hrb)] at h; simp at h
  rw [rxK1_ok (hb := hrb)] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨mp', a', M1, G1, hrun, hS2, hg2, hR2, -, hkx, hG1⟩ := hGo _ m1 a f CWF e fm ∅ _ M (G + 1) (G + 1) hgo hS1
    (hfm.grow hg1) he hR1 hbank
  have hGG : G ≤ G + 1 := uint_le_succ hGl
  obtain ⟨hS3, hg3⟩ := StageR.frame_hi hS2 (MemFrame.setCtl m1 219 g) (by simp) (by simp) (by simp) (by simp)
  refine ⟨a', ?_, lt_of_notbig hrb, M1, G1, hS3, (hg1.trans hg2).trans hg3,
    rfLeave hR2 (UInt64.le_trans hgG (UInt64.le_trans hGG hG1)), fun k gen hgen => hkx k gen
      (UInt64.le_trans hgen hGG) (fun e => by
        subst e; rw [UInt64.le_iff_toNat_le, UInt64.toNat_add, show (1 : Word).toNat = 1 from rfl] at hgen; omega),
    UInt64.le_trans hGG hG1⟩
  rw [ConRon.Arena.replaceFVars.eq_1, StateT.run_bind, ← CWF_eq, hrun]
  rfl

end steps

end L.Ind
