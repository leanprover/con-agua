import ConAgua.Arena.RecClassSpecK

/-!
# `RecClass`: `ClassGen.minorTy` — the conclusion and the composition (lane `indproofs2`, helper `rec2`)
-/


noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem pdW_afr : ∀ (n : Nat) (m m' : Mem) (xo xl e : Word) (r : List Word),
    pdW n m xo xl e = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, h => by simp [pdW] at h
  | n + 1, m, m', xo, xl, e, r, h => by
    simp only [pdW, pdK1.eq_def, pdK2.eq_def, pdK3.eq_def] at h
    afr_auto h [i1F_afr, pdW_afr n _ _ _ _ _ _, consW_afr]

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-- The model of `class_gen_minor_ty_concl2` simulates the twin's tail of `minorTy`. -/
theorem c2W_sim (n : Nat) (m : Mem) (a : AState) (g c d nPc fo fl ihso ihsl rao ral capp : Word)
    (G : ClassGen) (NPC : Nat) (fvs ihs ra : List EIdx) (hS : StageR dn vis fe m a)
    (hG : DecB (fun m => decCG m g.toNat) m G) (hns : G.nP + G.slots.length < 2 ^ 64)
    (hnpc : nPc.toNat = NPC)
    (hfvs : decHL m fo.toNat fl.toNat = some fvs) (hfb : fo.toNat + fl.toNat ≤ iwTop m)
    (hihs : decHL m ihso.toNat ihsl.toNat = some ihs) (hib : ihso.toNat + ihsl.toNat ≤ iwTop m)
    (hra : decHL m rao.toNat ral.toNat = some ra) (hrb : rao.toNat + ral.toNat ≤ iwTop m) (hcapp : H capp)
    (hA : AbsOK m) :
    RSim (c2W (n + 1) m g c d nPc fo fl ihso ihsl rao ral capp) (do
      let mc ← G.motVar c.toNat
      let concl ← mkAppN mc (List.drop NPC ra ++ [decI capp])
      let fbs ← List.mapM G.binder fvs
      let r ← ConRon.Arena.closeTelescope (fbs ++ ihs) d.toNat concl
      pure (some r)) a (fun b a' x => KP dn vis fe m decOE b a' x ∧ AbsOK b.2) := by
  rw [c2W.arm1]
  refine RSim.bind (K := c2W.k_class_gen_mot_var n d nPc fo fl ihso ihsl rao ral capp) rfl
    (RSim.withF (rec2SimMotVar n hS c hG hns) (fun _ hb => rec2MotVarF_afr hb)) ?_
  rintro ⟨r1, m1⟩ mc a1 - ⟨⟨hS1, hg1, hmcH, hmcd⟩, hf1⟩
  dsimp only at hS1 hg1 hmcH hmcd
  subst hmcd
  have hk1 : c2W.k_class_gen_mot_var n d nPc fo fl ihso ihsl rao ral capp (some (r1, m1)) =
      c2W.k_sl_snoc n d fo fl ihso ihsl (r1.headD 0)
        (snocW n m1 (if nPc < ral then rao + nPc else rao) (if nPc < ral then ral - nPc else 0) capp) := by
    by_cases hc : nPc < ral
    · rw [c2W.k_class_gen_mot_var.arm1 (hc1 := hc)]; simp only [c2W.j1, hc, ↓reduceIte]
    · rw [c2W.k_class_gen_mot_var.arm2 (hc1 := hc)]; simp only [c2W.j1, hc, ↓reduceIte]
  rw [hk1]
  have hra1 : decHL m1 rao.toNat ral.toNat = some ra := by rw [decHL_grow hg1 hrb]; exact hra
  have hrb1 := Nat.le_trans hrb hg1.1
  have hsl : decHL m1 (if nPc < ral then rao + nPc else rao).toNat (if nPc < ral then ral - nPc else 0).toNat =
      some (ra.drop NPC) ∧
      (if nPc < ral then rao + nPc else rao).toNat + (if nPc < ral then ral - nPc else 0).toNat ≤ iwTop m1 := by
    have hlen := decHL_length m1 hra1
    by_cases hc : nPc < ral
    · have hc' : nPc.toNat < ral.toNat := UInt64.lt_iff_toNat_lt.mp hc
      have e1 : (rao + nPc).toNat = rao.toNat + nPc.toNat := by
        rw [UInt64.toNat_add]; have := hS1.lt64 hrb1; omega
      have e2 : (ral - nPc).toNat = ral.toNat - nPc.toNat := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt hc)]
      simp only [ite_eq_left hc, e1, e2]
      rw [← hnpc]
      exact ⟨decHL_drop nPc.toNat hra1 (by omega), by omega⟩
    · have hc' : ral.toNat ≤ nPc.toNat := by
        have : ¬ nPc.toNat < ral.toNat := fun x => hc (UInt64.lt_iff_toNat_lt.mpr x)
        omega
      simp only [ite_eq_right hc]
      rw [List.drop_eq_nil_of_le (by rw [← hnpc]; omega)]
      exact ⟨by simp [decHL, hslice?], by simp; omega⟩
  refine RSim.lstep (K := c2W.k_sl_snoc n d fo fl ihso ihsl (r1.headD 0)) rfl fun ⟨r2, m2⟩ h2 => ?_
  obtain ⟨hr2, hd2, hg2, -, -, ht2⟩ := snocW_dec h2 hS1.2.2.2.1 hS1.2.2.2.2.2 hsl.2 hcapp hsl.1
  have hS2 := snocW_stage h2 hS1
  have hA2 := snocW_afr h2 (hf1 hA)
  rw [c2W.k_sl_snoc.arm1, hr2]
  simp only [List.headD_cons, List.tail_cons]
  refine RSim.bind (K := c2W.k_mk_app_n_f n d fo fl ihso ihsl) rfl
    (RSim.withF ((mknF_ok dn vis fe _ _ _ hmcH (ra.drop NPC ++ [decI capp])).sim ⟨hS2, hd2⟩)
      (fun _ hb => mknF_afr hb)) ?_
  rintro ⟨r3, m3⟩ body a3 - ⟨⟨hS3, hg3, hbH, hbd⟩, hf3⟩
  dsimp only at hS3 hg3 hbH hbd
  subst hbd
  rw [c2W.k_mk_app_n_f.arm1, rec2MapM_genBinder]
  have hg13 := hg1.trans (hg2.trans hg3)
  rcases n with _ | n
  · intro b hb; simp [mcW, c2W.k_class_gen_minor_ty_close] at hb
  rw [mcW.arm1]
  refine RSim.bind (K := fun o => c2W.k_class_gen_minor_ty_close (mcW.k_fvar_type_ds n ihso ihsl d (r3.headD 0) o)) rfl
    (RSim.withF ((ftdsF_ok dn vis fe _ _ fvs).sim
      ⟨hS3, by rw [decHL_grow hg13 hfb]; exact hfvs, fun _ => Nat.le_trans hfb hg13.1⟩) (fun _ hb => ftdsF_afr hb)) ?_
  rintro ⟨r4, m4⟩ fbs a4 - ⟨⟨hS4, hg4, hfbs, hfbb⟩, hf4⟩
  dsimp only at hS4 hg4 hfbs hfbb
  simp only [getD_zero, Nat.zero_add, getD_one] at hfbs hfbb
  rw [mcW.k_fvar_type_ds.arm1]
  have hg14 := hg13.trans hg4
  refine RSim.lstep (K := fun o => c2W.k_class_gen_minor_ty_close (mcW.k_sl_append n d (r3.headD 0) o)) rfl fun ⟨r5, m5⟩ h5 => ?_
  obtain ⟨hS5, hg5, hd5, hb5⟩ := rec2AppendW_dec h5 hS4 (decHL_decB hfbs hfbb)
    (by rw [decHL_grow hg14 hib]; exact hihs) (Nat.le_trans hib hg14.1)
  by_cases hov : d + r5.tail.headD 0 < d
  · rw [mcW.k_sl_append.abort1 (hc1 := hov)]; exact RSim.none
  rw [mcW.k_sl_append.arm1 (hc1 := hov)]
  have hdl : d.toNat + (r5.tail.headD 0).toNat < 2 ^ 64 := by
    have := nctAddNowrap (a := r5.tail.headD 0) (b := d) (by rwa [UInt64.add_comm]); omega
  refine RSim.bind (K := fun o => c2W.k_class_gen_minor_ty_close (mcW.k_close_telescope o)) rfl (Q1 := fun b a' x =>
    StageR dn vis fe b.2 a' ∧ IWGrow m5 b.2 ∧ decW0E b.2 b.1 x ∧ AbsOK b.2) ?_ ?_
  · rintro ⟨r6, m6⟩ h6
    obtain ⟨x, a', hrun, hS', hg, hx, hA6⟩ := closeW_ok n dn fe vis m5 m6 a4 _ _ d _ _ r6 h6 hS5 hbH hd5
      (hS5.lt64 hb5) hb5 hdl (appendW_afr h5 (hf4 (hf3 hA2)))
    exact ⟨x, a', hrun, hS', hg, hx, hA6⟩
  rintro ⟨r6, m6⟩ x a6 - ⟨hS6, hg6, hx, hA6⟩
  simp only [mcW.k_close_telescope.arm1, c2W.k_class_gen_minor_ty_close.arm1]
  exact RSim.pure_some ⟨⟨hS6, hg14.trans (hg5.trans hg6), rfl, by simpa [decW0E] using hx⟩, hA6⟩

end sims

/-- The constructor's name word, read through its record. -/
theorem rec2CCName {m : Mem} {x : Word} {X : ClassCtor} (hX : decCC m x.toNat = some X)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    ∃ w, rdW (m.arr64 EREC) (rdW (m.arr64 IW) x) = w ∧ H w ∧ decI w = X.cv.name := by
  simp only [decCC, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hX
  obtain ⟨q, hq, cv, hcv, nF, hnF, ks, hks, y4, hy4, y5, hy5, rfl⟩ := hX
  obtain ⟨eq, tq⟩ := rec2RdN (w := x) (k := 0) (by simpa using hq) hsz
  simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero] at eq
  simp only [decCVp, decCV, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hcv
  obtain ⟨nm, hnm, lps, hlps, ty, hty, rfl⟩ := hcv
  obtain ⟨w, hw, hwl, hwd⟩ := hd?_some hnm
  exact ⟨w, by rw [eq]; exact rdW_of_get? tq.symm hw, hwl, hwd.symm⟩

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

theorem cW_sim (n : Nat) (m : Mem) (a : AState) (g c x d lvls ds0 dl0 nPc fo fl res ihso ihsl : Word)
    (G : ClassGen) (X : ClassCtor) (LV : LsIdx) (NPC : Nat) (DS fvs ihs : List EIdx) (hS : StageR dn vis fe m a)
    (hG : DecB (fun m => decCG m g.toNat) m G) (hns : G.nP + G.slots.length < 2 ^ 64)
    (hX : DecB (fun m => decCC m x.toNat) m X) (hres : H res) (hlv : H lvls) (hlvd : decI lvls = LV)
    (hds : DecB (fun m => (decHL m ds0.toNat dl0.toNat : Option (List EIdx))) m DS) (hnpc : nPc.toNat = NPC)
    (hfvs : decHL m fo.toNat fl.toNat = some fvs) (hfb : fo.toNat + fl.toNat ≤ iwTop m)
    (hihs : decHL m ihso.toNat ihsl.toNat = some ihs) (hib : ihso.toNat + ihsl.toNat ≤ iwTop m)
    (hA : AbsOK m) :
    RSim (cW (n + 1) m g c x d lvls ds0 dl0 nPc fo fl res ihso ihsl) (do
      let ra ← getAppArgs coreWalkFuel (decI res)
      let cc ← internE (.const X.cv.name LV)
      let capp ← mkAppN cc (DS ++ fvs)
      let mc ← G.motVar c.toNat
      let concl ← mkAppN mc (List.drop NPC ra ++ [capp])
      let fbs ← List.mapM G.binder fvs
      let r ← ConRon.Arena.closeTelescope (fbs ++ ihs) d.toNat concl
      pure (some r)) a (fun b a' x => KP dn vis fe m decOE b a' x ∧ AbsOK b.2) := by
  rw [cW.arm1]
  refine RSim.bind (K := cW.k_get_app_args_f n g c x d lvls ds0 dl0 nPc fo fl ihso ihsl) rfl
    (RSim.withF (simGetAppArgs hS hres) (fun _ hb => gaaF_afr hb)) ?_
  rintro ⟨r1, m1⟩ ra a1 - ⟨⟨hS1, hg1, hra, hrb⟩, hf1⟩
  dsimp only at hS1 hg1 hra hrb
  simp only [getD_zero, Nat.zero_add, getD_one] at hra hrb
  rw [cW.k_get_app_args_f.arm1]
  obtain ⟨nw, enw, hnwH, hnwd⟩ := rec2CCName (hX.stab (decCC_mono _) m1 hg1) hS1.2.2.2.1
  rw [enw]
  subst hlvd
  refine RSim.bind (K := cW.k_intern_const n g c d ds0 dl0 nPc fo fl ihso ihsl (r1.headD 0) (r1.tail.headD 0)) rfl
    (Q1 := fun b a' x => StageR dn vis fe b.2 a' ∧ IWGrow m1 b.2 ∧ x = decE b.1 ∧ AbsOK b.2) ?_ ?_
  · rintro ⟨cc, m2⟩ h2
    obtain ⟨a', hrun, hS', hg⟩ := internConst_stage hS1 nw lvls hnwH hlv h2
    rw [hnwd] at hrun
    exact ⟨decE cc, a', hrun, hS', hg, rfl, ceinternW_afr h2 (hf1 hA)⟩
  rintro ⟨cc, m2⟩ ccx a2 - ⟨hS2, hg2, rfl, hA2⟩
  dsimp only at hS2 hg2
  by_cases hbig : 4294967296 ≤ cc
  · rw [cW.k_intern_const.abort1 (hc1 := hbig)]; exact RSim.none
  rw [cW.k_intern_const.arm1 (hc1 := hbig)]
  have hccH : H cc := by
    have : ¬ (4294967296 : Word).toNat ≤ cc.toNat := fun x => hbig (UInt64.le_iff_toNat_le.mpr x)
    simp at this; exact this
  have hg12 := hg1.trans hg2
  refine RSim.lstep (K := cW.k_sl_append n g c d nPc fo fl ihso ihsl (r1.headD 0) (r1.tail.headD 0) cc) rfl
    fun ⟨r3, m3⟩ h3 => ?_
  obtain ⟨hS3, hg3, hd3, hb3⟩ := rec2AppendW_dec h3 hS2 (hds.grow (OMono.decHL _ _) hg12)
    (by rw [decHL_grow hg12 hfb]; exact hfvs) (Nat.le_trans hfb hg12.1)
  rw [cW.k_sl_append.arm1]
  refine RSim.bind (K := cW.k_mk_app_n_f n g c d nPc fo fl ihso ihsl (r1.headD 0) (r1.tail.headD 0)) rfl
    (RSim.withF ((mknF_ok dn vis fe _ _ _ hccH (DS ++ fvs)).sim ⟨hS3, hd3⟩) (fun _ hb => mknF_afr hb)) ?_
  rintro ⟨r4, m4⟩ capp a4 - ⟨⟨hS4, hg4, hcH, hcd⟩, hf4⟩
  dsimp only at hS4 hg4 hcH hcd
  subst hcd
  rw [cW.k_mk_app_n_f.arm1]
  have hg14 := hg12.trans (hg3.trans hg4)
  rcases n with _ | n
  · intro b hb; simp [c2W, cW.k_class_gen_minor_ty_concl2] at hb
  refine RSim.bindPure (K := cW.k_class_gen_minor_ty_concl2) rfl (c2W_sim n m4 a4 g c d nPc fo fl ihso ihsl _ _ _ G NPC fvs ihs ra hS4
    (hG.grow (decCG_mono _) hg14) hns hnpc (by rw [decHL_grow hg14 hfb]; exact hfvs) (Nat.le_trans hfb hg14.1)
    (by rw [decHL_grow hg14 hib]; exact hihs) (Nat.le_trans hib hg14.1)
    (by rw [decHL_grow (hg2.trans (hg3.trans hg4)) hrb]; exact hra) (Nat.le_trans hrb (hg2.trans (hg3.trans hg4)).1)
    hcH (hf4 (appendW_afr h3 hA2))) ?_
  rintro ⟨r5, m5⟩ o a5 - ⟨⟨hS5, hg5, ho⟩, hA5⟩
  rw [cW.k_class_gen_minor_ty_concl2.arm1]
  refine RSim.pure_some ⟨⟨hS5, hg14.trans hg5, ?_⟩, hA5⟩
  cases o with
  | none => exact ho
  | some e => obtain ⟨h1, h2⟩ := ho; exact ⟨by simpa using h1, by simpa [decW0E] using h2⟩

end sims

theorem rec2CC_parts {m : Mem} {x : Nat} {X : ClassCtor} (hX : decCC m x = some X) :
    iwN m (x + 1) = some X.nF ∧ iwH m (x + 4) = some X.tyD ∧ iwH m (x + 5) = some X.tyN := by
  simp only [decCC, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hX
  obtain ⟨q, hq, cv, hcv, nF, hnF, ks, hks, y4, hy4, y5, hy5, rfl⟩ := hX
  exact ⟨hnF, hy4, hy5⟩

/-- The decoded result of `class_gen_minor_ty`. -/
theorem mnW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) (m : Mem)
    (a : AState) (g c x d : Word) (G : ClassGen) (X : ClassCtor) (hS : StageR dn vis fe m a)
    (hG : DecB (fun m => decCG m g.toNat) m G) (hns : G.nP + G.slots.length < 2 ^ 64)
    (hX : DecB (fun m => decCC m x.toNat) m X) (hA : AbsOK m) :
    RSim (mnW n m g c x d) (ConRon.Arena.ClassGen.minorTy G c.toNat X d.toNat) a
      (fun b a' x => KP dn vis fe m decOE b a' x ∧ AbsOK b.2) := by
  rcases n with _ | n
  · exact RSim.none
  rw [mnW_eq]
  unfold ConRon.Arena.ClassGen.minorTy
  have hsz := hS.2.2.2.1
  obtain ⟨-, hgt, ⟨o3, l3, h3, h4, hcls⟩, -⟩ := rec2CG_parts hG
  obtain ⟨e3, t3⟩ := rec2RdN (w := g) (k := 3) h3 hsz
  obtain ⟨e4, t4⟩ := rec2RdN (w := g) (k := 4) h4 hsz
  simp only [show UInt64.ofNat 3 = (3 : Word) from rfl, show UInt64.ofNat 4 = (4 : Word) from rfl] at e3 e4
  rw [e3, e4]
  have htop := hS.2.1
  have hb3 : o3 + l3 < 2 ^ 64 := by
    by_cases hl : l3 = 0
    · have := iwN_rdW h3 (by omega); omega
    · have := rec2DecB_PL_top hcls hl; omega
  refine RSim.bind (K := mnK1 n g c x d) rfl (RSim.withF (rec2SimTMA dn vis fe n m a _ _ c G.cls hS
    (by rw [t3, t4]; exact hcls) (by rw [t3, t4]; exact hb3)) (fun _ hb => tmaW_afr hb)) ?_
  rintro ⟨r1, m1⟩ tm a1 - ⟨⟨hS1, hg1, hTM, hds⟩, hf1⟩
  have hA1 := hf1 hA
  dsimp only at hS1 hg1 hTM hds
  rw [mnK1_some]
  have hsz1 := hS1.2.2.2.1
  obtain ⟨-, hlv, ⟨o, l, ho, hl, -⟩, hnpc, -⟩ := rec2DecTM_parts hTM
  have hds1 := hds o l ho hl
  obtain ⟨vl, evl, hvl, dvl⟩ := iwH_rdW_at (w := r1.headD 0) (k := 1) hlv hsz1
  obtain ⟨eo, to⟩ := rec2RdN (w := r1.headD 0) (k := 2) ho hsz1
  obtain ⟨el, tl⟩ := rec2RdN (w := r1.headD 0) (k := 3) hl hsz1
  obtain ⟨en, tn⟩ := rec2RdN (w := r1.headD 0) (k := 4) hnpc hsz1
  simp only [show UInt64.ofNat 1 = (1 : Word) from rfl, show UInt64.ofNat 2 = (2 : Word) from rfl,
    show UInt64.ofNat 3 = (3 : Word) from rfl, show UInt64.ofNat 4 = (4 : Word) from rfl] at evl eo el en
  rw [evl, eo, el, en]
  rw [← to, ← tl] at hds1
  rcases n with _ | n
  · intro b hb; simp [bW, cK4] at hb
  rw [bW.arm1]
  -- the constructor's words
  have hX1 := hX.stab (decCC_mono _) m1 hg1
  obtain ⟨hnF, htyD, htyN⟩ := rec2CC_parts hX1
  obtain ⟨enF, tnF⟩ := rec2RdN (w := x) (k := 1) hnF hsz1
  obtain ⟨vD, evD, hvD, dvD⟩ := iwH_rdW_at (w := x) (k := 4) htyD hsz1
  simp only [show UInt64.ofNat 1 = (1 : Word) from rfl, show UInt64.ofNat 4 = (4 : Word) from rfl] at enF evD
  rw [enF, evD]
  have ho := simOpenPisF (k := UInt64.ofNat X.nF) (i := d) hS1 hA1 hvD
  rw [tnF, dvD] at ho
  refine RSim.bind (K := fun o => cK4 (bW.k_open_pis_at_fvars_f n g c x d vl _ _ _ o)) rfl ho ?_
  rintro ⟨r2, m2⟩ o2 a2 - ⟨⟨hS2, hg2, ho2⟩, hA2⟩
  dsimp only at hS2 hg2 ho2
  rcases o2 with _ | p2
  · rw [bW.k_open_pis_at_fvars_f.arm1 (hc1 := ho2)]; exact RSim.pure_some ⟨⟨hS2, hg1.trans hg2, rfl⟩, hA2⟩
  obtain ⟨fvs, res⟩ := p2
  obtain ⟨h21, ⟨hfvs, hfb⟩, hrH, hrd⟩ := ho2
  simp only [getD_one, getD_two, Nat.reduceAdd] at hfvs hfb
  simp only [drop3_headD] at hrH hrd
  rw [bW.k_open_pis_at_fvars_f.arm2 (hc1 := by rw [h21]; decide)]
  have hg12 := hg1.trans hg2
  have hX2 := hX.stab (decCC_mono _) m2 hg12
  obtain ⟨-, -, htyN2⟩ := rec2CC_parts hX2
  obtain ⟨vN, evN, hvN, dvN⟩ := iwH_rdW_at (w := x) (k := 5) htyN2 hS2.2.2.2.1
  simp only [show UInt64.ofNat 5 = (5 : Word) from rfl] at evN
  rw [evN]
  refine RSim.bind (K := fun o => cK4 (bW.k_target_pi_doms_with n g c x d vl _ _ _ _ _ _ o)) rfl (Q1 := fun b a' x =>
    StageR dn vis fe b.2 a' ∧ IWGrow m2 b.2 ∧ PdRes b.2 b.1 x ∧ AbsOK b.2) ?_ ?_
  · rintro ⟨r3, m3⟩ h3
    obtain ⟨res', a', hrun, hS', hg, hres⟩ := pdW_ok dn vis fe n m2 m3 a2 _ _ vN r3 fvs h3 hS2 hvN hfvs
      (hS2.lt64 hfb) hfb
    rw [dvN] at hrun
    exact ⟨res', a', hrun, hS', hg, hres, pdW_afr _ _ _ _ _ _ _ h3 hA2⟩
  rintro ⟨r3, m3⟩ o3 a3 - ⟨hS3, hg3, ho3, hA3⟩
  dsimp only at hS3 hg3 ho3
  rcases o3 with _ | ws
  · rw [bW.k_target_pi_doms_with.arm1 (hc1 := ho3)]; exact RSim.pure_some ⟨⟨hS3, hg12.trans hg3, rfl⟩, hA3⟩
  obtain ⟨h31, hws, hwb⟩ := ho3
  rw [bW.k_target_pi_doms_with.arm2 (hc1 := by rw [h31]; decide)]
  have hg13 := hg12.trans hg3
  have hX3 := hX.grow (decCC_mono _) hg13
  obtain ⟨hnF3, -, -⟩ := rec2CC_parts (hX3.get (decCC_mono _))
  obtain ⟨enF3, -⟩ := rec2RdN (w := x) (k := 1) hnF3 hS3.2.2.2.1
  simp only [show UInt64.ofNat 1 = (1 : Word) from rfl] at enF3
  rw [enF3]
  have hi := misW_sim dn vis fe G X hns g x d (UInt64.ofNat X.nF) _ _ _ _ ws fvs tnF n m3 a3 0 0 hS3
    (hG.grow (decCG_mono _) hg13) hX3 hws hwb (by rw [decHL_grow hg3 hfb]; exact hfvs)
    (Nat.le_trans hfb hg3.1) (by simp) (by simp) hA3
  simp only [UInt64.toNat_zero] at hi
  have hr : rec2Recs X 0 = (List.range X.nF).filterMap (fun i =>
      match X.kinds.getD i ClassField.ordinary with
      | ClassField.recursive t tele => some (i, t, tele)
      | ClassField.ordinary => none) := rec2Recs_zero X
  refine RSim.bind (K := fun o => cK4 (bW.k_class_gen_minor_ty_ihs_go n g c x d vl _ _ _ _ _ _ o)) rfl
    (hr.symm ▸ hi : RSim _ (ConRon.Arena.ClassGen.minorTy.ihsGo G X d.toNat fvs ws 0 _) a3 _) ?_
  rintro ⟨r4, m4⟩ o4 a4 - ⟨hS4, hg4, ho4, hA4⟩
  dsimp only at hS4 hg4 ho4
  rcases o4 with _ | ihs
  · rw [bW.k_class_gen_minor_ty_ihs_go.arm1 (hc1 := ho4)]; exact RSim.pure_some ⟨⟨hS4, hg13.trans hg4, rfl⟩, hA4⟩
  obtain ⟨h41, hihs, hib⟩ := ho4
  rw [bW.k_class_gen_minor_ty_ihs_go.arm2 (hc1 := by rw [h41]; decide)]
  have hg14 := hg13.trans hg4
  rcases n with _ | n
  · intro b hb; simp [cW, bW.k_class_gen_minor_ty_concl, cK4] at hb
  have hc := cW_sim (dn := dn) (vis := vis) (fe := fe) n m4 a4 g c x d vl _ _ _ _ _ _ _ _ G X tm.lvls tm.nPc
    tm.ds fvs ihs hS4 (hG.grow (decCG_mono _) hg14) hns (hX.grow (decCC_mono _) hg14) hrH hvl dvl
    (hds1.grow (OMono.decHL _ _) (hg2.trans (hg3.trans hg4))) tn (by rw [decHL_grow (hg3.trans hg4) hfb]; exact hfvs)
    (Nat.le_trans hfb (hg3.trans hg4).1) hihs hib hA4
  rw [hrd] at hc
  refine RSim.bindPure (K := fun o => cK4 (bW.k_class_gen_minor_ty_concl o)) rfl hc ?_
  rintro ⟨r5, m5⟩ o5 a5 - ⟨⟨hS5, hg5, ho5⟩, hA5⟩
  simp only [bW.k_class_gen_minor_ty_concl.arm1, cK4_some]
  refine RSim.pure_some ⟨⟨hS5, hg14.trans hg5, ?_⟩, hA5⟩
  cases o5 with
  | none => exact ho5
  | some e => obtain ⟨h1, h2⟩ := ho5; exact ⟨by simpa using h1, by simpa [decW0E] using h2⟩

/-- **`class_gen_minor_ty` refines `ClassGen.minorTy`** (through `open_pis_at_fvars_f`'s real refinement and its other callees:
`get_app_args`, `mk_app_n_f`, `fvar_type_ds`, `close_telescope`'s `abstract1_fast`, …; the generator
and the constructor record decoded below the tops). -/
@[refines ConRon.Arena.ClassGen.minorTy]
theorem classGenMinorTy_refines (p : Prog) (hp : MnProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (g c x d : Word) (G : ClassGen) (X : ClassCtor)
    (hS : StageR dn vis fe s₀.mem a₀) (hG : DecB (fun m => decCG m g.toNat) s₀.mem G)
    (hns : G.nP + G.slots.length < 2 ^ 64) (hX : DecB (fun m => decCC m x.toNat) s₀.mem X)
    (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_gen_minor_ty" [g, c, x, d]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.ClassGen.minorTy G c.toNat X d.toNat) a₀ ∧
      KP dn vis fe s₀.mem decOE (r, s'.mem) (AM.st (ConRon.Arena.ClassGen.minorTy G c.toNat X d.toNat) a₀)
        (AM.res (ConRon.Arena.ClassGen.minorTy G c.toNat X d.toNat) a₀) ∧ AbsOK s'.mem; ⊤⦄ :=
  triple_post (classGenMinorTy_spec p hp n s₀ g c x d) fun _ _ ⟨hl, hw⟩ =>
    let h := (mnW_sim dn vis fe n _ a₀ g c x d G X hS hG hns hX hA).am hw
    ⟨hl, h.1, h.2.1, h.2.2⟩

end L.Ind
