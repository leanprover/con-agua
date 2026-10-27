import ConAgua.Arena.RecClassSpec.MkTMWAfr
import ConAgua.Arena.RecClassSpec.Rec2AppendWDec
import ConAgua.Arena.RecClassSpec.Rec2SimTMA
import ConAgua.Arena.RecClassSpec.PiBWRoom

/-!
# MjW

`rec2DecB_HL_stab`, `rec2SimInstW`, `rec2Major_eq`, `mjtW_sim`, `mjtW_afr`, `mjoW_sim` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem rec2DecB_HL_stab {k : IdxKind} {m m' : Mem} {o l : Nat} {xs : List (Idx k)}
    (h : DecB (fun m => (decHL m o l : Option (List (Idx k)))) m xs) (hg : IWGrow m m') :
    decHL m' o l = some xs :=
  h.stab (OMono.decHL o l) m' hg

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem} {a : AState}

/-- `inst_pis_with` on a slice decoded below the tops (possibly empty, at any offset). -/
theorem rec2SimInstW (n : Nat) (hS : StageR dn vis fe m a) {ao al e : Word} (he : H e) {args : List EIdx}
    (hd : DecB (fun m => (decHL m ao.toNat al.toNat : Option (List EIdx))) m args) :
    RSim (instW n m ao al e) (ConRon.Arena.instPisWith args (decI e)) a (KP dn vis fe m decOE) := by
  rintro ⟨r, m'⟩ h
  have hd0 : decHL m ao.toNat al.toNat = some args := hd.get (OMono.decHL _ _)
  by_cases hal : al = 0
  · cases n with
    | zero => simp [instW] at h
    | succ n =>
    rw [instW_nil n m ao al e hal] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have : args = [] := by
      have h0 : al.toNat = 0 := by rw [hal]; rfl
      rw [h0] at hd0; simpa [decHL, hslice?] using hd0.symm
    subst this
    exact ⟨some (decI e), a, rfl, hS, IWGrow.refl _, rfl, he, rfl⟩
  · have hl : al.toNat ≠ 0 := fun h0 => hal (UInt64.toNat_inj.mp (by simpa using h0))
    have ht := rec2DecB_HL_top hd hl
    obtain ⟨x, a', hrun, hS', hg, hout⟩ := instW_ok n dn fe vis m m' a ao al e args r h hS he hd0
      (hS.lt64 ht) ht
    exact ⟨x, a', hrun, hS', hg, hout⟩

end sims

theorem rec2Major_eq (g : ClassGen) (c d : Nat) : ConRon.Arena.ClassGen.major g c d = (do
    let ci ← ConRon.Arena.targetMajorAt g.cls c
    let fty ← ConRon.Arena.exprGetD g.formerTys c
    match ← ConRon.Arena.instPisWith ci.ds fty with
    | none => pure none
    | some ty => rec2MajOpen ci.ind ci.lvls ci.ds ci.nIdx ty d) := rfl

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

theorem mjtW_sim (n : Nat) (m : Mem) (a : AState) (ind lvls ds0 dl0 fo fl : Word) (I : NIdx) (U : LsIdx)
    (ds ifs : List EIdx) (hS : StageR dn vis fe m a) (hI : ind.toNat < 2 ^ 32 ∧ decI ind = I)
    (hU : lvls.toNat < 2 ^ 32 ∧ decI lvls = U)
    (hds : DecB (fun m => (decHL m ds0.toNat dl0.toNat : Option (List EIdx))) m ds)
    (hifs : decHL m fo.toNat fl.toNat = some ifs) (hfb : fo.toNat + fl.toNat ≤ iwTop m) :
    RSim (mjtW n m ind lvls ds0 dl0 fo fl) (rec2MajTail I U ds ifs) a (KP dn vis fe m decOLE) := by
  rcases n with _ | n
  · exact RSim.none
  rw [mjtW.arm1]
  obtain ⟨hI1, rfl⟩ := hI
  obtain ⟨hU1, rfl⟩ := hU
  refine RSim.bind (K := mjtW.k_intern_const n ds0 dl0 fo fl) rfl (Q1 := fun b a' x => StageR dn vis fe b.2 a' ∧
    IWGrow m b.2 ∧ x = decE b.1) ?_ ?_
  · rintro ⟨hd, m1⟩ h1
    obtain ⟨a', hrun, hS', hg⟩ := internConst_stage hS ind lvls hI1 hU1 h1
    exact ⟨decE hd, a', hrun, hS', hg, rfl⟩
  rintro ⟨hd, m1⟩ x a1 - ⟨hS1, hg1, rfl⟩
  by_cases hbig : 4294967296 ≤ hd
  · rw [mjtW.k_intern_const.abort1 (hc1 := hbig)]; exact RSim.none
  rw [mjtW.k_intern_const.arm1 (hc1 := hbig)]
  have hH : H hd := by
    have : ¬ (4294967296 : Word).toNat ≤ hd.toNat := fun x => hbig (UInt64.le_iff_toNat_le.mpr x)
    simp at this; exact this
  refine RSim.lstep (K := mjtW.k_sl_append fo fl hd) rfl fun ⟨r2, m2⟩ h2 => ?_
  obtain ⟨hS2, hg2, hd2, hb2⟩ := rec2AppendW_dec h2 hS1 (hds.grow (OMono.decHL _ _) hg1)
    (by rw [decHL_grow hg1 hfb]; exact hifs) (Nat.le_trans hfb hg1.1)
  rw [mjtW.k_sl_append.arm1]
  refine RSim.bind (K := mjtW.k_mk_app_n_f fo fl) rfl
    ((mknF_ok dn vis fe hd (r2.headD 0) (r2.tail.headD 0) hH (ds ++ ifs)).sim ⟨hS2, hd2⟩) ?_
  rintro ⟨r3, m3⟩ maj a3 - ⟨hS3, hg3, hmaj⟩
  rw [mjtW.k_mk_app_n_f.arm1]
  have hg := hg1.trans (hg2.trans hg3)
  refine RSim.pure_some ⟨hS3, hg, rfl, ⟨?_, ?_⟩, ?_⟩
  · show decHL m3 fo.toNat fl.toNat = some ifs
    rw [decHL_grow hg hfb]; exact hifs
  · show fo.toNat + fl.toNat ≤ iwTop m3
    exact Nat.le_trans hfb hg.1
  · exact hmaj

theorem mjtW_afr {n : Nat} {m m' : Mem} {ind lvls ds0 dl0 fo fl : Word} {r : List Word}
    (h : mjtW n m ind lvls ds0 dl0 fo fl = some (r, m')) : AFr m m' := by
  rcases n with _ | n
  · simp [mjtW] at h
  simp only [mjtW, mjtW.k_intern_const.eq_def, mjtW.k_sl_append.eq_def, mjtW.k_mk_app_n_f.eq_def] at h
  afr_auto h [ceinternW_afr, appendW_afr, mknF_afr]

theorem mjoW_sim (n : Nat) (m : Mem) (a : AState) (ind lvls ds0 dl0 nIdx ty d : Word) (I : NIdx) (U : LsIdx)
    (ds : List EIdx) (hS : StageR dn vis fe m a) (hI : ind.toNat < 2 ^ 32 ∧ decI ind = I)
    (hU : lvls.toNat < 2 ^ 32 ∧ decI lvls = U)
    (hds : DecB (fun m => (decHL m ds0.toNat dl0.toNat : Option (List EIdx))) m ds) (hty : H ty)
    (hA : AbsOK m) :
    RSim (mjoW n m ind lvls ds0 dl0 nIdx ty d) (rec2MajOpen I U ds nIdx.toNat (decI ty) d.toNat) a
      (fun b a' x => KP dn vis fe m decOLE b a' x ∧ AbsOK b.2) := by
  rcases n with _ | n
  · exact RSim.none
  rw [mjoW.arm1]
  refine RSim.bind (K := mjoW.k_open_pis_at_fvars_f n ind lvls ds0 dl0) rfl (simOpenPisF hS hA hty) ?_
  rintro ⟨r4, m4⟩ o a4 - ⟨⟨hS4, hg4, ho⟩, hA4⟩
  rcases o with _ | p4
  · rw [mjoW.k_open_pis_at_fvars_f.arm1 (hc1 := ho)]; exact RSim.pure_some ⟨⟨hS4, hg4, rfl⟩, hA4⟩
  obtain ⟨ifs, body⟩ := p4
  obtain ⟨h41, ⟨hifs, hfb⟩, -⟩ := ho
  simp only [getD_one, getD_two, Nat.reduceAdd] at hifs hfb
  rw [mjoW.k_open_pis_at_fvars_f.arm2 (hc1 := by rw [h41]; decide)]
  refine RSim.bindPure (K := mjoW.k_class_gen_major_tail) rfl (RSim.withF (mjtW_sim n m4 a4 ind lvls ds0 dl0 _ _ I U ds ifs hS4 hI hU
    (hds.grow (OMono.decHL _ _) hg4) hifs hfb) (fun _ hb => mjtW_afr hb)) ?_
  rintro ⟨r5, m5⟩ x a5 - ⟨⟨hS5, hg5, hx⟩, hf5⟩
  rw [mjoW.k_class_gen_major_tail.arm1]
  refine RSim.pure_some ⟨⟨hS5, hg4.trans hg5, ?_⟩, hf5 hA4⟩
  rcases x with _ | p
  · exact hx
  obtain ⟨h1, ⟨h2, h3⟩, h4⟩ := hx
  refine ⟨by simpa using h1, ⟨by simpa [getD_one, getD_two] using h2, by simpa [getD_one, getD_two] using h3⟩, ?_⟩
  simpa [decW0E, drop3_headD] using h4

end sims

theorem mjW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) (m : Mem)
    (a : AState) (g c d : Word) (G : ClassGen) (hS : StageR dn vis fe m a)
    (hG : DecB (fun m => decCG m g.toNat) m G) (hA : AbsOK m) :
    RSim (mjW n m g c d) (ConRon.Arena.ClassGen.major G c.toNat d.toNat) a
      (fun b a' x => KP dn vis fe m decOLE b a' x ∧ AbsOK b.2) := by
  rcases n with _ | n
  · exact RSim.none
  rw [mjW.arm1, rec2Major_eq]
  have hsz := hS.2.2.2.1
  have htop := hS.2.1
  obtain ⟨-, hgt, ⟨o3, l3, h3, h4, hcls⟩, ⟨o5, l5, h5, h6, hft⟩, -, -⟩ := rec2CG_parts hG
  obtain ⟨e3, t3⟩ := rec2RdN (w := g) (k := 3) h3 hsz
  obtain ⟨e4, t4⟩ := rec2RdN (w := g) (k := 4) h4 hsz
  simp only [show UInt64.ofNat 3 = (3 : Word) from rfl, show UInt64.ofNat 4 = (4 : Word) from rfl] at e3 e4
  rw [e3, e4]
  have hb3 : o3 + l3 < 2 ^ 64 := by
    by_cases hl : l3 = 0
    · have := iwN_rdW h3 (by omega); omega
    · have := rec2DecB_PL_top hcls hl; omega
  refine RSim.bind (K := mjW.k_target_major_at n g c d) rfl (RSim.withF (rec2SimTMA dn vis fe n m a _ _ c G.cls hS
    (by rw [t3, t4]; exact hcls) (by rw [t3, t4]; exact hb3)) (fun _ hb => tmaW_afr hb)) ?_
  rintro ⟨r1, m1⟩ tm a1 - ⟨⟨hS1, hg1, hTM, hds⟩, hf1⟩
  dsimp only at hS1 hg1 hTM hds
  rw [mjW.k_target_major_at.arm1]
  have hsz1 := hS1.2.2.2.1
  obtain ⟨hind, hlv, ⟨o, l, ho, hl, -⟩, -, hni⟩ := rec2DecTM_parts hTM
  have hds1 := hds o l ho hl
  obtain ⟨vi, evi, hvi, dvi⟩ := iwH_rdW_at (w := r1.headD 0) (k := 0) (by simpa using hind) hsz1
  obtain ⟨vl, evl, hvl, dvl⟩ := iwH_rdW_at (w := r1.headD 0) (k := 1) hlv hsz1
  obtain ⟨eo, to⟩ := rec2RdN (w := r1.headD 0) (k := 2) ho hsz1
  obtain ⟨el, tl⟩ := rec2RdN (w := r1.headD 0) (k := 3) hl hsz1
  obtain ⟨en, tn⟩ := rec2RdN (w := r1.headD 0) (k := 5) hni hsz1
  simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero, show UInt64.ofNat 1 = (1 : Word) from rfl,
    show UInt64.ofNat 2 = (2 : Word) from rfl, show UInt64.ofNat 3 = (3 : Word) from rfl,
    show UInt64.ofNat 5 = (5 : Word) from rfl] at evi evl eo el en
  rw [evi, evl, eo, el, en]
  -- the former types, at `m1`
  have e5' : iwN m1 (g.toNat + 5) = some o5 := by rw [iwN_grow hg1 (by omega)]; exact h5
  have e6' : iwN m1 (g.toNat + 6) = some l5 := by rw [iwN_grow hg1 (by omega)]; exact h6
  obtain ⟨e5, t5⟩ := rec2RdN (w := g) (k := 5) e5' hsz1
  obtain ⟨e6, t6⟩ := rec2RdN (w := g) (k := 6) e6' hsz1
  simp only [show UInt64.ofNat 5 = (5 : Word) from rfl, show UInt64.ofNat 6 = (6 : Word) from rfl] at e5 e6
  rw [e5, e6]
  have hb5 : o5 + l5 < 2 ^ 64 := by
    by_cases hl5 : l5 = 0
    · have := iwN_rdW h5 (by omega); omega
    · have := rec2DecB_HL_top hft hl5; omega
  refine RSim.bind (K := mjW.k_expr_get_d n d _ _ _ _ _) rfl (RSim.withF (rec2SimExprGetD n hS1
    (by rw [t5, t6]; exact rec2DecB_HL_stab hft hg1) (by rw [t5, t6]; exact hb5)) (fun _ hb => exprGetDF_afr hb)) ?_
  rintro ⟨r2, m2⟩ fty a2 - ⟨⟨hS2, hg2, hfH, hfd⟩, hf2⟩
  dsimp only at hS2 hg2 hfH hfd
  subst hfd
  rw [mjW.k_expr_get_d.arm1]
  have hds2 := hds1.grow (OMono.decHL _ _) hg2
  rw [← to, ← tl] at hds2
  refine RSim.bind (K := mjW.k_inst_pis_with n d _ _ _ _ _) rfl (RSim.withF (rec2SimInstW n hS2 hfH hds2)
    (fun _ hb => instW_afr _ _ _ _ _ _ _ hb)) ?_
  rintro ⟨r3, m3⟩ oty a3 - ⟨⟨hS3, hg3, ho3⟩, hf3⟩
  have hA3 : AbsOK m3 := hf3 (hf2 (hf1 hA))
  dsimp only at hS3 hg3 ho3
  rcases oty with _ | ty
  · rw [mjW.k_inst_pis_with.arm1 (hc1 := ho3)]; exact RSim.pure_some ⟨⟨hS3, hg1.trans (hg2.trans hg3), rfl⟩, hA3⟩
  obtain ⟨h31, htyH, htyd⟩ := ho3
  rw [mjW.k_inst_pis_with.arm2 (hc1 := by rw [h31]; decide)]
  have hm := mjoW_sim (dn := dn) (vis := vis) (fe := fe) n m3 a3 vi vl _ _ (UInt64.ofNat tm.nIdx)
    (r3.tail.headD 0) d tm.ind tm.lvls tm.ds hS3 ⟨hvi, dvi⟩ ⟨hvl, dvl⟩ (hds2.grow (OMono.decHL _ _) hg3) htyH hA3
  rw [tn, htyd] at hm
  refine RSim.bindPure (K := mjW.k_class_gen_major_open) rfl hm ?_
  rintro ⟨r5, m5⟩ x a5 - ⟨⟨hS5, hg5, hx⟩, hA5⟩
  rw [mjW.k_class_gen_major_open.arm1]
  refine RSim.pure_some ⟨⟨hS5, hg1.trans (hg2.trans (hg3.trans hg5)), ?_⟩, hA5⟩
  rcases x with _ | p
  · exact hx
  obtain ⟨h1, ⟨h2, h3⟩, h4⟩ := hx
  refine ⟨by simpa using h1, ⟨by simpa [getD_one, getD_two] using h2, by simpa [getD_one, getD_two] using h3⟩, ?_⟩
  simpa [decW0E, drop3_headD] using h4

/-! ## `class_gen_motive_ty` -/

theorem rec2MapM_classBinder : ∀ xs : List EIdx, xs.mapM ConRon.Arena.classBinder = fvarTypeDs xs
  | [] => rfl
  | x :: xs => by
    simp only [List.mapM_cons, fvarTypeDs, ConRon.Arena.classBinder, rec2MapM_classBinder xs]

/-- The decoded result of an `Option EIdx` producer. -/
theorem motW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) (m : Mem)
    (a : AState) (g c d : Word) (G : ClassGen) (hS : StageR dn vis fe m a)
    (hG : DecB (fun m => decCG m g.toNat) m G) (hA : AbsOK m) :
    RSim (motW n m g c d) (ConRon.Arena.ClassGen.motiveTy G c.toNat d.toNat) a
      (fun b a' x => KP dn vis fe m decOE b a' x ∧ AbsOK b.2) := by
  rcases n with _ | n
  · exact RSim.none
  rw [motW.arm1]
  unfold ConRon.Arena.ClassGen.motiveTy
  refine RSim.bind (K := motW.k_class_gen_major n g d) rfl
    (mjW_sim dn vis fe n m a g c d G hS hG hA) ?_
  rintro ⟨r1, m1⟩ o1 a1 - ⟨⟨hS1, hg1, ho1⟩, hA1⟩
  dsimp only at hS1 hg1 ho1
  rcases o1 with _ | p1
  · rw [motW.k_class_gen_major.arm1 (hc1 := ho1)]; exact RSim.pure_some ⟨⟨hS1, hg1, rfl⟩, hA1⟩
  obtain ⟨ifs, maj⟩ := p1
  obtain ⟨h11, ⟨hifs, hfb⟩, hmH, hmd⟩ := ho1
  simp only [getD_one, getD_two, Nat.reduceAdd] at hifs hfb
  simp only [drop3_headD] at hmH hmd
  rw [motW.k_class_gen_major.arm2 (hc1 := by rw [h11]; decide)]
  obtain ⟨-, hgt, -, -, hel, -⟩ := rec2CG_parts hG
  obtain ⟨ve, eve, hve, dve⟩ := iwH_rdW_at (w := g) (k := 11) (by rw [iwH_grow hg1 (show g.toNat + 11 < iwTop m by omega)]; exact hel) hS1.2.2.2.1
  simp only [show UInt64.ofNat 11 = (11 : Word) from rfl] at eve
  rw [eve]
  refine RSim.bind (K := motW.k_intern_sort n d _ _ _) rfl (Q1 := fun b a' x => StageR dn vis fe b.2 a' ∧
    IWGrow m1 b.2 ∧ x = decE b.1 ∧ AbsOK b.2) ?_ ?_
  · rintro ⟨srt, m2⟩ h2
    obtain ⟨a', hrun, hS', hg⟩ := internSort_stage hS1 ve hve h2
    rw [dve] at hrun
    exact ⟨decE srt, a', hrun, hS', hg, rfl, sointernW_afr h2 hA1⟩
  rintro ⟨srt, m2⟩ x a2 - ⟨hS2, hg2, rfl, hA2⟩
  by_cases hbig : 4294967296 ≤ srt
  · rw [motW.k_intern_sort.abort1 (hc1 := hbig)]; exact RSim.none
  rw [motW.k_intern_sort.arm1 (hc1 := hbig)]
  refine RSim.bind (K := motW.k_mk_forall n d _ _) rfl (Q1 := fun b a' x => StageR dn vis fe b.2 a' ∧
    IWGrow m2 b.2 ∧ x = decE b.1 ∧ AbsOK b.2) ?_ ?_
  · rintro ⟨b, m3⟩ h3
    obtain ⟨a', hrun, hS', hg⟩ := mkForall_stage hS2 _ srt h3
    exact ⟨decE b, a', by rw [← hmd]; exact hrun, hS', hg, rfl, mkForallW_afr h3 hA2⟩
  rintro ⟨b, m3⟩ x a3 - ⟨hS3, hg3, rfl, hA3⟩
  by_cases hbig3 : 4294967296 ≤ b
  · rw [motW.k_mk_forall.abort1 (hc1 := hbig3)]; exact RSim.none
  rw [motW.k_mk_forall.arm1 (hc1 := hbig3)]
  have hbH : H b := by
    have : ¬ (4294967296 : Word).toNat ≤ b.toNat := fun x => hbig3 (UInt64.le_iff_toNat_le.mpr x)
    simp at this; exact this
  have hg13 := hg1.trans (hg2.trans hg3)
  rw [rec2MapM_classBinder]
  refine RSim.bind (K := motW.k_fvar_type_ds n d b) rfl (RSim.withF ((ftdsF_ok dn vis fe _ _ ifs).sim
      ⟨hS3, by rw [decHL_grow (hg2.trans hg3) hfb]; exact hifs, fun _ => Nat.le_trans hfb (hg2.trans hg3).1⟩) (fun _ hb => ftdsF_afr hb)) ?_
  rintro ⟨r4, m4⟩ bs a4 - ⟨⟨hS4, hg4, hbs, hbb⟩, hf4⟩
  dsimp only at hS4 hg4 hbs hbb
  simp only [getD_zero, Nat.zero_add, getD_one] at hbs hbb
  by_cases hov : d + r4.tail.headD 0 < d
  · rw [motW.k_fvar_type_ds.abort1 (hc1 := hov)]; exact RSim.none
  rw [motW.k_fvar_type_ds.arm1 (hc1 := hov)]
  have hdl : d.toNat + (r4.tail.headD 0).toNat < 2 ^ 64 := by
    have := nctAddNowrap (a := r4.tail.headD 0) (b := d) (by rwa [UInt64.add_comm]); omega
  refine RSim.bind (K := motW.k_close_telescope) rfl (Q1 := fun b a' x => StageR dn vis fe b.2 a' ∧ IWGrow m4 b.2 ∧
    decW0E b.2 b.1 x ∧ AbsOK b.2) ?_ ?_
  · rintro ⟨r5, m5⟩ h5
    obtain ⟨x, a', hrun, hS', hg, hx, hA5⟩ := closeW_ok n dn fe vis m4 m5 a4 _ _ d b bs r5 h5 hS4 hbH hbs
      (hS4.lt64 hbb) hbb hdl (hf4 hA3)
    exact ⟨x, a', hrun, hS', hg, hx, hA5⟩
  rintro ⟨r5, m5⟩ x a5 - ⟨hS5, hg5, hx, hA5⟩
  rw [motW.k_close_telescope.arm1]
  exact RSim.pure_some ⟨⟨hS5, hg13.trans (hg4.trans hg5), rfl, by simpa [decW0E] using hx⟩, hA5⟩

end L.Ind

end
