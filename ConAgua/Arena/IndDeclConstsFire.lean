module

public import ConAgua.Arena.IndDeclConstsDrop
public import ConAgua.Arena.DeclCanonView2
import ConAgua.Arena.RecClassSpec.IhW
import ConAgua.Arena.IndSumSpec.TsrW
import ConAgua.L.ModelGen
import ConRon.Bridge.Grind
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import all ConAgua.Arena.IndDeclConsts
import ConAgua.Arena.IndSumSpec.DecHLTake
import ConAgua.L.WordOff
import ConAgua.Arena.RecClassSpec.MjProg
import ConAgua.Arena.RecLayout.CIDec

@[expose] public section

/-!
# A declaration's constants: how a recursor's rules fire (lane `ronsync2`, stage 3)

`rec_fire(p, rc)` refines con-ron's `recFire` (`Arena/Install.lean`): `.plain` (kind `0`) at a
member major, else the major's domain read off the recursor's type (`strip_pis`, `e_view`,
`get_app_fn_f`, `view_ls`, `get_app_args_f`) and its parameters dropped below the index binders
(`expr_drop_vars_list`): `.nested` (kind `1`) at two fresh `IW` slices of handles.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The lookups of `rec_fire`. -/
structure FireProg (p : Prog) : Prop extends DropProg p where
  strip : StripProg p
  view : p.lookup "e_view" = some eView
  ad : AdF p
  lsNode : p.lookup "ls_node" = some lsNode
  poolCopy : p.lookup "pool_copy" = some poolCopy
  viewLs : p.lookup "view_ls" = some viewLsL
  rf : p.lookup "rec_fire" = some recFire

l_model rf_spec (p : Prog) (hP : FireProg p)
  fns [hP.rf ↦ rfW list]
  specs [stripPis_specF p hP.strip n, eView_spec p hP.view n, gafF_spec p hP.ad n,
    viewLs_specW p hP.lsNode hP.alloc hP.poolCopy hP.viewLs n, gaaF_spec p hP.ad n, edvl_spec p hP.toDropProg n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000



/-- How a rule fires, as `(kind, lvls.off, lvls.len, pins.off, pins.len)`. -/
def decRF (m : Mem) (r : List Word) : IRecRuleFire → Prop
  | .plain => r = [0, 0, 0, 0, 0]
  | .nested lv ps => r.headD 0 = 1 ∧ decRL (fun m => decHL m) 1 m r lv ∧ decRL (fun m => decHL m) 3 m r ps
  | .levels _ => False

/-- A word of `IW` below the top, read at `o + w`. -/
theorem iwRd {m : Mem} {o w : Word} {v : Nat} (h : iwN (truncM m) (o.toNat + w.toNat) = some v) :
    (rdW (m.arr64 IW) (o + w)).toNat = v ∧ o.toNat + w.toNat < iwTop m := by
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨hlt, -⟩ := L.Ind.iwN_truncM_some h
  have e : (o + w).toNat = o.toNat + w.toNat := by rw [UInt64.toNat_add]; omega
  rw [← e] at h
  obtain ⟨x, hx, hxv, -⟩ := rdW_of_iwN_truncM h
  exact ⟨by rw [hx, hxv], hlt⟩

theorem iwLt {m : Mem} {o w : Word} {v : Nat} (h : iwN (truncM m) (o.toNat + w.toNat) = some v) :
    (o + w).toNat < iwTop m := by
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨hlt, -⟩ := L.Ind.iwN_truncM_some h
  rw [UInt64.toNat_add]; omega

/-- **`rec_fire` refines `recFire`** (its model, from the stage relation): the fire's kind and
its two `IW` slices of handles below the pool's top. -/
theorem rfW_ok {p : Prog} (hP : FireProg p) {vis : Word} {fe : IFEnv} {n : Nat} {m m' : Mem}
    {a : AState} {pp rc : Word} {bs : BlockShape} {rs : RecShape} {r : List Word}
    (hS : StageR vis fe m a) (hq : DecB (fun m => decBS m pp.toNat) m bs)
    (hrs : DecB (fun m => decRS m rc.toNat) m rs) (h : rfW p n m pp rc = some (r, m')) :
    ∃ f a', (ConRon.Arena.recFire bs rs).run a = .ok (f, a') ∧ KeepPost vis fe decRF m m' a' r f := by
  rcases n with _ | n
  · simp [rfW] at h
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hrs0 : decRS (truncM m) rc.toNat = some rs := hrs
  obtain ⟨⟨aw, haw, hcv⟩, hrP, hmI, htgt, -, -⟩ := decRS_some hrs0
  obtain ⟨htgtW, -⟩ := iwRd (o := rc) (w := 3) (by simpa using htgt)
  obtain ⟨hmIW, -⟩ := iwRd (o := rc) (w := 2) (by simpa using hmI)
  obtain ⟨hrPW, -⟩ := iwRd (o := rc) (w := 1) (by simpa using hrP)
  obtain ⟨cw, hcw, hcwv, -⟩ := rdW_of_iwN_truncM haw
  have hqt : decBS (truncM m) pp.toNat = some bs := hq
  obtain ⟨hmem, -⟩ := decBS_some hqt
  obtain ⟨o, l, -, hl, hg⟩ := decAt_some hmem
  obtain ⟨hkW, -⟩ := iwRd (o := pp) (w := 1) (by simpa using hl)
  have hk : l = bs.k := by rw [BlockShape.k, decPL_length _ hg]
  simp only [rfW] at h
  by_cases hlt : rdW (m.arr64 IW) (rc + 3) < rdW (m.arr64 IW) (pp + 1)
  · rw [ite_eq_left hlt] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have : rs.tgt < bs.k := by rw [← htgtW, ← hk, ← hkW]; exact UInt64.lt_iff_toNat_lt.mp hlt
    exact ⟨.plain, a, by simp [ConRon.Arena.recFire, this]; rfl, hS, IWGrow.refl m, rfl⟩
  rw [ite_eq_right hlt] at h
  have hnlt : ¬ rs.tgt < bs.k := by
    rw [← htgtW, ← hk, ← hkW]; exact fun c => hlt (UInt64.lt_iff_toNat_lt.mpr c)
  -- the recursor's type
  rw [hcw] at h
  have hcvE : decCV (erecP m) aw = some rs.cvR := decCVp_truncM hcv
  obtain ⟨-, -, ⟨w, hw, hw32, hwd⟩⟩ := decCV_words hcvE
  have h3 : (cw + 3).toNat = aw + 3 := by
    have := erecP_lt64 hw; rw [UInt64.toNat_add, hcwv]; simp; omega
  have hw' : rdW (m.arr64 (tierA EREC ((cw + 3) >>> 40))) (cw + 3 &&& 1099511627775) = w :=
    L.Arena.erRd_of _ _ (by rw [h3]; exact hw)
  rw [hw'] at h
  generalize hmIw : rdW (m.arr64 IW) (rc + 2) = mIw at h hmIW
  rcases hs : stripF 6 m [mIw, w] with _ | ⟨r1, m1⟩ <;> rw [hs] at h
  · simp [rfW.k_strip_pis] at h
  obtain ⟨x1, a1, hrun1, hS1, hg1, hd1⟩ := stripF_pis_ok vis fe mIw w hw32 m m1 a r1 hs hS
  rw [hmIW, ← hwd] at hrun1
  have e1 : ∀ (k : Option (List EIdx × EIdx) → AM IRecRuleFire),
      (ConRon.Arena.stripPis rs.mI rs.cvR.type >>= k).run a = (k x1).run a1 := by
    intro k; simp only [StateT.run_bind, hrun1]; rfl
  rcases x1 with _ | ⟨ls, e⟩
  · -- `strip_pis` declines: `.plain`
    simp only [decOLE] at hd1
    simp only [rfW.k_strip_pis, hd1, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨.plain, a1, ?_, hS1, hg1, rfl⟩
    simp only [ConRon.Arena.recFire, hnlt, ↓reduceIte]
    rw [e1]; rfl
  obtain ⟨hd10, -, hd1e⟩ := hd1
  obtain ⟨hew32, hewd⟩ := hd1e
  rw [L.headD_drop_three] at hew32 hewd
  have hne0 : ¬ r1.headD 0 = 0 := by rw [hd10]; decide
  simp only [rfW.k_strip_pis, hne0, ↓reduceIte] at h
  generalize hew : r1.tail.tail.tail.headD 0 = ew at h hew32 hewd
  have hftag : (decE ew).tag = ETag.forallE ↔ tagW ew = 6 := decE_tag_eq ew hew32 6 (by decide)
  by_cases h6 : tagW ew ≠ 6
  · rw [ite_eq_left h6] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have : ¬ (decE ew).tag = ETag.forallE := fun c => h6 (hftag.mp c)
    refine ⟨.plain, a1, ?_, hS1, hg1, rfl⟩
    simp only [ConRon.Arena.recFire, hnlt, ↓reduceIte]
    rw [e1]
    simp only [← hewd]
    have e3 : (decI ew : EIdx) = decE ew := rfl
    rw [e3]
    simp [this]; rfl
  rw [ite_eq_right h6] at h
  have h6' : tagW ew = 6 := Decidable.not_not.mp h6
  have htagT : ((decE ew).tag == ETag.forallE) = true := by simpa using hftag.mpr h6'
  by_cases hev : eViewW m1 ew = []
  · rw [ite_eq_left hev] at h; cases h
  rw [ite_eq_right hev] at h
  obtain ⟨v, hv, hR⟩ := eViewW_ok m1 a1 hS1.check.arena.base ew hev
  have hhead := eViewW_head6 m1 ew hev h6'
  have hdec : ∃ ty b : EIdx, v = .forallE ty b ∧
      ((eViewW m1 ew).tail.headD 0).toNat < 2 ^ 32 ∧ decE ((eViewW m1 ew).tail.headD 0) = ty := by
    cases v <;> simp only [ViewR] at hR
    case forallE ty b => exact ⟨ty, b, rfl, by rw [← L.getD_one]; exact hR.2.1, by rw [← L.getD_one]; exact hR.2.2.1⟩
    all_goals first | exact absurd (hhead.symm.trans hR.1) (by decide) | exact absurd (hhead.symm.trans hR) (by decide)
  obtain ⟨ty, bb, rfl, hdw32, hdwd⟩ := hdec
  have hvb := EStore.viewBind_of_view_forall _ _ _ _ hv
  generalize hdw : (eViewW m1 ew).tail.headD 0 = dw at h hdw32 hdwd
  rcases hga : gafF m1 [CWF, dw] with _ | ⟨r2, m2⟩ <;> rw [hga] at h
  · simp [rfW.k_get_app_fn_f] at h
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx232, hx2d⟩ := gafF_ok vis fe CWF dw hdw32 m1 m2 a1 r2 hga hS1
  simp only [rfW.k_get_app_fn_f] at h
  generalize hhd : r2.headD 0 = hd at h hx232 hx2d
  have hctag : (decE hd).tag = ETag.const ↔ tagW hd = 3 := decE_tag_eq hd hx232 3 (by decide)
  -- the twin up to the head
  have e3 : (decI ew : EIdx) = decE ew := rfl
  have e4 : (decI dw : EIdx) = decE dw := rfl
  rw [CWF_eq, e4, hdwd] at hrun2
  by_cases h3 : tagW hd ≠ 3
  · rw [ite_eq_left h3] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have : ¬ (decE hd).tag = ETag.const := fun c => h3 (hctag.mp c)
    refine ⟨.plain, a2, ?_, hS2, hg1.trans hg2, rfl⟩
    simp only [ConRon.Arena.recFire, hnlt, ↓reduceIte]
    rw [e1, ← hewd, e3]
    simp only [htagT, ↓reduceIte]
    have ev : (ConRon.Arena.viewBind (decE ew)) a1 = .ok (a1.store.viewBind (decE ew), a1) := rfl
    rw [hvb] at ev
    simp only [StateT.run, bind, StateT.bind, ev, Except.bind]
    simp only [StateT.run] at hrun2
    rw [hrun2]
    simp only [← hx2d]
    have e5 : (decI hd : EIdx) = decE hd := rfl
    simp [e5, this]; rfl
  rw [ite_eq_right h3] at h
  have h3' : tagW hd = 3 := Decidable.not_not.mp h3
  have hctT : ((decE hd).tag == ETag.const) = true := by simpa using hctag.mpr h3'
  by_cases hev2 : eViewW m2 hd = []
  · rw [ite_eq_left hev2] at h; cases h
  rw [ite_eq_right hev2] at h
  obtain ⟨v2, hv2, hR2⟩ := eViewW_ok m2 a2 hS2.check.arena.base hd hev2
  have hhead2 := eViewW_head3 m2 hd hev2 h3'
  have hdec2 : ∃ nn us, v2 = .const nn us ∧
      ((eViewW m2 hd).tail.tail.headD 0).toNat < 2 ^ 32 ∧ decI ((eViewW m2 hd).tail.tail.headD 0) = us := by
    cases v2 <;> simp only [ViewR] at hR2
    case const nn us => exact ⟨nn, us, rfl, by rw [← L.getD_two]; exact hR2.2.2.2.1, by rw [← L.getD_two]; exact hR2.2.2.2.2⟩
    all_goals first | exact absurd (hhead2.symm.trans hR2.1) (by decide) | exact absurd (hhead2.symm.trans hR2) (by decide)
  obtain ⟨nn, us, rfl, huw32, huwd⟩ := hdec2
  have hvc := EStore.viewConst_of_view_r _ _ _ _ hv2
  generalize huw : (eViewW m2 hd).tail.tail.headD 0 = uw at h huw32 huwd
  rcases hvl : viewLsW n m2 uw with _ | ⟨r3, m3⟩ <;> rw [hvl] at h
  · simp [rfW.k_view_ls] at h
  obtain ⟨ids, hrun3, hS3, hg3, hd3, -⟩ := viewLsW_ok hvl hS2 huw32 (L.Ind.poolSmall_of_stage hS2)
  simp only [rfW.k_view_ls] at h
  rcases hgaa : gaaF m3 [CWF, dw] with _ | ⟨r4, m4⟩ <;> rw [hgaa] at h
  · simp [rfW.k_get_app_args_f] at h
  obtain ⟨args, a4, hrun4, hS4, hg4, hd4⟩ := gaaF_ok (fun _ => none) vis fe CWF dw hdw32 m3 m4 a2 r4 hgaa hS3
  simp only [rfW.k_get_app_args_f] at h
  have hg04 : IWGrow m m4 := hg1.trans (hg2.trans (hg3.trans hg4))
  generalize hrPw : rdW (m.arr64 IW) (rc + 1) = rPw at hrPW
  rw [rdW_iw_grow hg04 (iwLt (o := rc) (w := 2) (by simpa using hmI)), hmIw,
    rdW_iw_grow hg04 (iwLt (o := rc) (w := 1) (by simpa using hrP)), hrPw] at h
  obtain ⟨nIw, hnI, h⟩ : ∃ nIw : Word, nIw.toNat = rs.mI - rs.rP ∧
      rfW.j1 p n (r3.headD 0) (r3.tail.headD 0) (r4.headD 0) (r4.tail.headD 0) nIw m4 = some (r, m') := by
    by_cases hc : mIw < rPw
    · rw [ite_eq_left hc] at h
      refine ⟨0, ?_, h⟩
      have := UInt64.lt_iff_toNat_lt.mp hc; simp; omega
    · rw [ite_eq_right hc] at h
      refine ⟨mIw - rPw, ?_, h⟩
      have : ¬ _ := fun c => hc (UInt64.lt_iff_toNat_lt.mpr c)
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]; omega
  obtain ⟨hargs, hargsb⟩ := hd4
  simp only [L.getD_zero, Nat.zero_add, L.getD_one] at hargs hargsb
  have hlen := decHL_length _ hargs
  obtain ⟨alw, hal, h⟩ : ∃ alw : Word, alw.toNat = args.length - (rs.mI - rs.rP) ∧
      rfW.j2 p n (r3.headD 0) (r3.tail.headD 0) (r4.headD 0) alw nIw m4 = some (r, m') := by
    unfold rfW.j1 at h
    by_cases hc : r4.tail.headD 0 < nIw
    · rw [ite_eq_left hc] at h
      refine ⟨0, ?_, h⟩
      have := UInt64.lt_iff_toNat_lt.mp hc; simp; omega
    · rw [ite_eq_right hc] at h
      refine ⟨r4.tail.headD 0 - nIw, ?_, h⟩
      have : ¬ _ := fun c => hc (UInt64.lt_iff_toNat_lt.mpr c)
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]; omega
  unfold rfW.j2 at h
  rcases hed : edvlW p n m4 nIw (r4.headD 0) alw with _ | ⟨r5, m5⟩ <;> rw [hed] at h
  · simp [rfW.k_expr_drop_vars_list] at h
  obtain ⟨ys, a5, hrun5, hd5, hb5, hS5, hg5⟩ := edvlW_ok hP.toDropProg vis fe nIw n m4 m5 a4 (r4.headD 0) alw
    (args.take (args.length - (rs.mI - rs.rP))) r5 hS4
    (by rw [hal]; exact decHL_take hargs _ (by omega)) (by omega) hed
  simp only [rfW.k_expr_drop_vars_list, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hids, hidsb⟩ := hd3
  simp only [L.getD_zero, Nat.zero_add, L.getD_one] at hids hidsb
  refine ⟨.nested ids ys, a5, ?_, hS5, hg04.trans hg5, rfl, ⟨?_, ?_⟩, ⟨by simpa using hd5, by simpa using hb5⟩⟩
  · simp only [ConRon.Arena.recFire, hnlt, ↓reduceIte]
    rw [e1, ← hewd, e3]
    simp only [htagT, ↓reduceIte]
    have ev : (ConRon.Arena.viewBind (decE ew)) a1 = .ok (a1.store.viewBind (decE ew), a1) := rfl
    rw [hvb] at ev
    simp only [StateT.run, bind, StateT.bind, ev, Except.bind]
    simp only [StateT.run] at hrun2 hrun3 hrun4 hrun5
    rw [hrun2]
    simp only [← hx2d]
    have e5 : (decI hd : EIdx) = decE hd := rfl
    have evc : (viewConst (decE hd)) a2 = .ok (a2.store.viewConst (decE hd), a2) := rfl
    rw [hvc] at evc
    simp only [e5, hctT, ↓reduceIte, StateT.bind, evc]
    rw [CWF_eq, e4, hdwd] at hrun4
    rw [← huwd]
    simp only [bind, Except.bind, StateT.bind]
    rw [hrun3]
    simp only
    rw [hrun4]
    simp only
    rw [hnI] at hrun5; rw [hrun5]
    rfl
  · simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [decHL_grow (hg4.trans hg5) hidsb]; exact hids
  · simp only [List.getD_cons_succ, List.getD_cons_zero]
    have := (hg4.trans hg5).iw; omega

end L.Ind

end
