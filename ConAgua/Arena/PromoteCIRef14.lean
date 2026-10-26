import ConAgua.Arena.PromoteCIRef13

/-!
# `promote_proj_table` refines `promoteProjTable`
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

theorem arenaD_ctl129 {m m' : Mem} {a : AState} {pm : PMemo} (hD : ArenaD m a) (hP : PMemoR m pm)
    (hf : MemFrame [] [129] m m') : ArenaD m' a ∧ PMemoR m' pm :=
  ⟨⟨ArenaR.frame_ext _ _ (by simp) (by simp) m _ hf a hD.1,
    DerR.frameM _ _ m _ hf (by simp) a hD.2⟩, hP.frame (by simp) (by simp) hf⟩

theorem ErecGrow.of_alloc {m m' : Mem} {k : Nat} (hE : m'.arr64 EREC = m.arr64 EREC)
    (hT : erecTop m' = erecTop m + k) : ErecGrow m m' :=
  ⟨by omega, fun i _ => by rw [hE], by rw [hE]⟩

section rel
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem proj_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f q : Word) (D : Nat)
    (tbl : IProjTable) (r : List Word) (m' : Mem) (hD : ArenaD m a) (hP : PMemoR m pm)
    (hsz : (m.arr64 EREC).size < 2 ^ 64) (hts : erecTop m ≤ (m.arr64 EREC).size)
    (htbl : decTbl (preE m D) q.toNat = some tbl)
    (hqD : q.toNat + 13 ≤ D) (hDt : D ≤ erecTop m)
    (hc : callW p n "promote_proj_table" [f, q] m = some (r, m')) :
    ∃ a' pm' tbl', (promoteProjTable pm f.toNat tbl).run a = .ok ((pm', tbl'), a') ∧
      ArenaD m' a' ∧ PMemoR m' pm' ∧ cp a' = cp a ∧
      MemFrame (EREC :: eArrs) (129 :: eCtl) m m' ∧ TierKeep m m' ∧ ErecGrow m m' ∧
      erecTop m' ≤ (m'.arr64 EREC).size ∧ (r.headD 0).toNat = erecTop m ∧
      (r.headD 0).toNat + 13 ≤ erecTop m' ∧
      decTbl (erecP m') (r.headD 0).toNat = some tbl' := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', hs', -, hW⟩ := callW_triple (promoteProj_spec p hp n ⟨m, Locals.init []⟩ f q) hc
  simp only at hW
  rw [hs'] at hW
  simp only [projW] at hW
  cases n with
  | zero => simp only [callW_zero', Option.bind_none] at hW; cases hW
  | succ n =>
  obtain ⟨hsn, hlp, hct, hss, hbs, hgs⟩ := pmDecTbl_words htbl
  have hqb : q.toNat + 13 ≤ (m.arr64 EREC).size := by omega
  -- the allocation
  obtain ⟨⟨r5, ma⟩, hal, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨hd5, hTa, hroom, hfa, hEa⟩ := alloc_rel p hp hal
  have hTa' : erecTop ma = erecTop m + 13 := by rw [hTa]; rfl
  have hga : ErecGrow m ma := ErecGrow.of_alloc hEa hTa'
  obtain ⟨hDa, hPa⟩ := arenaD_ctl129 hD hP hfa
  have hsza : (ma.arr64 EREC).size < 2 ^ 64 := by rw [hEa]; exact hsz
  have htsa : erecTop ma ≤ (ma.arr64 EREC).size := by
    rw [hEa, hTa']; have h := hroom; simp only [show ((13 : Word)).toNat = 13 from rfl] at h; exact h
  have hlift : ∀ {α : Type} (g : Array Word → Option α) (x : α),
      (∀ {a b : Array Word} (h : ArrExt a b) (y : α), g a = some y → g b = some y) →
      g (erecP m) = some x → g (erecP ma) = some x := fun g x hg h => hg hga.ext x h
  have h4 : ∀ {k : IdxKind} (i : Nat) (x : Idx k), hd? (preE m D) i = some x →
      hd? (erecP ma) i = some x := fun i x h =>
    hga.ext.hd? ((preE_mono m hDt).hd? h)
  have h4l : ∀ {k : IdxKind} (i : Nat) (x : List (Idx k)), hlist? (preE m D) i = some x →
      hlist? (erecP ma) i = some x := fun i x h =>
    hga.ext.hlist? ((preE_mono m hDt).hlist? h)
  -- proj_a
  obtain ⟨⟨ra, mb⟩, hpa, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨a1, pm1, a3, pm3, sn', lps', wl, hrun1, hrun3, hDb, hPb, hcpb, hfb, htkb,
    hgb, htsb, hpws, hds, hwl, hptr, hTb, hslb⟩ :=
    projA_rel p hp (n + 1) ma a pm f q tbl.structName tbl.levelParams ra mb hDa hPa
      hsza (by rw [hEa]; exact hqb) (h4 _ _ hsn) (h4l _ _ hlp) hpa
  have hszb : (mb.arr64 EREC).size < 2 ^ 64 := by rw [hgb.2.2]; exact hsza
  -- proj_b
  obtain ⟨⟨rb, mc⟩, hpb, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  have hg0b : ErecGrow m mb := hga.trans hgb
  obtain ⟨b1, qm1, b2, qm2, b3, qm3, b4, qm4, c', ss', bs', gs', wlb, wlg, hrunc, hruns, hrunb, hrung,
    hDc, hPc, hcpc, hfc, htkc, hgc, htsc, hpwc, hdc, hpwss, hdss, hwlb, hwlg, hptrb, hptrg, hTc, hslbs,
    hslgs⟩ :=
    projB_rel p hp (n + 1) mb a3 pm3 f q tbl.ctor tbl.structSort tbl.bodies.toList tbl.guards rb mc
      hDb hPb hszb (by rw [hgb.2.2, hEa]; exact hqb)
      (hgb.ext.hd? (h4 _ _ hct)) (hgb.ext.hd? (h4 _ _ hss)) (hgb.ext.hlist? (h4l _ _ hbs))
      (hgb.ext.hlist? (h4l _ _ hgs)) hpb
  have hgc0 : ErecGrow m mc := hg0b.trans hgc
  have hdv : (r5.headD 0).toNat = erecTop m := hd5
  have hszc : (mc.arr64 EREC).size = (m.arr64 EREC).size := by
    rw [hgc0.2.2]
  have keyc : ∀ i < erecTop m, (mc.arr64 EREC)[i]? = (m.arr64 EREC)[i]? := hgc0.2.1
  -- the copy
  obtain ⟨⟨z, md⟩, hcp, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨k1, k2, k3, k4⟩ := cp_rel p hp (n + 1) mc (r5.headD 0) q 13 z md
    (by simp only [show ((13 : Word)).toNat = 13 from rfl]; omega)
    (by simp only [show ((13 : Word)).toNat = 13 from rfl]; omega) (by rw [hszc]; exact hsz) hcp
  simp only [show ((13 : Word)).toNat = 13 from rfl] at k3 k4
  obtain ⟨⟨z2, me⟩, hwr, hW⟩ := Option.bind_eq_some_iff.mp hW
  dsimp only at hW
  obtain ⟨hr, hme⟩ := Prod.mk.inj (Option.some.inj hW)
  subst hme
  obtain ⟨w1, w2, w3, w5, w6, w7, w8, w9, w10⟩ := projWr_rel' p hp (d := r5.headD 0)
    (by rw [k1, hszc]; omega) (by rw [k1, hszc]; exact hsz) hwr
  have hTc' : erecTop mc = erecTop m + 13 + wl.toNat + wlb.toNat + wlg.toNat := by
    rw [hTc, hTb, hTa'] <;> omega
  have hTd : erecTop md = erecTop mc := by simp only [erecTop]; rw [k2.2.1 129 (by simp)]
  have hTe : erecTop me = erecTop mc := by
    simp only [erecTop]; rw [w2.2.1 129 (by simp), k2.2.1 129 (by simp)]
  have hsze : (me.arr64 EREC).size = (mc.arr64 EREC).size := by rw [w1, k1]
  have hgrs : SlotGrow mc me (r5.headD 0).toNat ((r5.headD 0).toNat + 13) :=
    ⟨by rw [hTe]; exact Nat.le_refl _, fun i hi hout => by
      rw [w3 i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        k3 i (by omega)], hsze⟩
  have htse : erecTop me ≤ (me.arr64 EREC).size := by rw [hTe, hsze]; exact htsc
  have hgm : SlotGrow m me (r5.headD 0).toNat ((r5.headD 0).toNat + 13) :=
    (SlotGrow.of_grow hgc0 _ _).trans hgrs (Nat.le_refl _) (Nat.le_refl _)
  have hgme : ErecGrow m me := hgm.toGrow (by omega)
  obtain ⟨hDf, hPf⟩ := arenaD_erecFrame hDc hPc (k2.trans w2)
  have W : ∀ i, i < 13 → i ≠ 2 → i ≠ 3 → i ≠ 6 → i ≠ 8 → i ≠ 9 → i ≠ 11 →
      (me.arr64 EREC)[(r5.headD 0).toNat + i]? = (m.arr64 EREC)[q.toNat + i]? := by
    intro i hi h2 h3 h6 h8 h9 h11
    rw [w3 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      k4 i hi, keyc _ (by omega)]
  have PE : ∀ {i : Nat} {w : Word}, i < erecTop me → (me.arr64 EREC)[i]? = some w →
      (erecP me)[i]? = some w := fun hi h => preE_of_get hi h
  have hq5 : (m.arr64 EREC)[q.toNat + 5]? = (preE m D)[q.toNat + 5]? := by
    rw [preE_get, if_pos (by omega)]
  have hdn : (r5.headD 0).toNat = erecTop m := hdv
  have WP : ∀ i, i < 13 → i ≠ 2 → i ≠ 3 → i ≠ 6 → i ≠ 8 → i ≠ 9 → i ≠ 11 →
      (erecP me)[(r5.headD 0).toNat + i]? = (preE m D)[q.toNat + i]? := by
    intro i hi h2 h3 h6 h8 h9 h11
    rw [erecP_getElem me _ (by omega) htse, W i hi h2 h3 h6 h8 h9 h11, preE_get,
      if_pos (by omega)]
  have hq4 : (m.arr64 EREC)[q.toNat + 4]? = some wl := by
    obtain ⟨w, hw, hwl'⟩ := nat?_get hwl
    have h1 := erecP_get hw
    rw [hEa] at h1
    exact (UInt64.toNat_inj.mp hwl') ▸ h1
  have hq10 : (m.arr64 EREC)[q.toNat + 10]? = some wlb := by
    obtain ⟨w, hw, hwl'⟩ := nat?_get hwlb
    have h1 := erecP_get hw
    rw [hg0b.2.1 _ (by omega)] at h1
    exact (UInt64.toNat_inj.mp hwl') ▸ h1
  have hq12 : (m.arr64 EREC)[q.toNat + 12]? = some wlg := by
    obtain ⟨w, hw, hwl'⟩ := nat?_get hwlg
    have h1 := erecP_get hw
    rw [hg0b.2.1 _ (by omega)] at h1
    exact (UInt64.toNat_inj.mp hwl') ▸ h1
  have hsn' : (hd? (erecP me) ((r5.headD 0).toNat + 2) : Option NIdx) = some sn' := by
    rw [← hds, erecP_eq_preE]; exact hd?_of_pre (by omega) w5 hpws.1
  have hc' : (hd? (erecP me) ((r5.headD 0).toNat + 6) : Option NIdx) = some c' := by
    rw [← hdc, erecP_eq_preE]; exact hd?_of_pre (by omega) w7 hpwc.1
  have hss'' : (hd? (erecP me) ((r5.headD 0).toNat + 8) : Option LIdx) = some ss' := by
    rw [← hdss, erecP_eq_preE]; exact hd?_of_pre (by omega) w8 hpwss.1
  have hlp' : (hlist? (erecP me) ((r5.headD 0).toNat + 3) : Option (List NIdx)) = some lps' := by
    simp only [L.Arena.hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff]
    refine ⟨(ra.tail.headD 0).toNat, ?_, wl.toNat, ?_, ?_⟩
    · rw [erecP_eq_preE]; exact nat?_of_pre (by omega) w6
    · rw [erecP_eq_preE]
      refine nat?_of_pre (m := me) (T := erecTop me) (w := wl) (by omega) ?_
      rw [show (r5.headD 0).toNat + 3 + 1 = (r5.headD 0).toNat + 4 from rfl,
        W 4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hq4
    · have h := hgc.ext.hslice? hslb
      have h2 := hgrs.hslice? htsc htse h (Or.inr (Or.inl (by omega)))
      exact (show (ra.tail.headD 0).toNat = erecTop ma from hptr) ▸ h2
  have hbs' : (hlist? (erecP me) ((r5.headD 0).toNat + 9) : Option (List EIdx)) = some bs' := by
    simp only [L.Arena.hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff]
    refine ⟨(rb.tail.tail.headD 0).toNat, ?_, wlb.toNat, ?_, ?_⟩
    · rw [erecP_eq_preE]; exact nat?_of_pre (by omega) w9
    · rw [erecP_eq_preE]
      refine nat?_of_pre (m := me) (T := erecTop me) (w := wlb) (by omega) ?_
      rw [show (r5.headD 0).toNat + 9 + 1 = (r5.headD 0).toNat + 10 from rfl,
        W 10 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hq10
    · have h2 := hgrs.hslice? htsc htse hslbs (Or.inr (Or.inl (by omega)))
      exact (show (rb.tail.tail.headD 0).toNat = erecTop mb from hptrb) ▸ h2
  have hgs' : (hlist? (erecP me) ((r5.headD 0).toNat + 11) : Option (List LIdx)) = some gs' := by
    simp only [L.Arena.hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff]
    refine ⟨(rb.tail.tail.tail.headD 0).toNat, ?_, wlg.toNat, ?_, ?_⟩
    · rw [erecP_eq_preE]; exact nat?_of_pre (by omega) w10
    · rw [erecP_eq_preE]
      refine nat?_of_pre (m := me) (T := erecTop me) (w := wlg) (by omega) ?_
      rw [show (r5.headD 0).toNat + 11 + 1 = (r5.headD 0).toNat + 12 from rfl,
        W 12 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hq12
    · have h2 := hgrs.hslice? htsc htse hslgs (Or.inr (Or.inl (by omega)))
      exact (show (rb.tail.tail.tail.headD 0).toNat = erecTop mb + wlb.toNat from hptrg) ▸ h2
  refine ⟨b4, qm4, ⟨sn', lps', tbl.numParams, c', tbl.numFields, ss', bs'.toArray, gs'⟩, ?_, hDf, hPf, hcpc.trans hcpb, ?_,
    (TierKeep.of_frame hfa (by simp)).trans (htkb.trans (htkc.trans (TierKeep.of_frame (k2.trans w2) (by simp)))),
    hgme, htse, ?_, ?_, ?_⟩
  · rw [promoteProjTable, run_bind_ok hrun1]
    simp only
    rw [run_bind_ok hrun3]
    simp only
    rw [run_bind_ok hrunc]
    simp only
    rw [run_bind_ok hruns]
    simp only
    rw [run_bind_ok hrunb]
    simp only
    rw [run_bind_ok hrung]; rfl
  · exact ((((hfa.mono (by simp) (by simp)).trans (hfb)).trans hfc)).trans
      ((k2.trans w2).mono (by simp) (by simp))
  · rw [← hr]; exact hdv
  · rw [← hr]; show (r5.headD 0).toNat + 13 ≤ erecTop me; omega
  · rw [← hr]
    exact decTbl_move htbl
      (by have := WP 5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega); exact this)
      (by have := WP 7 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega); exact this)
      hsn' hlp' hc' hss'' hbs' hgs'


end rel

end L.Arena
