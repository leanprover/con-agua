import ConAgua.Arena.IndPos2SpecH
import ConAgua.Arena.WhnfCoreProj

/-! # `IndPos2`'s leaves, continued (lane `indproofs2`, helper `pos`, fork E): `nestInstType`'s
relational side, `nestGrowGroup`. -/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `nest_inst_type_ty`: the relational side -/

/-- A `NestKey` record's `ds` slice ends below the pool's top. -/
def NKSl (m : Mem) (key : Word) : Prop :=
  (rdW (m.arr64 IW) (key + 2)).toNat + (rdW (m.arr64 IW) (key + 3)).toNat ≤ iwTop m

/-- A decoded `NestKey`'s fields, as the words L reads. -/
theorem nk_fields {m : Mem} {key : Word} {kk : NestKey} (hk : decNK m key.toNat = some kk)
    (hin : NKIn m key.toNat (· < iwTop m)) (htop : iwTop m < 2 ^ 64) :
    H (rdW (m.arr64 IW) key) ∧ decI (rdW (m.arr64 IW) key) = kk.cname ∧
    H (rdW (m.arr64 IW) (key + 1)) ∧ decI (rdW (m.arr64 IW) (key + 1)) = kk.lvls ∧
    decHL m (rdW (m.arr64 IW) (key + 2)).toNat (rdW (m.arr64 IW) (key + 3)).toNat = some kk.ds ∧
    (∀ j < (rdW (m.arr64 IW) (key + 3)).toNat, (rdW (m.arr64 IW) (key + 2)).toNat + j < iwTop m) ∧
    key.toNat + 4 ≤ iwTop m := by
  simp only [decNK, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at hk
  obtain ⟨c, hc, u, hu, ds, hds, heq⟩ := hk
  cases Option.some.inj heq
  have h3 := hin.1 3 (by omega)
  obtain ⟨o, l, ho, hl, hd⟩ := decAt_some hds
  have r2 : (rdW (m.arr64 IW) (key + 2)).toNat = o := rd_iwN (by simpa using ho) (by simp; omega)
  have r3 : (rdW (m.arr64 IW) (key + 3)).toNat = l := rd_iwN (by simpa using hl) (by simp; omega)
  obtain ⟨h0a, h0b⟩ := rd_iwH0E (m := m) (o := key) hc
  obtain ⟨h1a, h1b⟩ := rd_iwH (p := key) (i := 1) (by simpa using hu) (by simp; omega)
  refine ⟨h0a, h0b, h1a, h1b, by rw [r2, r3]; exact hd, by rw [r2, r3]; exact hin.2 o l ho (by simpa using hl), by omega⟩

theorem ntyW_ok (k : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (m m' : Mem)
    (a : AState) (key : Word) (kk : NestKey) (r : List Word) (cR : CallM)
    (hI : IlpRd cR dn vis fe (IlpBase m a))
    (h : ntyW cR k m vis key = some (r, m')) (hS : StageR dn vis fe m a)
    (hk : decNK m key.toNat = some kk) (hkin : NKIn m key.toNat (· < iwTop m)) (hksl : NKSl m key)
 :
    ∃ cv caps a3 q a4 tl a5 ty, fe.find? kk.cname = some (.indInfo cv caps) ∧
      a.store.lss.viewLen kk.lvls = some cv.levelParams.length ∧
      (stripPis kk.ds.length cv.type).run a = .ok (some q, a3) ∧
      (instLPFast coreWalkFuel cv.levelParams kk.lvls cv.type).run a3 = .ok (tl, a4) ∧
      (ConRon.Arena.instPisWith kk.ds tl).run a4 = .ok (some ty, a5) ∧
      StageR dn vis fe m' a5 ∧ IWGrow m m' ∧ H (r.headD 0) ∧ decI (r.headD 0) = ty ∧ AFr m m' := by
  have hE := hS.1.env
  have hR := hS.1.arena.1
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  have hEb : erTop m ≤ (m.arr64 EREC).size := hS.2.2.1
  have hEs : (m.arr64 EREC).size < 2 ^ 64 := hS.2.2.2.2.1
  obtain ⟨hcH, hcd, hlH, hld, hds, hdsb, hk4⟩ := nk_fields hk hkin htop
  unfold ntyW at h
  rcases hef : envFindW m (rdW (m.arr64 IW) key) vis with _ | ⟨r1, m1⟩ <;> rw [hef] at h; · simp [ntyK1] at h
  have hm1 := envFindW_mem hef
  rw [hm1] at h hef
  rw [ntyK1_eq] at h
  by_cases hf0 : r1.headD 0 = 0
  · rw [ite_eq_left hf0] at h; simp at h
  rw [ite_eq_right hf0] at h
  obtain ⟨-, hfind, ci, hci⟩ := envFindW_hit hef hE hcH hf0
  rw [hci] at hfind
  by_cases h3 : rdW (m.arr64 EREC) (r1.tail.headD 0) ≠ 3
  · rw [ite_eq_left h3] at h; simp at h
  rw [ite_eq_right h3] at h
  generalize r1.tail.headD 0 = q at h hfind hci h3
  have hciq := decCI_idx hci
  have hszE := erecP_size_le m
  have hk3 : nat? (erecP m) q.toNat = some 3 := by
    have : (erecP m)[q.toNat]? = (m.arr64 EREC)[q.toNat]? := erecP_getE (by omega)
    simp only [nat?, this]
    have hb : q.toNat < (m.arr64 EREC).size := by omega
    have : rdW (m.arr64 EREC) q = 3 := by simpa using h3
    simp [rdW, hb] at this ⊢; rw [this]; rfl
  obtain ⟨cv, caps, rfl, hcaps⟩ := decCI_kind3 hci hk3
  have hb16 := decCI_indInfo_bound hci
  have hcv : decCV (erecP m) (q.toNat + 1) = some cv := by
    simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at hci
    obtain ⟨kd, hkd, hci⟩ := hci
    rw [hk3] at hkd; cases hkd
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at hci
    obtain ⟨cv', h1, _, _, h2⟩ := hci
    cases h2; exact h1
  have e1 : (q + 1).toNat = q.toNat + 1 := word_add_toNat (by simp; omega)
  have e12 : (q + 1 + 2).toNat = q.toNat + 1 + 1 + 1 := by
    rw [word_add_toNat (by rw [e1]; simp; omega), e1]; rfl
  have e13 : (q + 1 + 3).toNat = q.toNat + 1 + 3 := by
    rw [word_add_toNat (by rw [e1]; simp; omega), e1]; rfl
  obtain ⟨-, hlps, hty⟩ := decCV_some hcv
  obtain ⟨wt, hwt, hwtH, hwtd⟩ := hd?_some hty
  have hrdt : rdW (m.arr64 EREC) (q + 1 + 3) = wt := by simp [rdW, e13, erecP_get hwt]
  simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hlps
  obtain ⟨lo, hlo, ll, hll, hsl⟩ := hlps
  have hlen : (rdW (m.arr64 EREC) (q + 1 + 2)).toNat = cv.levelParams.length := by
    rw [erecP_rdN hll e12]; simpa using (mapM_opt_length _ _ _ hsl).symm
  -- the level list's length
  rcases lsNodeW_cases m (rdW (m.arr64 IW) (key + 1)) with hln | ⟨o', l', hln⟩
  · rw [ite_eq_left hln] at h; simp at h
  rw [ite_eq_right (by rw [hln]; simp)] at h
  by_cases hneq : (lsNodeW m (rdW (m.arr64 IW) (key + 1))).tail.headD 0 ≠ rdW (m.arr64 EREC) (q + 1 + 2)
  · rw [ite_eq_left hneq] at h; simp at h
  rw [ite_eq_right hneq] at h
  have hvl := lsNodeW_viewLen hR hlH hln
  rw [hld] at hvl
  have hl'eq : l'.toNat = cv.levelParams.length := by
    rw [← hlen]; rw [hln] at hneq; rw [show l' = rdW (m.arr64 EREC) (q + 1 + 2) by simpa using hneq]
  rw [hl'eq] at hvl
  rw [hrdt] at h
  -- `strip_pis`
  rcases hst : stripF 6 m [rdW (m.arr64 IW) (key + 3), wt] with _ | ⟨r3, m3⟩ <;> rw [hst] at h; · simp [ntyK3] at h
  obtain ⟨x3, a3, hrun3, hS3, hg3, hx3⟩ := stripF_pis_ok dn vis fe _ wt hwtH m m3 a r3 hst hS
  have ha3 : a3 = a := stripPis_st _ _ _ _ _ hrun3
  subst a3
  have hdsl := decHL_length m hds
  rw [← hdsl, ← hwtd] at hrun3
  cases x3 with
  | none => have : r3.headD 0 = 0 := hx3; rw [ntyK3_none (h := this)] at h; simp at h
  | some q3 =>
  rw [ntyK3_some (h := by rw [hx3.1]; decide)] at h
  -- `cv_lps`
  have hcv3 : decCVp m3 (q + 1).toNat = some cv := by
    rw [e1]; exact (erecP_ext m3).decCV ((GrowX.of_grow (q := 0) (n := 0) hg3).erecP.decCV hcv)
  rcases hlp : cvLpsW k m3 (q + 1) with _ | ⟨r4, m4⟩ <;> rw [hlp] at h; · simp [ntyK4] at h
  rw [ntyK4_some] at h
  obtain ⟨hS4, hg4, hE4, hdec4, -⟩ := pos2_cvLpsW_stage hlp hS3 hcv3 (by rw [e1]; have := hg3.2.1; omega)
  have hg34 := hg3.trans hg4
  have hlv4 : rdW (m4.arr64 IW) (key + 1) = rdW (m.arr64 IW) (key + 1) := by
    have e : (key + 1).toNat = key.toNat + 1 := word_add_toNat (by simp; omega)
    simp only [rdW, e]; rw [hg34.2.2.1 _ (by omega)]
  have hwt4 : rdW (m4.arr64 EREC) (q + 1 + 3) = wt := by
    rw [hE4]
    have : (m3.arr64 EREC)[(q + 1 + 3).toNat]? = (m.arr64 EREC)[(q + 1 + 3).toNat]? := by
      rw [e13]; exact hg3.2.2.2 _ (by omega)
    simp only [rdW, this]; exact hrdt
  rw [hlv4, hwt4] at h
  -- `inst_lp_fast`
  rcases hil : cR k "inst_lp_fast" [CWF, r4.headD 0, r4.tail.headD 0, rdW (m.arr64 IW) (key + 1), wt] m4 with _ | ⟨r5, m5⟩ <;> rw [hil] at h; · simp [ntyK5] at h
  rw [ntyK5_some] at h
  obtain ⟨tl, a4, hrun4, ⟨hS5, hg5, htlH, htld⟩, -, hA5⟩ :=
    hI k CWF _ _ _ _ cv.levelParams m4 m5 a r5 hlH hwtH ⟨rfl, (stripF_frame hst).trans (erToIwW_iwFr hlp)⟩ hS4
      hdec4 hil
  rw [CWF_eq, hld, ← hwtd] at hrun4
  have hg35 := hg34.trans hg5
  have hrd2 : rdW (m5.arr64 IW) (key + 2) = rdW (m.arr64 IW) (key + 2) := by
    have e : (key + 2).toNat = key.toNat + 2 := word_add_toNat (by simp; omega)
    simp only [rdW, e]; rw [hg35.2.2.1 _ (by omega)]
  have hrd3 : rdW (m5.arr64 IW) (key + 3) = rdW (m.arr64 IW) (key + 3) := by
    have e : (key + 3).toNat = key.toNat + 3 := word_add_toNat (by simp; omega)
    simp only [rdW, e]; rw [hg35.2.2.1 _ (by omega)]
  rw [hrd2, hrd3] at h
  -- `inst_pis_with`
  rcases hiw : instW k m5 (rdW (m.arr64 IW) (key + 2)) (rdW (m.arr64 IW) (key + 3)) (r5.headD 0) with _ | ⟨r6, m6⟩ <;> rw [hiw] at h; · simp [ntyK6] at h
  obtain ⟨x6, a5, hrun5, hS6, hg6, hx6⟩ := instW_ok k dn fe vis m5 m6 a4 _ _ _ kk.ds r6 hiw hS5 htlH
    (by rw [decHL_agree (RdS.of_grow hg35) (fun j hj => hdsb j hj)]; exact hds) (by unfold NKSl at hksl; omega)
    (by have := hg35.1; exact Nat.le_trans hksl this)
  rw [htld] at hrun5
  cases x6 with
  | none => have : r6.headD 0 = 0 := hx6; rw [ntyK6_none (h := this)] at h; simp at h
  | some ty =>
  obtain ⟨hx61, hx6H, hx6d⟩ := hx6
  rw [ntyK6_some (h := by rw [hx61]; decide)] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact ⟨cv, caps, a, q3, a4, tl, a5, ty, by rw [← hcd]; exact hfind, hvl, hrun3, hrun4, hrun5, hS6,
    (hg35.trans hg6), hx6H, hx6d, (AFr.iw (stripF_frame hst)).trans ((AFr.iw (erToIwW_iwFr hlp)).trans
      (hA5.trans (instW_afr _ _ _ _ _ _ _ hiw)))⟩

theorem ntyW_mfr {cR : CallM} (hF : IlpFr cR) {k : Nat} {m m' : Mem} {vis key : Word} {r : List Word}
    (h : ntyW cR k m vis key = some (r, m')) : MFr [] [] m m' := by
  simp only [ntyW, ntyK1.eq_def, ntyK3.eq_def, ntyK4.eq_def, ntyK5.eq_def, ntyK6.eq_def] at h
  have hI : ∀ {a m r m'}, cR k "inst_lp_fast" a m = some (r, m') → MFr [] [] m m' := fun h =>
    let ⟨_, _, hA, hC, hf⟩ := hF _ _ _ _ _ h; MFr.of_frame hf hA hC
  mfr_auto h [envFindW_mfr, fun h => MFr.of_iw (stripF_frame h), posmemo_cvLpsW_mfr, hI, instW_mfr _ _ _ _ _ _ _]

/-! ## `nest_inst_type` refines `nestInstType` -/

/-- **What `nest_inst_type`'s `lvl_eq_fueled` call (read through `cR`) must do**, from the
start `(m, a)`: given the calls and the twin's steps before it (`nest_inst_type_ty`, `pi_binders`,
`nest_occ_any`; `stripPis`, `instLPFast`, `instPisWith`, `piBinders`, the result's sort), refine
`liftFueled (← lvlEq? s ctx.sort)` and establish `Q` (the stubs: `nitLe_stub`; the real call
under `StageC`: `IndT/PosNit.lean`). -/
def NitLe (cR : CallM) (k : Nat) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (ctx hi key : Word) (c : NestCtx) (kk : NestKey) (Q : Mem → AState → Prop) (m : Mem) (a : AState) :
    Prop :=
  ∀ (m1 m2 m3 m4 : Mem) (r1 rs r3 r4 : List Word) (cv : IConstantVal) (caps : IIndCaps)
    (q : List EIdx × EIdx) (a3 a4 a5 : AState) (tl ty : EIdx) (bs : List EIdx) (e : EIdx) (uw : Word),
    ntyWf cR k m vis key = some (r1, m1) → AFr m m1 → piBW k m1 CWF (r1.headD 0) = some (rs, m2) →
    noaW k m2 (rdW (m2.arr64 IW) ctx) (rdW (m2.arr64 IW) (ctx + 1)) (rdW (m2.arr64 IW) (ctx + 4)) hi
      (rs.headD 0) (rs.getD 1 0) = some (r3, m3) →
    fe.find? kk.cname = some (.indInfo cv caps) →
    (stripPis kk.ds.length cv.type).run a = .ok (some q, a3) →
    (instLPFast coreWalkFuel cv.levelParams kk.lvls cv.type).run a3 = .ok (tl, a4) →
    (ConRon.Arena.instPisWith kk.ds tl).run a4 = .ok (some ty, a5) →
    (ConRon.Arena.piBinders coreWalkFuel ty).run a5 = .ok ((bs, e), a5) →
    (view e).run a5 = .ok (.sort (decI uw), a5) →
    StageR dn vis fe m3 a5 → IWGrow m m3 → H uw → H (rdW (m3.arr64 IW) (ctx + 9)) →
    decI (rdW (m3.arr64 IW) (ctx + 9)) = c.sort →
    lveC cR k m3 uw (rdW (m3.arr64 IW) (ctx + 9)) = some (r4, m4) →
    ∃ b a6, (lvlEq? (decI uw) c.sort).run a5 = .ok (some b, a6) ∧ StageR dn vis fe m4 a6 ∧
      IWGrow m3 m4 ∧ MFr [] [] m3 m4 ∧ r4.headD 0 = (if b then 1 else 0) ∧ Q m4 a6

theorem nitW_ok (k : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis ctx hi : Word) (HI : Nat)
    (hHI : hi.toNat = HI) (c : NestCtx) (m m' : Mem) (a : AState) (key : Word) (kk : NestKey) (r : List Word)
    (cR : CallM) (hI : IlpRd cR dn vis fe (IlpBase m a)) (hF : IlpFr cR) (Q : Mem → AState → Prop)
    (hLE : NitLe cR k dn vis fe ctx hi key c kk Q m a)
    (h : nitW cR k m vis ctx hi key = some (r, m')) (hS : StageR dn vis fe m a)
    (hU : UCtx dn vis fe m ctx c) (hk : decNK m key.toNat = some kk) (hkin : NKIn m key.toNat (· < iwTop m))
    (hksl : NKSl m key) (hP : PosMR m) :
    ∃ x a', (ConRon.Arena.nestInstType fe c HI kk).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ (r.headD 0).toNat = x.1 ∧ H (r.tail.headD 0) ∧ decI (r.tail.headD 0) = x.2 ∧
      PosMR m' ∧ (∀ r1 m1, ntyWf cR k m vis key = some (r1, m1) → AFr m m1) ∧ Q m' a' := by
  unfold nitW at h
  cases k with
  | zero => simp [ntyWf, nitK1] at h
  | succ k =>
  simp only [ntyWf] at h
  rcases hty : ntyW cR k m vis key with _ | ⟨r1, m1⟩ <;> rw [hty] at h; · simp [nitK1] at h
  rw [nitK1_some] at h
  obtain ⟨cv, caps, a3, q, a4, tl, a5, ty, hfind, hvl, hrun3, hrun4, hrun5, hS1, hg1, htyH, htyd, hA1⟩ :=
    ntyW_ok k dn fe vis m m1 a key kk r1 cR hI hty hS hk hkin hksl
  have hAty : ∀ r1' m1', ntyWf cR (k + 1) m vis key = some (r1', m1') → AFr m m1' := by
    intro r1' m1' e; simp only [ntyWf, hty, Option.some.injEq, Prod.mk.injEq] at e; rw [← e.2]; exact hA1
  -- `pi_binders`
  rcases hpb : piBW (k + 1) m1 CWF (r1.headD 0) with _ | ⟨rs, m2⟩ <;> rw [hpb] at h; · simp [nitK2] at h
  rw [nitK2_eq] at h
  obtain ⟨bs, e, hrunpb, hdecbs, hresH, hresd, hS2, hg2, hbsb⟩ := piBW_cwf hpb hS1 htyH
  by_cases hv0 : eViewW m2 (rs.getD 2 0) = []
  · rw [ite_eq_left hv0] at h; simp at h
  rw [ite_eq_right hv0] at h
  by_cases hv2 : (eViewW m2 (rs.getD 2 0)).headD 0 ≠ 2
  · rw [ite_eq_left hv2] at h; simp at h
  rw [ite_eq_right hv2] at h
  obtain ⟨v, hview, hvr⟩ := eViewW_ok m2 a5 hS2.1.arena.1 (rs.getD 2 0) hv0
  have hv2' : (eViewW m2 (rs.getD 2 0)).headD 0 = 2 := by simpa using hv2
  obtain ⟨u, rfl, huH, hud⟩ : ∃ u, v = .sort u ∧ ((eViewW m2 (rs.getD 2 0)).getD 1 0).toNat < 2 ^ 32 ∧
      decI ((eViewW m2 (rs.getD 2 0)).getD 1 0) = u := by
    cases v <;> simp only [ViewR] at hvr <;> (try (rw [hv2'] at hvr; simp at hvr))
    · exact ⟨_, rfl, hvr.1, hvr.2⟩
  -- `nest_occ_any` over the binders
  have hg12 := hg1.trans hg2
  have hU2 := hU.grow hg12
  have htop2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1
  obtain ⟨hn2, -, -, -, hnP2, -⟩ := ctx_fields hU2.dec hU2.inn htop2
  have hne2 := ctx_names_end hU2.dec hU2.inn hU2.sl htop2
  rcases hoa : noaW (k + 1) m2 (rdW (m2.arr64 IW) ctx) (rdW (m2.arr64 IW) (ctx + 1)) (rdW (m2.arr64 IW) (ctx + 4)) hi
      (rs.headD 0) (rs.getD 1 0) with _ | ⟨r3, m3⟩; · rw [hoa] at h; simp [nitK4] at h
  rw [hoa] at h
  obtain ⟨b, hrunoa, hS3, hg3, hr3, hP3⟩ := noaW_ok dn fe vis _ _ _ _ c.names (k + 1) m2 m3 a5 _ _ bs r3 hoa hS2
    hn2 hne2 hdecbs (fun j hj => by omega) ((hP.fr (ntyW_mfr hF hty)).fr (piBW_mfr _ _ _ _ _ _ hpb))
  rw [hnP2, hHI] at hrunoa
  cases b with
  | true => rw [nitK4_occ (h := by rw [hr3]; decide)] at h; simp at h
  | false =>
  rw [nitK4_ok (h := by rw [hr3]; decide)] at h
  -- the sorts
  have hU3 := hU2.grow hg3
  have htop3 : iwTop m3 < 2 ^ 64 := Nat.lt_of_le_of_lt hS3.2.1 hS3.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, hsH, hsd, -⟩ := ctx_fields hU3.dec hU3.inn htop3
  rcases hle : lveC cR (k + 1) m3 ((eViewW m2 (rs.getD 2 0)).tail.headD 0) (rdW (m3.arr64 IW) (ctx + 9)) with _ | ⟨r4, m4⟩ <;> rw [hle] at h; · simp [nitK5] at h
  have huH' : H ((eViewW m2 (rs.getD 2 0)).tail.headD 0) := by rw [← getD1_eq]; exact huH
  have hrunpb' : (ConRon.Arena.piBinders coreWalkFuel ty).run a5 = .ok ((bs, e), a5) := htyd ▸ hrunpb
  have hview' : (view e).run a5 = .ok (.sort u, a5) := view_run _ _ _ (hresd ▸ hview)
  have hud' : decI ((eViewW m2 (rs.getD 2 0)).tail.headD 0) = u := by rw [← getD1_eq]; exact hud
  obtain ⟨b', a6, hrunle, hS4, hg4, hf4, hr4, hQ⟩ := hLE m1 m2 m3 m4 r1 rs r3 r4 cv caps q a3 a4 a5 tl ty bs e _
    hty hA1 hpb hoa hfind hrun3 hrun4 hrun5 hrunpb' (by rw [hud']; exact hview') hS3
    ((hg1.trans hg2).trans hg3) huH' hsH hsd hle
  rw [hud'] at hrunle
  cases b' with
  | false => rw [nitK5_none (h := by rw [hr4]; decide)] at h; simp at h
  | true =>
  rw [nitK5_some (h := by rw [hr4]; decide)] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  refine ⟨(bs.length, ty), a6, ?_, hS4, (hg12.trans hg3).trans hg4, ?_, htyH, htyd, hP3.fr hf4, hAty, hQ⟩
  · simp only [ConRon.Arena.nestInstType, hfind, unwrapOr, StateT.run_bind, StateT.run_pure, pure_bind,
      viewLsLen_run, hvl, bne_self_eq_false, Bool.false_eq_true, ite_false, hrun3, except_ok_bind, hrun4,
      hrun5, hrunpb', hview', hrunoa, hrunle, liftFueled, ite_true]
    rfl
  · simp only [List.headD_cons]; exact (decHL_length _ hdecbs).symm

section census
variable (p : Prog) (hl : NitLook p)
include hl

end census

end L.Ind
