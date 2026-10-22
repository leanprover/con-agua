import ConAgua.Arena.IndPos2SpecH

/-! # `IndPos2`'s leaves, continued (lane `indproofs2`, helper `pos`, fork E): `nestInstType`'s
relational side, `nestGrowGroup`. -/

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
    (a : AState) (key : Word) (kk : NestKey) (r : List Word)
    (h : ntyW k m vis key = some (r, m')) (hS : StageR dn vis fe m a)
    (hk : decNK m key.toNat = some kk) (hkin : NKIn m key.toNat (· < iwTop m)) (hksl : NKSl m key)
 :
    ∃ cv caps a3 q a4 tl a5 ty, fe.find? kk.cname = some (.indInfo cv caps) ∧
      a.store.lss.viewLen kk.lvls = some cv.levelParams.length ∧
      (stripPis kk.ds.length cv.type).run a = .ok (some q, a3) ∧
      (instLPFast coreWalkFuel cv.levelParams kk.lvls cv.type).run a3 = .ok (tl, a4) ∧
      (ConRon.Arena.instPisWith kk.ds tl).run a4 = .ok (some ty, a5) ∧
      StageR dn vis fe m' a5 ∧ IWGrow m m' ∧ H (r.headD 0) ∧ decI (r.headD 0) = ty := by
  have hE := hS.1.env
  have hR := hS.1.arena.1
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  have hEb : erTop m ≤ (m.arr64 EREC).size := hS.2.2.1
  have hEs : (m.arr64 EREC).size < 2 ^ 64 := hS.2.2.2.2.1
  obtain ⟨hcH, hcd, hlH, hld, hds, hdsb, hk4⟩ := nk_fields hk hkin htop
  unfold ntyW at h
  cases hef : envFindW m (rdW (m.arr64 IW) key) vis with
  | none => rw [hef] at h; simp [ntyK1] at h
  | some pr =>
  obtain ⟨r1, m1⟩ := pr
  rw [hef] at h
  have hm1 := envFindW_mem hef
  rw [hm1] at h hef
  rw [ntyK1_eq] at h
  by_cases hf0 : r1.headD 0 = 0
  · rw [if_pos hf0] at h; simp at h
  rw [if_neg hf0] at h
  obtain ⟨-, hfind, ci, hci⟩ := envFindW_hit hef hE hcH hf0
  rw [hci] at hfind
  by_cases h3 : rdW (m.arr64 EREC) (r1.tail.headD 0) ≠ 3
  · rw [if_pos h3] at h; simp at h
  rw [if_neg h3] at h
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
  · rw [if_pos hln] at h; simp at h
  rw [if_neg (by rw [hln]; simp)] at h
  by_cases hneq : (lsNodeW m (rdW (m.arr64 IW) (key + 1))).tail.headD 0 ≠ rdW (m.arr64 EREC) (q + 1 + 2)
  · rw [if_pos hneq] at h; simp at h
  rw [if_neg hneq] at h
  have hvl := lsNodeW_viewLen hR hlH hln
  rw [hld] at hvl
  have hl'eq : l'.toNat = cv.levelParams.length := by
    rw [← hlen]; rw [hln] at hneq; rw [show l' = rdW (m.arr64 EREC) (q + 1 + 2) by simpa using hneq]
  rw [hl'eq] at hvl
  rw [hrdt] at h
  -- `strip_pis`
  cases hst : stubM "strip_pis" m [rdW (m.arr64 IW) (key + 3), wt] with
  | none => rw [hst] at h; simp [ntyK3] at h
  | some pr3 =>
  obtain ⟨r3, m3⟩ := pr3
  rw [hst] at h
  obtain ⟨x3, a3, hrun3, hS3, hg3, hx3⟩ := stripPis_spec dn vis fe _ wt hwtH m m3 a r3 hst hS
  have hdsl := decHL_length m hds
  rw [← hdsl, ← hwtd] at hrun3
  cases x3 with
  | none => have : r3.headD 0 = 0 := hx3; rw [ntyK3_none (h := this)] at h; simp at h
  | some q3 =>
  rw [ntyK3_some (h := by rw [hx3.1]; decide)] at h
  -- `cv_lps`
  have hcv3 : decCVp m3 (q + 1).toNat = some cv := by
    rw [e1]; exact (erecP_ext m3).decCV ((GrowX.of_grow (q := 0) (n := 0) hg3).erecP.decCV hcv)
  cases hlp : cvLpsW k m3 (q + 1) with
  | none => rw [hlp] at h; simp [ntyK4] at h
  | some pr4 =>
  obtain ⟨r4, m4⟩ := pr4
  rw [hlp, ntyK4_some] at h
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
  cases hil : stubM "inst_lp_fast" m4 [CWF, r4.headD 0, r4.tail.headD 0, rdW (m.arr64 IW) (key + 1), wt] with
  | none => rw [hil] at h; simp [ntyK5] at h
  | some pr5 =>
  obtain ⟨r5, m5⟩ := pr5
  rw [hil, ntyK5_some] at h
  obtain ⟨tl, a4, hrun4, hS5, hg5, htlH, htld⟩ :=
    instLPFast_spec dn vis fe CWF _ _ _ _ hlH hwtH cv.levelParams m4 m5 a3 r5 hil ⟨hS4, hdec4⟩
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
  cases hiw : instW k m5 (rdW (m.arr64 IW) (key + 2)) (rdW (m.arr64 IW) (key + 3)) (r5.headD 0) with
  | none => rw [hiw] at h; simp [ntyK6] at h
  | some pr6 =>
  obtain ⟨r6, m6⟩ := pr6
  rw [hiw] at h
  obtain ⟨x6, a5, hrun5, hS6, hg6, hx6⟩ := instW_ok k dn fe vis m5 m6 a4 _ _ _ kk.ds r6 hiw hS5 htlH
    (by rw [decHL_agree (RdS.of_grow hg35) (fun j hj => hdsb j hj)]; exact hds) (by unfold NKSl at hksl; omega)
    (by have := hg35.1; exact Nat.le_trans hksl this)
  rw [htld] at hrun5
  cases x6 with
  | none => have : r6.headD 0 = 0 := hx6; rw [ntyK6_none (h := this)] at h; simp at h
  | some ty =>
  obtain ⟨hx61, hx6H, hx6d⟩ := hx6
  rw [ntyK6_some (h := by rw [hx61]; decide)] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨cv, caps, a3, q3, a4, tl, a5, ty, by rw [← hcd]; exact hfind, hvl, hrun3, hrun4, hrun5, hS6,
    (hg35.trans hg6), hx6H, hx6d⟩

/-! ## `nest_inst_type` refines `nestInstType` -/

theorem nitW_ok (k : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis ctx hi : Word) (HI : Nat)
    (hHI : hi.toNat = HI) (c : NestCtx) (m m' : Mem) (a : AState) (key : Word) (kk : NestKey) (r : List Word)
    (h : nitW k m vis ctx hi key = some (r, m')) (hS : StageR dn vis fe m a)
    (hU : UCtx dn vis fe m ctx c) (hk : decNK m key.toNat = some kk) (hkin : NKIn m key.toNat (· < iwTop m))
    (hksl : NKSl m key)
    (hMno : ∀ (m2 : Mem) (a2 : AState), StageR dn vis fe m2 a2 → ∃ mp0, noMR m2 mp0) :
    ∃ x a', (ConRon.Arena.nestInstType fe c HI kk).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ (r.headD 0).toNat = x.1 ∧ H (r.tail.headD 0) ∧ decI (r.tail.headD 0) = x.2 := by
  unfold nitW at h
  cases k with
  | zero => simp [ntyWf, nitK1] at h
  | succ k =>
  simp only [ntyWf] at h
  cases hty : ntyW k m vis key with
  | none => rw [hty] at h; simp [nitK1] at h
  | some pr1 =>
  obtain ⟨r1, m1⟩ := pr1
  rw [hty, nitK1_some] at h
  obtain ⟨cv, caps, a3, q, a4, tl, a5, ty, hfind, hvl, hrun3, hrun4, hrun5, hS1, hg1, htyH, htyd⟩ :=
    ntyW_ok k dn fe vis m m1 a key kk r1 hty hS hk hkin hksl
  -- `pi_binders`
  cases hpb : piBW (k + 1) m1 CWF (r1.headD 0) with
  | none => rw [hpb] at h; simp [nitK2] at h
  | some pr2 =>
  obtain ⟨rs, m2⟩ := pr2
  rw [hpb, nitK2_eq] at h
  obtain ⟨bs, e, hrunpb, hdecbs, hresH, hresd, hS2, hg2, hbsb⟩ := piBW_cwf hpb hS1 htyH
  by_cases hv0 : eViewW m2 (rs.getD 2 0) = []
  · rw [if_pos hv0] at h; simp at h
  rw [if_neg hv0] at h
  by_cases hv2 : (eViewW m2 (rs.getD 2 0)).headD 0 ≠ 2
  · rw [if_pos hv2] at h; simp at h
  rw [if_neg hv2] at h
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
  cases hoa : noaW (k + 1) m2 (rdW (m2.arr64 IW) ctx) (rdW (m2.arr64 IW) (ctx + 1)) (rdW (m2.arr64 IW) (ctx + 4)) hi
      (rs.headD 0) (rs.getD 1 0) with
  | none => rw [hoa] at h; simp [nitK4] at h
  | some pr3 =>
  obtain ⟨r3, m3⟩ := pr3
  rw [hoa] at h
  obtain ⟨b, hrunoa, hS3, hg3, hr3⟩ := noaW_ok dn fe vis _ _ _ _ c.names hMno (k + 1) m2 m3 a5 _ _ bs r3 hoa hS2
    hn2 hne2 hdecbs (fun j hj => by omega)
  rw [hnP2, hHI] at hrunoa
  cases b with
  | true => rw [nitK4_occ (h := by rw [hr3]; decide)] at h; simp at h
  | false =>
  rw [nitK4_ok (h := by rw [hr3]; decide)] at h
  -- the sorts
  have hU3 := hU2.grow hg3
  have htop3 : iwTop m3 < 2 ^ 64 := Nat.lt_of_le_of_lt hS3.2.1 hS3.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, hsH, hsd, -⟩ := ctx_fields hU3.dec hU3.inn htop3
  cases hle : lveW m3 ((eViewW m2 (rs.getD 2 0)).tail.headD 0) (rdW (m3.arr64 IW) (ctx + 9)) with
  | none => rw [hle] at h; simp [nitK5] at h
  | some pr4 =>
  obtain ⟨r4, m4⟩ := pr4
  rw [hle] at h
  have huH' : H ((eViewW m2 (rs.getD 2 0)).tail.headD 0) := by rw [← getD1_eq]; exact huH
  obtain ⟨b', a6, hrunle, hS4, hg4, hr4⟩ := lveW_ok dn vis fe m3 m4 a5 _ _ huH' hsH r4 hle hS3
  rw [← getD1_eq, hud, hsd] at hrunle
  cases b' with
  | false => rw [nitK5_none (h := by rw [hr4]; decide)] at h; simp at h
  | true =>
  rw [nitK5_some (h := by rw [hr4]; decide)] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨(bs.length, ty), a6, ?_, hS4, (hg12.trans hg3).trans hg4, ?_, htyH, htyd⟩
  · have hrunpb' : (ConRon.Arena.piBinders coreWalkFuel ty).run a5 = .ok ((bs, e), a5) := htyd ▸ hrunpb
    have hview' : (view e).run a5 = .ok (.sort u, a5) := view_run _ _ _ (hresd ▸ hview)
    simp only [ConRon.Arena.nestInstType, hfind, unwrapOr, StateT.run_bind, StateT.run_pure, pure_bind,
      viewLsLen_run, hvl, bne_self_eq_false, Bool.false_eq_true, ite_false, hrun3, except_ok_bind, hrun4,
      hrun5, hrunpb', hview', hrunoa, hrunle, liftFueled, ite_true]
    rfl
  · simp only [List.headD_cons]; exact (decHL_length _ hdecbs).symm


section census
variable (p : Prog) (hl : NitLook p)
include hl

/-- **`nest_inst_type` refines `nestInstType`** (through the `strip_pis`/`inst_lp_fast`/
`instantiate1_fast`/`lvl_eq` stubs; the key's `ds` slice ends below the top, the `nest_occ` memo well-formed in every stage state). -/
@[refines ConRon.Arena.nestInstType]
theorem nestInstType_refines (k : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis ctx hi key : Word) (c : NestCtx) (kk : NestKey) (hS : StageR dn vis fe s₀.mem a₀)
    (hU : UCtx dn vis fe s₀.mem ctx c) (hk : decNK s₀.mem key.toNat = some kk)
    (hkin : NKIn s₀.mem key.toNat (· < iwTop s₀.mem)) (hksl : NKSl s₀.mem key)
    (hMno : ∀ (m2 : Mem) (a2 : AState), StageR dn vis fe m2 a2 → ∃ mp0, noMR m2 mp0) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "nest_inst_type" [vis, ctx, hi, key]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.nestInstType fe c hi.toNat kk) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.nestInstType fe c hi.toNat kk) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      (r.headD 0).toNat = (AM.res (ConRon.Arena.nestInstType fe c hi.toNat kk) a₀).1 ∧
      H (r.tail.headD 0) ∧ decI (r.tail.headD 0) = (AM.res (ConRon.Arena.nestInstType fe c hi.toNat kk) a₀).2;
      ⊤⦄ := by
  refine triple_post (nestInstType_spec p hl k s₀ vis ctx hi key) ?_
  rintro r s' ⟨hlc, hm⟩
  obtain ⟨x, a', hrun, hS', hg, h1, h2, h3⟩ := nitW_ok k dn fe vis ctx hi hi.toNat rfl c _ _ a₀ key kk _ hm hS
    hU hk hkin hksl hMno
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hlc, hok, by rw [hst]; exact hS', hg, by rw [hres]; simpa using h1, by simpa using h2,
    by rw [hres]; simpa using h3⟩

end census

end L.Ind
