import ConAgua.Arena.IndPosSpec.Grow
import ConAgua.Arena.IndPosSpec.NitLe
import ConAgua.Arena.IndPosSpec.NtyW

/-!
# NitW

`nitK5_none`, `nitK4_occ`, `ntyW_mfr`, `nitW_ok`.
-/

section

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section arms
variable (cR : CallM) (k : Nat) (m1 m2 m4 m5 : Mem) (ctx hi ty : Word) (r1 rs r4 r5 v : List Word)
theorem nitK5_none (h : r5.headD 0 = 0) : nitK5 ty rs (some (r5, m5)) = none := by rw [nitK5, ite_eq_left h]
theorem nitK4_occ (h : r4.headD 0 ≠ 0) : nitK4 cR k ctx ty rs v (some (r4, m4)) = none := by
  rw [nitK4, ite_eq_left h]
end arms
attribute [ind_grind] nitK5_none nitK4_occ

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem ntyW_mfr {cR : CallM} (hF : IlpFr cR) {k : Nat} {m m' : Mem} {vis key : Word} {r : List Word}
    (h : ntyW cR k m vis key = some (r, m')) : MFr [] [] m m' := by
  simp only [ntyW, ntyK1.eq_def, ntyK3.eq_def, ntyK4.eq_def, ntyK5.eq_def, ntyK6.eq_def] at h
  have hI : ∀ {a m r m'}, cR k "inst_lp_fast" a m = some (r, m') → MFr [] [] m m' := fun h =>
    let ⟨_, _, hA, hC, hf⟩ := hF _ _ _ _ _ h; MFr.of_frame hf hA hC
  mfr_auto h [envFindW_mfr, fun h => MFr.of_iw (stripF_frame h), posmemo_cvLpsW_mfr, hI, instW_mfr _ _ _ _ _ _ _]

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

end L.Ind

end

end
