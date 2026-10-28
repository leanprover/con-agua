import ConAgua.Arena.WhnfCoreProj
import ConAgua.Arena.IndPosSpec.Grow
import ConAgua.Arena.IndPosSpec.NitLe
import ConAgua.Arena.IndPosSpec.NtyW
import ConAgua.Arena.IndGrindAttr

/-!
# NitW

`nitK5_none`, `nitK4_occ`, `ntyT`, `NtyPost`, `NtyOk`, `nitW_ok`.
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

/-- `nestInstType` up to the instantiated container type `ty`, then `K ty`. -/
def ntyT {β : Type} (fe : IFEnv) (key : NestKey) (K : EIdx → AM β) : AM β := do
  let cvC ← unwrapOr
    (match fe.find? key.cname with
     | some (.indInfo cv _) => some cv
     | _ => none)
    (.internal "nested positivity: container vanished")
  match ← viewLsLen key.lvls with
  | none => failDanglingLs
  | some nl =>
    if nl != cvC.levelParams.length then
      fail (.invalid "nested positivity: incorrect number of universe levels for a nested inductive datatype (official: incorrect number of universe levels)")
    else
      match ← stripPis key.ds.length cvC.type with
      | none => fail (.invalid "nested positivity: invalid nested inductive datatype, its type does not bind its parameters (official: ill-formed inductive type)")
      | some _ => do
        let tl ← instLPFast coreWalkFuel cvC.levelParams key.lvls cvC.type
        match ← ConRon.Arena.instPisWith key.ds tl with
        | none => fail (.invalid "nested positivity: invalid nested inductive datatype, its type does not bind its parameters (official: ill-formed inductive type)")
        | some ty => K ty

/-- What `nest_inst_type_ty` gives besides the twin's type `ty` (from `m`, `a`): the twin's steps,
the stage, the growth, the result word, the frames. -/
structure NtyPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (kk : NestKey)
    (m : Mem) (a : AState) (w : Word) (m' : Mem) (ty : EIdx) (a' : AState) : Prop where
  steps : ∃ cv caps q a3 a4 tl, fe.find? kk.cname = some (.indInfo cv caps) ∧
    a.store.lss.viewLen kk.lvls = some cv.levelParams.length ∧
    (stripPis kk.ds.length cv.type).run a = .ok (some q, a3) ∧
    (instLPFast coreWalkFuel cv.levelParams kk.lvls cv.type).run a3 = .ok (tl, a4) ∧
    (ConRon.Arena.instPisWith kk.ds tl).run a4 = .ok (some ty, a')
  stage : StageR dn vis fe m' a'
  grow : IWGrow m m'
  hw : H w
  dec : decI w = ty
  abs : AFr m m'
  mfr : MFr [] [] m m'

/-- **`nest_inst_type_ty`'s ok half through a reading `cR`**: its run refines `ntyT` (at the
real calls: `nty_ok`, `Verdict/PosNty.lean`). -/
def NtyOk (cR : CallM) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (k : Nat) (m : Mem)
    (a : AState) (key : Word) : Prop :=
  ∀ (kk : NestKey) (r1 : List Word) (m1 : Mem), StageR dn vis fe m a → decNK m key.toNat = some kk →
    NKIn m key.toNat (· < iwTop m) → NKSl m key → ntyR cR k m vis key = some (r1, m1) →
    ∃ ty a', NtyPost dn vis fe kk m a (r1.headD 0) m1 ty a'

theorem nitW_ok (k : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis ctx hi : Word) (HI : Nat)
    (hHI : hi.toNat = HI) (c : NestCtx) (m m' : Mem) (a : AState) (key : Word) (kk : NestKey) (r : List Word)
    (cR : CallM) (hTy : NtyOk cR dn vis fe k m a key) (Q : Mem → AState → Prop)
    (hLE : NitLe cR k dn vis fe ctx hi key c kk Q m a)
    (h : nitW cR k m vis ctx hi key = some (r, m')) (hS : StageR dn vis fe m a)
    (hU : UCtx dn vis fe m ctx c) (hk : decNK m key.toNat = some kk) (hkin : NKIn m key.toNat (· < iwTop m))
    (hksl : NKSl m key) (hP : PosMR m) :
    ∃ x a', (ConRon.Arena.nestInstType fe c HI kk).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ (r.headD 0).toNat = x.1 ∧ H (r.tail.headD 0) ∧ decI (r.tail.headD 0) = x.2 ∧
      PosMR m' ∧ (∀ r1 m1, ntyR cR k m vis key = some (r1, m1) → AFr m m1) ∧ Q m' a' := by
  unfold nitW at h
  rcases hty : ntyR cR k m vis key with _ | ⟨r1, m1⟩ <;> rw [hty] at h; · simp [nitK1] at h
  rw [nitK1_some] at h
  obtain ⟨ty, a5, ⟨cv, caps, q, a3, a4, tl, hfind, hvl, hrun3, hrun4, hrun5⟩, hS1, hg1, htyH, htyd, hA1, hM1⟩ :=
    hTy kk r1 m1 hS hk hkin hksl hty
  -- `pi_binders`
  rcases hpb : piBW k m1 CWF (r1.headD 0) with _ | ⟨rs, m2⟩ <;> rw [hpb] at h; · simp [nitK2] at h
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
  rcases hoa : noaW k m2 (rdW (m2.arr64 IW) ctx) (rdW (m2.arr64 IW) (ctx + 1)) (rdW (m2.arr64 IW) (ctx + 4)) hi
      (rs.headD 0) (rs.getD 1 0) with _ | ⟨r3, m3⟩; · rw [hoa] at h; simp [nitK4] at h
  rw [hoa] at h
  obtain ⟨b, hrunoa, hS3, hg3, hr3, hP3⟩ := noaW_ok dn fe vis _ _ _ _ c.names k m2 m3 a5 _ _ bs r3 hoa hS2
    hn2 hne2 hdecbs (fun j hj => by omega) ((hP.fr hM1).fr (piBW_mfr _ _ _ _ _ _ hpb))
  rw [hnP2, hHI] at hrunoa
  cases b with
  | true => rw [nitK4_occ (h := by rw [hr3]; decide)] at h; simp at h
  | false =>
  rw [nitK4_ok (h := by rw [hr3]; decide)] at h
  -- the sorts
  have hU3 := hU2.grow hg3
  have htop3 : iwTop m3 < 2 ^ 64 := Nat.lt_of_le_of_lt hS3.2.1 hS3.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, hsH, hsd, -⟩ := ctx_fields hU3.dec hU3.inn htop3
  rcases hle : lveC cR k m3 ((eViewW m2 (rs.getD 2 0)).tail.headD 0) (rdW (m3.arr64 IW) (ctx + 9)) with _ | ⟨r4, m4⟩ <;> rw [hle] at h; · simp [nitK5] at h
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
  refine ⟨(bs.length, ty), a6, ?_, hS4, (hg12.trans hg3).trans hg4, ?_, htyH, htyd, hP3.fr hf4, fun _ _ e => by cases e; exact hA1, hQ⟩
  · simp only [ConRon.Arena.nestInstType, hfind, unwrapOr, StateT.run_bind, StateT.run_pure, pure_bind,
      viewLsLen_run, hvl, bne_self_eq_false, Bool.false_eq_true, ite_false, hrun3, except_ok_bind, hrun4,
      hrun5, hrunpb', hview', hrunoa, hrunle, liftFueled, ite_true]
    rfl
  · simp only [List.headD_cons]; exact (decHL_length _ hdecbs).symm

end L.Ind

end

end
