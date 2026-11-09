module

public import ConAgua.Verdict.VCtx
public import ConAgua.Arena.IndT.Base
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.DeclCvg
public import ConAgua.Arena.IndRealWalk
public import ConAgua.Arena.TwinStep
public import ConRon.Bridge.Checker.Hyp
public import ConLeche.Verify.Shift
public import ConAgua.Arena.IndRealFvtD
public import ConAgua.Arena.IndT.StreamRecsOpa
import ConAgua.Arena.IndRealWalkT
import ConAgua.Arena.DeclCvgT
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.RefWalk
import ConAgua.Arena.IndInstallSpec.DomsW
import ConRon.Bridge.Inductives.StreamRecs
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
import all ConAgua.Arena.IndStream

@[expose] public section

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- The lookups of the stored type's and rules' checks. -/
structure StrTyProg (p : Prog) : Prop where
  cvg : CvgProg p
  sc : p.lookup "stream_closed" = some streamClosedL
  ftd : FtdF p
  opf : OpfF p
  opa : p.lookup "open_pis_at_fvars" = some openPisAtFvarsL
  rda : p.lookup "rec_doms_at" = some recDomsAtL
  rto : p.lookup "rec_ty_opened" = some recTyOpenedL
  rtc : p.lookup "rec_ty_check" = some recTyCheckL
  ra : p.lookup "rule_agree" = some ruleAgreeL

set_option experimental.vcgen true in
/-- **`stream_closed`'s unified model**: the two walks through their `Option` models. -/
l_model scE_spec (p : Prog) (hP : StrTyProg p)
  fns [hP.sc ↦ scE]
  specs [lbbF_spec p hP.cvg.bvb n, hffF_spec p hP.cvg.hf n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

set_option experimental.vcgen true in
/-- **`rec_doms_at`'s unified model**: `fvar_type_d` lifted, `is_def_eq_core` through its call,
the recursion through the model. -/
l_model rdaE_spec (p : Prog) (hP : StrTyProg p)
  fns [hP.rda ↦ rdaE]
  specs [ftdF_spec0 p hP.ftd n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `stream_closed` gives besides the twin's answer `b`: the stage, the growth, the memos,
the word `w` the answer. -/
structure ScPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (w : Word) (m' : Mem) (b : Bool) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  abs : AbsOK m'
  val : w = 0 ↔ b = false

section sims
variable {p : Prog} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
  {env : ConLeche.Env}

open ConRon.Bridge.Inductives.RC (looseBVarsBoundedFast_pstep hasFvarFast_pstep) in
/-- **`stream_closed` refines `streamClosed`** (no error of its own): the bounded-variables walk,
then the two free-variable walks, each by its `StageT` relation, `StageC` after by con-ron's
steps. -/
theorem sc_ref {G : Prop} {m : Mem} {a : AState} {s g : Word} (hs : H s)
    (hg : H g) (hC : StageC dn vis fe env m a) (hA : AbsOK m) {sP gP : ConLeche.Expr}
    (hsP : denoteE a.store (decI s) = some sP) (hgP : denoteE a.store (decI g) = some gP) :
    RefE G (scE p m s g) (ConRon.Arena.streamClosed (decI s) (decI g)) a
      (fun v b a' => ScPost dn vis fe env m v.1 v.2 b a') := by
  rw [scE.arm1]; unfold ConRon.Arena.streamClosed
  refine RefE.bindSim (fun _ => rfl) (fun r m' h => lbbF_okT dn vis fe CWF 0 s hs m m' a r h hC.stageT)
    fun r1 x1 m1 a1 h1 hrun1 ⟨hT1, hg1, hx1, _⟩ => ?_
  obtain ⟨p1, -⟩ := looseBVarsBoundedFast_pstep hC.check.state hsP hrun1
  have hA1 : AbsOK m1 := AFr.of_frame (lbbF_frame h1) (by decide) (by decide) hA
  have hC1 := hC.of_pstep hT1.stage hA1 p1
  dsimp only [scE.k_loose_bvars_bounded_fast]
  refine RefE.splitNot (fun h => by rw [← hx1, h]; decide) (fun h => by
      cases hx : x1
      · rw [hx] at hx1; simpa using hx1
      · exact absurd hx h) (fun _ _ => RefE.ret rfl ⟨hC1, hg1, hA1, by simp⟩) fun _ _ => ?_
  refine RefE.bindSim (fun _ => rfl)
    (fun r m' h => hffF_okT dn vis fe CWF s hs m1 m' a1 r h hC1.stageT)
    fun r2 x2 m2 a2 h2 hrun2 ⟨hT2, hg2, hx2, _⟩ => ?_
  obtain ⟨p2, -⟩ := hasFvarFast_pstep hC1.check.state (ConRon.Bridge.denote_ext hsP p1.ext) hrun2
  have hA2 : AbsOK m2 := AFr.of_frame (hffF_frame h2) (by decide) (by decide) hA1
  have hC2 := hC1.of_pstep hT2.stage hA2 p2
  dsimp only [scE.k_has_fvar_fast]
  refine RefE.split (fun h => by rw [← hx2]; simpa using h) (fun h => by rw [← hx2] at h; simpa using h)
    (fun _ _ => RefE.ret rfl ⟨hC2, hg1.trans hg2, hA2, by simp⟩) fun _ _ => ?_
  refine RefE.bindSim (fun _ => rfl)
    (fun r m' h => hffF_okT dn vis fe CWF g hg m2 m' a2 r h hC2.stageT)
    fun r3 x3 m3 a3 h3 hrun3 ⟨hT3, hg3, hx3, _⟩ => ?_
  obtain ⟨p3, -⟩ := hasFvarFast_pstep hC2.check.state
    (ConRon.Bridge.denote_ext hgP (p1.ext.trans p2.ext)) hrun3
  have hA3 : AbsOK m3 := AFr.of_frame (hffF_frame h3) (by decide) (by decide) hA2
  refine RefE.ret rfl ⟨hC2.of_pstep hT3.stage hA3 p3, (hg1.trans hg2).trans hg3, hA3, ?_⟩
  rw [← hx3]
  grind

/-- What a check of the stored recursors gives besides the twin's run (from `m`, `a`): the stage,
the growth, the memos, the core step. -/
structure SrPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (a : AState) (m' : Mem) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  abs : AbsOK m'
  core : ConRon.Bridge.CoreStep env fe a a'

theorem SrPost.refl {m : Mem} {a : AState} (hC : StageC dn vis fe env m a) (hA : AbsOK m) :
    SrPost dn vis fe env m a m a :=
  ⟨hC, IWGrow.refl m, hA, ConRon.Bridge.CoreStep.refl hC.check⟩

theorem SrPost.trans {m m₁ m₂ : Mem} {a a₁ a₂ : AState} (h₁ : SrPost dn vis fe env m a m₁ a₁)
    (h₂ : SrPost dn vis fe env m₁ a₁ m₂ a₂) : SrPost dn vis fe env m a m₂ a₂ :=
  ⟨h₂.stage, h₁.grow.trans h₂.grow, h₂.abs, h₁.core.trans h₂.core⟩

open ConRon.Bridge.Inductives (denoteEList_getElem? fvarTypeD_run) in
/-- **`rec_doms_at` refines `recDomsAt`, both outcomes** (twin side con-ron's `recDomsAt_spec`):
per binder the two domains (`fvar_type_d`, `ftdW_ok`), `is_def_eq_core` (`isDefEqC_rsim`; its
error the core stub's claim) and its guard, the rest by induction. -/
theorem rda_ref (hq : KnotStageProg p) (henv : ConLeche.EnvWF env) (N : Nat) (hN : N ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (so sl go gl j k : Word) (sfvs gfvs : List EIdx)
      (sfvsP gfvsP : List ConLeche.Expr),
    StageC dn vis fe env m a → AbsOK m →
    decHL m so.toNat sl.toNat = some sfvs → decHL m go.toNat gl.toNat = some gfvs →
    so.toNat + sl.toNat ≤ iwTop m → go.toNat + gl.toNat ≤ iwTop m →
    Frontend.denoteEList a.store sfvs = some sfvsP → Frontend.denoteEList a.store gfvs = some gfvsP →
    (∀ (i : Nat) (x : ConLeche.Expr), sfvsP[i]? = some x → ConLeche.Expr.WScoped i x.fvarTypeD) →
    (∀ (i : Nat) (x : ConLeche.Expr), gfvsP[i]? = some x → ConLeche.Expr.WScoped i x.fvarTypeD) →
    RefE (VerdictCtxU p) (rdaE p N m vis so sl go gl j k)
      (ConRon.Arena.recDomsAt V fe sfvs gfvs j.toNat k.toNat) a
      (fun v _ a' => SrPost dn vis fe env m a v.2 a') := by
  induction N with
  | zero => intros; rw [rdaE.eq_1]; exact RefE.of_cls0 rfl
  | succ N ih =>
  intro m a so sl go gl j k sfvs gfvs sfvsP gfvsP hC hA hs hg hsb hgb hsP hgP hcs hcg
  by_cases hk : k = 0
  · rw [rdaE.arm1 _ _ _ _ _ _ _ _ _ _ hk, show k.toNat = 0 by rw [hk]; rfl,
      ConRon.Arena.recDomsAt.eq_1]
    exact RefE.ret rfl (SrPost.refl hC hA)
  obtain ⟨k', hk'⟩ : ∃ k', k.toNat = k' + 1 :=
    ⟨k.toNat - 1, by have : k.toNat ≠ 0 := fun h => hk (UInt64.toNat_inj.mp (by simpa using h)); omega⟩
  rw [hk', ConRon.Arena.recDomsAt.eq_2]
  by_cases hsl : sl ≤ j
  · rw [rdaE.abort1 _ _ _ _ _ _ _ _ _ _ hk hsl]; exact RefE.of_cls0 rfl
  by_cases hgl : gl ≤ j
  · rw [rdaE.abort2 _ _ _ _ _ _ _ _ _ _ hk hsl hgl]; exact RefE.of_cls0 rfl
  rw [rdaE.arm2 _ _ _ _ _ _ _ _ _ _ hk hsl hgl]
  have hjs : j.toNat < sl.toNat := by simpa [UInt64.le_iff_toNat_le] using hsl
  have hjg : j.toNat < gl.toNat := by simpa [UInt64.le_iff_toNat_le] using hgl
  have hsz : (m.arr64 IW).size < 2 ^ 64 := hC.stage.iw.iwSize
  obtain ⟨ws, ews, hwsH, hws⟩ := decHL_word hs hsz j.toNat hjs
  obtain ⟨wg, ewg, hwgH, hwg⟩ := decHL_word hg hsz j.toNat hjg
  simp only [UInt64.ofNat_toNat, Nat.toUInt64_eq] at ews ewg
  rw [ews, hws, hwg]
  obtain ⟨xs, hxs, hdxs⟩ := (denoteEList_getElem? hsP j.toNat).2 _ hws
  obtain ⟨xg, hxg, hdxg⟩ := (denoteEList_getElem? hgP j.toNat).2 _ hwg
  dsimp only
  -- the two domains
  refine RefE.bindSim (fun _ => rdaE.k_fvar_type_d.none ..)
    (Q := fun r x m₁ a₁ => m₁ = m ∧ a₁ = a ∧ x = decI (r.headD 0) ∧ H (r.headD 0))
    (fun r m₁ h => by
      obtain ⟨rfl, hrun, hH⟩ := ftdW_ok m m₁ a hC.stage.check.arena.base ws hwsH r (ftdF_eq h)
      exact ⟨_, _, hrun, rfl, rfl, rfl, hH⟩)
    fun r1 x1 m1 a1 _ hrun1 ⟨e1, e2, e3, hH1⟩ => ?_
  subst m1 a1 x1
  rw [rdaE.k_fvar_type_d.arm1, ewg]
  refine RefE.bindSim (fun _ => rdaE.k_fvar_type_d_2.none ..)
    (Q := fun r x m₁ a₁ => m₁ = m ∧ a₁ = a ∧ x = decI (r.headD 0) ∧ H (r.headD 0))
    (fun r m₁ h => by
      obtain ⟨rfl, hrun, hH⟩ := ftdW_ok m m₁ a hC.stage.check.arena.base wg hwgH r (ftdF_eq h)
      exact ⟨_, _, hrun, rfl, rfl, rfl, hH⟩)
    fun r2 x2 m2 a2 _ hrun2 ⟨e1, e2, e3, hH2⟩ => ?_
  subst m2 a2 x2
  obtain ⟨-, hd1⟩ := fvarTypeD_run hC.check.state hdxs hrun1
  obtain ⟨-, hd2⟩ := fvarTypeD_run hC.check.state hdxg hrun2
  rw [rdaE.k_fvar_type_d_2.arm1]
  -- `is_def_eq_core(vis, j, a, b)`
  refine RefE.bindCall (fun _ => rdaE.k_is_def_eq_core.eq_1 ..)
    (fun hG' _ h5 => hG'.core.isDefEqCore N (by omega) hC.stageT j _ _ hH1 hH2 _ h5)
    (isDefEqC_rsim hq henv N (by omega) hC hA j _ _ hH1 hH2 hd1 hd2 (hcs _ _ hxs) (hcg _ _ hxg))
    fun r5 m5 bb a5 _ _ ⟨hC5, hg5, hbb, hA5, c5⟩ => ?_
  refine RefE.ofArms (fun h => rdaE.k_is_def_eq_core.abort1 _ _ _ _ _ _ _ _ _ _ _ h)
    (fun h => rdaE.k_is_def_eq_core.arm1 _ _ _ _ _ _ _ _ _ _ _ h) ?_
  dsimp only at hC5 hg5 hbb hA5
  refine RefE.guard rfl (fun h => by rw [← hbb, decBool, h]; rfl)
    (fun h => by rw [← hbb] at h; simpa [decBool] using h) fun _ _ => ?_
  -- the rest
  have hj1 : (j + 1).toNat = j.toNat + 1 := by
    have := sl.toNat_lt; rw [UInt64.toNat_add]; simp; omega
  have hk1 : (k - 1).toNat = k' := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
  rw [← hj1, ← hk1]
  refine RefE.lastE (fun _ => rfl) (fun _ => rdaE.k_rec_doms_at.arm1 ..) id
    (ih (by omega) m5 a5 so sl go gl (j + 1) (k - 1) sfvs gfvs sfvsP gfvsP hC5 hA5
      (by rw [decHL_grow hg5 hsb]; exact hs) (by rw [decHL_grow hg5 hgb]; exact hg)
      (Nat.le_trans hsb hg5.iw) (Nat.le_trans hgb hg5.iw)
      (ConRon.Bridge.denoteEList_ext c5.ext _ _ hsP) (ConRon.Bridge.denoteEList_ext c5.ext _ _ hgP)
      hcs hcg) fun v y a' _ hR => ?_
  exact SrPost.trans ⟨hC5, hg5, hA5, c5⟩ hR

end sims

end L.Ind

end
