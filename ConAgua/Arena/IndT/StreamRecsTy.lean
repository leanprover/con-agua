module

public import ConAgua.Verdict.VCtx
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.TwinStep
public import ConRon.Bridge.Checker.Hyp
public import ConRon.Bridge.Inductives.Rel
public import ConLeche.Verify.Shift
public import ConAgua.Arena.IndT.StreamRecsOpa
public import ConAgua.Arena.IndRealApdT
public import ConAgua.Arena.IndRealMemoCrT
import ConAgua.Arena.IndT.WalkC
import ConAgua.Verdict.DeclValsE
import ConAgua.Verdict.DeclHdrE
import ConRon.Bridge.Checker.Names
import ConAgua.Arena.IndRealWalkT
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.RefWalk
import ConAgua.Arena.IndInstallSpec.DomsW
import ConRon.Bridge.Inductives.StreamRecs
import ConLeche.Verify.Cached.BridgeCS3
import ConLeche.Verify.Denote.IndFrame
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
import all ConAgua.Arena.IndStream
public import ConAgua.Arena.KnotEntry

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

set_option experimental.vcgen true in
/-- **`rec_ty_opened`'s unified model**: `rec_doms_at` through its model, `is_def_eq_core` through
its call. -/
l_model rtoSE_spec (p : Prog) (hP : StrTyProg p)
  fns [hP.rto ↦ rtoSE]
  specs [rdaE_spec p hP n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

section sims2
variable {p : Prog} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
  {env : ConLeche.Env}

open ConRon.Bridge.Inductives (denoteOpen_some_inv) in
/-- **`rec_ty_opened` refines `recTyOpened`, both outcomes** (twin side con-ron's
`recTyOpened_spec`): the record's telescope missing is the twin's `.invalid`, the generated one's
an abort; the domains (`rda_ref`), then the residues (`isDefEqC_rsim`) and their guard. -/
theorem rtoS_ref (hq : KnotStageProg p) (henv : ConLeche.EnvWF env) (N : Nat)
    (hN : N ≤ 2 ^ 62) {m : Mem} {a : AState} {n sok so sl sr gok go gl gr : Word}
    {xs xg : Option (List EIdx × EIdx)} {sP gP : ConLeche.Expr}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m) (hds : decOLE m [sok, so, sl, sr] xs)
    (hdg : decOLE m [gok, go, gl, gr] xg) (hws : ConLeche.Expr.WScoped 0 sP)
    (hwg : ConLeche.Expr.WScoped 0 gP)
    (hos : ConRon.Bridge.Inductives.denoteOpen a.store xs = some (ConLeche.openPisAtFvars n.toNat sP 0))
    (hog : ConRon.Bridge.Inductives.denoteOpen a.store xg = some (ConLeche.openPisAtFvars n.toNat gP 0)) :
    RefE (VerdictCtxU p) (rtoSE p N m vis n sok so sl sr gok go gl gr)
      (ConRon.Arena.recTyOpened V fe n.toNat xs xg) a
      (fun v _ a' => SrPost dn vis fe env m a v.2 a') := by
  cases N with
  | zero => exact RefE.of_cls0 rfl
  | succ N =>
  simp only [rtoSE]
  cases xs with
  | none =>
    have h0 : sok = 0 := by simpa [decOLE] using hds
    rw [ite_eq_left h0]; exact fun _ => ErrClaim.fail _ _ rfl
  | some qs =>
  obtain ⟨sfvs, srest⟩ := qs
  obtain ⟨h1, ⟨hsl, hsb⟩, hsrH, hsr⟩ := hds
  simp only [List.headD_cons] at h1
  rw [ite_eq_right (by rw [h1]; decide)]
  cases xg with
  | none =>
    have h0 : gok = 0 := by simpa [decOLE] using hdg
    rw [ite_eq_left h0]; exact RefE.of_cls0 rfl
  | some qg =>
  obtain ⟨gfvs, grest⟩ := qg
  obtain ⟨g1, ⟨hgl, hgb⟩, hgrH, hgr⟩ := hdg
  simp only [List.headD_cons] at g1
  rw [ite_eq_right (by rw [g1]; decide), ConRon.Arena.recTyOpened.eq_1]
  simp only [List.getD_cons_succ, List.getD_cons_zero, List.drop_succ_cons, List.drop_zero,
    List.headD_cons] at hsl hsb hgl hgb hsrH hsr hgrH hgr
  subst hsr hgr
  obtain ⟨sfvsP, srestP, hos', hsf, hsrP⟩ := denoteOpen_some_inv hos
  obtain ⟨gfvsP, grestP, hog', hgf, hgrP⟩ := denoteOpen_some_inv hog
  have hcs : ∀ (i : Nat) (x : ConLeche.Expr), sfvsP[i]? = some x → ConLeche.Expr.WScoped i x.fvarTypeD :=
    fun i x hx => by simpa using ConLeche.Cached.openers_fvarTypeD_WScoped hos' hws hx
  have hcg : ∀ (i : Nat) (x : ConLeche.Expr), gfvsP[i]? = some x → ConLeche.Expr.WScoped i x.fvarTypeD :=
    fun i x hx => by simpa using ConLeche.Cached.openers_fvarTypeD_WScoped hog' hwg hx
  have hrs : ConLeche.Expr.WScoped n.toNat srestP := by
    simpa using (ConLeche.openPisAtFvars_WScoped n.toNat sP 0 hos' hws).2
  have hrg : ConLeche.Expr.WScoped n.toNat grestP := by
    simpa using (ConLeche.openPisAtFvars_WScoped n.toNat gP 0 hog' hwg).2
  -- the domains
  refine RefE.bindE (fun _ => rfl) id
    (rda_ref hq henv N (by omega) m a so sl go gl 0 n sfvs gfvs sfvsP gfvsP hC hA hsl hgl hsb hgb
      hsf hgf hcs hcg) fun ⟨r1, m1⟩ _ a1 _ hR1 => ?_
  dsimp only [rtoSE.k_rec_doms_at] at hR1 ⊢
  -- the residues
  refine RefE.bindCall (fun _ => rfl)
    (fun hG' _ h5 => hG'.core.isDefEqCore N (by omega) hR1.stage.stageT n _ _ hsrH hgrH _ h5)
    (isDefEqC_rsim hq henv N (by omega) hR1.stage hR1.abs n _ _ hsrH hgrH
      (ConRon.Bridge.denote_ext hsrP hR1.core.ext) (ConRon.Bridge.denote_ext hgrP hR1.core.ext) hrs hrg)
    fun r5 m5 bb a5 _ _ ⟨hC5, hg5, hbb, hA5, c5⟩ => ?_
  dsimp only [rtoSE.k_is_def_eq_core] at hC5 hg5 hbb hA5 ⊢
  refine RefE.guardIf rfl (fun h => by rw [← hbb, decBool, h]; rfl)
    (fun h => by rw [← hbb] at h; simpa [decBool] using h) fun _ _ => ?_
  exact RefE.ret rfl (hR1.trans ⟨hC5, hg5, hA5, c5⟩)

end sims2

set_option experimental.vcgen true in
/-- **`rec_ty_check`'s unified model**: `stream_closed` and `rec_ty_opened` through their models,
the gates and the core's entry points through their calls, `open_pis_at_fvars` lifted. -/
l_model rtycE_spec (p : Prog) (hP : StrTyProg p)
  fns [hP.rtc ↦ rtycE]
  specs [scE_spec p hP n, callW_spec p n "open_pis_at_fvars", rtoSE_spec p hP n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

set_option experimental.vcgen true in
/-- **`rule_agree`'s unified model**: `stream_closed` through its model, the gates and the core's
entry points through their calls. -/
l_model raE_spec (p : Prog) (hP : StrTyProg p)
  fns [hP.ra ↦ raE]
  specs [scE_spec p hP n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

section sims3
variable {p : Prog} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
  {env : ConLeche.Env}

theorem decOLE_grow {m m' : Mem} (hg : IWGrow m m') {r : List Word}
    {x : Option (List EIdx × EIdx)} (h : decOLE m r x) : decOLE m' r x := by
  cases x with
  | none => exact h
  | some q =>
    obtain ⟨fvs, b⟩ := q
    obtain ⟨h1, ⟨hl, hb⟩, h3⟩ := h
    exact ⟨h1, ⟨by dsimp only at hl ⊢; rw [decHL_grow hg hb]; exact hl, Nat.le_trans hb hg.iw⟩, h3⟩

theorem decOLE_four {m : Mem} {r : List Word} {x : Option (List EIdx × EIdx)} (h : decOLE m r x) :
    decOLE m [r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0] x := by
  have e1 : r.getD 1 0 = r.tail.headD 0 := by rcases r with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
  have e2 : r.getD 2 0 = r.tail.tail.headD 0 := by
    rcases r with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
  have e3 : (r.drop 3).headD 0 = r.tail.tail.tail.headD 0 := by
    rcases r with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;> rfl
  cases x with
  | none => exact h
  | some q =>
    obtain ⟨fvs, b⟩ := q
    obtain ⟨h1, ⟨hl, hb⟩, h3, h4⟩ := h
    rw [e1, e2] at hl hb
    rw [e3] at h3 h4
    exact ⟨h1, ⟨hl, hb⟩, h3, h4⟩

open ConRon.Bridge.Inductives (openPisAtFvars_run PStep) in
/-- `open_pis_at_fvars`, lifted, under `StageC`: `opa_ok` with con-ron's `openPisAtFvars_run`. -/
theorem opa_sim (hP : StrTyProg p) (N : Nat) {m : Mem} {a : AState}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m) (n e : Word) (he : H e) {eP : ConLeche.Expr}
    (hd : denoteE a.store (decI e) = some eP) :
    Sim (callW p N "open_pis_at_fvars" [n, e, 0] m) (openPisAtFvars n.toNat (decI e) 0) a
      (fun r x m' a' => StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ decOLE m' r x ∧ AbsOK m' ∧
        PStep a a' ∧
        ConRon.Bridge.Inductives.denoteOpen a'.store x = some (ConLeche.openPisAtFvars n.toNat eP 0)) := by
  intro r m' h
  obtain ⟨x, a', hrun, ⟨hS', hg', hdec⟩, hA'⟩ :=
    opa_ok vis fe hP.opf hP.opa N n e 0 he m m' a r h ⟨hC.stage, hA⟩
  obtain ⟨ps, ho⟩ := openPisAtFvars_run n.toNat hC.check.state hd hrun
  exact ⟨x, a', hrun, hC.of_pstep hS' hA' ps, hg', hdec, hA', ps, ho⟩

open ConRon.Bridge.Inductives (streamClosed_run constsResolveFFast_pstep PStep) in
open ConRon.Bridge (allLevelParamsDefined_run denote_ext denoteNList_ext) in
/-- **`rec_ty_check` refines `recTyCheck`, both outcomes** (twin side con-ron's `recTyCheck_spec`):
closedness (`sc_ref`), the level parameters (`apdF_okT`), the resolution (`crfF_okT`; its reject
site calls `unresolved_consts_error`, `uce_errClaim_hi`), the inference and the sort
(`inferC_rsim`, `ensureSortC_rsim`), the two openings (`opa_sim`), then `rec_ty_opened`
(`rtoS_ref`). -/
theorem rtyc_ref (hP : StrTyProg p) (hq : KnotStageProg p) (henv : ConLeche.EnvWF env)
    (hApd : ApdF p) (hCrf : CrfF p) (N : Nat) (hN : N ≤ 2 ^ 62) {m : Mem} {a : AState}
    {lo ll n s g : Word} {lps : List NIdx} {lpsP : List ConLeche.Name} {sP gP : ConLeche.Expr}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m) (hs : H s) (hg : H g)
    (hl : decHL m lo.toNat ll.toNat = some lps) (hlb : lo.toNat + ll.toNat ≤ iwTop m)
    (hlps : Frontend.denoteNList a.store.ns lps = some lpsP)
    (hsP : denoteE a.store (decI s) = some sP) (hgP : denoteE a.store (decI g) = some gP) :
    RefE (VerdictCtxU p) (rtycE p N m vis lo ll n s g)
      (ConRon.Arena.recTyCheck V fe lps n.toNat (decI s) (decI g)) a
      (fun v _ a' => SrPost dn vis fe env m a v.2 a') := by
  cases N with
  | zero => exact RefE.of_cls0 rfl
  | succ N =>
  simp only [rtycE]
  unfold ConRon.Arena.recTyCheck
  simp only [fail_bindAM]
  -- closed
  refine RefE.bindE (fun _ => rfl) (fun _ => trivial) (sc_ref (G := True) hs hg hC hA hsP hgP)
    fun ⟨c1, m1⟩ b1 a1 hrun1 ⟨hC1, hg1, hA1, hv1⟩ => ?_
  obtain ⟨p1, hb1⟩ := streamClosed_run hC.check.state hsP hgP hrun1
  dsimp only [rtycE.k_stream_closed] at hv1 ⊢
  refine RefE.guardIf rfl (fun h => hv1.mp h) (fun h => hv1.mpr h) fun _ hb => ?_
  rw [hb1] at hb
  have hfs : sP.hasFvar = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hb; exact hb.1.2
  have hfg : gP.hasFvar = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hb; exact hb.2
  have hws : ConLeche.Expr.WScoped 0 sP := ConLeche.Expr.WScoped.of_not_hasFvar hfs
  have hwg : ConLeche.Expr.WScoped 0 gP := ConLeche.Expr.WScoped.of_not_hasFvar hfg
  -- the level parameters
  have hl1 : decHL m1 lo.toNat ll.toNat = some lps := by rw [decHL_grow hg1 hlb]; exact hl
  have hlps1 := denoteNList_ext p1.ext.lss.ls.ns _ _ hlps
  have hsP1 := denote_ext hsP p1.ext
  refine RefE.bindCall (fun _ => rfl) (fun hG _ h8 => nvl hG.nv (by decide +kernel) h8)
    (fun b h8 => apdF_okT dn vis fe lo ll s hs lps m1 b.2 a1 b.1 (apdF_of_callW hApd h8)
      ⟨hC1.stageT, hl1, lpsP, denoteNList_mapM hlps1⟩)
    fun r2 m2 x2 a2 h2 hrun2 ⟨hT2, hg2, hx2, _⟩ => ?_
  obtain ⟨h2st, h2c, h2p, -⟩ := allLevelParamsDefined_run hC1.check.state hlps1 hsP1 hrun2
  have p2 : PStep a1 a2 := PStep.of_caches ⟨by rw [h2st]; exact hC1.check.state.wf⟩
    (by rw [h2st]; exact ConRon.Arena.Ext.refl _) h2c h2p
  have hA2 : AbsOK m2 := absOK_apdF (apdF_of_callW hApd (callW_of_callE h2)) hA1 hT2
  have hC2 := hC1.of_pstep hT2.stage hA2 p2
  dsimp only [rtycE.k_all_level_params_defined]
  refine RefE.guardIf rfl (fun h => by rw [← hx2, h]; rfl)
    (fun h => by rw [← hx2] at h; simpa using h) fun _ _ => ?_
  -- the resolution
  have hsP2 := denote_ext hsP1 p2.ext
  refine RefE.bindCall (fun _ => rfl) (fun hG _ h9 => nvl hG.nv (by decide +kernel) h9)
    (fun b h9 => crfF_okT dn vis fe s hs m2 b.2 a2 b.1 (crfF_of_callW hCrf h9)
      ⟨hC2.stageT, hA2.crMemo⟩)
    fun r3 m3 x3 a3 h3 hrun3 ⟨⟨hT3, hg3, hx3, _⟩, hCr3⟩ => ?_
  obtain ⟨p3, -⟩ := constsResolveFFast_pstep hC2.check.toR hsP2 hrun3
  have hA3 : AbsOK m3 := absOK_crfF' (crfF_of_callW hCrf (callW_of_callE h3)) hA2 hCr3.crOK hT3
  have hC3 := hC2.of_pstep hT3.stage hA3 p3
  dsimp only [rtycE.k_consts_resolve_ffast]
  refine RefE.splitNot (fun h => by rw [← hx3, h]; decide)
    (fun h => by rw [← hx3] at h; simpa using h) (fun _ _ => ?_) fun _ _ => ?_
  · rcases h10 : callE p N "unresolved_consts_error" [vis, s, 5] m3 with e10 | ⟨r10, m10⟩ <;>
      dsimp only [rtycE.k_unresolved_consts_error]
    · obtain ⟨M3, hC3'⟩ := hC3.stageT.core
      exact fun hG => uce_errClaim_hi hG.uce hG.nv hC3'.arena.base hC3'.pins hs (by decide) h10 _
    · exact RefE.of_cls0 rfl
  -- the inference, the sort
  have hsP3 := denote_ext hsP2 p3.ext
  refine RefE.bindCall (fun _ => rfl)
    (fun hG _ h4 => hG.core.inferTypeCore N (by omega) hC3.stageT 0 s hs _ h4)
    (inferC_rsim hq henv N (by omega) hC3 hA3 0 s hs hsP3 hws)
    fun r4 m4 x4 a4 _ _ ⟨hC4, hg4, hd4, hA4, c4, w4, hw4, hsc4⟩ => ?_
  dsimp only [rtycE.k_infer_type_core] at hC4 hg4 hd4 hA4 ⊢
  obtain ⟨hH4, hx4⟩ := hd4
  subst hx4
  refine RefE.bindCall (fun _ => rfl)
    (fun hG _ h5 => hG.core.ensureSortCore N (by omega) hC4.stageT 0 _ hH4 _ h5)
    (ensureSortC_rsim hq henv N (by omega) hC4 hA4 0 _ hH4 hw4 hsc4)
    fun r5 m5 x5 a5 _ _ ⟨hC5, hg5, _, hA5, c5, _⟩ => ?_
  dsimp only [rtycE.k_ensure_sort_core] at hC5 hg5 hA5 ⊢
  have c15 : ConRon.Bridge.CoreStep env fe a a5 :=
    ((((p1.trans p2).trans p3).toCore hC.check).trans c4).trans c5
  -- the two openings
  refine RefE.bindSim (fun _ => rfl) (opa_sim hP N hC5 hA5 n s hs (denote_ext hsP c15.ext))
    fun r6 x6 m6 a6 _ _ ⟨hC6, hg6, hd6, hA6, p6, ho6⟩ => ?_
  dsimp only [rtycE.k_open_pis_at_fvars]
  refine RefE.bindSim (fun _ => rfl)
    (opa_sim hP N hC6 hA6 n g hg (denote_ext hgP (c15.ext.trans p6.ext)))
    fun r7 x7 m7 a7 _ _ ⟨hC7, hg7, hd7, hA7, p7, ho7⟩ => ?_
  dsimp only [rtycE.k_open_pis_at_fvars_2]
  -- `rec_ty_opened`
  refine RefE.lastE (K := rtycE.k_rec_ty_opened p) (f := fun v => (0, v.2)) (fun _ => rfl)
    (fun _ => rfl) id (rtoS_ref hq henv N (by omega) hC7 hA7 (decOLE_four (decOLE_grow hg7 hd6)) (decOLE_four hd7)
      hws hwg (ConRon.Bridge.Inductives.SR.denoteOpen_ext p7.ext _ _ ho6) ho7) fun v y a' _ hR => ?_
  exact SrPost.trans ⟨hC7, ((((((hg1.trans hg2).trans hg3).trans hg4).trans hg5).trans hg6).trans hg7),
    hA7, c15.trans ((p6.trans p7).toCore hC5.check)⟩ hR

end sims3

section sims4
variable {p : Prog} {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
  {env : ConLeche.Env}

open ConRon.Bridge.Inductives (streamClosed_run constsResolveFFast_pstep PStep) in
open ConRon.Bridge (allLevelParamsDefined_run denote_ext denoteNList_ext) in
/-- **`rule_agree` refines `ruleAgree`, both outcomes** (twin side con-ron's `ruleAgree_spec`):
closedness, the level parameters, the resolution (its reject site `unresolved_consts_error`) as
in `rtyc_ref`, the two inferences (`inferC_rsim`), the two definitional equalities
(`isDefEqC_rsim`) and their guards. -/
theorem ra_ref (hq : KnotStageProg p) (henv : ConLeche.EnvWF env)
    (hApd : ApdF p) (hCrf : CrfF p) (N : Nat) (hN : N ≤ 2 ^ 62) {m : Mem} {a : AState}
    {lo ll s g : Word} {lps : List NIdx} {lpsP : List ConLeche.Name} {sP gP : ConLeche.Expr}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m) (hs : H s) (hg : H g)
    (hl : decHL m lo.toNat ll.toNat = some lps) (hlb : lo.toNat + ll.toNat ≤ iwTop m)
    (hlps : Frontend.denoteNList a.store.ns lps = some lpsP)
    (hsP : denoteE a.store (decI s) = some sP) (hgP : denoteE a.store (decI g) = some gP) :
    RefE (VerdictCtxU p) (raE p N m vis lo ll s g)
      (ConRon.Arena.ruleAgree V fe lps (decI s) (decI g)) a
      (fun v _ a' => SrPost dn vis fe env m a v.2 a') := by
  cases N with
  | zero => exact RefE.of_cls0 rfl
  | succ N =>
  simp only [raE]
  unfold ConRon.Arena.ruleAgree
  simp only [fail_bindAM]
  -- closed
  refine RefE.bindE (fun _ => rfl) (fun _ => trivial) (sc_ref (G := True) hs hg hC hA hsP hgP)
    fun ⟨c1, m1⟩ b1 a1 hrun1 ⟨hC1, hg1, hA1, hv1⟩ => ?_
  obtain ⟨p1, hb1⟩ := streamClosed_run hC.check.state hsP hgP hrun1
  dsimp only [raE.k_stream_closed] at hv1 ⊢
  refine RefE.guardIf rfl (fun h => hv1.mp h) (fun h => hv1.mpr h) fun _ hb => ?_
  rw [hb1] at hb
  have hfs : sP.hasFvar = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hb; exact hb.1.2
  have hfg : gP.hasFvar = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hb; exact hb.2
  have hws : ConLeche.Expr.WScoped 0 sP := ConLeche.Expr.WScoped.of_not_hasFvar hfs
  have hwg : ConLeche.Expr.WScoped 0 gP := ConLeche.Expr.WScoped.of_not_hasFvar hfg
  -- the level parameters
  have hl1 : decHL m1 lo.toNat ll.toNat = some lps := by rw [decHL_grow hg1 hlb]; exact hl
  have hlps1 := denoteNList_ext p1.ext.lss.ls.ns _ _ hlps
  have hsP1 := denote_ext hsP p1.ext
  refine RefE.bindCall (fun _ => rfl) (fun hG _ h8 => nvl hG.nv (by decide +kernel) h8)
    (fun b h8 => apdF_okT dn vis fe lo ll s hs lps m1 b.2 a1 b.1 (apdF_of_callW hApd h8)
      ⟨hC1.stageT, hl1, lpsP, denoteNList_mapM hlps1⟩)
    fun r2 m2 x2 a2 h2 hrun2 ⟨hT2, hg2, hx2, _⟩ => ?_
  obtain ⟨h2st, h2c, h2p, -⟩ := allLevelParamsDefined_run hC1.check.state hlps1 hsP1 hrun2
  have p2 : PStep a1 a2 := PStep.of_caches ⟨by rw [h2st]; exact hC1.check.state.wf⟩
    (by rw [h2st]; exact ConRon.Arena.Ext.refl _) h2c h2p
  have hA2 : AbsOK m2 := absOK_apdF (apdF_of_callW hApd (callW_of_callE h2)) hA1 hT2
  have hC2 := hC1.of_pstep hT2.stage hA2 p2
  dsimp only [raE.k_all_level_params_defined]
  refine RefE.guardIf rfl (fun h => by rw [← hx2, h]; rfl)
    (fun h => by rw [← hx2] at h; simpa using h) fun _ _ => ?_
  -- the resolution
  have hsP2 := denote_ext hsP1 p2.ext
  refine RefE.bindCall (fun _ => rfl) (fun hG _ h9 => nvl hG.nv (by decide +kernel) h9)
    (fun b h9 => crfF_okT dn vis fe s hs m2 b.2 a2 b.1 (crfF_of_callW hCrf h9)
      ⟨hC2.stageT, hA2.crMemo⟩)
    fun r3 m3 x3 a3 h3 hrun3 ⟨⟨hT3, hg3, hx3, _⟩, hCr3⟩ => ?_
  obtain ⟨p3, -⟩ := constsResolveFFast_pstep hC2.check.toR hsP2 hrun3
  have hA3 : AbsOK m3 := absOK_crfF' (crfF_of_callW hCrf (callW_of_callE h3)) hA2 hCr3.crOK hT3
  have hC3 := hC2.of_pstep hT3.stage hA3 p3
  dsimp only [raE.k_consts_resolve_ffast]
  refine RefE.splitNot (fun h => by rw [← hx3, h]; decide)
    (fun h => by rw [← hx3] at h; simpa using h) (fun _ _ => ?_) fun _ _ => ?_
  · rcases h10 : callE p N "unresolved_consts_error" [vis, s, 6] m3 with e10 | ⟨r10, m10⟩ <;>
      dsimp only [raE.k_unresolved_consts_error]
    · obtain ⟨M3, hC3'⟩ := hC3.stageT.core
      exact fun hG => uce_errClaim_hi hG.uce hG.nv hC3'.arena.base hC3'.pins hs (by decide) h10 _
    · exact RefE.of_cls0 rfl
  -- the two inferences
  have c13 : ConRon.Bridge.CoreStep env fe a a3 := ((p1.trans p2).trans p3).toCore hC.check
  refine RefE.bindCall (fun _ => rfl)
    (fun hG _ h4 => hG.core.inferTypeCore N (by omega) hC3.stageT 0 s hs _ h4)
    (inferC_rsim hq henv N (by omega) hC3 hA3 0 s hs (denote_ext hsP c13.ext) hws)
    fun r4 m4 x4 a4 _ _ ⟨hC4, hg4, hd4, hA4, c4, w4, hw4, hsc4⟩ => ?_
  dsimp only [raE.k_infer_type_core] at hC4 hg4 hd4 hA4 ⊢
  obtain ⟨hH4, hx4⟩ := hd4
  subst hx4
  refine RefE.bindCall (fun _ => rfl)
    (fun hG _ h5 => hG.core.inferTypeCore N (by omega) hC4.stageT 0 g hg _ h5)
    (inferC_rsim hq henv N (by omega) hC4 hA4 0 g hg (denote_ext hgP (c13.ext.trans c4.ext)) hwg)
    fun r5 m5 x5 a5 _ _ ⟨hC5, hg5, hd5, hA5, c5, w5, hw5, hsc5⟩ => ?_
  dsimp only [raE.k_infer_type_core_2] at hC5 hg5 hd5 hA5 ⊢
  obtain ⟨hH5, hx5⟩ := hd5
  subst hx5
  -- the types, then the right-hand sides
  refine RefE.bindCall (fun _ => rfl)
    (fun hG _ h6 => hG.core.isDefEqCore N (by omega) hC5.stageT 0 _ _ hH4 hH5 _ h6)
    (isDefEqC_rsim hq henv N (by omega) hC5 hA5 0 _ _ hH4 hH5 (denote_ext hw4 c5.ext) hw5 hsc4 hsc5)
    fun r6 m6 b6 a6 _ _ ⟨hC6, hg6, hb6, hA6, c6⟩ => ?_
  dsimp only [raE.k_is_def_eq_core] at hC6 hg6 hb6 hA6 ⊢
  refine RefE.guardIf rfl (fun h => by rw [← hb6, decBool, h]; rfl)
    (fun h => by rw [← hb6] at h; simpa [decBool] using h) fun _ _ => ?_
  have c36 := (c4.trans c5).trans c6
  refine RefE.bindCall (fun _ => rfl)
    (fun hG _ h7 => hG.core.isDefEqCore N (by omega) hC6.stageT 0 s g hs hg _ h7)
    (isDefEqC_rsim hq henv N (by omega) hC6 hA6 0 s g hs hg (denote_ext hsP (c13.ext.trans c36.ext))
      (denote_ext hgP (c13.ext.trans c36.ext)) hws hwg)
    fun r7 m7 b7 a7 _ _ ⟨hC7, hg7, hb7, hA7, c7⟩ => ?_
  dsimp only [raE.k_is_def_eq_core_2] at hC7 hg7 hb7 hA7 ⊢
  refine RefE.guardIf rfl (fun h => by rw [← hb7, decBool, h]; rfl)
    (fun h => by rw [← hb7] at h; simpa [decBool] using h) fun _ _ => ?_
  exact RefE.ret rfl ⟨hC7, ((((((hg1.trans hg2).trans hg3).trans hg4).trans hg5).trans hg6).trans hg7),
    hA7, (c13.trans c36).trans c7⟩

end sims4

end L.Ind

end
