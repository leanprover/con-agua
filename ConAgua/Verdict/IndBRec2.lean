module

public import ConAgua.Arena.RecClassSpec.ClassGenRecTy
public import ConAgua.Verdict.IndBHdr
public import ConAgua.Verdict.IndBRec1
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.RecGenSpec.ClassFeR
public import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen
public import ConRon.Bridge.Inductives.GenRec
import ConAgua.Arena.RefWalk
import ConAgua.Arena.StageC
import ConAgua.Checker.NoVerdictTree
import ConRon.Bridge.Core.Walks.Cached
public import ConAgua.Arena.TwinStep
import all ConAgua.Arena.RecGen

@[expose] public section

/-!
# `class_rec_ty_ok`: one model and one refinement for both outcomes

`classRecTyOkE` (`l_model … unified`: the guards and `class_rec_ty_check` through their unified
models, `class_gen_rec_ty` and `cv_new` lifted) and `rto_ref` under `StageC`; `class_rec_ty_check`
(`classRecTyCheckE`, `rtc_ref`: `class_const_ok` through `cco_ref`, then `is_def_eq_core`), from the inputs' denotations
con-ron's `classRecTyOk_spec` asks. Its ok half is `classRecTyOk_refinesC` and
`class_rec_tys_ok`'s ok refinement (`RefE.run_okW`), its error half `class_rec_tys_ok`'s error
claim (`RefE.run_err`); an error of class `1`/`2` claims the twin's failure.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dClassGen dRec dMajor dExt_denoteCV dClassGen_ext
  dClassGen_inv dRec_inv ROp RE mapM_option_cons_inv dRec_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- The lookups of `class_rec_ty_ok` with its callee `class_rec_ty_check` and `class_const_ok`'s. -/
structure RtoProgE (p : Prog) : Prop extends RtoProg p where
  cch : CchProg p
  crc : p.lookup "class_rec_ty_check" = some classRecTyCheckL

/-- **The model of `class_rec_ty_check`, both outcomes**: `class_const_ok` through its unified
model, `is_def_eq_core` through `callE`. -/
l_model classRecTyCheckE_spec (p : Prog) (hp : RtoProgE p)
  fns [hp.crc ↦ classRecTyCheckE] specs [classConstOkE_spec p hp.cch n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model classRecTyOkE_spec (p : Prog) (hp : RtoProgE p)
  fns [hp.rto ↦ classRecTyOkE]
  specs [classRecTyOkGuardsE_spec p hp.toRtoProg n, classGenRecTy_spec p hp.toGtProg n,
    cvNew_specW p hp.era hp.cch.rcp.put hp.cvn n, classRecTyCheckE_spec p hp n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 400000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]


/-- The usual `RSim` post under `StageC`. -/
def KPC {α : Type} (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (env : ConLeche.Env) (m : Mem) (dec : Mem → List Word → α → Prop) (b : List Word × Mem)
    (a' : AState) (x : α) : Prop :=
  StageC dn vis fe env b.2 a' ∧ IWGrow m b.2 ∧ dec b.2 b.1 x

/-- What `class_rec_ty_ok` gives besides the twin's checked constant `x` (from `m`): the stage
invariant under `StageC`, the growth, the new record `q` decoding to `x` below the top, the
abstraction memo. -/
structure RtoPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (q : Word) (m' : Mem) (x : IConstantVal) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  dec : decCVR m' [q] x
  abs : AbsOK m'

section sims
variable {p : Prog} (hP : CchProg p) (hq : KnotStageProg p) (hApd : ApdF p) (hCrf : CrfF p)
  {dn : NIdx → Option ConLeche.Name} (hCs : CcvSims p dn) {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

/-- What `class_rec_ty_check` gives besides the twin's run (from `m`): the stage invariant under
`StageC`, the growth, the abstraction memo. -/
structure RtcPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m m' : Mem) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  abs : AbsOK m'

include hP hq hApd hCrf hCs henv in
/-- **`class_rec_ty_check` refines `classRecTyCheck`, both outcomes** under `StageC` (the twin side
transcribed from con-ron's `classRecTyCheck_spec`'s proof): `classConstOk` (`cco_ref`, lifted to
`StageC` by con-ron's `classConstOk_spec`), then `isDefEqCore` (`isDefEqC_rsim`; its error the core
stub's claim). -/
theorem rtc_ref (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState} {cvRi q : Word}
    {CVRi CVG : IConstantVal} {cvRiP cvGP : ConLeche.ConstantVal} (hC : StageC dn vis fe env m a)
    (hdRi : decCV (erecP m) cvRi.toNat = some CVRi) (hdG : decCV (erecP m) q.toNat = some CVG)
    (hqb : q.toNat + 3 < 2 ^ 64) (hA : AbsOK m)
    (hRiP : Frontend.denoteCV a.store CVRi = some cvRiP) (hGP : Frontend.denoteCV a.store CVG = some cvGP)
    (hRi : ConLeche.Expr.WScoped 0 cvRiP.type) :
    RefE (VerdictCtxU p) (classRecTyCheckE p n m vis cvRi q)
      (ConRon.Arena.classRecTyCheck V fe CVRi CVG) a
      (fun v _ a' => RtcPost dn vis fe env m v.2 a') := by
  cases n with
  | zero => rw [classRecTyCheckE.eq_1]; exact RefE.of_cls0 rfl
  | succ n =>
  rw [classRecTyCheckE.arm1]
  unfold ConRon.Arena.classRecTyCheck
  -- `class_const_ok(vis, q)`
  refine RefE.bindE (fun _ => rfl) id
    (cco_ref hP hq hApd hCrf hCs n (by omega) hC.stageT hdG hqb hA hGP)
    fun ⟨r4, m4⟩ u a4 hrun4 ⟨hS4, hg4, hA4⟩ => ?_
  dsimp only at hS4 hg4 hA4
  obtain ⟨c4, -, ⟨hwG, -⟩, -⟩ := ConRon.Bridge.Inductives.classConstOk_spec fe
    ConRon.Bridge.CoreSpec.of_core henv _ _ a a4 u hC.check hGP hrun4
  have hC4 : StageC dn vis fe env m4 a4 := hC.of_check hS4.stage hA4 c4.ok c4.ext
  dsimp only [classRecTyCheckE.k_class_const_ok]
  -- the two types, read below the top
  obtain ⟨wt, hwt, hwtH, hwtE⟩ := (decCV_words hdRi).2.2
  obtain ⟨wg, hwg, hwgH, hwgE⟩ := (decCV_words hdG).2.2
  have et : rdW (m4.arr64 (L.tierA EREC ((cvRi + 3) >>> 40))) (cvRi + 3 &&& 1099511627775) = wt :=
    (erRdOK m4).off (hg4.ext _ _ hwt) (by simp)
  have eg : rdW (m4.arr64 (L.tierA EREC ((q + 3) >>> 40))) (q + 3 &&& 1099511627775) = wg :=
    (erRdOK m4).off (hg4.ext _ _ hwg) (by simp)
  rw [et, eg]
  -- `is_def_eq_core(vis, 0, cvRi.type, cvG.type)`
  have hdx : denoteE a4.store (decI wt) = some cvRiP.type := by
    rw [← hwtE]; exact (ConRon.Bridge.Core.denoteCV_inv (dExt_denoteCV c4.ext _ _ hRiP)).2.2
  have hdy : denoteE a4.store (decI wg) = some cvGP.type := by
    rw [← hwgE]; exact (ConRon.Bridge.Core.denoteCV_inv (dExt_denoteCV c4.ext _ _ hGP)).2.2
  rw [hwtE, hwgE]
  refine RefE.bindCall (fun _ => rfl)
    (fun hG' _ h5 => hG'.core.isDefEqCore n (by omega) hC4.stageT 0 wt wg hwtH hwgH _ h5)
    (isDefEqC_rsim hq henv n (by omega) hC4 hA4 0 wt wg hwtH hwgH hdx hdy hRi hwG)
    fun r5 m5 bb a5 _ _ ⟨hC5, hg5, hbb, hA5, _⟩ => ?_
  dsimp only [classRecTyCheckE.k_is_def_eq_core]
  refine RefE.guardIf (by decide) (fun h50 => by rw [← hbb]; simpa [decBool] using h50)
    (fun h50 => by rw [← hbb] at h50; simpa [decBool] using h50) fun _ _ => ?_
  exact RefE.ret rfl ⟨hC5, hg4.trans hg5, hA5⟩

include hP hq hApd hCrf hCs henv in
/-- **`class_rec_ty_ok` refines `classRecTyOk`, both outcomes** under `StageC` (the twin side
transcribed from con-ron's `classRecTyOk_spec`'s proof): the guards (`rg_ref`, against `rgT`:
`rgT_bind`), `classGenRecTy` (`gtW_sim`, outside the verdict closure), the record write (`cv_new`,
twin side none), then `classRecTyCheck` (`rtc_ref`). -/
theorem rto_ref (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState} {g k rc cvRi c : Word}
    {G : ClassGen} {RS : RecShape} {CVRi : IConstantVal} (hC : StageC dn vis fe env m a)
    (hG : DecB (fun m => decCG m g.toNat) m G) (hns : G.nP + G.slots.length < 2 ^ 64)
    (hrc : DecB (fun m => decRS m rc.toNat) m RS) (hcvR : ∀ q, iwN m rc.toNat = some q → CVExt m q)
    (hcvRi : DecB (fun m => decCVp m cvRi.toNat) m CVRi) (hA : AbsOK m)
    {gP : ConLeche.ClassGen} {rcP : ConLeche.RecShape} {cvRiP : ConLeche.ConstantVal}
    (hgP : dClassGen a.store G = some gP) (hrcP : dRec a.store RS = some rcP)
    (hRiP : Frontend.denoteCV a.store CVRi = some cvRiP) (hRi : ConLeche.Expr.WScoped 0 cvRiP.type) :
    RefE (VerdictCtxU p) (classRecTyOkE p n m vis g k rc cvRi c)
      (ConRon.Arena.classRecTyOk V fe G k.toNat RS CVRi c.toNat) a
      (fun v x a' => RtoPost dn vis fe env m v.1 v.2 x a') := by
  cases n with
  | zero => rw [classRecTyOkE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  rw [classRecTyOkE.arm1]
  unfold ConRon.Arena.classRecTyOk
  rw [rgT_bind]
  refine RefE.bindE (fun _ => rfl) (fun hV => hV.nv)
    (rg_ref (p := p) (k := k) (c := c) dn fe vis n hC.stage hG hns hrc hA)
    fun ⟨r1, m1⟩ tm a1 _ ⟨hrun1, hS1, hg1, hA1⟩ => ?_
  dsimp only at hrun1 hS1 hg1 hA1
  obtain ⟨-, -, hcls, -, -, -, -, -⟩ := dClassGen_inv hgP
  obtain ⟨p1, -⟩ := ConRon.Bridge.Inductives.targetMajorAt_spec G.cls gP.cls c.toNat a a1 tm
    hC.check.state hC.check.pins hcls hrun1
  have hC1 : StageC dn vis fe env m1 a1 := hC.of_pstep hS1 hA1 p1
  dsimp only [classRecTyOkE.k_class_rec_ty_ok_guards]
  -- `class_gen_rec_ty(g, c)`
  refine RefE.bindLift (fun _ => rfl) fun r2 m2 h2 => ?_
  obtain ⟨o, a2, hrun2, hC2, ⟨⟨hS2, hg2, ho⟩, hA2⟩, hR2, p2⟩ :=
    (RSim.liftPP hC1 (gtW_sim dn vis fe n m1 a1 g c G hS1 (hG.grow (decCG_mono _) hg1) hns hA1)
      (fun _ _ _ h => ⟨h.1.1, h.2⟩) (ConRon.Bridge.Inductives.classGenRecTy_spec G gP c.toNat)
      (dClassGen_ext p1.ext _ _ hgP)) (r2, m2) h2
  dsimp only at hS2 hg2 ho hA2 hC2
  refine ⟨_, _, hrun2, ?_⟩
  rcases o with _ | gty
  · rw [classRecTyOkE.k_class_gen_rec_ty.abort1 _ _ _ _ _ _ _ ho]; exact RefE.of_cls0 rfl
  obtain ⟨gtyP, -, hgtyd⟩ := hR2
  obtain ⟨h21, hgH, hgd⟩ := ho
  rw [classRecTyOkE.k_class_gen_rec_ty.arm1 _ _ _ _ _ _ _ (by rw [h21]; decide)]
  subst hgd
  have hg12 := hg1.trans hg2
  obtain ⟨q0, hq0, -⟩ := rec2DecRS_parts (show decRS (truncM m) rc.toNat = some RS from hrc)
  obtain ⟨hrct, hq0m⟩ := rec2IwN_trunc hq0
  have hq2 : iwN m2 rc.toNat = some q0 := by rw [iwN_grow hg12 hrct]; exact hq0m
  obtain ⟨q0', hq0', hcv2, -⟩ := rec2DecRS_parts (hrc.stab (decRS_mono _) m2 hg12)
  rw [hq2] at hq0'; cases hq0'
  have hext2 := CVExt_grow hg12 (hcvR q0 hq0m)
  obtain ⟨erc, trc⟩ := rec2RdN (w := rc) (k := 0) (by simpa using hq2) hS2.iw.iwSize
  simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero] at erc
  rw [erc]
  -- `cv_new(…)` (twin side none)
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun q m3 h3 => ?_
  dsimp only [classRecTyOkE.k_cv_new]
  obtain ⟨hS3, hg3, -, -, hq41, -, hdec3⟩ := cvNew_stage (cq := UInt64.ofNat q0) h3 hS2
    (by rw [trc]; exact hcv2) hgH
  have hext3 : CVExt m3 q.toNat := CVExt.of_dec hdec3
  have hqb : q.toNat + 3 < 2 ^ 64 := by omega
  have hA3 := cvNewW_afr h3 hA2
  have hC3 : StageC dn vis fe env m3 a2 := hC2.of_pstep hS3 hA3 (PStep.refl hC2.check.state)
  have p12 := p1.trans p2
  obtain ⟨hnm, hlps, -⟩ :=
    ConRon.Bridge.Core.denoteCV_inv (dExt_denoteCV p12.ext _ _ (dRec_inv hrcP).1)
  have hcvG : Frontend.denoteCV a2.store { RS.cvR with type := decI (r2.tail.headD 0) } =
      some { rcP.cvR with type := gtyP } := by
    simp only [Frontend.denoteCV, hnm, hlps, hgtyd]
  -- `class_rec_ty_check(vis, cvRi, q)`
  have hri := hcvRi.stab (OMono.decCVp _) m3 (hg12.trans hg3)
  refine RefE.bindE (fun _ => rfl) id
    (rtc_ref hP hq hApd hCrf hCs henv n (by omega) hC3 hri (rec2DecCV_erecP hdec3 hext3) hqb hA3
      (dExt_denoteCV p12.ext _ _ hRiP) hcvG hRi) fun ⟨r4, m4⟩ u a4 hrun4 ⟨hC4, hg4, hA4⟩ => ?_
  dsimp only at hC4 hg4 hA4
  dsimp only [classRecTyOkE.k_class_rec_ty_check]
  refine RefE.ret rfl ⟨hC4, (hg12.trans hg3).trans hg4, ⟨?_, CVExt_grow hg4 hext3⟩, hA4⟩
  show decCVp m4 q.toNat = _
  rw [decCVp_grow_r hg4 hext3, hdec3]

include hP hq hApd hCrf hCs henv in
/-- **`class_rec_ty_ok` refines `classRecTyOk`** under `StageC` (`rto_ref`'s ok half). -/
@[refines ConRon.Arena.classRecTyOk]
theorem classRecTyOk_refinesC (hp : RtoProgE p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (g k rc cvRi c : Word) (G : ClassGen) (RS : RecShape) (CVRi : IConstantVal)
    (hC : StageC dn vis fe env s₀.mem a₀) (hG : DecB (fun m => decCG m g.toNat) s₀.mem G)
    (hns : G.nP + G.slots.length < 2 ^ 64) (hrc : DecB (fun m => decRS m rc.toNat) s₀.mem RS)
    (hcvR : ∀ q, iwN s₀.mem rc.toNat = some q → CVExt s₀.mem q)
    (hcvRi : DecB (fun m => decCVp m cvRi.toNat) s₀.mem CVRi) (hA : AbsOK s₀.mem)
    {gP : ConLeche.ClassGen} {rcP : ConLeche.RecShape} {cvRiP : ConLeche.ConstantVal}
    (hgP : dClassGen a₀.store G = some gP) (hrcP : dRec a₀.store RS = some rcP)
    (hRiP : Frontend.denoteCV a₀.store CVRi = some cvRiP)
    (hRi : ConLeche.Expr.WScoped 0 cvRiP.type) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_rec_ty_ok" [vis, g, k, rc, cvRi, c]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classRecTyOk V fe G k.toNat RS CVRi c.toNat) a₀ ∧
      KPC dn vis fe env s₀.mem decCVR (r, s'.mem)
        (AM.st (ConRon.Arena.classRecTyOk V fe G k.toNat RS CVRi c.toNat) a₀)
        (AM.res (ConRon.Arena.classRecTyOk V fe G k.toNat RS CVRi c.toNat) a₀) ∧
      AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (classRecTyOkE_spec p hp n s₀ vis g k rc cvRi c)
    (rto_ref hP hq hApd hCrf hCs henv n hn hC hG hns hrc hcvR hcvRi hA hgP hrcP hRiP hRi)) ?_
  rintro r s' ⟨hl, x, a', run, hR⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, ⟨by rw [hst]; exact hR.stage, hR.grow, by rw [hres]; exact hR.dec⟩, hR.abs⟩

end sims

end L.Ind

end
