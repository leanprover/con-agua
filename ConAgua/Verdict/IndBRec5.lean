import ConAgua.Verdict.IndBRec4
import ConAgua.Arena.DeclCvg
import ConAgua.Arena.IndSumSpec.StructCtorResidOk
import ConAgua.Arena.RecClassSpec.RuW
import ConAgua.Arena.IndPartsSpec.PlW
import ConAgua.Arena.IndRealAbsPos
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
/-!
# `class_rules_ok`: one model and one refinement for both outcomes

`crsE` (`l_model … unified`: `class_rules_ok_one` through its unified model, `cv_lps`,
`param_levels`, `class_gen_rule` and `sl_cons` lifted) and `crs_ref` under `StageC`; twin side
con-ron's `classRulesOk_spec`'s proof: `paramLevels` (`paramLevels_spec`, a core-free grower:
`RSim.liftP` of `plW_sim`), `classGenRule` (`classGenRule_spec`: `RSim.liftPP` of `ruW_sim`; the
rule `class_gen_rule` omits is the twin's `classGenRule = none` reject), `classRuleOk` (`cr1_ref`),
the rest by induction. Its ok half is `classRulesOk_refinesC` and `class_recs_rules_ok_go`'s
refinement.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dClassGen dClassCtor dExt_denoteCV dClassGen_ext
  dClassCtor_ext mapM_option_cons_inv)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model crsE_spec (p : Prog) (hP : CrsProg p)
  fns [hP.crs ↦ crsE]
  specs [cvLps_specW p hP.cr.alloc hP.cr.copy hP.cr.eti hP.cr.lps n,
    plW_spec p hP.alloc hP.copy hP.cons hP.slGet hP.paramFind hP.paramPush hP.internParam hP.plGo hP.pl
      hP.il n,
    classGenRule_spec p hP.ru n, cr1E_spec p hP n, slCons_specW p hP.alloc hP.copy hP.cons n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `class_rules_ok` gives besides the twin's rules `xs` (from `m`, `a`): the stage invariant
under `StageC`, the growth, the rules a handle slice below the top, the abstraction memo, the core
step. -/
structure CrsPost (dn : NIdx → Option ConLeche.Name) (visR : Word) (feR : IFEnv) (env : ConLeche.Env)
    (m : Mem) (a : AState) (r : List Word) (m' : Mem) (xs : List EIdx) (a' : AState) : Prop where
  stage : StageC dn visR feR env m' a'
  grow : IWGrow m m'
  dec : decEL m' r xs
  abs : AbsOK m'
  core : ConRon.Bridge.CoreStep V env feR a a'

section sims
variable {p : Prog} (hq : KnotStageProg p) (hApd : ApdF p) {dn : NIdx → Option ConLeche.Name}
  {env : ConLeche.Env}

include hq hApd in
/-- **`class_rules_ok` refines `classRulesOk`, both outcomes** under `StageC` (the inputs'
denotations as con-ron's `classRulesOk_spec` asks). -/
theorem crs_ref (hP : CrsProg p) (henv : ConLeche.EnvWF env) (visT visR : Word) (feR : IFEnv)
    {env₂ : ConLeche.Env}
    (g rco rcl cgo cgl cvR c : Word) (G : ClassGen) (recCls : List Nat) (cvGs : List IConstantVal)
    (cv : IConstantVal) (hns : G.nP + G.slots.length < 2 ^ 64) (hrcb : rco.toNat + rcl.toNat < 2 ^ 64)
    (hcgb : cgo.toNat + cgl.toNat < 2 ^ 64) (gP : ConLeche.ClassGen)
    (cvGsP : List ConLeche.ConstantVal) (cvRP : ConLeche.ConstantVal) (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (xo xl : Word) (Xs : List ClassCtor) (XsP : List ConLeche.ClassCtor),
    StageC dn visR feR env m a →
    DecB (fun m => decCG m g.toNat) m G → DecB (fun m => decNL m rco.toNat rcl.toNat) m recCls →
    DecB (fun m => decPL m (decCVp m) cgo.toNat cgl.toNat) m cvGs →
    decCVp m cvR.toNat = some cv → CVExt m cvR.toNat →
    DecB (fun m => decPL m (decCC m) xo.toNat xl.toNat) m Xs → AbsOK m →
    dClassGen a.store G = some gP → cvGs.mapM (Frontend.denoteCV a.store) = some cvGsP →
    Frontend.denoteCV a.store cv = some cvRP → Xs.mapM (dClassCtor a.store) = some XsP →
    ConRon.Bridge.Inductives.IFEnvOKS env₂ (feR.restrictTo visT.toNat) a.store →
    RefE (VerdictCtxU p) (crsE p n m visT visR g rco rcl cgo cgl cvR c xo xl)
      (ConRon.Arena.classRulesOk V visT.toNat feR G recCls cvGs cv c.toNat Xs) a
      (fun v xs a' => CrsPost dn visR feR env m a v.1 v.2 xs a') := by
  induction n with
  | zero => intros; rw [crsE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a xo xl Xs XsP hC hG hrc hcg hcv hext hXs hA hgP hcvsP hcvP hXsP hie
  have hS := hC.stage
  have hsz := hS.2.2.2.1
  by_cases hxl : xl = 0
  · rw [crsE.arm1 p n m visT visR g rco rcl cgo cgl cvR c xo xl hxl]
    have : Xs = [] := by
      have := decPL_length _ (hXs.get (OMono.decPL (fun q => decCC_mono q) _ _))
      rw [hxl] at this; exact List.eq_nil_of_length_eq_zero (by simpa using this)
    subst this
    unfold ConRon.Arena.classRulesOk
    exact RefE.ret rfl ⟨hC, IWGrow.refl m, ⟨by simp [decHL, hslice?], by simp⟩, hA,
      ConRon.Bridge.CoreStep.refl hC.check⟩
  rw [crsE.arm2 p n m visT visR g rco rcl cgo cgl cvR c xo xl hxl]
  obtain ⟨jx, hjx⟩ : ∃ j, xl.toNat = j + 1 :=
    ⟨xl.toNat - 1, by
      have : xl.toNat ≠ 0 := fun e => hxl (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  have hXs' : decPL (truncM m) (decCC (truncM m)) xo.toNat (jx + 1) = some Xs := by
    rw [← hjx]; exact hXs
  obtain ⟨px, X, Xs', rfl, hpx, hX, hXsT⟩ := decPL_cons hXs'
  obtain ⟨XP, XsP', rfl, hXP, hXsP'⟩ := mapM_option_cons_inv hXsP
  obtain ⟨hxot, hpxm⟩ := rec2IwN_trunc hpx
  have hxot' : iwTop m ≤ (m.arr64 IW).size := hS.2.1
  obtain ⟨ex, tx⟩ := rec2RdN (w := xo) (k := 0) (by simpa using hpxm) hsz
  simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero] at ex
  rw [ex]
  have hX' : DecB (fun m => decCC m (UInt64.ofNat px : Word).toNat) m X := by rw [tx]; exact hX
  unfold ConRon.Arena.classRulesOk
  obtain ⟨-, hlps, -⟩ := ConRon.Bridge.Core.denoteCV_inv hcvP
  -- `cv_lps`: L only
  rcases h1 : L.Arena.cvLpsW n m cvR with _ | ⟨r1, m1⟩
  · rw [liftE_none, crsE.k_cv_lps.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, crsE.k_cv_lps.arm1]
  obtain ⟨hS1, hg1, hd1, ht1⟩ := cvLpsA_stage h1 hS hcv (rec3CVExt_lt hS hext)
  have hA1 := cvLpsA_afr h1 hA
  have hC1 : StageC dn visR feR env m1 a := hC.of_check hS1 hA1 hC.check (Ext.refl _)
  -- `param_levels`
  rcases h2 : plW n m1 (r1.headD 0) (r1.tail.headD 0) with _ | ⟨r2, m2⟩
  · rw [liftE_none, crsE.k_param_levels.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, crsE.k_param_levels.arm1]
  obtain ⟨rl, a2, hrl2, hC2, ⟨⟨hrlH, hrl, hS2, hg2⟩, hf2⟩, hRl, p1⟩ :=
    (RSim.liftP hC1 (RSim.withF (rec3Sim_rsim (plW_sim (k := n) hS1 hd1 ht1)) (fun _ hb => plW_afr hb))
      (fun _ _ _ h => ⟨h.1.2.2.1, h.2 hA1⟩)
      (ConRon.Bridge.Inductives.paramLevels_spec cv.levelParams _) hlps) (r2, m2) h2
  dsimp only at hrlH hrl hS2 hg2 hC2
  subst hrl
  refine RefE.bind_right hrl2 ?_
  have hg02 := hg1.trans hg2
  have hA2 := hf2 hA1
  -- `class_gen_rule`
  rcases h3 : ruW n m2 g rco rcl cgo cgl (r2.headD 0) c (UInt64.ofNat px) with _ | ⟨r3, m3⟩
  · rw [liftE_none, crsE.k_class_gen_rule.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨o3, a3, hr3, hC3, ⟨⟨hS3, hg3, ho3⟩, hA3⟩, hR3, p2⟩ :=
    (RSim.liftPP hC2 (ruW_sim dn visR feR n m2 a2 g rco rcl cgo cgl (r2.headD 0) c (UInt64.ofNat px)
      G X recCls cvGs hS2 (hG.grow (decCG_mono _) hg02) hns (hX'.grow (decCC_mono _) hg02) hrlH
      (hrc.grow (OMono.decNL _ _) hg02) hrcb
      (hcg.grow (OMono.decPL (fun q => OMono.decCVp q) _ _) hg02) hcgb hA2)
      (fun _ _ _ h => ⟨h.1.1, h.2⟩)
      (ConRon.Bridge.Inductives.classGenRule_spec G gP recCls cvGs cvGsP (decI (r2.headD 0)) _
        c.toNat X XP)
      ⟨dClassGen_ext p1.ext _ _ hgP, dClassCtor_ext p1.ext _ _ hXP,
        dExt_denoteCV.list p1.ext _ _ hcvsP, hRl⟩) (r3, m3) h3
  dsimp only at hS3 hg3 ho3 hC3
  refine RefE.bind_right hr3 ?_
  by_cases h30 : r3.headD 0 = 0
  · rw [crsE.k_class_gen_rule.abort1 p n visT visR g rco rcl cgo cgl cvR c xo xl _ r3 m3 h30]
    cases o3 with
    | none => exact fun _ => ErrClaim.fail _ _ (by decide)
    | some gen => exact absurd (by simpa using ho3.1 : r3.headD 0 = 1) (by rw [h30]; decide)
  rw [crsE.k_class_gen_rule.arm1 p n visT visR g rco rcl cgo cgl cvR c xo xl _ r3 m3 h30]
  rcases o3 with _ | gen
  · exact absurd ho3 h30
  obtain ⟨genP, -, hgenP⟩ := hR3
  obtain ⟨h31, hgH, hgd⟩ := ho3
  subst hgd
  have hg03 := hg02.trans hg3
  have p12 := p1.trans p2
  -- `class_rules_ok_one`
  have hr := cr1_ref hq hP.cr hApd henv n (by omega) hC3 hgH
    (by rw [decCVp_grow_r hg03 hext]; exact hcv) (CVExt_grow hg03 hext)
    (hG.grow (decCG_mono _) hg03) hns (hX'.grow (decCC_mono _) hg03) hA3
    (dExt_denoteCV p12.ext _ _ hcvP) hgenP (hie.mono p12.ext) (visT := visT)
  rcases h4 : cr1E p n m3 visT visR g cvR (UInt64.ofNat px) (r3.tail.headD 0) with e4 | ⟨r4, m4⟩ <;>
    rw [h4] at hr
  · rw [crsE.k_class_rules_ok_one.none]; exact RefE.bind_left hr
  rw [crsE.k_class_rules_ok_one.arm1]
  obtain ⟨y, a4, hrun4, hR4⟩ := hr
  have hv : r4 = r3.tail.headD 0 := hR4.val
  subst hv
  refine RefE.bind_right hrun4 ?_
  have hg04 := hg03.trans hR4.grow
  have c14 := (p12.toCore hC.check).trans hR4.core
  -- the rest
  have hxo1 := rec2ToNat_succ (o := xo) (i := xo.toNat) (Nat.le_refl _) (by omega)
  have hxl1 := rec2ToNat_pred hxl
  have ih' := ih (by omega) m4 a4 (xo + 1) (xl - 1) Xs' XsP' hR4.stage (hG.grow (decCG_mono _) hg04)
    (hrc.grow (OMono.decNL _ _) hg04)
    (hcg.grow (OMono.decPL (fun q => OMono.decCVp q) _ _) hg04)
    (by rw [decCVp_grow_r hg04 hext]; exact hcv) (CVExt_grow hg04 hext)
    (by rw [hxo1, hxl1, hjx]; exact (show DecB (fun m => decPL m (decCC m) (xo.toNat + 1) jx) m Xs' from
      hXsT).grow (OMono.decPL (fun q => decCC_mono q) _ _) hg04) hR4.abs
    (dClassGen_ext c14.ext _ _ hgP) (dExt_denoteCV.list c14.ext _ _ hcvsP)
    (dExt_denoteCV c14.ext _ _ hcvP) (dClassCtor_ext.list c14.ext _ _ hXsP') (hie.mono c14.ext)
  rcases h5 : crsE p n m4 visT visR g rco rcl cgo cgl cvR c (xo + 1) (xl - 1) with e5 | ⟨r5, m5⟩ <;>
    rw [h5] at ih'
  · rw [crsE.k_class_rules_ok.none]; exact RefE.bind_left ih'
  rw [crsE.k_class_rules_ok.arm1]
  obtain ⟨rs, a5, hrun5, hR5⟩ := ih'
  refine RefE.bind_right hrun5 ?_
  -- `sl_cons`
  rcases h6 : consW n m5 (r3.tail.headD 0) (r5.headD 0) (r5.tail.headD 0) with _ | ⟨r6, m6⟩
  · rw [liftE_none, crsE.k_sl_cons.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, crsE.k_sl_cons.arm1]
  obtain ⟨hrs, hrsb⟩ := hR5.dec
  rw [getD_zero, getD_one] at hrs hrsb
  obtain ⟨hS6, hg6, hd6, ht6⟩ := consW_stage h6 hR5.stage.stage hrsb hgH hrs
  have hA6 := consW_afr h6 hR5.abs
  refine RefE.ret rfl ⟨hR5.stage.of_check hS6 hA6 hR5.stage.check (Ext.refl _),
    hg04.trans (hR5.grow.trans hg6), ⟨?_, ?_⟩, hA6, c14.trans hR5.core⟩ <;>
    simp only [getD_zero, List.headD_cons, hR4.res]
  · exact hd6
  · exact Nat.le_of_eq ht6

include hq hApd in
/-- **`class_rules_ok` refines `classRulesOk`** under `StageC` (`crs_ref`'s ok half): the rules,
a handle slice below the top. -/
@[refines ConRon.Arena.classRulesOk]
theorem classRulesOk_refinesC (hp : CrsProg p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (henv : ConLeche.EnvWF env) (visT visR : Word) (feR : IFEnv) {env₂ : ConLeche.Env}
    (g rco rcl cgo cgl cvR c xo xl : Word) (G : ClassGen) (recCls : List Nat)
    (cvGs : List IConstantVal) (cv : IConstantVal) (Xs : List ClassCtor)
    (hC : StageC dn visR feR env s₀.mem a₀) (hG : DecB (fun m => decCG m g.toNat) s₀.mem G)
    (hns : G.nP + G.slots.length < 2 ^ 64)
    (hrc : DecB (fun m => decNL m rco.toNat rcl.toNat) s₀.mem recCls)
    (hrcb : rco.toNat + rcl.toNat < 2 ^ 64)
    (hcg : DecB (fun m => decPL m (decCVp m) cgo.toNat cgl.toNat) s₀.mem cvGs)
    (hcgb : cgo.toNat + cgl.toNat < 2 ^ 64)
    (hcv : decCVp s₀.mem cvR.toNat = some cv) (hext : CVExt s₀.mem cvR.toNat)
    (hXs : DecB (fun m => decPL m (decCC m) xo.toNat xl.toNat) s₀.mem Xs) (hA : AbsOK s₀.mem)
    {gP : ConLeche.ClassGen} {cvGsP : List ConLeche.ConstantVal} {cvRP : ConLeche.ConstantVal}
    {XsP : List ConLeche.ClassCtor} (hgP : dClassGen a₀.store G = some gP)
    (hcvsP : cvGs.mapM (Frontend.denoteCV a₀.store) = some cvGsP)
    (hcvP : Frontend.denoteCV a₀.store cv = some cvRP) (hXsP : Xs.mapM (dClassCtor a₀.store) = some XsP)
    (hie : ConRon.Bridge.Inductives.IFEnvOKS env₂ (feR.restrictTo visT.toNat) a₀.store) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_rules_ok"
      [visT, visR, g, rco, rcl, cgo, cgl, cvR, c, xo, xl]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.classRulesOk V visT.toNat feR G recCls cvGs cv c.toNat Xs) a₀ ∧
      (StageC dn visR feR env s'.mem
          (AM.st (ConRon.Arena.classRulesOk V visT.toNat feR G recCls cvGs cv c.toNat Xs) a₀) ∧
        IWGrow s₀.mem s'.mem ∧ decEL s'.mem r
          (AM.res (ConRon.Arena.classRulesOk V visT.toNat feR G recCls cvGs cv c.toNat Xs) a₀)) ∧
      AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (crsE_spec p hp n s₀ visT visR g rco rcl cgo cgl cvR c xo xl)
    (crs_ref hq hApd hp henv visT visR feR (env₂ := env₂) g rco rcl cgo cgl cvR c G recCls cvGs cv hns hrcb
      hcgb gP cvGsP cvRP n hn _ a₀ xo xl Xs XsP hC hG hrc hcg hcv hext hXs hA hgP hcvsP hcvP hXsP hie)) ?_
  rintro r s' ⟨hl, x, a', run, hR⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, ⟨by rw [hst]; exact hR.stage, hR.grow, by rw [hres]; exact hR.dec⟩, hR.abs⟩

end sims

end L.Ind

end
