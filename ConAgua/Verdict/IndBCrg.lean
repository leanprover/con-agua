import ConAgua.Arena.RecGenSpec.CruleProg
import ConAgua.Verdict.VCtx
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.IndT.WalkC
import ConAgua.Arena.IndRealMemoCrT
import ConAgua.Arena.RecGenSpec.FlushStage
import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen
import ConRon.Bridge.Inductives.GenRec

/-!
# `class_rule_ok_guards`: one model and one refinement for both outcomes

`class_rule_ok_guards` stands for the guards of the twin's `classRuleOk` (`crgT`: the closedness
guards, the level parameters, the resolution). Its unified model `crgE` lifts the walks outside the
verdict closure; `crg_ref` refines it against `crgT` under `VerdictCtxU p` (the consts-resolve
site's `uce_errClaim_hi`). Both halves are read by `class_rule_ok`'s refinement (`crule_ref`), which calls its
unified model directly.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

noncomputable section

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model crgE_spec (p : Prog) (hp : CruleProg p)
  fns [hp.guards ↦ crgE]
  specs [lbbF_spec p hp.bvb n, hffF_spec p hp.hf n, crfF_spec p hp.hcr n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **The twin's guards of `classRuleOk`** (the prefix `class_rule_ok_guards` stands for): the
closedness guards, the level parameters, the resolution. -/
def crgT (feR : IFEnv) (cv : IConstantVal) (gen : EIdx) : AM Unit := do
  unless ← looseBVarsBoundedFast coreWalkFuel 0 gen do
    fail (.internal "generated recursor: a rule of  is not closed")
  if ← hasFvarFast coreWalkFuel gen then
    fail (.internal "generated recursor: a rule of  is not closed")
  unless ← allLevelParamsDefined cv.levelParams gen do
    fail (.internal "generated recursor: a rule of  names an undeclared universe parameter")
  unless ← constsResolveFFast feR gen do
    fail (← unresolvedConstsError "generated rule of" gen)

/-- `classRuleOk` is its guards, then the rest. -/
theorem crgT_bind {γ : Type} (feR : IFEnv) (cv : IConstantVal) (gen : EIdx) (rest : AM γ) :
    (do
      unless ← looseBVarsBoundedFast coreWalkFuel 0 gen do
        fail (.internal "generated recursor: a rule of  is not closed")
      if ← hasFvarFast coreWalkFuel gen then
        fail (.internal "generated recursor: a rule of  is not closed")
      unless ← allLevelParamsDefined cv.levelParams gen do
        fail (.internal "generated recursor: a rule of  names an undeclared universe parameter")
      unless ← constsResolveFFast feR gen do
        fail (← unresolvedConstsError "generated rule of" gen)
      rest) = crgT feR cv gen >>= fun _ => rest := by
  simp only [crgT, bind_assoc, ite_bindAM, fail_bindAM, pure_bind]

/-- What `class_rule_ok_guards` gives besides the twin's guards' run (from `m`, `a`): the stage
relation, the growth, the abstraction memo, the core step, the rule closed. -/
structure CrgPost (dn : NIdx → Option ConLeche.Name) (visR : Word) (feR : IFEnv)
    (envR : ConLeche.Env) (m : Mem) (a : AState) (genP : ConLeche.Expr) (m' : Mem) (a' : AState) :
    Prop where
  stage : StageC dn visR feR envR m' a'
  grow : IWGrow m m'
  abs : AbsOK m'
  core : ConRon.Bridge.CoreStep V envR feR a a'
  closed : genP.hasFvar = false

/-- **`class_rule_ok_guards` refines `classRuleOk`'s guards (`crgT`), both outcomes**: the walks
(outside the verdict closure) under `StageC`, `all_level_params_defined` and
`consts_resolve_ffast` real (`apdF_okT`, `crfF_okT`); the one site of class `1`/`2` is the
consts-resolve site, the twin's `fail (← unresolvedConstsError …)` (`uce_errClaim_hi`). -/
theorem crg_ref {p : Prog} (hp : CruleProg p) (hApd : ApdF p) (n : Nat) {dn : NIdx → Option ConLeche.Name}
    {visR : Word} {feR : IFEnv} {envR : ConLeche.Env} {a : AState} {m : Mem} {cvR gen : Word}
    {cv : IConstantVal} (hC : StageC dn visR feR envR m a) (hgen : H gen)
    (hqd : decCV (erecP m) cvR.toNat = some cv) (hqb : cvR.toNat + 3 < 2 ^ 64) (hA : AbsOK m)
    {cvRP : ConLeche.ConstantVal} {genP : ConLeche.Expr}
    (hcvP : Frontend.denoteCV a.store cv = some cvRP)
    (hgP : denoteE a.store (decI gen) = some genP) :
    RefE (VerdictCtxU p) (crgE p n m visR cvR gen) (crgT feR cv (decI gen)) a
      (fun v _ a' => CrgPost dn visR feR envR m a genP v.2 a') := by
  cases n with
  | zero => rw [crgE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ N =>
  rw [crgE.arm1]
  have hS := hC.stage
  rcases h1 : lbbF m [CWF, 0, gen] with _ | ⟨r1, m1⟩
  · rw [liftE_none, crgE.k_loose_bvars_bounded_fast.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨x1, a1, hrun1, hS1, hg1, hx1, -⟩ :=
    lbbF_ok dn visR feR CWF 0 gen hgen m m1 a r1 h1 hS
  rw [CWF_eq, show ((0 : Word).toNat) = 0 from rfl] at hrun1
  by_cases hb1 : r1.headD 0 = 0
  · rw [crgE.k_loose_bvars_bounded_fast.abort1 _ _ _ _ _ _ _ hb1]; exact RefE.of_cls0 rfl
  rw [crgE.k_loose_bvars_bounded_fast.arm1 _ _ _ _ _ _ _ hb1]
  have ex1 : x1 = true := by rw [← hx1]; simpa using hb1
  subst ex1
  unfold crgT
  simp only [fail_bindAM]
  refine RefE.bind_right hrun1 (RefE.ite_pos rfl ?_)
  rcases h2 : hffF m1 [CWF, gen] with _ | ⟨r2, m2⟩
  · rw [liftE_none, crgE.k_has_fvar_fast.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2, -⟩ := hffF_ok dn visR feR CWF gen hgen m1 m2 a1 r2 h2 hS1
  rw [CWF_eq] at hrun2
  by_cases hb2 : r2.headD 0 ≠ 0
  · rw [crgE.k_has_fvar_fast.abort1 _ _ _ _ _ _ _ hb2]; exact RefE.of_cls0 rfl
  rw [crgE.k_has_fvar_fast.arm1 _ _ _ _ _ _ _ (by simpa using hb2)]
  have ex2 : x2 = false := by rw [← hx2]; simpa using hb2
  subst ex2
  refine RefE.bind_right hrun2 (RefE.ite_neg (by decide) ?_)
  -- the twin's closedness guards
  obtain ⟨-, hlps, -⟩ := ConRon.Bridge.Core.denoteCV_inv hcvP
  obtain ⟨p1, -⟩ := ConRon.Bridge.Inductives.RC.looseBVarsBoundedFast_pstep hC.check.state hgP hrun1
  obtain ⟨p2, hfv⟩ := ConRon.Bridge.Inductives.RC.hasFvarFast_pstep p1.ok
    (ConRon.Bridge.denote_ext hgP p1.ext) hrun2
  have p12 := p1.trans p2
  -- `cv_lps` (outside the verdict closure)
  rcases h3 : callE p N "cv_lps" [cvR] m2 with e3 | ⟨r3, m3⟩
  · rw [crgE.k_cv_lps.none]
    exact fun hV => ErrClaim.of_callE_nv hV.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h3
  rw [crgE.k_cv_lps.arm1]
  obtain ⟨s3, hs3, -, h3', -⟩ := triple_of_callE
    (L.Arena.cvLps_specW p hp.alloc hp.copy hp.eti hp.lps N ⟨m2, Locals.init []⟩ cvR) h3
  rw [hs3] at h3'
  have hg12 := hg1.trans hg2
  obtain ⟨hS3, hg3, hd3, -⟩ := cvLpsA_stage h3' hS2 (ArrExt.decCV (IWGrow.erecExt hg12) hqd) hqb
  have hA3 : AbsOK m3 := by
    have hA2 : AbsOK m2 := (AFr.of_frame (lbbF_frame h1)).trans (AFr.of_frame (hffF_frame h2)) hA
    cases N with
    | zero => simp [L.Arena.cvLpsW] at h3'
    | succ N => exact erToIwW_afr h3' hA2
  have hC3 : StageC dn visR feR envR m3 a2 := hC.of_pstep hS3 hA3 p12
  -- `all_level_params_defined`, real
  rcases h4 : callE p N "all_level_params_defined" [r3.headD 0, r3.tail.headD 0, gen] m3 with
    e4 | ⟨r4, m4⟩
  · rw [crgE.k_all_level_params_defined.none]
    exact fun hV => ErrClaim.of_callE_nv hV.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h4
  have h4' := apdF_of_callW hApd (callW_of_callE h4)
  have hlps2 := ConRon.Bridge.denoteNList_ext p12.ext.lss.ls.ns _ _ hlps
  obtain ⟨x4, a4, hrun4, hT4, hg4, hx4, -⟩ := apdF_okT dn visR feR _ _ gen hgen cv.levelParams m3 m4
    a2 r4 h4' ⟨hC3.stageT, hd3, _, denoteNList_mapM hlps2⟩
  have hA4 : AbsOK m4 := absOK_apdF h4' hA3 hT4
  by_cases hb4 : r4.headD 0 = 0
  · rw [crgE.k_all_level_params_defined.abort1 _ _ _ _ _ _ hb4]; exact RefE.of_cls0 rfl
  rw [crgE.k_all_level_params_defined.arm1 _ _ _ _ _ _ hb4]
  have ex4 : x4 = true := by rw [← hx4]; simpa using hb4
  subst ex4
  refine RefE.bind_right hrun4 (RefE.ite_pos rfl ?_)
  obtain ⟨h3st, h3c, h3p, -⟩ := ConRon.Bridge.allLevelParamsDefined_run p2.ok hlps2
    (ConRon.Bridge.denote_ext hgP p12.ext) hrun4
  have p3 : ConRon.Bridge.Inductives.PStep a2 a4 :=
    ConRon.Bridge.Inductives.PStep.of_caches ⟨by rw [h3st]; exact p2.ok.wf⟩
      (by rw [h3st]; exact Ext.refl _) h3c h3p
  have c13 := (p12.trans p3).toCore hC.check
  have hC4 : StageC dn visR feR envR m4 a4 := StageC.of_T hT4 c13.ok
  -- `consts_resolve_ffast`, real
  rcases h5 : crfF m4 [visR, gen] with _ | ⟨r5, m5⟩
  · rw [liftE_none, crgE.k_consts_resolve_ffast.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨x5, a5, hrun5, ⟨hT5, hg5, hx5, -⟩, hCr5⟩ :=
    crfF_okT dn visR feR gen hgen m4 m5 a4 r5 h5 ⟨hC4.stageT, hA4.crMemo⟩
  refine RefE.bind_right hrun5 ?_
  by_cases hb5 : r5.headD 0 = 0
  · -- the consts-resolve site
    rw [crgE.k_consts_resolve_ffast.arm1 _ _ _ _ _ _ hb5]
    have ex5 : x5 = false := by rw [← hx5]; simpa using hb5
    subst ex5
    refine RefE.ite_neg (by decide) ?_
    rcases h6 : callE p N "unresolved_consts_error" [visR, gen, 3] m5 with e6 | ⟨r6, m6⟩
    · rw [crgE.k_unresolved_consts_error.none]
      obtain ⟨M5, hC5⟩ := hT5.core
      exact fun hV => uce_errClaim_hi hV.uce hV.nv hC5.arena.base hC5.pins hgen (by decide) h6 _
    rw [crgE.k_unresolved_consts_error.abort1]; exact RefE.of_cls0 rfl
  rw [crgE.k_consts_resolve_ffast.arm2 _ _ _ _ _ _ hb5]
  have ex5 : x5 = true := by rw [← hx5]; simpa using hb5
  subst ex5
  obtain ⟨p4, -⟩ := ConRon.Bridge.Inductives.constsResolveFFast_pstep c13.ok.toR
    (ConRon.Bridge.denote_ext hgP c13.ext) hrun5
  have c14 := c13.trans (p4.toCore c13.ok)
  refine RefE.ite_pos rfl (RefE.ret rfl ⟨StageC.of_T hT5 c14.ok,
    ((hg12.trans hg3).trans hg4).trans hg5, absOK_crfF h5 hA4 hCr5 hT5, c14, by rw [← hfv]⟩)

end L.Ind

end
