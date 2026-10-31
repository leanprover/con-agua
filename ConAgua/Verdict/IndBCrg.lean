module

public import ConAgua.Arena.RecGenSpec.CruleProg
public import ConAgua.Verdict.VCtx
public import ConAgua.Arena.IndT.Lift
public import ConAgua.Arena.IndT.WalkC
public import ConAgua.Arena.IndRealMemoCrT
public import ConAgua.Arena.RecGenSpec.FlushStage
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.ModelGen
public import ConRon.Bridge.Inductives.GenRec

@[expose] public section

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
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
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
  unfold crgT
  simp only [fail_bindAM]
  refine RefE.bindSim (fun _ => rfl) (fun r m' h => lbbF_ok dn visR feR CWF 0 gen hgen m m' a r h hC.stage)
    fun r1 x1 m1 a1 h1 hrun1 ⟨hS1, hg1, hx1, _⟩ => ?_
  dsimp only [crgE.k_loose_bvars_bounded_fast]
  refine RefE.abort0 rfl fun hb1 => ?_
  obtain rfl : x1 = true := by rw [← hx1]; simpa using hb1
  refine RefE.ite_pos rfl ?_
  refine RefE.bindSim (fun _ => rfl) (fun r m' h => hffF_ok dn visR feR CWF gen hgen m1 m' a1 r h hS1)
    fun r2 x2 m2 a2 h2 hrun2 ⟨hS2, hg2, hx2, _⟩ => ?_
  dsimp only [crgE.k_has_fvar_fast]
  refine RefE.abort0 rfl fun hb2 => ?_
  obtain rfl : x2 = false := by rw [← hx2]; simpa using hb2
  refine RefE.ite_neg (by decide) ?_
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
  have hlps2 := ConRon.Bridge.denoteNList_ext p12.ext.lss.ls.ns _ _ hlps
  refine RefE.bindCall (fun _ => rfl)
    (fun hV _ h4 => ErrClaim.of_callE_nv hV.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h4)
    (fun b h4 => apdF_okT dn visR feR _ _ gen hgen cv.levelParams m3 b.2 a2 b.1 (apdF_of_callW hApd h4)
      ⟨hC3.stageT, hd3, _, denoteNList_mapM hlps2⟩)
    fun r4 m4 x4 a4 h4 hrun4 ⟨hT4, hg4, hx4, _⟩ => ?_
  have hA4 : AbsOK m4 := absOK_apdF (apdF_of_callW hApd (callW_of_callE h4)) hA3 hT4
  dsimp only [crgE.k_all_level_params_defined]
  refine RefE.abort0 rfl fun hb4 => ?_
  obtain rfl : x4 = true := by rw [← hx4]; simpa using hb4
  refine RefE.ite_pos rfl ?_
  obtain ⟨h3st, h3c, h3p, -⟩ := ConRon.Bridge.allLevelParamsDefined_run p2.ok hlps2
    (ConRon.Bridge.denote_ext hgP p12.ext) hrun4
  have p3 : ConRon.Bridge.Inductives.PStep a2 a4 :=
    ConRon.Bridge.Inductives.PStep.of_caches ⟨by rw [h3st]; exact p2.ok.wf⟩
      (by rw [h3st]; exact Ext.refl _) h3c h3p
  have c13 := (p12.trans p3).toCore hC.check
  have hC4 : StageC dn visR feR envR m4 a4 := StageC.of_T hT4 c13.ok
  -- `consts_resolve_ffast`, real
  refine RefE.bindSim (fun _ => rfl)
    (fun r m' h => crfF_okT dn visR feR gen hgen m4 m' a4 r h ⟨hC4.stageT, hA4.crMemo⟩)
    fun r5 x5 m5 a5 h5 hrun5 ⟨⟨hT5, hg5, hx5, _⟩, hCr5⟩ => ?_
  rw [crgE.k_consts_resolve_ffast.eq_2]
  refine RefE.splitNot (fun hb5 => by rw [← hx5]; simpa using hb5) (fun hb5 => by rw [← hx5] at hb5; simpa using hb5)
    (fun _ _ => ?_) fun _ hb5 => ?_
  · -- the consts-resolve site
    rcases h6 : callE p N "unresolved_consts_error" [visR, gen, 3] m5 with e6 | ⟨r6, m6⟩
    · rw [crgE.k_unresolved_consts_error.none]
      obtain ⟨M5, hC5⟩ := hT5.core
      exact fun hV => uce_errClaim_hi hV.uce hV.nv hC5.arena.base hC5.pins hgen (by decide) h6 _
    rw [crgE.k_unresolved_consts_error.abort1]; exact RefE.of_cls0 rfl
  subst hb5
  obtain ⟨p4, -⟩ := ConRon.Bridge.Inductives.constsResolveFFast_pstep c13.ok.toR
    (ConRon.Bridge.denote_ext hgP c13.ext) hrun5
  have c14 := c13.trans (p4.toCore c13.ok)
  exact RefE.ret rfl ⟨StageC.of_T hT5 c14.ok,
    ((hg12.trans hg3).trans hg4).trans hg5, absOK_crfF h5 hA4 hCr5 hT5, c14, by rw [← hfv]⟩

end L.Ind

end
