import ConAgua.Arena.IndT.RecGen4
import ConAgua.Verdict.IndBSum4
import ConAgua.Verdict.UnresolvedE

/-!
# Error refinement of `class_rule_ok` (lane `verdicts-b`, helper `ib`)

Its own aborts are of class `0` (the twin's `.internal`) but for the two consts-resolve sites
(`class_rule_ok_guards`' and the domains'), calls of `unresolved_consts_error` (`uce_errClaim_hi`);
the inference's claim is `infer_type_core`'s.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model crgE_spec (p : Prog) (hf : p.lookup "class_rule_ok_guards" = some classRuleOkGuards)
  fns [hf ↦ crgE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] errors

l_model cruleE_spec (p : Prog) (hf : p.lookup "class_rule_ok" = some classRuleOkL)
  fns [hf ↦ cruleE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] errors

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name}
  (hnv : closedNV p _root_.L.Checker.nvFns = true) (hcE : CoreStubsE p)


include hnv in
/-- **`class_rule_ok_guards`' error claim** (`crgW_okC`'s hypotheses): a failing call of class
`1`/`2` is the consts-resolve site, the twin's `fail (← unresolvedConstsError …)`. -/
theorem crgE_claim (hp : CruleProg p) (hApd : ApdF p) (hU : UceProg p) {visT visR : Word}
    {feR : IFEnv} {envR : ConLeche.Env} {a : AState} {N : Nat} {m : Mem} {cvR n gen : Word}
    {cv : IConstantVal} {e : Err}
    (h : callE p N "class_rule_ok_guards" [visR, cvR, gen] m = .error e)
    (hC : StageC dn visR feR envR m a) (hgen : H gen)
    (hqd : decCV (erecP m) cvR.toNat = some cv) (hqb : cvR.toNat + 3 < 2 ^ 64) (hA : AbsOK m)
    {cvRP : ConLeche.ConstantVal} {genP : ConLeche.Expr}
    (hcvP : Frontend.denoteCV a.store cv = some cvRP)
    (hgP : denoteE a.store (decI gen) = some genP) :
    ErrClaim (ConRon.Arena.classRuleOk .verified visT.toNat feR cv n.toNat (decI gen)) a e := by
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (crgE_spec p hp.guards N ⟨m, Locals.init []⟩ visR cvR gen) h
    (Err.code_ne_of_cls hk0)
  cases N with
  | zero => rw [crgE.eq_def] at hW; cases hW; exact absurd rfl hk0
  | succ N =>
  rw [crgE.arm1] at hW
  have hS := hC.stage
  cases h1 : callE p N "loose_bvars_bounded_fast" [CWF, 0, gen] m with
  | error e1 =>
    rw [h1, crgE.k_loose_bvars_bounded_fast.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  obtain ⟨s1, hs1, -, h1'⟩ := triple_of_callE (lbbF_spec p hp.bvb N ⟨m, Locals.init []⟩ _) h1
  rw [hs1] at h1'
  obtain ⟨x1, a1, hrun1, hS1, hg1, hx1, -⟩ :=
    lbbF_ok dn visR feR CWF 0 gen hgen m m1 a r1 h1' hS
  by_cases hb1 : r1.headD 0 = 0
  · rw [h1, crgE.k_loose_bvars_bounded_fast.abort1 _ _ _ _ _ _ _ hb1] at hW; cases hW
    exact absurd rfl hk0
  rw [h1, crgE.k_loose_bvars_bounded_fast.arm1 _ _ _ _ _ _ _ hb1] at hW
  cases h2 : callE p N "has_fvar_fast" [CWF, gen] m1 with
  | error e2 =>
    rw [h2, crgE.k_has_fvar_fast.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  obtain ⟨s2, hs2, -, h2'⟩ := triple_of_callE (hffF_spec p hp.hf N ⟨m1, Locals.init []⟩ _) h2
  rw [hs2] at h2'
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2, -⟩ :=
    hffF_ok dn visR feR CWF gen hgen m1 m2 a1 r2 h2' hS1
  by_cases hb2 : r2.headD 0 ≠ 0
  · rw [h2, crgE.k_has_fvar_fast.abort1 _ _ _ _ _ _ _ hb2] at hW; cases hW
    exact absurd rfl hk0
  rw [h2, crgE.k_has_fvar_fast.arm1 _ _ _ _ _ _ _ (by simpa using hb2)] at hW
  have ex1 : x1 = true := by rw [← hx1]; simpa using hb1
  have ex2 : x2 = false := by rw [← hx2]; simpa using hb2
  rw [CWF_eq] at hrun1 hrun2
  rw [show ((0 : Word).toNat) = 0 from rfl] at hrun1
  subst ex1 ex2
  obtain ⟨-, hlps, -⟩ := ConRon.Bridge.Core.denoteCV_inv hcvP
  obtain ⟨p1, -⟩ := ConRon.Bridge.Inductives.RC.looseBVarsBoundedFast_pstep hC.check.state hgP hrun1
  obtain ⟨p2, hfv⟩ := ConRon.Bridge.Inductives.RC.hasFvarFast_pstep p1.ok
    (ConRon.Bridge.denote_ext hgP p1.ext) hrun2
  have p12 := p1.trans p2
  cases h3 : callE p N "cv_lps" [cvR] m2 with
  | error e3 =>
    rw [h3, crgE.k_cv_lps.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h3
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  obtain ⟨s3, hs3, -, h3', -⟩ := triple_of_callE
    (L.Arena.cvLps_specW p hp.alloc hp.copy hp.eti hp.lps N ⟨m2, Locals.init []⟩ cvR) h3
  rw [hs3] at h3'
  rw [h3, crgE.k_cv_lps.arm1] at hW
  have hg12 := hg1.trans hg2
  obtain ⟨hS3, hg3, hd3, -⟩ := cvLpsA_stage h3' hS2 (ArrExt.decCV (IWGrow.erecExt hg12) hqd) hqb
  have hA3 : AbsOK m3 := by
    have hA2 : AbsOK m2 := (AFr.of_frame (lbbF_frame h1')).trans (AFr.of_frame (hffF_frame h2')) hA
    cases N with
    | zero => simp [L.Arena.cvLpsW] at h3'
    | succ N => exact erToIwW_afr h3' hA2
  have hC3 : StageC dn visR feR envR m3 a2 := hC.of_pstep hS3 hA3 p12
  cases h4 : callE p N "all_level_params_defined" [r3.headD 0, r3.tail.headD 0, gen] m3 with
  | error e4 =>
    rw [h4, crgE.k_all_level_params_defined.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h4
  | ok q4 =>
  obtain ⟨r4, m4⟩ := q4
  have h4' := apdF_of_callW hApd (callW_of_callE h4)
  have hlps2 := ConRon.Bridge.denoteNList_ext p12.ext.lss.ls.ns _ _ hlps
  obtain ⟨x4, a4, hrun4, hT4, hg4, hx4, -⟩ :=
    apdF_okT dn visR feR _ _ gen hgen cv.levelParams m3 m4 a2 r4 h4' ⟨hC3.stageT, hd3, _, denoteNList_mapM hlps2⟩
  have hA4 : AbsOK m4 := absOK_apdF h4' hA3 hT4
  by_cases hb4 : r4.headD 0 = 0
  · rw [h4, crgE.k_all_level_params_defined.abort1 _ _ _ _ _ _ hb4] at hW; cases hW
    exact absurd rfl hk0
  rw [h4, crgE.k_all_level_params_defined.arm1 _ _ _ _ _ _ hb4] at hW
  have ex4 : x4 = true := by rw [← hx4]; simpa using hb4
  subst ex4
  obtain ⟨h3st, h3c, h3p, -⟩ := ConRon.Bridge.allLevelParamsDefined_run p2.ok hlps2
    (ConRon.Bridge.denote_ext hgP p12.ext) hrun4
  have p3 : ConRon.Bridge.Inductives.PStep a2 a4 :=
    ConRon.Bridge.Inductives.PStep.of_caches ⟨by rw [h3st]; exact p2.ok.wf⟩
      (by rw [h3st]; exact Ext.refl _) h3c h3p
  have c13 := (p12.trans p3).toCore hC.check
  have hC4 : StageC dn visR feR envR m4 a4 := StageC.of_T hT4 c13.ok
  cases h5 : callE p N "consts_resolve_ffast" [visR, gen] m4 with
  | error e5 =>
    rw [h5, crgE.k_consts_resolve_ffast.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h5
  | ok q5 =>
  obtain ⟨r5, m5⟩ := q5
  obtain ⟨x5, a5, hrun5, ⟨hT5, hg5, hx5, -⟩, hCr5⟩ :=
    crfF_okT dn visR feR gen hgen m4 m5 a4 r5 (crfF_of_callW hp.hcr (callW_of_callE h5))
      ⟨hC4.stageT, hA4.crMemo⟩
  by_cases hb5' : r5.headD 0 ≠ 0
  · rw [h5, crgE.k_consts_resolve_ffast.arm2 _ _ _ _ _ _ hb5'] at hW; cases hW
  have hb5 : r5.headD 0 = 0 := by simpa using hb5'
  rw [h5, crgE.k_consts_resolve_ffast.arm1 _ _ _ _ _ _ hb5] at hW
  have ex5 : x5 = false := by rw [← hx5]; simpa using hb5
  subst ex5
  unfold ConRon.Arena.classRuleOk
  simp only [bind_assoc, ite_bindAM, fail_bindAM, pure_bind]
  refine ErrClaim.bind_right hrun1 (ErrClaim.ite_pos rfl ?_)
  refine ErrClaim.bind_right hrun2 (ErrClaim.ite_neg (by decide) ?_)
  refine ErrClaim.bind_right hrun4 (ErrClaim.ite_pos rfl ?_)
  refine ErrClaim.bind_right hrun5 (ErrClaim.ite_neg (by decide) ?_)
  cases h6 : callE p N "unresolved_consts_error" [visR, gen, 3] m5 with
  | error e6 =>
    rw [h6, crgE.k_unresolved_consts_error.none] at hW; cases hW
    obtain ⟨M5, hC5⟩ := hT5.core
    exact uce_errClaim_hi hU hnv hC5.arena.1 hC5.pins hgen (by decide) h6 _
  | ok q6 =>
    obtain ⟨r6, m6⟩ := q6
    rw [h6, crgE.k_unresolved_consts_error.abort1] at hW; cases hW
    exact ErrClaim.of_cls0 rfl

include hq hnv hcE in
/-- **`class_rule_ok`'s error claim** (the hypotheses of `classRuleOk_refinesC`, the core stubs'
`infer_type_core` claim): a failing call of class `1`/`2` is the guards' consts-resolve site, the
inference's, or the domains' consts-resolve site. -/
theorem classRuleOk_claim (hp : CruleProg p) (hApd : ApdF p) (hU : UceProg p) (N : Nat)
    (hN : N ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (visT visR : Word) (feR : IFEnv) {envR env₂ : ConLeche.Env}
    (henvR : ConLeche.EnvWF envR) (cvR n gen : Word) (cv : IConstantVal)
    (hC : StageC dn visR feR envR s₀.mem a₀) (hgen : H gen)
    (hqd : decCV (erecP s₀.mem) cvR.toNat = some cv) (hqb : cvR.toNat + 3 < 2 ^ 64)
    (hA : AbsOK s₀.mem) {cvRP : ConLeche.ConstantVal} {genP : ConLeche.Expr}
    (hcvP : Frontend.denoteCV a₀.store cv = some cvRP)
    (hgP : denoteE a₀.store (decI gen) = some genP)
    (hie : ConRon.Bridge.Inductives.IFEnvOKS env₂ (feR.restrictTo visT.toNat) a₀.store) :
    CoreSpecE p N "class_rule_ok" [visT, visR, cvR, n, gen]
      (ConRon.Arena.classRuleOk .verified visT.toNat feR cv n.toNat (decI gen)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc' => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (cruleE_spec p hp.rule N ⟨s₀.mem, Locals.init []⟩ visT visR cvR n gen) hc'
    (Err.code_ne_of_cls hk0)
  cases N with
  | zero => rw [cruleE.eq_def] at hW; cases hW; exact absurd rfl hk0
  | succ N =>
  rw [cruleE.arm1] at hW
  cases h1 : callE p N "class_rule_ok_guards" [visR, cvR, gen] s₀.mem with
  | error e1 =>
    rw [h1, cruleE.k_class_rule_ok_guards.none] at hW
    cases hW
    exact crgE_claim hnv hp hApd hU h1 hC hgen hqd hqb hA hcvP hgP
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, cruleE.k_class_rule_ok_guards.arm1] at hW
  obtain ⟨s1, hs1, -, h1m⟩ := triple_of_callW (classRuleOkGuards_spec p hp (realCall p) (realCall_spec p) N
    ⟨s₀.mem, Locals.init []⟩ visR cvR gen) (callW_of_callE h1)
  subst hs1
  obtain ⟨a1, a2, a4, a5, hl, hf, ha, hc, hC1, hg1, hA1, c14, hfvP⟩ :=
    crgW_okC hApd h1m hC hgen hqd hqb hA hcvP hgP
  have hws : ConLeche.Expr.WScoped 0 genP := ConLeche.Expr.WScoped.of_not_hasFvar hfvP
  unfold ConRon.Arena.classRuleOk
  simp only [bind_assoc, ite_bindAM, fail_bindAM, pure_bind]
  refine ErrClaim.bind_right hl (ErrClaim.ite_pos rfl ?_)
  refine ErrClaim.bind_right hf (ErrClaim.ite_neg (by decide) ?_)
  refine ErrClaim.bind_right ha (ErrClaim.ite_pos rfl ?_)
  refine ErrClaim.bind_right hc (ErrClaim.ite_pos rfl ?_)
  -- the inference
  cases h2 : callE p N "infer_type_core" [visR, 0, gen] s1.mem with
  | error e2 =>
    rw [h2, cruleE.k_infer_type_core.none] at hW
    cases hW
    refine ErrClaim.bind_left ?_
    have := hcE.inferTypeCore N (by omega) hC1.stageT 0 gen hgen _ h2
    simpa using this
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, cruleE.k_infer_type_core.arm1] at hW
  obtain ⟨x6, a6, hi, hC2, hg2, -, hA2, c5, -⟩ := inferC_rsim hq henvR N (by omega) hC1 hA1 0 gen
    hgen (ConRon.Bridge.denote_ext hgP c14.ext) hws (r2, m2) (callW_of_callE h2)
  rw [show ((0 : Word).toNat) = 0 from rfl] at hi
  refine ErrClaim.bind_right hi ?_
  cases h3 : callE p N "flush_caches" [] m2 with
  | error e3 =>
    rw [h3, cruleE.k_flush_caches.none] at hW
    cases hW
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h3
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, cruleE.k_flush_caches.arm1] at hW
  obtain ⟨s3, hs3, -, hok, hm3⟩ := triple_of_callE
    (flushCaches_spec p hp.toFlushProg N ⟨m2, Locals.init []⟩) h3
  rw [hs3] at hm3
  subst hm3
  obtain ⟨hS3, hg3⟩ := flush_stage hC2.stage hok
  obtain ⟨hok6, -, hst6⟩ := ConRon.Bridge.Inductives.ReadOK.flush (μ := V) hC2.check.toR
    (flushCaches_run a6)
  have hA3 : AbsOK (flushMem m2) := AFr.of_frame (flushMem_frame _) (by decide) (by decide) hA2
  have hx6 : Ext a6.store ({ a6 with caches := Caches.empty } : AState).store := Ext.refl _
  have hC3 := hC2.of_check hS3 hA3 hok6 hx6
  have c16 := (c14.trans c5).trans
    (⟨hok6, by rw [hst6]; exact Ext.refl _, rfl⟩ :
      ConRon.Bridge.CoreStep V envR feR a6 { a6 with caches := Caches.empty })
  refine ErrClaim.bind_right (flushCaches_run a6) ?_
  cases h4 : callE p N "strip_lams" [n, gen] (flushMem m2) with
  | error e4 =>
    rw [h4, cruleE.k_strip_lams.none] at hW
    cases hW
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h4
  | ok q4 =>
  obtain ⟨r4, m4⟩ := q4
  obtain ⟨s4, hs4, -, h4'⟩ := triple_of_callE
    (stripLams_specF p hp.strip N ⟨flushMem m2, Locals.init []⟩ n gen) h4
  rw [hs4] at h4'
  obtain ⟨x7, a7, hs, hS4, hg4, hd4⟩ := stripF_lams_ok dn visR feR n gen hgen _ m4 _ r4 h4' hS3
  have hA4 : AbsOK m4 := stripF_afr h4' hA3
  obtain ⟨hs7, hq7⟩ := ConRon.Bridge.Inductives.stripLams_pstep hok6.state
    (ConRon.Bridge.denote_ext hgP c16.ext) hs
  subst hs7
  have hC4 : StageC dn visR feR envR m4 { a6 with caches := Caches.empty } :=
    hC3.of_check hS4 hA4 hok6 (Ext.refl _)
  refine ErrClaim.bind_right hs ?_
  rcases x7 with _ | ⟨rbs, body⟩
  · rw [h4, cruleE.k_strip_lams.abort1 p N visT visR gen r4 m4 hd4] at hW
    cases hW; exact absurd rfl hk0
  obtain ⟨h41, ⟨hdl, htl⟩, -⟩ := hd4
  have h40 : r4.headD 0 ≠ 0 := by rw [h41]; decide
  rw [h4, cruleE.k_strip_lams.arm1 p N visT visR gen r4 m4 h40] at hW
  simp only [getD_one, getD_two, Nat.reduceAdd] at hdl htl
  obtain ⟨rbsP, bodyP, -, hrbs, -⟩ := ConRon.Bridge.Inductives.denoteBP_some hq7
  cases h5 : callE p N "class_rule_ok_domains" [visT, r4.tail.headD 0, r4.tail.tail.headD 0] m4 with
  | error e5 =>
    rw [h5, cruleE.k_class_rule_ok_domains.none] at hW
    cases hW
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h5
  | ok q5 =>
  obtain ⟨r5, m5⟩ := q5
  obtain ⟨s5, hs5, -, h5'⟩ := triple_of_callE
    (classRuleOkDomains_spec p hp.dom hp.hcr N ⟨m4, Locals.init []⟩ _ _ _) h5
  rw [hs5] at h5'
  have hb4 : (r4.tail.headD 0).toNat + (r4.tail.tail.headD 0).toNat < 2 ^ 64 := by
    have h1 : iwTop m4 ≤ (m4.arr64 IW).size := hS4.2.1
    have h2 : (m4.arr64 IW).size < 2 ^ 64 := hS4.2.2.2.1
    omega
  obtain ⟨b, a8, hdom, ⟨hS5, hg5, hb5⟩, hA5⟩ := iarW_ok dn (feR.restrictTo visT.toNat) N m4 m5 _
    visT _ _ rbs r5 h5' (hS4.restrict visT) hdl hb4 htl hA4
  have hdom' := hdom
  rw [← allM_resolve_eq] at hdom'
  have hr6 : ConRon.Bridge.Inductives.ReadOK env₂ (feR.restrictTo visT.toNat)
      { a6 with caches := Caches.empty } :=
    ⟨hok6.state, hok6.pins, (hie.mono c16.ext) _ rfl⟩
  obtain ⟨p8, -⟩ := ConRon.Bridge.Inductives.allM_domains_resolve rbs rbsP _ a8 b hr6 hrbs hdom'
  have c18 := c16.trans (p8.toCore hok6)
  by_cases h50' : r5.headD 0 ≠ 0
  · rw [h5, cruleE.k_class_rule_ok_domains.arm2 p _ _ _ r5 m5 h50'] at hW
    cases hW
  have h50 : r5.headD 0 = 0 := by simpa using h50'
  rw [h5, cruleE.k_class_rule_ok_domains.arm1 p _ _ _ r5 m5 h50] at hW
  have eb : b = false := by rw [← hb5.1]; simpa using h50
  subst eb
  refine ErrClaim.bind_right hdom' (ErrClaim.ite_neg (by decide) ?_)
  have hC5 : StageC dn visR feR envR m5 a8 :=
    hC4.of_check (hS5.unrestrict hC.stage.1.env.vis) hA5 c18.ok (p8.ext)
  cases h6 : callE p N "unresolved_consts_error" [visR, gen, 4] m5 with
  | error e6 =>
    rw [h6, cruleE.k_unresolved_consts_error.none] at hW; cases hW
    obtain ⟨M5, hC5'⟩ := hC5.stageT.core
    exact uce_errClaim_hi hU hnv hC5'.arena.1 hC5'.pins hgen (by decide) h6 _
  | ok q6 =>
    obtain ⟨r6, m6⟩ := q6
    rw [h6, cruleE.k_unresolved_consts_error.abort1] at hW; cases hW
    exact ErrClaim.of_cls0 rfl

end sims

end L.Ind
