import ConAgua.Verdict.IndBCrg
import ConAgua.Arena.RecGenSpec.CfhW
import ConAgua.Arena.IndSumSpec.FieldDomsResolve
import ConAgua.Arena.DeclValSpec
import ConRon.Bridge.Inductives.GenRec
import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen
/-!
# Error refinement of `class_rule_ok` (lane `verdicts-b`, helper `ib`)

Its own aborts are of class `0` (the twin's `.internal`) but for the domains' consts-resolve site,
a call of `unresolved_consts_error` (`uce_errClaim_hi`); the guards' claim is `crg_ref`'s error
half (`RefE.run_err`), the inference's is `infer_type_core`'s.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model cruleE_spec (p : Prog) (hf : p.lookup "class_rule_ok" = some classRuleOkL)
  fns [hf ↦ cruleE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] errors

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name}
  (hnv : closedNV p _root_.L.Checker.nvFns = true) (hcE : CoreStubsE p)


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
  have hR := crg_ref hp hApd N hC hgen hqd hqb hA hcvP hgP
  have hsG := crgE_spec p hp N ⟨s₀.mem, Locals.init []⟩ visR cvR gen
  unfold ConRon.Arena.classRuleOk
  rw [crgT_bind]
  cases h1 : callE p N "class_rule_ok_guards" [visR, cvR, gen] s₀.mem with
  | error e1 =>
    rw [h1, cruleE.k_class_rule_ok_guards.none] at hW
    cases hW
    exact ErrClaim.bind_left (RefE.run_err hsG hnv ⟨⟨hnv, hcE⟩, hU⟩ hR h1)
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, cruleE.k_class_rule_ok_guards.arm1] at hW
  obtain ⟨s1, rfl, -, _, a5, hc, ⟨hC1, hg1, hA1, c14, hfvP⟩⟩ := RefE.run_ok hsG hR h1
  have hws : ConLeche.Expr.WScoped 0 genP := ConLeche.Expr.WScoped.of_not_hasFvar hfvP
  simp only [fail_bindAM]
  refine ErrClaim.bind_right hc ?_
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
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h3
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
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h4
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
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h5
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
