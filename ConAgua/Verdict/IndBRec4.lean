import ConAgua.Arena.IndT.RecGen4
import ConAgua.Verdict.IndBSum4

/-!
# Error refinement of `class_rule_ok` (lane `verdicts-b`, helper `ib`)

All of its own aborts are of class `0` (the twin's `.internal`); only `infer_type_core`'s claim
remains.
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false
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
`infer_type_core` claim): a failing call of class `1`/`2` is the inference's. -/
theorem classRuleOk_claim (hp : CruleProg p) (hApd : ApdF p) (N : Nat) (hN : N ≤ 2 ^ 62) (s₀ : St)
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
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
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
  exfalso
  apply hk0
  cases h3 : callE p N "flush_caches" [] m2 with
  | error e3 =>
    rw [h3, cruleE.k_flush_caches.none] at hW
    cases hW
    exact callE_nv hnv (by decide +kernel) _ _ _ h3
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, cruleE.k_flush_caches.arm1] at hW
  cases h4 : callE p N "strip_lams" [n, gen] m3 with
  | error e4 =>
    rw [h4, cruleE.k_strip_lams.none] at hW
    cases hW
    exact callE_nv hnv (by decide +kernel) _ _ _ h4
  | ok q4 =>
  obtain ⟨r4, m4⟩ := q4
  by_cases h40 : r4.headD 0 = 0
  · rw [h4, cruleE.k_strip_lams.abort1 p N visT gen r4 m4 h40] at hW
    cases hW; rfl
  rw [h4, cruleE.k_strip_lams.arm1 p N visT gen r4 m4 h40] at hW
  cases h5 : callE p N "class_rule_ok_domains" [visT, r4.tail.headD 0, r4.tail.tail.headD 0] m4 with
  | error e5 =>
    rw [h5, cruleE.k_class_rule_ok_domains.none] at hW
    cases hW
    exact callE_nv hnv (by decide +kernel) _ _ _ h5
  | ok q5 =>
  obtain ⟨r5, m5⟩ := q5
  by_cases h50 : r5.headD 0 = 0
  · rw [h5, cruleE.k_class_rule_ok_domains.abort1 p gen r5 m5 h50] at hW
    cases hW; rfl
  rw [h5, cruleE.k_class_rule_ok_domains.arm1 p gen r5 m5 h50] at hW
  cases hW

end sims

end L.Ind
