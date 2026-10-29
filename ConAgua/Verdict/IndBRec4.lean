import ConAgua.Arena.RecGenSpec.CfhW
import ConAgua.Verdict.IndBCrg
import ConAgua.Arena.RecGenSpec.Rec3TmdWDecB
import ConAgua.Arena.RecGenSpec.ClassFeR
import ConAgua.Arena.IndSumSpec.FieldDomsResolve
import ConRon.Bridge.Inductives.GenRec
import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen
/-!
# `class_rule_ok`, `class_rules_ok_one`: one model and one refinement for both outcomes

`cruleE` (`l_model … unified`: the guards through `crgE`, the flush, `strip_lams` and the domains
lifted) and `crule_ref` under `StageC` (twin side con-ron's `classRuleOk_spec`'s proof). Its own
aborts are of class `0` (the twin's `.internal`) but for the domains' consts-resolve site, a call of
`unresolved_consts_error` (`uce_errClaim_hi`, so `G` is `VerdictCtxU`); the guards' errors are
`crg_ref`'s, the inference's the core stub's claim. `class_rules_ok_one` (`cr1_ref`) is its word
sum's overflow abort, then `class_rule_ok` in tail position. Their ok halves are
`classRuleOk_refinesC`; both halves of both go into `class_rules_ok`'s refinement (`crs_ref`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model cruleE_spec (p : Prog) (hp : CruleProg p)
  fns [hp.rule ↦ cruleE]
  specs [crgE_spec p hp n, flushCaches_spec p hp.toFlushProg n, stripLams_specF p hp.strip n,
    classRuleOkDomains_spec p hp.dom hp.hcr n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `class_rule_ok` gives besides the twin's rule `y` (from `m`, `a`): the stage invariant
under `StageC`, the growth, the rule returned as built (`gen` itself), the abstraction memo, the
core step. -/
structure CrulePost (dn : NIdx → Option ConLeche.Name) (visR : Word) (feR : IFEnv)
    (envR : ConLeche.Env) (m : Mem) (a : AState) (gen w : Word) (m' : Mem) (y : EIdx) (a' : AState) :
    Prop where
  stage : StageC dn visR feR envR m' a'
  grow : IWGrow m m'
  val : w = gen
  res : y = decI gen
  abs : AbsOK m'
  core : ConRon.Bridge.CoreStep V envR feR a a'

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name}

include hq in
/-- **`class_rule_ok` refines `classRuleOk`, both outcomes** under `StageC` (twin side con-ron's
`classRuleOk_spec`'s proof): the guards (`crg_ref`, against `crgT`: `crgT_bind`), the inference
(`inferC_rsim`; its error the core stub's claim), the flush (`ReadOK.flush`), the λ-telescope
(`stripLams_pstep`), the domains at the restricted index (`allM_domains_resolve`); the domains'
consts-resolve site calls `unresolved_consts_error` (`uce_errClaim_hi`). -/
theorem crule_ref (hp : CruleProg p) (hApd : ApdF p) {visT visR : Word} {feR : IFEnv}
    {envR env₂ : ConLeche.Env} (henvR : ConLeche.EnvWF envR) {a : AState} (N : Nat) (hN : N ≤ 2 ^ 62)
    {m : Mem} {cvR n gen : Word} {cv : IConstantVal}
    (hC : StageC dn visR feR envR m a) (hgen : H gen)
    (hqd : decCV (erecP m) cvR.toNat = some cv) (hqb : cvR.toNat + 3 < 2 ^ 64) (hA : AbsOK m)
    {cvRP : ConLeche.ConstantVal} {genP : ConLeche.Expr}
    (hcvP : Frontend.denoteCV a.store cv = some cvRP)
    (hgP : denoteE a.store (decI gen) = some genP)
    (hie : ConRon.Bridge.Inductives.IFEnvOKS env₂ (feR.restrictTo visT.toNat) a.store) :
    RefE (VerdictCtxU p) (cruleE p N m visT visR cvR n gen)
      (ConRon.Arena.classRuleOk .verified visT.toNat feR cv n.toNat (decI gen)) a
      (fun v y a' => CrulePost dn visR feR envR m a gen v.1 v.2 y a') := by
  cases N with
  | zero => rw [cruleE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ N =>
  rw [cruleE.arm1]
  have hR := crg_ref hp hApd N hC hgen hqd hqb hA hcvP hgP
  unfold ConRon.Arena.classRuleOk
  rw [crgT_bind]
  rcases h1 : crgE p N m visR cvR gen with e1 | ⟨r1, m1⟩
  · rw [h1] at hR
    rw [cruleE.k_class_rule_ok_guards.none]
    exact RefE.bind_left hR
  rw [h1] at hR
  obtain ⟨_, a1, hc, hC1, hg1, hA1, c14, hfvP⟩ := hR
  dsimp only at hC1 hg1 hA1
  have hws : ConLeche.Expr.WScoped 0 genP := ConLeche.Expr.WScoped.of_not_hasFvar hfvP
  rw [cruleE.k_class_rule_ok_guards.arm1]
  simp only [fail_bindAM]
  refine RefE.bind_right hc ?_
  -- the inference
  rcases h2 : callE p N "infer_type_core" [visR, 0, gen] m1 with e2 | ⟨r2, m2⟩
  · rw [cruleE.k_infer_type_core.none]
    refine RefE.bind_left fun hG => ?_
    have := hG.core.inferTypeCore N (by omega) hC1.stageT 0 gen hgen _ h2
    simpa using this
  obtain ⟨x6, a6, hi, hC2, hg2, -, hA2, c5, -⟩ := inferC_rsim hq henvR N (by omega) hC1 hA1 0 gen
    hgen (ConRon.Bridge.denote_ext hgP c14.ext) hws (r2, m2) (callW_of_callE h2)
  rw [show ((0 : Word).toNat) = 0 from rfl] at hi
  refine RefE.bind_right hi ?_
  -- the flush
  by_cases hno : ¬ FlushOK m2
  · rw [cruleE.k_infer_type_core.arm1 _ _ _ _ _ _ _ _ (by simpa using hno)]
    exact RefE.of_cls0 (by simp)
  have hok : FlushOK m2 := Classical.not_not.mp hno
  rw [cruleE.k_infer_type_core.arm2 _ _ _ _ _ _ _ _ (by simpa using hok)]
  obtain ⟨hS3, hg3⟩ := flush_stage hC2.stage hok
  obtain ⟨hok6, -, hst6⟩ := ConRon.Bridge.Inductives.ReadOK.flush (μ := V) hC2.check.toR
    (flushCaches_run a6)
  have hA3 : AbsOK (flushMem m2) := AFr.of_frame (flushMem_frame _) (by decide) (by decide) hA2
  have hx6 : Ext a6.store ({ a6 with caches := Caches.empty } : AState).store := Ext.refl _
  have hC3 := hC2.of_check hS3 hA3 hok6 hx6
  have c16 := (c14.trans c5).trans
    (⟨hok6, by rw [hst6]; exact Ext.refl _, rfl⟩ :
      ConRon.Bridge.CoreStep V envR feR a6 { a6 with caches := Caches.empty })
  refine RefE.bind_right (flushCaches_run a6) ?_
  -- the λ-telescope
  rcases h4 : stripF 5 (flushMem m2) [n, gen] with _ | ⟨r4, m4⟩
  · rw [liftE_none, cruleE.k_strip_lams.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨x7, a7, hs, hS4, hg4, hd4⟩ := stripF_lams_ok dn visR feR n gen hgen _ m4 _ r4 h4 hS3
  have hA4 : AbsOK m4 := stripF_afr h4 hA3
  obtain ⟨hs7, hq7⟩ := ConRon.Bridge.Inductives.stripLams_pstep hok6.state
    (ConRon.Bridge.denote_ext hgP c16.ext) hs
  subst hs7
  have hC4 : StageC dn visR feR envR m4 { a6 with caches := Caches.empty } :=
    hC3.of_check hS4 hA4 hok6 (Ext.refl _)
  refine RefE.bind_right hs ?_
  rcases x7 with _ | ⟨rbs, body⟩
  · rw [cruleE.k_strip_lams.abort1 _ _ _ _ _ _ _ hd4]; exact RefE.of_cls0 rfl
  obtain ⟨h41, ⟨hdl, htl⟩, -⟩ := hd4
  rw [cruleE.k_strip_lams.arm1 _ _ _ _ _ _ _ (by rw [h41]; decide)]
  simp only [getD_one, getD_two, Nat.reduceAdd] at hdl htl
  obtain ⟨rbsP, bodyP, -, hrbs, -⟩ := ConRon.Bridge.Inductives.denoteBP_some hq7
  -- the domains at the restricted index
  rcases h5 : iarW N m4 visT (r4.tail.headD 0) (r4.tail.tail.headD 0) with _ | ⟨r5, m5⟩
  · rw [liftE_none, cruleE.k_class_rule_ok_domains.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  have hb4 : (r4.tail.headD 0).toNat + (r4.tail.tail.headD 0).toNat < 2 ^ 64 := by
    have h1 : iwTop m4 ≤ (m4.arr64 IW).size := hS4.2.1
    have h2 : (m4.arr64 IW).size < 2 ^ 64 := hS4.2.2.2.1
    omega
  obtain ⟨b, a8, hdom, ⟨hS5, hg5, hb5⟩, hA5⟩ := iarW_ok dn (feR.restrictTo visT.toNat) N m4 m5 _
    visT _ _ rbs r5 h5 (hS4.restrict visT) hdl hb4 htl hA4
  have hdom' := hdom
  rw [← allM_resolve_eq] at hdom'
  have hr6 : ConRon.Bridge.Inductives.ReadOK env₂ (feR.restrictTo visT.toNat)
      { a6 with caches := Caches.empty } :=
    ⟨hok6.state, hok6.pins, (hie.mono c16.ext) _ rfl⟩
  obtain ⟨p8, -⟩ := ConRon.Bridge.Inductives.allM_domains_resolve rbs rbsP _ a8 b hr6 hrbs hdom'
  have c18 := c16.trans (p8.toCore hok6)
  have hC5 : StageC dn visR feR envR m5 a8 :=
    hC4.of_check (hS5.unrestrict hC.stage.1.env.vis) hA5 c18.ok (p8.ext)
  refine RefE.bind_right hdom' ?_
  by_cases h50 : r5.headD 0 = 0
  · rw [cruleE.k_class_rule_ok_domains.arm1 _ _ _ _ _ _ h50]
    have eb : b = false := by rw [← hb5.1]; simpa using h50
    subst eb
    refine RefE.ite_neg (by decide) ?_
    rcases h6 : callE p N "unresolved_consts_error" [visR, gen, 4] m5 with e6 | ⟨r6, m6⟩
    · rw [cruleE.k_unresolved_consts_error.eq_1]
      obtain ⟨M5, hC5'⟩ := hC5.stageT.core
      exact fun hG => uce_errClaim_hi hG.uce hG.nv hC5'.arena.1 hC5'.pins hgen (by decide) h6 _
    · rw [cruleE.k_unresolved_consts_error.abort1]; exact RefE.of_cls0 rfl
  rw [cruleE.k_class_rule_ok_domains.arm2 _ _ _ _ _ _ h50]
  have eb : b = true := by rw [← hb5.1]; simpa using h50
  subst eb
  refine RefE.ite_pos rfl (RefE.ret rfl ⟨hC5, (((hg1.trans hg2).trans hg3).trans hg4).trans hg5, rfl,
    rfl, hA5, c18⟩)

include hq in
/-- **`class_rule_ok` refines `classRuleOk`** under `StageC` (the inputs' denotations as con-ron's
`classRuleOk_spec` asks; `crule_ref`'s ok half): the rule is returned as built. -/
@[refines ConRon.Arena.classRuleOk]
theorem classRuleOk_refinesC (hp : CruleProg p) (hApd : ApdF p) (N : Nat) (hN : N ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (visT visR : Word) (feR : IFEnv) {envR env₂ : ConLeche.Env}
    (henvR : ConLeche.EnvWF envR) (cvR n gen : Word) (cv : IConstantVal)
    (hC : StageC dn visR feR envR s₀.mem a₀) (hgen : H gen)
    (hqd : decCV (erecP s₀.mem) cvR.toNat = some cv) (hqb : cvR.toNat + 3 < 2 ^ 64)
    (hA : AbsOK s₀.mem) {cvRP : ConLeche.ConstantVal} {genP : ConLeche.Expr}
    (hcvP : Frontend.denoteCV a₀.store cv = some cvRP)
    (hgP : denoteE a₀.store (decI gen) = some genP)
    (hie : ConRon.Bridge.Inductives.IFEnvOKS env₂ (feR.restrictTo visT.toNat) a₀.store) :
    ⦃fun s => s = s₀⦄ invoke p (exec p N) "class_rule_ok" [visT, visR, cvR, n, gen]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.classRuleOk .verified visT.toNat feR cv n.toNat (decI gen)) a₀ ∧
      StageC dn visR feR envR s'.mem
        (AM.st (ConRon.Arena.classRuleOk .verified visT.toNat feR cv n.toNat (decI gen)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decW0E s'.mem r (AM.res (ConRon.Arena.classRuleOk .verified visT.toNat feR cv n.toNat (decI gen)) a₀) ∧
      AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (cruleE_spec p hp N s₀ visT visR cvR n gen)
    (crule_ref hq hp hApd henvR N hN hC hgen hqd hqb hA hcvP hgP hie)) ?_
  rintro r s' ⟨hl, x, a', run, hR⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, by rw [hst]; exact hR.stage, hR.grow,
    by have hv : r.headD 0 = gen := hR.val
       rw [hres, hR.res]; exact ⟨by rw [hv]; exact hgen, by rw [hv]⟩, hR.abs⟩

end sims

l_model cr1E_spec (p : Prog) (hP : CrsProg p)
  fns [hP.one ↦ cr1E] specs [cruleE_spec p hP.cr n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

section cr1
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name}

include hq in
/-- **`class_rules_ok_one` refines `classRuleOk` at the telescope length `nP + |slots| + nF`, both
outcomes**: the word sum's overflow abort (class `0`), then `class_rule_ok` in tail position
(`crule_ref`). -/
theorem cr1_ref (hp : CruleProg p) (hApd : ApdF p) {visT visR : Word} {feR : IFEnv}
    {envR env₂ : ConLeche.Env} (henvR : ConLeche.EnvWF envR) {a : AState} (N : Nat) (hN : N ≤ 2 ^ 62)
    {m : Mem} {g cvR x gen : Word} {cv : IConstantVal} {G : ClassGen} {X : ClassCtor}
    (hC : StageC dn visR feR envR m a) (hgen : H gen) (hcv : decCVp m cvR.toNat = some cv)
    (hext : CVExt m cvR.toNat) (hG : DecB (fun m => decCG m g.toNat) m G)
    (hns : G.nP + G.slots.length < 2 ^ 64) (hX : DecB (fun m => decCC m x.toNat) m X)
    (hA : AbsOK m) {cvRP : ConLeche.ConstantVal} {genP : ConLeche.Expr}
    (hcvP : Frontend.denoteCV a.store cv = some cvRP)
    (hgP : denoteE a.store (decI gen) = some genP)
    (hie : ConRon.Bridge.Inductives.IFEnvOKS env₂ (feR.restrictTo visT.toNat) a.store) :
    RefE (VerdictCtxU p) (cr1E p N m visT visR g cvR x gen)
      (ConRon.Arena.classRuleOk V visT.toNat feR cv (G.nP + G.slots.length + X.nF) (decI gen)) a
      (fun v y a' => CrulePost dn visR feR envR m a gen v.1 v.2 y a') := by
  cases N with
  | zero => rw [cr1E.eq_1]; exact RefE.of_cls0 (by simp)
  | succ N =>
  have hsz := hC.stage.2.2.2.1
  obtain ⟨hnP, -⟩ := rec2CG_parts hG
  obtain ⟨hsl, -⟩ := rec3CG_parts hG
  obtain ⟨hnF, -, -⟩ := rec2CC_parts (hX.get (decCC_mono _))
  obtain ⟨e0, t0⟩ := rec2RdN (w := g) (k := 0) (by simpa using hnP) hsz
  obtain ⟨e8, t8⟩ := rec2RdN (w := g) (k := 8) hsl hsz
  obtain ⟨e1, t1⟩ := rec2RdN (w := x) (k := 1) hnF hsz
  simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero,
    show UInt64.ofNat 8 = (8 : Word) from rfl, show UInt64.ofNat 1 = (1 : Word) from rfl] at e0 e8 e1
  by_cases hb : rdW (m.arr64 IW) g + rdW (m.arr64 IW) (g + 8) + rdW (m.arr64 IW) (x + 1) <
      rdW (m.arr64 IW) g + rdW (m.arr64 IW) (g + 8)
  · rw [cr1E.abort1 p N m visT visR g cvR x gen hb]; exact RefE.of_cls0 rfl
  rw [cr1E.arm1 p N m visT visR g cvR x gen hb]
  have hn : (rdW (m.arr64 IW) g + rdW (m.arr64 IW) (g + 8) + rdW (m.arr64 IW) (x + 1)).toNat =
      G.nP + G.slots.length + X.nF := by
    rw [rec3Add_toNat hb, e0, e8, e1, t1]
    rw [UInt64.toNat_add, t0, t8]; exact congrArg (· + X.nF) (Nat.mod_eq_of_lt hns)
  have h := crule_ref hq hp hApd henvR N (by omega) hC hgen (rec2DecCV_erecP hcv hext)
    (rec3CVExt_lt hC.stage hext) hA hcvP hgP hie
    (n := rdW (m.arr64 IW) g + rdW (m.arr64 IW) (g + 8) + rdW (m.arr64 IW) (x + 1)) (visT := visT)
  rwa [hn] at h

end cr1

end L.Ind

end
