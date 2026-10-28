import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.IndT.WalkC
import ConRon.Bridge.Inductives.GenRec
import ConAgua.Arena.IndRealMemoCrT
import ConAgua.Arena.IndSumSpec.FieldDomsResolve
import ConAgua.Arena.RecGenSpec.CfhW
import ConAgua.Verdict.IndBCrg

/-!
# `classRuleOk` under `StageC` (lane `indstaget`)

`class_rule_ok`'s model at `realCall p`, from `StageC` and the inputs' denotations con-ron's
`classRuleOk_spec` asks; its twin side transcribed from that spec's proof: the closedness guards
(`RC.looseBVarsBoundedFast_pstep`, `RC.hasFvarFast_pstep`), the level parameters
(`allLevelParamsDefined_run`), the resolution (`constsResolveFFast_pstep`), the inference
(`inferC_rsim`), the flush (`ReadOK.flush`), the λ-telescope (`stripLams_pstep`), the domains at
the restricted index (`allM_domains_resolve`).
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name}

include hq in
/-- **`class_rule_ok` under `StageC`** (`cruleW_ok`'s, twin side con-ron's `classRuleOk_spec`). -/
theorem cruleW_okC (hp : CruleProg p) (hApd : ApdF p) {visT visR : Word} {feR : IFEnv} {envR env₂ : ConLeche.Env}
    (henvR : ConLeche.EnvWF envR) {a : AState} {N : Nat} (hN : N ≤ 2 ^ 62) {m m' : Mem}
    {cvR n gen : Word} {r : List Word} {cv : IConstantVal}
    (h : cruleW (realCall p) N m visT visR cvR n gen = some (r, m'))
    (hC : StageC dn visR feR envR m a) (hgen : H gen)
    (hqd : decCV (erecP m) cvR.toNat = some cv) (hqb : cvR.toNat + 3 < 2 ^ 64) (hA : AbsOK m)
    {cvRP : ConLeche.ConstantVal} {genP : ConLeche.Expr}
    (hcvP : Frontend.denoteCV a.store cv = some cvRP)
    (hgP : denoteE a.store (decI gen) = some genP)
    (hie : ConRon.Bridge.Inductives.IFEnvOKS env₂ (feR.restrictTo visT.toNat) a.store) :
    ∃ a', (ConRon.Arena.classRuleOk .verified visT.toNat feR cv n.toNat (decI gen)).run a =
      .ok (decI gen, a') ∧ StageC dn visR feR envR m' a' ∧ IWGrow m m' ∧ r = [gen] ∧
      AbsOK m' ∧ ConRon.Bridge.CoreStep V envR feR a a' := by
  rcases N with _ | N
  · simp [cruleW] at h
  rw [cruleW_eq] at h
  obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h rfl
  rw [cruK1_some] at h
  obtain ⟨s1, rfl, -, _, a1, hg, ⟨hC1, hg1, hA1, c14, hfvP⟩⟩ :=
    RefE.run_okW (crgE_spec p hp N ⟨m, Locals.init []⟩ visR cvR gen)
      (crg_ref hp hApd N hC hgen hqd hqb hA hcvP hgP) h1
  have hws : ConLeche.Expr.WScoped 0 genP := ConLeche.Expr.WScoped.of_not_hasFvar hfvP
  -- the inference
  obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h rfl
  obtain ⟨x6, a6, hi, hC2, hg2, -, hA2, c5, -⟩ := inferC_rsim hq henvR N (by omega) hC1 hA1 0 gen
    hgen (ConRon.Bridge.denote_ext hgP c14.ext) hws (r2, m2) h2
  rw [show ((0 : Word).toNat) = 0 from rfl] at hi
  -- the flush
  have hok : FlushOK m2 := Classical.byContradiction fun hn => by
    rw [cruK2_bad (h := hn)] at h; cases h
  rw [cruK2_some (h := hok)] at h
  obtain ⟨hS3, hg3⟩ := flush_stage hC2.stage hok
  obtain ⟨hok6, -, hst6⟩ := ConRon.Bridge.Inductives.ReadOK.flush (μ := V) hC2.check.toR
    (flushCaches_run a6)
  have hA3 : AbsOK (flushMem m2) := AFr.of_frame (flushMem_frame _) (by decide) (by decide) hA2
  have hx6 : Ext a6.store ({ a6 with caches := Caches.empty } : AState).store := Ext.refl _
  have hC3 := hC2.of_check hS3 hA3 hok6 hx6
  have c16 := (c14.trans c5).trans
    (⟨hok6, by rw [hst6]; exact Ext.refl _, rfl⟩ :
      ConRon.Bridge.CoreStep V envR feR a6 { a6 with caches := Caches.empty })
  -- the λ-telescope
  obtain ⟨⟨r4, m4⟩, h4, h⟩ := of_K h rfl
  obtain ⟨x7, a7, hs, hS4, hg4, hd4⟩ := stripF_lams_ok dn visR feR n gen hgen _ m4 _ r4 h4 hS3
  have hA4 : AbsOK m4 := stripF_afr h4 hA3
  obtain ⟨hs7, hq7⟩ := ConRon.Bridge.Inductives.stripLams_pstep hok6.state
    (ConRon.Bridge.denote_ext hgP c16.ext) hs
  subst hs7
  have hC4 : StageC dn visR feR envR m4 { a6 with caches := Caches.empty } :=
    hC3.of_check hS4 hA4 hok6 (Ext.refl _)
  rcases x7 with _ | ⟨rbs, body⟩
  · rw [cruK3_some, ite_eq_left (show r4.headD 0 = 0 from hd4)] at h; cases h
  obtain ⟨h41, ⟨hdl, htl⟩, -⟩ := hd4
  rw [cruK3_some, ite_eq_right (by rw [h41]; decide)] at h
  simp only [getD_one, getD_two, Nat.reduceAdd] at hdl htl
  obtain ⟨rbsP, bodyP, -, hrbs, -⟩ := ConRon.Bridge.Inductives.denoteBP_some hq7
  -- the domains at the restricted index
  obtain ⟨⟨r5, m5⟩, h5, h⟩ := of_K h rfl
  rw [cruK4_some] at h
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
  obtain ⟨hb, h⟩ := of_ite_none h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have eb : b = true := by rw [← hb5.1]; simpa using hb
  subst eb
  refine ⟨a8, ?_, hC4.of_check (hS5.unrestrict hC.stage.1.env.vis) hA5 c18.ok (p8.ext),
    (((hg1.trans hg2).trans hg3).trans hg4).trans hg5, rfl, hA5, c18⟩
  unfold ConRon.Arena.classRuleOk
  rw [crgT_bind]
  simp only [StateT.run_bind, hg, exc_ok_bind', hi,
    flushCaches_run, hs, hdom', Bool.false_eq_true, ite_true, ite_false]
  rfl

include hq in
/-- **`class_rule_ok` refines `classRuleOk`** under `StageC` (the inputs' denotations as con-ron's
`classRuleOk_spec` asks): the rule is returned as built. -/
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
  refine triple_post (classRuleOk_spec p hp (realCall p) (realCall_spec p) N s₀ visT visR cvR n gen) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨a', hrun, hC', hg, rfl, hA', -⟩ :=
    cruleW_okC hq hp hApd henvR hN hm hC hgen hqd hqb hA hcvP hgP hie
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hC', hg, by rw [hres]; exact ⟨hgen, rfl⟩, hA'⟩

end sims

end L.Ind
