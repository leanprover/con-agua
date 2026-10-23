import ConAgua.Arena.RecGenSpec4
import ConAgua.Arena.IndT.Lift
import ConRon.Bridge.Inductives.GenRec

/-!
# `classRuleOk` under `StageC` (lane `indstaget`)

`class_rule_ok`'s model at `realCall p`, from `StageC` and the inputs' denotations con-ron's
`classRuleOk_spec` asks; its twin side transcribed from that spec's proof: the closedness guards
(`RC.looseBVarsBoundedFast_pstep`, `RC.hasFvarFast_pstep`), the level parameters
(`allLevelParamsDefined_run`), the resolution (`constsResolveFFast_pstep`), the inference
(`inferC_rsim`), the flush (`ReadOK.flush`), the λ-telescope (`stripLams_pstep`), the domains at
the restricted index (`allM_domains_resolve`).
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

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
theorem cruleW_okC {visT visR : Word} {feR : IFEnv} {envR env₂ : ConLeche.Env}
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
  cases N with
  | zero => simp [cruleW] at h
  | succ N =>
  rw [cruleW_eq] at h
  cases h1 : crgW N m visR cvR gen with
  | none => rw [h1] at h; simp [cruK1] at h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, cruK1_some] at h
  obtain ⟨a1, a2, a4, a5, hl, hf, ha, hc, hS1, hg1, hA1⟩ := crgW_ok h1 hC.stage hgen hqd hqb hA
  -- the twin's guards (con-ron's chain)
  obtain ⟨-, hlps, -⟩ := ConRon.Bridge.Core.denoteCV_inv hcvP
  obtain ⟨p1, -⟩ := ConRon.Bridge.Inductives.RC.looseBVarsBoundedFast_pstep hC.check.state hgP hl
  obtain ⟨p2, hfv⟩ := ConRon.Bridge.Inductives.RC.hasFvarFast_pstep p1.ok
    (ConRon.Bridge.denote_ext hgP p1.ext) hf
  have p12 := p1.trans p2
  obtain ⟨h3st, h3c, h3p, -⟩ := ConRon.Bridge.allLevelParamsDefined_run p2.ok
    (ConRon.Bridge.denoteNList_ext p12.ext.lss.ls.ns _ _ hlps)
    (ConRon.Bridge.denote_ext hgP p12.ext) ha
  have p3 : ConRon.Bridge.Inductives.PStep a2 a4 :=
    ConRon.Bridge.Inductives.PStep.of_caches ⟨by rw [h3st]; exact p2.ok.wf⟩
      (by rw [h3st]; exact Ext.refl _) h3c h3p
  have c13 := (p12.trans p3).toCore hC.check
  obtain ⟨p4, -⟩ := ConRon.Bridge.Inductives.constsResolveFFast_pstep c13.ok.toR
    (ConRon.Bridge.denote_ext hgP c13.ext) hc
  have c14 := c13.trans (p4.toCore c13.ok)
  have hC1 : StageC dn visR feR envR m1 a5 := hC.of_check hS1 hA1 c14.ok c14.ext
  have hfvP : genP.hasFvar = false := by rw [← hfv]
  have hws : ConLeche.Expr.WScoped 0 genP := ConLeche.Expr.WScoped.of_not_hasFvar hfvP
  -- the inference
  cases h2 : realCall p N "infer_type_core" [visR, 0, gen] m1 with
  | none => rw [h2] at h; simp [cruK2] at h
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2] at h
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
  cases h4 : stripF 5 (flushMem m2) [n, gen] with
  | none => rw [h4] at h; simp [cruK3] at h
  | some rm4 =>
  obtain ⟨r4, m4⟩ := rm4
  rw [h4] at h
  obtain ⟨x7, a7, hs, hS4, hg4, hd4⟩ := stripF_lams_ok dn visR feR n gen hgen _ m4 _ r4 h4 hS3
  have hA4 : AbsOK m4 := stripF_afr h4 hA3
  obtain ⟨hs7, hq7⟩ := ConRon.Bridge.Inductives.stripLams_pstep hok6.state
    (ConRon.Bridge.denote_ext hgP c16.ext) hs
  subst hs7
  have hC4 : StageC dn visR feR envR m4 { a6 with caches := Caches.empty } :=
    hC3.of_check hS4 hA4 hok6 (Ext.refl _)
  cases x7 with
  | none =>
    have h0 : r4.headD 0 = 0 := hd4
    rw [cruK3_some, if_pos h0] at h; cases h
  | some rb =>
  obtain ⟨rbs, body⟩ := rb
  obtain ⟨h41, ⟨hdl, htl⟩, -⟩ := hd4
  rw [cruK3_some, if_neg (by rw [h41]; decide)] at h
  simp only [getD_one, getD_two, Nat.reduceAdd] at hdl htl
  obtain ⟨rbsP, bodyP, -, hrbs, -⟩ := ConRon.Bridge.Inductives.denoteBP_some hq7
  -- the domains at the restricted index
  cases h5 : iarW N m4 visT (r4.tail.headD 0) (r4.tail.tail.headD 0) with
  | none => rw [h5] at h; simp [cruK4] at h
  | some rm5 =>
  obtain ⟨r5, m5⟩ := rm5
  rw [h5, cruK4_some] at h
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
  by_cases hb : r5.headD 0 = 0
  · rw [if_pos hb] at h; cases h
  rw [if_neg hb] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have eb : b = true := by rw [← hb5.1]; simpa using hb
  subst eb
  refine ⟨a8, ?_, hC4.of_check (hS5.unrestrict hC.stage.1.env.vis) hA5 c18.ok (p8.ext),
    (((hg1.trans hg2).trans hg3).trans hg4).trans hg5, rfl, hA5, c18⟩
  simp only [ConRon.Arena.classRuleOk, StateT.run_bind, hl, exc_ok_bind', hf, ha, hc, hi,
    flushCaches_run, hs, hdom', if_true, if_false, Bool.false_eq_true, ite_true, ite_false,
    Bool.not_true, Bool.not_false]
  rfl

include hq in
/-- **`class_rule_ok` refines `classRuleOk`** under `StageC` (the inputs' denotations as con-ron's
`classRuleOk_spec` asks): the rule is returned as built. -/
@[refines ConRon.Arena.classRuleOk]
theorem classRuleOk_refinesC (hp : CruleProg p) (N : Nat) (hN : N ≤ 2 ^ 62) (s₀ : St)
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
    cruleW_okC hq henvR hN hm hC hgen hqd hqb hA hcvP hgP hie
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hC', hg, by rw [hres]; exact ⟨hgen, rfl⟩, hA'⟩

end sims

end L.Ind
