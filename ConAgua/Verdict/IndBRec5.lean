import ConAgua.Arena.IndT.RecGen9
import ConAgua.Verdict.IndBRec4

/-!
# Error refinements of `class_rules_ok_one` and `class_rules_ok` (lane `verdicts-b`, helper `ib`)
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dClassGen dClassCtor dExt_denoteCV dClassGen_ext
  dClassCtor_ext mapM_option_cons_inv)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model cr1E_spec (p : Prog) (hf : p.lookup "class_rules_ok_one" = some classRulesOkOne)
  fns [hf ↦ cr1E] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] errors

l_model crsE_spec (p : Prog) (hf : p.lookup "class_rules_ok" = some classRulesOkL)
  fns [hf ↦ crsE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] errors

section sims
variable {p : Prog} (hq : KnotStageProg p) (hApd : ApdF p) {dn : NIdx → Option ConLeche.Name}
  {env : ConLeche.Env} (hnv : closedNV p _root_.L.Checker.nvFns = true) (hcE : CoreStubsE p) (hU : UceProg p)

include hq hApd hnv hcE hU in
/-- **`class_rules_ok_one`'s error claim** (`cr1W_relC`'s hypotheses): the rule check at the
telescope length `nP + |slots| + nF` is `class_rule_ok`'s. -/
theorem cr1_claim (hP : CrsProg p) {visT visR : Word} {feR : IFEnv} {envR env₂ : ConLeche.Env}
    (henvR : ConLeche.EnvWF envR) (N : Nat) (hN : N ≤ 2 ^ 62) (s₀ : St) (a : AState)
    {g cvR x gen : Word} {cv : IConstantVal} {G : ClassGen} {X : ClassCtor}
    (hC : StageC dn visR feR envR s₀.mem a) (hgen : H gen) (hcv : decCVp s₀.mem cvR.toNat = some cv)
    (hext : CVExt s₀.mem cvR.toNat) (hG : DecB (fun m => decCG m g.toNat) s₀.mem G)
    (hns : G.nP + G.slots.length < 2 ^ 64) (hX : DecB (fun m => decCC m x.toNat) s₀.mem X)
    (hA : AbsOK s₀.mem) {cvRP : ConLeche.ConstantVal} {genP : ConLeche.Expr}
    (hcvP : Frontend.denoteCV a.store cv = some cvRP)
    (hgP : denoteE a.store (decI gen) = some genP)
    (hie : ConRon.Bridge.Inductives.IFEnvOKS env₂ (feR.restrictTo visT.toNat) a.store) :
    CoreSpecE p N "class_rules_ok_one" [visT, visR, g, cvR, x, gen]
      (ConRon.Arena.classRuleOk V visT.toNat feR cv (G.nP + G.slots.length + X.nF) (decI gen)) s₀ a := by
  refine CoreSpecE.of_runs fun er hc' => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (cr1E_spec p hP.one N ⟨s₀.mem, Locals.init []⟩ visT visR g cvR x gen) hc'
    (Err.code_ne_of_cls hk0)
  cases N with
  | zero => rw [cr1E.eq_def] at hW; cases hW; exact absurd rfl hk0
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
  by_cases hb : rdW (s₀.mem.arr64 IW) g + rdW (s₀.mem.arr64 IW) (g + 8) + rdW (s₀.mem.arr64 IW) (x + 1) <
      rdW (s₀.mem.arr64 IW) g + rdW (s₀.mem.arr64 IW) (g + 8)
  · rw [cr1E.abort1 p N s₀.mem visT visR g cvR x gen hb] at hW
    cases hW; exact absurd rfl hk0
  rw [cr1E.arm1 p N s₀.mem visT visR g cvR x gen hb] at hW
  have hn : (rdW (s₀.mem.arr64 IW) g + rdW (s₀.mem.arr64 IW) (g + 8) + rdW (s₀.mem.arr64 IW) (x + 1)).toNat =
      G.nP + G.slots.length + X.nF := by
    rw [rec3Add_toNat hb, e0, e8, e1, t1]
    rw [UInt64.toNat_add, t0, t8]; exact congrArg (· + X.nF) (Nat.mod_eq_of_lt hns)
  cases h1 : callE p N "class_rule_ok" [visT, visR, cvR,
      rdW (s₀.mem.arr64 IW) g + rdW (s₀.mem.arr64 IW) (g + 8) + rdW (s₀.mem.arr64 IW) (x + 1), gen] s₀.mem with
  | error e1 =>
    rw [h1, cr1E.k_class_rule_ok.none] at hW
    cases hW
    have := CoreSpecE.of_callE (classRuleOk_claim hq hnv hcE hP.cr hApd hU N (by omega) ⟨s₀.mem, Locals.init []⟩ a
      visT visR feR henvR cvR _ gen cv hC hgen (rec2DecCV_erecP hcv hext) (rec3CVExt_lt hC.stage hext) hA hcvP hgP
      hie) h1
    rwa [hn] at this
  | ok q1 =>
  rw [h1, cr1E.k_class_rule_ok.arm1] at hW
  cases hW

include hq hApd hnv hcE hU in
/-- **`class_rules_ok`'s model error claim** (`crsW_simC`'s hypotheses; the recursion is the model's
own): the rule `class_gen_rule` omits is the twin's `classGenRule = none` reject, the checks are
`class_rule_ok`'s. -/
theorem crsE_claim (hP : CrsProg p) (henv : ConLeche.EnvWF env) (visT visR : Word) (feR : IFEnv)
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
    ∀ e, crsE p n m visT visR g rco rcl cgo cgl cvR c xo xl = .error e →
      ErrClaim (ConRon.Arena.classRulesOk V visT.toNat feR G recCls cvGs cv c.toNat Xs) a e := by
  induction n with
  | zero =>
    intro m a xo xl Xs XsP hC hG hrc hcg hcv hext hXs hA hgP hcvsP hcvP hXsP hie e he
    rw [crsE.eq_def] at he
    cases he
    exact ErrClaim.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a xo xl Xs XsP hC hG hrc hcg hcv hext hXs hA hgP hcvsP hcvP hXsP hie e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hS := hC.stage
  have hsz := hS.2.2.2.1
  by_cases hxl : xl = 0
  · rw [crsE.arm1 p n m visT visR g rco rcl cgo cgl cvR c xo xl hxl] at he
    cases he
  rw [crsE.arm2 p n m visT visR g rco rcl cgo cgl cvR c xo xl hxl] at he
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
  rw [ex] at he
  have hX' : DecB (fun m => decCC m (UInt64.ofNat px : Word).toNat) m X := by rw [tx]; exact hX
  unfold ConRon.Arena.classRulesOk
  obtain ⟨-, hlps, -⟩ := ConRon.Bridge.Core.denoteCV_inv hcvP
  -- `cv_lps`
  cases h1 : callE p n "cv_lps" [cvR] m with
  | error e1 =>
    rw [h1, crsE.k_cv_lps.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, crsE.k_cv_lps.arm1] at he
  obtain ⟨s1, hs1, -, h1m⟩ := triple_of_callW (L.Arena.cvLps_specW p hP.cr.alloc hP.cr.copy hP.cr.eti hP.cr.lps n
    ⟨m, Locals.init []⟩ cvR) (callW_of_callE h1)
  subst hs1
  obtain ⟨hS1, hg1, hd1, ht1⟩ := cvLpsA_stage h1m.1 hS hcv (rec3CVExt_lt hS hext)
  have hA1 := cvLpsA_afr h1m.1 hA
  have hC1 : StageC dn visR feR env s1.mem a := hC.of_check hS1 hA1 hC.check (Ext.refl _)
  -- `param_levels`
  cases h2 : callE p n "param_levels" [r1.headD 0, r1.tail.headD 0] s1.mem with
  | error e2 =>
    rw [h2, crsE.k_param_levels.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, crsE.k_param_levels.arm1] at he
  obtain ⟨s2, hs2, -, h2m⟩ := triple_of_callW (plW_spec p hP.alloc hP.copy hP.cons hP.slGet hP.paramFind hP.paramPush
    hP.internParam hP.plGo hP.pl hP.il n ⟨s1.mem, Locals.init []⟩ (r1.headD 0) (r1.tail.headD 0)) (callW_of_callE h2)
  subst hs2
  obtain ⟨rl, a2, hrl2, hC2, ⟨⟨hrlH, hrl, hS2, hg2⟩, hf2⟩, hRl, p1⟩ :=
    (RSim.liftP hC1 (RSim.withF (rec3Sim_rsim (plW_sim (k := n) hS1 hd1 ht1)) (fun _ hb => plW_afr hb))
      (fun _ _ _ h => ⟨h.1.2.2.1, h.2 hA1⟩)
      (ConRon.Bridge.Inductives.paramLevels_spec cv.levelParams _) hlps) (r2, s2.mem) h2m
  dsimp only at hrlH hrl hS2 hg2 hC2
  subst hrl
  refine ErrClaim.bind_right hrl2 ?_
  have hg02 : IWGrow m s2.mem := hg1.trans hg2
  have hA2 := hf2 hA1
  -- `class_gen_rule`
  cases h3 : callE p n "class_gen_rule" [g, rco, rcl, cgo, cgl, r2.headD 0, c, UInt64.ofNat px] s2.mem with
  | error e3 =>
    rw [h3, crsE.k_class_gen_rule.none] at he
    cases he
    exact ErrClaim.bind_left (ErrClaim.of_callE_nv hnv (by decide +kernel) h3)
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  obtain ⟨s3, hs3, -, h3m⟩ := triple_of_callW (classGenRule_spec p hP.ru n ⟨s2.mem, Locals.init []⟩ g rco rcl cgo
    cgl (r2.headD 0) c (UInt64.ofNat px)) (callW_of_callE h3)
  subst hs3
  obtain ⟨o3, a3, hr3, hC3, ⟨⟨hS3, hg3, ho3⟩, hA3⟩, hR3, p2⟩ :=
    (RSim.liftPP hC2 (ruW_sim dn visR feR n s2.mem a2 g rco rcl cgo cgl (r2.headD 0) c (UInt64.ofNat px)
      G X recCls cvGs hS2 (hG.grow (decCG_mono _) hg02) hns (hX'.grow (decCC_mono _) hg02) hrlH
      (hrc.grow (OMono.decNL _ _) hg02) hrcb
      (hcg.grow (OMono.decPL (fun q => OMono.decCVp q) _ _) hg02) hcgb hA2)
      (fun _ _ _ h => ⟨h.1.1, h.2⟩)
      (ConRon.Bridge.Inductives.classGenRule_spec G gP recCls cvGs cvGsP (decI (r2.headD 0)) _
        c.toNat X XP)
      ⟨dClassGen_ext p1.ext _ _ hgP, dClassCtor_ext p1.ext _ _ hXP,
        dExt_denoteCV.list p1.ext _ _ hcvsP, hRl⟩) (r3, s3.mem) h3m
  dsimp only at hS3 hg3 ho3 hC3
  refine ErrClaim.bind_right hr3 ?_
  by_cases h30 : r3.headD 0 = 0
  · rw [h3, crsE.k_class_gen_rule.abort1 p n visT visR g rco rcl cgo cgl cvR c xo xl _ r3 s3.mem h30] at he
    cases he
    cases o3 with
    | none => exact ErrClaim.fail _ _ (by decide)
    | some gen => exact absurd (by simpa using ho3.1 : r3.headD 0 = 1) (by rw [h30]; decide)
  rw [h3, crsE.k_class_gen_rule.arm1 p n visT visR g rco rcl cgo cgl cvR c xo xl _ r3 s3.mem h30] at he
  cases o3 with
  | none => exact absurd ho3 h30
  | some gen =>
  obtain ⟨genP, -, hgenP⟩ := hR3
  obtain ⟨h31, hgH, hgd⟩ := ho3
  subst hgd
  have hg03 : IWGrow m s3.mem := hg02.trans hg3
  have p12 := p1.trans p2
  -- `class_rules_ok_one`
  cases h4 : callE p n "class_rules_ok_one" [visT, visR, g, cvR, UInt64.ofNat px, r3.tail.headD 0] s3.mem with
  | error e4 =>
    rw [h4, crsE.k_class_rules_ok_one.none] at he
    cases he
    refine ErrClaim.bind_left ?_
    exact CoreSpecE.of_callE (cr1_claim hq hApd hnv hcE hU hP henv n (by omega) ⟨s3.mem, Locals.init []⟩ a3
      hC3 hgH (by rw [decCVp_grow_r hg03 hext]; exact hcv) (CVExt_grow hg03 hext)
      (hG.grow (decCG_mono _) hg03) hns (hX'.grow (decCC_mono _) hg03) hA3
      (dExt_denoteCV p12.ext _ _ hcvP) hgenP (hie.mono p12.ext)) h4
  | ok q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [h4, crsE.k_class_rules_ok_one.arm1] at he
  obtain ⟨s4, hs4, -, h4m⟩ := triple_of_callW (classRulesOkOne_spec p hP (realCall p) (realCall_spec p) n
    ⟨s3.mem, Locals.init []⟩ visT visR g cvR (UInt64.ofNat px) (r3.tail.headD 0)) (callW_of_callE h4)
  subst hs4
  obtain ⟨a', hrun, hC', hg, hr, hA4, hc4⟩ := cr1W_relC hq hApd henv (by omega) h4m hC3 hgH
    (by rw [decCVp_grow_r hg03 hext]; exact hcv) (CVExt_grow hg03 hext)
    (hG.grow (decCG_mono _) hg03) hns (hX'.grow (decCC_mono _) hg03) hA3
    (dExt_denoteCV p12.ext _ _ hcvP) hgenP (hie.mono p12.ext)
  show ErrClaim (do
      let r ← ConRon.Arena.classRuleOk V visT.toNat feR cv (G.nP + G.slots.length + X.nF) (decI (r3.tail.headD 0))
      let rs ← ConRon.Arena.classRulesOk V visT.toNat feR G recCls cvGs cv c.toNat Xs'
      pure (r :: rs)) a3 e
  refine ErrClaim.bind_right hrun ?_
  subst hr
  have hg04 : IWGrow m s4.mem := hg03.trans hg
  have c14 := ((p12.toCore hC.check)).trans hc4
  have hxo1 := rec2ToNat_succ (o := xo) (i := xo.toNat) (Nat.le_refl _) (by omega)
  have hxl1 := rec2ToNat_pred hxl
  cases h5 : crsE p n s4.mem visT visR g rco rcl cgo cgl cvR c (xo + 1) (xl - 1) with
  | error e5 =>
    rw [h5, crsE.k_class_rules_ok.none] at he
    cases he
    refine ErrClaim.bind_left ?_
    exact ih (by omega) s4.mem a' (xo + 1) (xl - 1) Xs' XsP' hC' (hG.grow (decCG_mono _) hg04)
      (hrc.grow (OMono.decNL _ _) hg04)
      (hcg.grow (OMono.decPL (fun q => OMono.decCVp q) _ _) hg04)
      (by rw [decCVp_grow_r hg04 hext]; exact hcv) (CVExt_grow hg04 hext)
      (by rw [hxo1, hxl1, hjx]; exact (show DecB (fun m => decPL m (decCC m) (xo.toNat + 1) jx) m Xs' from
        hXsT).grow (OMono.decPL (fun q => decCC_mono q) _ _) hg04) hA4
      (dClassGen_ext c14.ext _ _ hgP) (dExt_denoteCV.list c14.ext _ _ hcvsP)
      (dExt_denoteCV c14.ext _ _ hcvP) (dClassCtor_ext.list c14.ext _ _ hXsP') (hie.mono c14.ext) _ h5
  | ok q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [h5, crsE.k_class_rules_ok.arm1] at he
  cases h6 : callE p n "sl_cons" [[r3.tail.headD 0].headD 0, r5.headD 0, r5.tail.headD 0] m5 with
  | error e6 =>
    rw [h6, crsE.k_sl_cons.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h6
  | ok q6 =>
  rw [h6, crsE.k_sl_cons.arm1] at he
  cases he

include hq hApd hnv hcE hU in
/-- **`class_rules_ok`'s error claim** (the hypotheses of `classRulesOk_refinesC`): a failing call of
class `1`/`2` claims that the twin's `classRulesOk` fails. -/
theorem classRulesOk_claim (hP : CrsProg p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
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
    CoreSpecE p n "class_rules_ok" [visT, visR, g, rco, rcl, cgo, cgl, cvR, c, xo, xl]
      (ConRon.Arena.classRulesOk V visT.toNat feR G recCls cvGs cv c.toNat Xs) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc' => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (crsE_spec p hP.crs n ⟨s₀.mem, Locals.init []⟩ visT visR g rco rcl cgo cgl cvR
    c xo xl) hc' (Err.code_ne_of_cls hk0)
  exact crsE_claim hq hApd hnv hcE hU hP henv visT visR feR g rco rcl cgo cgl cvR c G recCls cvGs cv hns hrcb hcgb
    gP cvGsP cvRP n hn s₀.mem a₀ xo xl Xs XsP hC hG hrc hcg hcv hext hXs hA hgP hcvsP hcvP hXsP hie er hW

end sims

end L.Ind
