import ConAgua.Arena.IndT.RecGen10
import ConAgua.Verdict.IndBRec5

/-!
# Error refinements of `class_recs_rules_ok_go`, `class_recs_rules_ok` (lane `verdicts-b`, helper `ib`)
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dClassGen dClassCtor dExt_denoteCV dClassGen_ext
  dClassCtor_ext dMajor_ext mapM_option_cons_inv dClassGen_inv)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model crrE_spec (p : Prog) (hf : p.lookup "class_recs_rules_ok_go" = some classRecsRulesOkGo)
  fns [hf ↦ crrE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] errors

l_model crraE_spec (p : Prog) (hf : p.lookup "class_recs_rules_ok" = some classRecsRulesOkL)
  fns [hf ↦ crraE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] errors

section sims
variable {p : Prog} (hq : KnotStageProg p) (hApd : ApdF p) {dn : NIdx → Option ConLeche.Name}
  {env : ConLeche.Env} (hnv : closedNV p _root_.L.Checker.nvFns = true) (hcE : CoreStubsE p) (hU : UceProg p)

include hq hApd hnv hcE hU in
/-- **`class_recs_rules_ok_go`'s model error claim** (`crrW_simC`'s hypotheses; the recursion is the
model's own). -/
theorem crrE_claim (hP : CrrProg p) (henv : ConLeche.EnvWF env) (visT visR : Word) (feR : IFEnv)
    {env₂ : ConLeche.Env} (g rco rcl cgo cgl : Word) (G : ClassGen) (recCls : List Nat)
    (cvGs : List IConstantVal) (hns : G.nP + G.slots.length < 2 ^ 64)
    (hrcb : rco.toNat + rcl.toNat < 2 ^ 64) (hcgb : cgo.toNat + cgl.toNat < 2 ^ 64)
    (gP : ConLeche.ClassGen) (cvGsP : List ConLeche.ConstantVal) (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (vo vl co cl : Word) (cvs : List IConstantVal) (cs : List Nat)
      (cvsP : List ConLeche.ConstantVal),
    StageC dn visR feR env m a → DecB (fun m => decCG m g.toNat) m G →
    DecB (fun m => decNL m rco.toNat rcl.toNat) m recCls → SPL decCVX m cgo.toNat cgl.toNat cvGs →
    SPL decCVX m vo.toNat vl.toNat cvs → DecB (fun m => decNL m co.toNat cl.toNat) m cs → AbsOK m →
    dClassGen a.store G = some gP → cvGs.mapM (Frontend.denoteCV a.store) = some cvGsP →
    cvs.mapM (Frontend.denoteCV a.store) = some cvsP →
    ConRon.Bridge.Inductives.IFEnvOKS env₂ (feR.restrictTo visT.toNat) a.store →
    ∀ e, crrE p n m visT visR g rco rcl cgo cgl vo vl co cl = .error e →
      ErrClaim (ConRon.Arena.classRecsRulesOk V visT.toNat feR G recCls cvGs cvs cs) a e := by
  induction n with
  | zero =>
    intro m a vo vl co cl cvs cs cvsP hC hG hrc hcg hcvs hcs hA hgP hcvGsP hcvsP hie e he
    rw [crrE.eq_def] at he
    cases he
    exact ErrClaim.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a vo vl co cl cvs cs cvsP hC hG hrc hcg hcvs hcs hA hgP hcvGsP hcvsP hie e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hS := hC.stage
  have hsz := hS.2.2.2.1
  by_cases hvl : vl = 0
  · rw [crrE.arm1 p n m visT visR g rco rcl cgo cgl vo vl co cl hvl] at he
    cases he
  obtain ⟨jv, hjv⟩ : ∃ j, vl.toNat = j + 1 :=
    ⟨vl.toNat - 1, by
      have : vl.toNat ≠ 0 := fun e => hvl (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  obtain ⟨pp, cv, cvs', rfl, hp, hpt, hcv, hcvsT⟩ := rec3SPL_uncons (by rw [← hjv]; exact hcvs)
  obtain ⟨cvP, cvsP', rfl, hcvP, hcvsP'⟩ := mapM_option_cons_inv hcvsP
  by_cases hcl : cl = 0
  · rw [crrE.arm2 p n m visT visR g rco rcl cgo cgl vo vl co cl hvl hcl] at he
    cases he
  obtain ⟨jc, hjc⟩ : ∃ j, cl.toNat = j + 1 :=
    ⟨cl.toNat - 1, by
      have : cl.toNat ≠ 0 := fun e => hcl (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  have hcs' : decNL (truncM m) co.toNat (jc + 1) = some cs := by rw [← hjc]; exact hcs
  rw [decNL_succ] at hcs'
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hcs'
  obtain ⟨c0, hc0, cs', hcsT, rfl⟩ := hcs'
  obtain ⟨-, hc0m⟩ := rec2IwN_trunc hc0
  obtain ⟨ep, tp⟩ := rec2RdN (w := vo) (k := 0) (by simpa using hp) hsz
  obtain ⟨ec, tc⟩ := rec2RdN (w := co) (k := 0) (by simpa using hc0m) hsz
  simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero] at ep ec
  -- the model's constructor slice is `crrXs`
  have hj1 : crrE p (n + 1) m visT visR g rco rcl cgo cgl vo vl co cl =
        crrE.k_class_rules_ok p n visT visR g rco rcl cgo cgl vo vl co cl (UInt64.ofNat pp)
          (UInt64.ofNat c0)
          (callE p n "class_rules_ok" [visT, visR, g, rco, rcl, cgo, cgl, UInt64.ofNat pp,
            UInt64.ofNat c0, (crrXs m g (UInt64.ofNat c0)).1, (crrXs m g (UInt64.ofNat c0)).2] m) := by
    by_cases hc : rdW (m.arr64 IW) co < rdW (m.arr64 IW) (g + 10)
    · rw [crrE.arm3 p n m visT visR g rco rcl cgo cgl vo vl co cl hvl hcl hc, crrE.j1.arm1, ep, ec]
      rw [ec] at hc
      rw [crrXs_hit (h := hc)]
    · rw [crrE.arm4 p n m visT visR g rco rcl cgo cgl vo vl co cl hvl hcl hc, crrE.j1.arm1, ep, ec]
      rw [ec] at hc
      rw [crrXs_miss (h := hc)]
  rw [hj1] at he
  obtain ⟨hcvp, hcvx⟩ := rec3CVX hcv
  unfold ConRon.Arena.classRecsRulesOk
  dsimp only
  have hxs := rec3CtorsAt (c := UInt64.ofNat c0) hS hG
  rw [tc] at hxs
  -- `class_rules_ok`
  cases h1 : callE p n "class_rules_ok" [visT, visR, g, rco, rcl, cgo, cgl, UInt64.ofNat pp, UInt64.ofNat c0,
      (crrXs m g (UInt64.ofNat c0)).1, (crrXs m g (UInt64.ofNat c0)).2] m with
  | error e1 =>
    rw [h1, crrE.k_class_rules_ok.none] at he
    cases he
    refine ErrClaim.bind_left ?_
    have := CoreSpecE.of_callE (classRulesOk_claim hq hApd hnv hcE hU hP.crs n (by omega) ⟨m, Locals.init []⟩ a
      henv visT visR feR g rco rcl cgo cgl (UInt64.ofNat pp) (UInt64.ofNat c0) _ _ G recCls cvGs cv
      (G.ctors.getD c0 []) hC hG hns hrc hrcb (rec3SPL_decB hcg) hcgb (by rw [tp]; exact hcvp)
      (by rw [tp]; exact hcvx) hxs hA hgP hcvGsP hcvP (ctorsAt_denote hgP c0) hie) h1
    rwa [tc] at this
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, crrE.k_class_rules_ok.arm1] at he
  obtain ⟨s1, hs1, -, h1m⟩ := triple_of_callW (classRulesOk_spec p hP.crs (realCall p) (realCall_spec p) n
    ⟨m, Locals.init []⟩ visT visR g rco rcl cgo cgl (UInt64.ofNat pp) (UInt64.ofNat c0)
    (crrXs m g (UInt64.ofNat c0)).1 (crrXs m g (UInt64.ofNat c0)).2) (callW_of_callE h1)
  subst hs1
  have hcsim := crsW_simC hq hApd henv visT visR feR (env₂ := env₂) g rco rcl cgo cgl (UInt64.ofNat pp)
    (UInt64.ofNat c0) G recCls cvGs cv hns hrcb hcgb gP cvGsP cvP n (by omega) m a _ _ _
    (gP.ctors.getD c0 []) hC hG hrc (rec3SPL_decB hcg) (by rw [tp]; exact hcvp)
    (by rw [tp]; exact hcvx) hxs hA hgP hcvGsP hcvP (ctorsAt_denote hgP c0) hie
  rw [tc] at hcsim
  obtain ⟨rhss, a1, hrun1, ⟨hC1, hg1, hr1⟩, hA1, c1⟩ := hcsim (r1, s1.mem) h1m
  dsimp only at hC1 hg1 hr1 hA1
  refine ErrClaim.bind_right hrun1 ?_
  -- `target_major_at`
  have hS1 := hC1.stage
  have hG1 := hG.grow (decCG_mono _) hg1
  have hsz1 := hS1.2.2.2.1
  obtain ⟨-, -, ⟨o3, l3, h3, h4, hcls⟩, -⟩ := rec2CG_parts hG1
  obtain ⟨e3, t3⟩ := rec2RdN (w := g) (k := 3) h3 hsz1
  obtain ⟨e4, t4⟩ := rec2RdN (w := g) (k := 4) h4 hsz1
  simp only [show UInt64.ofNat 3 = (3 : Word) from rfl, show UInt64.ofNat 4 = (4 : Word) from rfl] at e3 e4
  have hb3 : o3 + l3 < 2 ^ 64 := by
    by_cases hl : l3 = 0
    · have := iwN_rdW h3 (by have := hS1.2.1; have := (rec2CG_parts hG1).2.1; omega); omega
    · have := rec2DecB_PL_top hcls hl; have := hS1.2.1; omega
  cases h2 : callE p n "target_major_at" [rdW (s1.mem.arr64 IW) (g + 3), rdW (s1.mem.arr64 IW) (g + 4),
      UInt64.ofNat c0] s1.mem with
  | error e2 =>
    rw [h2, crrE.k_target_major_at.none] at he
    cases he
    exact ErrClaim.bind_left (ErrClaim.of_callE_nv hnv (by decide +kernel) h2)
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, crrE.k_target_major_at.arm1] at he
  obtain ⟨s2, hs2, -, h2m⟩ := triple_of_callW (targetMajorAt_spec p hP.crs.alloc hP.pw hP.mtm hP.tmd hP.tma hP.na n
    ⟨s1.mem, Locals.init []⟩ (rdW (s1.mem.arr64 IW) (g + 3)) (rdW (s1.mem.arr64 IW) (g + 4)) (UInt64.ofNat c0))
    (callW_of_callE h2)
  subst hs2
  have hM := rec3TMA_sim dn visR feR n s1.mem a1 (UInt64.ofNat o3) (UInt64.ofNat l3) (UInt64.ofNat c0)
    G.cls hS1 (by rw [t3, t4]; exact hcls) (by rw [t3, t4]; exact hb3)
  rw [tc] at hM
  rw [e3, e4] at h2m
  obtain ⟨-, -, hclsP, -, -, -, -, -⟩ := dClassGen_inv hgP
  obtain ⟨M, a2, hrun2, hC2, ⟨⟨hS2, hg2, hMd⟩, hf2⟩, -, p2⟩ :=
    (RSim.liftPP hC1 (RSim.withF hM (fun _ hb => tmaW_afr hb)) (fun _ _ _ h => ⟨h.1.1, h.2 hA1⟩)
      (ConRon.Bridge.Inductives.targetMajorAt_spec G.cls gP.cls c0)
      (dMajor_ext.list c1.ext _ _ hclsP)) (r2, s2.mem) h2m
  dsimp only at hS2 hg2 hMd hC2
  have c12 := c1.trans (p2.toCore c1.ok)
  refine ErrClaim.bind_right hrun2 ?_
  -- `rec4`
  cases h3' : callE p n "rec4" [UInt64.ofNat pp, r2.headD 0, r1.headD 0, r1.tail.headD 0] s2.mem with
  | error e3' =>
    rw [h3', crrE.k_rec4.none] at he
    cases he
    exact ErrClaim.bind_left (ErrClaim.of_callE_nv hnv (by decide +kernel) h3')
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3', crrE.k_rec4.arm1] at he
  obtain ⟨s3, hs3, -, h3m⟩ := triple_of_callW (rec4_specW p hP.crs.alloc n hP.rec4 ⟨s2.mem, Locals.init []⟩
    (UInt64.ofNat pp) (r2.headD 0) (r1.headD 0) (r1.tail.headD 0)) (callW_of_callE h3')
  subst hs3
  obtain ⟨hS3, hg3, hr3, hget3, htop3⟩ := recW_stage h3m hS2 rfl
  have hA3 := recW_afr h3m (hf2 hA1)
  have hC3 : StageC dn visR feR env s3.mem a2 := hC2.of_check hS3 hA3 hC2.check (Ext.refl _)
  have hg13 := hg2.trans hg3
  have hg03 : IWGrow m s3.mem := hg1.trans hg13
  have hvo1 := rec2ToNat_succ (o := vo) (i := vo.toNat) (Nat.le_refl _) (by have := hS.2.1; omega)
  have hco1 := rec2ToNat_succ (o := co) (i := co.toNat) (Nat.le_refl _)
    (by have := hS.2.1; have := (rec2IwN_trunc hc0).1; omega)
  have hvl1 := rec2ToNat_pred hvl
  have hcl1 := rec2ToNat_pred hcl
  refine ErrClaim.bind_left ?_
  cases h4 : crrE p n s3.mem visT visR g rco rcl cgo cgl (vo + 1) (vl - 1) (co + 1) (cl - 1) with
  | error e4 =>
    rw [h4, crrE.k_class_recs_rules_ok_go.none] at he
    cases he
    exact ih (by omega) s3.mem a2 (vo + 1) (vl - 1) (co + 1) (cl - 1) cvs' cs' cvsP' hC3
      (hG.grow (decCG_mono _) hg03) (hrc.grow (OMono.decNL _ _) hg03) (hcg.grow hg03)
      (by rw [hvo1, hvl1, hjv]; exact hcvsT.grow hg03)
      (by rw [hco1, hcl1, hjc]; exact (show DecB (fun m => decNL m (co.toNat + 1) jc) m cs' from
        hcsT).grow (OMono.decNL _ _) hg03) hA3
      (dClassGen_ext c12.ext _ _ hgP) (dExt_denoteCV.list c12.ext _ _ hcvGsP)
      (dExt_denoteCV.list c12.ext _ _ hcvsP') (hie.mono c12.ext) _ h4
  | ok q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [h4, crrE.k_class_recs_rules_ok_go.arm1] at he
  cases h5 : callE p n "sl_cons" [r3.headD 0, r4.headD 0, r4.tail.headD 0] m4 with
  | error e5 =>
    rw [h5, crrE.k_sl_cons.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h5
  | ok q5 =>
  rw [h5, crrE.k_sl_cons.arm1] at he
  cases he

include hq hApd hnv hcE hU in
/-- **`class_recs_rules_ok`'s error claim** (the hypotheses of `classRecsRulesOk_refinesC`): a
failing call of class `1`/`2` claims that the twin's `classRecsRulesOk` fails. -/
theorem classRecsRulesOk_claim (hP : CrrProg p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (henv : ConLeche.EnvWF env) (visT visR : Word) (feR : IFEnv) {env₂ : ConLeche.Env}
    (g rco rcl cgo cgl : Word) (G : ClassGen) (recCls : List Nat) (cvGs : List IConstantVal)
    (hC : StageC dn visR feR env s₀.mem a₀) (hG : DecB (fun m => decCG m g.toNat) s₀.mem G)
    (hns : G.nP + G.slots.length < 2 ^ 64)
    (hrc : DecB (fun m => decNL m rco.toNat rcl.toNat) s₀.mem recCls)
    (hrcb : rco.toNat + rcl.toNat < 2 ^ 64)
    (hcg : SPL decCVX s₀.mem cgo.toNat cgl.toNat cvGs) (hcgb : cgo.toNat + cgl.toNat < 2 ^ 64)
    (hA : AbsOK s₀.mem) {gP : ConLeche.ClassGen} {cvGsP : List ConLeche.ConstantVal}
    (hgP : dClassGen a₀.store G = some gP) (hcvGsP : cvGs.mapM (Frontend.denoteCV a₀.store) = some cvGsP)
    (hie : ConRon.Bridge.Inductives.IFEnvOKS env₂ (feR.restrictTo visT.toNat) a₀.store) :
    CoreSpecE p n "class_recs_rules_ok" [visT, visR, g, rco, rcl, cgo, cgl]
      (ConRon.Arena.classRecsRulesOk V visT.toNat feR G recCls cvGs cvGs recCls) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc' => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (crraE_spec p hP.top n ⟨s₀.mem, Locals.init []⟩ visT visR g rco rcl cgo cgl) hc'
    (Err.code_ne_of_cls hk0)
  cases n with
  | zero => rw [crraE.eq_def] at hW; cases hW; exact absurd rfl hk0
  | succ n =>
  rw [crraE.arm1] at hW
  cases h1 : callE p n "class_recs_rules_ok_go" [visT, visR, g, rco, rcl, cgo, cgl, cgo, cgl, rco, rcl] s₀.mem with
  | error e1 =>
    rw [h1, crraE.k_class_recs_rules_ok_go.none] at hW
    cases hW
    exact crrE_claim hq hApd hnv hcE hU hP henv visT visR feR g rco rcl cgo cgl G recCls cvGs hns hrcb hcgb gP
      cvGsP n (by omega) s₀.mem a₀ cgo cgl rco rcl cvGs recCls cvGsP hC hG hrc hcg hcg hrc hA hgP hcvGsP hcvGsP
      hie _ (triple_of_callE_err (crrE_spec p hP.go n ⟨s₀.mem, Locals.init []⟩ visT visR g rco rcl cgo cgl cgo cgl
        rco rcl) h1 (Err.code_ne_of_cls hk0))
  | ok q1 =>
  rw [h1, crraE.k_class_recs_rules_ok_go.arm1] at hW
  cases hW

end sims

end L.Ind
