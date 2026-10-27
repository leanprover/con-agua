import ConAgua.Arena.IndT.RecGen4
import ConAgua.Arena.RecGenSpec9
import ConAgua.Arena.RecClassSpecO
import ConAgua.Arena.RecGenSpec8

/-!
# `classRulesOk` under `StageC` (lane `indstaget`)

`class_rules_ok`'s model at `realCall p`; twin side con-ron's `classRulesOk_spec`'s proof:
`paramLevels` (`paramLevels_spec`, a core-free grower: `RSim.liftP` of `plW_sim`), `classGenRule`
(`classGenRule_spec`: `RSim.liftPP` of `ruW_sim`), `classRuleOk` (`cr1W_relC`, from
`cruleW_okC`), the rest by induction.
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dClassGen dClassCtor dExt_denoteCV dClassGen_ext
  dClassCtor_ext mapM_option_cons_inv)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section sims
variable {p : Prog} (hq : KnotStageProg p) (hApd : ApdF p) {dn : NIdx → Option ConLeche.Name} {env : ConLeche.Env}

include hq hApd in
/-- `class_rules_ok_one` under `StageC` (`cr1W_rel`'s, `cruleW_okC`). -/
theorem cr1W_relC {visT visR : Word} {feR : IFEnv} {envR env₂ : ConLeche.Env}
    (henvR : ConLeche.EnvWF envR) {a : AState} {N : Nat} (hN : N ≤ 2 ^ 62) {m m' : Mem}
    {g cvR x gen : Word} {r : List Word} {cv : IConstantVal} {G : ClassGen} {X : ClassCtor}
    (h : cr1W (realCall p) N m visT visR g cvR x gen = some (r, m'))
    (hC : StageC dn visR feR envR m a) (hgen : H gen) (hcv : decCVp m cvR.toNat = some cv)
    (hext : CVExt m cvR.toNat) (hG : DecB (fun m => decCG m g.toNat) m G)
    (hns : G.nP + G.slots.length < 2 ^ 64) (hX : DecB (fun m => decCC m x.toNat) m X)
    (hA : AbsOK m) {cvRP : ConLeche.ConstantVal} {genP : ConLeche.Expr}
    (hcvP : Frontend.denoteCV a.store cv = some cvRP)
    (hgP : denoteE a.store (decI gen) = some genP)
    (hie : ConRon.Bridge.Inductives.IFEnvOKS env₂ (feR.restrictTo visT.toNat) a.store) :
    ∃ a', (ConRon.Arena.classRuleOk V visT.toNat feR cv (G.nP + G.slots.length + X.nF)
        (decI gen)).run a = .ok (decI gen, a') ∧ StageC dn visR feR envR m' a' ∧ IWGrow m m' ∧
      r = [gen] ∧ AbsOK m' ∧ ConRon.Bridge.CoreStep V envR feR a a' := by
  rcases N with _ | N
  · simp [cr1W] at h
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
  · rw [cr1W_big (h := hb)] at h; cases h
  rw [cr1W_ok (h := hb)] at h
  obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h rfl
  rw [cr1K_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨a', hrun, hC', hg, rfl, hA', hc'⟩ := cruleW_okC hq hApd henvR (by omega) h1 hC hgen
    (rec2DecCV_erecP hcv hext) (rec3CVExt_lt hC.stage hext) hA hcvP hgP hie
  have hn : (rdW (m.arr64 IW) g + rdW (m.arr64 IW) (g + 8) + rdW (m.arr64 IW) (x + 1)).toNat =
      G.nP + G.slots.length + X.nF := by
    rw [rec3Add_toNat hb, e0, e8, e1, t1]
    rw [UInt64.toNat_add, t0, t8]; exact congrArg (· + X.nF) (Nat.mod_eq_of_lt hns)
  rw [hn] at hrun
  exact ⟨a', hrun, hC', hg, rfl, hA', hc'⟩

include hq hApd in
/-- **`class_rules_ok` under `StageC`** (`crsW_sim`'s; twin side con-ron's `classRulesOk_spec`). -/
theorem crsW_simC (henv : ConLeche.EnvWF env) (visT visR : Word) (feR : IFEnv) {env₂ : ConLeche.Env}
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
    RSim (crsW (realCall p) n m visT visR g rco rcl cgo cgl cvR c xo xl)
      (ConRon.Arena.classRulesOk V visT.toNat feR G recCls cvGs cv c.toNat Xs) a
      (fun b a' x => (StageC dn visR feR env b.2 a' ∧ IWGrow m b.2 ∧ decEL b.2 b.1 x) ∧
        AbsOK b.2 ∧ ConRon.Bridge.CoreStep V env feR a a') := by
  induction n with
  | zero => intros; intro b hb; simp [crsW] at hb
  | succ n ih =>
  intro m a xo xl Xs XsP hC hG hrc hcg hcv hext hXs hA hgP hcvsP hcvP hXsP hie
  have hS := hC.stage
  have hsz := hS.2.2.2.1
  by_cases hxl : xl = 0
  · rw [crsW_nil (h := hxl)]
    have : Xs = [] := by
      have := decPL_length _ (hXs.get (OMono.decPL (fun q => decCC_mono q) _ _))
      rw [hxl] at this; exact List.eq_nil_of_length_eq_zero (by simpa using this)
    subst this
    unfold ConRon.Arena.classRulesOk
    exact RSim.pure_some ⟨⟨hC, IWGrow.refl m, by simp [decHL, hslice?], by simp⟩, hA,
      ConRon.Bridge.CoreStep.refl hC.check⟩
  rw [crsW_cons (h := hxl)]
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
  rw [ex]
  have hX' : DecB (fun m => decCC m (UInt64.ofNat px : Word).toNat) m X := by rw [tx]; exact hX
  unfold ConRon.Arena.classRulesOk
  obtain ⟨-, hlps, -⟩ := ConRon.Bridge.Core.denoteCV_inv hcvP
  -- `cv_lps`: L only
  refine RSim.lstep (K := crsK1 (realCall p) n visT visR g rco rcl cgo cgl cvR c xo xl
    (UInt64.ofNat px)) (by rw [crsK1]) fun ⟨r1, m1⟩ h1 => ?_
  obtain ⟨hS1, hg1, hd1, ht1⟩ := cvLpsA_stage h1 hS hcv (rec3CVExt_lt hS hext)
  have hA1 := cvLpsA_afr h1 hA
  have hC1 : StageC dn visR feR env m1 a := hC.of_check hS1 hA1 hC.check (Ext.refl _)
  rw [crsK1_some]
  -- `param_levels`
  refine RSim.bind (K := crsK2 (realCall p) n visT visR g rco rcl cgo cgl cvR c xo xl
    (UInt64.ofNat px)) (by rw [crsK2])
    (RSim.liftP hC1 (RSim.withF (rec3Sim_rsim (plW_sim (k := n) hS1 hd1 ht1)) (fun _ hb => plW_afr hb))
      (fun _ _ _ h => ⟨h.1.2.2.1, h.2 hA1⟩)
      (ConRon.Bridge.Inductives.paramLevels_spec cv.levelParams _) hlps) ?_
  rintro ⟨r2, m2⟩ rl a2 - ⟨hC2, ⟨⟨hrlH, hrl, hS2, hg2⟩, hf2⟩, hRl, p1⟩
  dsimp only at hrlH hrl hS2 hg2 hC2
  subst hrl
  rw [crsK2_some]
  have hg02 := hg1.trans hg2
  have hA2 := hf2 hA1
  -- `class_gen_rule`
  refine RSim.bind (K := crsK3 (realCall p) n visT visR g rco rcl cgo cgl cvR c xo xl
    (UInt64.ofNat px)) (by rw [crsK3])
    (RSim.liftPP hC2 (ruW_sim dn visR feR n m2 a2 g rco rcl cgo cgl (r2.headD 0) c (UInt64.ofNat px)
      G X recCls cvGs hS2 (hG.grow (decCG_mono _) hg02) hns (hX'.grow (decCC_mono _) hg02) hrlH
      (hrc.grow (OMono.decNL _ _) hg02) hrcb
      (hcg.grow (OMono.decPL (fun q => OMono.decCVp q) _ _) hg02) hcgb hA2)
      (fun _ _ _ h => ⟨h.1.1, h.2⟩)
      (ConRon.Bridge.Inductives.classGenRule_spec G gP recCls cvGs cvGsP (decI (r2.headD 0)) _
        c.toNat X XP)
      ⟨dClassGen_ext p1.ext _ _ hgP, dClassCtor_ext p1.ext _ _ hXP,
        dExt_denoteCV.list p1.ext _ _ hcvsP, hRl⟩) ?_
  rintro ⟨r3, m3⟩ o3 a3 - ⟨hC3, ⟨⟨hS3, hg3, ho3⟩, hA3⟩, hR3, p2⟩
  dsimp only at hS3 hg3 ho3 hC3
  rcases o3 with _ | gen
  · rw [crsK3_fail (h := ho3)]; exact RSim.none
  obtain ⟨genP, -, hgenP⟩ := hR3
  obtain ⟨h31, hgH, hgd⟩ := ho3
  rw [crsK3_ok (h := by rw [h31]; decide)]
  subst hgd
  have hg03 := hg02.trans hg3
  have p12 := p1.trans p2
  -- `class_rules_ok_one`
  refine RSim.bind (K := crsK4 (realCall p) n visT visR g rco rcl cgo cgl cvR c xo xl)
    (by rw [crsK4])
    (Q1 := fun b a' y => StageC dn visR feR env b.2 a' ∧ IWGrow m3 b.2 ∧
      b.1 = [r3.tail.headD 0] ∧ y = decI (r3.tail.headD 0) ∧ AbsOK b.2 ∧
      ConRon.Bridge.CoreStep V env feR a3 a')
    (fun ⟨r4, m4⟩ h4 => by
      obtain ⟨a', hrun, hC', hg, hr, hA4, hc4⟩ := cr1W_relC hq hApd henv (by omega) h4 hC3 hgH
        (by rw [decCVp_grow_r hg03 hext]; exact hcv) (CVExt_grow hg03 hext)
        (hG.grow (decCG_mono _) hg03) hns (hX'.grow (decCC_mono _) hg03) hA3
        (dExt_denoteCV p12.ext _ _ hcvP) hgenP (hie.mono p12.ext)
      exact ⟨_, a', hrun, hC', hg, hr, rfl, hA4, hc4⟩) ?_
  rintro ⟨r4, m4⟩ y a4 - ⟨hC4, hg4, hr4, rfl, hA4, c4⟩
  dsimp only at hC4 hg4 hr4
  subst hr4
  rw [crsK4_some]
  have hg04 := hg03.trans hg4
  have c14 := (p12.toCore hC.check).trans c4
  -- the rest
  have hxo1 := rec2ToNat_succ (o := xo) (i := xo.toNat) (Nat.le_refl _) (by omega)
  have hxl1 := rec2ToNat_pred hxl
  refine RSim.bind (K := crsK5 n (r3.tail.headD 0)) rfl
    (ih (by omega) m4 a4 (xo + 1) (xl - 1) Xs' XsP' hC4 (hG.grow (decCG_mono _) hg04)
      (hrc.grow (OMono.decNL _ _) hg04)
      (hcg.grow (OMono.decPL (fun q => OMono.decCVp q) _ _) hg04)
      (by rw [decCVp_grow_r hg04 hext]; exact hcv) (CVExt_grow hg04 hext)
      (by rw [hxo1, hxl1, hjx]; exact (show DecB (fun m => decPL m (decCC m) (xo.toNat + 1) jx) m Xs' from
        hXsT).grow (OMono.decPL (fun q => decCC_mono q) _ _) hg04) hA4
      (dClassGen_ext c14.ext _ _ hgP) (dExt_denoteCV.list c14.ext _ _ hcvsP)
      (dExt_denoteCV c14.ext _ _ hcvP) (dClassCtor_ext.list c14.ext _ _ hXsP') (hie.mono c14.ext)) ?_
  rintro ⟨r5, m5⟩ rs a5 - ⟨⟨hC5, hg5, hrs, hrsb⟩, hA5, c5⟩
  dsimp only at hC5 hg5 hrs hrsb
  rw [crsK5_some]
  refine RSim.lstep (K := crsK6) rfl fun ⟨r6, m6⟩ h6 => ?_
  rw [getD_zero, getD_one] at hrs hrsb
  obtain ⟨hS6, hg6, hd6, ht6⟩ := consW_stage h6 hC5.stage hrsb hgH hrs
  rw [crsK6_some]
  have hA6 := consW_afr h6 hA5
  refine RSim.pure_some ⟨⟨hC5.of_check hS6 hA6 hC5.check (Ext.refl _), hg04.trans (hg5.trans hg6),
    ?_, ?_⟩, hA6, c14.trans c5⟩ <;>
    simp only [getD_zero, List.headD_cons]
  · exact hd6
  · exact Nat.le_of_eq ht6

include hq hApd in
/-- **`class_rules_ok` refines `classRulesOk`** under `StageC` (the inputs' denotations as con-ron's
`classRulesOk_spec` asks): the rules, a handle slice below the top. -/
@[refines ConRon.Arena.classRulesOk]
theorem classRulesOk_refinesC (hp : CrsProg p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
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
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_rules_ok"
      [visT, visR, g, rco, rcl, cgo, cgl, cvR, c, xo, xl]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.classRulesOk V visT.toNat feR G recCls cvGs cv c.toNat Xs) a₀ ∧
      (StageC dn visR feR env s'.mem
          (AM.st (ConRon.Arena.classRulesOk V visT.toNat feR G recCls cvGs cv c.toNat Xs) a₀) ∧
        IWGrow s₀.mem s'.mem ∧ decEL s'.mem r
          (AM.res (ConRon.Arena.classRulesOk V visT.toNat feR G recCls cvGs cv c.toNat Xs) a₀)) ∧
      AbsOK s'.mem; ⊤⦄ :=
  triple_post (classRulesOk_spec p hp (realCall p) (realCall_spec p) n s₀ visT visR g rco rcl cgo cgl
    cvR c xo xl) fun _ _ ⟨hl, hw⟩ =>
    let h := (crsW_simC hq hApd henv visT visR feR (env₂ := env₂) g rco rcl cgo cgl cvR c G recCls cvGs cv
      hns hrcb hcgb gP cvGsP cvRP n hn _ a₀ xo xl Xs XsP hC hG hrc hcg hcv hext hXs hA hgP hcvsP
      hcvP hXsP hie).am hw
    ⟨hl, h.1, h.2.1, h.2.2.1⟩

end sims

end L.Ind
