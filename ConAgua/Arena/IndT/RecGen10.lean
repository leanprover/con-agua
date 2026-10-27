import ConAgua.Arena.IndT.RecGen9
import ConAgua.Arena.RecGenSpec10

/-!
# `classRecsRulesOk` under `StageC` (lane `indstaget`)

`class_recs_rules_ok`'s model at `realCall p`; twin side con-ron's `classRecsRulesOk_spec`'s proof:
`classRulesOk` (`crsW_simC`), `targetMajorAt` (`targetMajorAt_spec`: `RSim.liftPP` of
`rec3TMA_sim`), the record write (twin side none), the rest by induction.
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dClassGen dClassCtor dExt_denoteCV dClassGen_ext
  dClassCtor_ext dMajor_ext mapM_option_cons_inv dClassGen_inv)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section sims
variable {p : Prog} (hq : KnotStageProg p) (hApd : ApdF p) {dn : NIdx → Option ConLeche.Name} {env : ConLeche.Env}

/-- The class's constructors denote (con-ron's `classRecsRulesOk_spec`, its first step). -/
theorem ctorsAt_denote {st : EStore} {G : ClassGen} {gP : ConLeche.ClassGen}
    (hg : dClassGen st G = some gP) (c : Nat) :
    (G.ctors.getD c []).mapM (dClassCtor st) = some (gP.ctors.getD c []) := by
  obtain ⟨-, -, -, -, -, hctors, -, -⟩ := dClassGen_inv hg
  have hcj := ConRon.Bridge.Inductives.mapM_option_getElem? (st := st) hctors c
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rcases hc : G.ctors[c]? with _ | xs
  · rw [hc] at hcj; have : gP.ctors[c]? = none := hcj; rw [this]; rfl
  rw [hc] at hcj
  obtain ⟨xsP, hxsP, hd⟩ := hcj
  rw [hxsP]; exact hd

include hq hApd in
/-- **`class_recs_rules_ok` under `StageC`** (`crrW_sim`'s; twin side con-ron's
`classRecsRulesOk_spec`). -/
theorem crrW_simC (henv : ConLeche.EnvWF env) (visT visR : Word) (feR : IFEnv)
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
    RSim (crrW (realCall p) n m visT visR g rco rcl cgo cgl vo vl co cl)
      (ConRon.Arena.classRecsRulesOk V visT.toNat feR G recCls cvGs cvs cs) a
      (fun b a' x => (StageC dn visR feR env b.2 a' ∧ IWGrow m b.2 ∧ decRRS b.2 b.1 x) ∧
        AbsOK b.2 ∧ ConRon.Bridge.CoreStep V env feR a a') := by
  induction n with
  | zero => intros; intro b hb; simp [crrW] at hb
  | succ n ih =>
  intro m a vo vl co cl cvs cs cvsP hC hG hrc hcg hcvs hcs hA hgP hcvGsP hcvsP hie
  have hS := hC.stage
  have hsz := hS.2.2.2.1
  have hnil : RSim (some ([0, 0], m))
      (Pure.pure [] : AM (List (IConstantVal × TargetMajor × List EIdx))) a
      (fun b a' x => (StageC dn visR feR env b.2 a' ∧ IWGrow m b.2 ∧ decRRS b.2 b.1 x) ∧
        AbsOK b.2 ∧ ConRon.Bridge.CoreStep V env feR a a') :=
    RSim.pure_some ⟨⟨hC, IWGrow.refl m, by show decPL (truncM m) _ _ _ = some []; simp [decPL],
      by simp⟩, hA, ConRon.Bridge.CoreStep.refl hC.check⟩
  by_cases hvl : vl = 0
  · rw [crrW_nil1 (h := hvl)]
    have : cvs = [] := by
      have := hcvs.length; rw [hvl] at this; exact List.eq_nil_of_length_eq_zero (by simpa using this)
    subst this
    unfold ConRon.Arena.classRecsRulesOk
    exact hnil
  obtain ⟨jv, hjv⟩ : ∃ j, vl.toNat = j + 1 :=
    ⟨vl.toNat - 1, by
      have : vl.toNat ≠ 0 := fun e => hvl (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  obtain ⟨pp, cv, cvs', rfl, hp, hpt, hcv, hcvsT⟩ := rec3SPL_uncons (by rw [← hjv]; exact hcvs)
  obtain ⟨cvP, cvsP', rfl, hcvP, hcvsP'⟩ := mapM_option_cons_inv hcvsP
  by_cases hcl : cl = 0
  · rw [crrW_nil2 (h1 := hvl) (h := hcl)]
    have : cs = [] := by
      have := decNL_length _ (hcs.get (OMono.decNL _ _)); rw [hcl] at this
      exact List.eq_nil_of_length_eq_zero (by simpa using this)
    subst this
    unfold ConRon.Arena.classRecsRulesOk
    exact hnil
  rw [crrW_cons (h1 := hvl) (h := hcl)]
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
  rw [ep, ec]
  obtain ⟨hcvp, hcvx⟩ := rec3CVX hcv
  unfold ConRon.Arena.classRecsRulesOk
  dsimp only
  -- `class_rules_ok`
  have hxs := rec3CtorsAt (c := UInt64.ofNat c0) hS hG
  rw [tc] at hxs
  refine RSim.bind (K := crrK1 (realCall p) n visT visR g rco rcl cgo cgl vo vl co cl
    (UInt64.ofNat pp) (UInt64.ofNat c0)) (by rw [crrK1])
    (by
      have := crsW_simC hq hApd henv visT visR feR (env₂ := env₂) g rco rcl cgo cgl (UInt64.ofNat pp)
        (UInt64.ofNat c0) G recCls cvGs cv hns hrcb hcgb gP cvGsP cvP n (by omega) m a _ _ _
        (gP.ctors.getD c0 []) hC hG hrc (rec3SPL_decB hcg) (by rw [tp]; exact hcvp)
        (by rw [tp]; exact hcvx) hxs hA hgP hcvGsP hcvP (ctorsAt_denote hgP c0) hie
      rw [tc] at this
      exact this) ?_
  rintro ⟨r1, m1⟩ rhss a1 - ⟨⟨hC1, hg1, hr1⟩, hA1, c1⟩
  dsimp only at hC1 hg1 hr1 hA1
  rw [crrK1_some]
  -- `target_major_at`
  have hS1 := hC1.stage
  have hG1 := hG.grow (decCG_mono _) hg1
  have hsz1 := hS1.2.2.2.1
  obtain ⟨-, -, ⟨o3, l3, h3, h4, hcls⟩, -⟩ := rec2CG_parts hG1
  obtain ⟨e3, t3⟩ := rec2RdN (w := g) (k := 3) h3 hsz1
  obtain ⟨e4, t4⟩ := rec2RdN (w := g) (k := 4) h4 hsz1
  simp only [show UInt64.ofNat 3 = (3 : Word) from rfl, show UInt64.ofNat 4 = (4 : Word) from rfl] at e3 e4
  rw [e3, e4]
  have hb3 : o3 + l3 < 2 ^ 64 := by
    by_cases hl : l3 = 0
    · have := iwN_rdW h3 (by have := hS1.2.1; have := (rec2CG_parts hG1).2.1; omega); omega
    · have := rec2DecB_PL_top hcls hl; have := hS1.2.1; omega
  have hM := rec3TMA_sim dn visR feR n m1 a1 (UInt64.ofNat o3) (UInt64.ofNat l3) (UInt64.ofNat c0)
    G.cls hS1 (by rw [t3, t4]; exact hcls) (by rw [t3, t4]; exact hb3)
  rw [tc] at hM
  obtain ⟨-, -, hclsP, -, -, -, -, -⟩ := dClassGen_inv hgP
  refine RSim.bind (K := crrK2 (realCall p) n visT visR g rco rcl cgo cgl vo vl co cl
    (UInt64.ofNat pp) (r1.headD 0) (r1.tail.headD 0)) (by rw [crrK2])
    (RSim.liftPP hC1 (RSim.withF hM (fun _ hb => tmaW_afr hb)) (fun _ _ _ h => ⟨h.1.1, h.2 hA1⟩)
      (ConRon.Bridge.Inductives.targetMajorAt_spec G.cls gP.cls c0)
      (dMajor_ext.list c1.ext _ _ hclsP)) ?_
  rintro ⟨r2, m2⟩ M a2 - ⟨hC2, ⟨⟨hS2, hg2, hMd⟩, hf2⟩, -, p2⟩
  dsimp only at hS2 hg2 hMd hC2
  rw [crrK2_some]
  have c12 := c1.trans (p2.toCore c1.ok)
  -- `rec4`: L only
  refine RSim.lstep (K := crrK3 (realCall p) n visT visR g rco rcl cgo cgl vo vl co cl)
    (by rw [crrK3]) fun ⟨r3, m3⟩ h3' => ?_
  obtain ⟨hS3, hg3, hr3, hget3, htop3⟩ := recW_stage h3' hS2 rfl
  have hA3 := recW_afr h3' (hf2 hA1)
  have hC3 : StageC dn visR feR env m3 a2 := hC2.of_check hS3 hA3 hC2.check (Ext.refl _)
  rw [crrK3_some]
  have hg13 := hg2.trans hg3
  have hrec : DecB (fun m => decRR m (r3.headD 0).toNat) m3 (cv, M, rhss) := by
    rw [hr3]
    refine rec3Rec4_decB (m := m2) (fun j hj => hget3 j (by simpa using hj))
      (by simp at htop3; simp [iwTop] at htop3 ⊢; omega) hg3
      ((rec3CVX_decB hcv).grow (OMono.decCVp _) ((hg1.trans hg2)) |> fun h => by rw [tp]; exact h) hMd
      ((decRL_decB hr1).grow (OMono.decHL _ _) hg2 |> fun h => by
        simp only [getD_zero, Nat.zero_add, getD_one] at h; exact h)
  -- the rest
  have hg03 := hg1.trans hg13
  have hvo1 := rec2ToNat_succ (o := vo) (i := vo.toNat) (Nat.le_refl _) (by have := hS.2.1; omega)
  have hco1 := rec2ToNat_succ (o := co) (i := co.toNat) (Nat.le_refl _)
    (by have := hS.2.1; have := (rec2IwN_trunc hc0).1; omega)
  have hvl1 := rec2ToNat_pred hvl
  have hcl1 := rec2ToNat_pred hcl
  refine RSim.bind (K := crrK4 n (r3.headD 0)) rfl
    (ih (by omega) m3 a2 (vo + 1) (vl - 1) (co + 1) (cl - 1) cvs' cs' cvsP' hC3
      (hG.grow (decCG_mono _) hg03) (hrc.grow (OMono.decNL _ _) hg03) (hcg.grow hg03)
      (by rw [hvo1, hvl1, hjv]; exact hcvsT.grow hg03)
      (by rw [hco1, hcl1, hjc]; exact (show DecB (fun m => decNL m (co.toNat + 1) jc) m cs' from
        hcsT).grow (OMono.decNL _ _) hg03) hA3
      (dClassGen_ext c12.ext _ _ hgP) (dExt_denoteCV.list c12.ext _ _ hcvGsP)
      (dExt_denoteCV.list c12.ext _ _ hcvsP') (hie.mono c12.ext)) ?_
  rintro ⟨r4, m4⟩ rest a4 - ⟨⟨hC4, hg4, hrs, hrsb⟩, hA4, c4⟩
  dsimp only at hC4 hg4 hrs hrsb
  rw [crrK4_some]
  refine RSim.lstep (K := crrK5) rfl fun ⟨r5, m5⟩ h5 => ?_
  obtain ⟨hS5, hg5, hd5, ht5⟩ := partsConsPL decRR_mono h5 hC4.stage hrsb hrs
    (hrec.grow (decRR_mono _) hg4)
  rw [crrK5_some]
  have hA5 := consW_afr h5 hA4
  exact RSim.pure_some ⟨⟨hC4.of_check hS5 hA5 hC4.check (Ext.refl _), hg03.trans (hg4.trans hg5),
    by simpa using hd5, by simp only [List.headD_cons, List.tail_cons]; omega⟩, hA5,
    c12.trans c4⟩

include hq hApd in
/-- **`class_recs_rules_ok` refines `classRecsRulesOk`** under `StageC` (the inputs' denotations as
con-ron's `classRecsRulesOk_spec` asks). -/
@[refines ConRon.Arena.classRecsRulesOk]
theorem classRecsRulesOk_refinesC (hp : CrrProg p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St)
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
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_recs_rules_ok" [visT, visR, g, rco, rcl, cgo, cgl]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.classRecsRulesOk V visT.toNat feR G recCls cvGs cvGs recCls) a₀ ∧
      (StageC dn visR feR env s'.mem
          (AM.st (ConRon.Arena.classRecsRulesOk V visT.toNat feR G recCls cvGs cvGs recCls) a₀) ∧
        IWGrow s₀.mem s'.mem ∧ decRRS s'.mem r
          (AM.res (ConRon.Arena.classRecsRulesOk V visT.toNat feR G recCls cvGs cvGs recCls) a₀)) ∧
      AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (classRecsRulesOk_spec p hp (realCall p) (realCall_spec p) n s₀ visT visR g rco
    rcl cgo cgl) fun _ _ ⟨hl, hw⟩ => ?_
  rcases n with _ | n
  · simp [crraW] at hw
  rw [crraW_eq] at hw
  have h := RSim.am (RSim.bindPure (K := crrK5) rfl (crrW_simC hq hApd henv visT visR feR (env₂ := env₂)
    g rco rcl cgo cgl G recCls cvGs hns hrcb hcgb gP cvGsP n (by omega) s₀.mem a₀ cgo cgl rco rcl
    cvGs recCls cvGsP hC hG hrc hcg hcg hrc hA hgP hcvGsP hcvGsP hie) (Q := fun b a' x =>
      (StageC dn visR feR env b.2 a' ∧ IWGrow s₀.mem b.2 ∧ decRRS b.2 b.1 x) ∧ AbsOK b.2) ?_) hw
  · exact ⟨hl, h.1, h.2.1, h.2.2⟩
  rintro ⟨r1, m1⟩ x a1 - ⟨⟨hC1, hg1, hd1, hb1⟩, hA1, -⟩
  rw [crrK5_some]
  exact RSim.pure_some ⟨⟨hC1, hg1, by simpa using hd1, by simpa using hb1⟩, hA1⟩

end sims

end L.Ind
