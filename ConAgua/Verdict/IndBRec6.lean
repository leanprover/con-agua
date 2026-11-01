module

import ConRon.Bridge.Inductives.PosWalks
public import ConAgua.Verdict.IndBRec5
import ConAgua.Arena.IndSumSpec.ConsBlockRecsTF
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndRealAbsSim
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.RecClassSpec.MkTMWAfr
import ConAgua.Arena.RecClassSpec.PiBWRoom
import ConAgua.Arena.RecGenSpec.ClassFeR
import ConAgua.Arena.RecGenSpec.Rec3CVX
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree

@[expose] public section
/-!
# `class_recs_rules_ok_go`, `class_recs_rules_ok`: one model and one refinement for both outcomes

`crrE` (`l_model … unified`: `class_rules_ok` through its unified model, `target_major_at`, `rec4`
and `sl_cons` lifted) and `crr_ref` under `StageC`; twin side con-ron's `classRecsRulesOk_spec`'s
proof: `classRulesOk` (`crs_ref`), `targetMajorAt` (`targetMajorAt_spec`: `RSim.liftPP` of
`rec3TMA_sim`), the record write (twin side none), the rest by induction. `class_recs_rules_ok`
(`crra_ref`) is the first call, repacked. Their ok half is `classRecsRulesOk_refinesC`, their error
half `classRecsRulesOk_claim`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dClassGen dClassCtor dExt_denoteCV dClassGen_ext
  dClassCtor_ext dMajor_ext mapM_option_cons_inv dClassGen_inv)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model crrE_spec (p : Prog) (hP : CrrProg p)
  fns [hP.go ↦ crrE]
  specs [crsE_spec p hP.crs n, targetMajorAt_spec p hP.crs.alloc hP.pw hP.mtm hP.tmd hP.tma hP.na n,
    rec4_specW p hP.crs.alloc n hP.rec4, slCons_specW p hP.crs.alloc hP.crs.copy hP.crs.cons n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model crraE_spec (p : Prog) (hP : CrrProg p)
  fns [hP.top ↦ crraE] specs [crrE_spec p hP n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `class_recs_rules_ok(_go)` gives besides the twin's records `xs` (from `m`, `a`): the stage
invariant under `StageC`, the growth, the records a slice below the tops, the abstraction memo, the
core step. -/
structure CrrPost (dn : NIdx → Option ConLeche.Name) (visR : Word) (feR : IFEnv) (env : ConLeche.Env)
    (m : Mem) (a : AState) (r : List Word) (m' : Mem)
    (xs : List (IConstantVal × TargetMajor × List EIdx)) (a' : AState) : Prop where
  stage : StageC dn visR feR env m' a'
  grow : IWGrow m m'
  dec : decRRS m' r xs
  abs : AbsOK m'
  core : ConRon.Bridge.CoreStep V env feR a a'

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

section sims
variable {p : Prog} (hq : KnotStageProg p) (hApd : ApdF p) {dn : NIdx → Option ConLeche.Name}
  {env : ConLeche.Env} (hnv : closedNV p _root_.L.Checker.nvFns = true) (hcE : CoreStubsE p) (hU : UceProg p)

include hq hApd in
/-- **`class_recs_rules_ok_go` refines `classRecsRulesOk`, both outcomes** under `StageC` (the
inputs' denotations as con-ron's `classRecsRulesOk_spec` asks). -/
theorem crr_ref (hP : CrrProg p) (henv : ConLeche.EnvWF env) (visT visR : Word) (feR : IFEnv)
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
    RefE (VerdictCtxU p) (crrE p n m visT visR g rco rcl cgo cgl vo vl co cl)
      (ConRon.Arena.classRecsRulesOk V visT.toNat feR G recCls cvGs cvs cs) a
      (fun v xs a' => CrrPost dn visR feR env m a v.1 v.2 xs a') := by
  induction n with
  | zero => intros; rw [crrE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a vo vl co cl cvs cs cvsP hC hG hrc hcg hcvs hcs hA hgP hcvGsP hcvsP hie
  have hS := hC.stage
  have hsz := hS.iw.iwSize
  have hnil : RefE (VerdictCtxU p) (.ok ([0, 0], m))
      (Pure.pure [] : AM (List (IConstantVal × TargetMajor × List EIdx))) a
      (fun v xs a' => CrrPost dn visR feR env m a v.1 v.2 xs a') :=
    RefE.ret rfl ⟨hC, IWGrow.refl m, ⟨by show decPL (truncM m) _ _ _ = some []; simp [decPL], by simp⟩,
      hA, ConRon.Bridge.CoreStep.refl hC.check⟩
  by_cases hvl : vl = 0
  · rw [crrE.arm1 p n m visT visR g rco rcl cgo cgl vo vl co cl hvl]
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
  · rw [crrE.arm2 p n m visT visR g rco rcl cgo cgl vo vl co cl hvl hcl]
    have : cs = [] := by
      have := decNL_length _ (hcs.get (OMono.decNL _ _)); rw [hcl] at this
      exact List.eq_nil_of_length_eq_zero (by simpa using this)
    subst this
    unfold ConRon.Arena.classRecsRulesOk
    exact hnil
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
          (crsE p n m visT visR g rco rcl cgo cgl (UInt64.ofNat pp) (UInt64.ofNat c0)
            (crrXs m g (UInt64.ofNat c0)).1 (crrXs m g (UInt64.ofNat c0)).2) := by
    by_cases hc : rdW (m.arr64 IW) co < rdW (m.arr64 IW) (g + 10)
    · rw [crrE.arm3 p n m visT visR g rco rcl cgo cgl vo vl co cl hvl hcl hc, crrE.j1.arm1, ep, ec]
      rw [ec] at hc
      rw [crrXs_hit (h := hc)]
    · rw [crrE.arm4 p n m visT visR g rco rcl cgo cgl vo vl co cl hvl hcl hc, crrE.j1.arm1, ep, ec]
      rw [ec] at hc
      rw [crrXs_miss (h := hc)]
  rw [hj1]
  obtain ⟨hcvp, hcvx⟩ := rec3CVX hcv
  unfold ConRon.Arena.classRecsRulesOk
  dsimp only
  -- `class_rules_ok`
  have hxs := rec3CtorsAt (c := UInt64.ofNat c0) hS hG
  rw [tc] at hxs
  have hr := crs_ref hq hApd hP.crs henv visT visR feR (env₂ := env₂) g rco rcl cgo cgl (UInt64.ofNat pp)
    (UInt64.ofNat c0) G recCls cvGs cv hns hrcb hcgb gP cvGsP cvP n (by omega) m a _ _ _
    (gP.ctors.getD c0 []) hC hG hrc (rec3SPL_decB hcg) (by rw [tp]; exact hcvp)
    (by rw [tp]; exact hcvx) hxs hA hgP hcvGsP hcvP (ctorsAt_denote hgP c0) hie
  rw [tc] at hr
  refine RefE.bindE (fun _ => crrE.k_class_rules_ok.none ..) id hr fun ⟨r1, m1⟩ rhss a1 _ hR1 => ?_
  rw [crrE.k_class_rules_ok.arm1]
  -- `target_major_at`
  have hS1 := hR1.stage.stage
  have hG1 := hG.grow (decCG_mono _) hR1.grow
  have hsz1 := hS1.iw.iwSize
  obtain ⟨-, -, ⟨o3, l3, h3, h4, hcls⟩, -⟩ := rec2CG_parts hG1
  obtain ⟨e3, t3⟩ := rec2RdN (w := g) (k := 3) h3 hsz1
  obtain ⟨e4, t4⟩ := rec2RdN (w := g) (k := 4) h4 hsz1
  simp only [show UInt64.ofNat 3 = (3 : Word) from rfl, show UInt64.ofNat 4 = (4 : Word) from rfl] at e3 e4
  rw [e3, e4]
  have hb3 : o3 + l3 < 2 ^ 64 := by
    by_cases hl : l3 = 0
    · have := iwN_rdW h3 (by have := hS1.iw.iw; have := (rec2CG_parts hG1).2.1; omega); omega
    · have := rec2DecB_PL_top hcls hl; have := hS1.iw.iw; omega
  have hM := rec3TMA_sim dn visR feR n m1 a1 (UInt64.ofNat o3) (UInt64.ofNat l3) (UInt64.ofNat c0)
    G.cls hS1 (by rw [t3, t4]; exact hcls) (by rw [t3, t4]; exact hb3)
  rw [tc] at hM
  obtain ⟨-, -, hclsP, -, -, -, -, -⟩ := dClassGen_inv hgP
  refine RefE.bindLift (fun _ => crrE.k_target_major_at.none ..) fun r2 m2 h2 => ?_
  obtain ⟨M, a2, hrun2, hC2, ⟨⟨hS2, hg2, hMd⟩, hf2⟩, -, p2⟩ :=
    (RSim.liftPP hR1.stage (RSim.withF hM (fun _ hb => tmaW_afr hb)) (fun _ _ _ h => ⟨h.1.1, h.2 hR1.abs⟩)
      (ConRon.Bridge.Inductives.targetMajorAt_spec G.cls gP.cls c0)
      (dMajor_ext.list hR1.core.ext _ _ hclsP)) (r2, m2) h2
  dsimp only at hS2 hg2 hMd hC2
  have c12 := hR1.core.trans (p2.toCore hR1.core.ok)
  refine ⟨_, _, hrun2, ?_⟩
  rw [crrE.k_target_major_at.arm1]
  -- `rec4`: L only
  refine RefE.onlySim (fun _ => crrE.k_rec4.none ..) (fun _ _ h => h) fun r3 m3 h3' => ?_
  rw [crrE.k_rec4.arm1]
  obtain ⟨hS3, hg3, hr3, hget3, htop3⟩ := recW_stage h3' hS2 rfl
  have hA3 := recW_afr h3' (hf2 hR1.abs)
  have hC3 : StageC dn visR feR env m3 a2 := hC2.of_check hS3 hA3 hC2.check (Ext.refl _)
  have hrec : DecB (fun m => decRR m (r3.headD 0).toNat) m3 (cv, M, rhss) := by
    rw [hr3]
    refine rec3Rec4_decB (m := m2) (fun j hj => hget3 j (by simpa using hj))
      (by simp at htop3; simp [iwTop] at htop3 ⊢; omega) hg3
      ((rec3CVX_decB hcv).grow (OMono.decCVp _) ((hR1.grow.trans hg2)) |> fun h => by rw [tp]; exact h) hMd
      ((decRL_decB hR1.dec).grow (OMono.decHL _ _) hg2 |> fun h => by
        simp only [getD_zero, Nat.zero_add, getD_one] at h; exact h)
  -- the rest
  have hg03 := hR1.grow.trans (hg2.trans hg3)
  have hvo1 := rec2ToNat_succ (o := vo) (i := vo.toNat) (Nat.le_refl _) (by have := hS.iw.iw; omega)
  have hco1 := rec2ToNat_succ (o := co) (i := co.toNat) (Nat.le_refl _)
    (by have := hS.iw.iw; have := (rec2IwN_trunc hc0).1; omega)
  have hvl1 := rec2ToNat_pred hvl
  have hcl1 := rec2ToNat_pred hcl
  have ih' := ih (by omega) m3 a2 (vo + 1) (vl - 1) (co + 1) (cl - 1) cvs' cs' cvsP' hC3
    (hG.grow (decCG_mono _) hg03) (hrc.grow (OMono.decNL _ _) hg03) (hcg.grow hg03)
    (by rw [hvo1, hvl1, hjv]; exact hcvsT.grow hg03)
    (by rw [hco1, hcl1, hjc]; exact (show DecB (fun m => decNL m (co.toNat + 1) jc) m cs' from
      hcsT).grow (OMono.decNL _ _) hg03) hA3
    (dClassGen_ext c12.ext _ _ hgP) (dExt_denoteCV.list c12.ext _ _ hcvGsP)
    (dExt_denoteCV.list c12.ext _ _ hcvsP') (hie.mono c12.ext)
  refine RefE.bindE (fun _ => crrE.k_class_recs_rules_ok_go.none ..) id ih' fun ⟨r4, m4⟩ rest a4 _ hR4 => ?_
  rw [crrE.k_class_recs_rules_ok_go.arm1]
  -- `sl_cons`
  refine RefE.onlySim (fun _ => crrE.k_sl_cons.none ..) (fun _ _ h => h) fun r5 m5 h5 => ?_
  rw [crrE.k_sl_cons.arm1]
  obtain ⟨hrs, hrsb⟩ := hR4.dec
  obtain ⟨hS5, hg5, hd5, ht5⟩ := partsConsPL decRR_mono h5 hR4.stage.stage hrsb hrs
    (hrec.grow (decRR_mono _) hR4.grow)
  have hA5 := consW_afr h5 hR4.abs
  exact RefE.ret rfl ⟨hR4.stage.of_check hS5 hA5 hR4.stage.check (Ext.refl _),
    hg03.trans (hR4.grow.trans hg5), ⟨by simpa using hd5, by simp only [List.headD_cons, List.tail_cons]; omega⟩,
    hA5, c12.trans hR4.core⟩

include hq hApd in
/-- **`class_recs_rules_ok` refines `classRecsRulesOk`, both outcomes** under `StageC`: the
first call of `class_recs_rules_ok_go` (`crr_ref`), its result repacked. -/
theorem crra_ref (hP : CrrProg p) (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    (henv : ConLeche.EnvWF env) (visT visR : Word) (feR : IFEnv) {env₂ : ConLeche.Env}
    (g rco rcl cgo cgl : Word) (G : ClassGen) (recCls : List Nat) (cvGs : List IConstantVal)
    (hC : StageC dn visR feR env m a) (hG : DecB (fun m => decCG m g.toNat) m G)
    (hns : G.nP + G.slots.length < 2 ^ 64)
    (hrc : DecB (fun m => decNL m rco.toNat rcl.toNat) m recCls)
    (hrcb : rco.toNat + rcl.toNat < 2 ^ 64)
    (hcg : SPL decCVX m cgo.toNat cgl.toNat cvGs) (hcgb : cgo.toNat + cgl.toNat < 2 ^ 64)
    (hA : AbsOK m) {gP : ConLeche.ClassGen} {cvGsP : List ConLeche.ConstantVal}
    (hgP : dClassGen a.store G = some gP) (hcvGsP : cvGs.mapM (Frontend.denoteCV a.store) = some cvGsP)
    (hie : ConRon.Bridge.Inductives.IFEnvOKS env₂ (feR.restrictTo visT.toNat) a.store) :
    RefE (VerdictCtxU p) (crraE p n m visT visR g rco rcl cgo cgl)
      (ConRon.Arena.classRecsRulesOk V visT.toNat feR G recCls cvGs cvGs recCls) a
      (fun v xs a' => CrrPost dn visR feR env m a v.1 v.2 xs a') := by
  cases n with
  | zero => rw [crraE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ n =>
  rw [crraE.arm1]
  have h := crr_ref hq hApd hP henv visT visR feR (env₂ := env₂) g rco rcl cgo cgl G recCls cvGs hns hrcb
    hcgb gP cvGsP n (by omega) m a cgo cgl rco rcl cvGs recCls cvGsP hC hG hrc hcg hcg hrc hA hgP hcvGsP
    hcvGsP hie
  refine RefE.lastE (fun _ => crraE.k_class_recs_rules_ok_go.none ..)
    (fun _ => crraE.k_class_recs_rules_ok_go.arm1 ..) id h fun _ _ _ _ hR =>
    ⟨hR.stage, hR.grow, ⟨by simpa using hR.dec.1, by simpa using hR.dec.2⟩, hR.abs, hR.core⟩

include hq hApd in
/-- **`class_recs_rules_ok` refines `classRecsRulesOk`** under `StageC` (the inputs' denotations as
con-ron's `classRecsRulesOk_spec` asks; `crra_ref`'s ok half). -/
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
  refine triple_post (RefE.triple (crraE_spec p hp n s₀ visT visR g rco rcl cgo cgl)
    (crra_ref hq hApd hp n hn henv visT visR feR (env₂ := env₂) g rco rcl cgo cgl G recCls cvGs hC hG hns hrc
      hrcb hcg hcgb hA hgP hcvGsP hie)) ?_
  rintro r s' ⟨hl, x, a', run, hR⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, ⟨by rw [hst]; exact hR.stage, hR.grow, by rw [hres]; exact hR.dec⟩, hR.abs⟩

include hq hApd hnv hcE hU in
/-- **`class_recs_rules_ok`'s error claim** (the hypotheses of `classRecsRulesOk_refinesC`; `crra_ref`'s
error half): a failing call of class `1`/`2` claims that the twin's `classRecsRulesOk` fails. -/
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
      (ConRon.Arena.classRecsRulesOk V visT.toNat feR G recCls cvGs cvGs recCls) s₀ a₀ :=
  RefE.coreSpecE (crraE_spec p hP n s₀ visT visR g rco rcl cgo cgl) hnv { nv := hnv, core := hcE, uce := hU }
    (crra_ref hq hApd hP n hn henv visT visR feR (env₂ := env₂) g rco rcl cgo cgl G recCls cvGs hC hG hns hrc
      hrcb hcg hcgb hA hgP hcvGsP hie)

end sims

end L.Ind

end
