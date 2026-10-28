import ConAgua.Verdict.IndBTka
import ConAgua.Arena.IndT.RecGen19
import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen

/-!
# `target_k53_heads`, `target_k53`: one model and one refinement each, for both outcomes

`tkhE`, `tkE` (`l_model … unified`): `target_k53_args` and `target_k53_heads` through their
unified models (`tkaE`, `tkhE`), the callees outside the verdict closure (`get_app_fn_f`,
`get_app_args_f`, `e_view`, `strip_pis`, `target_k53_tele`) through their `Option` models.
`tkh_ref` and `tk_ref` refine `tkHeads` and `targetK53` for both outcomes (`tka_ref` below them);
`tk_ref`'s ok half is `targetK53_refinesC` and `class_nodes_agree`'s ok refinement (`RecGen23`,
through the run), its error half `class_nodes_agree`'s refinement (`cna_ref`, `RecGen23`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dShape dMajor)
open ConRon.Bridge (CoreStep denote_ext denoteEList_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

-- `finish (gen := 20)`: the generation depth (the default 8 leaves four paths open; `simp […]`
-- passes too, about 1 s slower)
l_model tkhE_spec (p : Prog) (hL : K53Look p)
  fns [hL.tkh ↦ tkhE]
  specs [gafF_spec p hL.ad n, gaaF_spec p hL.ad n, eView_spec p hL.hv n, tkaE_spec p hL n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  finish [] gen 20 heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model tkE_spec (p : Prog) (hL : K53Look p)
  fns [hL.tk ↦ tkE]
  specs [stripPis_specF p hL.strip n, tte_spec p hL n, tkhE_spec p hL n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq henv in
/-- **`target_k53_heads` refines `tkHeads`, both outcomes** (twin side: con-ron's
`targetK53_spec`, the heads' part: read-only steps, then `tka_ref`). -/
theorem tkh_ref (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState} {q fto ftl Mc leafW majDom : Word}
    {bs : BlockShape} {formerTys : List EIdx} {TM : TargetMajor}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hbs : BSOK m q.toNat bs) (hft : decHL m fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop m) (hMc : DecB (fun m => decTM m Mc.toNat) m TM)
    (hl : H leafW) (hmj : H majDom) (hP : RcMR m)
    {pP : ConLeche.BlockShape} {formerTysP : List ConLeche.Expr} {McP : ConLeche.TargetMajor}
    {lwP mdP : ConLeche.Expr}
    (hsh : dShape a.store bs = some pP)
    (hftP : Frontend.denoteEList a.store formerTys = some formerTysP)
    (hMcP : dMajor a.store TM = some McP)
    (hlwP : denoteE a.store (decE leafW) = some lwP) (hmdP : denoteE a.store (decE majDom) = some mdP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ConLeche.Cached.TargetMajScoped McP) :
    RefE (VerdictCtx p) (tkhE p n m vis q fto ftl Mc leafW majDom)
      (tkHeads fe bs formerTys TM (decE leafW) (decE majDom)) a
      (fun v c a' => TcmPost dn vis fe env m v.1 v.2 c a') := by
  have hS := hC.stage
  obtain _ | n := n
  · rw [tkhE.eq_1]; exact RefE.of_cls0 (by simp)
  rw [tkhE.arm1]
  unfold tkHeads
  -- `get_app_fn_f` of the leaf and of the major's domain
  rcases h1 : gafF m [CWF, leafW] with _ | ⟨rl, m1⟩
  · rw [liftE_none, tkhE.k_get_app_fn_f.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, tkhE.k_get_app_fn_f.arm1]
  obtain ⟨lh, a1, run1, hS1, hg1, hlhH, hlhD⟩ := gafF_ok dn vis fe CWF leafW hl m m1 a rl h1 hS
  rw [CWF_eq, ← decE_eq] at run1
  rw [← hlhD, ← decE_eq] at run1
  have hP1 := hP.fr (MFr.ofGafF h1)
  have hA1 := gafF_afr h1 hA
  obtain ⟨e1, hlh⟩ := ConRon.Bridge.Inductives.getAppFn_run hC.check.state hlwP run1
  subst a1
  have hC1 := hC.of_pstep hS1 hA1 (PStep.refl hC.check.state)
  refine RefE.bind_right run1 ?_
  rcases h2 : gafF m1 [CWF, majDom] with _ | ⟨rm, m2⟩
  · rw [liftE_none, tkhE.k_get_app_fn_f_2.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨mh, a2, run2, hS2, hg2, hmhH, hmhD⟩ := gafF_ok dn vis fe CWF majDom hmj m1 m2 a rm h2 hS1
  rw [CWF_eq, ← decE_eq] at run2
  rw [← hmhD, ← decE_eq] at run2
  have hP2 := hP1.fr (MFr.ofGafF h2)
  have hA2 := gafF_afr h2 hA1
  obtain ⟨e2, hmh⟩ := ConRon.Bridge.Inductives.getAppFn_run hC.check.state hmdP run2
  subst a2
  have hC2 := hC1.of_pstep hS2 hA2 (PStep.refl hC.check.state)
  have hg12 := hg1.trans hg2
  refine RefE.bind_right run2 ?_
  -- the heads' tags
  by_cases t1 : rl.headD 0 >>> 28 ≠ 3
  · rw [tkhE.k_get_app_fn_f_2.arm1 (hc1 := t1)]
    have : ¬ (decE (rl.headD 0)).tag = ETag.const := fun e => t1 ((decE_tag_const _ hlhH).mp e)
    have hb : ((decE (rl.headD 0)).tag == ETag.const) = false := by rw [beq_eq_false_iff_ne]; exact this
    rw [hb, Bool.false_and]
    exact RefE.ret (y := false) rfl ⟨rfl, hC2, hg12, hP2, hA2⟩
  have t1' : rl.headD 0 >>> 28 = 3 := by simpa using t1
  by_cases t2 : rm.headD 0 >>> 28 ≠ 3
  · rw [tkhE.k_get_app_fn_f_2.arm2 (hc1 := t1') (hc2 := t2)]
    have : ¬ (decE (rm.headD 0)).tag = ETag.const := fun e => t2 ((decE_tag_const _ hmhH).mp e)
    have hb : ((decE (rm.headD 0)).tag == ETag.const) = false := by rw [beq_eq_false_iff_ne]; exact this
    rw [hb, Bool.and_false]
    exact RefE.ret (y := false) rfl ⟨rfl, hC2, hg12, hP2, hA2⟩
  have t2' : rm.headD 0 >>> 28 = 3 := by simpa using t2
  -- `e_view` of both heads
  by_cases v1 : eViewW m2 (rl.headD 0) = []
  · rw [tkhE.k_get_app_fn_f_2.arm3 (hc1 := t1') (hc2 := t2') (hc3 := v1)]; exact RefE.of_cls0 (by simp)
  by_cases v2 : eViewW m2 (rm.headD 0) = []
  · rw [tkhE.k_get_app_fn_f_2.arm4 (hc1 := t1') (hc2 := t2') (hc3 := v1) (hc4 := v2)]
    exact RefE.of_cls0 (by simp)
  rw [tkhE.k_get_app_fn_f_2.arm5 (hc1 := t1') (hc2 := t2') (hc3 := v1) (hc4 := v2)]
  obtain ⟨vr1, hipH, husH⟩ := viewConstW hS2.1.arena.1 v1 t1'
  obtain ⟨vr2, hiiH, -⟩ := viewConstW hS2.1.arena.1 v2 t2'
  generalize hip : (eViewW m2 (rl.headD 0)).tail.headD 0 = ip at vr1 hipH ⊢
  generalize hus : (eViewW m2 (rl.headD 0)).tail.tail.headD 0 = usp at vr1 husH ⊢
  generalize hii : (eViewW m2 (rm.headD 0)).tail.headD 0 = ii at vr2 hiiH ⊢
  have c1 : (decE (rl.headD 0)).tag = ETag.const := (decE_tag_const _ hlhH).mpr t1'
  have c2 : (decE (rm.headD 0)).tag = ETag.const := (decE_tag_const _ hmhH).mpr t2'
  have ct1 : ((decE (rl.headD 0)).tag == ETag.const) = true := by rw [beq_iff_eq]; exact c1
  have ct2 : ((decE (rm.headD 0)).tag == ETag.const) = true := by rw [beq_iff_eq]; exact c2
  obtain ⟨-, hv1⟩ := ConRon.Bridge.Inductives.viewConst_run vr1
  obtain ⟨I'P, us'P, -, hI', hus'⟩ := ConRon.Bridge.denote_const_inv hC.check.state.wf
    (ConRon.Bridge.view_of_viewConst_tag ct1 hv1.symm) hlh
  rw [ct1, ct2]
  simp only [Bool.and_self, ite_true]
  refine RefE.bind_right vr1 (RefE.bind_right vr2 ?_)
  dsimp only
  -- `get_app_args_f` of the leaf and of the major's domain
  rcases h3 : gaaF m2 [CWF, leafW] with _ | ⟨ra, m3⟩
  · rw [liftE_none, tkhE.k_get_app_args_f.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, tkhE.k_get_app_args_f.arm1]
  obtain ⟨la, a3, run3, hS3, hg3, hla, hlab⟩ := gaaF_ok dn vis fe CWF leafW hl m2 m3 a ra h3 hS2
  rw [CWF_eq, ← decE_eq] at run3
  have hP3 := hP2.fr (MFr.ofGaaF h3)
  have hA3 := gaaF_afr h3 hA2
  obtain ⟨e3, hlaP⟩ := ConRon.Bridge.Inductives.getAppArgs_run hC.check.state hlwP run3
  subst a3
  refine RefE.bind_right run3 ?_
  rcases h4 : gaaF m3 [CWF, majDom] with _ | ⟨rb, m4⟩
  · rw [liftE_none, tkhE.k_get_app_args_f_2.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨ma, a4, run4, hS4, hg4, hma, hmab⟩ := gaaF_ok dn vis fe CWF majDom hmj m3 m4 a rb h4 hS3
  rw [CWF_eq, ← decE_eq] at run4
  have hP4 := hP3.fr (MFr.ofGaaF h4)
  have hA4 := gaaF_afr h4 hA3
  obtain ⟨e4, hmaP⟩ := ConRon.Bridge.Inductives.getAppArgs_run hC.check.state hmdP run4
  subst a4
  refine RefE.bind_right run4 ?_
  have hC4 := hC2.of_pstep hS4 hA4 (PStep.refl hC.check.state)
  have hg14 := (hg12.trans hg3).trans hg4
  simp only [getD_zero, getD_one, Nat.zero_add] at hla hlab hma hmab
  have hla4 : HSl0 m4 (ra.headD 0) (ra.tail.headD 0) la := (HSl0.of hla hlab).grow hg4
  have hma4 : HSl0 m4 (rb.headD 0) (rb.tail.headD 0) ma := HSl0.of hma hmab
  -- the same class, as many arguments
  by_cases hi : ip ≠ ii
  · rw [tkhE.k_get_app_args_f_2.arm1 (hc1 := hi)]
    have : (decI ip == (decI ii : NIdx)) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact fun e => hi (decI_inj hipH hiiH e)
    exact RefE.ite_pos (by simp [this]) (RefE.ret (y := false) rfl ⟨rfl, hC4, hg14, hP4, hA4⟩)
  have hii' : ip = ii := by simpa using hi
  subst hii'
  have hlen1 : la.length = (ra.tail.headD 0).toNat := hla4.len
  have hlen2 : ma.length = (rb.tail.headD 0).toNat := hma4.len
  by_cases hl2 : ra.tail.headD 0 ≠ rb.tail.headD 0
  · rw [tkhE.k_get_app_args_f_2.arm2 (hc1 := rfl) (hc2 := hl2)]
    have : (la.length == ma.length) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq, hlen1, hlen2]
      exact fun e => hl2 (UInt64.toNat_inj.mp e)
    exact RefE.ite_pos (by simp [this]) (RefE.ret (y := false) rfl ⟨rfl, hC4, hg14, hP4, hA4⟩)
  have hl2' : ra.tail.headD 0 = rb.tail.headD 0 := by simpa using hl2
  rw [tkhE.k_get_app_args_f_2.arm3 (hc1 := rfl) (hc2 := hl2')]
  have hll : (la.length == ma.length) = true := by
    simp only [beq_iff_eq, hlen1, hlen2]; exact congrArg UInt64.toNat hl2'
  refine RefE.ite_neg (by simp [hll]) ?_
  -- `target_k53_args`
  exact RefE.mono (tka_ref hq henv n (by omega) hC4 hA4 (hbs.grow hg14)
    (by rw [decHL_grow hg14 hftb]; exact hft) (by have := hg14.1; omega)
    (hMc.grow (decTM_mono _) hg14) hipH husH hla4 hma4 hP4 hsh hftP hMcP hI' hus' hlaP hmaP hformer hMs)
    fun v c a' h => ⟨h.res, h.stage, hg14.trans h.grow, h.rc, h.abs⟩

include hq henv in
/-- **`target_k53` refines `targetK53`, both outcomes** (twin side: con-ron's `targetK53_spec`'s
proof): `stripPis`, the telescope check (`tkTele_cstep`), then `tkh_ref`. -/
theorem tk_ref (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState} {q fto ftl Mc teo tel majDom f : Word}
    {bs : BlockShape} {formerTys : List EIdx} {TM : TargetMajor} {tele : List EIdx}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hbs : BSOK m q.toNat bs) (hft : decHL m fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop m) (hMc : DecB (fun m => decTM m Mc.toNat) m TM)
    (htl : HSl0 m teo tel tele) (hmj : H majDom) (hf : H f) (hP : RcMR m)
    {pP : ConLeche.BlockShape} {formerTysP teleP : List ConLeche.Expr} {McP : ConLeche.TargetMajor}
    {mdP fP : ConLeche.Expr}
    (hsh : dShape a.store bs = some pP)
    (hftP : Frontend.denoteEList a.store formerTys = some formerTysP)
    (hMcP : dMajor a.store TM = some McP)
    (htlP : Frontend.denoteEList a.store tele = some teleP)
    (hmdP : denoteE a.store (decE majDom) = some mdP) (hfP : denoteE a.store (decE f) = some fP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ConLeche.Cached.TargetMajScoped McP) :
    RefE (VerdictCtx p) (tkE p n m vis q fto ftl Mc teo tel majDom f)
      (ConRon.Arena.targetK53 V fe bs formerTys TM tele (decE majDom) (decE f)) a
      (fun v c a' => TcmPost dn vis fe env m v.1 v.2 c a') := by
  have hS := hC.stage
  obtain _ | n := n
  · rw [tkE.eq_1]; exact RefE.of_cls0 (by simp)
  rw [tkE.arm1, tk53_eq]
  -- `strip_pis`
  rcases h1 : stripF 6 m [tel, f] with _ | ⟨rs, m1⟩
  · rw [liftE_none, tkE.k_strip_pis.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨o, a1, run1, hS1, hg1, hd1⟩ := stripF_pis_ok dn vis fe tel f hf m m1 a rs h1 hS
  rw [← decE_eq, ← htl.len] at run1
  have hP1 := hP.fr (MFr.ofStripF h1)
  have hA1 := stripF_afr h1 hA
  obtain ⟨e1, hbp⟩ := ConRon.Bridge.Inductives.stripPis_pstep hC.check.state hfP run1
  subst a1
  have hC1 := hC.of_pstep hS1 hA1 (PStep.refl hC.check.state)
  refine RefE.bind_right run1 ?_
  rcases o with _ | ⟨teleW, leafW⟩
  · have h0 : rs.headD 0 = 0 := hd1
    rw [tkE.k_strip_pis.arm1 (hc1 := h0)]
    exact RefE.ret (y := false) rfl ⟨rfl, hC1, hg1, hP1, hA1⟩
  obtain ⟨twP, lwP, -, htw, hlw⟩ := ConRon.Bridge.Inductives.denoteBP_some hbp
  obtain ⟨h0, ⟨hdl, hbl⟩, hlwH, hlwD⟩ := hd1
  rw [tkE.k_strip_pis.arm2 (hc1 := by rw [h0]; decide)]
  simp only [show (1 + 1 : Nat) = 2 from rfl, getD_one, getD_two] at hdl hbl
  have hl3 : (rs.drop 3).headD 0 = rs.tail.tail.tail.headD 0 := by
    rcases rs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
  rw [hl3] at hlwH hlwD
  dsimp only
  -- `target_k53_tele`
  rcases h2 : tteW n m1 (rs.tail.headD 0) (rs.tail.tail.headD 0) teo tel with _ | ⟨rt, m2⟩
  · rw [liftE_none, tkE.k_target_k53_tele.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨c1, a2, run2, hc1, hS2, hg2, hP2⟩ := tteW_ok dn fe vis n h2 hS1 (HSl0.of hdl hbl) (htl.grow hg1) hP1
  have hA2 := tteW_afr h2 hA1
  have q2 := tkTele_cstep hC.check htw htlP run2
  have hC2 := hC1.of_cstep hS2 hA2 q2
  have hg12 := hg1.trans hg2
  refine RefE.bind_right run2 ?_
  by_cases hz : rt.headD 0 = 0
  · rw [tkE.k_target_k53_tele.arm1 (hc1 := hz)]
    have : c1 = false := by rw [← hc1, hz]; rfl
    subst this
    exact RefE.ite_neg (by simp) (RefE.ret (y := false) rfl ⟨rfl, hC2, hg12, hP2, hA2⟩)
  rw [tkE.k_target_k53_tele.arm2 (hc1 := hz)]
  have : c1 = true := by rw [← hc1]; simpa using hz
  subst this
  refine RefE.ite_pos rfl ?_
  -- `target_k53_heads`
  rw [← decE_eq] at hlwD
  have h3 := tkh_ref hq henv n (by omega) hC2 hA2
    (hbs.grow hg12) (by rw [decHL_grow hg12 hftb]; exact hft) (by have := hg12.1; omega)
    (hMc.grow (decTM_mono _) hg12) hlwH hmj hP2
    (ConRon.Bridge.Inductives.dShape_ext q2.ext _ _ hsh) (denoteEList_ext q2.ext _ _ hftP)
    (ConRon.Bridge.Inductives.dMajor_ext q2.ext _ _ hMcP) (by rw [hlwD]; exact denote_ext hlw q2.ext)
    (denote_ext hmdP q2.ext) hformer hMs
  rw [hlwD] at h3
  exact RefE.mono h3 fun v c a' h => ⟨h.res, h.stage, hg12.trans h.grow, h.rc, h.abs⟩

include hq henv in
/-- **`target_k53` refines `targetK53`** under `StageC` (`tk_ref`'s ok half; the knot's core calls;
the inputs' denotations and scoping as con-ron's `targetK53_spec` asks). -/
@[refines ConRon.Arena.targetK53]
theorem targetK53_refinesC (L : K53Look p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (q fto ftl Mc teo tel majDom f : Word)
    (bs : BlockShape) (formerTys : List EIdx) (TM : TargetMajor) (tele : List EIdx)
    (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem) (hbs : BSOK s₀.mem q.toNat bs)
    (hft : decHL s₀.mem fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop s₀.mem)
    (hMc : DecB (fun m => decTM m Mc.toNat) s₀.mem TM) (htl : HSl0 s₀.mem teo tel tele)
    (hmj : H majDom) (hf : H f) (hP : RcMR s₀.mem)
    {pP : ConLeche.BlockShape} {formerTysP teleP : List ConLeche.Expr} {McP : ConLeche.TargetMajor}
    {mdP fP : ConLeche.Expr}
    (hsh : dShape a₀.store bs = some pP)
    (hftP : Frontend.denoteEList a₀.store formerTys = some formerTysP)
    (hMcP : dMajor a₀.store TM = some McP)
    (htlP : Frontend.denoteEList a₀.store tele = some teleP)
    (hmdP : denoteE a₀.store (decE majDom) = some mdP) (hfP : denoteE a₀.store (decE f) = some fP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ConLeche.Cached.TargetMajScoped McP) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_k53" [vis, q, fto, ftl, Mc, teo, tel, majDom, f]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.targetK53 V fe bs formerTys TM tele (decE majDom) (decE f)) a₀ ∧
      (r.headD 0 != 0) =
        AM.res (ConRon.Arena.targetK53 V fe bs formerTys TM tele (decE majDom) (decE f)) a₀ ∧
      StageC dn vis fe env s'.mem
        (AM.st (ConRon.Arena.targetK53 V fe bs formerTys TM tele (decE majDom) (decE f)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ RcMR s'.mem ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (RefE.triple (tkE_spec p L n s₀ vis q fto ftl Mc teo tel majDom f)
    (tk_ref hq henv n hn hC hA hbs hft hftb hMc htl hmj hf hP hsh hftP hMcP htlP hmdP hfP hformer hMs)) ?_
  rintro r s' ⟨hl', c, a', run, hR⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl', hok, by rw [hres]; exact hR.res, by rw [hst]; exact hR.stage, hR.grow, hR.rc, hR.abs⟩

end sims

end L.Ind
