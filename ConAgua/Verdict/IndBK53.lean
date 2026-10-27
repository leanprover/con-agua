import ConAgua.Arena.IndT.RecCheckK53
import ConAgua.Arena.Verdict
import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree

/-!
# Error refinement of `target_k53`, `target_k53_heads` (lane `verdicts-b`, helper `ib`)

`target_k53_args` (whose model the generator cannot produce: its `grind` fails) is a hypothesis
(`TkaE`), in `tkaW_okC`'s shape.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dShape dMajor)
open ConRon.Bridge (CoreStep denote_ext denoteEList_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **`target_k53_args`' error claim** (hypothesis; `tkaW_okC`'s hypotheses). -/
def TkaE (p : Prog) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (env : ConLeche.Env) : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (s₀ : St) (a : AState) (q fto ftl Mc ip usp lao lal mao mal : Word)
    (bs : BlockShape) (formerTys : List EIdx) (TM : TargetMajor) (la ma : List EIdx)
    {pP : ConLeche.BlockShape} {formerTysP laP maP : List ConLeche.Expr} {McP : ConLeche.TargetMajor}
    {I'P : ConLeche.Name} {us'P : List ConLeche.Level},
    StageC dn vis fe env s₀.mem a → AbsOK s₀.mem → BSOK s₀.mem q.toNat bs →
    decHL s₀.mem fto.toNat ftl.toNat = some formerTys → fto.toNat + ftl.toNat ≤ iwTop s₀.mem →
    DecB (fun m => decTM m Mc.toNat) s₀.mem TM → H ip → H usp → HSl0 s₀.mem lao lal la →
    HSl0 s₀.mem mao mal ma → RcMR s₀.mem →
    dShape a.store bs = some pP → Frontend.denoteEList a.store formerTys = some formerTysP →
    dMajor a.store TM = some McP → denoteN a.store.ns (decI ip) = some I'P →
    denoteLs a.store.lss (decI usp) = some us'P → Frontend.denoteEList a.store la = some laP →
    Frontend.denoteEList a.store ma = some maP → (∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t) →
    ConLeche.Cached.TargetMajScoped McP →
    CoreSpecE p n "target_k53_args" [vis, q, fto, ftl, Mc, ip, usp, lao, lal, mao, mal]
      (tkArgs fe bs formerTys TM (decI ip) (decI usp) la ma) s₀ a

l_model tkhE_spec (p : Prog) (hf : p.lookup "target_k53_heads" = some targetK53Heads)
  fns [hf ↦ tkhE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] errors

l_model tkE_spec (p : Prog) (hf : p.lookup "target_k53" = some targetK53)
  fns [hf ↦ tkE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] errors

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hnv : closedNV p _root_.L.Checker.nvFns = true) (hTka : TkaE p dn vis fe env)

include hnv hTka in
/-- **`target_k53_heads`' model error claim** (`tkhW_okC`'s hypotheses). -/
theorem tkhE_claim (L : K53Look p) (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    {q fto ftl Mc leafW majDom : Word} {bs : BlockShape} {formerTys : List EIdx} {TM : TargetMajor}
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
    ∀ e, tkhE p n m vis q fto ftl Mc leafW majDom = .error e →
      ErrClaim (tkHeads fe bs formerTys TM (decE leafW) (decE majDom)) a e := by
  intro e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hS := hC.stage
  obtain _ | n := n
  · simp only [tkhE] at he
    cases he
    exact ErrClaim.of_cls0 Err.cls_outOfFuel
  rw [tkhE.arm1] at he
  cases h1 : callE p n "get_app_fn_f" [CWF, leafW] m with
  | error e1 =>
    rw [h1, tkhE.k_get_app_fn_f.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h1
  | ok q1 =>
  obtain ⟨rl, m1⟩ := q1
  rw [h1, tkhE.k_get_app_fn_f.arm1] at he
  obtain ⟨s1, hs1, -, h1m⟩ := triple_of_callW (gafF_spec p L.ad n ⟨m, Locals.init []⟩ [CWF, leafW])
    (callW_of_callE h1)
  subst hs1
  dsimp only at h1m
  obtain ⟨lh, a1, run1, hS1, hg1, hlhH, hlhD⟩ := gafF_ok dn vis fe CWF leafW hl m s1.mem a rl h1m hS
  rw [CWF_eq, ← decE_eq] at run1
  rw [← hlhD, ← decE_eq] at run1
  have hP1 := hP.fr (MFr.ofGafF h1m)
  have hA1 := gafF_afr h1m hA
  obtain ⟨e1, hlh⟩ := ConRon.Bridge.Inductives.getAppFn_run hC.check.state hlwP run1
  subst a1
  have hC1 := hC.of_pstep hS1 hA1 (PStep.refl hC.check.state)
  rw [tkHeads]
  refine ErrClaim.bind_right run1 ?_
  cases h2 : callE p n "get_app_fn_f" [CWF, majDom] s1.mem with
  | error e2 =>
    rw [h2, tkhE.k_get_app_fn_f_2.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h2
  | ok q2 =>
  obtain ⟨rm, m2⟩ := q2
  obtain ⟨s2, hs2, -, h2m⟩ := triple_of_callW (gafF_spec p L.ad n ⟨s1.mem, Locals.init []⟩ [CWF, majDom])
    (callW_of_callE h2)
  subst hs2
  dsimp only at h2m
  obtain ⟨mh, a2, run2, hS2, hg2, hmhH, hmhD⟩ := gafF_ok dn vis fe CWF majDom hmj s1.mem s2.mem a rm h2m hS1
  rw [CWF_eq, ← decE_eq] at run2
  rw [← hmhD, ← decE_eq] at run2
  have hP2 := hP1.fr (MFr.ofGafF h2m)
  have hA2 := gafF_afr h2m hA1
  obtain ⟨e2, hmh⟩ := ConRon.Bridge.Inductives.getAppFn_run hC.check.state hmdP run2
  subst a2
  have hC2 := hC1.of_pstep hS2 hA2 (PStep.refl hC.check.state)
  have hg12 := hg1.trans hg2
  refine ErrClaim.bind_right run2 ?_
  by_cases t1 : rl.headD 0 >>> 28 ≠ 3
  · rw [h2, tkhE.k_get_app_fn_f_2.arm1 p n vis q fto ftl Mc leafW majDom _ _ _ t1] at he
    cases he
  by_cases t2 : rm.headD 0 >>> 28 ≠ 3
  · rw [h2, tkhE.k_get_app_fn_f_2.arm2 p n vis q fto ftl Mc leafW majDom _ _ _ (by simpa using t1) t2] at he
    cases he
  have t1' : rl.headD 0 >>> 28 = 3 := by simpa using t1
  have t2' : rm.headD 0 >>> 28 = 3 := by simpa using t2
  rw [h2, tkhE.k_get_app_fn_f_2.arm3 p n vis q fto ftl Mc leafW majDom _ _ _ t1' t2'] at he
  -- `e_view` of the leaf's head
  cases h3 : callE p n "e_view" [rl.headD 0] s2.mem with
  | error e3 =>
    rw [h3, tkhE.k_e_view.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h3
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  obtain ⟨s3, hs3, hs3x, hne3, hr3⟩ := triple_of_callW (eView_spec p L.hv n ⟨s2.mem, Locals.init []⟩ (rl.headD 0))
    (callW_of_callE h3)
  subst hs3x
  dsimp only at hr3 hs3
  subst hr3 hs3
  rw [h3, tkhE.k_e_view.arm1] at he
  cases h4 : callE p n "e_view" [rm.headD 0] s2.mem with
  | error e4 =>
    rw [h4, tkhE.k_e_view_2.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h4
  | ok q4 =>
  obtain ⟨r4, m4⟩ := q4
  obtain ⟨s4, hs4, hs4x, hne4, hr4⟩ := triple_of_callW (eView_spec p L.hv n ⟨s2.mem, Locals.init []⟩ (rm.headD 0))
    (callW_of_callE h4)
  subst hs4x
  dsimp only at hr4 hs4
  subst hr4 hs4
  rw [h4, tkhE.k_e_view_2.arm1] at he
  obtain ⟨vr1, hipH, husH⟩ := viewConstW hS2.1.arena.1 hne3 t1'
  obtain ⟨vr2, hiiH, -⟩ := viewConstW hS2.1.arena.1 hne4 t2'
  generalize hip : (eViewW s2.mem (rl.headD 0)).tail.headD 0 = ip at he vr1 hipH
  generalize hus : (eViewW s2.mem (rl.headD 0)).tail.tail.headD 0 = usp at he vr1 husH
  generalize hii : (eViewW s2.mem (rm.headD 0)).tail.headD 0 = ii at he vr2 hiiH
  have c1 : (decE (rl.headD 0)).tag = ETag.const := (decE_tag_const _ hlhH).mpr t1'
  have c2 : (decE (rm.headD 0)).tag = ETag.const := (decE_tag_const _ hmhH).mpr t2'
  have ct1 : ((decE (rl.headD 0)).tag == ETag.const) = true := by rw [beq_iff_eq]; exact c1
  have ct2 : ((decE (rm.headD 0)).tag == ETag.const) = true := by rw [beq_iff_eq]; exact c2
  obtain ⟨-, hv1⟩ := ConRon.Bridge.Inductives.viewConst_run vr1
  obtain ⟨I'P, us'P, -, hI', hus'⟩ := ConRon.Bridge.denote_const_inv hC.check.state.wf
    (ConRon.Bridge.view_of_viewConst_tag ct1 hv1.symm) hlh
  rw [ct1, ct2]
  simp only [Bool.and_self, ite_true]
  refine ErrClaim.bind_right vr1 ?_
  refine ErrClaim.bind_right vr2 ?_
  dsimp only
  cases h5 : callE p n "get_app_args_f" [CWF, leafW] s2.mem with
  | error e5 =>
    rw [h5, tkhE.k_get_app_args_f.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h5
  | ok q5 =>
  obtain ⟨ra, m5⟩ := q5
  rw [h5, tkhE.k_get_app_args_f.arm1] at he
  obtain ⟨s5, hs5, -, h5m⟩ := triple_of_callW (gaaF_spec p L.ad n ⟨s2.mem, Locals.init []⟩ [CWF, leafW])
    (callW_of_callE h5)
  subst hs5
  dsimp only at h5m
  obtain ⟨la, a3, run3, hS3, hg3, hla, hlab⟩ := gaaF_ok dn vis fe CWF leafW hl s2.mem s5.mem a ra h5m hS2
  rw [CWF_eq, ← decE_eq] at run3
  have hP3 := hP2.fr (MFr.ofGaaF h5m)
  have hA3 := gaaF_afr h5m hA2
  obtain ⟨e3, hlaP⟩ := ConRon.Bridge.Inductives.getAppArgs_run hC.check.state hlwP run3
  subst a3
  refine ErrClaim.bind_right run3 ?_
  cases h6 : callE p n "get_app_args_f" [CWF, majDom] s5.mem with
  | error e6 =>
    rw [h6, tkhE.k_get_app_args_f_2.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h6
  | ok q6 =>
  obtain ⟨rb, m6⟩ := q6
  obtain ⟨s6, hs6, -, h6m⟩ := triple_of_callW (gaaF_spec p L.ad n ⟨s5.mem, Locals.init []⟩ [CWF, majDom])
    (callW_of_callE h6)
  subst hs6
  dsimp only at h6m
  obtain ⟨ma, a4, run4, hS4, hg4, hma, hmab⟩ := gaaF_ok dn vis fe CWF majDom hmj s5.mem s6.mem a rb h6m hS3
  rw [CWF_eq, ← decE_eq] at run4
  have hP4 := hP3.fr (MFr.ofGaaF h6m)
  have hA4 := gaaF_afr h6m hA3
  obtain ⟨e4, hmaP⟩ := ConRon.Bridge.Inductives.getAppArgs_run hC.check.state hmdP run4
  subst a4
  refine ErrClaim.bind_right run4 ?_
  have hC4 := hC2.of_pstep hS4 hA4 (PStep.refl hC.check.state)
  have hg14 := (hg12.trans hg3).trans hg4
  simp only [getD_zero, getD_one, Nat.zero_add] at hla hlab hma hmab
  have hla4 : HSl0 s6.mem (ra.headD 0) (ra.tail.headD 0) la := (HSl0.of hla hlab).grow hg4
  have hma4 : HSl0 s6.mem (rb.headD 0) (rb.tail.headD 0) ma := HSl0.of hma hmab
  by_cases hi : ip ≠ ii
  · rw [h6, tkhE.k_get_app_args_f_2.arm1 p n vis q fto ftl Mc ip usp ii _ _ _ _ hi] at he
    cases he
  have hii' : ip = ii := by simpa using hi
  subst hii'
  have hlen1 : la.length = (ra.tail.headD 0).toNat := hla4.len
  have hlen2 : ma.length = (rb.tail.headD 0).toNat := hma4.len
  by_cases hl2 : ra.tail.headD 0 ≠ rb.tail.headD 0
  · rw [h6, tkhE.k_get_app_args_f_2.arm2 p n vis q fto ftl Mc ip usp ip _ _ _ _ rfl hl2] at he
    cases he
  have hl2' : ra.tail.headD 0 = rb.tail.headD 0 := by simpa using hl2
  rw [h6, tkhE.k_get_app_args_f_2.arm3 p n vis q fto ftl Mc ip usp ip _ _ _ _ rfl hl2'] at he
  have hll : (la.length == ma.length) = true := by
    simp only [beq_iff_eq, hlen1, hlen2]; exact congrArg UInt64.toNat hl2'
  simp only [beq_self_eq_true, hll, Bool.and_self, Bool.not_true, Bool.false_eq_true, ite_false]
  cases h7 : callE p n "target_k53_args" [vis, q, fto, ftl, Mc, ip, usp, ra.headD 0, ra.tail.headD 0, rb.headD 0,
      rb.tail.headD 0] s6.mem with
  | error e7 =>
    rw [h7, tkhE.k_target_k53_args.none] at he
    cases he
    exact CoreSpecE.of_callE (hTka n (by omega) ⟨s6.mem, Locals.init []⟩ a q fto ftl Mc ip usp (ra.headD 0)
      (ra.tail.headD 0) (rb.headD 0) (rb.tail.headD 0) bs formerTys TM la ma hC4 hA4
      (hbs.grow hg14) (by rw [decHL_grow hg14 hftb]; exact hft) (by dsimp only; have := hg14.1; omega)
      (hMc.grow (decTM_mono _) hg14) hipH husH hla4 hma4 hP4 hsh hftP hMcP hI' hus' hlaP hmaP hformer hMs) h7
  | ok q7 =>
    rw [h7, tkhE.k_target_k53_args.arm1] at he
    cases he

include hnv hTka in
/-- **`target_k53_heads`' error claim** (every fuel; `tkhW_okC`'s hypotheses). -/
theorem targetK53Heads_claim (L : K53Look p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a : AState)
    (q fto ftl Mc leafW majDom : Word) (bs : BlockShape) (formerTys : List EIdx) (TM : TargetMajor)
    (hC : StageC dn vis fe env s₀.mem a) (hA : AbsOK s₀.mem)
    (hbs : BSOK s₀.mem q.toNat bs) (hft : decHL s₀.mem fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop s₀.mem) (hMc : DecB (fun m => decTM m Mc.toNat) s₀.mem TM)
    (hl : H leafW) (hmj : H majDom) (hP : RcMR s₀.mem)
    {pP : ConLeche.BlockShape} {formerTysP : List ConLeche.Expr} {McP : ConLeche.TargetMajor}
    {lwP mdP : ConLeche.Expr}
    (hsh : dShape a.store bs = some pP)
    (hftP : Frontend.denoteEList a.store formerTys = some formerTysP)
    (hMcP : dMajor a.store TM = some McP)
    (hlwP : denoteE a.store (decE leafW) = some lwP) (hmdP : denoteE a.store (decE majDom) = some mdP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ConLeche.Cached.TargetMajScoped McP) :
    CoreSpecE p n "target_k53_heads" [vis, q, fto, ftl, Mc, leafW, majDom]
      (tkHeads fe bs formerTys TM (decE leafW) (decE majDom)) s₀ a :=
  CoreSpecE.of_runs fun e hc => by
    by_cases hk0 : e.cls = 0
    · exact ErrClaim.of_cls0 hk0
    exact tkhE_claim hnv hTka L n hn hC hA hbs hft hftb hMc hl hmj hP hsh hftP hMcP hlwP hmdP hformer hMs e
      (triple_of_callE_err (tkhE_spec p L.tkh n s₀ vis q fto ftl Mc leafW majDom) hc (Err.code_ne_of_cls hk0))

include hnv hTka in
/-- **`target_k53`'s model error claim** (`tkW_okC`'s hypotheses). -/
theorem tkE_claim (L : K53Look p) (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    {q fto ftl Mc teo tel majDom f : Word} {bs : BlockShape} {formerTys : List EIdx} {TM : TargetMajor}
    {tele : List EIdx}
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
    ∀ e, tkE p n m vis q fto ftl Mc teo tel majDom f = .error e →
      ErrClaim (ConRon.Arena.targetK53 V fe bs formerTys TM tele (decE majDom) (decE f)) a e := by
  intro e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hS := hC.stage
  obtain _ | n := n
  · simp only [tkE] at he
    cases he
    exact ErrClaim.of_cls0 Err.cls_outOfFuel
  rw [tkE.arm1] at he
  rw [tk53_eq]
  cases h1 : callE p n "strip_pis" [tel, f] m with
  | error e1 =>
    rw [h1, tkE.k_strip_pis.none] at he
    cases he
    exact ErrClaim.bind_left (ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h1)
  | ok q1 =>
  obtain ⟨rs, m1⟩ := q1
  obtain ⟨s1, hs1, -, h1m⟩ := triple_of_callW (stripPis_specF p L.strip n ⟨m, Locals.init []⟩ tel f)
    (callW_of_callE h1)
  subst hs1
  dsimp only at h1m
  obtain ⟨o, a1, run1, hS1, hg1, hd1⟩ := stripF_pis_ok dn vis fe tel f hf m s1.mem a rs h1m hS
  rw [← decE_eq, ← htl.len] at run1
  have hP1 := hP.fr (MFr.ofStripF h1m)
  have hA1 := stripF_afr h1m hA
  obtain ⟨e1, hbp⟩ := ConRon.Bridge.Inductives.stripPis_pstep hC.check.state hfP run1
  subst a1
  have hC1 := hC.of_pstep hS1 hA1 (PStep.refl hC.check.state)
  refine ErrClaim.bind_right run1 ?_
  rcases o with _ | ⟨teleW, leafW⟩
  · have h0 : rs.headD 0 = 0 := hd1
    rw [h1, tkE.k_strip_pis.arm1 p n vis q fto ftl Mc teo tel majDom _ _ h0] at he
    cases he
  obtain ⟨twP, lwP, -, htw, hlw⟩ := ConRon.Bridge.Inductives.denoteBP_some hbp
  obtain ⟨h0, ⟨hdl, hbl⟩, hlwH, hlwD⟩ := hd1
  rw [h1, tkE.k_strip_pis.arm2 p n vis q fto ftl Mc teo tel majDom _ _ (by rw [h0]; decide)] at he
  simp only [show (1 + 1 : Nat) = 2 from rfl, getD_one, getD_two] at hdl hbl
  have hl3 : (rs.drop 3).headD 0 = rs.tail.tail.tail.headD 0 := by
    rcases rs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
  rw [hl3] at hlwH hlwD
  dsimp only
  cases h2 : callE p n "target_k53_tele" [rs.tail.headD 0, rs.tail.tail.headD 0, teo, tel] s1.mem with
  | error e2 =>
    rw [h2, tkE.k_target_k53_tele.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h2
  | ok q2 =>
  obtain ⟨rt, m2⟩ := q2
  obtain ⟨s2, hs2, -, h2m⟩ := triple_of_callW (tte_spec p L n ⟨s1.mem, Locals.init []⟩ (rs.tail.headD 0)
    (rs.tail.tail.headD 0) teo tel) (callW_of_callE h2)
  subst hs2
  dsimp only at h2m
  obtain ⟨c1, a2, run2, hc1, hS2, hg2, hP2⟩ := tteW_ok dn fe vis n h2m hS1 (HSl0.of hdl hbl) (htl.grow hg1) hP1
  have hA2 := tteW_afr h2m hA1
  have q2 := tkTele_cstep hC.check htw htlP run2
  have hC2 := hC1.of_cstep hS2 hA2 q2
  have hg12 := hg1.trans hg2
  refine ErrClaim.bind_right run2 ?_
  by_cases hz : rt.headD 0 = 0
  · rw [h2, tkE.k_target_k53_tele.arm1 p n vis q fto ftl Mc majDom _ _ _ hz] at he
    cases he
  rw [h2, tkE.k_target_k53_tele.arm2 p n vis q fto ftl Mc majDom _ _ _ hz] at he
  have : c1 = true := by rw [← hc1]; simpa using hz
  subst this
  simp only [ite_true]
  rw [← decE_eq] at hlwD
  cases h3 : callE p n "target_k53_heads" [vis, q, fto, ftl, Mc, rs.tail.tail.tail.headD 0, majDom] s2.mem with
  | error e3 =>
    rw [h3, tkE.k_target_k53_heads.none] at he
    cases he
    have := CoreSpecE.of_callE (targetK53Heads_claim hnv hTka L n (by omega) ⟨s2.mem, Locals.init []⟩ a2 q fto ftl Mc
      (rs.tail.tail.tail.headD 0) majDom bs formerTys TM hC2 hA2
      (hbs.grow hg12) (by rw [decHL_grow hg12 hftb]; exact hft) (by dsimp only; have := hg12.1; omega)
      (hMc.grow (decTM_mono _) hg12) hlwH hmj hP2
      (ConRon.Bridge.Inductives.dShape_ext q2.ext _ _ hsh) (denoteEList_ext q2.ext _ _ hftP)
      (ConRon.Bridge.Inductives.dMajor_ext q2.ext _ _ hMcP) (by rw [hlwD]; exact denote_ext hlw q2.ext)
      (denote_ext hmdP q2.ext) hformer hMs) h3
    rw [hlwD] at this
    exact this
  | ok q3 =>
    rw [h3, tkE.k_target_k53_heads.arm1] at he
    cases he

include hnv hTka in
/-- **`target_k53`'s error claim** (every fuel; `tkW_okC`'s hypotheses). -/
theorem targetK53_claim (L : K53Look p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) (a : AState)
    (q fto ftl Mc teo tel majDom f : Word) (bs : BlockShape) (formerTys : List EIdx) (TM : TargetMajor)
    (tele : List EIdx) (hC : StageC dn vis fe env s₀.mem a) (hA : AbsOK s₀.mem)
    (hbs : BSOK s₀.mem q.toNat bs) (hft : decHL s₀.mem fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop s₀.mem) (hMc : DecB (fun m => decTM m Mc.toNat) s₀.mem TM)
    (htl : HSl0 s₀.mem teo tel tele) (hmj : H majDom) (hf : H f) (hP : RcMR s₀.mem)
    {pP : ConLeche.BlockShape} {formerTysP teleP : List ConLeche.Expr} {McP : ConLeche.TargetMajor}
    {mdP fP : ConLeche.Expr}
    (hsh : dShape a.store bs = some pP)
    (hftP : Frontend.denoteEList a.store formerTys = some formerTysP)
    (hMcP : dMajor a.store TM = some McP)
    (htlP : Frontend.denoteEList a.store tele = some teleP)
    (hmdP : denoteE a.store (decE majDom) = some mdP) (hfP : denoteE a.store (decE f) = some fP)
    (hformer : ∀ t ∈ formerTysP, ConLeche.Expr.WScoped 0 t)
    (hMs : ConLeche.Cached.TargetMajScoped McP) :
    CoreSpecE p n "target_k53" [vis, q, fto, ftl, Mc, teo, tel, majDom, f]
      (ConRon.Arena.targetK53 V fe bs formerTys TM tele (decE majDom) (decE f)) s₀ a :=
  CoreSpecE.of_runs fun e hc => by
    by_cases hk0 : e.cls = 0
    · exact ErrClaim.of_cls0 hk0
    exact tkE_claim hnv hTka L n hn hC hA hbs hft hftb hMc htl hmj hf hP hsh hftP hMcP htlP hmdP hfP
      hformer hMs e
      (triple_of_callE_err (tkE_spec p L.tk n s₀ vis q fto ftl Mc teo tel majDom f) hc (Err.code_ne_of_cls hk0))

end sims

end L.Ind
