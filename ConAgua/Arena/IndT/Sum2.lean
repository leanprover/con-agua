import ConAgua.Verdict.DeclValsE
import ConAgua.Arena.IndT.Sum1
import ConAgua.Arena.RecGenSpec.ClassFeR
import ConAgua.Arena.RecGenSpec.Rec3TmdWDecB
import ConRon.Bridge.Inductives.SumInstall
import ConAgua.L.ModelGen

/-!
# `checkSumTele.checkSumTeleSlow`, `checkSumTele` under `StageC`, both outcomes (lane `indstaget`)

The unified models of `check_sum_tele_slow` (`ctsE`) and `check_sum_tele` (`ctE`) and one
refinement each for both outcomes (`cts_ref`, `ct_ref`), from `StageC` and con-ron's preconditions
of `checkSumTele_spec` (the two constant values denote, the stored type is closed, the environment
denotes). The twin side is transcribed from that spec's `slow` arm: `whnfTelescope` (`wt_ref`, and
con-ron's `whnfTelescope_spec` on its run for the answer's denotation), the sort's intern
(`internSortE_run`), `closeTelescope` (`closeTelescope_spec`), the record write (twin side none),
`checkConstantVal` (`ccv_ref`, con-ron's `checkConstantVal_bridge` on its run for the `CoreStep`).
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- The lookups `check_sum_tele_slow`'s model reads: `whnf_telescope`'s, the sort's intern, the
telescope's closing, the record write. -/
structure CtsProg (p : Prog) : Prop extends WtProg p where
  sf : p.lookup "sort_find" = some sortFind
  sp : p.lookup "sort_push" = some sortPush
  is : p.lookup "intern_sort" = some internSort
  d : p.lookup "der_b" = some derB
  pf : p.lookup "forall_find" = some forallFind
  pp : p.lookup "forall_push" = some forallPush
  pi : p.lookup "intern_forall" = some internForallL
  mkf : p.lookup "mk_forall" = some mkForall
  ct : p.lookup "close_telescope" = some closeTelescope
  ea : p.lookup "erec_alloc" = some erecAlloc
  cn : p.lookup "cv_new" = some cvNew
  sl : p.lookup "check_sum_tele_slow" = some checkSumTeleSlowL
  ab : AbF p

/-- The lookups `check_sum_tele`'s model reads besides the slow arm's. -/
structure CtProg (p : Prog) : Prop extends CtsProg p where
  st : StripProg p
  cst : p.lookup "check_sum_tele" = some checkSumTeleL

set_option experimental.vcgen true in
/-- **The model of `check_sum_tele_slow`, both outcomes**: `whnf_telescope` and
`check_constant_val` by their unified models, the intern, the closing and the record write
(outside the verdict closure) through their `Option` models. -/
l_model ctsE_spec (p : Prog) (hV : ValProg p) (hP : CtsProg p)
  fns [hP.sl ↦ ctsE]
  specs [wtE_spec p hP.toWtProg n, internSort_spec p hP.sf hP.sp hP.is n,
    closeTelescope_spec p hP.d hP.pf hP.pp hP.pi hP.mkf hP.ct hP.ab n, cvNew_specW p hP.ea hP.cn n,
    checkConstantVal_specE p hV n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

set_option experimental.vcgen true in
/-- **The model of `check_sum_tele`, both outcomes**: `strip_pis` and `e_view` (outside the
verdict closure) through their `Option` models, the slow arm by its unified model. -/
l_model ctE_spec (p : Prog) (hV : ValProg p) (hP : CtProg p)
  fns [hP.cst ↦ ctE]
  specs [stripPis_specF p hP.st n, eView_spec p hP.view n, ctsE_spec p hV hP.toCtsProg n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hV : ValProg p)
  (hApd : ApdF p) (hCrk : CrKeep p) (hP : WtProg p)

/-- What `check_sum_tele(_slow)`'s error arms assume: `check_constant_val`'s (`VerdictCtxU`) and
`whnf_top`'s claim (`whnf_telescope`'s, `WtG`). -/
structure CtsG (p : Prog) : Prop extends VerdictCtxU p where
  whnf : WhnfTopE p

/-- What `check_sum_tele(_slow)` gives besides the twin's `(cvTa, s)`: the stage, the growth, the
new constant value as a record below `EREC`'s top (its level slice too), the sort as a word, the
walk memos. -/
structure CtsPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (w : List Word × Mem) (res : IConstantVal × LIdx) (a' : AState) : Prop where
  stage : StageC dn vis fe env w.2 a'
  grow : IWGrow m w.2
  cv : decCVp w.2 (w.1.headD 0).toNat = some res.1
  top : (w.1.headD 0).toNat + 4 ≤ erTop w.2
  lps : ∀ lo ll, nat? (erA w.2) ((w.1.headD 0).toNat + 1) = some lo →
    nat? (erA w.2) ((w.1.headD 0).toNat + 2) = some ll → lo + ll ≤ erTop w.2 ∨ ll = 0
  sort32 : (w.1.tail.headD 0).toNat < 2 ^ 32
  sort : decI (w.1.tail.headD 0) = res.2
  abs : AbsOK w.2

include hq henv hApd hCrk hP in
/-- **`check_sum_tele_slow` refines `checkSumTele.checkSumTeleSlow .verified` under `StageC`,
both outcomes** (twin side: the `slow` arm of con-ron's `checkSumTele_spec`): `whnf_telescope` by
`wt_ref`, `check_constant_val` by `ccv_ref`. -/
theorem cts_ref (k : Nat) (hk : k ≤ 2 ^ 62)
    (m : Mem) (a : AState) (cv n cvTa0 : Word) (cvv cvTa : IConstantVal)
    (hC : StageC dn vis fe env m a)
    (hcv : decCVp m cv.toNat = some cvv) (hcvb : cv.toNat + 4 ≤ erTop m)
    (hsl : ∀ lo ll, nat? (erA m) (cv.toNat + 1) = some lo → nat? (erA m) (cv.toNat + 2) = some ll →
      lo + ll ≤ erTop m ∨ ll = 0)
    (hta : decCVp m cvTa0.toNat = some cvTa) (hta4 : cvTa0.toNat + 4 ≤ erTop m) (hA : AbsOK m)
    {cvP cvTaP : ConLeche.ConstantVal} (hcvP : Frontend.denoteCV a.store cvv = some cvP)
    (hcvTaP : Frontend.denoteCV a.store cvTa = some cvTaP)
    (hws : ConLeche.Expr.WScoped 0 cvTaP.type) (hfe : ConRon.Bridge.denoteFEnv a.store fe = some env) :
    RefE (CtsG p) (ctsE p k m vis cv n cvTa0) (checkSumTele.checkSumTeleSlow V fe cvv n.toNat cvTa) a
      (fun w res a' => CtsPost dn vis fe env m w res a') := by
  have hS := hC.stage
  obtain ⟨hI1, hE1, hsz, hEs, hc⟩ := hS.iw
  cases k with
  | zero => rw [ctsE.eq_1]; exact RefE.of_cls0 rfl
  | succ k =>
  rw [ctsE.arm1]
  obtain ⟨w, hw, hw32, hwd⟩ := hd?_rdW (decCV_type hta) (by omega)
  have hw' : rdW (m.arr64 EREC) (cvTa0 + 3) = w := by
    rw [← hw]; congr 1
  rw [hw']
  have hdw : denoteE a.store (decI w) = some cvTaP.type := by
    rw [hwd]; exact ConRon.Bridge.denoteCV_type hcvTaP
  unfold checkSumTele.checkSumTeleSlow
  rw [← hwd]
  -- `whnf_telescope`
  have h1R := wt_ref hq hP henv k (by omega) m a 0 n w hC hA hw32 (by simpa using n.toNat_lt) hdw hws
  rw [show (0 : Word).toNat = 0 from rfl] at h1R
  refine RefE.bindE (fun _ => rfl) (fun hG => ⟨hG.nv, hG.whnf⟩) h1R
    fun ⟨r1, m1⟩ ⟨bs, s⟩ a1 hrun1 ⟨hC1, hg1, hd1, ht1, hs32, hs, hA1⟩ => ?_
  dsimp only [ctsE.k_whnf_telescope] at hC1 hg1 hd1 ht1 hs32 hs hA1 ⊢
  have hS1 := hC1.stage
  obtain ⟨c1, F₁, bsP, sP, -, hbs, hsP⟩ := ConRon.Bridge.Inductives.whnfTelescope_spec fe
    (ConRon.Bridge.CoreSpec.of_core rfl) henv 0 n.toNat (decI w) cvTaP.type hws a a1 (bs, s)
    hC.check ⟨hdw, hfe⟩ hrun1
  dsimp only at hbs hsP
  -- `intern_sort` (outside the verdict closure)
  refine RefE.bindLift (fun _ => rfl) fun ss m2 h2 => ?_
  obtain ⟨a2, hrun2, hS2, hg2⟩ := internSort_stage hS1 _ hs32 h2
  rw [hs] at hrun2
  refine ⟨_, _, hrun2, ?_⟩
  dsimp only [ctsE.k_intern_sort]
  refine RefE.abort0 rfl fun hss => ?_
  have hss32 : ss.toNat < 2 ^ 32 := by have : ¬ (4294967296 : Nat) ≤ ss.toNat := hss; omega
  obtain ⟨p2, hsort⟩ := ConRon.Bridge.Inductives.internSortE_run hC1.check.state hsP hrun2
  have hA2 := sointernW_afr h2 hA1
  have hC2 : StageC dn vis fe env m2 a2 := hC1.of_pstep hS2 hA2 p2
  -- `close_telescope` (outside the verdict closure)
  have hb1 : (r1.headD 0).toNat + (r1.tail.headD 0).toNat < 2 ^ 64 := by
    obtain ⟨hI, -, hsz1, -⟩ := hS1.iw; simp only [iwTop] at hI ht1 ⊢; omega
  refine RefE.bindLift (fun _ => rfl) fun rt m3 h3 => ?_
  obtain ⟨ty, a3, hrun3, hS3, hg3, ⟨hty32, htyd⟩, hA3⟩ := closeW_ok k dn fe vis m2 m3 a2 _ _ 0 ss bs rt h3
    hS2 hss32 (by rw [decHL_grow hg2 ht1]; exact hd1) hb1 (by have := hg2.iw; omega)
    (by rw [show (0 : Word).toNat = 0 from rfl]; omega) hA2
  rw [show (0 : Word).toNat = 0 from rfl] at hrun3
  obtain ⟨p3, hty⟩ := ConRon.Bridge.Inductives.closeTelescope_spec bs bsP 0 (decI ss) (.sort sP) a2 a3 ty
    hC2.check.state ⟨ConRon.Bridge.denoteEList_ext p2.ext _ _ hbs, by rw [← decE_eq]; exact hsort⟩ hrun3
  have hC3 : StageC dn vis fe env m3 a3 := hC2.of_pstep hS3 hA3 p3
  have hg13 := (hg1.trans hg2).trans hg3
  rw [← decE_eq] at hrun3
  refine ⟨_, _, hrun3, ?_⟩
  dsimp only [ctsE.k_close_telescope]
  -- `cv_new` (outside the verdict closure; no twin step)
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun q m4 h4 => ?_
  dsimp only [ctsE.k_cv_new]
  have hnat : ∀ j, j < 4 → nat? (erA m3) (cv.toNat + j) = nat? (erA m) (cv.toNat + j) := fun j hj => by
    simp only [nat?, erA]; rw [hg13.erGet _ (by omega)]
  obtain ⟨hS4, hg4, hqe, htop4, hsl4, hdq⟩ := cvNew_stage h4 hS3 (decCVp_grow hg13 hcvb hsl hcv)
    (by have := hg13.er; omega)
    (fun lo ll e1 e2 => by
      rw [show cv.toNat + 1 = cv.toNat + 1 from rfl, hnat 1 (by decide)] at e1
      rw [hnat 2 (by decide)] at e2
      have := hsl lo ll e1 e2; have := hg13.er; omega)
    hty32
  have hA4 := cvNewW_afr h4 hA3
  have hC4 : StageC dn vis fe env m4 a3 := hC3.of_pstep hS4 hA4 (PStep.refl hC3.check.state)
  have c3 := c1.trans ((p2.trans p3).toCore c1.ok)
  have hcvT : Frontend.denoteCV a3.store { cvv with type := decI (rt.headD 0) } =
      some { cvP with type := ConLeche.closeTelescope bsP 0 (.sort sP) } := by
    obtain ⟨hn, hl, -⟩ := ConRon.Bridge.denoteCV_inv hcvP
    simp only [Frontend.denoteCV, ConRon.Bridge.denoteN_ext hn c3.ext,
      ConRon.Bridge.denoteNListE_ext c3.ext _ _ hl, htyd, hty]
  have hqx : CVExt m4 q.toNat := ⟨by omega, fun lo ll e1 e2 => by
    rcases hsl4 lo ll e1 e2 with h' | h'
    · left; omega
    · right; exact h'⟩
  -- `check_constant_val`
  have h5R := ccv_ref hq hApd hCrk (n := k) (by omega) hC4.stageT (rec2DecCV_erecP hdq hqx)
    (rec3CVExt_lt hS4 hqx) (denoteCV_lps hcvT) hA4.crMemo.crOK
  rw [← htyd]
  refine RefE.bindE (fun _ => rfl) (fun hG => hG.toVerdictCtxU) h5R fun ⟨u, m5⟩ u' a5 hrun5 hP5 => ?_
  obtain ⟨c5, -⟩ := ConRon.Bridge.checkConstantVal_bridge rfl (ConRon.Bridge.CoreSpec.of_core rfl)
    hC4.check henv hcvT hrun5
  have hg5 : IWGrow m4 m5 := hP5.grow
  refine RefE.ret rfl ⟨StageC.of_T hP5.stage c5.ok, (hg13.trans hg4).trans hg5,
    ?_, ?_, ?_, by simpa using hs32, by simpa using hs, hP5.abs hA4⟩
  · simp only [List.headD]
    exact decCVp_grow hg5 (by omega) (fun lo ll e1 e2 => by have := hsl4 lo ll e1 e2; omega) hdq
  · simp only [List.headD]; have := hg5.er; omega
  · intro lo ll e1 e2
    simp only [List.headD] at e1 e2 ⊢
    have hn : ∀ j, j < 4 → nat? (erA m5) (q.toNat + j) = nat? (erA m4) (q.toNat + j) := fun j hj => by
      simp only [nat?, erA]; rw [hg5.erGet _ (by omega)]
    rw [hn 1 (by decide)] at e1; rw [hn 2 (by decide)] at e2
    have := hsl4 lo ll e1 e2; have := hg4.er; have := hg5.er; omega

include hq henv hApd hCrk hP in
/-- **`check_sum_tele` refines `checkSumTele .verified` under `StageC`, both outcomes** (twin side:
con-ron's `checkSumTele_spec`'s proof: `stripPis` leaves the twin's state, the syntactic sort is a
read, the slow arm `cts_ref`). -/
theorem ct_ref (k : Nat) (hk : k ≤ 2 ^ 62)
    (m : Mem) (a : AState) (cv n cvTa0 : Word) (cvv cvTa : IConstantVal)
    (hC : StageC dn vis fe env m a)
    (hcv : decCVp m cv.toNat = some cvv) (hcvb : cv.toNat + 4 ≤ erTop m)
    (hsl : ∀ lo ll, nat? (erA m) (cv.toNat + 1) = some lo → nat? (erA m) (cv.toNat + 2) = some ll →
      lo + ll ≤ erTop m ∨ ll = 0)
    (hta : decCVp m cvTa0.toNat = some cvTa) (hta4 : cvTa0.toNat + 4 ≤ erTop m)
    (hslTa : ∀ lo ll, nat? (erA m) (cvTa0.toNat + 1) = some lo →
      nat? (erA m) (cvTa0.toNat + 2) = some ll → lo + ll ≤ erTop m ∨ ll = 0) (hA : AbsOK m)
    {cvP cvTaP : ConLeche.ConstantVal} (hcvP : Frontend.denoteCV a.store cvv = some cvP)
    (hcvTaP : Frontend.denoteCV a.store cvTa = some cvTaP)
    (hws : ConLeche.Expr.WScoped 0 cvTaP.type) (hfe : ConRon.Bridge.denoteFEnv a.store fe = some env) :
    RefE (CtsG p) (ctE p k m vis cv n cvTa0) (checkSumTele V fe cvv n.toNat cvTa) a
      (fun w res a' => CtsPost dn vis fe env m w res a') := by
  have hS := hC.stage
  obtain ⟨hI1, hE1, hsz, hEs, hc⟩ := hS.iw
  cases k with
  | zero => rw [ctE.eq_1]; exact RefE.of_cls0 rfl
  | succ k =>
  rw [ctE.arm1]
  obtain ⟨w, hw, hw32, hwd⟩ := hd?_rdW (decCV_type hta) (by omega)
  have hw' : rdW (m.arr64 EREC) (cvTa0 + 3) = w := by
    rw [← hw]; congr 1
  rw [hw']
  have hdw : denoteE a.store (decI w) = some cvTaP.type := by
    rw [hwd]; exact ConRon.Bridge.denoteCV_type hcvTaP
  unfold checkSumTele
  rw [← hwd]
  -- `strip_pis` (outside the verdict closure)
  refine RefE.bindLift (fun _ => rfl) fun r1 m1 h1 => ?_
  obtain ⟨x, a1, hrun1, hS1, hg1, hdec⟩ := stripF_pis_ok dn vis fe n w hw32 m m1 a r1 h1 hS
  obtain ⟨ha1, -⟩ := ConRon.Bridge.Inductives.stripPis_pstep hC.check.state hdw hrun1
  rw [ha1] at hrun1 hS1
  refine ⟨_, _, hrun1, ?_⟩
  have hA1 := stripF_afr h1 hA
  have hC1 : StageC dn vis fe env m1 a := hC.of_pstep hS1 hA1 (PStep.refl hC.check.state)
  have hcv1 := decCVp_grow hg1 hcvb hsl hcv
  have hta1 := decCVp_grow hg1 hta4 hslTa hta
  have hnat : ∀ q : Word, q.toNat + 4 ≤ erTop m → ∀ j, j < 4 →
      nat? (erA m1) (q.toNat + j) = nat? (erA m) (q.toNat + j) := fun q hq j hj => by
    simp only [nat?, erA]; rw [hg1.erGet _ (by omega)]
  by_cases hf : r1.headD 0 = 1 ∧ tagW (r1.tail.tail.tail.headD 0) = 2
  · cases x with
    | none => simp only [decOLE] at hdec; rw [hf.1] at hdec; cases hdec
    | some le =>
    obtain ⟨l, e⟩ := le
    simp only [decOLE, decW0E] at hdec
    obtain ⟨-, -, hb32, hbe⟩ := hdec
    rw [drop3_eq] at hb32 hbe
    by_cases hne : eViewW m1 (r1.tail.tail.tail.headD 0) = []
    · rw [ctE.k_strip_pis.arm1 _ _ _ _ _ _ _ _ hf hne]; exact RefE.of_cls0 (by simp)
    rw [ctE.k_strip_pis.arm2 _ _ _ _ _ _ _ _ hf hne]
    obtain ⟨vv, hview, hVR⟩ := eViewW_ok m1 a hS1.check.arena.base _ hne
    have h2 := eViewW_head2 m1 _ hf.2 hne
    have htag : (decE (r1.tail.tail.tail.headD 0)).tag = ETag.sort :=
      (decE_tag_sort _ (by simpa using hb32)).mpr hf.2
    cases vv with
    | sort u =>
      obtain ⟨-, hu32, hu⟩ := hVR
      have hvs := viewSort_of_view _ _ _ htag hview
      have hx1 : (eViewW m1 (r1.tail.tail.tail.headD 0)).getD 1 0 =
          (eViewW m1 (r1.tail.tail.tail.headD 0)).tail.headD 0 := by
        cases eViewW m1 (r1.tail.tail.tail.headD 0) with
        | nil => rfl
        | cons _ t => cases t <;> rfl
      simp only []
      rw [← hbe, ← decE_eq, htag]
      simp only [beq_self_eq_true, ite_true]
      refine RefE.bind_right (viewSort_run hvs) (RefE.ret rfl ⟨hC1, hg1, by simpa using hta1,
        by simp only [List.headD]; have := hg1.er; omega,
        fun lo ll e1 e2 => by
          simp only [List.headD] at e1 e2 ⊢
          rw [hnat cvTa0 hta4 1 (by decide)] at e1; rw [hnat cvTa0 hta4 2 (by decide)] at e2
          have := hslTa lo ll e1 e2; have := hg1.er; omega,
        by simpa [hx1] using hu32, by simpa [hx1] using hu, hA1⟩)
    | _ => simp only [ViewR] at hVR <;> (rw [h2] at hVR) <;> simp at hVR
  rw [ctE.k_strip_pis.arm3 _ _ _ _ _ _ _ _ hf]
  -- the slow arm
  have hR := cts_ref hq henv hApd hCrk hP k (by omega) m1 a cv n cvTa0 cvv cvTa hC1 hcv1
    (by have := hg1.er; omega)
    (fun lo ll e1 e2 => by
      rw [hnat cv hcvb 1 (by decide)] at e1; rw [hnat cv hcvb 2 (by decide)] at e2
      have := hsl lo ll e1 e2; have := hg1.er; omega)
    hta1 (by have := hg1.er; omega) hA1 hcvP hcvTaP hws hfe
  suffices hS' : RefE (CtsG p) (ctE.k_check_sum_tele_slow p (ctsE p k m1 vis cv n cvTa0))
      (checkSumTele.checkSumTeleSlow V fe cvv n.toNat cvTa) a
      (fun w res a' => CtsPost dn vis fe env m w res a') by
    cases x with
    | none => exact hS'
    | some le =>
      obtain ⟨l, e⟩ := le
      simp only [decOLE, decW0E] at hdec
      obtain ⟨h1', -, hb32, hbe⟩ := hdec
      rw [drop3_eq] at hb32 hbe
      have hnt : ¬ (e.tag == ETag.sort) = true := by
        rw [← hbe, ← decE_eq]
        intro ht
        exact hf ⟨h1', (decE_tag_sort _ (by simpa using hb32)).mp (by simpa using ht)⟩
      simp only [hnt, Bool.false_eq_true, ite_false]
      exact hS'
  exact RefE.lastE (K := ctE.k_check_sum_tele_slow p) (fun _ => rfl) (fun _ => rfl) id hR
    fun _ _ _ _ hR2 => ⟨hR2.stage, hg1.trans hR2.grow,
    by simpa using hR2.cv, by simpa using hR2.top, by simpa using hR2.lps, by simpa using hR2.sort32,
    by simpa using hR2.sort, hR2.abs⟩

section census
variable (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
  (hv : p.lookup "e_view" = some eView)
  (hff : p.lookup "fvar_find" = some fvarFind) (hfp : p.lookup "fvar_push" = some fvarPush)
  (hif : p.lookup "intern_fvar" = some internFVar)
  (hwt : p.lookup "whnf_telescope" = some whnfTelescopeL)
  (hsf : p.lookup "sort_find" = some sortFind) (hsp : p.lookup "sort_push" = some sortPush)
  (his : p.lookup "intern_sort" = some internSort)
  (hd : p.lookup "der_b" = some derB)
  (hpf : p.lookup "forall_find" = some forallFind)
  (hpp : p.lookup "forall_push" = some forallPush) (hpi : p.lookup "intern_forall" = some internForallL)
  (hmk : p.lookup "mk_forall" = some mkForall)
  (hct : p.lookup "close_telescope" = some closeTelescope)
  (hea : p.lookup "erec_alloc" = some erecAlloc) (hcn : p.lookup "cv_new" = some cvNew)
  (hsl : p.lookup "check_sum_tele_slow" = some checkSumTeleSlowL) (hi1 : I1Prog p) (hab : AbF p)
include ha hc hsc hv hff hfp hif hwt hsf hsp his hd hpf hpp hpi hmk hct hea hcn hsl hi1 hab

include hq henv hV hApd hCrk in
/-- **`check_sum_tele_slow` refines `checkSumTele.checkSumTeleSlow .verified`** under `StageC`
(the knot's `whnf`; the inputs' denotations as con-ron's `checkSumTele_spec` asks): the new
constant value is a record in `EREC`. -/
@[refines ConRon.Arena.checkSumTele.checkSumTeleSlow]
theorem checkSumTeleSlow_refinesC (k : Nat) (hk : k ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (cv n cvTa0 : Word) (cvv cvTa : IConstantVal) (hC : StageC dn vis fe env s₀.mem a₀)
    (hcv : decCVp s₀.mem cv.toNat = some cvv) (hcvb : cv.toNat + 4 ≤ erTop s₀.mem)
    (hsl' : ∀ lo ll, nat? (erA s₀.mem) (cv.toNat + 1) = some lo →
      nat? (erA s₀.mem) (cv.toNat + 2) = some ll → lo + ll ≤ erTop s₀.mem ∨ ll = 0)
    (hta : decCVp s₀.mem cvTa0.toNat = some cvTa) (hta4 : cvTa0.toNat + 4 ≤ erTop s₀.mem)
    (hA : AbsOK s₀.mem) {cvP cvTaP : ConLeche.ConstantVal}
    (hcvP : Frontend.denoteCV a₀.store cvv = some cvP)
    (hcvTaP : Frontend.denoteCV a₀.store cvTa = some cvTaP)
    (hws : ConLeche.Expr.WScoped 0 cvTaP.type) (hfe : ConRon.Bridge.denoteFEnv a₀.store fe = some env) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "check_sum_tele_slow" [vis, cv, n, cvTa0]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (checkSumTele.checkSumTeleSlow V fe cvv n.toNat cvTa) a₀ ∧
      StageC dn vis fe env s'.mem (AM.st (checkSumTele.checkSumTeleSlow V fe cvv n.toNat cvTa) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decCVp s'.mem (r.headD 0).toNat =
        some (AM.res (checkSumTele.checkSumTeleSlow V fe cvv n.toNat cvTa) a₀).1 ∧
      (r.tail.headD 0).toNat < 2 ^ 32 ∧
      decI (r.tail.headD 0) = (AM.res (checkSumTele.checkSumTeleSlow V fe cvv n.toNat cvTa) a₀).2 ∧
      AbsOK s'.mem; ⊤⦄ := by
  have hP : CtsProg p := ⟨⟨ha, hc, hsc, hv, hff, hfp, hif, hwt, hi1⟩, hsf, hsp, his, hd, hpf, hpp, hpi,
    hmk, hct, hea, hcn, hsl, hab⟩
  refine triple_post (RefE.triple (ctsE_spec p hV hP k s₀ vis cv n cvTa0)
    (cts_ref hq henv hApd hCrk hP.toWtProg k hk _ a₀ cv n cvTa0 cvv cvTa hC hcv hcvb hsl' hta hta4 hA
      hcvP hcvTaP hws hfe)) fun _ _ ⟨hl, _, _, hrun, hR⟩ => ?_
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hR.stage, hR.grow, by rw [hres]; exact hR.cv, hR.sort32,
    by rw [hres]; exact hR.sort, hR.abs⟩

include hq henv hV hApd hCrk in
/-- **`check_sum_tele` refines `checkSumTele .verified`** under `StageC` (the inputs' denotations
as con-ron's `checkSumTele_spec` asks). -/
@[refines ConRon.Arena.checkSumTele]
theorem checkSumTele_refinesC (hp : p.lookup "check_sum_tele" = some checkSumTeleL) (hst : StripProg p)
    (k : Nat) (hk : k ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (cv n cvTa0 : Word) (cvv cvTa : IConstantVal) (hC : StageC dn vis fe env s₀.mem a₀)
    (hcv : decCVp s₀.mem cv.toNat = some cvv) (hcvb : cv.toNat + 4 ≤ erTop s₀.mem)
    (hsl' : ∀ lo ll, nat? (erA s₀.mem) (cv.toNat + 1) = some lo →
      nat? (erA s₀.mem) (cv.toNat + 2) = some ll → lo + ll ≤ erTop s₀.mem ∨ ll = 0)
    (hta : decCVp s₀.mem cvTa0.toNat = some cvTa) (hta4 : cvTa0.toNat + 4 ≤ erTop s₀.mem)
    (hslTa : ∀ lo ll, nat? (erA s₀.mem) (cvTa0.toNat + 1) = some lo →
      nat? (erA s₀.mem) (cvTa0.toNat + 2) = some ll → lo + ll ≤ erTop s₀.mem ∨ ll = 0)
    (hA : AbsOK s₀.mem) {cvP cvTaP : ConLeche.ConstantVal}
    (hcvP : Frontend.denoteCV a₀.store cvv = some cvP)
    (hcvTaP : Frontend.denoteCV a₀.store cvTa = some cvTaP)
    (hws : ConLeche.Expr.WScoped 0 cvTaP.type) (hfe : ConRon.Bridge.denoteFEnv a₀.store fe = some env) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "check_sum_tele" [vis, cv, n, cvTa0]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (checkSumTele V fe cvv n.toNat cvTa) a₀ ∧
      StageC dn vis fe env s'.mem (AM.st (checkSumTele V fe cvv n.toNat cvTa) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      decCVp s'.mem (r.headD 0).toNat = some (AM.res (checkSumTele V fe cvv n.toNat cvTa) a₀).1 ∧
      (r.tail.headD 0).toNat < 2 ^ 32 ∧
      decI (r.tail.headD 0) = (AM.res (checkSumTele V fe cvv n.toNat cvTa) a₀).2 ∧
      (r.headD 0).toNat + 4 ≤ erTop s'.mem ∧
      (∀ lo ll, nat? (erA s'.mem) ((r.headD 0).toNat + 1) = some lo →
        nat? (erA s'.mem) ((r.headD 0).toNat + 2) = some ll → lo + ll ≤ erTop s'.mem ∨ ll = 0) ∧
      AbsOK s'.mem; ⊤⦄ := by
  have hP : CtProg p := ⟨⟨⟨ha, hc, hsc, hv, hff, hfp, hif, hwt, hi1⟩, hsf, hsp, his, hd, hpf, hpp, hpi,
    hmk, hct, hea, hcn, hsl, hab⟩, hst, hp⟩
  refine triple_post (RefE.triple (ctE_spec p hV hP k s₀ vis cv n cvTa0)
    (ct_ref hq henv hApd hCrk hP.toWtProg k hk _ a₀ cv n cvTa0 cvv cvTa hC hcv hcvb hsl' hta hta4 hslTa
      hA hcvP hcvTaP hws hfe)) fun _ _ ⟨hl, _, _, hrun, hR⟩ => ?_
  obtain ⟨hok, hst', hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst']; exact hR.stage, hR.grow, by rw [hres]; exact hR.cv, hR.sort32,
    by rw [hres]; exact hR.sort, hR.top, hR.lps, hR.abs⟩

end census

end sims

end L.Ind

end
