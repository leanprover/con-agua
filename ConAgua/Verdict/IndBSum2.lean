import ConAgua.Arena.CrOKFrame
import ConAgua.Arena.IndRealApdT
import ConAgua.Arena.IndRealMemoCrT
import ConAgua.Arena.IndT.Sum1
import ConAgua.Arena.Verdict
import ConAgua.Checker.NoVerdictFns
import ConRon.Bridge.Inductives.SumInstall
import ConAgua.Arena.RecGenSpec.ClassFeR
import ConAgua.Arena.RecGenSpec.Rec3TmdWDecB
import ConAgua.Arena.DeclValSpec
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

/-!
# Error refinements of `check_sum_tele_slow`, `check_sum_tele` (lane `verdicts-b`, helper `ib`)

The callees `whnf_telescope` (the whnf family) and `check_constant_val` (the declaration family)
are taken as hypotheses in the shape of their ok refinements (`WtE`, `CcvE`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **`whnf_telescope`'s error claim** (the hypotheses of `whnfTelescope_refinesC`; the whnf family
discharges it). -/
def WtE (p : Prog) : Prop :=
  ∀ {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env},
    ConLeche.EnvWF env → ∀ (k : Nat), k ≤ 2 ^ 62 → ∀ (s₀ : St) (a₀ : AState) (i n e : Word),
    StageC dn vis fe env s₀.mem a₀ → AbsOK s₀.mem → H e → i.toNat + n.toNat < 2 ^ 64 →
    ∀ {eP : ConLeche.Expr}, denoteE a₀.store (decI e) = some eP → ConLeche.Expr.WScoped i.toNat eP →
    CoreSpecE p k "whnf_telescope" [vis, i, n, e] (whnfTelescope V fe i.toNat n.toNat (decI e)) s₀ a₀

/-- **`check_constant_val`'s error claim** (the hypotheses of `checkConstantVal_refinesT`; the
declaration family discharges it). -/
def CcvE (p : Prog) : Prop :=
  ∀ {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat), n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (q : Word) (cv : IConstantVal), StageT dn vis fe s₀.mem a₀ →
    decCV (erecP s₀.mem) q.toNat = some cv → q.toNat + 3 < 2 ^ 64 →
    (∃ ks, cv.levelParams.mapM (denoteN a₀.store.ns) = some ks) → L.Stubs.CrOK s₀.mem →
    CoreSpecE p n "check_constant_val" [vis, q] (checkConstantVal V fe cv) s₀ a₀

l_model ctE_spec (p : Prog) (hf : p.lookup "check_sum_tele" = some checkSumTeleL)
  fns [hf ↦ ctE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model ctsE_spec (p : Prog) (hf : p.lookup "check_sum_tele_slow" = some checkSumTeleSlowL)
  fns [hf ↦ ctsE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hV : ValProg p)
  (hApd : ApdF p) (hCrk : CrKeep p) (hnv : closedNV p _root_.L.Checker.nvFns = true)
  (hW : WtE p) (hCcv : CcvE p)

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

include hq henv hV hApd hCrk hnv hW hCcv in
/-- **`check_sum_tele_slow`'s error claim** (the hypotheses of `checkSumTeleSlow_refinesC`, and the
callees' error claims `WtE`, `CcvE`). -/
theorem checkSumTeleSlow_claim (k : Nat) (hk : k ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (cv n cvTa0 : Word) (cvv cvTa : IConstantVal) (hC : StageC dn vis fe env s₀.mem a₀)
    (hcv : decCVp s₀.mem cv.toNat = some cvv) (hcvb : cv.toNat + 4 ≤ erTop s₀.mem)
    (hsl' : ∀ lo ll, nat? (erA s₀.mem) (cv.toNat + 1) = some lo →
      nat? (erA s₀.mem) (cv.toNat + 2) = some ll → lo + ll ≤ erTop s₀.mem ∨ ll = 0)
    (hta : decCVp s₀.mem cvTa0.toNat = some cvTa) (hta4 : cvTa0.toNat + 4 ≤ erTop s₀.mem)
    (hA : AbsOK s₀.mem) {cvP cvTaP : ConLeche.ConstantVal}
    (hcvP : Frontend.denoteCV a₀.store cvv = some cvP)
    (hcvTaP : Frontend.denoteCV a₀.store cvTa = some cvTaP)
    (hws : ConLeche.Expr.WScoped 0 cvTaP.type) (hfe : ConRon.Bridge.denoteFEnv a₀.store fe = some env) :
    CoreSpecE p k "check_sum_tele_slow" [vis, cv, n, cvTa0]
      (checkSumTele.checkSumTeleSlow V fe cvv n.toNat cvTa) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc' => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW' := triple_of_callE_err (ctsE_spec p hsl k ⟨s₀.mem, Locals.init []⟩ vis cv n cvTa0) hc'
    (Err.code_ne_of_cls hk0)
  have hS := hC.stage
  obtain ⟨hI1, hE1, hsz, hEs, hc0⟩ := hS.2
  cases k with
  | zero => rw [ctsE.eq_def] at hW'; cases hW'; exact absurd rfl hk0
  | succ k =>
  rw [ctsE.arm1] at hW'
  obtain ⟨w, hw, hw32, hwd⟩ := hd?_rdW (decCV_type hta) (by omega)
  have hw' : rdW (s₀.mem.arr64 EREC) (cvTa0 + 3) = w := by
    rw [← hw]; congr 1
  rw [hw'] at hW'
  have hdw : denoteE a₀.store (decI w) = some cvTaP.type := by
    rw [hwd]; exact ConRon.Bridge.denoteCV_type hcvTaP
  unfold checkSumTele.checkSumTeleSlow
  rw [← hwd]
  cases h1 : callE p k "whnf_telescope" [vis, 0, n, w] s₀.mem with
  | error e1 =>
    rw [h1, ctsE.k_whnf_telescope.none] at hW'
    cases hW'
    refine ErrClaim.bind_left ?_
    have := CoreSpecE.of_callE (hW henv (k := k) (by omega) s₀ a₀ 0 n w hC hA hw32 (by simpa using n.toNat_lt) hdw hws) h1
    simpa using this
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, ctsE.k_whnf_telescope.arm1] at hW'
  obtain ⟨s1, hs1, -, h1m⟩ := triple_of_callW
    (wtW_spec p ha hc hsc hv hff hfp hif hwt hi1 (realCall p) (realCall_spec p) k ⟨s₀.mem, Locals.init []⟩ vis 0 n w)
    (callW_of_callE h1)
  subst hs1
  obtain ⟨⟨bs, s⟩, a1, hrun1, hC1, hg1, hd1, ht1, hs32, hs, hA1⟩ :=
    wtW_simC hq henv k (by omega) s₀.mem a₀ 0 n w hC hA hw32 (by simpa using n.toNat_lt) hdw hws _ h1m
  dsimp only at hC1 hg1 hd1 ht1 hs32 hs hA1
  have hS1 := hC1.stage
  rw [show (0 : Word).toNat = 0 from rfl] at hrun1
  obtain ⟨c1, F₁, bsP, sP, -, hbs, hsP⟩ := ConRon.Bridge.Inductives.whnfTelescope_spec fe
    (ConRon.Bridge.CoreSpec.of_core rfl) henv 0 n.toNat (decI w) cvTaP.type hws a₀ a1 (bs, s)
    hC.check ⟨hdw, hfe⟩ hrun1
  dsimp only at hbs hsP
  refine ErrClaim.bind_right hrun1 ?_
  cases h2 : callE p k "intern_sort" [r1.tail.tail.headD 0] s1.mem with
  | error e2 =>
    rw [h2, ctsE.k_intern_sort.none] at hW'
    cases hW'
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨ri, m2⟩ := q2
  by_cases hss : 4294967296 ≤ ri.headD 0
  · rw [h2, ctsE.k_intern_sort.abort1 p k vis cv _ _ _ ri m2 hss] at hW'
    cases hW'
    exact ErrClaim.of_cls0 rfl
  rw [h2, ctsE.k_intern_sort.arm1 p k vis cv _ _ _ ri m2 hss] at hW'
  obtain ⟨s2, hs2, -, h2m⟩ := triple_of_callW (internSort_spec p hsf hsp his k ⟨s1.mem, Locals.init []⟩ _)
    (callW_of_callE h2)
  subst hs2
  have hss32 : (ri.headD 0).toNat < 2 ^ 32 := by
    have : ¬ (4294967296 : Nat) ≤ (ri.headD 0).toNat := hss; omega
  obtain ⟨a2, hrun2, hS2, hg2⟩ := internSort_stage hS1 _ hs32 h2m
  rw [hs] at hrun2
  obtain ⟨p2, hsort⟩ := ConRon.Bridge.Inductives.internSortE_run hC1.check.state hsP hrun2
  have hA2 := sointernW_afr h2m hA1
  have hC2 : StageC dn vis fe env s2.mem a2 := hC1.of_pstep hS2 hA2 p2
  refine ErrClaim.bind_right hrun2 ?_
  cases h3 : callE p k "close_telescope" [r1.headD 0, r1.tail.headD 0, 0, ri.headD 0] s2.mem with
  | error e3 =>
    rw [h3, ctsE.k_close_telescope.none] at hW'
    cases hW'
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h3
  | ok q3 =>
  obtain ⟨rt, m3⟩ := q3
  rw [h3, ctsE.k_close_telescope.arm1] at hW'
  obtain ⟨s3, hs3, -, h3m⟩ := triple_of_callW
    (closeTelescope_spec p hd hpf hpp hpi hmk hct hab k ⟨s2.mem, Locals.init []⟩ _ _ 0 _) (callW_of_callE h3)
  subst hs3
  have hb1 : (r1.headD 0).toNat + (r1.tail.headD 0).toNat < 2 ^ 64 := by
    obtain ⟨hI, -, hsz1, -⟩ := hS1.2; simp only [iwTop] at hI ht1 ⊢; omega
  obtain ⟨ty, a3, hrun3, hS3, hg3, ⟨hty32, htyd⟩, hA3⟩ := closeW_ok k dn fe vis s2.mem s3.mem a2 _ _ 0
    (ri.headD 0) bs rt h3m hS2 hss32 (by rw [decHL_grow hg2 ht1]; exact hd1) hb1 (by have := hg2.1; omega)
    (by rw [show (0 : Word).toNat = 0 from rfl]; omega) hA2
  rw [show (0 : Word).toNat = 0 from rfl] at hrun3
  obtain ⟨p3, hty⟩ := ConRon.Bridge.Inductives.closeTelescope_spec bs bsP 0 (decI (ri.headD 0)) (.sort sP) a2 a3 ty
    hC2.check.state ⟨ConRon.Bridge.denoteEList_ext p2.ext _ _ hbs, by rw [← decE_eq]; exact hsort⟩ hrun3
  have hC3 : StageC dn vis fe env s3.mem a3 := hC2.of_pstep hS3 hA3 p3
  have hg13 := (hg1.trans hg2).trans hg3
  refine ErrClaim.bind_right (by rw [← decE_eq] at hrun3; exact hrun3) ?_
  cases h4 : callE p k "cv_new" [rdW (s3.mem.arr64 EREC) cv, rdW (s3.mem.arr64 EREC) (cv + 1),
      rdW (s3.mem.arr64 EREC) (cv + 2), rt.headD 0] s3.mem with
  | error e4 =>
    rw [h4, ctsE.k_cv_new.none] at hW'
    cases hW'
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h4
  | ok q4 =>
  obtain ⟨rq, m4⟩ := q4
  rw [h4, ctsE.k_cv_new.arm1] at hW'
  obtain ⟨s4, hs4, -, h4m⟩ := triple_of_callW (cvNew_specW p hea hcn k ⟨s3.mem, Locals.init []⟩ _ _ _ _)
    (callW_of_callE h4)
  subst hs4
  dsimp only at h4m
  have hnat : ∀ j, j < 4 → nat? (erA s3.mem) (cv.toNat + j) = nat? (erA s₀.mem) (cv.toNat + j) := fun j hj => by
    simp only [nat?, erA]; rw [hg13.2.2.2 _ (by omega)]
  obtain ⟨hS4, hg4, hqe, htop4, hsl4, hdq⟩ := cvNew_stage h4m hS3 (decCVp_grow hg13 hcvb hsl' hcv)
    (by have := hg13.2.1; omega)
    (fun lo ll e1 e2 => by
      rw [show cv.toNat + 1 = cv.toNat + 1 from rfl, hnat 1 (by decide)] at e1
      rw [hnat 2 (by decide)] at e2
      have := hsl' lo ll e1 e2; have := hg13.2.1; omega)
    hty32
  have hA4 := cvNewW_afr h4m hA3
  have hC4 : StageC dn vis fe env s4.mem a3 := hC3.of_pstep hS4 hA4 (PStep.refl hC3.check.state)
  have c3 := c1.trans ((p2.trans p3).toCore c1.ok)
  have hcvT : Frontend.denoteCV a3.store { cvv with type := decI (rt.headD 0) } =
      some { cvP with type := ConLeche.closeTelescope bsP 0 (.sort sP) } := by
    obtain ⟨hn', hl, -⟩ := ConRon.Bridge.denoteCV_inv hcvP
    simp only [Frontend.denoteCV, ConRon.Bridge.denoteN_ext hn' c3.ext,
      ConRon.Bridge.denoteNListE_ext c3.ext _ _ hl, htyd, hty]
  have hqx : CVExt s4.mem (rq.headD 0).toNat := ⟨by omega, fun lo ll e1 e2 => by
    rcases hsl4 lo ll e1 e2 with h' | h'
    · left; omega
    · right; exact h'⟩
  have hcc := hCcv (dn := dn) (vis := vis) (fe := fe) k (by omega) ⟨s4.mem, Locals.init []⟩ a3 (rq.headD 0) _
    hC4.stageT (rec2DecCV_erecP hdq hqx) (rec3CVExt_lt hS4 hqx) (denoteCV_lps hcvT) hA4.crMemo.crOK
  cases h5 : callE p k "check_constant_val" [vis, rq.headD 0] s4.mem with
  | error e5 =>
    rw [h5, ctsE.k_check_constant_val.none] at hW'
    cases hW'
    refine ErrClaim.bind_left ?_
    have := CoreSpecE.of_callE hcc h5
    rw [← htyd]
    exact this
  | ok q5 =>
  rw [h5, ctsE.k_check_constant_val.arm1] at hW'
  cases hW'

include hq henv hV hApd hCrk hnv hW hCcv in
/-- **`check_sum_tele`'s error claim** (the hypotheses of `checkSumTele_refinesC`, and the
callees' error claims): only the slow arm can fail with a verdict. -/
theorem checkSumTele_claim (hp : p.lookup "check_sum_tele" = some checkSumTeleL) (hst : StripProg p)
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
    CoreSpecE p k "check_sum_tele" [vis, cv, n, cvTa0] (checkSumTele V fe cvv n.toNat cvTa) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc' => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW' := triple_of_callE_err (ctE_spec p hp k ⟨s₀.mem, Locals.init []⟩ vis cv n cvTa0) hc'
    (Err.code_ne_of_cls hk0)
  have hS := hC.stage
  obtain ⟨hI1, hE1, hsz, hEs, hc0⟩ := hS.2
  cases k with
  | zero => rw [ctE.eq_def] at hW'; cases hW'; exact absurd rfl hk0
  | succ k =>
  rw [ctE.arm1] at hW'
  obtain ⟨w, hw, hw32, hwd⟩ := hd?_rdW (decCV_type hta) (by omega)
  have hw' : rdW (s₀.mem.arr64 EREC) (cvTa0 + 3) = w := by
    rw [← hw]; congr 1
  rw [hw'] at hW'
  cases h1 : callE p k "strip_pis" [n, w] s₀.mem with
  | error e1 =>
    rw [h1, ctE.k_strip_pis.none] at hW'
    cases hW'
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  obtain ⟨s1, hs1, -, h1m⟩ := triple_of_callW (stripPis_specF p hst k ⟨s₀.mem, Locals.init []⟩ n w)
    (callW_of_callE h1)
  subst hs1
  obtain ⟨x, a1, hrun1, hS1, hg1, hdec⟩ := stripF_pis_ok dn vis fe n w hw32 s₀.mem s1.mem a₀ r1 h1m hS
  have hdw : denoteE a₀.store (decI w) = some cvTaP.type := by
    rw [hwd]; exact ConRon.Bridge.denoteCV_type hcvTaP
  obtain ⟨ha1, -⟩ := ConRon.Bridge.Inductives.stripPis_pstep hC.check.state hdw hrun1
  rw [ha1] at hrun1 hS1
  have hA1 := stripF_afr h1m hA
  have hC1 : StageC dn vis fe env s1.mem a₀ := hC.of_pstep hS1 hA1 (PStep.refl hC.check.state)
  have hcv1 := decCVp_grow hg1 hcvb hsl' hcv
  have hta1 := decCVp_grow hg1 hta4 hslTa hta
  have hnat : ∀ q : Word, q.toNat + 4 ≤ erTop s₀.mem → ∀ j, j < 4 →
      nat? (erA s1.mem) (q.toNat + j) = nat? (erA s₀.mem) (q.toNat + j) := fun q hq j hj => by
    simp only [nat?, erA]; rw [hg1.2.2.2 _ (by omega)]
  have hrun0 : ∀ {β : Type} (f : Option (List EIdx × EIdx) → AM β),
      (stripPis n.toNat cvTa.type >>= f).run a₀ = (f x).run a₀ := by
    intro β f; rw [StateT.run_bind, ← hwd, hrun1]; rfl
  by_cases hf : r1.headD 0 = 1 ∧ r1.tail.tail.tail.headD 0 >>> 28 = 2
  · rw [h1, ctE.k_strip_pis.arm1 p k vis cv n cvTa0 r1 s1.mem hf] at hW'
    cases h2 : callE p k "e_view" [r1.tail.tail.tail.headD 0] s1.mem with
    | error e2 =>
      rw [h2, ctE.k_e_view.none] at hW'
      cases hW'
      exact ErrClaim.of_callE_nv hnv (by decide +kernel) h2
    | ok q2 =>
      rw [h2, ctE.k_e_view.arm1] at hW'
      cases hW'
  · rw [h1, ctE.k_strip_pis.arm2 p k vis cv n cvTa0 r1 s1.mem hf] at hW'
    cases h2 : callE p k "check_sum_tele_slow" [vis, cv, n, cvTa0] s1.mem with
    | error e2 =>
      rw [h2, ctE.k_check_sum_tele_slow.none] at hW'
      cases hW'
      have hcl := CoreSpecE.of_callE (checkSumTeleSlow_claim hq henv hV hApd hCrk hnv hW hCcv ha hc hsc hv hff
        hfp hif hwt hsf hsp his hd hpf hpp hpi hmk hct hea hcn hsl hi1 hab k (by omega) s1 a₀ cv n cvTa0 cvv cvTa
        hC1 hcv1 (by have := hg1.2.1; omega)
        (fun lo ll e1 e2 => by
          rw [hnat cv hcvb 1 (by decide)] at e1; rw [hnat cv hcvb 2 (by decide)] at e2
          have := hsl' lo ll e1 e2; have := hg1.2.1; omega)
        hta1 (by have := hg1.2.1; omega) hA1 hcvP hcvTaP hws hfe) h2
      unfold checkSumTele
      rw [← hwd]
      refine ErrClaim.bind_right hrun1 ?_
      cases x with
      | none => exact hcl
      | some le =>
        obtain ⟨l, e⟩ := le
        simp only [decOLE, decW0E] at hdec
        obtain ⟨h1', -, hb32, hbe⟩ := hdec
        rw [drop3_eq] at hb32 hbe
        have hnt : ¬ (e.tag == ETag.sort) = true := by
          rw [← hbe, ← decE_eq]
          intro ht
          exact hf ⟨h1', (tag_sort_iff _ (by simpa using hb32)).mp (by simpa using ht)⟩
        simp only [hnt, ite_false, Bool.false_eq_true]
        exact hcl
    | ok q2 =>
      rw [h2, ctE.k_check_sum_tele_slow.arm1] at hW'
      cases hW'

end census

end sims

end L.Ind
