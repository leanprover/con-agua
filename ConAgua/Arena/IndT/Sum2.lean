import ConAgua.Arena.DeclArmT
import ConAgua.Arena.IndT.Sum1
import ConAgua.Arena.RecGenSpec.ClassFeR
import ConAgua.Arena.RecGenSpec.Rec3TmdWDecB
import ConRon.Bridge.Inductives.SumInstall

/-!
# `checkSumTele.checkSumTeleSlow`, `checkSumTele` under `StageC` (lane `indstaget`)

`check_sum_tele_slow`'s model at `realCall p`, from `StageC` and con-ron's preconditions of
`checkSumTele_spec` (the two constant values denote, the stored type is closed, the environment
denotes), its twin side transcribed from that spec's `slow` arm: `whnfTelescope` (`wtW_simC`, and
con-ron's `whnfTelescope_spec` on its run for the answer's denotation), the sort's intern
(`internSortE_run`), `closeTelescope` (`closeTelescope_spec`), the record write (twin side none),
`checkConstantVal` (the stub's `StageR` contract, con-ron's `checkConstantVal_bridge` on its run
for the `CoreStep`).
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hV : ValProg p)
  (hApd : ApdF p) (hCrk : CrKeep p)

include hq henv hV hApd hCrk in
/-- **`check_sum_tele_slow` under `StageC`** (twin side: the `slow` arm of con-ron's
`checkSumTele_spec`). -/
theorem ctsW_okC (k : Nat) (hk : k ≤ 2 ^ 62)
    (m m' : Mem) (a : AState) (cv n cvTa0 : Word) (r : List Word) (cvv cvTa : IConstantVal)
    (h : ctsW (realCall p) k m vis cv n cvTa0 = some (r, m')) (hC : StageC dn vis fe env m a)
    (hcv : decCVp m cv.toNat = some cvv) (hcvb : cv.toNat + 4 ≤ erTop m)
    (hsl : ∀ lo ll, nat? (erA m) (cv.toNat + 1) = some lo → nat? (erA m) (cv.toNat + 2) = some ll →
      lo + ll ≤ erTop m ∨ ll = 0)
    (hta : decCVp m cvTa0.toNat = some cvTa) (hta4 : cvTa0.toNat + 4 ≤ erTop m) (hA : AbsOK m)
    {cvP cvTaP : ConLeche.ConstantVal} (hcvP : Frontend.denoteCV a.store cvv = some cvP)
    (hcvTaP : Frontend.denoteCV a.store cvTa = some cvTaP)
    (hws : ConLeche.Expr.WScoped 0 cvTaP.type) (hfe : ConRon.Bridge.denoteFEnv a.store fe = some env) :
    ∃ res a', (checkSumTele.checkSumTeleSlow V fe cvv n.toNat cvTa).run a = .ok (res, a') ∧
      StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ decCVp m' (r.headD 0).toNat = some res.1 ∧
      (r.headD 0).toNat + 4 ≤ erTop m' ∧
      (∀ lo ll, nat? (erA m') ((r.headD 0).toNat + 1) = some lo →
        nat? (erA m') ((r.headD 0).toNat + 2) = some ll → lo + ll ≤ erTop m' ∨ ll = 0) ∧
      (r.tail.headD 0).toNat < 2 ^ 32 ∧ decI (r.tail.headD 0) = res.2 ∧ AbsOK m' := by
  have hS := hC.stage
  obtain ⟨hI1, hE1, hsz, hEs, hc⟩ := hS.2
  cases k with
  | zero => cases h
  | succ k =>
  rw [ctsW_succ (realCall p)] at h
  obtain ⟨w, hw, hw32, hwd⟩ := hd?_rdW (decCV_type hta) (by omega)
  have hw' : rdW (m.arr64 EREC) (cvTa0 + 3) = w := by
    rw [← hw]; congr 1
  rw [hw'] at h
  have hdw : denoteE a.store (decI w) = some cvTaP.type := by
    rw [hwd]; exact ConRon.Bridge.denoteCV_type hcvTaP
  obtain ⟨r1, m1, h1, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
  rw [ctsK1_some] at h
  obtain ⟨⟨bs, s⟩, a1, hrun1, hC1, hg1, hd1, ht1, hs32, hs, hA1⟩ :=
    wtW_simC hq henv k (by omega) m a 0 n w hC hA hw32 (by simpa using n.toNat_lt) hdw hws _ h1
  dsimp only at hC1 hg1 hd1 ht1 hs32 hs hA1
  have hS1 := hC1.stage
  rw [show (0 : Word).toNat = 0 from rfl] at hrun1
  obtain ⟨c1, F₁, bsP, sP, -, hbs, hsP⟩ := ConRon.Bridge.Inductives.whnfTelescope_spec fe
    (ConRon.Bridge.CoreSpec.of_core rfl) henv 0 n.toNat (decI w) cvTaP.type hws a a1 (bs, s)
    hC.check ⟨hdw, hfe⟩ hrun1
  dsimp only at hbs hsP
  obtain ⟨ss, m2, h2, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
  by_cases hss : 4294967296 ≤ ss
  · rw [ctsK2_big _ k m2 vis cv _ _ _ ss hss] at h; cases h
  rw [ctsK2_ok _ k m2 vis cv _ _ _ ss hss] at h
  have hss32 : ss.toNat < 2 ^ 32 := by have : ¬ (4294967296 : Nat) ≤ ss.toNat := hss; omega
  obtain ⟨a2, hrun2, hS2, hg2⟩ := internSort_stage hS1 _ hs32 h2
  rw [hs] at hrun2
  obtain ⟨p2, hsort⟩ := ConRon.Bridge.Inductives.internSortE_run hC1.check.state hsP hrun2
  have hA2 := sointernW_afr h2 hA1
  have hC2 : StageC dn vis fe env m2 a2 := hC1.of_pstep hS2 hA2 p2
  have hb1 : (r1.headD 0).toNat + (r1.tail.headD 0).toNat < 2 ^ 64 := by
    obtain ⟨hI, -, hsz1, -⟩ := hS1.2; simp only [iwTop] at hI ht1 ⊢; omega
  obtain ⟨rt, m3, h3, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
  rw [ctsK3_some] at h
  obtain ⟨ty, a3, hrun3, hS3, hg3, ⟨hty32, htyd⟩, hA3⟩ := closeW_ok k dn fe vis m2 m3 a2 _ _ 0 ss bs rt h3 hS2
    hss32 (by rw [decHL_grow hg2 ht1]; exact hd1) hb1 (by have := hg2.1; omega)
    (by rw [show (0 : Word).toNat = 0 from rfl]; omega) hA2
  rw [show (0 : Word).toNat = 0 from rfl] at hrun3
  obtain ⟨p3, hty⟩ := ConRon.Bridge.Inductives.closeTelescope_spec bs bsP 0 (decI ss) (.sort sP) a2 a3 ty
    hC2.check.state ⟨ConRon.Bridge.denoteEList_ext p2.ext _ _ hbs, by rw [← decE_eq]; exact hsort⟩ hrun3
  have hC3 : StageC dn vis fe env m3 a3 := hC2.of_pstep hS3 hA3 p3
  have hg13 := (hg1.trans hg2).trans hg3
  cases h4 : cvNewW m3 (rdW (m3.arr64 EREC) cv) (rdW (m3.arr64 EREC) (cv + 1))
      (rdW (m3.arr64 EREC) (cv + 2)) (rt.headD 0) with
  | none => rw [h4] at h; cases h
  | some x4 =>
  obtain ⟨q, m4⟩ := x4
  rw [h4, ctsK4_some] at h
  have hnat : ∀ j, j < 4 → nat? (erA m3) (cv.toNat + j) = nat? (erA m) (cv.toNat + j) := fun j hj => by
    simp only [nat?, erA]; rw [hg13.2.2.2 _ (by omega)]
  obtain ⟨hS4, hg4, hqe, htop4, hsl4, hdq⟩ := cvNew_stage h4 hS3 (decCVp_grow hg13 hcvb hsl hcv)
    (by have := hg13.2.1; omega)
    (fun lo ll e1 e2 => by
      rw [show cv.toNat + 1 = cv.toNat + 1 from rfl, hnat 1 (by decide)] at e1
      rw [hnat 2 (by decide)] at e2
      have := hsl lo ll e1 e2; have := hg13.2.1; omega)
    hty32
  have hA4 := cvNewW_afr h4 hA3
  have hC4 : StageC dn vis fe env m4 a3 := hC3.of_pstep hS4 hA4 (PStep.refl hC3.check.state)
  have c3 := c1.trans ((p2.trans p3).toCore c1.ok)
  have hcvT : Frontend.denoteCV a3.store { cvv with type := decI (rt.headD 0) } =
      some { cvP with type := ConLeche.closeTelescope bsP 0 (.sort sP) } := by
    obtain ⟨hn, hl, -⟩ := ConRon.Bridge.denoteCV_inv hcvP
    simp only [Frontend.denoteCV, ConRon.Bridge.denoteN_ext hn c3.ext,
      ConRon.Bridge.denoteNListE_ext c3.ext _ _ hl, htyd, hty]
  obtain ⟨r5, m5, h5, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
  rw [ctsK5_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hqx : CVExt m4 q.toNat := ⟨by omega, fun lo ll e1 e2 => by
    rcases hsl4 lo ll e1 e2 with h' | h'
    · left; omega
    · right; exact h'⟩
  obtain ⟨s5, hs5, -, hok5, hT5, hg5, -⟩ := triple_of_callW (s₀ := ⟨m4, Locals.init []⟩)
    (checkConstantVal_refinesT p hV hq hApd hCrk k (by omega) _ a3 dn fe vis q _ hC4.stageT
      (rec2DecCV_erecP hdq hqx) (rec3CVExt_lt hS4 hqx) (denoteCV_lps hcvT) hA4.crMemo.crOK) h5
  simp only at hs5 hT5 hg5
  subst hs5
  have hrun5 := AM.run_of_ok _ a3 hok5
  generalize AM.res (ConRon.Arena.checkConstantVal V fe { cvv with type := decI (rt.headD 0) }) a3 = u
    at hrun5
  generalize AM.st (ConRon.Arena.checkConstantVal V fe { cvv with type := decI (rt.headD 0) }) a3 = a5
    at hrun5 hT5
  obtain ⟨c5, -⟩ := ConRon.Bridge.checkConstantVal_bridge rfl (ConRon.Bridge.CoreSpec.of_core rfl)
    hC4.check henv hcvT hrun5
  have hA5 := checkConstantVal_absOK p hV hq hApd hCrk (n := k) (by omega) hC4.stageT
    (rec2DecCV_erecP hdq hqx) (rec3CVExt_lt hS4 hqx) (denoteCV_lps hcvT) hA4.crMemo.crOK h5 hA4
  have hg15 := (hg13.trans hg4).trans hg5
  refine ⟨({ cvv with type := ty }, s), a5, ?_, StageC.of_T hT5 c5.ok, hg15, ?_, ?_, ?_,
    by simpa using hs32, by simpa using hs, hA5⟩
  · simp only [checkSumTele.checkSumTeleSlow, StateT.run_bind]
    rw [← hwd, hrun1]
    simp only [bind, Except.bind]
    rw [hrun2]
    simp only
    rw [← decE_eq] at hrun3
    rw [hrun3]
    simp only
    rw [← htyd]
    rw [hrun5]
    rfl
  · simp only [List.headD]
    rw [decCVp_grow hg5 (by omega) (fun lo ll e1 e2 => by have := hsl4 lo ll e1 e2; omega) hdq, htyd]
  · simp only [List.headD]; have := hg5.2.1; omega
  · intro lo ll e1 e2
    simp only [List.headD] at e1 e2
    have hn : ∀ j, j < 4 → nat? (erA s5.mem) (q.toNat + j) = nat? (erA m4) (q.toNat + j) := fun j hj => by
      simp only [nat?, erA]; rw [hg5.2.2.2 _ (by omega)]
    rw [hn 1 (by decide)] at e1; rw [hn 2 (by decide)] at e2
    have := hsl4 lo ll e1 e2; have := hg4.2.1; have := hg5.2.1; omega

include hq henv hV hApd hCrk in
/-- **`check_sum_tele` under `StageC`** (twin side: con-ron's `checkSumTele_spec`'s proof:
`stripPis` leaves the twin's state, the syntactic sort is a read, the slow arm `ctsW_okC`). -/
theorem ctW_okC (k : Nat) (hk : k ≤ 2 ^ 62)
    (m m' : Mem) (a : AState) (cv n cvTa0 : Word) (r : List Word) (cvv cvTa : IConstantVal)
    (h : ctW (realCall p) k m vis cv n cvTa0 = some (r, m')) (hC : StageC dn vis fe env m a)
    (hcv : decCVp m cv.toNat = some cvv) (hcvb : cv.toNat + 4 ≤ erTop m)
    (hsl : ∀ lo ll, nat? (erA m) (cv.toNat + 1) = some lo → nat? (erA m) (cv.toNat + 2) = some ll →
      lo + ll ≤ erTop m ∨ ll = 0)
    (hta : decCVp m cvTa0.toNat = some cvTa) (hta4 : cvTa0.toNat + 4 ≤ erTop m)
    (hslTa : ∀ lo ll, nat? (erA m) (cvTa0.toNat + 1) = some lo →
      nat? (erA m) (cvTa0.toNat + 2) = some ll → lo + ll ≤ erTop m ∨ ll = 0) (hA : AbsOK m)
    {cvP cvTaP : ConLeche.ConstantVal} (hcvP : Frontend.denoteCV a.store cvv = some cvP)
    (hcvTaP : Frontend.denoteCV a.store cvTa = some cvTaP)
    (hws : ConLeche.Expr.WScoped 0 cvTaP.type) (hfe : ConRon.Bridge.denoteFEnv a.store fe = some env) :
    ∃ res a', (checkSumTele V fe cvv n.toNat cvTa).run a = .ok (res, a') ∧
      StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ decCVp m' (r.headD 0).toNat = some res.1 ∧
      (r.headD 0).toNat + 4 ≤ erTop m' ∧
      (∀ lo ll, nat? (erA m') ((r.headD 0).toNat + 1) = some lo →
        nat? (erA m') ((r.headD 0).toNat + 2) = some ll → lo + ll ≤ erTop m' ∨ ll = 0) ∧
      (r.tail.headD 0).toNat < 2 ^ 32 ∧ decI (r.tail.headD 0) = res.2 ∧ AbsOK m' := by
  have hS := hC.stage
  obtain ⟨hI1, hE1, hsz, hEs, hc⟩ := hS.2
  cases k with
  | zero => cases h
  | succ k =>
  rw [ctW_succ (realCall p)] at h
  obtain ⟨w, hw, hw32, hwd⟩ := hd?_rdW (decCV_type hta) (by omega)
  have hw' : rdW (m.arr64 EREC) (cvTa0 + 3) = w := by
    rw [← hw]; congr 1
  rw [hw'] at h
  obtain ⟨r1, m1, h1, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
  obtain ⟨x, a1, hrun1, hS1, hg1, hdec⟩ := stripF_pis_ok dn vis fe n w hw32 m m1 a r1 h1 hS
  have hdw : denoteE a.store (decI w) = some cvTaP.type := by
    rw [hwd]; exact ConRon.Bridge.denoteCV_type hcvTaP
  obtain ⟨ha1, -⟩ := ConRon.Bridge.Inductives.stripPis_pstep hC.check.state hdw hrun1
  rw [ha1] at hrun1 hS1
  have hA1 := stripF_afr h1 hA
  have hC1 : StageC dn vis fe env m1 a := hC.of_pstep hS1 hA1 (PStep.refl hC.check.state)
  have hcv1 := decCVp_grow hg1 hcvb hsl hcv
  have hta1 := decCVp_grow hg1 hta4 hslTa hta
  have hnat : ∀ q : Word, q.toNat + 4 ≤ erTop m → ∀ j, j < 4 →
      nat? (erA m1) (q.toNat + j) = nat? (erA m) (q.toNat + j) := fun q hq j hj => by
    simp only [nat?, erA]; rw [hg1.2.2.2 _ (by omega)]
  have hrun0 : ∀ {β : Type} (f : Option (List EIdx × EIdx) → AM β),
      (stripPis n.toNat cvTa.type >>= f).run a = (f x).run a := by
    intro β f; rw [StateT.run_bind, ← hwd, hrun1]; rfl
  by_cases hf : r1.headD 0 = 1 ∧ r1.tail.tail.tail.headD 0 >>> 28 = 2
  · cases x with
    | none => simp only [decOLE] at hdec; rw [hf.1] at hdec; cases hdec
    | some le =>
    obtain ⟨l, e⟩ := le
    simp only [decOLE, decW0E] at hdec
    obtain ⟨-, -, hb32, hbe⟩ := hdec
    rw [drop3_eq] at hb32 hbe
    by_cases hne : eViewW m1 (r1.tail.tail.tail.headD 0) = []
    · rw [ctK1_fast0 (realCall p) k m1 vis cv n cvTa0 r1 hf hne] at h; cases h
    rw [ctK1_fast (realCall p) k m1 vis cv n cvTa0 r1 hf hne] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨vv, hview, hVR⟩ := eViewW_ok m1 a hS1.1.arena.1 _ hne
    have h2 := eViewW_head2 m1 _ hf.2 hne
    have htag : (decE (r1.tail.tail.tail.headD 0)).tag = ETag.sort :=
      (tag_sort_iff _ (by simpa using hb32)).mpr hf.2
    cases vv with
    | sort u =>
      obtain ⟨-, hu32, hu⟩ := hVR
      have hvs := viewSort_of_view _ _ _ htag hview
      have hx1 : (eViewW m1 (r1.tail.tail.tail.headD 0)).getD 1 0 =
          (eViewW m1 (r1.tail.tail.tail.headD 0)).tail.headD 0 := by
        cases eViewW m1 (r1.tail.tail.tail.headD 0) with
        | nil => rfl
        | cons _ t => cases t <;> rfl
      refine ⟨(cvTa, u), a, ?_, hC1, hg1, by simpa using hta1, by simp only [List.headD]; have := hg1.2.1; omega,
        fun lo ll e1 e2 => by
          simp only [List.headD] at e1 e2
          rw [hnat cvTa0 hta4 1 (by decide)] at e1; rw [hnat cvTa0 hta4 2 (by decide)] at e2
          have := hslTa lo ll e1 e2; have := hg1.2.1; omega,
        by simpa [hx1] using hu32, by simpa [hx1] using hu, hA1⟩
      simp only [checkSumTele]
      rw [hrun0]
      simp only []
      rw [← hbe, ← decE_eq, htag]
      simp only [beq_self_eq_true, ite_true, StateT.run_bind]
      rw [viewSort_run hvs]
      rfl
    | _ => simp only [ViewR] at hVR <;> (rw [h2] at hVR) <;> simp at hVR
  · rw [ctK1_slow (realCall p) k m1 vis cv n cvTa0 r1 hf] at h
    obtain ⟨r2, m2, h2, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
    rw [ctK2_some] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨res, a2, hrun2, hC2, hg2, hdec2, hb2, hsl2, hs32, hs, hA2⟩ := ctsW_okC hq henv hV hApd hCrk k (by omega)
      m1 m2 a cv n cvTa0 r2 cvv cvTa h2 hC1 hcv1 (by have := hg1.2.1; omega)
      (fun lo ll e1 e2 => by
        rw [hnat cv hcvb 1 (by decide)] at e1; rw [hnat cv hcvb 2 (by decide)] at e2
        have := hsl lo ll e1 e2; have := hg1.2.1; omega)
      hta1 (by have := hg1.2.1; omega) hA1 hcvP hcvTaP hws hfe
    refine ⟨res, a2, ?_, hC2, hg1.trans hg2, by simpa using hdec2, by simpa using hb2, by simpa using hsl2,
      by simpa using hs32, by simpa using hs, hA2⟩
    simp only [checkSumTele]
    rw [hrun0]
    cases x with
    | none => exact hrun2
    | some le =>
      obtain ⟨l, e⟩ := le
      simp only [decOLE, decW0E] at hdec
      obtain ⟨h1', -, hb32, hbe⟩ := hdec
      rw [drop3_eq] at hb32 hbe
      have hnt : ¬ (e.tag == ETag.sort) = true := by
        rw [← hbe, ← decE_eq]
        intro ht
        exact hf ⟨h1', (tag_sort_iff _ (by simpa using hb32)).mp (by simpa using ht)⟩
      simp only [hnt]
      simp only [Bool.false_eq_true, ite_false]
      exact hrun2

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
  refine triple_post (ctsW_spec p ha hc hsc hv hff hfp hif hwt hsf hsp his hd hpf hpp hpi hmk hct
    hea hcn hsl hi1 hab (realCall p) (realCall_spec p) k s₀ vis cv n cvTa0) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨res, a', hrun, hC', hg, hdec, -, -, hs32, hs, hA'⟩ :=
    ctsW_okC hq henv hV hApd hCrk k hk _ _ _ _ _ _ _ _ _ hm hC hcv hcvb hsl' hta hta4 hA hcvP hcvTaP hws hfe
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hC', hg, by rw [hres]; exact hdec, hs32, by rw [hres]; exact hs, hA'⟩

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
  refine triple_post (ctW_spec p ha hc hsc hv hff hfp hif hwt hsf hsp his hd hpf hpp hpi hmk hct
    hea hcn hsl hp hst hi1 hab (realCall p) (realCall_spec p) k s₀ vis cv n cvTa0) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨res, a', hrun, hC', hg, hdec, hb, hslr, hs32, hs, hA'⟩ :=
    ctW_okC hq henv hV hApd hCrk k hk _ _ _ _ _ _ _ _ _ hm hC hcv hcvb hsl' hta hta4 hslTa hA hcvP hcvTaP hws hfe
  obtain ⟨hok, hst', hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst']; exact hC', hg, by rw [hres]; exact hdec, hs32, by rw [hres]; exact hs,
    hb, hslr, hA'⟩

end census

end sims

end L.Ind
