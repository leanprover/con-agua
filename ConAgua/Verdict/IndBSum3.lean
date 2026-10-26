import ConAgua.Verdict.IndBSum2

/-!
# Error refinements of `check_sum_ctor_tail`, `check_sum_ctor`, `check_sum_ctors`
(lane `verdicts-b`, helper `ib`)
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model ctlE_spec (p : Prog) (hf : p.lookup "check_sum_ctor_tail" = some checkSumCtorTailL)
  fns [hf ↦ ctlE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] errors

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hOpf : OpfF p) (hLC : LvlCacheProg p)
  (hLT : p.lookup "lv_leq_top" = some lvLeqTop)
  (hnv : closedNV p _root_.L.Checker.nvFns = true) (hcE : CoreStubsE p)

include hq henv hOpf hLC hLT hnv hcE in
/-- **`check_sum_ctor_tail`'s error claim** (the hypotheses of `ctlW_okC`, and the core stubs' error
claims): the opened residual not the family's (a decline), a field domain after the block (a
decline), an index expression mentioning the block (a reject), and the field sorts'. -/
theorem ctl_claim (hP : SumProg p) (n : Nat) (hn : n + 1 ≤ 2 ^ 62) (s₀ : St)
    (a : AState) (vis0 T lo ll nP nIdx rs isP lg nF cqO cqL cqB : Word) (lps : List NIdx)
    (cq1 : List EIdx) (cvCa : IConstantVal) (hC : StageC dn vis fe env s₀.mem a) (hT : H T)
    (hlps : decHL s₀.mem lo.toNat ll.toNat = some lps) (hlb : lo.toNat + ll.toNat ≤ iwTop s₀.mem)
    (hcq : decHL s₀.mem cqO.toNat cqL.toNat = some cq1) (hcqb : cqO.toNat + cqL.toNat ≤ iwTop s₀.mem)
    (hcqB : H cqB) (hrs : H rs) (hni : nP.toNat + nIdx.toNat < 2 ^ 64)
    (hnf : nP.toNat + nF.toNat < 2 ^ 64) (hA : AbsOK s₀.mem)
    {env₀ : ConLeche.Env} {TP : ConLeche.Name} {lpsP : List ConLeche.Name} {rsP : ConLeche.Level}
    {crestP : ConLeche.Expr}
    (hTP : denoteN a.store.ns (decI T) = some TP)
    (hlpsP : Frontend.denoteNList a.store.ns lps = some lpsP)
    (hrsP : denoteL a.store.ls (decI rs) = some rsP)
    (hcqBP : denoteE a.store (decI cqB) = some crestP) (hwsc : ConLeche.Expr.WScoped nP.toNat crestP)
    (hok₀ : ConRon.Bridge.Inductives.IFEnvOKS env₀ (fe.restrictTo vis0.toNat) a.store)
    (hfe : ConRon.Bridge.denoteFEnv a.store fe = some env) :
    CoreSpecE p (n + 2) "check_sum_ctor_tail"
      [vis0, vis, T, lo, ll, nP, nIdx, rs, isP, lg, nF, cqO, cqL, cqB]
      (cscTailT (fe.restrictTo vis0.toNat) fe (decI T) lps nP.toNat nIdx.toNat (decI rs) (isP != 0)
        (lg != 0) cvCa nF.toNat (cq1, decI cqB)) s₀ a := by
  refine CoreSpecE.of_runs fun er hc' => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (ctlE_spec p hP.htail (n + 2) ⟨s₀.mem, Locals.init []⟩ vis0 vis T lo ll nP
    nIdx rs isP lg nF cqO cqL cqB) hc' (Err.code_ne_of_cls hk0)
  rw [ctlE.arm1] at hW
  have hS := hC.stage
  have hv := hS.1.env.vis
  unfold cscTailT
  cases h1 : callE p (n + 1) "open_pis_at_fvars_f" [nF, cqB, nP] s₀.mem with
  | error e1 =>
    rw [h1, ctlE.k_open_pis_at_fvars_f.none] at hW
    cases hW
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨rx, m1⟩ := q1
  obtain ⟨ox, a1, hrun1, ⟨⟨hS1, hg1, hdec1⟩, hr1⟩, hA1⟩ :=
    opfSimRA (n := n + 1) hOpf hcqB hS hA rx m1 (callW_of_callE h1)
  obtain ⟨p1, ho1⟩ := ConRon.Bridge.Inductives.openPisAtFvarsF_run hC.check.state hcqBP hr1
  have hC1 : StageC dn vis fe env m1 a1 := hC.of_pstep hS1 hA1 p1
  refine ErrClaim.bind_right hrun1 ?_
  by_cases h0 : rx.headD 0 = 0
  · rw [h1, ctlE.k_open_pis_at_fvars_f.abort1 p (n + 1) _ _ _ _ _ _ _ _ _ _ _ _ _ rx m1 h0] at hW
    cases hW
    cases ox with
    | none =>
      simp only [unwrapOr]
      exact ErrClaim.bind_left (ErrClaim.fail _ _ (by decide))
    | some xq => exact absurd (by simpa [decOLE] using hdec1.1 : rx.headD 0 = 1) (by rw [h0]; decide)
  rw [h1, ctlE.k_open_pis_at_fvars_f.arm1 p (n + 1) vis0 vis T lo ll nP nIdx rs isP lg nF cqO cqL rx m1 h0] at hW
  cases ox with
  | none => exact absurd hdec1 h0
  | some xq =>
  obtain ⟨xl1, xb⟩ := xq
  obtain ⟨xfvsP, xrestP, hxq, hxfvs, hxrest⟩ := ConRon.Bridge.Inductives.denoteOpen_some_inv ho1
  obtain ⟨-, ⟨hxl, hxlb⟩, hxb, hxbd⟩ := hdec1
  rw [sumGetD1, sumGetD2] at hxl hxlb
  rw [drop3_eq] at hxb hxbd
  simp only [unwrapOr, pure_bind]
  -- `param_levels`
  cases h2 : callE p (n + 1) "param_levels" [lo, ll] m1 with
  | error e2 =>
    rw [h2, ctlE.k_param_levels.none] at hW
    cases hW
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨ru, m2⟩ := q2
  rw [h2, ctlE.k_param_levels.arm1] at hW
  obtain ⟨s2, hs2, -, h2m⟩ := triple_of_callW
    (plW_spec p hP.ha hP.hc hP.hsc hP.hg hP.hpf hP.hpp hP.hip hP.hplg hP.hpl hP.hil (n + 1)
      ⟨m1, Locals.init []⟩ lo ll) (callW_of_callE h2)
  subst hs2
  obtain ⟨us, a2, hrun2, hS2, hg2, hu, hus⟩ := plSim (n + 1) m1 a1 lo ll lps hS1
    (by rw [decHL_grow hg1 hlb]; exact hlps) (by have := hg1.1; omega) ru s2.mem h2m
  have hA2 : AbsOK s2.mem := plW_afr h2m hA1
  obtain ⟨p2, husP⟩ := ConRon.Bridge.Inductives.paramLevels_spec lps lpsP a1 a2 us hC1.check.state
    (ConRon.Bridge.denoteNListE_ext p1.ext _ _ hlpsP) hrun2
  have hC2 : StageC dn vis fe env s2.mem a2 := hC1.of_pstep hS2 hA2 p2
  subst hus
  refine ErrClaim.bind_right hrun2 ?_
  generalize hxo : rx.tail.headD 0 = xo at hxl hxlb hW
  generalize hxlw : rx.tail.tail.headD 0 = xlw at hxl hxlb hW
  generalize hxbw : rx.tail.tail.tail.headD 0 = xbw at hxb hxbd hW
  -- `intern_const`
  cases h3 : callE p (n + 1) "intern_const" [T, ru.headD 0] s2.mem with
  | error e3 =>
    rw [h3, ctlE.k_intern_const.none] at hW
    cases hW
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h3
  | ok q3 =>
  obtain ⟨rh, m3⟩ := q3
  by_cases hbig : 4294967296 ≤ rh.headD 0
  · rw [h3, ctlE.k_intern_const.abort1 p (n + 1) vis0 vis nP nIdx rs isP lg nF cqO cqL xo xlw xbw rh m3 hbig] at hW
    cases hW
    exact ErrClaim.of_cls0 rfl
  rw [h3, ctlE.k_intern_const.arm1 p (n + 1) vis0 vis nP nIdx rs isP lg nF cqO cqL xo xlw xbw rh m3 hbig] at hW
  obtain ⟨s3, hs3, -, h3m⟩ := triple_of_callW (internConst_spec p hP.hcf hP.hcp hP.hic (n + 1)
    ⟨s2.mem, Locals.init []⟩ T (ru.headD 0)) (callW_of_callE h3)
  subst hs3
  obtain ⟨he, a3, hrun3, he', hS3, hg3⟩ := ceSim s2.mem a2 T (ru.headD 0) hS2 hT hu (rh.headD 0) s3.mem
    (by rw [h3m])
  have hA3 : AbsOK s3.mem := ceinternW_afr h3m hA2
  obtain ⟨p3, hhd⟩ := ConRon.Bridge.Inductives.internConstE_run hC2.check.state
    (ConRon.Bridge.denoteN_ext hTP (p1.ext.trans p2.ext)) husP hrun3
  have hC3 : StageC dn vis fe env s3.mem a3 := hC2.of_pstep hS3 hA3 p3
  subst he'
  refine ErrClaim.bind_right hrun3 ?_
  have hd32 : H (rh.headD 0) := by
    have : ¬ (4294967296 : Nat) ≤ (rh.headD 0).toNat := hbig
    show (rh.headD 0).toNat < 2 ^ 32; omega
  have hx13 := p2.ext.trans p3.ext
  have hxr3 : denoteE a3.store (decI xbw) = some xrestP := by
    rw [hxbd]; exact ConRon.Bridge.denote_ext hxrest hx13
  -- `get_app_fn_f`
  have h4 := gafF_ok dn vis fe CWF xbw hxb
  rw [CWF_eq, hxbd] at h4
  cases h4c : callE p (n + 1) "get_app_fn_f" [CWF, xbw] s3.mem with
  | error e4 =>
    rw [h4c, ctlE.k_get_app_fn_f.none] at hW
    cases hW
    exact ErrClaim.bind_left (ErrClaim.of_callE_nv hnv (by decide +kernel) h4c)
  | ok q4 =>
  obtain ⟨rf, m4⟩ := q4
  rw [h4c, ctlE.k_get_app_fn_f.arm1] at hW
  obtain ⟨s4, hs4, -, h4m⟩ := triple_of_callW (gafF_spec p hP.ad (n + 1) ⟨s3.mem, Locals.init []⟩ [CWF, xbw])
    (callW_of_callE h4c)
  subst hs4
  obtain ⟨xfn, a4, hr4, hS4, hg4, hf32, hfd⟩ := (sumSim_of_relW h4 hS3) rf s4.mem h4m
  have hA4 : AbsOK s4.mem := (show AFr _ _ from AFr.of_frame (gafF_frame h4m)) hA3
  have hr4c := hr4
  rw [← hxbd] at hr4
  obtain ⟨ha4, -⟩ := ConRon.Bridge.Inductives.getAppFn_run hC3.check.state hxr3 hr4
  rw [ha4] at hS4 hr4c
  have hC4 : StageC dn vis fe env s4.mem a3 := hC3.of_pstep hS4 hA4 (PStep.refl hC3.check.state)
  refine ErrClaim.bind_right hr4c ?_
  -- `get_app_args_f`
  have h5 := gaaF_ok dn vis fe CWF xbw hxb
  rw [CWF_eq, hxbd] at h5
  cases h5c : callE p (n + 1) "get_app_args_f" [CWF, xbw] s4.mem with
  | error e5 =>
    rw [h5c, ctlE.k_get_app_args_f.none] at hW
    cases hW
    exact ErrClaim.bind_left (ErrClaim.of_callE_nv hnv (by decide +kernel) h5c)
  | ok q5 =>
  obtain ⟨ra, m5⟩ := q5
  obtain ⟨s5, hs5, -, h5m⟩ := triple_of_callW (gaaF_spec p hP.ad (n + 1) ⟨s4.mem, Locals.init []⟩ [CWF, xbw])
    (callW_of_callE h5c)
  subst hs5
  obtain ⟨args, a5, hr5, hS5, hg5, hargs, hab⟩ := (sumSim_of_relW h5 hS4) ra s5.mem h5m
  have hA5 : AbsOK s5.mem := gaaF_afr h5m hA4
  have hr5c := hr5
  rw [← hxbd] at hr5
  obtain ⟨ha5, hargsP⟩ := ConRon.Bridge.Inductives.getAppArgs_run hC4.check.state hxr3 hr5
  rw [ha5] at hS5 hr5c
  have hC5 : StageC dn vis fe env s5.mem a3 := hC4.of_pstep hS5 hA5 (PStep.refl hC4.check.state)
  refine ErrClaim.bind_right hr5c ?_
  rw [sumGetD0, sumGetD1] at hargs hab
  subst hfd
  rw [h5c] at hW
  generalize hao : ra.headD 0 = ao at hargs hab hW
  generalize hal : ra.tail.headD 0 = al at hargs hab hW
  have hlen : args.length = al.toNat := decHL_length s5.mem hargs
  have hg15 := ((hg2.trans hg3).trans hg4).trans hg5
  have hg05 := hg1.trans hg15
  have hcq5 : decHL s5.mem cqO.toNat cqL.toNat = some cq1 := by rw [decHL_grow hg05 hcqb]; exact hcq
  have hle' : ¬ nP ≤ al → al.toNat < nP.toNat := fun h => by
    have : ¬ nP.toNat ≤ al.toNat := fun e => h (UInt64.le_iff_toNat_le.mpr e)
    omega
  by_cases hle : nP ≤ al
  · have hle1 : (if nP ≤ ra.tail.headD 0 then (1 : Word) else 0) = 1 := by rw [hal]; simp [hle]
    rw [ctlE.k_get_app_args_f.arm1 p (n + 1) vis0 vis nP nIdx rs isP lg nF cqO cqL xo xlw (rh.headD 0)
      (rf.headD 0) _ _ hle1, hao, hal] at hW
    cases h6 : callE p (n + 1) "sl_eq" [ao, nP, cqO, cqL] s5.mem with
    | error e6 =>
      rw [h6, ctlE.k_sl_eq.none] at hW
      cases hW
      exact ErrClaim.of_callE_nv hnv (by decide +kernel) h6
    | ok q6 =>
    obtain ⟨re, m6⟩ := q6
    rw [h6, ctlE.k_sl_eq.arm1] at hW
    obtain ⟨s6, hs6, -, hm6, hq6⟩ := triple_of_callW (slEq_spec p hP.heq (n + 1) ⟨s5.mem, Locals.init []⟩ ao nP cqO cqL)
      (callW_of_callE h6)
    have hm6' : m6 = s5.mem := by rw [← hs6, hm6]
    subst hm6'
    have hle2 : nP.toNat ≤ al.toNat := UInt64.le_iff_toNat_le.mp hle
    have hcq5 : decHL s5.mem cqO.toNat cqL.toNat = some cq1 := by rw [decHL_grow hg05 hcqb]; exact hcq
    have htk := decHL_take hargs nP.toNat hle2
    obtain ⟨ws1, hs1, hmm1, hb1⟩ := slR_of_decHL s5.mem _ _ _ htk (hS5.lt64 (by omega))
    obtain ⟨ws2, hs2, hmm2, hb2⟩ := slR_of_decHL s5.mem _ _ _ hcq5 (hS5.lt64 (by have := hg05.1; omega))
    simp only [UInt64.ofNat_toNat] at hs1 hs2
    have heq := eqW_ok (n + 1) s5.mem _ _ _ _ (re.headD 0) ws1 ws2 hs1 hs2 hq6
    have hb3 : re.headD 0 = if (args.take nP.toNat == cq1) then 1 else 0 := by
      rw [heq]
      have := map_decI_inj (k := .expr) ws1 ws2 hb1 hb2
      by_cases hw : ws1 = ws2
      · rw [if_pos hw]
        have ht : args.take nP.toNat = cq1 := by rw [hmm1, hmm2, hw]
        rw [ht]; simp
      · rw [if_neg hw]
        have hne : args.take nP.toNat ≠ cq1 := by
          rw [hmm1, hmm2]; exact fun h' => hw (this.mp h')
        rw [show (args.take nP.toNat == cq1) = false from by simpa using hne]; rfl
    by_cases hcond : (if rf.headD 0 = rh.headD 0 then (1 : Word) else 0) = 0 ∨
        (if al = nP + nIdx then (1 : Word) else 0) = 0 ∨ re.headD 0 = 0
    · rw [ctlE.j1.abort1 p (n + 1) vis0 vis nP rs isP lg nF xo xlw ao al _ _ _ s5.mem hcond] at hW
      cases hW
      have hfalse : ((decI (rf.headD 0) : EIdx) == (decI (rh.headD 0) : EIdx) && args.take nP.toNat == cq1 &&
          args.length == nP.toNat + nIdx.toNat) = false := by
        cases hh : ((decI (rf.headD 0) : EIdx) == (decI (rh.headD 0) : EIdx) && args.take nP.toNat == cq1 &&
          args.length == nP.toNat + nIdx.toNat)
        · rfl
        · exfalso
          simp only [Bool.and_eq_true, beq_iff_eq] at hh
          obtain ⟨⟨h1', h2'⟩, h3'⟩ := hh
          rcases hcond with h | h | h
          · apply absurd h
            rw [if_pos (decI_inj (k := .expr) hf32 (by omega) h1')]; decide
          · apply absurd h
            rw [if_pos (by apply UInt64.toNat_inj.mp; rw [sum_toNat_add hni, ← hlen]; exact h3')]; decide
          · rw [hb3, h2'] at h; simp at h
      simp only [hfalse, Bool.false_eq_true, ite_false]
      exact ErrClaim.bind_left (ErrClaim.fail _ _ (by decide))
    · rw [ctlE.j1.arm1 p (n + 1) vis0 vis nP rs isP lg nF xo xlw ao al _ _ _ s5.mem hcond] at hW
      have htrue : ((decI (rf.headD 0) : EIdx) == (decI (rh.headD 0) : EIdx) && args.take nP.toNat == cq1 &&
          args.length == nP.toNat + nIdx.toNat) = true := by
        simp only [not_or] at hcond
        obtain ⟨h1', h2', h3'⟩ := hcond
        have e1 : rf.headD 0 = rh.headD 0 := by
          refine Classical.byContradiction fun hne => ?_; apply h1'; rw [if_neg hne]
        have e2 : al = nP + nIdx := by
          refine Classical.byContradiction fun hne => ?_; apply h2'; rw [if_neg hne]
        have e3 : args.take nP.toNat = cq1 := by
          rw [hb3] at h3'
          refine Classical.byContradiction fun hne => ?_
          apply h3'
          rw [show (args.take nP.toNat == cq1) = false from by simpa using hne]; rfl
        rw [e1, e3, hlen, e2, sum_toNat_add hni]; simp
      simp only [htrue, ite_true]
      have hT5 : ao.toNat + al.toNat < 2 ^ 64 := hS5.lt64 hab
      have hxl5 : decHL s5.mem xo.toNat xlw.toNat = some xl1 := by rw [decHL_grow hg15 hxlb]; exact hxl
      have hxlb5 : xo.toNat + xlw.toNat ≤ iwTop s5.mem := by have := hg15.1; omega
      have hx03 := p1.ext.trans hx13
      have hread : ConRon.Bridge.Inductives.ReadOK env₀ (fe.restrictTo vis0.toNat) a3 :=
        ⟨hC5.check.state, hC5.check.pins, hok₀.mono hx03 a3 rfl⟩
      -- `field_doms_resolve`
      cases h7 : callE p (n + 1) "field_doms_resolve" [vis0, xo, xlw] s5.mem with
      | error e7 =>
        rw [h7, ctlE.k_field_doms_resolve.none] at hW
        cases hW
        exact ErrClaim.of_callE_nv hnv (by decide +kernel) h7
      | ok q7 =>
      obtain ⟨r7, m7⟩ := q7
      obtain ⟨s7, hs7, -, h7m⟩ := triple_of_callW (fdrW_spec p hP.hfdr hP.ad.ftd hP.hcr (n + 1)
        ⟨s5.mem, Locals.init []⟩ vis0 xo xlw) (callW_of_callE h7)
      subst hs7
      obtain ⟨b1, a6, hr6, hQ6, hA6⟩ := (fdrSim (n + 1) s5.mem a3 xo xlw xl1 (hS5.restrict vis0) hxl5 hxlb5 hA5)
        r7 s7.mem h7m
      obtain ⟨hS6, hg6, hb1⟩ := sumKeep_restrict hv hQ6
      obtain ⟨p6, -⟩ := ConRon.Bridge.Inductives.fieldDomsResolve_spec xl1 xfvsP hread
        (ConRon.Bridge.denoteEList_ext hx13 _ _ hxfvs) hr6
      have hC6 : StageC dn vis fe env s7.mem a6 := hC5.of_pstep hS6 hA6 p6
      refine ErrClaim.bind_right hr6 ?_
      by_cases h71 : r7.headD 0 = 0
      · rw [h7, ctlE.k_field_doms_resolve.abort1 p (n + 1) vis0 vis nP rs isP lg nF xo xlw (ao + nP) (al - nP)
          r7 s7.mem h71] at hW
        cases hW
        have hbf : b1 = false := by rw [← hb1, h71]; rfl
        subst hbf
        simp only [Bool.false_eq_true, ite_false]
        exact ErrClaim.bind_left (ErrClaim.fail _ _ (by decide))
      rw [h7, ctlE.k_field_doms_resolve.arm1 p (n + 1) vis0 vis nP rs isP lg nF xo xlw (ao + nP) (al - nP)
        r7 s7.mem h71] at hW
      have hb1' : b1 = true := by rw [← hb1]; simpa using h71
      subst hb1'
      simp only [ite_true]
      -- `idx_args_resolve`
      have hao' : (ao + nP).toNat = ao.toNat + nP.toNat := sum_toNat_add (by omega)
      have halp : (al - nP).toNat = al.toNat - nP.toNat := by
        rw [UInt64.toNat_sub_of_le _ _ hle]
      have hdrop6 : decHL s7.mem (ao + nP).toNat (al - nP).toNat = some (args.drop nP.toNat) := by
        rw [hao', halp]
        exact decHL_drop nP.toNat (by rw [decHL_grow hg6 hab]; exact hargs) hle2
      have hdb6 : (ao + nP).toNat + (al - nP).toNat ≤ iwTop s7.mem := by
        rw [hao', halp]; have := hg6.1; omega
      cases h8 : callE p (n + 1) "idx_args_resolve" [vis0, ao + nP, al - nP] s7.mem with
      | error e8 =>
        rw [h8, ctlE.k_idx_args_resolve.none] at hW
        cases hW
        exact ErrClaim.bind_left (ErrClaim.of_callE_nv hnv (by decide +kernel) h8)
      | ok q8 =>
      obtain ⟨r8, m8⟩ := q8
      obtain ⟨s8, hs8, -, h8m⟩ := triple_of_callW (iarW_spec p hP.hiar hP.hcr (n + 1)
        ⟨s7.mem, Locals.init []⟩ vis0 (ao + nP) (al - nP)) (callW_of_callE h8)
      subst hs8
      obtain ⟨b2, a7, hr7, hQ7, hA7⟩ := (iarSim (n + 1) s7.mem a6 (ao + nP) (al - nP) (args.drop nP.toNat)
        (hS6.restrict vis0) hdrop6 hdb6 hA6) r8 s8.mem h8m
      obtain ⟨hS7, hg7, hb2⟩ := sumKeep_restrict hv hQ7
      have hargs6 := ConRon.Bridge.denoteEList_ext p6.ext _ _ hargsP
      obtain ⟨p7, -⟩ := ConRon.Bridge.Inductives.idxArgsResolve_spec (args.drop nP.toNat)
        (xrestP.getAppArgs.drop nP.toNat) (hread.mono p6.ok p6.ext p6.pins)
        (ConRon.Bridge.Inductives.denoteEList_drop hargs6 nP.toNat) hr7
      have hC7 : StageC dn vis fe env s8.mem a7 := hC6.of_pstep hS7 hA7 p7
      refine ErrClaim.bind_right hr7 ?_
      by_cases h81 : r8.headD 0 = 0
      · rw [h8, ctlE.k_idx_args_resolve.abort1 p (n + 1) vis nP rs isP lg nF xo xlw (ao + nP) (al - nP)
          r8 s8.mem h81] at hW
        cases hW
        have hbf : b2 = false := by rw [← hb2, h81]; rfl
        subst hbf
        simp only [Bool.false_eq_true, ite_false]
        exact ErrClaim.bind_left (ErrClaim.fail _ _ (by decide))
      rw [h8, ctlE.k_idx_args_resolve.arm1 p (n + 1) vis nP rs isP lg nF xo xlw (ao + nP) (al - nP)
        r8 s8.mem h81] at hW
      have hb2' : b2 = true := by rw [← hb2]; simpa using h81
      subst hb2'
      simp only [ite_true]
      -- the field sorts
      have hg67 := hg6.trans hg7
      have hx37 := p6.ext.trans p7.ext
      have hx07 := hx03.trans hx37
      have hxfvs7 := ConRon.Bridge.denoteEList_ext (hx13.trans hx37) _ _ hxfvs
      have hxpos : ∀ i, i < nF.toNat → ∀ x, xfvsP[i]? = some x →
          ConLeche.Expr.WScoped (nP.toNat + i) x.fvarTypeD :=
        fun i _ x hx => ConRon.Bridge.Inductives.openers_typeD_WScoped hxq hwsc i x hx
      cases h9 : callE p (n + 1) "check_struct_field_sorts_i" [vis, isP, lg, rs, nP, xo, xlw, ao + nP, al - nP, nF]
          s8.mem with
      | error e9 =>
        rw [h9, ctlE.k_check_struct_field_sorts_i.none] at hW
        cases hW
        refine ErrClaim.bind_left ?_
        exact CoreSpecE.of_callE (checkStructFieldSortsI_claim hq henv hLC hLT hnv hcE hP.hg hP.hpw hP.het hP.hcn
          hP.hfsb hP.hcfg hP.ha hP.hcfs hP.ad.ftd n (by omega) s8 a7 isP lg rs nP xo xlw (ao + nP) (al - nP) nF
          xl1 (args.drop nP.toNat) hC7 hA7
          (by rw [decHL_grow hg67 hxlb5]; exact hxl5) (by have := hg67.1; omega)
          (by rw [decHL_grow hg7 hdb6]; exact hdrop6) (by have := hg7.1; omega) hrs
          (ConRon.Bridge.denoteL_ext hrsP hx07) hnf hxfvs7 hxpos) h9
      | ok q9 =>
      rw [h9, ctlE.k_check_struct_field_sorts_i.arm1] at hW
      cases hW
  · have hle1 : (if nP ≤ ra.tail.headD 0 then (1 : Word) else 0) ≠ 1 := by
      rw [hal]; simp [hle]
    rw [ctlE.k_get_app_args_f.arm2 p (n + 1) vis0 vis nP nIdx rs isP lg nF cqO cqL xo xlw (rh.headD 0)
      (rf.headD 0) _ _ hle1, hao, hal] at hW
    rw [ctlE.j1.abort1 p (n + 1) vis0 vis nP rs isP lg nF xo xlw ao al _ _ _ s5.mem (Or.inr (Or.inr rfl))] at hW
    cases hW
    have hlt := hle' hle
    have hfalse : ((decI (rf.headD 0) : EIdx) == (decI (rh.headD 0) : EIdx) && args.take nP.toNat == cq1 &&
        args.length == nP.toNat + nIdx.toNat) = false := by
      have : (args.length == nP.toNat + nIdx.toNat) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; omega
      rw [this]; simp
    simp only [hfalse, Bool.false_eq_true, ite_false]
    exact ErrClaim.bind_left (ErrClaim.fail _ _ (by decide))

end sims

end L.Ind
