import ConAgua.Verdict.IndBSum3

/-!
# Error refinement of `check_sum_ctors` (lane `verdicts-b`, helper `ib`)
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model sctsE_spec (p : Prog) (hf : p.lookup "check_sum_ctors" = some checkSumCtorsL)
  fns [hf ↦ sctsE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] errors

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hV : ValProg p) (hOpf : OpfF p) (hLC : LvlCacheProg p)
  (hLT : p.lookup "lv_leq_top" = some lvLeqTop)
  (hApd : ApdF p) (hCrk : CrKeep p)
  (hnv : closedNV p _root_.L.Checker.nvFns = true) (hcE : CoreStubsE p) (hCcv : CcvE p)

include hq henv hV hOpf hLC hLT hApd hCrk hnv hcE hCcv in
/-- **`check_sum_ctors`' model error claim** (`sctsW_okC`'s hypotheses; the callees' claims). -/
theorem sctsE_claim (hP : SumProg p)
    (vis0 T lo ll nP nIdx rs isP lg cvTaw : Word) (lps : List NIdx) (cvTa : IConstantVal)
    (hT : H T) (hrs : H rs) {env₀ : ConLeche.Env} {TP : ConLeche.Name} {lpsP : List ConLeche.Name}
    {rsP : ConLeche.Level} {cvTaP : ConLeche.ConstantVal} (hws : ConLeche.Expr.WScoped 0 cvTaP.type)
    (k : Nat) (hk : k ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (cO cL : Word) (cs : List (IConstantVal × Nat))
      (csP : List (ConLeche.ConstantVal × Nat)),
    StageC dn vis fe env m a → decHL m lo.toNat ll.toNat = some lps → lo.toNat + ll.toNat ≤ iwTop m →
    DecB (fun m => decCVp m cvTaw.toNat) m cvTa →
    DecB (fun m => decPL m (decCN m) cO.toNat cL.toNat) m cs → AbsOK m →
    denoteN a.store.ns (decI T) = some TP → Frontend.denoteNList a.store.ns lps = some lpsP →
    denoteL a.store.ls (decI rs) = some rsP → Frontend.denoteCV a.store cvTa = some cvTaP →
    ConRon.Bridge.Inductives.denoteCtors a.store cs = some csP →
    ConRon.Bridge.Inductives.IFEnvOKS env₀ (fe.restrictTo vis0.toNat) a.store →
    ConRon.Bridge.denoteFEnv a.store fe = some env →
    ∀ e, sctsE p k m vis0 vis T lo ll nP nIdx rs isP lg cvTaw cO cL = .error e →
      ErrClaim (checkSumCtors V (fe.restrictTo vis0.toNat) fe (decI T) lps nP.toNat nIdx.toNat (decI rs)
        (isP != 0) (lg != 0) cvTa cs) a e := by
  induction k with
  | zero =>
    intro m a cO cL cs csP hC hlps hlb hta hcs hA hTP hlpsP hrsP hcvTaP hcsP hok₀ hfe e he
    rw [sctsE.eq_def] at he
    cases he
    exact ErrClaim.of_cls0 Err.cls_outOfFuel
  | succ k ih =>
  intro m a cO cL cs csP hC hlps hlb hta hcs hA hTP hlpsP hrsP hcvTaP hcsP hok₀ hfe e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hS := hC.stage
  have hcl := decPL_length (m := truncM m) hcs
  by_cases hl : cL = 0
  · rw [sctsE.arm1 p k m vis0 vis T lo ll nP nIdx rs isP lg cvTaw cO cL hl] at he
    cases he
  by_cases hov1 : nP + nIdx < nP
  · rw [sctsE.abort1 p k m vis0 vis T lo ll nP nIdx rs isP lg cvTaw cO cL hl hov1] at he
    cases he; exact absurd rfl hk0
  have hni : nP.toNat + nIdx.toNat < 2 ^ 64 := by rw [← sumAddNoOv hov1]; exact UInt64.toNat_lt _
  obtain ⟨L, hL⟩ : ∃ L, cL.toNat = L + 1 :=
    ⟨cL.toNat - 1, by have : cL.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  have hcs' : decPL (truncM m) (decCN (truncM m)) cO.toNat (L + 1) = some cs := by
    have := hcs; simp only [DecB, hL] at this; exact this
  cases cs with
  | nil => simp at hcl; omega
  | cons c cs =>
  obtain ⟨cv, nF⟩ := c
  simp only [ConRon.Bridge.Inductives.denoteCtors] at hcsP
  cases hcvP : Frontend.denoteCV a.store cv with
  | none => rw [hcvP] at hcsP; simp at hcsP
  | some cP =>
  cases hrestP : ConRon.Bridge.Inductives.denoteCtors a.store cs with
  | none => rw [hcvP, hrestP] at hcsP; simp at hcsP
  | some restP =>
  obtain ⟨pv, hpv, hc⟩ := decPL_head hcs'
  have htail := decPL_tail hcs'
  obtain ⟨⟨cqN, hcq, hcv⟩, hnF⟩ := decCN_some hc
  obtain ⟨w, hw, hwv, hcO⟩ := rdW_of_iwN_truncM hpv
  have hcq' : iwN (truncM m) w.toNat = some cqN := by rw [hwv]; exact hcq
  obtain ⟨w2, hw2, hw2v, hpvlt⟩ := rdW_of_iwN_truncM hcq'
  have hT0 := hS.lt64 (x := iwTop m) (Nat.le_refl _)
  have hw1 : (w + 1).toNat = pv + 1 := by rw [UInt64.toNat_add, hwv]; simp; omega
  have hnF' : iwN (truncM m) (w + 1).toNat = some nF := by rw [hw1]; exact hnF
  obtain ⟨w3, hw3, hw3v, -⟩ := rdW_of_iwN_truncM hnF'
  by_cases hov2 : nP + rdW (m.arr64 IW) (rdW (m.arr64 IW) cO + 1) < nP
  · rw [sctsE.abort2 p k m vis0 vis T lo ll nP nIdx rs isP lg cvTaw cO cL hl hov1 hov2] at he
    cases he; exact absurd rfl hk0
  rw [sctsE.arm2 p k m vis0 vis T lo ll nP nIdx rs isP lg cvTaw cO cL hl hov1 hov2] at he
  rw [hw, hw3] at hov2
  rw [hw, hw2, hw3] at he
  have hcvB : DecB (fun m => decCVp m w2.toNat) m cv := by
    show decCVp (truncM m) w2.toNat = some cv; rw [hw2v]; exact hcv
  have hnf : nP.toNat + w3.toNat < 2 ^ 64 := by rw [← sumAddNoOv hov2]; exact UInt64.toNat_lt _
  subst hw3v
  simp only [checkSumCtors]
  -- the head constructor
  cases h1 : callE p k "check_sum_ctor" [vis0, vis, T, lo, ll, nP, nIdx, rs, isP, lg, w2, w3, cvTaw] m with
  | error e1 =>
    rw [h1, sctsE.k_check_sum_ctor.none] at he
    cases he
    refine ErrClaim.bind_left ?_
    rcases Nat.eq_zero_or_pos k with hk00 | hk00
    · subst hk00
      obtain ⟨e', he', h0⟩ := callE_zero p "check_sum_ctor" [vis0, vis, T, lo, ll, nP, nIdx, rs, isP, lg, w2, w3, cvTaw] m
      rw [h1] at he'
      cases he'
      exact ErrClaim.of_cls0 h0
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      exact CoreSpecE.of_callE (ctor_claim hq henv hOpf hLC hLT hnv hcE hV hApd hCrk hCcv hP k' (by omega) ⟨m, Locals.init []⟩
        a vis0 T lo ll nP nIdx rs isP lg w2 w3 cvTaw lps cv cvTa hC hT hlps hlb hcvB hta hrs hni hnf hA hTP hlpsP hrsP
        hcvP hcvTaP hws hok₀ hfe) h1
  | ok q1 =>
  obtain ⟨r, m1⟩ := q1
  rw [h1, sctsE.k_check_sum_ctor.arm1] at he
  obtain ⟨s1, hs1, -, h1m⟩ := triple_of_callW (ctorX_spec p hP (realCall p) (realCall_spec p) k ⟨m, Locals.init []⟩
    vis0 vis T lo ll nP nIdx rs isP lg w2 w3 cvTaw) (callW_of_callE h1)
  subst hs1
  obtain hk3 | ⟨j, rfl⟩ : k < 3 ∨ ∃ j, k = j + 3 := by
    rcases Nat.lt_or_ge k 3 with h | h
    · exact .inl h
    · exact .inr ⟨k - 3, by omega⟩
  · exfalso
    have : ctorX (realCall p) k m vis0 vis T lo ll nP nIdx rs isP lg w2 w3 cvTaw = none := by
      match k, hk3 with
      | 0, _ => rfl
      | 1, _ => rfl
      | 2, _ => rfl
    rw [this] at h1m
    cases h1m
  obtain ⟨x, a1, hrun1, hC1, hg1, hr0, hx1, hsorts, hsb, hA1, c1⟩ :=
    ctorW_okC hq henv hV hOpf hLC hLT hApd hCrk j (by omega) m a vis0 T lo ll nP nIdx rs isP lg w2 w3 cvTaw lps cv cvTa
      hC hT hlps hlb hcvB hta hrs hni hnf hA hTP hlpsP hrsP hcvP hcvTaP hws hok₀ hfe r s1.mem h1m
  refine ErrClaim.bind_right hrun1 ?_
  have hS1 := hC1.stage
  obtain ⟨cvCa, sorts⟩ := x
  simp only at hx1 hsorts
  subst hx1
  -- `rec2` for the record
  cases h2 : callE p (j + 3) "rec2" [r.headD 0, w3] s1.mem with
  | error e2 =>
    rw [h2, sctsE.k_rec2.none] at he
    cases he
    exact ErrClaim.bind_left (ErrClaim.of_callE_nv hnv (by decide +kernel) h2)
  | ok q2 =>
  obtain ⟨rn, m2⟩ := q2
  rw [h2, sctsE.k_rec2.arm1] at he
  obtain ⟨s2, hs2, -, hn⟩ := triple_of_callW (rec2_specW p hP.ha (j + 3) hP.hrec2 ⟨s1.mem, Locals.init []⟩ (r.headD 0) w3)
    (callW_of_callE h2)
  subst hs2
  obtain ⟨hS2, hg2, hn0, hn1⟩ := sumRec2 hn hS1
  have hA2 : AbsOK s2.mem := recW_afr hn hA1
  have hC2 : StageC dn vis fe env s2.mem a1 := hC1.of_pstep hS2 hA2 (PStep.refl hC1.check.state)
  cases h3 : callE p (j + 3) "rec2" [r.tail.headD 0, r.tail.tail.headD 0] s2.mem with
  | error e3 =>
    rw [h3, sctsE.k_rec2_2.none] at he
    cases he
    exact ErrClaim.bind_left (ErrClaim.of_callE_nv hnv (by decide +kernel) h3)
  | ok q3 =>
  obtain ⟨rh, m3⟩ := q3
  rw [h3, sctsE.k_rec2_2.arm1] at he
  obtain ⟨s3, hs3, -, hh⟩ := triple_of_callW (rec2_specW p hP.ha (j + 3) hP.hrec2 ⟨s2.mem, Locals.init []⟩
    (r.tail.headD 0) (r.tail.tail.headD 0)) (callW_of_callE h3)
  subst hs3
  obtain ⟨hS3, hg3, hh0, hh1⟩ := sumRec2 hh hS2
  have hA3 : AbsOK s3.mem := recW_afr hh hA2
  have hC3 : StageC dn vis fe env s3.mem a1 := hC2.of_pstep hS3 hA3 (PStep.refl hC2.check.state)
  have x1 := c1.ext
  have hg03 := (hg1.trans hg2).trans hg3
  have hcO1 : (cO + 1).toNat = cO.toNat + 1 := sumToNat_succ (by omega)
  have hcL1 : (cL - 1).toNat = L := by rw [sumToNat_pred hl]; omega
  refine ErrClaim.bind_left ?_
  cases h4 : sctsE p (j + 3) s3.mem vis0 vis T lo ll nP nIdx rs isP lg cvTaw (cO + 1) (cL - 1) with
  | error e4 =>
    rw [h4, sctsE.k_check_sum_ctors.none] at he
    cases he
    exact ih (by omega) s3.mem a1 (cO + 1) (cL - 1) cs restP hC3 (by rw [decHL_grow hg03 hlb]; exact hlps)
      (by have := hg03.1; omega) (DecB.grow (OMono.decCVp _) hg03 hta)
      (by rw [hcO1, hcL1]; exact DecB.grow (OMono.decPL decCN_mono _ _) hg03 htail) hA3
      (ConRon.Bridge.denoteN_ext hTP x1) (ConRon.Bridge.denoteNListE_ext x1 _ _ hlpsP)
      (ConRon.Bridge.denoteL_ext hrsP x1) (ConRon.Bridge.denoteCV_ext hcvTaP x1)
      (ConRon.Bridge.Inductives.denoteCtors_ext x1 _ _ hrestP) (hok₀.mono x1)
      (ConRon.Bridge.denoteFEnv_mono x1 hfe) _ h4
  | ok q4 =>
  obtain ⟨rr, m4⟩ := q4
  rw [h4, sctsE.k_check_sum_ctors.arm1] at he
  cases h5 : callE p (j + 3) "sl_cons" [rn.headD 0, rr.headD 0, rr.tail.headD 0] m4 with
  | error e5 =>
    rw [h5, sctsE.k_sl_cons.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h5
  | ok q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [h5, sctsE.k_sl_cons.arm1] at he
  cases h6 : callE p (j + 3) "sl_cons" [rh.headD 0, rr.tail.tail.headD 0, rr.tail.tail.tail.headD 0] m5 with
  | error e6 =>
    rw [h6, sctsE.k_sl_cons_2.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h6
  | ok q6 =>
  rw [h6, sctsE.k_sl_cons_2.arm1] at he
  cases he

include hq henv hV hOpf hLC hLT hApd hCrk hnv hcE hCcv in
/-- **`check_sum_ctors`' error claim** (the hypotheses of `checkSumCtors_refinesC`, the core stubs'
and `check_constant_val`'s error claims): a failing call of class `1`/`2` claims that the twin's
`checkSumCtors` fails. -/
theorem checkSumCtors_claim (hP : SumProg p) (k : Nat) (hk : k ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (vis0 T lo ll nP nIdx rs isP lg cvTaw cO cL : Word) (lps : List NIdx) (cvTa : IConstantVal)
    (cs : List (IConstantVal × Nat)) (hC : StageC dn vis fe env s₀.mem a₀) (hT : H T) (hrs : H rs)
    (hlps : decHL s₀.mem lo.toNat ll.toNat = some lps) (hlb : lo.toNat + ll.toNat ≤ iwTop s₀.mem)
    (hta : DecB (fun m => decCVp m cvTaw.toNat) s₀.mem cvTa)
    (hcs : DecB (fun m => decPL m (decCN m) cO.toNat cL.toNat) s₀.mem cs) (hA : AbsOK s₀.mem)
    {env₀ : ConLeche.Env} {TP : ConLeche.Name} {lpsP : List ConLeche.Name} {rsP : ConLeche.Level}
    {cvTaP : ConLeche.ConstantVal} {csP : List (ConLeche.ConstantVal × Nat)}
    (hTP : denoteN a₀.store.ns (decI T) = some TP)
    (hlpsP : Frontend.denoteNList a₀.store.ns lps = some lpsP)
    (hrsP : denoteL a₀.store.ls (decI rs) = some rsP)
    (hcvTaP : Frontend.denoteCV a₀.store cvTa = some cvTaP) (hws : ConLeche.Expr.WScoped 0 cvTaP.type)
    (hcsP : ConRon.Bridge.Inductives.denoteCtors a₀.store cs = some csP)
    (hok₀ : ConRon.Bridge.Inductives.IFEnvOKS env₀ (fe.restrictTo vis0.toNat) a₀.store)
    (hfe : ConRon.Bridge.denoteFEnv a₀.store fe = some env) :
    CoreSpecE p k "check_sum_ctors" [vis0, vis, T, lo, ll, nP, nIdx, rs, isP, lg, cvTaw, cO, cL]
      (checkSumCtors V (fe.restrictTo vis0.toNat) fe (decI T) lps nP.toNat nIdx.toNat (decI rs)
        (isP != 0) (lg != 0) cvTa cs) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc' => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (sctsE_spec p hP.hcs k ⟨s₀.mem, Locals.init []⟩ vis0 vis T lo ll nP nIdx rs
    isP lg cvTaw cO cL) hc' (Err.code_ne_of_cls hk0)
  exact sctsE_claim hq henv hV hOpf hLC hLT hApd hCrk hnv hcE hCcv hP vis0 T lo ll nP nIdx rs isP lg cvTaw lps cvTa
    hT hrs hws k hk s₀.mem a₀ cO cL cs csP hC hlps hlb hta hcs hA hTP hlpsP hrsP hcvTaP hcsP hok₀ hfe er hW

end sims

end L.Ind
