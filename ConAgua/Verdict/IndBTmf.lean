import ConAgua.Verdict.IndBTmc
import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen
/-!
# Error refinement of `target_major_of` (lane `verdicts-b`, helper `ib`)

Mirrors `tmfW_simC` (`IndT/RecGenTmf`): `get_app_args_f`, `get_app_fn_f` and `e_view` are
`closedNV`; the reject is the twin's "not an inductive's application" fail; the tail is
`tmc_claim`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dMajor)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model tmfE_spec (p : Prog) (hf : p.lookup "target_major_of" = some targetMajorOf)
  fns [hf ↦ tmfE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] errors

section sims
variable {p : Prog} (hP : TmfProg p) (hIlpf : IlpfF p) (hcore : CoreStageClosed p)
  (hLC : LvlCacheProg p) (hnv : closedNV p _root_.L.Checker.nvFns = true) {env : ConLeche.Env}
  {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

include hP hIlpf hcore hLC hnv in
theorem tmfE_claim (n : Nat) {m : Mem} {a : AState}
    {pp cao cal pfo pfl fvo fvl mty : Word} {bs : BlockShape}
    {css : List (List (IConstantVal × Nat))} {pfvs fvs : List EIdx}
    (hS : StageR dn vis fe m a) (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp)
    (hcss : PSlR decCNS css cao cal m) (hpf : DecB (fun m => decHL m pfo.toNat pfl.toNat) m pfvs)
    (hfv : DecB (fun m => decHL m fvo.toNat fvl.toNat) m fvs) (hfvb : fvo.toNat + fvl.toNat ≤ iwTop m)
    (hmty : H mty) (hPm : PosMR m)
    (hC : StageC dn vis fe env m a) (hA : AbsOK m) {pP : ConLeche.BlockShape}
    (hshP : ConRon.Bridge.Inductives.dShape a.store bs = some pP) {mtyP : ConLeche.Expr}
    (hmtyP : denoteE a.store (decI mty) = some mtyP) :
    ∀ e, tmfE p (n + 1) m vis pp cao cal pfo pfl fvo fvl mty = .error e →
      ErrClaim (ConRon.Arena.targetMajorOf fe bs css pfvs fvs (decI mty)) a e := by
  intro e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  rw [targetMajorOf_eq]
  rw [tmfE.arm1] at he
  cases h1 : callE p n "get_app_args_f" [CWF, mty] m with
  | error e1 =>
    rw [h1, tmfE.k_get_app_args_f.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  obtain ⟨s1, hs1, -, hs1'⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (gaaF_spec p hP.ad n _ [CWF, mty]) (callW_of_callE h1)
  obtain ⟨x, a', hrun, hS1, hg1, hd1⟩ := gaaF_ok dn vis fe CWF mty hmty m s1.mem a r1 hs1' hS
  rw [CWF_eq] at hrun
  obtain ⟨ha', hargs⟩ := ConRon.Bridge.Inductives.getAppArgs_run hC.check.state hmtyP hrun
  subst ha'
  refine ErrClaim.bind_right hrun ?_
  subst hs1
  rw [h1, tmfE.k_get_app_args_f.arm1] at he
  obtain ⟨hd1', hb1⟩ := hd1
  have hP1 : PosMR s1.mem := hPm.fr (MFr.ofGaaF hs1')
  have hA1 : AbsOK s1.mem := gaaF_afr hs1' hA
  have hC1 : StageC dn vis fe env s1.mem a' := hC.of_pstep hS1 hA1 (PStep.refl hC.check.state)
  rw [getD_zero, getD_one] at hd1' hb1
  cases h2 : callE p n "get_app_fn_f" [CWF, mty] s1.mem with
  | error e2 =>
    rw [h2, tmfE.k_get_app_fn_f.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  obtain ⟨s2, hs2, -, hs2'⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (gafF_spec p hP.ad n _ [CWF, mty]) (callW_of_callE h2)
  obtain ⟨x2, a2, hrun2, hS2, hg2, hd2⟩ := gafF_ok dn vis fe CWF mty hmty s1.mem s2.mem a' r2 hs2' hS1
  rw [CWF_eq] at hrun2
  obtain ⟨ha2, hhd⟩ := ConRon.Bridge.Inductives.getAppFn_run hC1.check.state hmtyP hrun2
  subst ha2
  refine ErrClaim.bind_right hrun2 ?_
  subst hs2
  obtain ⟨hw32, hwd⟩ := hd2
  have hP2 : PosMR s2.mem := hP1.fr (MFr.ofGafF hs2')
  have hA2 : AbsOK s2.mem := gafF_afr hs2' hA1
  have hC2 : StageC dn vis fe env s2.mem a2 := hC1.of_pstep hS2 hA2 (PStep.refl hC1.check.state)
  by_cases hng : r2.headD 0 >>> 28 ≠ 3
  · rw [h2, tmfE.k_get_app_fn_f.abort1 p n vis pp cao cal pfo pfl fvo fvl _ _ r2 _ hng] at he
    cases he
    have hct := ctag_iff (r2.headD 0) hw32 3 (by decide)
    refine ErrClaim.ite_neg ?_ (ErrClaim.fail _ _ (by decide))
    rw [← hwd, show (decI (r2.headD 0) : EIdx) = decE (r2.headD 0) from rfl]
    intro hc
    exact hng (hct.mp (beq_iff_eq.mp hc))
  have hg : r2.headD 0 >>> 28 = 3 := by simpa using hng
  rw [h2, tmfE.k_get_app_fn_f.arm1 p n vis pp cao cal pfo pfl fvo fvl _ _ r2 _ hg] at he
  have hct := ctag_iff (r2.headD 0) hw32 3 (by decide)
  have htag0 : (decE (r2.headD 0)).tag = ETag.const := hct.mpr hg
  have htag : ((decE (r2.headD 0)).tag == ETag.const) = true := by simpa using htag0
  refine ErrClaim.ite_pos (by rw [← hwd, show (decI (r2.headD 0) : EIdx) = decE (r2.headD 0) from rfl]; exact htag) ?_
  cases h3 : callE p n "e_view" [r2.headD 0] s2.mem with
  | error e3 =>
    rw [h3, tmfE.k_e_view.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h3
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  obtain ⟨s3, hs3, hs3'⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (eView_spec p hP.ev n _ (r2.headD 0)) (callW_of_callE h3)
  obtain ⟨hs3e, hne, hr3⟩ := hs3'
  have hm3 : s3.mem = s2.mem := by rw [hs3e]
  obtain ⟨hrun3, hxH, hyH⟩ := viewConstW hS2.1.arena.1 (by rw [← hr3]; exact hne) hg
  rw [← hr3] at hrun3 hxH hyH
  obtain ⟨-, hvc⟩ := ConRon.Bridge.Inductives.viewConst_run hrun3
  subst hwd
  rw [show (decI (r2.headD 0) : EIdx) = decE (r2.headD 0) from rfl] at hhd ⊢
  obtain ⟨IP, usP, -, hIP, husP⟩ := ConRon.Bridge.denote_const_inv hC2.check.state.wf
    (ConRon.Bridge.view_of_viewConst_tag htag hvc.symm) hhd
  refine ErrClaim.bind_right hrun3 ?_
  simp only
  have hm3' : m3 = s2.mem := hs3.symm.trans hm3
  subst hm3'
  rw [h3, tmfE.k_e_view.arm1] at he
  have hg12 := hg1.trans hg2
  cases h4 : callE p n "target_major_of_const" [vis, pp, cao, cal, pfo, pfl, fvo, fvl, r1.headD 0, r1.tail.headD 0,
      r3.tail.headD 0, r3.tail.tail.headD 0] s2.mem with
  | error e4 =>
    rw [h4, tmfE.k_target_major_of_const.none] at he
    cases he
    exact CoreSpecE.of_callE (tmc_claim hP hIlpf hcore hLC hnv n (s₀ := ⟨s2.mem, Locals.init []⟩) hS2
      (hq.grow (decBS_mono _) hg12) (partsHsrc_grow hg12 (partsShapeFacts hq hsrc).2.1 hsrc)
      (hcss.grow decCNS_mono hg12) (hpf.grow (OMono.decHL _ _) hg12) (hfv.grow (OMono.decHL _ _) hg12)
      (Nat.le_trans hfvb hg12.1)
      (decHL_decB (by rw [decHL_grow hg2 hb1]; exact hd1') (Nat.le_trans hb1 hg2.1))
      (Nat.le_trans hb1 hg2.1) hxH hyH hP2 hC2 hA2 hshP hIP husP hargs) h4
  | ok q4 =>
    rw [h4] at he
    simp [tmfE.k_target_major_of_const] at he

include hP hIlpf hcore hLC hnv in
/-- **`target_major_of`'s error claim** (every fuel). -/
theorem tmf_claim (N : Nat) {s₀ : St} {a : AState}
    {pp cao cal pfo pfl fvo fvl mty : Word} {bs : BlockShape}
    {css : List (List (IConstantVal × Nat))} {pfvs fvs : List EIdx}
    (hS : StageR dn vis fe s₀.mem a) (hq : DecB (fun m => decBS m pp.toNat) s₀.mem bs) (hsrc : ShapeSrc s₀.mem pp)
    (hcss : PSlR decCNS css cao cal s₀.mem) (hpf : DecB (fun m => decHL m pfo.toNat pfl.toNat) s₀.mem pfvs)
    (hfv : DecB (fun m => decHL m fvo.toNat fvl.toNat) s₀.mem fvs) (hfvb : fvo.toNat + fvl.toNat ≤ iwTop s₀.mem)
    (hmty : H mty) (hPm : PosMR s₀.mem)
    (hC : StageC dn vis fe env s₀.mem a) (hA : AbsOK s₀.mem) {pP : ConLeche.BlockShape}
    (hshP : ConRon.Bridge.Inductives.dShape a.store bs = some pP) {mtyP : ConLeche.Expr}
    (hmtyP : denoteE a.store (decI mty) = some mtyP) :
    CoreSpecE p N "target_major_of" [vis, pp, cao, cal, pfo, pfl, fvo, fvl, mty]
      (ConRon.Arena.targetMajorOf fe bs css pfvs fvs (decI mty)) s₀ a := by
  cases N with
  | zero => exact CoreSpecE.zero _ _ _ _ _ _
  | succ n =>
    refine CoreSpecE.of_runs fun e hc => ?_
    by_cases hk0 : e.cls = 0
    · exact ErrClaim.of_cls0 hk0
    exact tmfE_claim hP hIlpf hcore hLC hnv n hS hq hsrc hcss hpf hfv hfvb hmty hPm hC hA hshP hmtyP e
      (triple_of_callE_err (tmfE_spec p hP.tmf (n + 1) s₀ vis pp cao cal pfo pfl fvo fvl mty) hc
        (Err.code_ne_of_cls hk0))

end sims

end L.Ind
