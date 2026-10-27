import ConAgua.Verdict.IndBHdr
import ConAgua.Verdict.IndBRec1
import ConAgua.Arena.IndT.RecGen7
import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree

/-!
# Error refinement of `class_rec_ty_ok` (lane `verdicts-b`, helper `ib`)
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dClassGen dRec dMajor dExt_denoteCV dClassGen_ext
  dClassGen_inv dRec_inv ROp RE mapM_option_cons_inv dRec_ext)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model classRecTyOkE_spec (p : Prog) (hf : p.lookup "class_rec_ty_ok" = some classRecTyOkL)
  fns [hf ↦ classRecTyOkE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

section sims
variable {p : Prog} (hq : KnotStageProg p) (hApd : ApdF p) (hCrk : CrKeep p)
  (hnv : closedNV p _root_.L.Checker.nvFns = true) (hcE : CoreStubsE p) (hU : UceProg p)
  {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq hApd hCrk hnv hcE henv hU in
/-- **`class_rec_ty_ok`'s error claim** (the hypotheses of `classRecTyOk_refinesC`, and the core
stubs' error claims): a failing call of class `1`/`2` claims that the twin's `classRecTyOk` fails. -/
theorem classRecTyOk_claim (hp : RtoProg p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (g k rc cvRi c : Word) (G : ClassGen) (RS : RecShape) (CVRi : IConstantVal)
    (hC : StageC dn vis fe env s₀.mem a₀) (hG : DecB (fun m => decCG m g.toNat) s₀.mem G)
    (hns : G.nP + G.slots.length < 2 ^ 64) (hrc : DecB (fun m => decRS m rc.toNat) s₀.mem RS)
    (hcvR : ∀ q, iwN s₀.mem rc.toNat = some q → CVExt s₀.mem q)
    (hcvRi : DecB (fun m => decCVp m cvRi.toNat) s₀.mem CVRi) (hA : AbsOK s₀.mem)
    {gP : ConLeche.ClassGen} {rcP : ConLeche.RecShape} {cvRiP : ConLeche.ConstantVal}
    (hgP : dClassGen a₀.store G = some gP) (hrcP : dRec a₀.store RS = some rcP)
    (_hRiP : Frontend.denoteCV a₀.store CVRi = some cvRiP)
    (_hRi : ConLeche.Expr.WScoped 0 cvRiP.type) :
    CoreSpecE p n "class_rec_ty_ok" [vis, g, k, rc, cvRi, c]
      (ConRon.Arena.classRecTyOk V fe G k.toNat RS CVRi c.toNat) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc' => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (classRecTyOkE_spec p hp.rto n ⟨s₀.mem, Locals.init []⟩ vis g k rc cvRi c)
    hc' (Err.code_ne_of_cls hk0)
  cases n with
  | zero => rw [classRecTyOkE.eq_1] at hW; cases hW; exact absurd rfl hk0
  | succ n =>
  rw [classRecTyOkE.arm1] at hW
  unfold ConRon.Arena.classRecTyOk
  cases n with
  | zero =>
    obtain ⟨e', he', h0⟩ := callE_zero p "class_rec_ty_ok_guards" [g, k, rc, c] s₀.mem
    rw [he', classRecTyOkE.k_class_rec_ty_ok_guards.none] at hW
    cases hW
    exact absurd h0 hk0
  | succ n =>
  cases h1 : callE p (n + 1) "class_rec_ty_ok_guards" [g, k, rc, c] s₀.mem with
  | error e1 =>
    rw [h1, classRecTyOkE.k_class_rec_ty_ok_guards.none] at hW
    cases hW
    exact rgE_claim dn fe vis hnv hp n s₀.mem a₀ g k rc c G RS hC.stage hG hns hrc hA _ er
      (triple_of_callE_err (classRecTyOkGuardsE_spec p hp.rg (n + 1) ⟨s₀.mem, Locals.init []⟩ g k rc c) h1
        (Err.code_ne_of_cls hk0))
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, classRecTyOkE.k_class_rec_ty_ok_guards.arm1] at hW
  obtain ⟨s1, hs1, -, hmg⟩ := triple_of_callW
    (classRecTyOkGuards_spec p hp (n + 1) ⟨s₀.mem, Locals.init []⟩ g k rc c) (callW_of_callE h1)
  subst hs1
  obtain ⟨tm, a1, hrun1, hS1, hg1, hA1, g1t, g2t⟩ :=
    rgW_pass dn fe vis n s₀.mem a₀ g k rc c G RS hC.stage hG hns hrc hA r1 s1.mem hmg
  obtain ⟨-, -, hcls, -, -, -, -, -⟩ := dClassGen_inv hgP
  obtain ⟨p1, -⟩ := ConRon.Bridge.Inductives.targetMajorAt_spec G.cls gP.cls c.toNat a₀ a1 tm
    hC.check.state hC.check.pins hcls hrun1
  have hC1 : StageC dn vis fe env s1.mem a1 := hC.of_pstep hS1 hA1 p1
  refine ErrClaim.bind_right hrun1 ?_
  simp only [g1t, g2t, ite_true]
  cases h2 : callE p (n + 1) "class_gen_rec_ty" [g, c] s1.mem with
  | error e2 =>
    rw [h2, classRecTyOkE.k_class_gen_rec_ty.none] at hW
    cases hW
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  by_cases h20 : r2.headD 0 = 0
  · rw [h2, classRecTyOkE.k_class_gen_rec_ty.abort1 p _ _ _ _ _ _ h20] at hW
    cases hW
    exact ErrClaim.of_cls0 rfl
  rw [h2, classRecTyOkE.k_class_gen_rec_ty.arm1 p _ _ _ _ _ _ h20] at hW
  obtain ⟨s2, hs2, -, hmg2⟩ := triple_of_callW
    (classGenRecTy_spec p hp.toGtProg (n + 1) ⟨s1.mem, Locals.init []⟩ g c) (callW_of_callE h2)
  subst hs2
  obtain ⟨o, a2, hrun2, hC2, ⟨⟨hS2, hg2, ho⟩, hA2⟩, hR2, p2⟩ :=
    (RSim.liftPP hC1 (gtW_sim dn vis fe (n + 1) s1.mem a1 g c G hS1 (hG.grow (decCG_mono _) hg1) hns hA1)
      (fun _ _ _ h => ⟨h.1.1, h.2⟩) (ConRon.Bridge.Inductives.classGenRecTy_spec G gP c.toNat)
      (dClassGen_ext p1.ext _ _ hgP)) (r2, s2.mem) hmg2
  dsimp only at hS2 hg2 ho hA2 hC2
  refine ErrClaim.bind_right hrun2 ?_
  rcases o with _ | gty
  · exact absurd ho h20
  obtain ⟨gtyP, -, hgtyd⟩ := hR2
  obtain ⟨h21, hgH, hgd⟩ := ho
  subst hgd
  have hg12 := hg1.trans hg2
  obtain ⟨q0, hq0, -⟩ := rec2DecRS_parts (show decRS (truncM s₀.mem) rc.toNat = some RS from hrc)
  obtain ⟨hrct, hq0m⟩ := rec2IwN_trunc hq0
  have hq2 : iwN s2.mem rc.toNat = some q0 := by rw [iwN_grow hg12 hrct]; exact hq0m
  obtain ⟨q0', hq0', hcv2, -⟩ := rec2DecRS_parts (hrc.stab (decRS_mono _) s2.mem hg12)
  rw [hq2] at hq0'; cases hq0'
  have hext2 := CVExt_grow hg12 (hcvR q0 hq0m)
  obtain ⟨erc, trc⟩ := rec2RdN (w := rc) (k := 0) (by simpa using hq2) hS2.2.2.2.1
  simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero] at erc
  rw [erc] at hW
  cases h3 : callE p (n + 1) "cv_new" [rdW (s2.mem.arr64 EREC) (UInt64.ofNat q0),
      rdW (s2.mem.arr64 EREC) (UInt64.ofNat q0 + 1), rdW (s2.mem.arr64 EREC) (UInt64.ofNat q0 + 2),
      r2.tail.headD 0] s2.mem with
  | error e3 =>
    rw [h3, classRecTyOkE.k_cv_new.none] at hW
    cases hW
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h3
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, classRecTyOkE.k_cv_new.arm1] at hW
  obtain ⟨s3, hs3, -, hm3⟩ := triple_of_callW
    (cvNew_specW p hp.era hp.cvn (n + 1) ⟨s2.mem, Locals.init []⟩ _ _ _ _) (callW_of_callE h3)
  subst hs3
  obtain ⟨hS3, hg3, hqe, htop3, hsl3, hdec3⟩ := cvNew_stage (cq := UInt64.ofNat q0) hm3 hS2
    (by rw [trc]; exact hcv2) (by rw [trc]; exact hext2.1) (by rw [trc]; exact hext2.2) hgH
  have hext3 : CVExt s3.mem (r3.headD 0).toNat :=
    ⟨by omega, fun o l ho hl => (hsl3 o l ho hl).imp_left fun h => Nat.le_trans h hg3.2.1⟩
  have hqb : (r3.headD 0).toNat + 3 < 2 ^ 64 := by
    obtain ⟨-, hE1, -, hEs, -⟩ := hS3.2
    omega
  have hA3 := cvNewW_afr hm3 hA2
  have hC3 : StageC dn vis fe env s3.mem a2 := hC2.of_pstep hS3 hA3 (PStep.refl hC2.check.state)
  have p12 := p1.trans p2
  obtain ⟨hnm, hlps, -⟩ :=
    ConRon.Bridge.Core.denoteCV_inv (dExt_denoteCV p12.ext _ _ (dRec_inv hrcP).1)
  have hcvG : Frontend.denoteCV a2.store { RS.cvR with type := decI (r2.tail.headD 0) } =
      some { rcP.cvR with type := gtyP } := by
    simp only [Frontend.denoteCV, hnm, hlps, hgtyd]
  dsimp only
  have hq4 : decCV (erecP s3.mem) (r3.headD 0).toNat = some
      { name := RS.cvR.name, levelParams := RS.cvR.levelParams, type := decI (r2.tail.headD 0) } :=
    rec2DecCV_erecP hdec3 hext3
  cases h4 : callE p (n + 1) "class_const_ok" [vis, r3.headD 0] s3.mem with
  | error e4 =>
    rw [h4, classRecTyOkE.k_class_const_ok.none] at hW
    cases hW
    refine ErrClaim.bind_left ?_
    exact CoreSpecE.of_callE (classConstOk_claim hq hApd hCrk hnv hcE hU hp.ih hp.ccoh hp.cco (n + 1)
      (by omega) s3 a2 (r3.headD 0) _ hC3.stageT hq4 hqb hA3 (denoteCV_lps hcvG)) h4
  | ok q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [h4, classRecTyOkE.k_class_const_ok.arm1] at hW
  obtain ⟨s4, hs4, -, hm4⟩ := triple_of_callW
    (classConstOk_spec p hp.ih hp.ccoh hp.cco (realCall p) (realCall_spec p) (n + 1)
      ⟨s3.mem, Locals.init []⟩ vis (r3.headD 0)) (callW_of_callE h4)
  subst hs4
  obtain ⟨u, a4, hrun4, ⟨⟨⟨hC4, hg4, -⟩, hA4⟩, hwG, c4⟩⟩ :=
    (ccoW_simC hq hApd hCrk henv (n + 1) (by omega) s3.mem a2 (r3.headD 0) _ hC3 hq4 hqb hA3 hcvG)
      (r4, s4.mem) hm4
  refine ErrClaim.bind_right hrun4 ?_
  dsimp only at hA4 hC4 hg4
  have hg14 := hg12.trans (hg3.trans hg4)
  have hri := hcvRi.stab (OMono.decCVp _) s4.mem hg14
  obtain ⟨wt, hwt, hwtH, hwtE⟩ := decCV_typeW hri
  have hEi := (Array.getElem?_eq_some_iff.mp hwt).1
  have hE64 := hC4.stage.2.2.2.2.1
  have et : rdW (s4.mem.arr64 EREC) (cvRi + 3) = wt :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp [erA] at hEi ⊢; omega) hwt
  rw [et] at hW
  rw [hwtE]
  cases h5 : callE p (n + 1) "is_def_eq_core" [vis, 0, wt, r2.tail.headD 0] s4.mem with
  | error e5 =>
    rw [h5, classRecTyOkE.k_is_def_eq_core.none] at hW
    cases hW
    refine ErrClaim.bind_left ?_
    have := hcE.isDefEqCore (n + 1) (by omega) hC4.stageT 0 wt (r2.tail.headD 0) hwtH hgH _ h5
    simpa using this
  | ok q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [h5] at hW
  have hi := isDefEqT_rsim hq (n + 1) (by omega) hC4.stageT 0 wt (r2.tail.headD 0) hwtH hgH
  rw [show (0 : Word).toNat = 0 from rfl] at hi
  obtain ⟨bb, a5, hrun5, hS5, hg5, hbb⟩ := hi (r5, m5) (callW_of_callE h5)
  refine ErrClaim.bind_right hrun5 ?_
  by_cases h50 : r5.headD 0 = 0
  · rw [classRecTyOkE.k_is_def_eq_core.abort1 p _ r5 m5 h50] at hW
    cases hW
    have hbf : bb = false := by rw [← hbb]; simp [decBool]; simpa using h50
    subst hbf
    simp only [Bool.false_eq_true, ite_false]
    exact ErrClaim.fail _ _ (by decide)
  · rw [classRecTyOkE.k_is_def_eq_core.arm1 p _ r5 m5 h50] at hW
    cases hW

end sims

end L.Ind
