import ConAgua.Arena.DeclCrpT
import ConAgua.Verdict.DeclHdrE
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

/-!
# The verdict claim of `check_reduce_pin` (lane `verdicts-b`, helper `d`)

Under the hypotheses of `crpW_okT` and the core stubs' error claims: the three guards and the
spelling test decline (`notImplemented`), the identity certificate failing is the twin's
`internal` (class `0`: the L code aborts plainly).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind
open ConRon.Bridge (CheckOK StepOK CoreSpec)

local notation "V" => ConLeche.CheckMode.verified

l_model checkReducePin_specE (p : Prog) (hf : p.lookup "check_reduce_pin" = some checkReducePinL)
  fns [hf ↦ checkReducePinE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] errors

theorem crpE_okT {p : Prog} (hC : CrpProg p) (hq : KnotStageProg p) (hcl : LeafClosed p)
    (hkp : CrKeep p) (hnv : closedNV p L.Checker.nvFns = true) (hcE : CoreStubsE p)
    {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn) {vis vis2 : Word} {fe2 : IFEnv}
    {env env2 : ConLeche.Env} {a : AState} {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem} {c v : Word}
    {nm : ConLeche.Name} {x : ConLeche.Expr}
    (hS : StageR dn vis2 fe2 m a)
    (hck : CheckOK V env (fe2.restrictTo vis.toNat) a) (henv : ConLeche.EnvWF env)
    (hok2 : StepOK env2 fe2 a) (hmem : TwinMem dn m a) (hflag : pinW m 0 ≠ 0)
    (hnm : denoteN a.store.ns (decI c) = some nm) (hvx : denoteE a.store (decI v) = some x)
    (hws : ConLeche.Expr.WScoped 0 x) (hc : c.toNat < 2 ^ 32) (hv : v.toNat < 2 ^ 32)
    (hCr : L.Stubs.CrOK m) {e : Err}
    (hce : callE p n "check_reduce_pin" [vis, vis2, c, v] m = .error e) :
    ErrClaim (checkReducePin V (fe2.restrictTo vis.toNat) fe2 (decI c) (decI v)) a e := by
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (checkReducePin_specE p hC.crp n ⟨m, Locals.init []⟩ vis vis2 c v)
    hce (Err.code_ne_of_cls hk0)
  cases n with
  | zero => rw [checkReducePinE.eq_1] at hW; cases hW; exact absurd rfl hk0
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  simp only [checkReducePinE] at hW
  simp only [checkReducePin]
  have hvb : fe2.visibleBelow = vis2.toNat := hS.1.env.vis
  have hC0 : StageC dn vis (fe2.restrictTo vis.toNat) env m a := ⟨hS.restrict vis, hck, hmem, hflag⟩
  generalize hfe : fe2.restrictTo vis.toNat = fe at hC0 hck ⊢
  -- the stored constant, at `vis2`
  cases h1 : callE p n "reduce_stored_ok" [vis2, c] m with
  | error e1 =>
    rw [h1, checkReducePinE.k_reduce_stored_ok.none] at hW; cases hW
    exact nvl hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1] at hW
  have hCr1 := hkp.call (im_mem _ rfl) (callW_of_callE h1) hCr
  obtain ⟨s1, hs1, -, hok1, hS1, hg1, hb1, -⟩ := triple_of_callE
    (reduceStoredOk_refines p hC.red dn vis2 fe2 c hc n ⟨m, Locals.init []⟩ a hS) h1
  subst hs1
  have hrun1 := AM.run_of_ok _ _ hok1
  by_cases e1 : r1.headD 0 = 0
  · rw [checkReducePinE.k_reduce_stored_ok.abort1 p _ _ _ _ _ _ e1] at hW; cases hW
    have t1 : AM.res (reduceStoredOk fe2 (decI c)) a = false := by rw [← hb1]; simpa using e1
    rw [t1] at hrun1
    refine ErrClaim.bind_right hrun1 ?_
    exact ErrClaim.ite_neg (by decide) (ErrClaim.fail _ _ rfl)
  rw [checkReducePinE.k_reduce_stored_ok.arm1 p _ _ _ _ _ _ e1] at hW
  have t1 : AM.res (reduceStoredOk fe2 (decI c)) a = true := by rw [← hb1]; simpa using e1
  rw [t1] at hrun1
  refine ErrClaim.bind_right hrun1 ?_
  refine ErrClaim.ite_pos rfl ?_
  obtain ⟨hi1, -⟩ := ConRon.Bridge.reduceStoredOk_run hck.state hck.pins hok2.ienv hnm _ _ hrun1
  generalize AM.st (reduceStoredOk fe2 (decI c)) a = a1 at hrun1 hS1 hi1
  have hC1 : StageC dn vis fe env s1.mem a1 :=
    StageC.of_leaf hC0 (by rw [← hfe]; exact hS1.restrict vis)
      (callW_leafFrame hcl (leaf_mem _ (by decide)) (callW_of_callE h1)) hi1
  have hnm1 := ConRon.Bridge.denoteN_ext hnm hi1.ext
  have hv1 := ConRon.Bridge.denote_ext hvx hi1.ext
  -- the element inductive
  cases h2 : callE p n "reduce_elem_ok" [vis, c] s1.mem with
  | error e2 =>
    rw [h2, checkReducePinE.k_reduce_elem_ok.none] at hW; cases hW
    exact nvl hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2] at hW
  have hCr2 := hkp.call (im_mem _ rfl) (callW_of_callE h2) hCr1
  obtain ⟨s2, hs2, -, hok2', hS2, hg2, hb2, -⟩ := triple_of_callE
    (reduceElemOk_refines p hC.red dn hdn vis fe c hc n ⟨s1.mem, Locals.init []⟩ a1 hC1.stage) h2
  subst hs2
  have hrun2 := AM.run_of_ok _ _ hok2'
  by_cases e2 : r2.headD 0 = 0
  · rw [checkReducePinE.k_reduce_elem_ok.abort1 p _ _ _ _ _ _ e2] at hW; cases hW
    have t2 : AM.res (reduceElemOk fe (decI c)) a1 = false := by rw [← hb2]; simpa using e2
    rw [t2] at hrun2
    refine ErrClaim.bind_right hrun2 ?_
    exact ErrClaim.ite_neg (by decide) (ErrClaim.fail _ _ rfl)
  rw [checkReducePinE.k_reduce_elem_ok.arm1 p _ _ _ _ _ _ e2] at hW
  have t2 : AM.res (reduceElemOk fe (decI c)) a1 = true := by rw [← hb2]; simpa using e2
  rw [t2] at hrun2
  refine ErrClaim.bind_right hrun2 ?_
  refine ErrClaim.ite_pos rfl ?_
  obtain ⟨hi2, -⟩ := ConRon.Bridge.reduceElemOk_run hC1.check.state hC1.check.pins
    hC1.check.ienv hnm1 _ _ hrun2
  generalize AM.st (reduceElemOk fe (decI c)) a1 = a2 at hrun2 hS2 hi2
  have hC2 := StageC.of_leaf hC1 hS2 (callW_leafFrame hcl (leaf_mem _ (by decide)) (callW_of_callE h2)) hi2
  have hnm2 := ConRon.Bridge.denoteN_ext hnm1 hi2.ext
  have hv2 := ConRon.Bridge.denote_ext hv1 hi2.ext
  -- the pin's guards
  cases h3 : callE p n "reduce_pin_guard" [vis, c] s2.mem with
  | error e3 =>
    rw [h3, checkReducePinE.k_reduce_pin_guard.none] at hW; cases hW
    exact nvl hnv (by decide +kernel) h3
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3] at hW
  obtain ⟨s3, hs3, -, hW3⟩ := triple_of_callE
    (rpg_specW p hC.bvb hC.hf hC.rpg (realCall p) (realCall_spec p) n ⟨s2.mem, Locals.init []⟩ vis c)
    h3
  subst hs3
  obtain ⟨x3, a3, hrun3, hC3, hx3, hr3, hg3, hb3⟩ :=
    rpgW_okC hC.red.pa hC.rdp hC.red.rom hcl hC.apd hkp hW3 hC2 hc hnm2 hCr2
  by_cases e3 : r3.headD 0 = 0
  · rw [checkReducePinE.k_reduce_pin_guard.abort1 p _ _ _ _ _ _ e3] at hW; cases hW
    have t3 : x3 = false := by rw [← hb3.1]; simpa using e3
    rw [t3] at hrun3
    refine ErrClaim.bind_right hrun3 ?_
    exact ErrClaim.ite_neg (by decide) (ErrClaim.fail _ _ rfl)
  rw [checkReducePinE.k_reduce_pin_guard.arm1 p _ _ _ _ _ _ e3] at hW
  have t3 : x3 = true := by rw [← hb3.1]; simpa using e3
  rw [t3] at hrun3
  refine ErrClaim.bind_right hrun3 ?_
  refine ErrClaim.ite_pos rfl ?_
  have hc2 : ConLeche.reducePinGuard env nm = true := by rw [← hr3, t3]
  have hwsP : ConLeche.Expr.WScoped 0 (ConLeche.reduceDeclPin nm) := by
    refine ConLeche.Expr.WScoped.of_not_hasFvar ?_
    simp only [ConLeche.reducePinGuard, Bool.and_eq_true, Bool.not_eq_true'] at hc2
    exact hc2.1.1.2
  have hnm3 := ConRon.Bridge.denoteN_ext hnm2 hx3
  have hv3 := ConRon.Bridge.denote_ext hv2 hx3
  -- the pin
  cases h4 : callE p n "reduce_decl_pin" [c] s3.mem with
  | error e4 =>
    rw [h4, checkReducePinE.k_reduce_decl_pin.none] at hW; cases hW
    exact nvl hnv (by decide +kernel) h4
  | ok q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [h4, checkReducePinE.k_reduce_decl_pin.arm1] at hW
  obtain ⟨s4, hs4, -, hok4, hS4, hg4, hpl, hpe⟩ := triple_of_callE
    (reduceDeclPin_refines p hC.red.pa n ⟨s3.mem, Locals.init []⟩ a3 dn fe vis c hC3.stage hc
      hC.red.rom hC.rdp) h4
  subst hs4
  have hrun4 := AM.run_of_ok _ _ hok4
  rw [← hpe] at hrun4
  obtain ⟨hi4, hpd⟩ := ConRon.Bridge.reduceDeclPin_run hC3.check.state hC3.check.pins hnm3 hrun4
  generalize AM.st (reduceDeclPin (decI c)) a3 = a4 at hrun4 hS4 hi4 hpd
  refine ErrClaim.bind_right hrun4 ?_
  have hC4 := StageC.of_leaf hC3 hS4 (callW_leafFrame hcl (leaf_mem _ (by decide)) (callW_of_callE h4)) hi4
  have hnm4 := ConRon.Bridge.denoteN_ext hnm3 hi4.ext
  have hv4 := ConRon.Bridge.denote_ext hv3 hi4.ext
  -- the value against the pin
  cases h5 : callE p n "is_def_eq_core" [vis, 0, v, r4.headD 0] s4.mem with
  | error e5 =>
    rw [h5, checkReducePinE.k_is_def_eq_core.none] at hW; cases hW
    have := hcE.isDefEqCore n hn' hC4.stageT 0 v (r4.headD 0) hv hpl _ h5
    rw [show ((0 : Word).toNat) = 0 from rfl] at this
    exact ErrClaim.bind_left this
  | ok q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [h5] at hW
  obtain ⟨x5, a5, hrun5, hT5, hg5, hx5⟩ :=
    hq.isDefEqCore_sim n hn' hC4.stageT 0 v (r4.headD 0) hv hpl r5 m5 (callW_of_callE h5)
  have h00 : (0 : Word).toNat = 0 := rfl
  have h01 : (1 : Word).toNat = 1 := rfl
  rw [h00] at hrun5
  obtain ⟨hck5, hx5', -, -⟩ := defeq_check henv hC4.check hv4 hpd hws hwsP hrun5
  have hC5 := StageC.of_T hT5 hck5
  refine ErrClaim.bind_right hrun5 ?_
  by_cases e5 : r5.headD 0 = 0
  · rw [checkReducePinE.k_is_def_eq_core.abort1 p _ _ _ _ _ _ e5] at hW; cases hW
    have t5 : x5 = false := by rw [← hx5, decBool, e5]; rfl
    rw [t5]
    exact ErrClaim.ite_neg (by decide) (ErrClaim.fail _ _ rfl)
  rw [checkReducePinE.k_is_def_eq_core.arm1 p _ _ _ _ _ _ e5] at hW
  have t5 : x5 = true := by rw [← hx5]; simpa [decBool] using e5
  rw [t5]
  refine ErrClaim.ite_pos rfl ?_
  have hnm5 := ConRon.Bridge.denoteN_ext hnm4 hx5'
  have hv5 := ConRon.Bridge.denote_ext hv4 hx5'
  -- the certificate's variable
  cases h6 : callE p n "reduce_cert_var" [c] m5 with
  | error e6 =>
    rw [h6, checkReducePinE.k_reduce_cert_var.none] at hW; cases hW
    exact nvl hnv (by decide +kernel) h6
  | ok q6 =>
  obtain ⟨r6, m6⟩ := q6
  rw [h6] at hW
  obtain ⟨s6, hs6, -, hok6, hS6, hg6, hx6⟩ := triple_of_callE
    (reduceCertVar_refines p hC.rcv n ⟨m5, Locals.init []⟩ a5 dn fe vis c hC5.stage hc) h6
  subst hs6
  have hrun6 := AM.run_of_ok _ _ hok6
  rw [hx6] at hrun6
  obtain ⟨hi6, hxv⟩ := ConRon.Bridge.reduceCertVar_run hck5.state hck5.pins hnm5 hrun6
  generalize AM.st (reduceCertVar (decI c)) a5 = a6 at hrun6 hS6 hi6 hxv
  refine ErrClaim.bind_right hrun6 ?_
  have hC6 := StageC.of_leaf hC5 hS6 (callW_leafFrame hcl (leaf_mem _ (by decide)) (callW_of_callE h6)) hi6
  have hv6 : denoteE a6.store (decE v) = some x := ConRon.Bridge.denote_ext hv5 hi6.ext
  by_cases e6 : 4294967296 ≤ r6.headD 0
  · rw [checkReducePinE.k_reduce_cert_var.abort1 p _ _ _ _ _ e6] at hW; cases hW
    exact ErrClaim.of_cls0 rfl
  rw [checkReducePinE.k_reduce_cert_var.arm1 p _ _ _ _ _ e6] at hW
  have hxl : (r6.headD 0).toNat < 2 ^ 32 := by
    have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp e6); simpa using this
  -- the application
  cases h7 : callE p n "mk_app" [v, r6.headD 0] s6.mem with
  | error e7 =>
    rw [h7, checkReducePinE.k_mk_app.none] at hW; cases hW
    exact nvl hnv (by decide +kernel) h7
  | ok q7 =>
  obtain ⟨r7, m7⟩ := q7
  rw [h7, checkReducePinE.k_mk_app.arm1] at hW
  obtain ⟨s7, hs7, -, hW7⟩ := triple_of_callE
    (mkApp_spec p hC.db hC.af hC.ap hC.ia hC.ma n ⟨s6.mem, Locals.init []⟩ v (r6.headD 0)) h7
  subst hs7
  obtain ⟨a7, hrun7, hS7, hg7⟩ := mkApp_stage hC6.stage v (r6.headD 0) hW7
  have haxl := mkAppW_hw s6.mem a6 hC6.stage.1.arena v (r6.headD 0) (r7.headD 0) s7.mem hW7
  obtain ⟨hi7, hax⟩ := ConRon.Bridge.Frontend.internE_sstep hC6.check.state
    (ConRon.Bridge.viewOK_app (by rw [hv6]; rfl) (by rw [hxv]; rfl)) hrun7
  have hax' : denoteE a7.store (decE (r7.headD 0)) = some (.app x (ConLeche.reduceCertVar nm)) := by
    rw [hax]
    simp only [denoteEView, ConRon.Bridge.denote_ext hv6 hi7.ext,
      ConRon.Bridge.denote_ext hxv hi7.ext, opt2]
  have hC7 := StageC.of_leaf hC6 hS7 (mkAppW_leafFrame hW7) hi7
  have hwsC : ConLeche.Expr.WScoped 1 (ConLeche.reduceCertVar nm) := by
    unfold ConLeche.reduceCertVar ConLeche.reduceElemTy
    split <;> simp [ConLeche.Expr.WScoped]
  have hwsA : ConLeche.Expr.WScoped 1 (.app x (ConLeche.reduceCertVar nm)) := by
    unfold ConLeche.Expr.WScoped
    exact ⟨ConLeche.Expr.WScoped.mono (by omega) hws, hwsC⟩
  have e7 : (internE (.app (decI v) (decE (r6.headD 0)))).run a6 = .ok (decE (r7.headD 0), a7) := hrun7
  refine ErrClaim.bind_right e7 ?_
  -- the identity certificate
  cases h8 : callE p n "is_def_eq_core" [vis, 1, r7.headD 0, r6.headD 0] s7.mem with
  | error e8 =>
    rw [h8, checkReducePinE.k_is_def_eq_core_2.none] at hW; cases hW
    have := hcE.isDefEqCore n hn' hC7.stageT 1 (r7.headD 0) (r6.headD 0) haxl hxl _ h8
    rw [show ((1 : Word).toNat) = 1 from rfl] at this
    exact ErrClaim.bind_left this
  | ok q8 =>
  obtain ⟨r8, m8⟩ := q8
  rw [h8] at hW
  obtain ⟨x8, a8, hrun8, hT8, hg8, hx8⟩ :=
    hq.isDefEqCore_sim n hn' hC7.stageT 1 (r7.headD 0) (r6.headD 0) haxl hxl r8 m8
      (callW_of_callE h8)
  rw [show ((1 : Word).toNat) = 1 from rfl] at hrun8
  refine ErrClaim.bind_right hrun8 ?_
  by_cases e8 : r8.headD 0 = 0
  · rw [checkReducePinE.k_is_def_eq_core_2.abort1 p _ _ e8] at hW; cases hW
    exact ErrClaim.of_cls0 rfl
  rw [checkReducePinE.k_is_def_eq_core_2.arm1 p _ _ e8] at hW
  cases hW

end L.Arena
