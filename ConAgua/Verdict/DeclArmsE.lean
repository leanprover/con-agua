import ConAgua.Verdict.DeclValsE
import ConAgua.Verdict.DeclCrpE
import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen

/-!
# The verdict claims of the `check_decl` arms (lane `verdicts-b`, helper `d`)

`ArmSpecE`: the error half of `ArmSpecT` (`Arena/CheckerT.lean`), the arm's failing runs claim
the twin's `checkDecl` failure. Under the hypotheses of the ok refinements and the callees' error
claims (`CoreStubsE`, `IvgE`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsF)
open ConRon.Bridge (FoldOK PinsDenote CheckOK StepOK)

local notation "V" => ConLeche.CheckMode.verified

l_model checkDeclThm_specE (p : Prog) (hf : p.lookup "check_decl_thm" = some checkDeclThm)
  fns [hf ↦ checkDeclThmE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] errors

l_model checkDeclOpaque_specE (p : Prog) (hf : p.lookup "check_decl_opaque" = some checkDeclOpaque)
  fns [hf ↦ checkDeclOpaqueE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] errors

section arms
variable (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)

/-- **The shape of an arm's error spec** (`ArmSpecT`'s error half): a failing run of the arm on
record `d` claims the twin's `checkDecl` failure from the same state. -/
def ArmSpecE (p : Prog) (f : FnName) (d : IDeclaration) : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (m : Mem) (a₀ : AState) (vis : Word) (fe : IFEnv)
    (pend : Array PendingCheck) (i : Word), i.toNat < ds.size → ds[i.toNat]? = some d →
    ConRon.Bridge.StateOK a₀ → LoopR pins dn m a₀ vis fe pend ds →
    StageT dn vis fe m a₀ → (∃ env, FoldOK V env fe a₀) →
    (∃ x, Frontend.denoteDecl a₀.store d = some x) → (∃ pinsP, PinsDenote a₀.store pins pinsP) →
    L.Stubs.CrOK m → ∀ e, callE p n f [i, vis] m = .error e →
    ErrClaim (checkDecl V pins fe d) a₀ e

/-- **`check_decl_thm`'s error claim under `StageT`.** -/
theorem checkDeclThm_errT {p : Prog} (hV : ValProg p) (hq : KnotStageProg p) (hap : ApdF p)
    (hkp : CrKeep p) (hnv : closedNV p L.Checker.nvFns = true) (hcE : CoreStubsE p)
    (hUL : UceLookups p) (hivE : IvgE p) (hnvP : NVAt p "pin_word") (hnvL : NVAt p "lvl_eq_c")
    (hnvE : NVAt p "env_push")
    (hp : p.lookup "check_decl_thm" = some checkDeclThm) (cv : IConstantVal) (v : EIdx) :
    ArmSpecE pins dn ds p "check_decl_thm" (.thmDecl cv v) := by
  unfold ArmSpecE
  intro n hn m a vis fe pend i hi hd _ hR hS hF hden _ hCr e hc
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (checkDeclThm_specE p hp n ⟨m, Locals.init []⟩ i vis) hc
    (Err.code_ne_of_cls hk0)
  have hd' : ds[i.toNat] = .thmDecl cv v := by
    rw [Array.getElem?_eq_getElem hi] at hd; exact Option.some.inj hd
  obtain ⟨env, hF⟩ := hF
  obtain ⟨x, hx⟩ := hden
  simp only [Frontend.denoteDecl] at hx
  split at hx
  rotate_left
  · cases hx
  rename_i c e' hcd he
  show ErrClaim (do checkConstantVal V fe cv; checkThmVal V fe cv v) a e
  cases n with
  | zero => rw [checkDeclThmE.eq_1] at hW; cases hW; exact absurd rfl hk0
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  simp only [checkDeclThmE] at hW
  cases h1 : callE p n "erec_ci" [i, 2] m with
  | error e1 =>
    rw [h1, checkDeclThmE.k_erec_ci.none] at hW; cases hW
    exact nvl hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, checkDeclThmE.k_erec_ci.arm1] at hW
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callE (erecCi_specW p hV.rcp n ⟨m, Locals.init []⟩ i 2) h1
  subst hs1
  have hCr1 := CrOK.frame hCr (erecCiW_frame hW1) (by decide) (by decide)
  obtain ⟨hS1, hg1, hci1, hcv1, hval1, htop1⟩ :=
    erecCiW_okT (ci := .thmInfo cv) hW1 hS hR.decls hi (by rw [hd']; rfl)
  rw [hd'] at hcv1 hval1
  simp only [stepCV, stepVal] at hcv1 hval1
  generalize hq0 : r1.headD 0 = q at hW hci1 hcv1 hval1 htop1
  have hqb : q.toNat + 8 < 2 ^ 64 := by
    have := hS1.stage.2.2.1; have := hS1.stage.2.2.2.2.1; omega
  have hq1 : (q + 1).toNat = q.toNat + 1 := toNat_add_small q 1 (by omega)
  -- `check_constant_val(vis, q + 1)`
  cases h2 : callE p n "check_constant_val" [vis, q + 1] s1.mem with
  | error e2 =>
    rw [h2, checkDeclThmE.k_check_constant_val.none] at hW; cases hW
    exact ErrClaim.bind_left (ccvE_okT hq hV hap hkp hnv hcE hUL hn' h2 hS1 (by rw [hq1]; exact hcv1)
      (by omega) (denoteCV_lps hcd) hCr1)
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, checkDeclThmE.k_check_constant_val.arm1] at hW
  obtain ⟨s2, hs2, -, hok2, hS2, hg2, hCr2⟩ := triple_of_callE
    (checkConstantVal_refinesT p hV hq hap hkp n hn' ⟨s1.mem, Locals.init []⟩ a dn fe vis (q + 1) cv
      hS1 (by rw [hq1]; exact hcv1) (by omega) (denoteCV_lps hcd) hCr1) h2
  subst hs2
  have hrun2 := AM.run_of_ok _ _ hok2
  obtain ⟨hstep1, _F1, hpure1⟩ :=
    ConRon.Bridge.checkConstantVal_bridge_of_fold rfl (ConRon.Bridge.CoreSpec.of_core rfl) hF hcd hrun2
  have hok1 := hF.ofCore hstep1
  have hcA := ConRon.Bridge.denoteCV_ext hcd hstep1.ext
  have hwsT : ConLeche.Expr.WScoped 0 c.type :=
    ConLeche.Expr.WScoped.of_not_hasFvar (ConRon.Bridge.checkConstantVal_typeWF hpure1).fvar
  refine ErrClaim.bind_right hrun2 ?_
  -- `check_thm_val(vis, q)`
  cases h3 : callE p n "check_thm_val" [vis, q] s2.mem with
  | error e3 =>
    rw [h3, checkDeclThmE.k_check_thm_val.none] at hW; cases hW
    have hx2 : ArrExt (erecP s1.mem) (erecP s2.mem) := IWGrow.erecPExt hg2
    exact tvE_okT hq hV hq.knot.lvc hap hkp hcE hivE hnvP hnvL hnvE hn' hS2
      (ArrExt.decCV hx2 hcv1) (ArrExt.hd? hx2 hval1) ⟨env, c, hok1.envWF, hok1.check, hcA, hwsT⟩
      hCr2 h3
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, checkDeclThmE.k_check_thm_val.arm1] at hW
  cases hW

/-- **`check_decl_opaque`'s error claim under `StageT`.** -/
theorem checkDeclOpaque_errT {p : Prog} (hV : ValProg p) (hC : CrpProg p) (hq : KnotStageProg p)
    (hcl : LeafClosed p) (hlc : LoopClosed p) (hap : ApdF p) (hkp : CrKeep p)
    (hnv : closedNV p L.Checker.nvFns = true) (hcE : CoreStubsE p) (hUL : UceLookups p)
    (hivE : IvgE p) (hnvE : NVAt p "env_push") (hdn : DnInj dn)
    (hp : p.lookup "check_decl_opaque" = some checkDeclOpaque) (cv : IConstantVal) (v : EIdx) :
    ArmSpecE pins dn ds p "check_decl_opaque" (.opaqueDecl cv v) := by
  unfold ArmSpecE
  intro n hn m a vis fe pend i hi hd _ hR hS hF hden _ hCr e hc
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (checkDeclOpaque_specE p hp n ⟨m, Locals.init []⟩ i vis) hc
    (Err.code_ne_of_cls hk0)
  have hd' : ds[i.toNat] = .opaqueDecl cv v := by
    rw [Array.getElem?_eq_getElem hi] at hd; exact Option.some.inj hd
  obtain ⟨env, hF⟩ := hF
  obtain ⟨x, hx⟩ := hden
  simp only [Frontend.denoteDecl] at hx
  split at hx
  rotate_left
  · cases hx
  rename_i c e' hcd he
  show ErrClaim (do checkConstantVal V fe cv
                    let fe2 ← checkOpaqueVal V fe cv v
                    if (← reduceOpNames).contains cv.name then
                      checkReducePin V (fe2.restrictTo fe.visibleBelow) fe2 cv.name v
                    pure fe2) a e
  cases n with
  | zero => rw [checkDeclOpaqueE.eq_1] at hW; cases hW; exact absurd rfl hk0
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [checkDeclOpaqueE.arm1] at hW
  cases h1 : callE p n "erec_ci" [i, 0] m with
  | error e1 =>
    rw [h1, checkDeclOpaqueE.k_erec_ci.none] at hW; cases hW
    exact nvl hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, checkDeclOpaqueE.k_erec_ci.arm1] at hW
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callE (erecCi_specW p hV.rcp n ⟨m, Locals.init []⟩ i 0) h1
  subst hs1
  have hCr1 := CrOK.frame hCr (erecCiW_frame hW1) (by decide) (by decide)
  obtain ⟨hS1, hg1, hci1, hcv1, hval1, htop1⟩ :=
    erecCiW_okT (ci := .axiomInfo cv) hW1 hS hR.decls hi (by rw [hd']; rfl)
  rw [hd'] at hcv1 hval1
  simp only [stepCV, stepVal] at hcv1 hval1
  generalize hq0 : r1.headD 0 = q at hW hci1 hcv1 hval1 htop1
  have hqb : q.toNat + 8 < 2 ^ 64 := by
    have := hS1.stage.2.2.1; have := hS1.stage.2.2.2.2.1; omega
  have hq1 : (q + 1).toNat = q.toNat + 1 := toNat_add_small q 1 (by omega)
  have hq5 : (q + 5).toNat = q.toNat + 5 := toNat_add_small q 5 (by omega)
  obtain ⟨wn, hwn, hwnl, hname0⟩ := decCI_name hci1
  have hname : cv.name = decI wn := hname0
  obtain ⟨wv, hwv, hwvl, rfl⟩ := hd?_some hval1
  rw [rdW_of_get? hq1.symm (erecP_get hwn), rdW_of_get? hq5.symm (erecP_get hwv)] at hW
  -- `check_constant_val`
  cases h2 : callE p n "check_constant_val" [vis, q + 1] s1.mem with
  | error e2 =>
    rw [h2, checkDeclOpaqueE.k_check_constant_val.none] at hW; cases hW
    exact ErrClaim.bind_left (ccvE_okT hq hV hap hkp hnv hcE hUL hn' h2 hS1 (by rw [hq1]; exact hcv1)
      (by omega) (denoteCV_lps hcd) hCr1)
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, checkDeclOpaqueE.k_check_constant_val.arm1] at hW
  have hCr2 := hkp.call (im_mem _ rfl) (callW_of_callE h2) hCr1
  obtain ⟨s2, hs2, -, hok2, hS2, hg2, -⟩ := triple_of_callE
    (checkConstantVal_refinesT p hV hq hap hkp n hn' ⟨s1.mem, Locals.init []⟩ a dn fe vis (q + 1) cv hS1
      (by rw [hq1]; exact hcv1) (by omega) (denoteCV_lps hcd) hCr1) h2
  subst hs2
  have hrun2 := AM.run_of_ok _ _ hok2
  obtain ⟨hstep1, F1, hpure1⟩ :=
    ConRon.Bridge.checkConstantVal_bridge_of_fold rfl (ConRon.Bridge.CoreSpec.of_core rfl) hF hcd hrun2
  have hok1 := hF.ofCore hstep1
  have hcA := ConRon.Bridge.denoteCV_ext hcd hstep1.ext
  have hv1 := ConRon.Bridge.denote_ext he hstep1.ext
  refine ErrClaim.bind_right hrun2 ?_
  generalize AM.st (checkConstantVal V fe cv) a = a2 at hrun2 hS2 hok1 hcA hv1
  -- `check_opaque_val`
  cases h3 : callE p n "check_opaque_val" [vis, q] s2.mem with
  | error e3 =>
    rw [h3, checkDeclOpaqueE.k_check_opaque_val.none] at hW; cases hW
    have hx2 : ArrExt (erecP s1.mem) (erecP s2.mem) := IWGrow.erecPExt hg2
    exact ErrClaim.bind_left (opaquevE_okT hq hV hap hkp hcE hivE hnvE hn' hS2
      (ArrExt.decCI hx2 hci1) (by have := ArrExt.decCV hx2 (decCI_cvTA hci1 (.inr rfl)); exact this)
      (ArrExt.hd? hx2 hval1) (denoteCV_lps hcA) hCr2 h3)
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, checkDeclOpaqueE.k_check_opaque_val.arm1] at hW
  have hCr3 := hkp.call (im_mem _ rfl) (callW_of_callE h3) hCr2
  have hx2 : ArrExt (erecP s1.mem) (erecP s2.mem) := IWGrow.erecPExt hg2
  obtain ⟨s3, hs3, -, hW3⟩ := triple_of_callE
    (ov_specW p hV (realCall p) (realCall_spec p) n ⟨s2.mem, Locals.init []⟩ vis q) h3
  subst hs3
  obtain ⟨a3, hrun3, hS3, hM3, hg3⟩ := dvW_okT hq hV.rcp hC.apd hkp hn' "type mismatch in opaque"
    hW3 hS2 (ArrExt.decCI hx2 hci1)
    (by have := ArrExt.decCV hx2 (decCI_cvTA hci1 (.inr rfl)); exact this) (ArrExt.hd? hx2 hval1)
    (denoteCV_lps hcA) hCr2
  rw [← checkOpaqueVal_dvT] at hrun3
  obtain ⟨hstep2, -, -, env2, F2, hstepOK2, hpure2⟩ := ConRon.Bridge.checkOpaqueVal_bridge rfl
    (ConRon.Bridge.CoreSpec.of_core rfl) hok1 hcA (ConRon.Bridge.checkConstantVal_typeWF hpure1) hv1 hrun3
  have hok3 := hok1.ofCore hstep2
  have hnm3 : denoteN a3.store.ns (decI wn) = some c.name := by
    rw [← hname]
    exact ConRon.Bridge.denoteN_ext (ConRon.Bridge.denoteCV_inv hcA).1 hstep2.ext
  have hv3 := ConRon.Bridge.denote_ext hv1 hstep2.ext
  have hvis : fe.visibleBelow = vis.toNat := hS.stage.1.env.vis
  have hpre := ConRon.Bridge.restrict_pushed_find (fe2 := fe.push (.axiomInfo cv)) rfl
    (hok3.check.ienv.find?_none (show denoteN a3.store.ns cv.name = some c.name by rw [hname]; exact hnm3)
      (ConRon.Bridge.checkConstantVal_fresh hpure1))
  have hck3 : CheckOK V env ((fe.push (.axiomInfo cv)).restrictTo vis.toNat) a3 := by
    rw [← hvis]; exact hok3.check.congr_find hpre rfl
  have hws : ConLeche.Expr.WScoped 0 e' :=
    ConLeche.Expr.WScoped.of_not_hasFvar (ConRon.Bridge.checkOpaqueVal_noFvar hpure2)
  have hf3 := (run_memFrame hlc checkOpaqueVal_loop (run_of_callW (callW_of_callE h3))).1
  have hmem3 : TwinMem dn s3.mem a3 :=
    ⟨by rw [hf3.2.2.1]; exact hS2.twin.erec, by rw [hf3.2.2.1]; exact hS2.twin.spn,
      by rw [hf3.2.2.1]; exact hS2.twin.bstk, hM3,
      fun k y e => hstep2.ext.lss.ls.ns k y (hS2.twin.den.dnN k y e)⟩
  have hflag3 : pinW s3.mem 0 ≠ 0 := by
    simp only [pinW, hf3.1 PINS loopA_pins (by decide)]; exact hS2.flag
  refine ErrClaim.bind_right hrun3 ?_
  generalize hfe2 : fe.push (.axiomInfo cv) = fe2 at hS3 hrun3 hck3 hstepOK2
  -- the two pins
  cases h4 : callE p n "pin_at" [43] s3.mem with
  | error e4 =>
    rw [h4, checkDeclOpaqueE.k_pin_at.none] at hW; cases hW
    exact nvl hnv (by decide +kernel) h4
  | ok q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [h4, checkDeclOpaqueE.k_pin_at.arm1] at hW
  obtain ⟨s4, hs4, -, hW4⟩ := triple_of_callE
    (pinAt_specW p hC.red.pa n ⟨s3.mem, Locals.init []⟩ 43) h4
  obtain ⟨hm4, hr4, -, -⟩ := pinAtW_ok hW4 hS3.1.pins
  have hm4' : m4 = s3.mem := hs4.symm.trans hm4
  subst hm4'
  cases h5 : callE p n "pin_at" [44] s3.mem with
  | error e5 =>
    rw [h5, checkDeclOpaqueE.k_pin_at_2.none] at hW; cases hW
    exact nvl hnv (by decide +kernel) h5
  | ok q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [h5] at hW
  obtain ⟨s5, hs5, -, hW5⟩ := triple_of_callE
    (pinAt_specW p hC.red.pa n ⟨s3.mem, Locals.init []⟩ 44) h5
  obtain ⟨hm5, hr5, -, -⟩ := pinAtW_ok hW5 hS3.1.pins
  have hm5' : m5 = s3.mem := hs5.symm.trans hm5
  subst hm5'
  have e4 : r4.headD 0 = pinW s3.mem (1 + (43 : Word).toNat) := by rw [hr4]; rfl
  have e5 : r5.headD 0 = pinW s3.mem (1 + (44 : Word).toNat) := by rw [hr5]; rfl
  have hF3 := hS3.1.pins.full hflag3
  have hcont : (reduceOpNames.run a3) =
      .ok ((List.range' 44 2).map (fun j => decI (pinW s3.mem j)), a3) := reduceOpNames_run hF3
  have hiff := contains_pins hF3 hwnl 44 2 (by omega) (by omega)
  refine ErrClaim.bind_right hcont ?_
  by_cases hin : wn = r4.headD 0 ∨ wn = r5.headD 0
  · rw [checkDeclOpaqueE.k_pin_at_2.arm1 p _ _ _ _ _ _ _ _ hin] at hW
    rw [e4, e5] at hin
    have hc : ((List.range' 44 2).map fun j => (decI (pinW s3.mem j) : NIdx)).contains (decI wn) =
        true := by
      rw [hiff]
      rcases hin with e | e
      · exact ⟨44, by omega, by omega, e.symm⟩
      · exact ⟨45, by omega, by omega, e.symm⟩
    rw [hname]
    refine ErrClaim.ite_pos hc ?_
    cases h6 : callE p n "check_reduce_pin" [vis, r3.headD 0, wn, wv] s3.mem with
    | error e6 =>
      rw [h6, checkDeclOpaqueE.k_check_reduce_pin.none] at hW; cases hW
      refine ErrClaim.bind_left ?_
      rw [hvis]
      exact crpE_okT hC hq hcl hkp hnv hcE hdn hn' hS3 hck3 hok3.envWF hstepOK2 hmem3 hflag3 hnm3
        hv3 hws hwnl hwvl hCr3 h6
    | ok q6 =>
    obtain ⟨r6, m6⟩ := q6
    rw [h6, checkDeclOpaqueE.k_check_reduce_pin.arm1] at hW
    rw [checkDeclOpaqueE.j1.arm1] at hW
    cases hW
  · rw [checkDeclOpaqueE.k_pin_at_2.arm2 p _ _ _ _ _ _ _ _ hin] at hW
    rw [checkDeclOpaqueE.j1.arm1] at hW
    cases hW

end arms

end L.Arena
