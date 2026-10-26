import ConAgua.Verdict.DeclAxiomE
import ConAgua.Arena.DeclDefnT

/-!
# The verdict claim of the definition arm `check_decl_defn` (lane `verdicts-b`, helper `d`)

The constant check, the definition check and the two gates' failures claim the twin's `checkDecl`
failure. The gates' error claims (`NatGateSpecE`, `DivGateSpecE`) are hypotheses here
(`DeclGatesE.lean` proves them).
-/

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind
open L.Rom (PinSetsR)
open L.Front (DECL DLP DeclsF DeclAt CVAt dw)
open ConRon.Bridge (FoldOK PinsDenote CheckOK StepOK)

local notation "V" => ConLeche.CheckMode.verified

l_model checkDeclDefn_specE (p : Prog) (hf : p.lookup "check_decl_defn" = some checkDeclDefn)
  fns [hf ↦ checkDeclDefnE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] errors

/-- **`defn_nat_gate`'s error claim under `StageC`** (the error half of `defnNatGate_okC`). -/
def NatGateSpecE (p : Prog) : Prop :=
  ∀ (dn : NIdx → Option ConLeche.Name) (vis w : Word) (fe2 : IFEnv) (env env2 : ConLeche.Env)
    (n : Word) (nm : ConLeche.Name) (k : Nat), k ≤ 2 ^ 62 → ∀ (m : Mem) (a : AState), H n →
    StageR dn w fe2 m a → StageC dn vis (fe2.restrictTo vis.toNat) env m a →
    ConLeche.EnvWF env → StepOK env2 fe2 a → denoteN a.store.ns (decI n) = some nm →
    ∀ e, callE p k "defn_nat_gate" [vis, w, n] m = .error e →
    ErrClaim (natGateT (fe2.restrictTo vis.toNat) fe2 (decI n)) a e

/-- **`defn_div_gate`'s error claim under `StageC`** (the error half of `DivGateSpecC`). -/
def DivGateSpecE (p : Prog) (pins : List INatOpPinSet) : Prop :=
  ∀ (dn : NIdx → Option ConLeche.Name), DnInj dn → ∀ (vis w : Word) (fe2 : IFEnv)
    (env env2 : ConLeche.Env) (n : Word) (nm : ConLeche.Name) (k : Nat), k ≤ 2 ^ 62 →
    ∀ (m : Mem) (a : AState), n.toNat < 2 ^ 32 →
    StageR dn w fe2 m a → StageC dn vis (fe2.restrictTo vis.toNat) env m a →
    ConLeche.EnvWF env → StepOK env2 fe2 a → PinSetsR m pins →
    (∃ pinsP, PinsDenote a.store pins pinsP) →
    denoteN a.store.ns (decI n) = some nm → L.Stubs.CrOK m →
    ∀ e, callE p k "defn_div_gate" [vis, w, n] m = .error e →
    ErrClaim (divGateT pins (fe2.restrictTo vis.toNat) fe2 (decI n)) a e

section defn
variable (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name) (ds : Array IDeclaration)

/-- **`check_decl_defn`'s error claim under `StageT`.** -/
theorem checkDeclDefn_errT {p : Prog} (hA : ArmProg p) (hV : ValProg p)
    (hG : DefnProgT p pins) (hq : KnotStageProg p) (hcl : LeafClosed p)
    (hlc : LoopClosed p) (hap : ApdF p) (hkp : CrKeep p)
    (hnv : closedNV p L.Checker.nvFns = true) (hcE : CoreStubsE p) (hivE : IvgE p)
    (hNG : NatGateSpecE p) (hDG : DivGateSpecE p pins) (hdn : DnInj dn)
    (cv : IConstantVal) (v : EIdx) (hh : ConLeche.ReducibilityHint) :
    ArmSpecE pins dn ds p "check_decl_defn" (.defnDecl cv v hh) := by
  unfold ArmSpecE
  intro n hn m a vis fe pend i hi hd hok hR hS hF hden hPD hCr e hc
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (checkDeclDefn_specE p hG.df n ⟨m, Locals.init []⟩ i vis) hc
    (Err.code_ne_of_cls hk0)
  have hd' : ds[i.toNat] = .defnDecl cv v hh := by
    rw [Array.getElem?_eq_getElem hi] at hd; exact Option.some.inj hd
  obtain ⟨env, hfold⟩ := hF
  obtain ⟨x, hx⟩ := hden
  simp only [Frontend.denoteDecl] at hx
  split at hx
  rotate_left
  · cases hx
  rename_i c e' hcvd hvd
  cases n with
  | zero => rw [checkDeclDefnE.eq_1] at hW; cases hW; exact absurd rfl hk0
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  have hfr : ∀ {k : Nat} {f : FnName} {args : List Word} {mx my : Mem} {rx : List Word},
      f ∈ armFns → callW p k f args mx = some (rx, my) → MemFrame stepA stepC mx my := by
    intro k f args mx my rx hf hc
    obtain ⟨s', hs', hfr', -⟩ := triple_of_callW (s₀ := ⟨mx, Locals.init []⟩)
      (hA.closed.memFrame k hf args ⟨mx, Locals.init []⟩) hc
    rw [← hs']; exact hfr'
  rw [checkDeclDefnE.arm1] at hW
  rw [checkDecl_defn_eq]
  -- `erec_ci`
  cases h1 : callE p n "erec_ci" [i, 1] m with
  | error e1 =>
    rw [h1, checkDeclDefnE.k_erec_ci.none] at hW; cases hW
    exact nvl hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, checkDeclDefnE.k_erec_ci.arm1] at hW
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callE (erecCi_specW p hV.rcp n ⟨m, Locals.init []⟩ i 1) h1
  subst hs1
  obtain ⟨hS1, hg1, hci1, hcv1, hval1, htop1⟩ :=
    erecCiW_okT (ci := .defnInfo cv v hh) hW1 hS hR.decls hi (by rw [hd']; rfl)
  have hCr1 := CrOK.frame hCr (erecCiW_frame hW1) (by decide) (by decide)
  have hPS1 := PinSetsR.step hR.pinsets hg1 (hfr (by decide) (callW_of_callE h1))
  rw [hd'] at hcv1 hval1
  simp only [stepCV, stepVal] at hcv1 hval1
  generalize hq0 : r1.headD 0 = q at hW hci1 hcv1 hval1 htop1
  have hqb : q.toNat + 8 < 2 ^ 64 := by
    have := hS1.stage.2.2.1; have := hS1.stage.2.2.2.2.1; omega
  have hq1 : (q + 1).toNat = q.toNat + 1 := toNat_add_small q 1 (by omega)
  obtain ⟨wn, hwn, hwnl, hname0⟩ := decCI_name hci1
  have hname : cv.name = decI wn := hname0
  rw [rdW_of_get? hq1.symm (erecP_get hwn)] at hW
  -- `check_constant_val`
  cases h2 : callE p n "check_constant_val" [vis, q + 1] s1.mem with
  | error e2 =>
    rw [h2, checkDeclDefnE.k_check_constant_val.none] at hW; cases hW
    exact ErrClaim.bind_left (ccvE_okT hq hV hap hkp hnv hcE hn' h2 hS1 (by rw [hq1]; exact hcv1)
      (by omega) (denoteCV_lps hcvd) hCr1)
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, checkDeclDefnE.k_check_constant_val.arm1] at hW
  obtain ⟨s2, hs2, -, hok2, hS2, hg2, hCr2⟩ := triple_of_callE
    (checkConstantVal_refinesT p hV hq hap hkp n hn' ⟨s1.mem, Locals.init []⟩ a dn fe vis (q + 1) cv hS1
      (by rw [hq1]; exact hcv1) (by omega) (denoteCV_lps hcvd) hCr1) h2
  subst hs2
  have hPS2 := PinSetsR.step hPS1 hg2 (hfr (by decide) (callW_of_callE h2))
  have hrun2 := AM.run_of_ok _ _ hok2
  obtain ⟨hstep1, F1, hpure1⟩ :=
    ConRon.Bridge.checkConstantVal_bridge_of_fold rfl (ConRon.Bridge.CoreSpec.of_core rfl) hfold hcvd hrun2
  have hok1 := hfold.ofCore hstep1
  have hcA := ConRon.Bridge.denoteCV_ext hcvd hstep1.ext
  have hv1 := ConRon.Bridge.denote_ext hvd hstep1.ext
  have hPD1 : ∃ pinsP, PinsDenote (AM.st (checkConstantVal V fe cv) a).store pins pinsP := by
    obtain ⟨pp, hp⟩ := hPD; exact ⟨pp, PinsDenote.mono hstep1.ext _ _ hp⟩
  refine ErrClaim.bind_right hrun2 ?_
  generalize AM.st (checkConstantVal V fe cv) a = a2 at hrun2 hS2 hok1 hcA hv1 hPD1
  -- `check_defn_val`
  cases h3 : callE p n "check_defn_val" [vis, q] s2.mem with
  | error e3 =>
    rw [h3, checkDeclDefnE.k_check_defn_val.none] at hW; cases hW
    have hx2 : ArrExt (erecP s1.mem) (erecP s2.mem) := IWGrow.erecPExt hg2
    exact ErrClaim.bind_left (defnvE_okT hq hV hap hkp hcE hivE (hnvE := fun _ _ _ _ h =>
      callE_nv hnv (declNv_mem _ (by decide +kernel)) _ _ _ h) hn' hS2 (hh := hh)
      (ArrExt.decCI hx2 hci1) (ArrExt.decCV hx2 hcv1) (ArrExt.hd? hx2 hval1) (denoteCV_lps hcA) hCr2 h3)
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, checkDeclDefnE.k_check_defn_val.arm1] at hW
  have hCr3 := hkp.call (im_mem _ rfl) (callW_of_callE h3) hCr2
  have hx2 : ArrExt (erecP s1.mem) (erecP s2.mem) := IWGrow.erecPExt hg2
  obtain ⟨s3, hs3, -, hW3⟩ := triple_of_callE
    (dv_specW p hV (realCall p) (realCall_spec p) n ⟨s2.mem, Locals.init []⟩ vis q) h3
  subst hs3
  obtain ⟨a3, hrun3, hS3, hM3, hg3⟩ := dvW_okT hq hV.rcp hap hkp hn' "type mismatch in definition"
    hW3 hS2 (ArrExt.decCI hx2 hci1)
    (ArrExt.decCV hx2 hcv1) (ArrExt.hd? hx2 hval1) (denoteCV_lps hcA) hCr2
  have hPS3 := PinSetsR.step hPS2 hg3 (hfr (by decide) (callW_of_callE h3))
  rw [← checkDefnVal_dvT] at hrun3
  obtain ⟨hstep2, -, -, env2, F2, hstepOK2, hpure2⟩ := ConRon.Bridge.checkDefnVal_bridge rfl
    (ConRon.Bridge.CoreSpec.of_core rfl) hok1 hcA (ConRon.Bridge.checkConstantVal_typeWF hpure1) hv1 hrun3
  have hok3 := hok1.ofCore hstep2
  have hnm3 : denoteN a3.store.ns (decI wn) = some c.name := by
    rw [← hname]
    exact ConRon.Bridge.denoteN_ext (ConRon.Bridge.denoteCV_inv hcA).1 hstep2.ext
  have hPD3 : ∃ pinsP, PinsDenote a3.store pins pinsP := by
    obtain ⟨pp, hp⟩ := hPD1; exact ⟨pp, PinsDenote.mono hstep2.ext _ _ hp⟩
  have hvis : fe.visibleBelow = vis.toNat := hS.stage.1.env.vis
  have hpre := ConRon.Bridge.restrict_pushed_find (fe2 := fe.push (.defnInfo cv v hh)) rfl
    (hok3.check.ienv.find?_none (show denoteN a3.store.ns cv.name = some c.name by rw [hname]; exact hnm3)
      (ConRon.Bridge.checkConstantVal_fresh hpure1))
  have hck3 : CheckOK V env ((fe.push (.defnInfo cv v hh)).restrictTo vis.toNat) a3 := by
    rw [← hvis]; exact hok3.check.congr_find hpre rfl
  have hf3 := (run_memFrame hlc checkDefnVal_loop (run_of_callW (callW_of_callE h3))).1
  have hmem3 : TwinMem dn s3.mem a3 :=
    ⟨by rw [hf3.2.2.1]; exact hS2.twin.erec, by rw [hf3.2.2.1]; exact hS2.twin.spn,
      by rw [hf3.2.2.1]; exact hS2.twin.bstk, hM3,
      fun k y e => hstep2.ext.lss.ls.ns k y (hS2.twin.den.dnN k y e)⟩
  have hflag3 : pinW s3.mem 0 ≠ 0 := by
    simp only [pinW, hf3.1 PINS loopA_pins (by decide)]; exact hS2.flag
  refine ErrClaim.bind_right hrun3 ?_
  generalize hfe2 : fe.push (.defnInfo cv v hh) = fe2 at hS3 hrun3 hck3 hstepOK2
  generalize hw : r3.headD 0 = w at hW hS3
  have hC3 : StageC dn vis (fe2.restrictTo vis.toNat) env s3.mem a3 :=
    ⟨hS3.restrict vis, hck3, hmem3, hflag3⟩
  have hvb : fe2.visibleBelow = w.toNat := hS3.1.env.vis
  -- the structural gate
  cases h4 : callE p n "defn_nat_gate" [vis, w, wn] s3.mem with
  | error e4 =>
    rw [h4, checkDeclDefnE.k_defn_nat_gate.none] at hW; cases hW
    rw [hvis, hname]
    exact ErrClaim.bind_left (hNG dn vis w fe2 env env2 wn c.name n hn' s3.mem a3 hwnl hS3 hC3 hok3.envWF
      hstepOK2 hnm3 _ h4)
  | ok q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [h4, checkDeclDefnE.k_defn_nat_gate.arm1] at hW
  obtain ⟨a4, hrun4, hS4, hC4, hg4, hx4⟩ := defnNatGate_okC hG.nat hG.natGate hG.natCert hq hcl hn'
    hwnl (callW_of_callE h4) hS3 hC3 hok3.envWF hstepOK2 hnm3
  have hPS4 := PinSetsR.step hPS3 hg4 (by
    obtain ⟨s', hs', hfr', -⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
      (hG.natIn.memFrame n (f := "defn_nat_gate") (by decide) [vis, w, wn] ⟨s3.mem, Locals.init []⟩)
      (callW_of_callE h4)
    rw [← hs']; exact hfr')
  have hPD4 : ∃ pinsP, PinsDenote a4.store pins pinsP := by
    obtain ⟨pp, hp⟩ := hPD3; exact ⟨pp, PinsDenote.mono hx4 _ _ hp⟩
  rw [hvis, hname]
  refine ErrClaim.bind_right hrun4 ?_
  -- the pin gate
  cases h5 : callE p n "defn_div_gate" [vis, w, wn] m4 with
  | error e5 =>
    rw [h5, checkDeclDefnE.k_defn_div_gate.none] at hW; cases hW
    exact ErrClaim.bind_left (hDG dn hdn vis w fe2 env env2 wn c.name n hn' m4 a4 hwnl hS4 hC4
      hok3.envWF (hstepOK2.mono hx4) hPS4 hPD4 (ConRon.Bridge.denoteN_ext hnm3 hx4)
      (hkp.call (im_mem _ rfl) (callW_of_callE h4) hCr3) _ h5)
  | ok q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [h5, checkDeclDefnE.k_defn_div_gate.arm1] at hW; cases hW

end defn

end L.Arena
