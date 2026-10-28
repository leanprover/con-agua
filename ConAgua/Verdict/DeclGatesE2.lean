import ConAgua.Verdict.DeclGatesE
import ConAgua.Arena.DeclDefnT
import ConAgua.Verdict.DivModPinE
import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen

/-!
# The verdict claims of the `Nat.div`-family pin gate (lane `verdicts-b`, helper `d`)
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind
open L.Rom (PinSetsR PinSetR)
open ConRon.Bridge (FoldOK PinsDenote PinSetDenote CheckOK StepOK CoreStep CoreSpec)

local notation "V" => ConLeche.CheckMode.verified

l_model checkDivModPinLoop_specE (p : Prog)
  (hf : p.lookup "check_div_mod_pin_loop" = some checkDivModPinLoopL)
  fns [hf ↦ checkDivModPinLoopE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] errors

l_model checkDivModPin_specE (p : Prog) (hf : p.lookup "check_div_mod_pin" = some checkDivModPinL)
  fns [hf ↦ checkDivModPinE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] errors

l_model defnDivGate_specE (p : Prog) (hf : p.lookup "defn_div_gate" = some defnDivGate)
  fns [hf ↦ defnDivGateE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] errors

section gate
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  {p : Prog}

/-- `check_div_mod_pin_at`'s claim in `DivModPinE`'s callee shape (`cpa_ref`'s error half). -/
theorem cpaClaimE_of (hD : DmProg8 p) (hq : KnotStageProg p) (hcl : LeafClosed p) (hkp : CrKeep p)
    (hs0 : SubstC0 p dn vis fe) (hsA : SubstCAll p dn vis fe) (henv : ConLeche.EnvWF env)
    (hcE : CoreStubsE p) (hnv : closedNV p L.Checker.nvFns = true) :
    L.Ind.CpaClaimE p dn vis fe env :=
  fun _c _value _ps _ip _psP _nm _v k hk m _a hC hc hval hP hps hn hv hwsv hpg hCr _e hce =>
    RefE.run_err (s₀ := ⟨m, Locals.init []⟩) (checkDivModPinAt_specE p hD.lCheckDivModPinAt
      hD.lCheckTypePins hD.lCheckDivModPinValue hD.lCheckDivModCerts k _ _ _ _ _) hnv hcE
      (cpa_ref hD hq hcl hkp hs0 hsA henv hk hC hc hval hP hps hn hv hwsv hpg hCr) hce

/-- **`defn_div_gate`'s error claim under `StageC`** (the error half of `divGateSpecC`). -/
theorem divGateSpecE_of (hD : DmProg10 p) (hq : KnotStageProg p) (hcl : LeafClosed p)
    (hCl : StepIn p dgFns) (hs0 : ∀ dn vis fe, SubstC0 p dn vis fe)
    (hsA : ∀ dn vis fe, SubstCAll p dn vis fe) (hkp : CrKeep p) (hcE : CoreStubsE p)
    (hnv : closedNV p L.Checker.nvFns = true) (pins : List INatOpPinSet) :
    DivGateSpecE p pins := by
  intro dn hdn vis w fe2 env env2 n nm k hk m a hn hS hC henv hok2 hP hpd hnm hCr e hce
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  obtain ⟨psPs, hpd⟩ := hpd
  have hW := triple_of_callE_err (defnDivGate_specE p hD.lDefnDivGate k ⟨m, Locals.init []⟩ vis w n)
    hce (Err.code_ne_of_cls hk0)
  cases k with
  | zero => rw [defnDivGateE.eq_1] at hW; cases hW; exact absurd rfl hk0
  | succ k =>
  have hk' : k ≤ 2 ^ 62 := by omega
  rw [defnDivGateE.arm1] at hW
  have hfrOf : ∀ {k : Nat} {f : FnName} {args : List Word} {mx my : Mem} {rx : List Word},
      f ∈ dgFns → callW p k f args mx = some (rx, my) → MemFrame stepA stepC mx my := by
    intro k f args mx my rx hf hc
    obtain ⟨s', hs', hfr', -⟩ := triple_of_callW (s₀ := ⟨mx, Locals.init []⟩)
      (hCl.memFrame k hf args ⟨mx, Locals.init []⟩) hc
    rw [← hs']; exact hfr'
  have hN : NatGateProg p := hD.toDmProg9.toDmProg8.toDmProg7.toDmProg6.toDmProg5.toDmProg2.toNatEqProg.toNatTyProg.toNatGuardProg.toNatLitProg.toNatCvProg.toNatGateProg
  unfold divGateT
  cases h1 : callE p k "nat_div_mod_names" [] m with
  | error e1 =>
    rw [h1, defnDivGateE.k_nat_div_mod_names.none] at hW; cases hW
    exact ErrClaim.bind_left (nvlG hnv (by decide +kernel) h1)
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, defnDivGateE.k_nat_div_mod_names.arm1] at hW
  obtain ⟨x1, a1, hrun1, hS1, hg1, hd1⟩ :=
    natDivModNames_ref hN (vis := w) (fe := fe2) (dn := dn) k m a r1 m1 hS (callW_of_callE h1)
  obtain ⟨e1, -⟩ := ConRon.Bridge.natDivModNames_run hC.check.pins hrun1
  rw [e1] at hrun1 hS1
  have hC1 := StageC.of_core hC (hS1.restrict vis)
    (callW_leafFrame hcl (leaf_mem _ (by decide)) (callW_of_callE h1)) (CoreStep.refl hC.check)
  have hP1 := PinSetsR.step hP hg1 (hfrOf (by simp [dgFns]) (callW_of_callE h1))
  unfold decRL at hd1
  simp only [Nat.zero_add, ntGetD0, ntGetD1] at hd1
  have hrun1' : natDivModNames.run a = .ok (x1, a) := hrun1
  refine ErrClaim.bind_right hrun1' ?_
  have hCr1 := hkp.call (im_mem _ rfl) (callW_of_callE h1) hCr
  cases h2 : callE p k "sl_contains" [r1.headD 0, r1.tail.headD 0, n] m1 with
  | error e2 =>
    rw [h2, defnDivGateE.k_sl_contains.none] at hW; cases hW
    exact nvlG hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2] at hW
  obtain ⟨x2, a2, hrun2, hS2, hg2, hd2⟩ := slContains_ref hN.lSlContains (vis := w) (fe := fe2)
    (dn := dn) (r1.headD 0) (r1.tail.headD 0) n x1 (by exact_mod_cast hn) k m1 a r2 m2
    ⟨hS1, hd1.1⟩ (callW_of_callE h2)
  have hP2 := PinSetsR.step hP1 hg2 (hfrOf (by simp [dgFns]) (callW_of_callE h2))
  have hrun2' : (pure (x1.contains (decI n)) : AM Bool).run a = .ok (x2, a2) := hrun2
  obtain ⟨hx2e, hxa⟩ := pure_run_eq hrun2'
  rw [hxa] at hS2
  have hC2 := StageC.of_core hC1 (hS2.restrict vis)
    (callW_leafFrame hcl (leaf_mem _ (by decide)) (callW_of_callE h2)) (CoreStep.refl hC1.check)
  have hCr2 := hkp.call (im_mem _ rfl) (callW_of_callE h2) hCr1
  by_cases z2 : r2.headD 0 ≠ 0
  · rw [defnDivGateE.k_sl_contains.arm1 p _ _ _ _ _ _ z2] at hW
    have hx2 := decW0B_true hd2 z2
    have hx2' : x1.contains (decI n) = true := by rw [← hx2e]; exact hx2
    refine ErrClaim.ite_pos hx2' ?_
    cases h3 : callE p k "rom_pin_sets" [] m2 with
    | error e3 =>
      rw [h3, defnDivGateE.k_rom_pin_sets.none] at hW; cases hW
      exact nvlG hnv (by decide +kernel) h3
    | ok q3 =>
    obtain ⟨r3, m3⟩ := q3
    rw [h3, defnDivGateE.k_rom_pin_sets.arm1] at hW
    obtain ⟨hS3, hg3, hP3, hI3⟩ := romPinSets_ref hD hS2 hP2 (callW_of_callE h3)
    have hC3 := StageC.of_core hC2 (hS3.restrict vis)
      (callW_leafFrame hcl (leaf_mem _ (by decide)) (callW_of_callE h3)) (CoreStep.refl hC2.check)
    have hCr3 := hkp.call (im_mem _ rfl) (callW_of_callE h3) hCr2
    cases h4 : callE p k "check_div_mod_pin" [r3.headD 0, r3.tail.headD 0, vis, w, n] m3 with
    | ok q4 =>
      obtain ⟨r4, m4⟩ := q4
      rw [h4, defnDivGateE.k_check_div_mod_pin.arm1, defnDivGateE.j1.arm1] at hW; cases hW
    | error e4 =>
    rw [h4, defnDivGateE.k_check_div_mod_pin.none] at hW; cases hW
    by_cases hk4 : e.cls = 0
    · exact ErrClaim.of_cls0 hk4
    have hW4 := triple_of_callE_err (L.Ind.cpE_spec p hD.toDmProg9.lCheckDivModPin k
      ⟨m3, Locals.init []⟩ (r3.headD 0) (r3.tail.headD 0) vis w n) h4 (Err.code_ne_of_cls hk4)
    have hCpa := cpaClaimE_of (fe := fe2.restrictTo vis.toNat) hD.toDmProg9.toDmProg8 hq hcl hkp (hs0 dn vis _) (hsA dn vis _)
      henv hcE hnv
    exact L.Ind.cpCE hD.toDmProg9 hq hcl hkp hdn hnv
      (L.Ind.loopClaimE hD.toDmProg9 hq hcl hkp (hs0 dn vis _) (hsA dn vis _) henv hnv hCpa)
      hk' hS3 hC3 hok2 (by exact_mod_cast hn) hI3 hpd hnm hCr3 e hW4
  · rw [defnDivGateE.k_sl_contains.arm2 p _ _ _ _ _ _ (by simpa using z2), defnDivGateE.j1.arm1] at hW
    cases hW

end gate

end L.Arena
