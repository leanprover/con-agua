import ConAgua.Verdict.DeclGatesE

/-!
# The verdict claims of the `Nat.div`-family pin gate (lane `verdicts-b`, helper `d`)
-/

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind
open L.Rom (PinSetsR PinSetR)
open ConRon.Bridge (FoldOK PinsDenote PinSetDenote CheckOK StepOK CoreStep CoreSpec)

local notation "V" => ConLeche.CheckMode.verified

l_model checkDivModCerts_specE (p : Prog)
  (hf : p.lookup "check_div_mod_certs" = some checkDivModCertsL)
  fns [hf ↦ checkDivModCertsE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] errors

l_model checkTypePins_specE (p : Prog) (hf : p.lookup "check_type_pins" = some checkTypePinsL)
  fns [hf ↦ checkTypePinsE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] errors

l_model checkDivModPinValue_specE (p : Prog)
  (hf : p.lookup "check_div_mod_pin_value" = some checkDivModPinValueL)
  fns [hf ↦ checkDivModPinValueE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] errors

l_model checkDivModPinAt_specE (p : Prog)
  (hf : p.lookup "check_div_mod_pin_at" = some checkDivModPinAtL)
  fns [hf ↦ checkDivModPinAtE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] errors

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

section certs
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  {p : Prog}

/-- **`check_div_mod_certs`' error claim under `StageC`** (the error half of `cmC`), on the model,
by induction on the statements. -/
theorem cmE (hD : DmProg8 p) (hq : KnotStageProg p) (hcl : LeafClosed p) (hkp : CrKeep p)
    (hs0 : SubstC0 p dn vis fe) (hsA : SubstCAll p dn vis fe) (henv : ConLeche.EnvWF env)
    (hcE : CoreStubsE p) (hnv : closedNV p L.Checker.nvFns = true)
    (c annVal : Word) (hc : H c) (hann : H annVal) {nm : ConLeche.Name} {v : ConLeche.Expr}
    (hwsv : ConLeche.Expr.WScoped 0 v) :
    ∀ (ss : List (List EIdx × EIdx)) (xs : List (List ConLeche.Expr × ConLeche.Expr))
      (proofs : List EIdx) (ps : List ConLeche.Expr) (so sl po pl : Word) (k : Nat), k ≤ 2 ^ 62 →
      ∀ (m : Mem) (a : AState) (e : Err), StageC dn vis fe env m a →
      L.Stubs.CrOK m →
      StmtL m so.toNat sl.toNat ss → decHL m po.toNat pl.toNat = some proofs →
      po.toNat + pl.toNat ≤ iwTop m → denoteN a.store.ns (decI c) = some nm →
      denoteE a.store (decE annVal) = some v → ConRon.Bridge.StmtsDenote a.store ss xs →
      Frontend.denoteEList a.store proofs = some ps →
      (∀ q ∈ xs, (∀ h ∈ q.1, ConLeche.Expr.WScoped 2 h) ∧ ConLeche.Expr.WScoped 2 q.2) →
      checkDivModCertsE p k m vis c annVal so sl po pl = .error e →
      ErrClaim (checkDivModCerts V fe (decI c) (decE annVal) ss proofs) a e := by
  have hws4 : ConLeche.Expr.WScoped 4 v := ConLeche.Expr.WScoped.mono (by omega) hwsv
  have hws2 : ConLeche.Expr.WScoped 2 v := ConLeche.Expr.WScoped.mono (by omega) hwsv
  intro ss
  induction ss with
  | nil =>
    intro xs proofs ps so sl po pl k hk m a e hC _ hs hd hb hn hv hsd hpr hwq hw
    have hsl : sl = 0 := UInt64.toNat_inj.mp (by have := hs.2.1; simpa using this)
    cases k with
    | zero => rw [checkDivModCertsE.eq_1] at hw; cases hw; exact fun hk => absurd rfl hk
    | succ k =>
    cases proofs with
    | nil =>
      have hpl : pl = 0 := UInt64.toNat_inj.mp (by have := decHL_length m hd; simp at this ⊢; omega)
      rw [checkDivModCertsE.arm1 p k m vis c annVal so sl po pl ⟨hsl, hpl⟩] at hw; cases hw
    | cons pf pfs =>
      have hpl : pl ≠ 0 := fun e => by
        have := decHL_length m hd; rw [e] at this; simp at this
      rw [checkDivModCertsE.arm2 p k m vis c annVal so sl po pl (fun h => hpl h.2) (Or.inl hsl)] at hw
      cases hw
  | cons st ss ih =>
    rcases st with ⟨hy, eqq⟩
    intro xs proofs ps so sl po pl k hk m a e hC hCr hs hd hb hn hv hsd hpr hwq hw
    have hS := hC.stage
    cases xs with
    | nil => exact hsd.elim
    | cons xq xrest =>
    obtain ⟨hx, ex⟩ := xq
    obtain ⟨hsd1, hsd2, hsd3⟩ := hsd
    obtain ⟨hwh, hwe⟩ := hwq (hx, ex) (by simp)
    obtain ⟨hsl0, q, hq0, hstm, hrest⟩ := StmtL.cons hS.2 hs
    cases k with
    | zero => rw [checkDivModCertsE.eq_1] at hw; cases hw; exact fun hk => absurd rfl hk
    | succ k =>
    have hk' : k ≤ 2 ^ 62 := by omega
    cases proofs with
    | nil =>
      have hpl : pl = 0 := UInt64.toNat_inj.mp (by have := decHL_length m hd; simp at this ⊢; omega)
      rw [checkDivModCertsE.arm2 p k m vis c annVal so sl po pl (fun h => hsl0 h.1)
        (Or.inr hpl)] at hw; cases hw
    | cons pf pfs =>
    obtain ⟨px, pxs, hpx, hpxs, rfl⟩ := ConRon.Bridge.denoteEList_cons hpr
    obtain ⟨hpl0, hpwlt, hpf, hdrest⟩ := decHL_cons_iw hS.2.2.2.1 hd
    subst hpf
    obtain ⟨ho, hl, e0, hr3, hbd, hdh, he, hst2⟩ := hstm
    obtain ⟨hp3, h0, h1, h2⟩ := hr3
    have hst2' : eqq = decE e0 := hst2
    subst hst2'
    rw [checkDivModCertsE.arm3 p k m vis c annVal so sl po pl (fun h => hsl0 h.1)
      (by rintro (h | h); exact hsl0 h; exact hpl0 h)] at hw
    have hsz := hS.2.2.2.1
    have hI1 := hS.2.1
    have r0 : rdW (m.arr64 IW) so = q := hq0
    have rq1 : rdW (m.arr64 IW) q = ho := rdW_iw_of h0 rfl
    have rq2 : rdW (m.arr64 IW) (q + 1) = hl := rdW_iw_of h1 (word_add_one (by omega))
    have rq3 : rdW (m.arr64 IW) (q + 2) = e0 := rdW_iw_of h2 (word_add_two (by omega))
    have hlpos : 0 < pl.toNat :=
      Nat.pos_of_ne_zero (fun e' => hpl0 (UInt64.toNat_inj.mp (by simpa using e')))
    have hpo1 : (po + 1).toNat = po.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; omega
    have hpl1 : (pl - 1).toNat = pl.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
    have hpo : po.toNat < iwTop m := by omega
    have hq3 : q.toNat + 3 ≤ iwTop m := hp3
    have hq0' : q.toNat < iwTop m := by omega
    have hq1 : (q + 1).toNat < iwTop m := by rw [word_add_one (by omega)]; omega
    have hq2 : (q + 2).toNat < iwTop m := by rw [word_add_two (by omega)]; omega
    rw [r0, rq1, rq2, rq3] at hw
    simp only [checkDivModCerts]
    -- the guard
    cases h1' : callE p k "div_mod_cert_guard" [vis, c, annVal, ho, hl, e0, rdW (m.arr64 IW) po] m with
    | error e1 =>
      rw [h1', checkDivModCertsE.k_div_mod_cert_guard.none] at hw; cases hw
      exact ErrClaim.bind_left (nvlG hnv (by decide +kernel) h1')
    | ok q1 =>
    obtain ⟨r1, m1⟩ := q1
    rw [h1'] at hw
    obtain ⟨x1, a1, hrun1, hC1, c1, hg1, hd1, hxv1⟩ :=
      cgC hD.toDmProg7.toDmProg6.toDmProg5 hcl hkp hs0 hsA (callW_of_callE h1') hC hc hann he hpwlt
        hdh hbd hn hv hsd1 hsd2 hpx hCr
    have hCr1 := hkp.call (im_mem _ rfl) (callW_of_callE h1') hCr
    have hrun1' : (divModCertGuard fe (decI c) (decE annVal) hy (decE e0)
        (decI (rdW (m.arr64 IW) po))).run a = .ok (x1, a1) := hrun1
    refine ErrClaim.bind_right hrun1' ?_
    by_cases z1 : r1.headD 0 = 0
    · rw [checkDivModCertsE.k_div_mod_cert_guard.arm1 p _ _ _ _ _ _ _ _ _ _ _ z1] at hw; cases hw
    rw [checkDivModCertsE.k_div_mod_cert_guard.arm2 p _ _ _ _ _ _ _ _ _ _ _ z1] at hw
    have hx1 := decW0B_true hd1 z1
    rw [hx1]
    refine ErrClaim.ite_pos rfl ?_
    have hg' : ConLeche.divModCertGuard env nm v hx ex px = true := by rw [← hxv1, hx1]
    simp only [ConLeche.divModCertGuard, Bool.and_eq_true, Bool.not_eq_true'] at hg'
    have hPf : (ConLeche.Expr.substConstAll nm v px).hasFvar = false := hg'.1.1.1.1.2
    have hn1 := ConRon.Bridge.denoteN_ext hn c1.ext
    have hv1 := ConRon.Bridge.denote_ext hv c1.ext
    -- the substituted proof
    rw [iw_rd_grow hg1 hpo] at hw
    cases h2' : callE p k "subst_const_all" [c, annVal, 4000000000, rdW (m.arr64 IW) po] m1 with
    | error e2 =>
      rw [h2', checkDivModCertsE.k_subst_const_all.none] at hw; cases hw
      exact ErrClaim.bind_left (nvlG hnv (by decide +kernel) h2')
    | ok q2 =>
    obtain ⟨r2, m2⟩ := q2
    rw [h2', checkDivModCertsE.k_subst_const_all.arm1] at hw
    have hCr2 := hkp.call (im_mem _ rfl) (callW_of_callE h2') hCr1
    obtain ⟨x2, a2, hrun2, hS2, hg2, hl2, hx2⟩ := hsA c annVal _ hc hann hpwlt k m1 a1 r2 m2 hC1.stage
      (callW_of_callE h2')
    subst hx2
    obtain ⟨hi2, hpd⟩ := ConRon.Bridge.substConstAll_run coreWalkFuel hC1.check.state
      hC1.check.pins hn1 hv1 (ConRon.Bridge.denote_ext hpx c1.ext) hrun2
    have c2 := ConRon.Bridge.CoreStep.of_istep hC1.check hi2
    have hC2 := StageC.of_core hC1 hS2 (callW_leafFrame hcl (leaf_mem _ (by decide)) (callW_of_callE h2')) c2
    have c02 := c1.trans c2
    have hG2 : IWGrow m m2 := hg1.trans hg2
    refine ErrClaim.bind_right hrun2 ?_
    -- the substituted hypotheses
    rw [iw_rd_grow hG2 hq0', rq1, iw_rd_grow hG2 hq1, rq2] at hw
    cases h3' : callE p k "subst_const0_list" [c, annVal, ho, hl] m2 with
    | error e3 =>
      rw [h3', checkDivModCertsE.k_subst_const0_list.none] at hw; cases hw
      exact ErrClaim.bind_left (nvlG hnv (by decide +kernel) h3')
    | ok q3 =>
    obtain ⟨r3, m3⟩ := q3
    rw [h3', checkDivModCertsE.k_subst_const0_list.arm1] at hw
    have hdh2 : decHL m2 ho.toNat hl.toNat = some hy := by rw [decHL_grow hG2 hbd]; exact hdh
    have hCr3 := hkp.call (im_mem _ rfl) (callW_of_callE h3') hCr2
    obtain ⟨x3, a3, hrun3, hS3, hg3, hd3⟩ := sc0List_ref hD.toDmProg7.toDmProg6.toDmProg5 hs0 c
      annVal hc hann hy ho hl k m2 a2 r3 m3 hC2.stage hdh2 (Nat.le_trans hbd hG2.1) (callW_of_callE h3')
    simp only [decRL, Nat.zero_add, ntGetD0, ntGetD1] at hd3
    obtain ⟨hi3, hhs⟩ := ConRon.Bridge.substConst0List_run hy hx hC2.check.state hC2.check.pins
      (ConRon.Bridge.denoteN_ext hn c02.ext) (ConRon.Bridge.denote_ext hv c02.ext)
      (ConRon.Bridge.denoteEList_ext c02.ext _ _ hsd1) hrun3
    have c3 := ConRon.Bridge.CoreStep.of_istep hC2.check hi3
    have hC3 := StageC.of_core hC2 hS3 (callW_leafFrame hcl (leaf_mem _ (by decide)) (callW_of_callE h3')) c3
    have c03 := c02.trans c3
    have hG3 : IWGrow m m3 := hG2.trans hg3
    refine ErrClaim.bind_right hrun3 ?_
    -- the application
    cases h4' : callE p k "div_mod_cert_applied" [r2.headD 0, r3.headD 0, r3.tail.headD 0] m3 with
    | error e4 =>
      rw [h4', checkDivModCertsE.k_div_mod_cert_applied.none] at hw; cases hw
      exact ErrClaim.bind_left (nvlG hnv (by decide +kernel) h4')
    | ok q4 =>
    obtain ⟨r4, m4⟩ := q4
    rw [h4', checkDivModCertsE.k_div_mod_cert_applied.arm1] at hw
    obtain ⟨x4, a4, hrun4, hS4, hg4, hl4, rfl⟩ :=
      (applied_ref (dn := dn) (vis := vis) (fe := fe) hD.toDmProg7.toDmProg6.toDmProg5 (r2.headD 0)
        (r3.headD 0) (r3.tail.headD 0) x3) k m3 a3 r4 m4 ⟨hC3.stage, hl2, hd3.1, hd3.2⟩
        (callW_of_callE h4')
    have hCr4 := hkp.call (im_mem _ rfl) (callW_of_callE h4') hCr3
    obtain ⟨hi4, hap0⟩ := ConRon.Bridge.divModCertApplied_run hC3.check.state hC3.check.pins
      (ConRon.Bridge.denote_ext hpd hi3.ext) hhs hrun4
    have c4 := ConRon.Bridge.CoreStep.of_istep hC3.check hi4
    have hC4 := StageC.of_core hC3 hS4 (callW_leafFrame hcl (leaf_mem _ (by decide)) (callW_of_callE h4')) c4
    have c04 := c03.trans c4
    have hG4 : IWGrow m m4 := hG3.trans hg4
    have hwsA : ConLeche.Expr.WScoped 4 (ConLeche.divModCertApplied
        (ConLeche.Expr.substConstAll nm v px) (hx.map (ConLeche.Expr.substConst0 nm v))) := by
      refine ConRon.Bridge.divModCertApplied_wscoped hPf fun h hh => ?_
      obtain ⟨h0, hh0, rfl⟩ := List.mem_map.mp hh
      exact ConRon.Bridge.substConst0_wscoped hws2 _ (hwh h0 hh0)
    have hrun4' : (divModCertApplied (decI (r2.headD 0)) x3).run a3 =
        .ok (decI (r4.headD 0), a4) := hrun4
    refine ErrClaim.bind_right hrun4' ?_
    -- the type
    cases h5 : callE p k "infer_type_core" [vis, 4, r4.headD 0] m4 with
    | error e5 =>
      rw [h5, checkDivModCertsE.k_infer_type_core.none] at hw; cases hw
      have := hcE.inferTypeCore k hk' hC4.stageT 4 (r4.headD 0) hl4 _ h5
      exact ErrClaim.bind_left this
    | ok q5 =>
    obtain ⟨r5, m5⟩ := q5
    rw [h5, checkDivModCertsE.k_infer_type_core.arm1] at hw
    have hCr5 := hkp.call (im_mem _ rfl) (callW_of_callE h5) hCr4
    obtain ⟨x5, a5, hrun5, hT5, hg5, hl5, hx5⟩ :=
      hq.inferTypeCore_sim k hk' hC4.stageT 4 (r4.headD 0) hl4 r5 m5 (callW_of_callE h5)
    subst hx5
    have h4w : (4 : Word).toNat = 4 := rfl
    rw [h4w] at hrun5
    obtain ⟨hck5, hx5', hp5, tpx, htp5, hwstp, -⟩ := infer_check henv hC4.check hap0 hwsA hrun5
    have c5 : CoreStep V env fe a4 a5 := ⟨hck5, hx5', hp5⟩
    have hC5 := StageC.of_T hT5 hck5
    have c05 := c04.trans c5
    have hG5 : IWGrow m m5 := hG4.trans hg5
    refine ErrClaim.bind_right hrun5 ?_
    -- the equation, substituted
    rw [iw_rd_grow hG5 hq2, rq3] at hw
    cases h6 : callE p k "subst_const0" [c, annVal, 4000000000, e0] m5 with
    | error e6 =>
      rw [h6, checkDivModCertsE.k_subst_const0.none] at hw; cases hw
      exact ErrClaim.bind_left (nvlG hnv (by decide +kernel) h6)
    | ok q6 =>
    obtain ⟨r6, m6⟩ := q6
    rw [h6, checkDivModCertsE.k_subst_const0.arm1] at hw
    have hCr6 := hkp.call (im_mem _ rfl) (callW_of_callE h6) hCr5
    obtain ⟨x6, a6, hrun6, hS6, hg6, hl6, hx6⟩ :=
      hs0 c annVal e0 hc hann he k m5 a5 r6 m6 hC5.stage (callW_of_callE h6)
    subst hx6
    obtain ⟨hi6, hrhs⟩ := ConRon.Bridge.substConst0_run coreWalkFuel hC5.check.state hC5.check.pins
      (ConRon.Bridge.denoteN_ext hn c05.ext) (ConRon.Bridge.denote_ext hv c05.ext)
      (ConRon.Bridge.denote_ext hsd2 c05.ext) hrun6
    have c6 := ConRon.Bridge.CoreStep.of_istep hC5.check hi6
    have hC6 := StageC.of_core hC5 hS6 (callW_leafFrame hcl (leaf_mem _ (by decide)) (callW_of_callE h6)) c6
    have hG6 : IWGrow m m6 := hG5.trans hg6
    have hwsR : ConLeche.Expr.WScoped 4 (ConLeche.Expr.substConst0 nm v ex) :=
      ConRon.Bridge.substConst0_wscoped hws4 _ (ConLeche.Expr.WScoped.mono (by omega) hwe)
    have hrun6' : (substConst0 (decI c) (decE annVal) coreWalkFuel (decE e0)).run a5 =
        .ok (decI (r6.headD 0), a6) := hrun6
    refine ErrClaim.bind_right hrun6' ?_
    -- the comparison
    cases h7 : callE p k "is_def_eq_core" [vis, 4, r5.headD 0, r6.headD 0] m6 with
    | error e7 =>
      rw [h7, checkDivModCertsE.k_is_def_eq_core.none] at hw; cases hw
      have := hcE.isDefEqCore k hk' hC6.stageT 4 (r5.headD 0) (r6.headD 0) hl5 hl6 _ h7
      exact ErrClaim.bind_left this
    | ok q7 =>
    obtain ⟨r7, m7⟩ := q7
    rw [h7] at hw
    have hCr7 := hkp.call (im_mem _ rfl) (callW_of_callE h7) hCr6
    obtain ⟨x7, a7, hrun7, hT7, hg7, hd7⟩ :=
      hq.isDefEqCore_sim k hk' hC6.stageT 4 (r5.headD 0) (r6.headD 0) hl5 hl6 r7 m7
        (callW_of_callE h7)
    rw [h4w] at hrun7
    obtain ⟨hck7, hx7', hp7, -⟩ := defeq_check henv hC6.check
      (ConRon.Bridge.denote_ext htp5 hi6.ext) hrhs hwstp hwsR hrun7
    have c7 : CoreStep V env fe a6 a7 := ⟨hck7, hx7', hp7⟩
    have hC7 := StageC.of_T hT7 hck7
    have c07 := (c05.trans c6).trans c7
    have hG7 : IWGrow m m7 := hG6.trans hg7
    refine ErrClaim.bind_right hrun7 ?_
    by_cases z7 : r7.headD 0 = 0
    · rw [checkDivModCertsE.k_is_def_eq_core.arm1 p _ _ _ _ _ _ _ _ _ _ z7] at hw; cases hw
    rw [checkDivModCertsE.k_is_def_eq_core.arm2 p _ _ _ _ _ _ _ _ _ _ z7] at hw
    have hx7 : x7 = true := by rw [← hd7]; simpa [decBool] using z7
    rw [hx7]
    refine ErrClaim.ite_pos rfl ?_
    have hdr1 : decHL m7 (po + 1).toNat (pl - 1).toNat = some pfs := by
      rw [decHL_grow hG7 (by rw [hpo1, hpl1]; omega)]; exact hdrest
    exact ih xrest pfs pxs (so + 1) (sl - 1) (po + 1) (pl - 1) k (by omega) m7 a7 e hC7 hCr7
      (hrest.grow hG7) hdr1 (by rw [hpo1, hpl1]; have := hG7.1; omega)
      (ConRon.Bridge.denoteN_ext hn c07.ext) (ConRon.Bridge.denote_ext hv c07.ext)
      (ConRon.Bridge.StmtsDenote.mono c07.ext _ _ hsd3)
      (ConRon.Bridge.denoteEList_ext c07.ext _ _ hpxs)
      (fun q hq => hwq q (List.mem_cons_of_mem _ hq)) hw

end certs

section typePins
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  {p : Prog}

/-- **`check_type_pins`' error claim under `StageC`** (the error half of `ctpC`), on the model, by
induction on the pairs. -/
theorem ctpE (hD : DmProg8 p) (hq : KnotStageProg p) (hcl : LeafClosed p) (hkp : CrKeep p)
    (henv : ConLeche.EnvWF env) (hcE : CoreStubsE p) (hnv : closedNV p L.Checker.nvFns = true) :
    ∀ (tps : List (NIdx × EIdx)) (tpsP : List (ConLeche.Name × ConLeche.Expr)) (o l : Word)
      (k : Nat), k ≤ 2 ^ 62 → ∀ (m : Mem) (a : AState) (e : Err),
      StageC dn vis fe env m a → L.Stubs.CrOK m → L.Rom.TPinsR m o l tps →
      ConRon.Bridge.TypePinsDenote a.store tps tpsP →
      (∀ q ∈ tpsP, (ConLeche.typePinStored env q.1).hasFvar = false ∧ q.2.hasFvar = false) →
      checkTypePinsE p k m vis o l = .error e →
      ErrClaim (checkTypePins V fe tps) a e := by
  intro tps
  induction tps with
  | nil =>
    intro tpsP o l k _ m a e hC _ ht hd _ hw
    have hl : l = 0 := UInt64.toNat_inj.mp (by have := ht.2.1; simpa using this)
    cases k with
    | zero => rw [checkTypePinsE.eq_1] at hw; cases hw; exact fun hk => absurd rfl hk
    | succ k => rw [checkTypePinsE.arm1 p k m vis o l hl] at hw; cases hw
  | cons tp tps ih =>
    intro tpsP o l k hk m a e hC hCr ht hd hcl' hw
    cases tpsP with
    | nil => exact hd.elim
    | cons q qs =>
    obtain ⟨hd1, hd2, hd3⟩ := hd
    cases k with
    | zero => rw [checkTypePinsE.eq_1] at hw; cases hw; exact fun hk => absurd rfl hk
    | succ k =>
    have hk' : k ≤ 2 ^ 62 := by omega
    obtain ⟨hb, hlen, hv⟩ := ht
    have hl0 : l ≠ 0 := fun e => by rw [e] at hlen; simp at hlen
    rw [checkTypePinsE.arm2 p k m vis o l hl0] at hw
    obtain ⟨v0, v1⟩ := hv 0 (by simp)
    simp only [List.getElem_cons_zero, show (2 : Word) * UInt64.ofNat 0 = 0 from rfl,
      UInt64.add_zero] at v0 v1
    rw [v0] at hw
    have htl := L.Rom.top_lt m
    have hD6 := hD.toDmProg7.toDmProg6
    simp only [checkTypePins]
    -- the stored type
    cases h1 : callE p k "type_pin_stored" [vis, tp.1.word.toUInt64] m with
    | error e1 =>
      rw [h1, checkTypePinsE.k_type_pin_stored.none] at hw; cases hw
      exact ErrClaim.bind_left (nvlG hnv (by decide +kernel) h1)
    | ok q1 =>
    obtain ⟨r1, m1⟩ := q1
    rw [h1, checkTypePinsE.k_type_pin_stored.arm1] at hw
    obtain ⟨x1, a1, hrun1, hS1, hg1, hl1, hx1⟩ :=
      (tps_ref hD6 tp.1.word.toUInt64) k m a r1 m1 ⟨hC.stage, dmWord_lt32 _⟩ (callW_of_callE h1)
    have hCr1 := hkp.call (im_mem _ rfl) (callW_of_callE h1) hCr
    rw [decI_word] at hrun1
    obtain ⟨hck1, hxt1, hp1, hden1⟩ := ConRon.Bridge.AM.of_run (P := fun t => t = a) rfl hrun1
      (ConRon.Bridge.typePinStored_spec a tp.1 q.1 hC.check hd1)
    have c1 : CoreStep V env fe a a1 := ⟨hck1, hxt1, hp1⟩
    have hC1 := StageC.of_core hC hS1 (callW_leafFrame hcl (leaf_mem _ (by decide)) (callW_of_callE h1)) c1
    rw [← hx1] at hden1 hrun1
    have hrd : rdW (m1.arr64 EREC) (o + 1) = tp.2.word.toUInt64 := by
      rw [rdW_erec_grow hg1 (by
        have hlen1 : l.toNat = tps.length + 1 := by simpa using hlen
        obtain ⟨_, h1⟩ := L.Rom.pairIdx (o := o) (i := 0) (by omega)
        simp only [show (2 : Word) * UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero] at h1
        rw [h1]; omega)]
      exact v1
    rw [hrd] at hw
    refine ErrClaim.bind_right hrun1 ?_
    -- the comparison
    cases h2 : callE p k "is_def_eq_core" [vis, 0, r1.headD 0, tp.2.word.toUInt64] m1 with
    | error e2 =>
      rw [h2, checkTypePinsE.k_is_def_eq_core.none] at hw; cases hw
      have := hcE.isDefEqCore k hk' hC1.stageT 0 (r1.headD 0) tp.2.word.toUInt64 hl1
        (dmWord_lt32 _) _ h2
      rw [decI_word] at this
      exact ErrClaim.bind_left this
    | ok q2 =>
    obtain ⟨r2, m2⟩ := q2
    rw [h2] at hw
    have hCr2 := hkp.call (im_mem _ rfl) (callW_of_callE h2) hCr1
    obtain ⟨x2, a2, hrun2, hT2, hg2, hd2'⟩ :=
      hq.isDefEqCore_sim k hk' hC1.stageT 0 (r1.headD 0) tp.2.word.toUInt64 hl1 (dmWord_lt32 _)
        r2 m2 (callW_of_callE h2)
    have h0w : (0 : Word).toNat = 0 := rfl
    rw [h0w] at hrun2
    have hq1 := hcl' q (by simp)
    obtain ⟨hck2, hx2', hp2, -⟩ := defeq_check henv hC1.check hden1
      (by rw [decI_word]; exact ConRon.Bridge.denote_ext hd2 c1.ext)
      (ConLeche.Expr.WScoped.of_not_hasFvar hq1.1) (ConLeche.Expr.WScoped.of_not_hasFvar hq1.2) hrun2
    have c2 : CoreStep V env fe a1 a2 := ⟨hck2, hx2', hp2⟩
    have hC2 := StageC.of_T hT2 hck2
    have hrun2' : (isDefEqCore V fe checkFuel 0 (decI (r1.headD 0)) tp.2).run a1 = .ok (x2, a2) := by
      rw [← decI_word tp.2]; exact hrun2
    refine ErrClaim.bind_right hrun2' ?_
    by_cases z2 : r2.headD 0 = 0
    · rw [checkTypePinsE.k_is_def_eq_core.arm1 p _ _ _ _ _ _ z2] at hw; cases hw
    rw [checkTypePinsE.k_is_def_eq_core.arm2 p _ _ _ _ _ _ z2] at hw
    have hx2 : x2 = true := by rw [← hd2']; simpa [decBool] using z2
    rw [hx2]
    refine ErrClaim.ite_pos rfl ?_
    have hG2 : IWGrow m m2 := hg1.trans hg2
    have hlen' : l.toNat = tps.length + 1 := by simpa using hlen
    have hrest : L.Rom.TPinsR m2 (o + 2) (l - 1) tps := by
      have hl1' : (l - 1).toNat = l.toNat - 1 := by
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
      have ho2 : (o + 2).toNat = o.toNat + 2 := L.Rom.addN (by simp; omega)
      refine L.Rom.TPinsR.keep ⟨by rw [ho2, hl1']; omega, by rw [hl1']; omega,
        fun i hi => ?_⟩ ⟨hG2.2.1, hG2.2.2.2⟩
      have := hv (i + 1) (by simpa using hi)
      simp only [List.getElem_cons_succ] at this
      have e : o + 2 * UInt64.ofNat (i + 1) = o + 2 + 2 * UInt64.ofNat i := by
        rw [UInt64.ofNat_add, UInt64.ofNat_one, UInt64.mul_add, UInt64.mul_one]; ac_rfl
      rw [e] at this
      exact this
    exact ih qs (o + 2) (l - 1) k hk' m2 a2 e hC2 hCr2 hrest
      (ConRon.Bridge.TypePinsDenote.mono (c1.trans c2).ext _ _ hd3)
      (fun r hr => hcl' r (by simp [hr])) hw

end typePins

section pinValue
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  {p : Prog}

/-- **`check_div_mod_pin_value`' error claim under `StageC`** (the error half of `cpvC`). -/
theorem cpvE (hD : DmProg8 p) (hq : KnotStageProg p) (hcl : LeafClosed p) (hkp : CrKeep p)
    (hs0 : SubstC0 p dn vis fe) (hsA : SubstCAll p dn vis fe) (henv : ConLeche.EnvWF env)
    (hcE : CoreStubsE p) (hnv : closedNV p L.Checker.nvFns = true)
    {c value ps : Word} {ip : INatOpPinSet} {psP : ConLeche.NatOpPinSet} {nm : ConLeche.Name}
    {v : ConLeche.Expr} {k : Nat} (hk : k ≤ 2 ^ 62) {m : Mem} {a : AState} {e : Err}
    (hcall : callE p k "check_div_mod_pin_value" [vis, c, value, ps] m = .error e)
    (hC : StageC dn vis fe env m a) (hc : H c) (hval : H value) (hP : PinSetR m ps ip)
    (hps : PinSetDenote a.store ip psP) (hn : denoteN a.store.ns (decI c) = some nm)
    (hv : denoteE a.store (decE value) = some v) (hwsv : ConLeche.Expr.WScoped 0 v)
    (hpg : ConLeche.divModPinGuard psP env nm = true) (hCr : L.Stubs.CrOK m) :
    ErrClaim (checkDivModPinValue V fe (decI c) (decE value) ip) a e := by
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (checkDivModPinValue_specE p hD.lCheckDivModPinValue k
    ⟨m, Locals.init []⟩ vis c value ps) hcall (Err.code_ne_of_cls hk0)
  cases k with
  | zero => rw [checkDivModPinValueE.eq_1] at hW; cases hW; exact absurd rfl hk0
  | succ k =>
  have hk' : k ≤ 2 ^ 62 := by omega
  rw [checkDivModPinValueE.arm1] at hW
  have h0w : (0 : Word).toNat = 0 := rfl
  have hD5 := hD.toDmProg7.toDmProg6.toDmProg5
  have hwsP : ConLeche.Expr.WScoped 0 (ConLeche.divModDeclPin psP nm) := by
    simp only [ConLeche.divModPinGuard, Bool.and_eq_true, Bool.not_eq_true'] at hpg
    exact ConLeche.Expr.WScoped.of_not_hasFvar hpg.1.1.1.2
  simp only [checkDivModPinValue]
  -- the pin
  cases h1 : callE p k "div_mod_decl_pin" [ps, c] m with
  | error e1 =>
    rw [h1, checkDivModPinValueE.k_div_mod_decl_pin.none] at hW; cases hW
    exact ErrClaim.bind_left (nvlG hnv (by decide +kernel) h1)
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, checkDivModPinValueE.k_div_mod_decl_pin.arm1] at hW
  obtain ⟨x1, a1, hrun1, hS1, hg1, hl1, hx1⟩ :=
    (divModDeclPin_ref hD5.toDmProg2.toDmProg1 ps c ip) k m a r1 m1 ⟨hC.stage, hc, hP⟩
      (callW_of_callE h1)
  have hCr1 := hkp.call (im_mem _ rfl) (callW_of_callE h1) hCr
  obtain ⟨e1, hpd⟩ := ConRon.Bridge.divModDeclPin_run hC.check.state hC.check.pins hps hn hrun1
  rw [e1] at hrun1 hS1
  have hC1 := StageC.of_core hC hS1 (callW_leafFrame hcl (leaf_mem _ (by decide)) (callW_of_callE h1))
    (CoreStep.refl hC.check)
  rw [← hx1] at hpd
  have hrun1' : (divModDeclPin ip (decI c)).run a = .ok (decI (r1.headD 0), a) := by
    rw [hx1]; exact hrun1
  refine ErrClaim.bind_right hrun1' ?_
  -- the value against the pin
  cases h2 : callE p k "is_def_eq_core" [vis, 0, value, r1.headD 0] m1 with
  | error e2 =>
    rw [h2, checkDivModPinValueE.k_is_def_eq_core.none] at hW; cases hW
    have := hcE.isDefEqCore k hk' hC1.stageT 0 value (r1.headD 0) hval hl1 _ h2
    exact ErrClaim.bind_left this
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2] at hW
  have hCr2 := hkp.call (im_mem _ rfl) (callW_of_callE h2) hCr1
  obtain ⟨x2, a2, hrun2, hT2, hg2, hd2⟩ :=
    hq.isDefEqCore_sim k hk' hC1.stageT 0 value (r1.headD 0) hval hl1 r2 m2 (callW_of_callE h2)
  rw [h0w] at hrun2
  obtain ⟨hck2, hx2', hp2, -⟩ := defeq_check henv hC1.check hv hpd hwsv hwsP hrun2
  have c2 : CoreStep V env fe a a2 := ⟨hck2, hx2', hp2⟩
  have hC2 := StageC.of_T hT2 hck2
  have hrun2' : (isDefEqCore V fe checkFuel 0 (decE value) (decI (r1.headD 0))).run a =
      .ok (x2, a2) := hrun2
  refine ErrClaim.bind_right hrun2' ?_
  by_cases z2 : r2.headD 0 = 0
  · rw [checkDivModPinValueE.k_is_def_eq_core.arm1 p _ _ _ _ _ _ _ z2] at hW; cases hW
  rw [checkDivModPinValueE.k_is_def_eq_core.arm2 p _ _ _ _ _ _ _ z2] at hW
  have hx2 : x2 = true := by rw [← hd2]; simpa [decBool] using z2
  rw [hx2]
  refine ErrClaim.ite_pos rfl ?_
  -- the statements and the proofs
  cases h3 : callE p k "div_mod_cert_stmts" [c] m2 with
  | error e3 =>
    rw [h3, checkDivModPinValueE.k_div_mod_cert_stmts.none] at hW; cases hW
    exact ErrClaim.bind_left (nvlG hnv (by decide +kernel) h3)
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, checkDivModPinValueE.k_div_mod_cert_stmts.arm1] at hW
  obtain ⟨x3, a3, hrun3, hS3, hg3, hd3⟩ :=
    (divModCertStmts_ref hD5.toDmProg2 c) k m2 a2 r3 m3 ⟨hC2.stage, hc⟩ (callW_of_callE h3)
  have hCr3 := hkp.call (im_mem _ rfl) (callW_of_callE h3) hCr2
  have hn2 := ConRon.Bridge.denoteN_ext hn c2.ext
  obtain ⟨hi3, hsd⟩ := ConRon.Bridge.divModCertStmts_run hC2.check.state hC2.check.pins hn2 hrun3
  have c3 := ConRon.Bridge.CoreStep.of_istep hC2.check hi3
  have hC3 := StageC.of_core hC2 hS3 (callW_leafFrame hcl (leaf_mem _ (by decide)) (callW_of_callE h3)) c3
  have c03 := c2.trans c3
  refine ErrClaim.bind_right hrun3 ?_
  cases h4 : callE p k "div_mod_cert_proofs" [ps, c] m3 with
  | error e4 =>
    rw [h4, checkDivModPinValueE.k_div_mod_cert_proofs.none] at hW; cases hW
    exact ErrClaim.bind_left (nvlG hnv (by decide +kernel) h4)
  | ok q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [h4, checkDivModPinValueE.k_div_mod_cert_proofs.arm1] at hW
  obtain ⟨x4, a4, hrun4, hS4, hg4, hd4⟩ :=
    (divModCertProofs_ref hD5.toDmProg2.toDmProg1 ps c ip) k m3 a3 r4 m4
      ⟨hS3, hc, L.Ind.PinSetR.grow (L.Ind.PinSetR.grow hP hg1) (hg2.trans hg3)⟩ (callW_of_callE h4)
  have hCr4 := hkp.call (im_mem _ rfl) (callW_of_callE h4) hCr3
  have hps3 := (ConRon.Bridge.PinsDenote.mono c03.ext [ip] [psP] ⟨hps, trivial⟩).1
  have hn3 := ConRon.Bridge.denoteN_ext hn c03.ext
  obtain ⟨e4, hpr⟩ := ConRon.Bridge.divModCertProofs_run hC3.check.state hC3.check.pins hps3 hn3
    hrun4
  rw [e4] at hrun4 hS4
  have hC4 := StageC.of_core hC3 hS4 (callW_leafFrame hcl (leaf_mem _ (by decide)) (callW_of_callE h4))
    (CoreStep.refl hC3.check)
  refine ErrClaim.bind_right hrun4 ?_
  -- the certificates
  cases h5 : callE p k "check_div_mod_certs" [vis, c, value, r3.headD 0, r3.tail.headD 0,
      r4.headD 0, r4.tail.headD 0] m4 with
  | error e5 =>
    rw [h5, checkDivModPinValueE.k_check_div_mod_certs.none] at hW; cases hW
    by_cases hk5 : e.cls = 0
    · exact ErrClaim.of_cls0 hk5
    have hW5 := triple_of_callE_err (checkDivModCerts_specE p hD.lCheckDivModCerts k
      ⟨m4, Locals.init []⟩ vis c value (r3.headD 0) (r3.tail.headD 0) (r4.headD 0)
      (r4.tail.headD 0)) h5 (Err.code_ne_of_cls hk5)
    simp only [decStmtL, ntGetD0, ntGetD1] at hd3
    unfold decRL at hd4
    simp only [Nat.zero_add, ntGetD0, ntGetD1] at hd4
    exact cmE hD hq hcl hkp hs0 hsA henv hcE hnv c value hc hval hwsv x3 _ x4 _ (r3.headD 0)
      (r3.tail.headD 0) (r4.headD 0) (r4.tail.headD 0) k hk' m4 a3 e hC4 hCr4 (hd3.grow hg4) hd4.1
      hd4.2 hn3 (ConRon.Bridge.denote_ext hv c03.ext) hsd hpr
      (ConRon.Bridge.divModCertStmts_wscoped nm) hW5
  | ok q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [h5, checkDivModPinValueE.k_check_div_mod_certs.arm1] at hW; cases hW

end pinValue

section pinAt
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
  {p : Prog}

/-- **`check_div_mod_pin_at`'s error claim under `StageC`** (the error half of `cpaC`). -/
theorem cpaE (hD : DmProg8 p) (hq : KnotStageProg p) (hcl : LeafClosed p) (hkp : CrKeep p)
    (hs0 : SubstC0 p dn vis fe) (hsA : SubstCAll p dn vis fe) (henv : ConLeche.EnvWF env)
    (hcE : CoreStubsE p) (hnv : closedNV p L.Checker.nvFns = true)
    {c value ps : Word} {ip : INatOpPinSet} {psP : ConLeche.NatOpPinSet} {nm : ConLeche.Name}
    {v : ConLeche.Expr} {k : Nat} (hk : k ≤ 2 ^ 62) {m : Mem} {a : AState} {e : Err}
    (hcall : callE p k "check_div_mod_pin_at" [vis, c, value, ps] m = .error e)
    (hC : StageC dn vis fe env m a) (hc : H c) (hval : H value) (hP : PinSetR m ps ip)
    (hps : PinSetDenote a.store ip psP) (hn : denoteN a.store.ns (decI c) = some nm)
    (hv : denoteE a.store (decE value) = some v) (hwsv : ConLeche.Expr.WScoped 0 v)
    (hpg : ConLeche.divModPinGuard psP env nm = true) (hCr : L.Stubs.CrOK m) :
    ErrClaim (checkDivModPinAt V fe (decI c) (decE value) ip) a e := by
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (checkDivModPinAt_specE p hD.lCheckDivModPinAt k
    ⟨m, Locals.init []⟩ vis c value ps) hcall (Err.code_ne_of_cls hk0)
  cases k with
  | zero => rw [checkDivModPinAtE.eq_1] at hW; cases hW; exact absurd rfl hk0
  | succ k =>
  have hk' : k ≤ 2 ^ 62 := by omega
  rw [checkDivModPinAtE.arm1] at hW
  have hD1 := hD.toDmProg7.toDmProg6.toDmProg5.toDmProg2.toDmProg1
  simp only [checkDivModPinAt]
  -- the type pins
  cases h1 : callE p k "div_mod_type_pins" [ps, c] m with
  | error e1 =>
    rw [h1, checkDivModPinAtE.k_div_mod_type_pins.none] at hW; cases hW
    exact ErrClaim.bind_left (nvlG hnv (by decide +kernel) h1)
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, checkDivModPinAtE.k_div_mod_type_pins.arm1] at hW
  obtain ⟨x1, a1, hrun1, hS1, hg1, hd1⟩ :=
    (divModTypePins_ref hD1 ps c ip) k m a r1 m1 ⟨hC.stage, hc, hP⟩ (callW_of_callE h1)
  have hCr1 := hkp.call (im_mem _ rfl) (callW_of_callE h1) hCr
  obtain ⟨e1, htd⟩ := ConRon.Bridge.divModTypePins_run hC.check.state hC.check.pins hps hn hrun1
  rw [e1] at hrun1 hS1
  have hC1 := StageC.of_core hC hS1 (callW_leafFrame hcl (leaf_mem _ (by decide)) (callW_of_callE h1))
    (CoreStep.refl hC.check)
  refine ErrClaim.bind_right hrun1 ?_
  cases h2 : callE p k "check_type_pins" [vis, r1.headD 0, r1.tail.headD 0] m1 with
  | error e2 =>
    rw [h2, checkDivModPinAtE.k_check_type_pins.none] at hW; cases hW
    by_cases hk2 : e.cls = 0
    · exact ErrClaim.of_cls0 hk2
    have hW2 := triple_of_callE_err (checkTypePins_specE p hD.lCheckTypePins k ⟨m1, Locals.init []⟩
      vis (r1.headD 0) (r1.tail.headD 0)) h2 (Err.code_ne_of_cls hk2)
    exact ErrClaim.bind_left (ctpE hD hq hcl hkp henv hcE hnv x1 _ _ _ k hk' m1 a e hC1 hCr1 hd1 htd
      (ConRon.Bridge.divModTypePins_closed hpg) hW2)
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2] at hW
  obtain ⟨x2, a2, hrun2, hC2, c2, hg2, hd2⟩ := ctpC hD hq hcl hkp henv x1 _ _ _ k hk' m1 a r2 m2 hC1
    hCr1 hd1 htd (ConRon.Bridge.divModTypePins_closed hpg) (callW_of_callE h2)
  have hCr2 := hkp.call (im_mem _ rfl) (callW_of_callE h2) hCr1
  refine ErrClaim.bind_right hrun2 ?_
  by_cases z2 : r2.headD 0 = 0
  · rw [checkDivModPinAtE.k_check_type_pins.arm1 p _ _ _ _ _ _ _ z2] at hW; cases hW
  rw [checkDivModPinAtE.k_check_type_pins.arm2 p _ _ _ _ _ _ _ z2] at hW
  have hx2 := decW0B_true hd2 z2
  rw [hx2]
  refine ErrClaim.ite_pos rfl ?_
  cases h3 : callE p k "check_div_mod_pin_value" [vis, c, value, ps] m2 with
  | error e3 =>
    rw [h3, checkDivModPinAtE.k_check_div_mod_pin_value.none] at hW; cases hW
    exact cpvE hD hq hcl hkp hs0 hsA henv hcE hnv hk' h3 hC2 hc hval
      (L.Ind.PinSetR.grow hP (hg1.trans hg2))
      (ConRon.Bridge.PinsDenote.mono c2.ext [ip] [psP] ⟨hps, trivial⟩).1
      (ConRon.Bridge.denoteN_ext hn c2.ext) (ConRon.Bridge.denote_ext hv c2.ext) hwsv hpg hCr2
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, checkDivModPinAtE.k_check_div_mod_pin_value.arm1] at hW; cases hW

end pinAt

end L.Arena
