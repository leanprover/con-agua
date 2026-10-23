import ConAgua.Arena.DeclDivMod7

/-!
# The `Nat.div` family's pin gate, bottom up: the certificates (lane `decls3`, `decls3-divmod`)

Part 8: `check_div_mod_certs`. The inference and the definitional equality are the stubs'
(`inferTypeCore_spec`, `isDefEqCore_spec`).
-/

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open L.Rom (PinSetR)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

structure DmProg8 (p : Prog) : Prop extends DmProg7 p where
  lCheckDivModCerts : p.lookup "check_div_mod_certs" = some checkDivModCertsL
  lCheckDivModPinAt : p.lookup "check_div_mod_pin_at" = some checkDivModPinAtL
  lCheckDivModPinLoop : p.lookup "check_div_mod_pin_loop" = some checkDivModPinLoopL
  lCheckDivModPin : p.lookup "check_div_mod_pin" = some checkDivModPinL

section certs
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

def cmW (p : Prog) (cl : CallM) (n : Nat) (m : Mem) (vs c annVal so sl po pl : Word) : Option (List Word × Mem) :=
  if sl = 0 ∧ pl = 0 then some ([1], m) else
  if sl = 0 ∨ pl = 0 then some ([0], m) else
  ntBW (callW p n "div_mod_cert_guard" [vs, c, annVal, rdW (m.arr64 IW) (rdW (m.arr64 IW) so),
    rdW (m.arr64 IW) (rdW (m.arr64 IW) so + 1), rdW (m.arr64 IW) (rdW (m.arr64 IW) so + 2),
    rdW (m.arr64 IW) po] m) fun r1 m1 =>
  if r1.headD 0 = 0 then some ([0], m1) else
  ntBW (callW p n "subst_const_all" [c, annVal, 4000000000, rdW (m1.arr64 IW) po] m1) fun r2 m2 =>
  ntBW (callW p n "subst_const0_list" [c, annVal, rdW (m2.arr64 IW) (rdW (m.arr64 IW) so),
    rdW (m2.arr64 IW) (rdW (m.arr64 IW) so + 1)] m2) fun r3 m3 =>
  ntBW (callW p n "div_mod_cert_applied" [r2.headD 0, r3.headD 0, r3.tail.headD 0] m3) fun r4 m4 =>
  ntBW (cl n "infer_type_core" [vs, 4, r4.headD 0] m4) fun r5 m5 =>
  ntBW (callW p n "subst_const0" [c, annVal, 4000000000,
    rdW (m5.arr64 IW) (rdW (m.arr64 IW) so + 2)] m5) fun r6 m6 =>
  ntBW (cl n "is_def_eq_core" [vs, 4, r5.headD 0, r6.headD 0] m6) fun r7 m7 =>
  if r7.headD 0 = 0 then some ([0], m7) else
  ntBW (callW p n "check_div_mod_certs" [vs, c, annVal, so + 1, sl - 1, po + 1, pl - 1] m7) fun r8 m8 =>
    some ([r8.headD 0], m8)

set_option maxHeartbeats 3200000 in
theorem cm_specW (p : Prog) (hp : p.lookup "check_div_mod_certs" = some checkDivModCertsL)
    (cl : CallM) (hc : CallSpec p cl) (n : Nat) (s₀ : St) (vs c annVal so sl po pl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check_div_mod_certs" [vs, c, annVal, so, sl, po, pl]
    ⦃fun r s' => LocEq s' s₀ ∧ cmW p cl n s₀.mem vs c annVal so sl po pl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkDivModCertsL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "div_mod_cert_guard", callW_spec p n "subst_const_all",
      callW_spec p n "subst_const0_list", callW_spec p n "div_mod_cert_applied",
      hc n "infer_type_core", callW_spec p n "subst_const0",
      hc n "is_def_eq_core", callW_spec p n "check_div_mod_certs"] <;>
    finish (gen := 30) (instances := 10000) [cmW, ntBW, rdW_eq]

theorem cm_ref (hD : DmProg8 p) (hs0 : SubstC0 p dn vis fe) (hsA : SubstCAll p dn vis fe)
    (c annVal : Word) (hc : H c) (hann : H annVal) :
    ∀ (ss : List (List EIdx × EIdx)) (proofs : List EIdx) (so sl po pl : Word) (k : Nat) (m : Mem)
      (a : AState) (res : List Word) (m' : Mem), StageR dn vis fe m a →
      StmtL m so.toNat sl.toNat ss → decHL m po.toNat pl.toNat = some proofs →
      po.toNat + pl.toNat ≤ iwTop m →
      callW p k "check_div_mod_certs" [vis, c, annVal, so, sl, po, pl] m = some (res, m') →
      ∃ x a', (checkDivModCerts V fe (decI c) (decE annVal) ss proofs).run a = .ok (x, a') ∧
        KeepPost dn vis fe decW0B m m' a' res x := by
  intro ss
  induction ss with
  | nil =>
    intro proofs so sl po pl k m a res m' hS hs hd hb hc'
    have hsl : sl = 0 := UInt64.toNat_inj.mp (by have := hs.2.1; simpa using this)
    cases k with
    | zero => rw [callW_zero] at hc'; cases hc'
    | succ k =>
    have hw := callW_model (M := fun mq => cmW p stubCall k mq vis c annVal so sl po pl)
      (cm_specW p hD.lCheckDivModCerts stubCall (stubCall_spec p) k · vis c annVal so sl po pl) hc'
    unfold cmW at hw
    cases proofs with
    | nil =>
      have hpl : pl = 0 := UInt64.toNat_inj.mp (by have := decHL_length m hd; simp at this ⊢; omega)
      simp only [hsl, hpl, and_self, if_true, Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      exact ⟨true, a, rfl, hS, IWGrow.refl _, by simp [decW0B]⟩
    | cons pf pfs =>
      have hpl : pl ≠ 0 := fun e => by
        have := decHL_length m hd; rw [e] at this; simp at this
      rw [if_neg (fun h => hpl h.2), if_pos (Or.inl hsl)] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      exact ⟨false, a, rfl, hS, IWGrow.refl _, by simp [decW0B]⟩
  | cons st ss ih =>
    rcases st with ⟨hy, eqq⟩
    intro proofs so sl po pl k m a res m' hS hs hd hb hc'
    cases k with
    | zero => rw [callW_zero] at hc'; cases hc'
    | succ k =>
    have hw := callW_model (M := fun mq => cmW p stubCall k mq vis c annVal so sl po pl)
      (cm_specW p hD.lCheckDivModCerts stubCall (stubCall_spec p) k · vis c annVal so sl po pl) hc'
    unfold cmW at hw
    obtain ⟨hsl0, q, hq, hstm, hrest⟩ := StmtL.cons hS.2 hs
    cases proofs with
    | nil =>
      have hpl : pl = 0 := UInt64.toNat_inj.mp (by have := decHL_length m hd; simp at this ⊢; omega)
      simp only [hpl, and_true, or_true, hsl0, false_and, if_false, if_true, Option.some.injEq,
        Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      exact ⟨false, a, rfl, hS, IWGrow.refl _, by simp [decW0B]⟩
    | cons pf pfs =>
    obtain ⟨hpl0, hpwlt, hpf, hdrest⟩ := decHL_cons_iw hS.2.2.2.1 hd
    subst hpf
    obtain ⟨ho, hl, e, hr3, hbd, hdh, he, hst2⟩ := hstm
    obtain ⟨hp3, h0, h1, h2⟩ := hr3
    have hst2' : eqq = decE e := hst2
    subst hst2'
    rw [if_neg (fun h => hsl0 h.1), if_neg (by rintro (h | h); exact hsl0 h; exact hpl0 h)] at hw
    have hsz := hS.2.2.2.1
    have hI1 := hS.2.1
    have r0 : rdW (m.arr64 IW) so = q := hq
    have rq1 : rdW (m.arr64 IW) q = ho := rdW_iw_of h0 rfl
    have rq2 : rdW (m.arr64 IW) (q + 1) = hl := rdW_iw_of h1 (word_add_one (by omega))
    have rq3 : rdW (m.arr64 IW) (q + 2) = e := rdW_iw_of h2 (word_add_two (by omega))
    have hlpos : 0 < pl.toNat := Nat.pos_of_ne_zero (fun e' => hpl0 (UInt64.toNat_inj.mp (by simpa using e')))
    have hpo1 : (po + 1).toNat = po.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; omega
    have hpl1 : (pl - 1).toNat = pl.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
    have hpo : po.toNat < iwTop m := by omega
    have hq3 : q.toNat + 3 ≤ iwTop m := hp3
    have hq0 : q.toNat < iwTop m := by omega
    have hq1 : (q + 1).toNat < iwTop m := by rw [word_add_one (by omega)]; omega
    have hq2 : (q + 2).toNat < iwTop m := by rw [word_add_two (by omega)]; omega
    rw [r0, rq1, rq2, rq3] at hw
    -- the guard
    cases h1' : callW p k "div_mod_cert_guard" [vis, c, annVal, ho, hl, e, rdW (m.arr64 IW) po] m with
    | none => rw [h1'] at hw; simp at hw
    | some q1 =>
    obtain ⟨r1, m1⟩ := q1
    rw [h1', bW_some] at hw
    obtain ⟨x1, a1, hrun1, hS1, hg1, hd1⟩ :=
      cg_ref hD.toDmProg7.toDmProg6.toDmProg5 hs0 hsA c annVal ho hl e (rdW (m.arr64 IW) po) hy k m a r1 m1
        ⟨hS, hc, hann, he, hpwlt, hdh, hbd⟩ h1'
    have hrun1' : (divModCertGuard fe (decI c) (decE annVal) hy (decE e) (decI (rdW (m.arr64 IW) po))).run a = .ok (x1, a1) := hrun1
    by_cases z1 : r1.headD 0 = 0
    · rw [if_pos z1] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      have hx1 := decW0B_false hd1 z1
      refine ⟨false, a1, ?_, hS1, hg1, decW0B_of_false _⟩
      simp only [checkDivModCerts, StateT.run_bind, hrun1', exc_ok_bind', hx1, Bool.false_eq_true,
        if_false]
      rfl
    rw [if_neg z1] at hw
    have hx1 := decW0B_true hd1 z1
    -- the substituted proof
    rw [iw_rd_grow hg1 hpo] at hw
    cases h2' : callW p k "subst_const_all" [c, annVal, 4000000000, rdW (m.arr64 IW) po] m1 with
    | none => rw [h2'] at hw; simp at hw
    | some q2 =>
    obtain ⟨r2, m2⟩ := q2
    rw [h2', bW_some] at hw
    obtain ⟨x2, a2, hrun2, hS2, hg2, hl2, hx2⟩ := hsA c annVal _ hc hann hpwlt k m1 a1 r2 m2 hS1 h2'
    subst hx2
    have hG2 : IWGrow m m2 := hg1.trans hg2
    -- the substituted hypotheses
    rw [iw_rd_grow hG2 hq0, rq1, iw_rd_grow hG2 hq1, rq2] at hw
    cases h3' : callW p k "subst_const0_list" [c, annVal, ho, hl] m2 with
    | none => rw [h3'] at hw; simp at hw
    | some q3 =>
    obtain ⟨r3, m3⟩ := q3
    rw [h3', bW_some] at hw
    have hdh2 : decHL m2 ho.toNat hl.toNat = some hy := by rw [decHL_grow hG2 hbd]; exact hdh
    obtain ⟨x3, a3, hrun3, hS3, hg3, hd3⟩ := sc0List_ref hD.toDmProg7.toDmProg6.toDmProg5 hs0 c annVal hc hann hy ho hl k m2 a2 r3 m3 hS2 hdh2
      (Nat.le_trans hbd hG2.1) h3'
    simp only [decRL, Nat.zero_add, ntGetD0, ntGetD1] at hd3
    have hG3 : IWGrow m m3 := hG2.trans hg3
    -- the application
    obtain ⟨r4, m4, x4, a4, hrun4, ⟨hS4, hg4, hl4, rfl⟩, hw⟩ :=
      (applied_ref (dn := dn) (vis := vis) (fe := fe) hD.toDmProg7.toDmProg6.toDmProg5 (r2.headD 0) (r3.headD 0)
        (r3.tail.headD 0) x3).bind_ ⟨hS3, hl2, hd3.1, hd3.2⟩ hw
    have hG4 : IWGrow m m4 := hG3.trans hg4
    -- the type
    cases h5 : stubCall k "infer_type_core" [vis, 4, r4.headD 0] m4 with
    | none => rw [h5] at hw; simp at hw
    | some q5 =>
    obtain ⟨r5, m5⟩ := q5
    rw [h5, bW_some] at hw
    obtain ⟨x5, a5, hrun5, hS5, hg5, hl5, hx5⟩ := inferTypeCore_spec dn vis fe 4 (r4.headD 0) hl4 m4 m5 a4 r5 h5 hS4
    subst hx5
    have h4w : (4 : Word).toNat = 4 := rfl
    rw [h4w] at hrun5
    have hG5 : IWGrow m m5 := hG4.trans hg5
    -- the equation, substituted
    rw [iw_rd_grow hG5 hq2, rq3] at hw
    cases h6 : callW p k "subst_const0" [c, annVal, 4000000000, e] m5 with
    | none => rw [h6] at hw; simp at hw
    | some q6 =>
    obtain ⟨r6, m6⟩ := q6
    rw [h6, bW_some] at hw
    obtain ⟨x6, a6, hrun6, hS6, hg6, hl6, hx6⟩ := hs0 c annVal e hc hann he k m5 a5 r6 m6 hS5 h6
    subst hx6
    have hG6 : IWGrow m m6 := hG5.trans hg6
    cases h7 : stubCall k "is_def_eq_core" [vis, 4, r5.headD 0, r6.headD 0] m6 with
    | none => rw [h7] at hw; simp at hw
    | some q7 =>
    obtain ⟨r7, m7⟩ := q7
    rw [h7, bW_some] at hw
    obtain ⟨x7, a7, hrun7, hS7, hg7, hd7⟩ := isDefEqCore_spec dn vis fe 4 (r5.headD 0) (r6.headD 0) hl5 hl6 m6 m7 a6 r7 h7 hS6
    rw [h4w] at hrun7
    have hG7 : IWGrow m m7 := hG6.trans hg7
    have hrun4' : (divModCertApplied (decI (r2.headD 0)) x3).run a3 = .ok (decI (r4.headD 0), a4) := hrun4
    have hrun2' : (substConstAll (decI c) (decE annVal) coreWalkFuel (decI (rdW (m.arr64 IW) po))).run a1 = .ok (decI (r2.headD 0), a2) := hrun2
    have hrun6' : (substConst0 (decI c) (decE annVal) coreWalkFuel (decE e)).run a5 = .ok (decI (r6.headD 0), a6) := hrun6
    by_cases z7 : r7.headD 0 = 0
    · rw [if_pos z7] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      have hx7 := decW0B_false hd7 z7
      refine ⟨false, a7, ?_, hS7, hG7, decW0B_of_false _⟩
      simp only [checkDivModCerts, StateT.run_bind, hrun1', exc_ok_bind', hx1, if_true, hrun2', hrun3, hrun4', hrun5,
        hrun6', hrun7, hx7, Bool.false_eq_true, if_false]
      try rfl
    rw [if_neg z7] at hw
    have hx7 := decW0B_true hd7 z7
    cases h8 : callW p k "check_div_mod_certs" [vis, c, annVal, so + 1, sl - 1, po + 1, pl - 1] m7 with
    | none => rw [h8] at hw; simp at hw
    | some q8 =>
    obtain ⟨r8, m8⟩ := q8
    rw [h8, bW_some] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hdr1 : decHL m7 (po + 1).toNat (pl - 1).toNat = some pfs := by
      rw [decHL_grow hG7 (by rw [hpo1, hpl1]; omega)]; exact hdrest
    obtain ⟨x8, a8, hrun8, hS8, hg8, hd8⟩ := ih pfs (so + 1) (sl - 1) (po + 1) (pl - 1) k m7 a7 r8 m8 hS7
      (hrest.grow hG7) hdr1 (by rw [hpo1, hpl1]; have := hG7.1; omega) h8
    refine ⟨x8, a8, ?_, hS8, hG7.trans hg8, hd8⟩
    simp only [checkDivModCerts, StateT.run_bind, hrun1', exc_ok_bind', hx1, if_true, hrun2', hrun3, hrun4', hrun5,
      hrun6', hrun7, hx7, if_true]
    exact hrun8

/-- Under `StageR` (the core through its stub); the census link is `cmC` (`DeclDivGateT2.lean`). -/
theorem checkDivModCerts_refines (hD : DmProg8 p) (hs0 : SubstC0 p dn vis fe)
    (hsA : SubstCAll p dn vis fe) (c annVal : Word) (hc : H c) (hann : H annVal)
    (so sl po pl : Word) (ss : List (List EIdx × EIdx)) (proofs : List EIdx) :
    RefAM p "check_div_mod_certs" [vis, c, annVal, so, sl, po, pl]
      (fun m s => StageR dn vis fe m s ∧ StmtL m so.toNat sl.toNat ss ∧
        decHL m po.toNat pl.toNat = some proofs ∧ po.toNat + pl.toNat ≤ iwTop m)
      (checkDivModCerts V fe (decI c) (decE annVal) ss proofs) (KeepPost dn vis fe decW0B) :=
  CallRef.refAM (fun k m a res m' ⟨hS, hs, hd, hb⟩ hcall =>
    cm_ref hD hs0 hsA c annVal hc hann ss proofs so sl po pl k m a res m' hS hs hd hb hcall)

/-! ## `check_div_mod_pin_at` -/

def cpaW (p : Prog) (cl : CallM) (n : Nat) (m : Mem) (vs c value ps : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "div_mod_decl_pin" [ps, c] m) fun r1 m1 =>
  ntBW (cl n "is_def_eq_core" [vs, 0, value, r1.headD 0] m1) fun r2 m2 =>
  if r2.headD 0 = 0 then some ([0], m2) else
  ntBW (callW p n "div_mod_cert_stmts" [c] m2) fun r3 m3 =>
  ntBW (callW p n "div_mod_cert_proofs" [ps, c] m3) fun r4 m4 =>
  ntBW (callW p n "check_div_mod_certs" [vs, c, value, r3.headD 0, r3.tail.headD 0, r4.headD 0,
    r4.tail.headD 0] m4) fun r5 m5 => some ([r5.headD 0], m5)

set_option maxHeartbeats 3200000 in
theorem cpa_specW (p : Prog) (hp : p.lookup "check_div_mod_pin_at" = some checkDivModPinAtL)
    (cl : CallM) (hc : CallSpec p cl) (n : Nat) (s₀ : St) (vs c value ps : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check_div_mod_pin_at" [vs, c, value, ps]
    ⦃fun r s' => LocEq s' s₀ ∧ cpaW p cl n s₀.mem vs c value ps = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkDivModPinAtL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "div_mod_decl_pin", hc n "is_def_eq_core",
      callW_spec p n "div_mod_cert_stmts", callW_spec p n "div_mod_cert_proofs",
      callW_spec p n "check_div_mod_certs"] <;>
    finish (gen := 30) (instances := 10000) [cpaW, ntBW]

theorem cpa_ref (hD : DmProg8 p) (hs0 : SubstC0 p dn vis fe) (hsA : SubstCAll p dn vis fe)
    (c value ps : Word) (ip : INatOpPinSet) :
    CallRef p "check_div_mod_pin_at" [vis, c, value, ps]
      (fun m s => StageR dn vis fe m s ∧ H c ∧ H value ∧ PinSetR m ps ip)
      (checkDivModPinAt V fe (decI c) (decE value) ip) (KeepPost dn vis fe decW0B) := by
  refine CallRef.of_succ fun k m s rr mm ⟨hS, hc, hval, hP⟩ hcall => ?_
  have hw := callW_model (M := fun mq => cpaW p stubCall k mq vis c value ps)
    (cpa_specW p hD.lCheckDivModPinAt stubCall (stubCall_spec p) k · vis c value ps) hcall
  unfold cpaW at hw
  have h0w : (0 : Word).toNat = 0 := rfl
  have hD5 := hD.toDmProg7.toDmProg6.toDmProg5
  obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hg1, hl1, hx1⟩, hw⟩ :=
    (divModDeclPin_ref hD5.toDmProg2.toDmProg1 ps c ip).bind_ ⟨hS, hc, hP⟩ hw
  cases h2 : stubCall k "is_def_eq_core" [vis, 0, value, r1.headD 0] m1 with
  | none => rw [h2] at hw; simp at hw
  | some q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, bW_some] at hw
  obtain ⟨x2, a2, hrun2, hS2, hg2, hd2⟩ := isDefEqCore_spec dn vis fe 0 value (r1.headD 0) hval hl1 m1 m2 a1 r2 h2 hS1
  rw [h0w, hx1] at hrun2
  have hrun1' : (divModDeclPin ip (decI c)).run s = .ok (decI (r1.headD 0), a1) := by rw [hx1]; exact hrun1
  have hrun2' : (isDefEqCore V fe checkFuel 0 (decE value) (decI (r1.headD 0))).run a1 = .ok (x2, a2) := by
    rw [hx1]; exact hrun2
  by_cases z2 : r2.headD 0 = 0
  · rw [if_pos z2] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hx2 := decW0B_false hd2 z2
    refine ⟨false, a2, ?_, hS2, hg1.trans hg2, decW0B_of_false _⟩
    simp only [checkDivModPinAt, StateT.run_bind, hrun1', exc_ok_bind', hrun2', hx2,
      Bool.false_eq_true, if_false]
    rfl
  rw [if_neg z2] at hw
  have hx2 := decW0B_true hd2 z2
  obtain ⟨r3, m3, x3, a3, hrun3, ⟨hS3, hg3, hd3⟩, hw⟩ :=
    (divModCertStmts_ref hD5.toDmProg2 c).bind_ ⟨hS2, hc⟩ hw
  obtain ⟨r4, m4, x4, a4, hrun4, ⟨hS4, hg4, hd4⟩, hw⟩ :=
    (divModCertProofs_ref hD5.toDmProg2.toDmProg1 ps c ip).bind_
      ⟨hS3, hc, PinSetR.grow (PinSetR.grow hP hg1) (hg2.trans hg3)⟩ hw
  cases h5 : callW p k "check_div_mod_certs" [vis, c, value, r3.headD 0, r3.tail.headD 0,
      r4.headD 0, r4.tail.headD 0] m4 with
  | none => rw [h5] at hw; simp at hw
  | some q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [h5, bW_some] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  simp only [decStmtL, ntGetD0, ntGetD1] at hd3
  unfold decRL at hd4
  simp only [Nat.zero_add, ntGetD0, ntGetD1] at hd4
  obtain ⟨x5, a5, hrun5, hS5, hg5, hd5⟩ := cm_ref hD hs0 hsA c value hc hval x3 x4 (r3.headD 0)
    (r3.tail.headD 0) (r4.headD 0) (r4.tail.headD 0) k m4 a4 r5 m5 hS4 (hd3.grow hg4) hd4.1 hd4.2 h5
  refine ⟨x5, a5, ?_, hS5, hg1.trans (hg2.trans (hg3.trans (hg4.trans hg5))), hd5⟩
  simp only [checkDivModPinAt, StateT.run_bind, hrun1', exc_ok_bind', hrun2', hx2, if_true, hrun3,
    hrun4]
  exact hrun5

/-- Under `StageR` (the core through its stub); the census link is `cpaC` (`DeclDivGateT2.lean`). -/
theorem checkDivModPinAt_refines (hD : DmProg8 p) (hs0 : SubstC0 p dn vis fe)
    (hsA : SubstCAll p dn vis fe) (c value ps : Word) (ip : INatOpPinSet) :
    RefAM p "check_div_mod_pin_at" [vis, c, value, ps]
      (fun m s => StageR dn vis fe m s ∧ H c ∧ H value ∧ PinSetR m ps ip)
      (checkDivModPinAt V fe (decI c) (decE value) ip) (KeepPost dn vis fe decW0B) :=
  (cpa_ref hD hs0 hsA c value ps ip).refAM

end certs

end L.Ind
