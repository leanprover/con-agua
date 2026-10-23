import ConAgua.Arena.DeclDivMod5
import ConAgua.Arena.DeclCanonEq
import ConAgua.Arena.DeclRomStubs

/-!
# The `Nat.div` family's pin gate, bottom up: the guards (lane `decls3`, `decls3-divmod`)

Part 6: `bool_ctor_typed`, `div_mod_pin_guard`, `div_mod_certs_guard_go`, `div_mod_certs_guard`.
-/

noncomputable section

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

structure DmProg6 (p : Prog) : Prop extends DmProg5 p where
  lBoolCtorTyped : p.lookup "bool_ctor_typed" = some boolCtorTypedL
  lDivModPinGuard : p.lookup "div_mod_pin_guard" = some divModPinGuardL
  lCertsGuardGo : p.lookup "div_mod_certs_guard_go" = some divModCertsGuardGoL
  lCertsGuard : p.lookup "div_mod_certs_guard" = some divModCertsGuardL

section guards
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

/-! ## `bool_ctor_typed` -/

def dmBctW (p : Prog) (n : Nat) (m : Mem) (v nm : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "env_find" [nm, v] m) fun r1 m1 =>
  if r1.headD 0 = 0 then some ([0], m1) else
  ntBW (callW p n "ci_to_cv" [r1.tail.headD 0] m1) fun r2 m2 =>
  ntBW (callW p n "pin_at" [29] m2) fun r3 m3 =>
  ntBW (callW p n "const_e" [r3.headD 0] m3) fun r4 m4 =>
  some ([if rdW (m4.arr64 EREC) (r2.headD 0 + 3) = r4.headD 0 then 1 else 0], m4)

set_option maxHeartbeats 1600000 in
theorem bct_specW (p : Prog) (hp : p.lookup "bool_ctor_typed" = some boolCtorTypedL) (n : Nat)
    (s₀ : St) (v nm : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "bool_ctor_typed" [v, nm]
    ⦃fun r s' => LocEq s' s₀ ∧ dmBctW p n s₀.mem v nm = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, boolCtorTypedL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "env_find", callW_spec p n "ci_to_cv", callW_spec p n "pin_at",
      callW_spec p n "const_e"] <;>
    finish (gen := 30) (instances := 10000) [dmBctW, ntBW, rdW_eq]

theorem DmProg2.cvProg (hD : DmProg2 p) : NatCvProg p :=
  hD.toNatEqProg.toNatTyProg.toNatGuardProg.toNatLitProg.toNatCvProg

theorem bct_ref (hD : DmProg6 p) (nm : Word) :
    CallRef p "bool_ctor_typed" [vis, nm] (fun m a => StageR dn vis fe m a ∧ H nm)
      (boolCtorTyped fe (decI nm)) (KeepPost dn vis fe decW0B) := by
  refine CallRef.of_succ fun k m a r m' ⟨hS, hn⟩ hcall => ?_
  have hw := callW_model (M := fun mq => dmBctW p k mq vis nm)
    (bct_specW p hD.lBoolCtorTyped k · vis nm) hcall
  unfold dmBctW at hw
  cases h1 : callW p k "env_find" [nm, vis] m with
  | none => rw [h1] at hw; simp at hw
  | some q1 =>
  obtain ⟨rf, m1⟩ := q1
  rw [h1, bW_some] at hw
  obtain ⟨hm1, hfd⟩ := envFind_call hD.toDmProg5.toMasterProg nm hn hS.1.env h1
  subst hm1
  cases hf : fe.find? (decI nm) with
  | none =>
    rw [hf] at hfd
    have hz : rf.headD 0 = 0 := hfd
    rw [if_pos hz] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact ⟨false, a, by simp only [boolCtorTyped, hf]; rfl, hS, IWGrow.refl _, by simp [decW0B]⟩
  | some ci =>
    rw [hf] at hfd
    obtain ⟨hr1, hci⟩ := hfd
    rw [if_neg (by rw [hr1]; decide)] at hw
    obtain ⟨r2, m2, x2, a2, hrun2, ⟨hS2, hg2, hcv2⟩, hw⟩ :=
      (ciToCv_ref hD.toDmProg5.cvProg (rf.tail.headD 0) ci).bind_ ⟨hS, hci⟩ hw
    obtain ⟨r3, m3, x3, a3, hrun3, ⟨hS3, hg3, hl3, rfl⟩, hw⟩ :=
      (pinSlot_ref p hD.toDmProg5.lPinAt 29 pinBool rfl).bind_ hS2 hw
    obtain ⟨r4, m4, x4, a4, hrun4, ⟨hS4, hg4, hl4, rfl⟩, hw⟩ :=
      (constE_ref hD.toDmProg5.toMasterProg (r3.headD 0)).bind_ ⟨hS3, hl3⟩ hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    obtain ⟨wt, -, hrd, hwt, hty, hst⟩ := cvWordsAt hS2.2.2.2.2.1 hcv2
    have hrd4 := (hst m4 (hg3.trans hg4)).2
    refine ⟨decide (wt = r4.headD 0), a4, ?_, hS4, hg2.trans (hg3.trans hg4), ?_⟩
    · have hb := decI_beq_word (κ := IdxKind.expr) hwt hl4
      simp only [boolCtorTyped, hf, StateT.run_bind, hrun2, exc_ok_bind', boolName, hrun3]
      have hrun4' : (constE (decI (r3.headD 0))).run a3 = .ok (decI (r4.headD 0), a4) := hrun4
      simp only [hrun4', exc_ok_bind', hty]
      simp only [bne_iff_ne, hb]
      try rfl
    · rw [hrd4]
      unfold decW0B
      simp only [List.headD_cons]
      generalize r4.headD 0 = z
      by_cases e : wt = z <;> simp [e]

@[refines ConRon.Arena.boolCtorTyped]
theorem boolCtorTyped_refines (hD : DmProg6 p) (nm : Word) :
    RefAM p "bool_ctor_typed" [vis, nm] (fun m a => StageR dn vis fe m a ∧ H nm)
      (boolCtorTyped fe (decI nm)) (KeepPost dn vis fe decW0B) :=
  (bct_ref hD nm).refAM

/-! ## `div_mod_pin_guard` -/

def dmPgW (p : Prog) (cl : CallM) (n : Nat) (m : Mem) (ps vs c : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "div_mod_decl_pin" [ps, c] m) fun r1 m1 =>
  ntBW (lbbF m1 [4000000000, 0, r1.headD 0]) fun r2 m2 =>
  if r2.headD 0 = 0 then some ([0], m2) else
  ntBW (hffF m2 [4000000000, r1.headD 0]) fun r3 m3 =>
  if r3.headD 0 ≠ 0 then some ([0], m3) else
  ntBW (cl n "all_level_params_defined" [0, 0, r1.headD 0] m3) fun r4 m4 =>
  if r4.headD 0 = 0 then some ([0], m4) else
  ntBW (stubM "consts_resolve_ffast" m4 [vs, r1.headD 0]) fun r5 m5 => some ([r5.headD 0], m5)

set_option maxHeartbeats 1600000 in
theorem pg_specW (p : Prog) (hb : BvbProg p) (hf : HfF p) (hp : p.lookup "div_mod_pin_guard" = some divModPinGuardL)
    (cl : CallM) (hcl : CallSpec p cl) (n : Nat)
    (s₀ : St) (ps vs c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "div_mod_pin_guard" [ps, vs, c]
    ⦃fun r s' => LocEq s' s₀ ∧ dmPgW p cl n s₀.mem ps vs c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, divModPinGuardL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "div_mod_decl_pin", lbbF_spec p hb n,
      hffF_spec p hf n, hcl n "all_level_params_defined",
      stubM_spec p "consts_resolve_ffast" n] <;>
    finish (gen := 30) (instances := 10000) [dmPgW, ntBW]

theorem pg_ref (hD : DmProg6 p) (ps c : Word) (ip : INatOpPinSet) :
    CallRef p "div_mod_pin_guard" [ps, vis, c]
      (fun m s => StageR dn vis fe m s ∧ H c ∧ PinSetR m ps ip)
      (divModPinGuard ip fe (decI c)) (KeepPost dn vis fe decW0B) := by
  refine CallRef.of_succ fun k m s rr mm ⟨hS, hc, hP⟩ hcall => ?_
  have hw := callW_model (M := fun mq => dmPgW p stubCall k mq ps vis c)
    (pg_specW p hD.bvb hD.hf hD.lDivModPinGuard stubCall (stubCall_spec p) k · ps vis c) hcall
  unfold dmPgW at hw
  have h0w : (0 : Word).toNat = 0 := rfl
  obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hg1, hl1, hx1⟩, hw⟩ :=
    (divModDeclPin_ref hD.toDmProg5.toDmProg2.toDmProg1 ps c ip).bind_ ⟨hS, hc, hP⟩ hw
  cases h2 : lbbF m1 [4000000000, 0, r1.headD 0] with
  | none => rw [h2] at hw; simp at hw
  | some q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, bW_some] at hw
  obtain ⟨x2, a2, hrun2, hS2, hg2, hd2⟩ :=
    lbbF_ok dn vis fe 4000000000 0 (r1.headD 0) hl1 m1 m2 a1 r2 h2 hS1
  rw [fuelW_eq, h0w, hx1] at hrun2
  by_cases z2 : r2.headD 0 = 0
  · rw [if_pos z2] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hx2 := decW0B_false hd2 z2
    refine ⟨false, a2, ?_, hS2, hg1.trans hg2, decW0B_of_false _⟩
    simp only [divModPinGuard, StateT.run_bind, hrun1, exc_ok_bind', hrun2, hx2]
    rfl
  rw [if_neg z2] at hw
  have hx2 := decW0B_true hd2 z2
  cases h3 : hffF m2 [4000000000, r1.headD 0] with
  | none => rw [h3] at hw; simp at hw
  | some q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, bW_some] at hw
  obtain ⟨x3, a3, hrun3, hS3, hg3, hd3⟩ := hffF_ok dn vis fe 4000000000 (r1.headD 0) hl1 m2 m3 a2 r3 h3 hS2
  rw [fuelW_eq, hx1] at hrun3
  by_cases z3 : r3.headD 0 ≠ 0
  · rw [if_pos z3] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hx3 := decW0B_true hd3 z3
    refine ⟨false, a3, ?_, hS3, hg1.trans (hg2.trans hg3), decW0B_of_false _⟩
    simp only [divModPinGuard, StateT.run_bind, hrun1, exc_ok_bind', hrun2, hx2, hrun3, hx3,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, eq_self, if_true, if_false]
    rfl
  rw [if_neg z3] at hw
  have z3' : r3.headD 0 = 0 := by simpa using z3
  have hx3 := decW0B_false hd3 z3'
  cases h4 : stubCall k "all_level_params_defined" [0, 0, r1.headD 0] m3 with
  | none => rw [h4] at hw; simp at hw
  | some q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [h4, bW_some] at hw
  obtain ⟨x4, a4, hrun4, hS4, hg4, hd4⟩ := allLevelParamsDefined_spec dn vis fe 0 0 (r1.headD 0) hl1 []
    m3 m4 a3 r4 h4 ⟨hS3, by rw [h0w]; simp [decHL, hslice?]⟩
  rw [hx1] at hrun4
  by_cases z4 : r4.headD 0 = 0
  · rw [if_pos z4] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hx4 := decW0B_false hd4 z4
    refine ⟨false, a4, ?_, hS4, hg1.trans (hg2.trans (hg3.trans hg4)), decW0B_of_false _⟩
    simp only [divModPinGuard, StateT.run_bind, hrun1, exc_ok_bind', hrun2, hx2, hrun3, hx3, hrun4,
      hx4, Bool.not_true, Bool.not_false, Bool.false_eq_true, eq_self, if_true, if_false]
    rfl
  rw [if_neg z4] at hw
  have hx4 := decW0B_true hd4 z4
  cases h5 : stubM "consts_resolve_ffast" m4 [vis, r1.headD 0] with
  | none => rw [h5] at hw; simp at hw
  | some q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [h5, bW_some] at hw
  obtain ⟨x5, a5, hrun5, hS5, hg5, hd5⟩ := constsResolveFFast_spec dn vis fe (r1.headD 0) hl1 m4 m5 a4 r5 h5 hS4
  rw [hx1] at hrun5
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  refine ⟨x5, a5, ?_, hS5, hg1.trans (hg2.trans (hg3.trans (hg4.trans hg5))), hd5⟩
  simp only [divModPinGuard, StateT.run_bind, hrun1, exc_ok_bind', hrun2, hx2, hrun3, hx3, hrun4,
    hx4, hrun5, Bool.not_true, Bool.not_false, Bool.false_eq_true, eq_self, if_true, if_false]

@[refines ConRon.Arena.divModPinGuard]
theorem divModPinGuard_refines (hD : DmProg6 p) (ps c : Word) (ip : INatOpPinSet) :
    RefAM p "div_mod_pin_guard" [ps, vis, c]
      (fun m s => StageR dn vis fe m s ∧ H c ∧ PinSetR m ps ip)
      (divModPinGuard ip fe (decI c)) (KeepPost dn vis fe decW0B) :=
  (pg_ref hD ps c ip).refAM

/-! ## `div_mod_certs_guard_go` -/

theorem rdW_iw_of {m : Mem} {x : Word} {i : Nat} {w : Word} (h : (iwA m)[i]? = some w)
    (hx : x.toNat = i) : rdW (m.arr64 IW) x = w := by
  simp only [iwA] at h; simp [rdW, hx, h]

theorem word_add_two {w : Word} (h : w.toNat + 2 < 2 ^ 64) : (w + 2).toNat = w.toNat + 2 := by
  rw [UInt64.toNat_add]; simp; omega

theorem StmtL.cons {m : Mem} {so sl : Word} {s : List EIdx × EIdx} {ss : List (List EIdx × EIdx)}
    (hI : IWOK m) (h : StmtL m so.toNat sl.toNat (s :: ss)) :
    sl ≠ 0 ∧ ∃ q : Word, rdW (m.arr64 IW) so = q ∧ StmtAt m q s ∧
      StmtL m (so + 1).toNat (sl - 1).toNat ss := by
  obtain ⟨hb, hl, hj⟩ := h
  have hl0 : sl ≠ 0 := fun e => by rw [e] at hl; simp at hl
  have hlen : sl.toNat = ss.length + 1 := by simpa using hl
  have ho : (so + 1).toNat = so.toNat + 1 := by
    have h1 := hI.1; have h2 := hI.2.2.1
    rw [UInt64.toNat_add]; simp; omega
  have hl1 : (sl - 1).toNat = ss.length := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
  obtain ⟨q, hq, hs⟩ := hj 0 (by simp)
  refine ⟨hl0, q, rdW_iw_of (by simpa using hq) rfl, by simpa using hs, ?_⟩
  rw [ho, hl1]
  refine ⟨by omega, rfl, fun j hj' => ?_⟩
  obtain ⟨q2, hq2, hs2⟩ := hj (j + 1) (by simpa using hj')
  exact ⟨q2, by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hq2, by simpa using hs2⟩

def cggoW (p : Prog) (n : Nat) (m : Mem) (vs c annVal so sl po pl : Word) : Option (List Word × Mem) :=
  if sl = 0 ∨ pl = 0 then some ([1], m) else
  ntBW (callW p n "div_mod_cert_guard" [vs, c, annVal, rdW (m.arr64 IW) (rdW (m.arr64 IW) so),
    rdW (m.arr64 IW) (rdW (m.arr64 IW) so + 1), rdW (m.arr64 IW) (rdW (m.arr64 IW) so + 2),
    rdW (m.arr64 IW) po] m) fun r1 m1 =>
  if r1.headD 0 = 0 then some ([0], m1) else
  ntBW (callW p n "div_mod_certs_guard_go" [vs, c, annVal, so + 1, sl - 1, po + 1, pl - 1] m1) fun r2 m2 =>
    some ([r2.headD 0], m2)

set_option maxHeartbeats 1600000 in
theorem cggo_specW (p : Prog) (hp : p.lookup "div_mod_certs_guard_go" = some divModCertsGuardGoL)
    (n : Nat) (s₀ : St) (vs c annVal so sl po pl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "div_mod_certs_guard_go" [vs, c, annVal, so, sl, po, pl]
    ⦃fun r s' => LocEq s' s₀ ∧ cggoW p n s₀.mem vs c annVal so sl po pl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, divModCertsGuardGoL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "div_mod_cert_guard", callW_spec p n "div_mod_certs_guard_go"] <;>
    finish (gen := 30) (instances := 10000) [cggoW, ntBW, rdW_eq]

theorem cggo_ref (hD : DmProg6 p) (hs0 : SubstC0 p dn vis fe) (hsA : SubstCAll p dn vis fe)
    (c annVal : Word) (hc : H c) (hann : H annVal) :
    ∀ (ss : List (List EIdx × EIdx)) (proofs : List EIdx) (so sl po pl : Word) (k : Nat) (m : Mem)
      (a : AState) (res : List Word) (m' : Mem), StageR dn vis fe m a →
      StmtL m so.toNat sl.toNat ss → decHL m po.toNat pl.toNat = some proofs →
      po.toNat + pl.toNat ≤ iwTop m →
      callW p k "div_mod_certs_guard_go" [vis, c, annVal, so, sl, po, pl] m = some (res, m') →
      ∃ x a', (divModCertsGuardGo fe (decI c) (decE annVal) ss proofs).run a = .ok (x, a') ∧
        KeepPost dn vis fe decW0B m m' a' res x := by
  intro ss
  induction ss with
  | nil =>
    intro proofs so sl po pl k m a res m' hS hs hd hb hc'
    have hsl : sl = 0 := UInt64.toNat_inj.mp (by have := hs.2.1; simpa using this)
    cases k with
    | zero => rw [callW_zero] at hc'; cases hc'
    | succ k =>
    have hw := callW_model (M := fun mq => cggoW p k mq vis c annVal so sl po pl)
      (cggo_specW p hD.lCertsGuardGo k · vis c annVal so sl po pl) hc'
    simp only [cggoW, hsl, true_or, if_true, Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact ⟨true, a, by cases proofs <;> rfl, hS, IWGrow.refl _, by simp [decW0B]⟩
  | cons st ss ih =>
    rcases st with ⟨hy, eqq⟩
    intro proofs so sl po pl k m a res m' hS hs hd hb hc'
    cases k with
    | zero => rw [callW_zero] at hc'; cases hc'
    | succ k =>
    have hw := callW_model (M := fun mq => cggoW p k mq vis c annVal so sl po pl)
      (cggo_specW p hD.lCertsGuardGo k · vis c annVal so sl po pl) hc'
    unfold cggoW at hw
    cases proofs with
    | nil =>
      have hpl : pl = 0 := UInt64.toNat_inj.mp (by have := decHL_length m hd; simp at this ⊢; omega)
      simp only [hpl, or_true, if_true, Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      exact ⟨true, a, rfl, hS, IWGrow.refl _, by simp [decW0B]⟩
    | cons pf pfs =>
    obtain ⟨hsl0, q, hq, hstm, hrest⟩ := StmtL.cons hS.2 hs
    obtain ⟨hpl0, hpwlt, hpf, hdrest⟩ := decHL_cons_iw hS.2.2.2.1 hd
    subst hpf
    obtain ⟨ho, hl, e, hr3, hbd, hdh, he, hst2⟩ := hstm
    obtain ⟨hp3, h0, h1, h2⟩ := hr3
    have hst2' : eqq = decE e := hst2
    subst hst2'
    rw [if_neg (by simp [hsl0, hpl0])] at hw
    have hsz := hS.2.2.2.1
    have hI1 := hS.2.1
    have r0 : rdW (m.arr64 IW) so = q := hq
    have rq1 : rdW (m.arr64 IW) q = ho := rdW_iw_of h0 rfl
    have rq2 : rdW (m.arr64 IW) (q + 1) = hl :=
      rdW_iw_of h1 (word_add_one (by omega))
    have rq3 : rdW (m.arr64 IW) (q + 2) = e :=
      rdW_iw_of h2 (word_add_two (by omega))
    rw [r0, rq1, rq2, rq3] at hw
    cases h1' : callW p k "div_mod_cert_guard" [vis, c, annVal, ho, hl, e, rdW (m.arr64 IW) po] m with
    | none => rw [h1'] at hw; simp at hw
    | some q1 =>
    obtain ⟨r1, m1⟩ := q1
    rw [h1', bW_some] at hw
    obtain ⟨x1, a1, hrun1, hS1, hg1, hd1⟩ :=
      cg_ref hD.toDmProg5 hs0 hsA c annVal ho hl e (rdW (m.arr64 IW) po) hy k m a r1 m1
        ⟨hS, hc, hann, he, hpwlt, hdh, hbd⟩ h1'
    have hrun1' : (divModCertGuard fe (decI c) (decE annVal) hy (decE e) (decI (rdW (m.arr64 IW) po))).run a = .ok (x1, a1) := hrun1
    have hlpos : 0 < pl.toNat := Nat.pos_of_ne_zero (fun e' => hpl0 (UInt64.toNat_inj.mp (by simpa using e')))
    have hpo1 : (po + 1).toNat = po.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; omega
    have hpl1 : (pl - 1).toNat = pl.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
    by_cases z1 : r1.headD 0 = 0
    · rw [if_pos z1] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      have hx1 := decW0B_false hd1 z1
      refine ⟨false, a1, ?_, hS1, hg1, decW0B_of_false _⟩
      simp only [divModCertsGuardGo, StateT.run_bind, hrun1', exc_ok_bind', hx1,
        Bool.false_eq_true, if_false]
      rfl
    rw [if_neg z1] at hw
    have hx1 := decW0B_true hd1 z1
    cases h2 : callW p k "div_mod_certs_guard_go" [vis, c, annVal, so + 1, sl - 1, po + 1, pl - 1] m1 with
    | none => rw [h2] at hw; simp at hw
    | some q2 =>
    obtain ⟨r2, m2⟩ := q2
    rw [h2, bW_some] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    have hdr1 : decHL m1 (po + 1).toNat (pl - 1).toNat = some pfs := by
      rw [decHL_grow hg1 (by rw [hpo1, hpl1]; omega)]; exact hdrest
    obtain ⟨x2, a2, hrun2, hS2, hg2, hd2⟩ := ih pfs (so + 1) (sl - 1) (po + 1) (pl - 1) k m1 a1 r2 m2 hS1
      (hrest.grow hg1) hdr1 (by rw [hpo1, hpl1]; have := hg1.1; omega) h2
    refine ⟨x2, a2, ?_, hS2, hg1.trans hg2, hd2⟩
    simp only [divModCertsGuardGo, StateT.run_bind, hrun1', exc_ok_bind', hx1, if_true]
    exact hrun2

@[refines ConRon.Arena.divModCertsGuardGo]
theorem divModCertsGuardGo_refines (hD : DmProg6 p) (hs0 : SubstC0 p dn vis fe)
    (hsA : SubstCAll p dn vis fe) (c annVal : Word) (hc : H c) (hann : H annVal)
    (so sl po pl : Word) (ss : List (List EIdx × EIdx)) (proofs : List EIdx) :
    RefAM p "div_mod_certs_guard_go" [vis, c, annVal, so, sl, po, pl]
      (fun m s => StageR dn vis fe m s ∧ StmtL m so.toNat sl.toNat ss ∧
        decHL m po.toNat pl.toNat = some proofs ∧ po.toNat + pl.toNat ≤ iwTop m)
      (divModCertsGuardGo fe (decI c) (decE annVal) ss proofs) (KeepPost dn vis fe decW0B) :=
  CallRef.refAM (fun k m a res m' ⟨hS, hs, hd, hb⟩ hcall =>
    cggo_ref hD hs0 hsA c annVal hc hann ss proofs so sl po pl k m a res m' hS hs hd hb hcall)

/-! ## `div_mod_certs_guard` -/

def cgsW (p : Prog) (n : Nat) (m : Mem) (ps vs c annVal : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "div_mod_cert_stmts" [c] m) fun r1 m1 =>
  ntBW (callW p n "div_mod_cert_proofs" [ps, c] m1) fun r2 m2 =>
  ntBW (callW p n "div_mod_certs_guard_go" [vs, c, annVal, r1.headD 0, r1.tail.headD 0, r2.headD 0,
    r2.tail.headD 0] m2) fun r3 m3 => some ([r3.headD 0], m3)

set_option maxHeartbeats 1600000 in
theorem cgs_specW (p : Prog) (hp : p.lookup "div_mod_certs_guard" = some divModCertsGuardL)
    (n : Nat) (s₀ : St) (ps vs c annVal : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "div_mod_certs_guard" [ps, vs, c, annVal]
    ⦃fun r s' => LocEq s' s₀ ∧ cgsW p n s₀.mem ps vs c annVal = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, divModCertsGuardL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "div_mod_cert_stmts", callW_spec p n "div_mod_cert_proofs",
      callW_spec p n "div_mod_certs_guard_go"] <;>
    finish (gen := 20) [cgsW, ntBW]

theorem cgs_ref (hD : DmProg6 p) (hs0 : SubstC0 p dn vis fe) (hsA : SubstCAll p dn vis fe)
    (ps c annVal : Word) (ip : INatOpPinSet) :
    CallRef p "div_mod_certs_guard" [ps, vis, c, annVal]
      (fun m s => StageR dn vis fe m s ∧ H c ∧ H annVal ∧ PinSetR m ps ip)
      (divModCertsGuard ip fe (decI c) (decE annVal)) (KeepPost dn vis fe decW0B) := by
  refine CallRef.of_succ fun k m s rr mm ⟨hS, hc, hann, hP⟩ hcall => ?_
  have hw := callW_model (M := fun mq => cgsW p k mq ps vis c annVal)
    (cgs_specW p hD.lCertsGuard k · ps vis c annVal) hcall
  unfold cgsW at hw
  obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hg1, hd1⟩, hw⟩ :=
    (divModCertStmts_ref hD.toDmProg5.toDmProg2 c).bind_ ⟨hS, hc⟩ hw
  obtain ⟨r2, m2, x2, a2, hrun2, ⟨hS2, hg2, hd2⟩, hw⟩ :=
    (divModCertProofs_ref hD.toDmProg5.toDmProg2.toDmProg1 ps c ip).bind_ ⟨hS1, hc, PinSetR.grow hP hg1⟩ hw
  cases h3 : callW p k "div_mod_certs_guard_go" [vis, c, annVal, r1.headD 0, r1.tail.headD 0,
      r2.headD 0, r2.tail.headD 0] m2 with
  | none => rw [h3] at hw; simp at hw
  | some q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, bW_some] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  simp only [decStmtL, ntGetD0, ntGetD1] at hd1
  unfold decRL at hd2
  simp only [Nat.zero_add, ntGetD0, ntGetD1] at hd2
  obtain ⟨x3, a3, hrun3, hS3, hg3, hd3⟩ := cggo_ref hD hs0 hsA c annVal hc hann x1 x2
    (r1.headD 0) (r1.tail.headD 0) (r2.headD 0) (r2.tail.headD 0) k m2 a2 r3 m3 hS2
    (hd1.grow hg2) hd2.1 hd2.2 h3
  refine ⟨x3, a3, ?_, hS3, hg1.trans (hg2.trans hg3), hd3⟩
  simp only [divModCertsGuard, StateT.run_bind, hrun1, exc_ok_bind', hrun2]
  exact hrun3

@[refines ConRon.Arena.divModCertsGuard]
theorem divModCertsGuard_refines (hD : DmProg6 p) (hs0 : SubstC0 p dn vis fe)
    (hsA : SubstCAll p dn vis fe) (ps c annVal : Word) (ip : INatOpPinSet) :
    RefAM p "div_mod_certs_guard" [ps, vis, c, annVal]
      (fun m s => StageR dn vis fe m s ∧ H c ∧ H annVal ∧ PinSetR m ps ip)
      (divModCertsGuard ip fe (decI c) (decE annVal)) (KeepPost dn vis fe decW0B) :=
  (cgs_ref hD hs0 hsA ps c annVal ip).refAM

end guards

end L.Ind
