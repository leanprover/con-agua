import ConAgua.Arena.DeclDivMod8
import ConAgua.Arena.DeclReducePin

/-!
# The `Nat.div` family's pin gate, bottom up: the variant loop and the gate (lane `decls3`, `decls3-divmod`)

Part 9: `check_div_mod_pin_loop`, `check_div_mod_pin`.

**D4** (docs/deviations.md): the L loop aborts on any error inside an attempt where the twin's
`orElseAttempt` restores the state and tries the next variant. Every callee's refinement here
returns only for runs in which the twin's counterpart succeeds, so a *returning* L loop is a
successful twin run with no recovery: the theorem is exact on the runs where no attempt errors,
and says nothing where L aborts (`refines_part`).
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

/-- **The variant slice**: `IW[o ‥ o + l]` holds pointers to the 24-word records of the variants
`ips`, in order. -/
def PinsIW (m : Mem) (o l : Nat) (ips : List INatOpPinSet) : Prop :=
  o + l ≤ iwTop m ∧ l = ips.length ∧ ∀ (j : Nat) (hj : j < ips.length), ∃ ps : Word,
    (iwA m)[o + j]? = some ps ∧ PinSetR m ps ips[j]

theorem PinsIW.grow {m m' : Mem} {o l : Nat} {ips : List INatOpPinSet} (h : PinsIW m o l ips)
    (hg : IWGrow m m') : PinsIW m' o l ips := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Nat.le_trans h1 hg.1, h2, fun j hj => ?_⟩
  obtain ⟨ps, hp, hP⟩ := h3 j hj
  refine ⟨ps, ?_, PinSetR.grow hP hg⟩
  simp only [iwA] at hp ⊢; rw [hg.2.2.1 _ (by omega)]; exact hp

structure DmProg9 (p : Prog) : Prop extends DmProg8 p

section loop
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

def loopW (p : Prog) (n : Nat) (m : Mem) (vs c value po pl : Word) : Option (List Word × Mem) :=
  if pl = 0 then none else
  ntBW (callW p n "div_mod_pin_guard" [rdW (m.arr64 IW) po, vs, c] m) fun r1 m1 =>
  ntBW (callW p n "div_mod_certs_guard" [rdW (m.arr64 IW) po, vs, c, value] m1) fun r2 m2 =>
  if r1.headD 0 ≠ 0 ∧ r2.headD 0 ≠ 0 then
    ntBW (callW p n "check_div_mod_pin_at" [vs, c, value, rdW (m.arr64 IW) po] m2) fun r3 m3 =>
    if r3.headD 0 ≠ 0 then some ([0], m3) else
    ntBW (callW p n "check_div_mod_pin_loop" [vs, c, value, po + 1, pl - 1] m3) fun r4 m4 =>
      some ([r4.headD 0], m4)
  else
    ntBW (callW p n "check_div_mod_pin_loop" [vs, c, value, po + 1, pl - 1] m2) fun r4 m4 =>
      some ([r4.headD 0], m4)

set_option maxHeartbeats 3200000 in
theorem loop_specW (p : Prog) (hp : p.lookup "check_div_mod_pin_loop" = some checkDivModPinLoopL)
    (n : Nat) (s₀ : St) (vs c value po pl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check_div_mod_pin_loop" [vs, c, value, po, pl]
    ⦃fun r s' => LocEq s' s₀ ∧ loopW p n s₀.mem vs c value po pl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkDivModPinLoopL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "div_mod_pin_guard", callW_spec p n "div_mod_certs_guard",
      callW_spec p n "check_div_mod_pin_at", callW_spec p n "check_div_mod_pin_loop"] <;>
    finish (gen := 30) (instances := 10000) [loopW, ntBW, rdW_eq]

/-- The twin's attempt step, on a successful attempt. -/
theorem orElse_run_ok {att : AM Bool} {b : Bool} {a a' : AState} (h : att.run a = Except.ok (b, a')) :
    (orElseAttempt att).run a = Except.ok (orElseStepOf (Except.ok b), a') := by
  have : att a = Except.ok (b, a') := h
  show orElseAttempt att a = _
  simp only [orElseAttempt, this]

theorem loop_ref (hD : DmProg9 p) (hs0 : SubstC0 p dn vis fe) (hsA : SubstCAll p dn vis fe)
    (c value : Word) (hc : H c) (hval : H value) :
    ∀ (ips : List INatOpPinSet) (po pl : Word) (tried : List String) (k : Nat) (m : Mem) (a : AState)
      (res : List Word) (m' : Mem), StageR dn vis fe m a → PinsIW m po.toNat pl.toNat ips →
      callW p k "check_div_mod_pin_loop" [vis, c, value, po, pl] m = some (res, m') →
      ∃ x a', (checkDivModPinLoop V fe (decI c) (decE value) ips tried).run a = .ok (x, a') ∧
        KeepPost dn vis fe decUnit m m' a' res x := by
  intro ips
  induction ips with
  | nil =>
    intro po pl tried k m a res m' hS hI hc'
    have hpl : pl = 0 := UInt64.toNat_inj.mp (by have := hI.2.1; simpa using this)
    cases k with
    | zero => rw [callW_zero] at hc'; cases hc'
    | succ k =>
    have hw := callW_model (M := fun mq => loopW p k mq vis c value po pl)
      (loop_specW p hD.lCheckDivModPinLoop k · vis c value po pl) hc'
    simp [loopW, hpl] at hw
  | cons ip rest ih =>
    intro po pl tried k m a res m' hS hI hc'
    cases k with
    | zero => rw [callW_zero] at hc'; cases hc'
    | succ k =>
    have hw := callW_model (M := fun mq => loopW p k mq vis c value po pl)
      (loop_specW p hD.lCheckDivModPinLoop k · vis c value po pl) hc'
    unfold loopW at hw
    have hsz := hS.2.2.2.1
    have hI1 := hS.2.1
    obtain ⟨hb, hl, hj⟩ := hI
    have hpl0 : pl ≠ 0 := fun e => by rw [e] at hl; simp at hl
    rw [if_neg hpl0] at hw
    obtain ⟨ps, hps, hP⟩ := hj 0 (by simp)
    have hpsw : rdW (m.arr64 IW) po = ps := rdW_iw_of (by simpa using hps) rfl
    have hlpos : 0 < pl.toNat := Nat.pos_of_ne_zero (fun e' => hpl0 (UInt64.toNat_inj.mp (by simpa using e')))
    have hpo1 : (po + 1).toNat = po.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; omega
    have hpl1 : (pl - 1).toNat = pl.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
    have hrestI : ∀ m2, IWGrow m m2 → PinsIW m2 (po + 1).toNat (pl - 1).toNat rest := by
      intro m2 hg
      have h0 : PinsIW m (po + 1).toNat (pl - 1).toNat rest := by
        rw [hpo1, hpl1]
        refine ⟨by simp at hl; omega, by simp at hl; omega, fun j hj' => ?_⟩
        obtain ⟨ps2, hp2, hP2⟩ := hj (j + 1) (by simpa using hj')
        exact ⟨ps2, by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hp2, by simpa using hP2⟩
      exact h0.grow hg
    rw [hpsw] at hw
    obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hg1, hd1⟩, hw⟩ :=
      (pg_ref hD.toDmProg8.toDmProg7.toDmProg6 ps c ip).bind_ ⟨hS, hc, hP⟩ hw
    obtain ⟨r2, m2, x2, a2, hrun2, ⟨hS2, hg2, hd2⟩, hw⟩ :=
      (cgs_ref hD.toDmProg8.toDmProg7.toDmProg6 hs0 hsA ps c value ip).bind_
        ⟨hS1, hc, hval, PinSetR.grow hP hg1⟩ hw
    have hG2 : IWGrow m m2 := hg1.trans hg2
    have hrun1' : (divModPinGuard ip fe (decI c)).run a = .ok (x1, a1) := hrun1
    have hrun2' : (divModCertsGuard ip fe (decI c) (decE value)).run a1 = .ok (x2, a2) := hrun2
    by_cases hg : r1.headD 0 ≠ 0 ∧ r2.headD 0 ≠ 0
    · rw [if_pos hg] at hw
      have hx1 := decW0B_true hd1 hg.1
      have hx2 := decW0B_true hd2 hg.2
      obtain ⟨r3, m3, x3, a3, hrun3, ⟨hS3, hg3, hd3⟩, hw⟩ :=
        (cpa_ref hD.toDmProg8 hs0 hsA c value ps ip).bind_
          ⟨hS2, hc, hval, PinSetR.grow hP hG2⟩ hw
      have hrun3' := orElse_run_ok hrun3
      have hG3 : IWGrow m m3 := hG2.trans hg3
      by_cases z3 : r3.headD 0 ≠ 0
      · rw [if_pos z3] at hw
        simp only [Option.some.injEq, Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        have hx3 := decW0B_true hd3 z3
        refine ⟨(), a3, ?_, hS3, hG3, trivial⟩
        simp only [checkDivModPinLoop, StateT.run_bind, hrun1', exc_ok_bind', hrun2', hx1, hx2,
          Bool.and_self, if_true, hrun3', hx3, orElseStepOf]
        rfl
      · rw [if_neg z3] at hw
        have z3' : r3.headD 0 = 0 := by simpa using z3
        have hx3 := decW0B_false hd3 z3'
        cases h4 : callW p k "check_div_mod_pin_loop" [vis, c, value, po + 1, pl - 1] m3 with
        | none => rw [h4] at hw; simp at hw
        | some q4 =>
        obtain ⟨r4, m4⟩ := q4
        rw [h4, bW_some] at hw
        simp only [Option.some.injEq, Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        obtain ⟨x4, a4, hrun4, hS4, hg4, hd4⟩ := ih (po + 1) (pl - 1) (tried ++ [divModAttemptReason ip none]) k m3 a3 r4 m4 hS3
          (hrestI m3 hG3) h4
        refine ⟨x4, a4, ?_, hS4, hG3.trans hg4, hd4⟩
        simp only [checkDivModPinLoop, StateT.run_bind, hrun1', exc_ok_bind', hrun2', hx1, hx2,
          Bool.and_self, if_true, hrun3', hx3, orElseStepOf]
        exact hrun4
    · rw [if_neg hg] at hw
      cases h4 : callW p k "check_div_mod_pin_loop" [vis, c, value, po + 1, pl - 1] m2 with
      | none => rw [h4] at hw; simp at hw
      | some q4 =>
      obtain ⟨r4, m4⟩ := q4
      rw [h4, bW_some] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      obtain ⟨x4, a4, hrun4, hS4, hg4, hd4⟩ := ih (po + 1) (pl - 1)
        (tried ++ [s!"{ip.toolchain}: pin or certificate ground constants absent"]) k m2 a2 r4 m4 hS2
        (hrestI m2 hG2) h4
      refine ⟨x4, a4, ?_, hS4, hG2.trans hg4, hd4⟩
      have hx : (x1 && x2) = false := by
        by_cases e1 : r1.headD 0 = 0
        · rw [decW0B_false hd1 e1]; rfl
        · have e2 : r2.headD 0 = 0 := Classical.byContradiction fun e2 => hg ⟨e1, e2⟩
          rw [decW0B_false hd2 e2]; simp
      simp only [checkDivModPinLoop, StateT.run_bind, hrun1', exc_ok_bind', hrun2', hx,
        Bool.false_eq_true, if_false]
      exact hrun4

@[refines_part ConRon.Arena.checkDivModPinLoop "an attempt's error aborts (D4)"]
theorem checkDivModPinLoop_refines (hD : DmProg9 p) (hs0 : SubstC0 p dn vis fe)
    (hsA : SubstCAll p dn vis fe) (c value : Word) (hc : H c) (hval : H value)
    (ips : List INatOpPinSet) (po pl : Word) (tried : List String) :
    RefAM p "check_div_mod_pin_loop" [vis, c, value, po, pl]
      (fun m s => StageR dn vis fe m s ∧ PinsIW m po.toNat pl.toNat ips)
      (checkDivModPinLoop V fe (decI c) (decE value) ips tried) (KeepPost dn vis fe decUnit) :=
  CallRef.refAM (fun k m a res m' ⟨hS, hI⟩ hcall =>
    loop_ref hD hs0 hsA c value hc hval ips po pl tried k m a res m' hS hI hcall)

end loop

end L.Ind

namespace L.Ind
open L.Arena

theorem decCI_defn_value {a : Array Word} {dn : NIdx → Option ConLeche.Name} {p : Nat}
    {cv : IConstantVal} {v : EIdx} {hint : ConLeche.ReducibilityHint}
    (h : decCI a dn p = some (.defnInfo cv v hint)) :
    a[p]? = some 1 ∧ ∃ w, a[p + 5]? = some w ∧ w.toNat < 2 ^ 32 ∧ v = decI w := by
  obtain ⟨hk, -⟩ : a[p]? = some 1 ∧ True := by
    rcases decCI_defn_cases h with ⟨cv', v', hint', he, hk, hcv⟩ | ⟨w, hw, hne, hnd⟩
    · exact ⟨hk, trivial⟩
    · exact absurd rfl (hnd cv v hint)
  refine ⟨hk, ?_⟩
  unfold decCI at h
  have hn : nat? a p = some 1 := by simp [nat?, hk]
  rw [hn] at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨a1, ha1, h⟩ := h
  cases ha1
  simp only [pure, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨cv2, -, v2, hv2, h3, -, he2⟩ := h
  have hv : v2 = v := by cases he2; rfl
  subst hv
  cases hq : a[p + 5]? with
  | none => simp [hd?, hq] at hv2
  | some w =>
    by_cases hlt : w.toNat < 2 ^ 32
    · have e : (hd? a (p + 5) : Option EIdx) = some (decI w) := by simp [hd?, hq, hlt]
      rw [e] at hv2
      exact ⟨w, rfl, hlt, (Option.some.inj hv2).symm⟩
    · simp [hd?, hq, hlt] at hv2

local notation "V" => ConLeche.CheckMode.verified

section pin
variable {dn : NIdx → Option ConLeche.Name} {p : Prog}

def dmCpW (p : Prog) (n : Nat) (m : Mem) (po pl vs vs2 c : Word) : Option (List Word × Mem) :=
  ntBW (callW p n "div_mod_env_guard" [vs2, c] m) fun r1 m1 =>
  if r1.headD 0 = 0 then none else
  ntBW (callW p n "env_find" [c, vs2] m1) fun r2 m2 =>
  if r2.headD 0 = 0 then none else
  if rdW (m2.arr64 EREC) (r2.tail.headD 0) ≠ 1 then none else
  ntBW (callW p n "check_div_mod_pin_loop" [vs, c, rdW (m2.arr64 EREC) (r2.tail.headD 0 + 5), po, pl] m2)
    fun r3 m3 => some ([0], m3)

set_option maxHeartbeats 1600000 in
theorem cp_specW (p : Prog) (hp : p.lookup "check_div_mod_pin" = some checkDivModPinL) (n : Nat)
    (s₀ : St) (po pl vs vs2 c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check_div_mod_pin" [po, pl, vs, vs2, c]
    ⦃fun r s' => LocEq s' s₀ ∧ dmCpW p n s₀.mem po pl vs vs2 c = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkDivModPinL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "div_mod_env_guard", callW_spec p n "env_find",
      callW_spec p n "check_div_mod_pin_loop"] <;>
    finish (gen := 30) (instances := 10000) [dmCpW, ntBW, rdW_eq]

theorem cp_ref (hD : DmProg9 p) (hdn : DnInj dn) {vis vis2 : Word} {fe2 : IFEnv}
    (hs0 : SubstC0 p dn vis (fe2.restrictTo vis.toNat))
    (hsA : SubstCAll p dn vis (fe2.restrictTo vis.toNat))
    (po pl c : Word) (ips : List INatOpPinSet) :
    CallRef p "check_div_mod_pin" [po, pl, vis, vis2, c]
      (fun m s => StageR dn vis2 fe2 m s ∧ H c ∧ PinsIW m po.toNat pl.toNat ips)
      (checkDivModPin V ips (fe2.restrictTo vis.toNat) fe2 (decI c))
      (KeepPost dn vis2 fe2 decUnit) := by
  refine CallRef.of_succ fun k m s rr mm ⟨hS, hc, hI⟩ hcall => ?_
  have hw := callW_model (M := fun mq => dmCpW p k mq po pl vis vis2 c)
    (cp_specW p hD.lCheckDivModPin k · po pl vis vis2 c) hcall
  unfold dmCpW at hw
  have hD8 := hD.toDmProg8
  have hD7 := hD8.toDmProg7
  obtain ⟨r1, m1, x1, a1, hrun1, ⟨hS1, hg1, hd1⟩, hw⟩ :=
    (eg_ref hD7 hdn c).bind_ ⟨hS, hc⟩ hw
  by_cases z1 : r1.headD 0 = 0
  · rw [if_pos z1] at hw; cases hw
  rw [if_neg z1] at hw
  have hx1 := decW0B_true hd1 z1
  have hrun1' : (divModEnvGuard fe2 (decI c)).run s = .ok (true, a1) := by rw [← hx1]; exact hrun1
  cases h2 : callW p k "env_find" [c, vis2] m1 with
  | none => rw [h2] at hw; simp at hw
  | some q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, bW_some] at hw
  obtain ⟨hm2, hfd⟩ := envFind_call hD7.toDmProg6.toDmProg5.toMasterProg c hc hS1.1.env h2
  subst hm2
  cases hf : fe2.find? (decI c) with
  | none =>
    rw [hf] at hfd
    rw [if_pos (show r2.headD 0 = 0 from hfd)] at hw; cases hw
  | some ci =>
  rw [hf] at hfd
  obtain ⟨hr2, hci⟩ := hfd
  rw [if_neg (by rw [hr2]; decide)] at hw
  have hsz := hS1.2.2.2.2.1
  obtain ⟨cv, v, hint, rfl, hk, hcv⟩ : ∃ cv v hint, ci = .defnInfo cv v hint ∧
      (erecP m2)[(r2.tail.headD 0).toNat]? = some 1 ∧ decCV (erecP m2) ((r2.tail.headD 0).toNat + 1) = some cv := by
    rcases decCI_defn_cases hci with h | ⟨w, hw', hne, hnd⟩
    · exact h
    · exfalso
      have := rdW_erec_of hsz hw'
      rw [if_pos (by rw [this]; exact hne)] at hw; cases hw
  obtain ⟨-, wv, hwv, hwlt, hvw⟩ := decCI_defn_value hci
  have hk1 : rdW (m2.arr64 EREC) (r2.tail.headD 0) = 1 := rdW_erec_of hsz hk
  rw [if_neg (by rw [hk1]; simp)] at hw
  have hq5 : (r2.tail.headD 0 + 5).toNat = (r2.tail.headD 0).toNat + 5 := by
    have h1 : (r2.tail.headD 0).toNat + 5 < (erecP m2).size := by
      have := (Array.getElem?_eq_some_iff.mp hwv).1; omega
    have h2 : (erecP m2).size ≤ erTop m2 := erecP_size_le' m2
    have h3 : erTop m2 < 2 ^ 64 := (rdW (m2.arr64 CTL) 129).toNat_lt
    have h5 : (5 : Word).toNat = 5 := rfl
    rw [UInt64.toNat_add, h5]; exact Nat.mod_eq_of_lt (by omega)
  have hval : rdW (m2.arr64 EREC) (r2.tail.headD 0 + 5) = wv := by
    have : (erecP m2)[(r2.tail.headD 0 + 5).toNat]? = some wv := by rw [hq5]; exact hwv
    exact rdW_erec_of hsz this
  rw [hval] at hw
  cases h3 : callW p k "check_div_mod_pin_loop" [vis, c, wv, po, pl] m2 with
  | none => rw [h3] at hw; simp at hw
  | some q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, bW_some] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  have hS1' := StageR.restrict hS1 vis
  obtain ⟨x3, a3, hrun3, hS3, hg3, -⟩ := loop_ref hD hs0 hsA c wv hc hwlt ips po pl [] k m2 a1 r3 m3 hS1'
    (hI.grow hg1) h3
  have hS3' := StageR.restrict hS3 vis2
  rw [IFEnv.restrictTo_restrictTo, ← hS.1.env.vis, IFEnv.restrictTo_self] at hS3'
  refine ⟨(), a3, ?_, hS3', hg1.trans hg3, trivial⟩
  simp only [checkDivModPin, StateT.run_bind, hrun1', exc_ok_bind', if_true, hf]
  rw [hvw]
  exact hrun3

@[refines_part ConRon.Arena.checkDivModPin "the loop's attempt error aborts (D4)"]
theorem checkDivModPin_refines (hD : DmProg9 p) (hdn : DnInj dn) {vis vis2 : Word} {fe2 : IFEnv}
    (hs0 : SubstC0 p dn vis (fe2.restrictTo vis.toNat))
    (hsA : SubstCAll p dn vis (fe2.restrictTo vis.toNat))
    (po pl c : Word) (ips : List INatOpPinSet) :
    RefAM p "check_div_mod_pin" [po, pl, vis, vis2, c]
      (fun m s => StageR dn vis2 fe2 m s ∧ H c ∧ PinsIW m po.toNat pl.toNat ips)
      (checkDivModPin V ips (fe2.restrictTo vis.toNat) fe2 (decI c))
      (KeepPost dn vis2 fe2 decUnit) :=
  (cp_ref hD hdn hs0 hsA po pl c ips).refAM

end pin

end L.Ind
