import ConAgua.Arena.DeclDivMod8

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
  bW (callW p n "div_mod_pin_guard" [rdW (m.arr64 IW) po, vs, c] m) fun r1 m1 =>
  bW (callW p n "div_mod_certs_guard" [rdW (m.arr64 IW) po, vs, c, value] m1) fun r2 m2 =>
  if r1.headD 0 ≠ 0 ∧ r2.headD 0 ≠ 0 then
    bW (callW p n "check_div_mod_pin_at" [vs, c, value, rdW (m.arr64 IW) po] m2) fun r3 m3 =>
    if r3.headD 0 ≠ 0 then some ([0], m3) else
    bW (callW p n "check_div_mod_pin_loop" [vs, c, value, po + 1, pl - 1] m3) fun r4 m4 =>
      some ([r4.headD 0], m4)
  else
    bW (callW p n "check_div_mod_pin_loop" [vs, c, value, po + 1, pl - 1] m2) fun r4 m4 =>
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
    finish (gen := 30) (instances := 10000) [loopW, bW, rdW_eq]

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

end loop

end L.Ind
