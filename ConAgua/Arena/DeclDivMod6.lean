import ConAgua.Arena.DeclDivMod5
import ConAgua.Arena.DeclCanonEq
import ConAgua.Arena.DeclRomStubs

/-!
# The `Nat.div` family's pin gate, bottom up: the guards (lane `decls3`, `decls3-divmod`)

Part 6: `bool_ctor_typed`, `div_mod_pin_guard`, `div_mod_certs_guard_go`, `div_mod_certs_guard`.
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

structure DmProg6 (p : Prog) : Prop extends DmProg5 p where
  lBoolCtorTyped : p.lookup "bool_ctor_typed" = some boolCtorTypedL
  lDivModPinGuard : p.lookup "div_mod_pin_guard" = some divModPinGuardL
  lCertsGuardGo : p.lookup "div_mod_certs_guard_go" = some divModCertsGuardGoL
  lCertsGuard : p.lookup "div_mod_certs_guard" = some divModCertsGuardL

section guards
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

/-! ## `bool_ctor_typed` -/

def bctW (p : Prog) (n : Nat) (m : Mem) (v nm : Word) : Option (List Word × Mem) :=
  bW (callW p n "env_find" [nm, v] m) fun r1 m1 =>
  if r1.headD 0 = 0 then some ([0], m1) else
  bW (callW p n "ci_to_cv" [r1.tail.headD 0] m1) fun r2 m2 =>
  bW (callW p n "pin_at" [29] m2) fun r3 m3 =>
  bW (callW p n "const_e" [r3.headD 0] m3) fun r4 m4 =>
  some ([if rdW (m4.arr64 EREC) (r2.headD 0 + 3) = r4.headD 0 then 1 else 0], m4)

set_option maxHeartbeats 1600000 in
theorem bct_specW (p : Prog) (hp : p.lookup "bool_ctor_typed" = some boolCtorTypedL) (n : Nat)
    (s₀ : St) (v nm : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "bool_ctor_typed" [v, nm]
    ⦃fun r s' => LocEq s' s₀ ∧ bctW p n s₀.mem v nm = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, boolCtorTypedL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "env_find", callW_spec p n "ci_to_cv", callW_spec p n "pin_at",
      callW_spec p n "const_e"] <;>
    finish (gen := 30) (instances := 10000) [bctW, bW, rdW_eq]

theorem DmProg2.cvProg (hD : DmProg2 p) : NatCvProg p :=
  hD.toNatEqProg.toNatTyProg.toNatGuardProg.toNatLitProg.toNatCvProg

theorem bct_ref (hD : DmProg6 p) (nm : Word) :
    CallRef p "bool_ctor_typed" [vis, nm] (fun m a => StageR dn vis fe m a ∧ H nm)
      (boolCtorTyped fe (decI nm)) (KeepPost dn vis fe decW0B) := by
  refine CallRef.of_succ fun k m a r m' ⟨hS, hn⟩ hcall => ?_
  have hw := callW_model (M := fun mq => bctW p k mq vis nm)
    (bct_specW p hD.lBoolCtorTyped k · vis nm) hcall
  unfold bctW at hw
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

end guards

end L.Ind
