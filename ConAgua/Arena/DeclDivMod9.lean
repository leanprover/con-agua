import ConAgua.Arena.DeclDivMod8
import ConAgua.Arena.DeclReducePin
import ConAgua.L.ModelGen

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

/-- **`check_div_mod_pin` is its model `dmCpW`** (generated). -/
l_model cp_specW (p : Prog) (hp : p.lookup "check_div_mod_pin" = some checkDivModPinL)
  fns [hp ↦ dmCpW list]
  specs [callW_spec p n "div_mod_env_guard", callW_spec p n "env_find", callW_spec p n "check_div_mod_pin_loop"]
  grind [arena_grind] heartbeats 1600000 bind ntBW simp [ntBW, rdW_eq, getElem_rdW']

end pin

end L.Ind
