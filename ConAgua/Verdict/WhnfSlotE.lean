module

public import ConAgua.Arena.DefEqKnot
import ConAgua.Arena.CoreNatOp
import ConAgua.Arena.StrLitKeep
import ConAgua.Arena.WhnfSlotRefine
public import ConAgua.Arena.WhnfCoreLoop

@[expose] public section

/-!
# The knot's `whnf_core` and `whnf` slots' verdict claims (lane `verdicts-b`, helper `k2`)
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

/-- A continuation that passes errors on and fails nowhere else: its error is its argument's. -/
theorem err_of_k {β γ : Type} {k : Except Err β → Except Err γ}
    (hk : ∀ q e, k (.ok q) ≠ .error e) (hn : ∀ e, k (.error e) = .error e) {c : Except Err β}
    {er : Err} (h : k c = .error er) : c = .error er := by
  cases c with
  | error e => rw [hn] at h; cases h; rfl
  | ok q => exact absurd h (hk q er)

/-! ## `whnf_core`: the step's and the slot's claims from their refinements -/

section core
variable (p : Prog) (hp : WhnfCoreProg p) (hwc : WhnfCallees p) (hcc : CoreCallees p) (hnv : closedNV p L.Checker.nvFns = true) (hI : IotaRecAtE p)

include hp hwc hcc hnv hI in
/-- **`whnf_core_step`'s claim at every L fuel up to `n`** (`step_ref`'s error half). -/
theorem coreStepE_of (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) : CoreStepE p n :=
  fun j hj F hF hn s₀ a₀ dn vis fe MM eb mode cheap d h e hs hh he =>
    RefE.coreSpecE (whnfCoreStepE_spec p hp (j + 1) s₀ mode cheap vis d h e) hnv ⟨hkE.mono hj, hI⟩
      (step_ref p hp hwc hcc j (hk.mono hj) F hF hn s₀ a₀ dn vis fe MM eb mode cheap d h e hs hh he)

include hp hwc hcc hnv hI in
/-- **The knot's `whnfCore` slot's verdicts, one level up** (`core_ref`'s error half). -/
theorem whnfCoreSlot_stepE (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) :
    WhnfCoreSlotE p (n + 1) :=
  fun F s₀ a₀ dn vis fe MM eb mode cheap d e hF hn hs he =>
    RefE.coreSpecE (whnfCoreE_spec p hp (n + 1) s₀ mode cheap vis d e) hnv
      (coreStepE_of p hp hwc hcc hnv hI n hk hkE)
      (core_ref p hp hwc hcc n hk F s₀ a₀ dn vis fe MM eb mode cheap d e hF hn hs he)

end core

/-! ## The two slots' steps -/

/-- **The `whnf_core` and `whnf` slots' error halves, one level up** (the knot's `whnf` family's
part of `KnotStepE`), under the ok knot's program hypotheses and the error claim of the slot
bodies' callee `iota_rec_at`. -/
theorem whnfSlotsE_step {p : Prog} (hq : KnotAllProg p) (hnv : closedNV p L.Checker.nvFns = true)
    (hI : IotaRecAtE p) (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) :
    WhnfCoreSlotE p (n + 1) ∧ WhnfSlotE p (n + 1) :=
  ⟨whnfCoreSlot_stepE p hq.core (KnotAllProg.whnfC hq) (KnotAllProg.coreC hq) supKeep_of hnv hI n
      hk hkE,
    whnfSlot_stepE p hq.delta (KnotAllProg.instLP hq) (natOpResultOK_of_agree hq.delta.natAgree) hnv
      n hk hkE⟩

end L.Arena
