import ConAgua.Arena.PhaseBStep

/-!
# Phase B's loop over one group: `check_pending_go(j, j + 1, v)` (lane parmode)

The threads' entry 2 runs `check_b` over the range `[j, j + 1)`, i.e. `check_pending_go(j, j + 1, v)`:
`check_pending_next(j, j + 1, v)`, which is `check_pending(j, v)` and then
`check_pending_go(j + 1, j + 1, v)`, an immediate return. So it is `PhaseBStart.step`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

section one
variable (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
  (ds : Array IDeclaration) (p : Prog)

/-- `check_pending_go(j + 1, j + 1, v)` returns at once, memory and locals unchanged. -/
theorem checkPendingGo_empty (hP : PhaseBProg p) (n : Nat) (s₀ : St) (j k v : Word) (hjk : j = k) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_pending_go" [j, k, v]
    ⦃fun _ s' => s' = s₀; ⊤⦄ := by
  rw [invoke_eq _ hP.cpg]
  simp only [callFn, checkPendingGoL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [L.exec, L.step, evalE, evalC, evalArgs, setLoc, setLocs,
      (L.invoke_loc p (exec p n) "check_pending_next" · ·)] <;> simp_all [Cmp.eval, Locals.init]

/-- **One group through phase B's loop**: `check_pending_go(j, j + 1, v)` from `PhaseBStart`
(`j` below the count) refines `checkPending` on group `j` and ends in `PhaseBStart` at the twin's
state after it. -/
theorem PhaseBStart.one (hm : mode = .verified) (hP : PhaseBProg p) (n : Nat) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (j v : Word) (fe : IFEnv) (pend : Array PendingCheck)
    (hj : j.toNat < pend.size) (hj62 : j.toNat < 2 ^ 62)
    (h : PhaseBStart pins dn ds fe pend s₀.mem a₀ v) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_pending_go" [j, j + 1, v]
    ⦃fun _ s' => AM.ok (checkPending mode fe (pdAt pend j)) a₀ ∧
      PhaseBStart pins dn ds fe pend s'.mem (AM.st (checkPending mode fe (pdAt pend j)) a₀) v; ⊤⦄ := by
  have h1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  -- `check_pending_next(j, j + 1, v)` at any fuel
  have inner : ∀ (k : Nat), k ≤ 2 ^ 62 → ∀ s₁ : St, ∀ x y z : Word, x = j → y = j + 1 → z = v →
      PhaseBStart pins dn ds fe pend s₁.mem a₀ v →
      ⦃fun s => s = s₁⦄ invoke p (exec p k) "check_pending_next" [x, y, z]
      ⦃fun _ s' => AM.ok (checkPending mode fe (pdAt pend j)) a₀ ∧
        PhaseBStart pins dn ds fe pend s'.mem (AM.st (checkPending mode fe (pdAt pend j)) a₀) v; ⊤⦄ := by
    intro k hk s₁ x y z hx hy hz h
    subst hx hy hz
    rw [invoke_eq _ hP.cpx]
    simp only [callFn, checkPendingNextL]
    cases k with
    | zero => vcgen [exec] <;> grind
    | succ k =>
      vcgen [L.exec, L.step, evalE, evalC, evalArgs, setLoc, setLocs,
        (PhaseBStart.step mode pins dn ds p hm hP k (by omega) · a₀ · · fe pend · ·),
        (checkPendingGo_empty p hP k · · · · ·)]
      all_goals first
        | (simp_all [Locals.init, St.setLocs, St.setLoc, BinOp.eval]; done)
        | (grind [lang_grind]; done)
        | (trace_state; sorry)
  rw [invoke_eq _ hP.cpg]
  simp only [callFn, checkPendingGoL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [L.exec, L.step, evalE, evalC, evalArgs, setLoc, setLocs, (inner n (by omega) · · · · · · · ·)]
    all_goals first
      | (simp_all [Locals.init, St.setLocs, St.setLoc]; done)
      | (grind [lang_grind]; done)
      | (trace_state; sorry)

end one

end L.Arena
