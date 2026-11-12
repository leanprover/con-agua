module

public import ConAgua.Arena.DefEqStuckWith
public import ConAgua.Arena.IndRecRead
import ConAgua.Arena.DefEqLeaves2
import ConAgua.Arena.RefWalk
import ConAgua.Arena.WhnfCoreRefine
import ConRon.Bridge.Grind

@[expose] public section

/-!
# `struct_eta_cert_go` refines `structEtaCertWith`'s keys (lane `defeq`, helper `defeq-top`)

The twin's `let reserved ← …; match ← viewLsLen us' …; let slots ← towerSlotsAll …; if … then
…` (`setGoT`). Under `CoreS` the pin reads and `viewLsLen` have no effect (`setGoT_run`), so L's
pure calls (`er_slice_eq`, `reserved_contains`, `ls_node`) run first and the one effect,
`tower_slots_all`, is the twin's. The decoded records: `decCI_ctorLp` (a constructor's level
parameters), `decCI_indCaps` (an inductive's level parameters and η caps).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The twin -/

theorem reservedBasisNames_run {m : Mem} {a : AState} (hP : PinsFull m a.pins) :
    reservedBasisNames.run a = .ok (a.pins.reserved, a) := by
  simp only [reservedBasisNames, pinReserved, StateT.run_bind, StateT.run_get, pure_bind,
    L.Arena.pinsReady_true hP, ↓reduceIte]
  rfl

theorem reservedContainsT_run {m : Mem} {a : AState} (hP : PinsFull m a.pins) (n : NIdx) :
    (reservedContainsT n).run a = .ok (a.pins.reserved.contains n, a) := by
  simp only [reservedContainsT, StateT.run_bind, reservedBasisNames_run hP, except_ok_bind]
  rfl

section sgKarms
variable (m0 : Mem) (c q tn lpe r1 r2 uslen : Word) (r : List Word)

/-- The tests of `struct_eta_cert_go`, all passed. -/
def sgOK : Prop :=
  erRd m0 (q + 5) ≠ 0 ∧ erRd m0 (q + 6) = c ∧ r1 = 0 ∧ r2 = 0 ∧
    tn = erRd m0 (q + 7) ∧ uslen = erRd m0 (q + 3) ∧ lpe ≠ 0 ∧ r.headD 0 ≠ 0

end sgKarms

/-- A `reserved_contains` run: the twin unchanged, the verdict the pins' list's. -/
theorem reservedContains_callW {p : Prog} (hc : StuckCallees p) {n : Nat}
    {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word} {fe : IFEnv}
    {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) {x : Word} (hx : HW x)
    {r : List Word} (hcall : callW p n "reserved_contains_w" [x] m = some (r, m')) :
    CoreAfter dn m m' a vis fe M eb ∧ decBool r = a.pins.reserved.contains (decI x) := by
  have h := CoreSpec.of_callW (hc.reservedContains n ⟨m, Locals.init []⟩ a dn vis fe M eb x hS hx) hcall
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ (reservedContainsT_run hS.pins (decI x))
  refine ⟨hst ▸ h.after, ?_⟩
  rw [← h.res, hres]

section secgTests
variable (p : Prog) (n : Nat) (m0 : Mem) (mode vis d b us c T q us2 ao an to tn lpe r1 r2
  uslen : Word) (r : List Word) (m : Mem)

/-- `struct_eta_cert_go`'s tests, all passed: the tail. -/
theorem secgE_yes (h : sgOK m0 c q tn lpe r1 r2 uslen r) :
    secgE.k_tower_slots_all p n mode vis d b us c T us2 ao an to tn (erRd m0 (q + 5))
      (erRd m0 (q + 6)) (erRd m0 (q + 7)) (erRd m0 (q + 8))
      (erRd m0 (q + 3)) lpe r1 r2 uslen (.ok (r, m)) =
    secgE.k_struct_eta_cert_tail p (sectE p n m mode vis d b us T us2 ao an to tn
      (erRd m0 (q + 7)) (erRd m0 (q + 8))) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  simp only [secgE.k_tower_slots_all, h1, h2, h3, h4, h5, h6, h7, h8, ne_eq, not_true_eq_false,
    ↓reduceIte]

/-- `struct_eta_cert_go`'s tests, one failed: `false`. -/
theorem secgE_no (h : ¬ sgOK m0 c q tn lpe r1 r2 uslen r) :
    secgE.k_tower_slots_all p n mode vis d b us c T us2 ao an to tn (erRd m0 (q + 5))
      (erRd m0 (q + 6)) (erRd m0 (q + 7)) (erRd m0 (q + 8))
      (erRd m0 (q + 3)) lpe r1 r2 uslen (.ok (r, m)) = .ok ([0], m) := by
  unfold secgE.k_tower_slots_all
  by_cases h1 : erRd m0 (q + 5) = 0
  · simp only [h1, ↓reduceIte]
  by_cases h2 : erRd m0 (q + 6) ≠ c
  · simp only [h1, h2, ne_eq, not_false_eq_true, ↓reduceIte]
  by_cases h3 : r1 ≠ 0
  · simp only [h1, h2, h3, ne_eq, not_false_eq_true, ↓reduceIte]
  by_cases h4 : r2 ≠ 0
  · simp only [h1, h2, h3, h4, ne_eq, not_false_eq_true, ↓reduceIte]
  by_cases h5 : tn ≠ erRd m0 (q + 7)
  · simp only [h1, h2, h3, h4, h5, ne_eq, not_false_eq_true, ↓reduceIte]
  by_cases h6 : uslen ≠ erRd m0 (q + 3)
  · simp only [h1, h2, h3, h4, h5, h6, ne_eq, not_false_eq_true, ↓reduceIte]
  by_cases h7 : lpe = 0
  · simp only [h1, h2, h3, h4, h5, h6, h7, ↓reduceIte]
  by_cases h8 : r.headD 0 = 0
  · simp only [h1, h2, h3, h4, h5, h6, h7, h8, ↓reduceIte]
  exact absurd ⟨h1, by simpa using h2, by simpa using h3, by simpa using h4, by simpa using h5,
    by simpa using h6, h7, h8⟩ h

end secgTests

end L.Arena
