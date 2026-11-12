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

/-- **`structEtaCertWith` once both heads and spines are known**, copied. -/
def setGoT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (b : EIdx) (c : NIdx) (us : LsIdx)
    (cvc : IConstantVal) (T : NIdx) (us' : LsIdx) (cvT : IConstantVal) (caps : IIndCaps)
    (aargs targs : List EIdx) : AM Bool := do
  let reserved ← reservedBasisNames
  match ← viewLsLen us' with
  | none => failDanglingLs
  | some uslen =>
  let slots ← (pure (towerSlotsAll fe T caps.etaFields) : AM Bool)
  if caps.eta = true ∧ caps.etaCtor = c ∧
      reserved.contains T = false ∧ reserved.contains c = false ∧
      targs.length = caps.etaParams ∧
      uslen = cvT.levelParams.length ∧
      cvc.levelParams = cvT.levelParams ∧ slots = true then
    setTailT r fe depth b us T us' caps.etaParams caps.etaFields aargs targs
  else pure false

theorem reservedBasisNames_run {m : Mem} {a : AState} (hP : PinsFull m a.pins) :
    reservedBasisNames.run a = .ok (a.pins.reserved, a) := by
  simp only [reservedBasisNames, pinReserved, StateT.run_bind, StateT.run_get, pure_bind,
    L.Arena.pinsReady_true hP, ↓reduceIte]
  rfl

theorem reservedContainsT_run {m : Mem} {a : AState} (hP : PinsFull m a.pins) (n : NIdx) :
    (reservedContainsT n).run a = .ok (a.pins.reserved.contains n, a) := by
  simp only [reservedContainsT, StateT.run_bind, reservedBasisNames_run hP, except_ok_bind]
  rfl

/-- `setGoT`'s test and tail, at the reserved names `rs`, the level list's length and `slots`. -/
def setGoK (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (b : EIdx) (c : NIdx) (us : LsIdx)
    (cvc : IConstantVal) (T : NIdx) (us' : LsIdx) (cvT : IConstantVal) (caps : IIndCaps)
    (aargs targs : List EIdx) (rs : List NIdx) (uslen : Nat) (slots : Bool) : AM Bool :=
  if caps.eta = true ∧ caps.etaCtor = c ∧
      rs.contains T = false ∧ rs.contains c = false ∧
      targs.length = caps.etaParams ∧
      uslen = cvT.levelParams.length ∧
      cvc.levelParams = cvT.levelParams ∧ slots = true then
    setTailT r fe depth b us T us' caps.etaParams caps.etaFields aargs targs
  else pure false

/-- **`setGoT` from `towerSlotsAll` on**, under the pins and a level list that has a length. -/
theorem setGoT_run (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (b : EIdx) (c : NIdx) (us : LsIdx)
    (cvc : IConstantVal) (T : NIdx) (us' : LsIdx) (cvT : IConstantVal) (caps : IIndCaps)
    (aargs targs : List EIdx) {m : Mem} {a : AState} (hP : PinsFull m a.pins) (uslen : Nat)
    (hv : a.store.lss.viewLen us' = some uslen) :
    (setGoT r fe depth b c us cvc T us' cvT caps aargs targs).run a =
      ((pure (towerSlotsAll fe T caps.etaFields) : AM Bool) >>=
        setGoK r fe depth b c us cvc T us' cvT caps aargs targs a.pins.reserved uslen).run a := by
  simp only [setGoT, StateT.run_bind, reservedBasisNames_run hP, except_ok_bind, viewLsLen_run, hv]
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

/-- A `const` node's level list at a state, read back after `towerSlotsAll`. -/
theorem constLs_after_tower {fe : IFEnv} {T : NIdx} {nF : Nat} {a : AState} {x : EIdx} {c : NIdx}
    {us : LsIdx} (hv : a.store.view x = some (.const c us)) :
    (AM.st (pure (towerSlotsAll fe T nF) : AM Bool) a).store.view x = some (.const c us) := hv

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

/-- **`struct_eta_cert_go` refines `setGoT`, both outcomes** (the projections' slice left on the
stack): the errors are `struct_eta_cert_tail`'s. -/
@[refines_part ConRon.Arena.structEtaCertWith "the keys, then the tail (setGoT)"]
theorem secg_ref (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d b us c pc T q us2 ao an to tn : Word) (aargs targs : Array EIdx)
    (cvc : IConstantVal) (np nf : Nat) (cvT : IConstantVal) (caps : IIndCaps) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hb : HW b) (hus : HW us)
    (hcw : HW c) (hT : HW T) (hus2 : HW us2)
    (hvus : ∃ x c', a₀.store.view x = some (.const c' (decI us)))
    (hvus2 : ∃ x c', a₀.store.view x = some (.const c' (decI us2)))
    (hcvc : decCI (erecP s₀.mem) pc.toNat = some (.ctorInfo cvc np nf))
    (hcvT : decCI (erecP s₀.mem) q.toNat = some (.indInfo cvT caps))
    (ha : SpineR s₀.mem ao an aargs) (ht : SpineR s₀.mem to tn targs)
    (hat : ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat)
    (htt : to.toNat + tn.toNat ≤ (spTop s₀.mem).toNat) :
    RefE (SetG p n) (secgE p (n + 1) s₀.mem mode vis d b us c pc T q us2 ao an to tn)
      (setGoT (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE b) (decI c) (decI us) cvc (decI T)
        (decI us2) cvT caps aargs.toList targs.toList) a₀
      (GrowPost decBool dn s₀.mem vis fe M eb ResH) := by
  sorry

end L.Arena
