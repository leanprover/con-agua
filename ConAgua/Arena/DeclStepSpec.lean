module

public import ConAgua.Arena.DeclCvg
import ConAgua.Arena.DeclPins
public import ConAgua.Arena.DeclBase

@[expose] public section

/-!
# The specs of phase A's step and phase B's check (`install_step_go`, `check_value_group`)

The two callees of the declaration loop's skeleton (`Checker.lean`) that `DeclStep.lean`
translates, with the specs the skeleton is proved from.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Front (DECL DLP DeclsF)

/-! ## The loop's relation across a step's callee -/

/-- A grown pool keeps every record of the old one, inside the new pool's records. -/
theorem IWGrow.erecPExt {m m' : Mem} (h : L.Ind.IWGrow m m') : ArrExt (erecP m) (erecP m') := by
  sorry

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **The pending checks across a step's callee**: `PEND` and its count unchanged, the records
only extended. -/
theorem PendR.ext {m m' : Mem} (hP : m'.arr64 PEND = m.arr64 PEND)
    (hc : rdW (m'.arr64 CTL) 130 = rdW (m.arr64 CTL) 130) (hx : ArrExt (erecP m) (erecP m'))
    (h : PendR m pend) : PendR m' pend := by
  sorry
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **The loop's relation after a step's callee**: the stage relation after it (at any view and
environment), a frame of the step's write set (`stepA`, `stepC`: nothing of `PEND`, `DECL`,
`DLP`, `CTL[130]`), and the records only extended. -/
theorem step_keeps : (PEND : TieredArray) ∉ stepA ∧ (DECL : TieredArray) ∉ stepA ∧
    (DLP : TieredArray) ∉ stepA ∧ (130 : Word) ∉ stepC := by
  decide +kernel
-/

/-- The step's write set misses the pin variant list's header. -/
theorem step_pins : (150 : Word) ∉ stepC ∧ (151 : Word) ∉ stepC := by decide +kernel

/-- The step's write set misses the promotion memo (arrays 146‥149, `CTL` 140‥147). -/
theorem step_pmemo : (∀ b ∈ stepA, b.arr < 146 ∨ 149 < b.arr) ∧
    (∀ x ∈ stepC, x.toNat < 140 ∨ 147 < x.toNat) := by
  sorry

theorem LoopR.of_step {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState} {vis vis' : Word} {fe fe' : IFEnv}
    {ds : Array IDeclaration} (h : LoopR pins m a vis fe ds)
    (hS : L.Ind.StageR vis' fe' m' a') (hf : MemFrame stepA stepC m m')
    (hx : ArrExt (erecP m) (erecP m')) : LoopR pins m' a' vis' fe' ds := by
  sorry

end L.Arena
