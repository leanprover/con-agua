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
theorem IWGrow.erecPExt {m m' : Mem} (h : L.Ind.IWGrow m m') : ArrExt (erecP m) (erecP m') :=
  h.ext

/-- The step's write set misses the front's records. -/
theorem step_keeps : (DECL : TieredArray) ∉ stepA ∧ (DLP : TieredArray) ∉ stepA := by
  decide +kernel

/-- The step's write set misses the pin variant list's header. -/
theorem step_pins : (150 : Word) ∉ stepC ∧ (151 : Word) ∉ stepC := by decide +kernel

/-- **The job relation after a step's callee**: the stage relation after it (at any view and
environment), a frame of the step's write set (`stepA`, `stepC`: nothing of `DECL`, `DLP`, the
pin variant list's header), and the records only extended. -/
theorem LoopR.of_step {pins : List INatOpPinSet} {m m' : Mem} {a a' : AState} {vis vis' : Word}
    {fe fe' : IFEnv} {ds : Array IDeclaration} (h : LoopR pins m a vis fe ds)
    (hS : L.Ind.StageR vis' fe' m' a') (hf : MemFrame stepA stepC m m')
    (hx : ArrExt (erecP m) (erecP m')) : LoopR pins m' a' vis' fe' ds := by
  have hD1 : m'.arr64 DECL = m.arr64 DECL := hf.arr _ step_keeps.1 (by decide)
  have hD2 : m'.arr64 DLP = m.arr64 DLP := hf.arr _ step_keeps.2 (by decide)
  exact ⟨hS.check, by rw [hD1, hD2]; exact h.decls, hS.iw,
    PinSetsR.grow h.pinsets (RecGrow.of_ext h.iw hx) (hf.ctl _ step_pins.1) (hf.ctl _ step_pins.2)⟩

end L.Arena
