module

public import ConAgua.Rom.PinSets
public import ConAgua.Front.StateDR

@[expose] public section

/-!
# A job's relation (`LoopR`)

Split out of `Checker.lean` so that a job's callees (`Decl*.lean`) can state their specs over
`LoopR`: the checker state at the view `vis` of `fe` (`CheckR`, whose environment is the job's own
layer over the frozen stream index), the front's declaration records, the work pools, the pin
variants.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Front (DECL DLP DeclsF)

/-- For `AM.res` at the check's result types. -/
instance : Inhabited IFEnv := ⟨IFEnv.ofParts IEnv.empty {} {} {}⟩

/-- A front record that is not an inductive block is a one-constant record. -/
theorem declAt_of_F {D P : Array Word} {i : Nat} {d : IDeclaration} (h : L.Front.DeclAtF D P i d)
    (hne : ∀ b k, d ≠ .indDecl b k) : L.Front.DeclAt D P i d := by
  cases d with
  | indDecl b k => exact (hne b k rfl).elim
  | _ => exact h

/-- **What a job keeps**: the checker state at the view `vis` of `fe`, and the declaration
records. -/
structure LoopR (pins : List INatOpPinSet) (m : Mem) (a : AState) (vis : Word) (fe : IFEnv)
    (ds : Array IDeclaration) : Prop where
  check : CheckR m a vis fe
  decls : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds
  /-- The work pool and the record pool are in bounds (lane `induct`'s `IWOK`): the callees of
  the check run on the stage relation `StageR = CheckR ∧ IWOK`. -/
  iw : L.Ind.IWOK m
  /-- The pin variants the startup interned are `pins` (lane `romload`'s `PinSetsR`): the
  definition arm's `Nat.div`-family gate reads them. -/
  pinsets : L.Rom.PinSetsR m pins

/-- Declaration record `i` (a plain function, so that congruence sees through it). -/
def dsAt (ds : Array IDeclaration) (i : Word) : IDeclaration := ds.getD i.toNat default

end L.Arena
