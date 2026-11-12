module

public import ConAgua.Arena.BasisBlockC
public import ConAgua.Arena.IndDeclConstsRef
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
import ConAgua.Arena.IlpRd
import ConRon.Bridge.Checker.Basis
import all ConAgua.Arena.DeclArms

@[expose] public section

/-!
# The pinned block's comparison's contract (`PinListOkRef`)

`pin_list_ok(io, il, po, pl)` (`BasisL.lean`) refines `pinListOk` (its proof: `PinListRef.lean`),
what the reserved names' check `basis_names_ok` reads at a block under a pinned block's names.
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **The pinned block's comparison's contract**: `pin_list_ok(io, il, po, pl)` on two `IW`
slices of constant records (the block's copy, the pin) refines `pinListOk block pins` (con-ron's
`pinListOk_run`: an `RStep`). Its proof belongs with `BasisL.lean`'s entry points (`basisRefs_of`). -/
def PinListOkRef (p : Prog) : Prop := ∀ (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (io il po pl : Word) (block pins : List IConstantInfo),
  L.Rom.RomRef p "pin_list_ok" [io, il, po, pl]
    (fun m a => StageT dn vis fe m a ∧ ConRon.Bridge.StateOK a ∧ ConRon.Bridge.ReadOK a ∧
      DecB (basisDec dn io.toNat il.toNat) m block ∧ DecB (basisDec dn po.toNat pl.toNat) m pins ∧
      (∃ B, Frontend.denoteCIList a.store block = some B) ∧
      (∃ P, Frontend.denoteCIList a.store pins = some P))
    (ConRon.Arena.pinListOk block pins) (KeepPostT dn vis fe (fun _ r b => (r.headD 0 ≠ 0 ↔ b = true)))

/-- An unconditional refinement under any `G`. -/
theorem RefE.ofTrue {α β : Type} {G : Prop} {x : Except Err α} {T : AM β} {a : AState}
    {R : α → β → AState → Prop} (h : RefE True x T a R) : RefE G x T a R := by
  cases x with
  | error e => exact fun _ => h trivial
  | ok v => exact h

end L.Ind
