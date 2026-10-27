import ConAgua.Arena.RecClassSpec.SlotProg
import ConAgua.Arena.RecSim

/-!
# SlotsProg

`SlotsProg`, `simInternFVar`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The lookups `class_read_slots` needs. -/
structure SlotsProg (p : Prog) : Prop extends SlotProg p where
  sn : p.lookup "sl_snoc" = some slSnoc
  ff : p.lookup "fvar_find" = some fvarFind
  fp : p.lookup "fvar_push" = some fvarPush
  ifv : p.lookup "intern_fvar" = some internFVar
  slots : p.lookup "class_read_slots" = some classReadSlots
  next : p.lookup "class_read_slots_next" = some classReadSlotsNext
  msn : p.lookup "class_read_slots_snoc" = some classReadSlotsSnoc
  hi1 : I1Prog p

end L.Ind

namespace L.Ind

open L.Arena

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem} {a : AState}

theorem simInternFVar (hS : StageR dn vis fe m a) (u : Word) {ty : Word} (hty : H ty) :
    RSim (fvinternW m u ty) (internFVarE u.toNat (decI ty)) a
      (fun b a' x => StageR dn vis fe b.2 a' ∧ IWGrow m b.2 ∧ x = decE b.1) := by
  rintro ⟨r, m'⟩ h
  obtain ⟨a', hrun, hS', hg⟩ := internFVar_stage hS u ty hty h
  exact ⟨decE r, a', hrun, hS', hg, rfl⟩

end sims

end L.Ind

end
