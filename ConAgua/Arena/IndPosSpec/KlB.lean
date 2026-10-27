import ConAgua.Arena.IndDecStab
import ConAgua.Arena.IndInstallSpec.BlockCapsAt

/-!
# KlB

`KlB`, `decKE_mono`, `OutsB`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Field-kind slices, `(kinds, closed)` records -/

/-- A field-kind slice decoded below the tops. -/
def KlB (m : Mem) (o l : Nat) (ks : List NestFieldKind) : Prop := DecB (fun m => decKL m o l) m ks

theorem decKE_mono (v : Nat) : OMono (fun m => decKE m v) := by
  unfold decKE
  exact OMono.bind (OMono.decAt (fun o l => decKL_mono o l) v) fun _ =>
    OMono.bind (OMono.iwH (v + 2)) fun _ => OMono.const _

/-- A slice of `(kinds, closed)` records decoded below the tops. -/
def OutsB (m : Mem) (o l : Nat) (outs : List (List NestFieldKind × EIdx)) : Prop :=
  DecB (fun m => decPL m (decKE m) o l) m outs

end L.Ind

end
