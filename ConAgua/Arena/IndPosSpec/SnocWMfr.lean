module

import ConAgua.Arena.IndPosSpec.DepthGo
import ConAgua.Arena.IndPosSpec.CrLook
public import ConAgua.Arena.IndPosSpec.NoGoStep

@[expose] public section

/-!
# SnocWMfr

`snocW_mfr`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem snocW_mfr {n : Nat} {m m' : Mem} {o l x : Word} {r : List Word} (h : snocW n m o l x = some (r, m')) :
    MFr [] [] m m' := by
  unfold snocW at h
  mfr_auto h [allocW_mfr, fun h => MFr.of_iw (L.Ind.copyW_iwFrame _ _ _ _ _ _ h)]
  simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact MFr.set_iw _ _ _

end L.Ind

end
