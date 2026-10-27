import ConAgua.Arena.IndPosSpec.Pos2CvLpsWStage
import ConAgua.Arena.IndPosSpec.RootHoles

/-!
# SnocWStage

`snocW_stage`, `CtxSl.grow`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `nest_holes(_go)` refines `nestHoles(.go)` -/

theorem snocW_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {o l x : Word} {r : List Word} (h : snocW n m o l x = some (r, m'))
    (hS : StageR dn vis fe m a) : StageR dn vis fe m' a := by
  simp only [snocW] at h
  by_cases h0 : l + 1 = 0
  · simp [h0] at h
  simp only [h0, ite_false] at h
  rcases hal : allocW m (l + 1) with _ | ⟨q, m1⟩; · simp [hal] at h
  simp only [hal] at h
  rcases hcp : copyW (n - 1) m1 q o l with _ | m2; · simp [hcp] at h
  simp only [hcp, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact (StageR.ofCopyW _ hcp (hS.alloc hal).1).set_iw _ _

theorem CtxSl.grow {m m' : Mem} {p : Nat} (h : CtxSl m p) (hin : CtxIn m p (· < iwTop m))
    (hg : IWGrow m m') : CtxSl m' p := by
  intro i hi o l ho hl
  have e0 := iwN_agree (RdS.of_grow hg) (hin.1 i (by omega))
  have e1 := iwN_agree (RdS.of_grow hg) (show p + i + 1 < iwTop m from by
    have := hin.1 (i + 1) (by omega); simpa [Nat.add_assoc] using this)
  rw [e0] at ho; rw [e1] at hl
  exact Nat.le_trans (h i hi o l ho hl) hg.1

end L.Ind

end
