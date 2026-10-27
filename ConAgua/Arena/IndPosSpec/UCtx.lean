import ConAgua.Arena.IndPosSpec.EnvFindWHit
import ConAgua.Arena.IndPosSpec.Pos2CvLpsWStage

/-!
# UCtx

`CsAt.tail`, `UCtx`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order
namespace L.Ind
open L.Arena

theorem CsAt.tail {m : Mem} {o : Nat} {x : IConstantVal × Nat} {xs : List (IConstantVal × Nat)}
    {P : Nat → Prop} (h : CsAt m o (x :: xs) P) : CsAt m (o + 1) xs P := fun i hi => by
  obtain ⟨w, hw, hc⟩ := h (i + 1) (by simp; omega)
  exact ⟨w, by rw [show o + 1 + i = o + (i + 1) by omega]; exact hw, by simpa using hc⟩

/-- The context facts the uniform checks need, at one memory. -/
structure UCtx (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m : Mem) (ctx : Word)
    (c : NestCtx) : Prop where
  dec : decCtx m ctx.toNat = some c
  inn : CtxIn m ctx.toNat (· < iwTop m)
  sl : CtxSl m ctx.toNat

end L.Ind

end
