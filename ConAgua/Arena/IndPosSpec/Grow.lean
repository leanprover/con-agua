import ConAgua.Arena.IndPosSpec.SnocWStage
import ConAgua.Arena.IndPosSpec.UCtx

/-!
# Grow

`UCtx.grow`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order
namespace L.Ind
open L.Arena

theorem UCtx.grow {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m' : Mem} {ctx : Word}
    {c : NestCtx} (h : UCtx dn vis fe m ctx c) (hg : IWGrow m m') : UCtx dn vis fe m' ctx c :=
  ⟨by rw [(CtxIn.grow h.inn hg).1]; exact h.dec, (CtxIn.grow h.inn hg).2, h.sl.grow h.inn hg⟩

end L.Ind

end
