import ConAgua.Arena.IndPosSpec.DepthGo

/-!
# Mfr

`RfInv.mfr`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem RfInv.mfr {S : List ArrId} {T : List Word} {m m' : Mem} {M : Std.HashMap (EIdx × Word) EIdx} {G g : Word}
    (h : RfInv m M G g) (hf : MFr S T m m') (hS : RFM ∉ S)
    (hT : (208 : Word) ∉ T ∧ (218 : Word) ∉ T ∧ (219 : Word) ∉ T) : RfInv m' M G g :=
  h.frame (RfFr.of_mfr hf hS hT)

end L.Ind

end
