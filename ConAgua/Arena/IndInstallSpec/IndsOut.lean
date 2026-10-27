import ConAgua.Arena.IndInstallSpec.CapsProg
import ConAgua.Arena.IndPartsSpec.PartsConsPL

/-!
# IndsOut

`IndsOut`.
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- Stage 1's post: the environment with the formers pushed at the returned view, the formers'
constants a slice below the tops, the shape with its sort below the tops. -/
def IndsOut (dn : NIdx → Option ConLeche.Name) (m : Mem) (r : List Word)
    (x : IFEnv × List IConstantVal × BlockShape) (m' : Mem) (a' : AState) : Prop :=
  StageR dn (r.headD 0) x.1 m' a' ∧ IWGrow m m' ∧
    PSlR decCVp x.2.1 (r.tail.headD 0) (r.tail.tail.headD 0) m' ∧
    DecB (fun m => decBS m (r.tail.tail.tail.headD 0).toNat) m' x.2.2 ∧
    ShapeSrc m' (r.tail.tail.tail.headD 0)

end L.Ind

end
