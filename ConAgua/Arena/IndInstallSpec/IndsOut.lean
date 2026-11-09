module

public import ConAgua.Arena.IndInstallSpec.CapsProg
public import ConAgua.Arena.IndPartsSpec.PartsConsPL

@[expose] public section

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

/-- Stage 1's post: the environment with the formers pushed at the returned view (word `0`), the
shape with its sort (word `1`) below the tops. -/
def IndsOut (m : Mem) (r : List Word) (x : IFEnv × BlockShape) (m' : Mem) (a' : AState) : Prop :=
  StageR (r.headD 0) x.1 m' a' ∧ IWGrow m m' ∧
    DecB (fun m => decBS m (r.tail.headD 0).toNat) m' x.2 ∧ ShapeSrc m' (r.tail.headD 0)

end L.Ind

end
