import ConAgua.Arena.IndIface

/-!
# CtorLp

`cxoK9`, `rdW_er_grow`, `CtorLp`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## The model -/

section model
variable (p : Prog) (n : Nat)

/-- After `rec6`: the record. -/
def cxoK9 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

end model

/-- A word of the constant records below their top stays. -/
theorem rdW_er_grow {m m' : Mem} (hg : IWGrow m m') {x : Word} (hi : x.toNat < erTop m) :
    rdW (m'.arr64 EREC) x = rdW (m.arr64 EREC) x := by
  simp only [rdW, hg.2.2.2 _ hi]

/-- The constant's level-parameter slice lies in `EREC` or is empty (`target_ctor_at`'s
hypothesis), at the constant of the `[cv, nF]` record `cA`. -/
def CtorLp (m : Mem) (cA : Word) : Prop :=
  (rdW (m.arr64 EREC) (rdW (m.arr64 IW) cA + 2)).toNat = 0 ∨
  (rdW (m.arr64 EREC) (rdW (m.arr64 IW) cA + 1)).toNat + (rdW (m.arr64 EREC) (rdW (m.arr64 IW) cA + 2)).toNat ≤
    (m.arr64 EREC).size

end L.Ind

end
