module

public import ConAgua.Arena.RecClassSpec.Classes

@[expose] public section

/-!
# DecCVX

`decCVX`, `rec2ToNat_succ`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## Relational lemma -/

open Classical in
/-- A constant record below the record top, decoded. -/
noncomputable def decCVX (m : Mem) (p : Nat) : Option IConstantVal :=
  if CVExt m p then decCVp m p else none

theorem rec2ToNat_succ {o : Word} {i : Nat} (h : o.toNat ≤ i) (hi : i < 2 ^ 64 - 1) :
    (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega

end L.Ind

end
