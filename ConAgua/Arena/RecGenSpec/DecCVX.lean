import ConAgua.Arena.RecClassSpec.Classes

/-!
# DecCVX

`rtsK3`, `decCVX`, `rec2ToNat_succ`, `rec2ToNat_pred`.
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

def rtsK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => some ([r3.headD 0, r3.tail.headD 0], m3)

/-! ## Relational lemma -/

open Classical in
/-- A constant record below the record top, decoded. -/
noncomputable def decCVX (m : Mem) (p : Nat) : Option IConstantVal :=
  if CVExt m p then decCVp m p else none

theorem rec2ToNat_succ {o : Word} {i : Nat} (h : o.toNat ≤ i) (hi : i < 2 ^ 64 - 1) :
    (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega

theorem rec2ToNat_pred {l : Word} (h : l ≠ 0) : (l - 1).toNat = l.toNat - 1 := by
  have : l.toNat ≠ 0 := fun e => h (UInt64.toNat_inj.mp (by simpa using e))
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp

end L.Ind

end
