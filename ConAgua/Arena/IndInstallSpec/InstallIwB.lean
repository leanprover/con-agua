module

public import ConAgua.Arena.IndInstallSpec.InstallCvDecB
public import ConAgua.Arena.IndSumSpec.SumProg
public import ConAgua.Arena.IndDecPLB

@[expose] public section

/-!
# InstallIwB

`installIwB`, `CtorsProg` (`decPLB`, `decCNSB`: `IndDecPLB`).
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- A `bool?` word of a record decoded below the tops, read at its word address. -/
theorem installIwB {m : Mem} {w : Word} {k : Nat} {b : Bool} (h : iwB (truncM m) (w.toNat + k) = some b)
    (hsz : (m.arr64 IW).size < 2 ^ 64) : (rdW (m.arr64 IW) (w + UInt64.ofNat k) != 0) = b := by
  simp only [iwB, bool?, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, rfl⟩ := h
  obtain ⟨hi, hx'⟩ := truncM_iw_get hx
  simp only [iwA, aread_apply, aread_apply] at hx'
  have hlt : w.toNat + k < (m.arr64 IW).size := (Array.getElem?_eq_some_iff.mp hx').1
  have hk : k < 2 ^ 64 := by omega
  have hwk : w.toNat + k < 2 ^ 64 := by omega
  have he : (w + UInt64.ofNat k).toNat = w.toNat + k := by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' hk]; exact Nat.mod_eq_of_lt hwk
  rw [rdW_of_get? he.symm hx']

/-- The lookups of `check_block_ctors`. -/
structure CtorsProg (p : Prog) : Prop extends CstProg p where
  rec2 : p.lookup "rec2" = some rec2
  erCopy : p.lookup "er_copy" = some erCopy
  erToIw : p.lookup "er_to_iw" = some erToIw
  lps : p.lookup "block_shape_lps" = some blockShapeLps
  ctors : p.lookup "check_block_ctors" = some checkBlockCtors
  sum : SumProg p

end L.Ind

end
