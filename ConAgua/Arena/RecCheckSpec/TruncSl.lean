module

public import ConAgua.Arena.RecCheckSpec.TcmF
public import ConAgua.Arena.RecCheckSpec.Tpd
import ConAgua.Arena.RecGenSpec.Rec3IwSlice
public import ConAgua.Arena.IndSumSpec.Row
import ConAgua.Arena.RecClassSpec.MjProg
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
public import ConAgua.Arena.RecCheckSpec.RcLook

@[expose] public section

/-!
# TruncSl

`truncH`, `truncSl`: record fields decoded below the tops.
-/

section

noncomputable section


noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## Reading records decoded below the tops -/

/-- A handle field of a record decoded in the cut pools, read at its word address. -/
theorem truncH {k : IdxKind} {m : Mem} {w : Word} {i : Nat} {x : Idx k}
    (h : iwH (truncM m) (w.toNat + i) = some x) (hsz : (m.arr64 IW).size < 2 ^ 64) :
    H (rdW (m.arr64 IW) (w + UInt64.ofNat i)) ∧ decI (rdW (m.arr64 IW) (w + UInt64.ofNat i)) = x := by
  sorry

/-- A slice field `(off, len)` of a record decoded in the cut pools, read at its word addresses. -/
theorem truncSl {k : IdxKind} {m : Mem} {w : Word} {i o l : Nat} {xs : List (Idx k)}
    (ho : iwN (truncM m) (w.toNat + i) = some o) (hl : iwN (truncM m) (w.toNat + i + 1) = some l)
    (hd : decHL (truncM m) o l = some xs) (hsz : (m.arr64 IW).size < 2 ^ 64) :
    HSl0 m (rdW (m.arr64 IW) (w + UInt64.ofNat i)) (rdW (m.arr64 IW) (w + UInt64.ofNat (i + 1))) xs := by
  obtain ⟨-, hom⟩ := rec2IwN_trunc ho
  obtain ⟨-, hlm⟩ := rec2IwN_trunc hl
  obtain ⟨eo, to⟩ := rec2RdN (w := w) (k := i) hom hsz
  obtain ⟨el, tl⟩ := rec2RdN (w := w) (k := i + 1) (by simpa [Nat.add_assoc] using hlm) hsz
  rw [eo, el]
  rcases rec3IwSlice hd with hb | h0
  · refine HSl0.of ?_ (by rw [to, tl]; exact hb)
    rw [to, tl, ← decHL_truncM hb]; exact hd
  · subst h0
    have hx : xs = [] := by have := decHL_length _ hd; simpa using this
    subst hx
    exact ⟨by rw [tl]; simp [decHL, hslice?], .inl (UInt64.toNat_inj.mp (by rw [tl]; rfl))⟩

end L.Ind

end
end

end
