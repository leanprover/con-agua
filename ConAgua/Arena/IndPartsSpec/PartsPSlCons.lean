import ConAgua.Arena.IndPartsSpec.BsW
import ConAgua.Arena.IndPartsSpec.IndPartsProg2

/-!
# PartsPSlCons

`partsPSl_cons`, `partsCVName`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- A pointer slice's head and tail, below the tops. -/
theorem partsPSl_cons {α : Type} {f : Mem → Nat → Option α} {xs : List α} {o l : Word} {m : Mem}
    (h : PSlR f xs o l m) (hl : l ≠ 0) :
    ∃ p x xs', xs = x :: xs' ∧ rdW (m.arr64 IW) o = UInt64.ofNat p ∧ p < 2 ^ 64 ∧
      DecB (fun m => f m p) m x ∧ PSlR f xs' (o + 1) (l - 1) m := by
  obtain ⟨L, hL⟩ : ∃ L, l.toNat = L + 1 :=
    ⟨l.toNat - 1, by have : l.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  have hd := h.1; simp only [DecB, hL] at hd
  obtain ⟨p, x, xs', rfl, hp, hx, hxs'⟩ := decPL_cons hd
  obtain ⟨hw, hpb, holt⟩ := partsIwRd hp rfl
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have ho1 : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  refine ⟨p, x, xs', rfl, hw, hpb, hx, ⟨?_, ?_⟩⟩
  · show decPL _ _ _ _ = _; rw [ho1, partsPred_of hL]; exact hxs'
  · rw [ho1, partsPred_of hL]; have := h.2; omega

/-- A constant decoded below the tops: its name word, in any memory grown into. -/
theorem partsCVName {m m' : Mem} (hg : IWGrow m m') {q : Nat} {cv : IConstantVal}
    (h : DecB (fun m => decCVp m q) m cv) (hq : q < 2 ^ 64) :
    (rdW (m'.arr64 EREC) (UInt64.ofNat q)).toNat < 2 ^ 32 ∧
      decI (rdW (m'.arr64 EREC) (UInt64.ofNat q)) = cv.name :=
  decCVp_name_p (h.stab (OMono.decCVp _) m' hg) hq

end L.Ind

end
