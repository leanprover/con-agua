import ConAgua.Arena.IndInstallSpec.InstallRec2Tele
import ConAgua.Arena.IndPartsSpec.PartsPSlCons

/-!
# Cons

`MemsOK.cons`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

theorem MemsOK.cons {m : Mem} {o l : Word} {mss : List MemberShape} (h : MemsOK m o l mss)
    (hl : l ≠ 0) : ∃ q x rest, mss = x :: rest ∧ rdW (m.arr64 IW) o = UInt64.ofNat q ∧ q < 2 ^ 64 ∧
      MemOK m (UInt64.ofNat q : Word).toNat x ∧ MemsOK m (o + 1) (l - 1) rest := by
  obtain ⟨hp, hx⟩ := h
  obtain ⟨q, x, rest, rfl, hw, hqb, hdx, hrest⟩ := partsPSl_cons hp hl
  have hq' : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hlpos : 0 < l.toNat := Nat.pos_of_ne_zero fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
  obtain ⟨L, hL⟩ : ∃ L, l.toNat = L + 1 := ⟨l.toNat - 1, by omega⟩
  have hd1 : decPL (truncM m) (decMS (truncM m)) o.toNat (L + 1) = some (x :: rest) := by
    have := hp.1; simp only [DecB, hL] at this; exact this
  obtain ⟨v, hv, -⟩ := decPL_head hd1
  obtain ⟨hwv, -, -⟩ := partsIwRd hv rfl
  have hvq : v = q := by
    have h1 := congrArg UInt64.toNat (hwv.symm.trans hw)
    rw [UInt64.toNat_ofNat_of_lt' (partsIwRd hv rfl).2.1, hq'] at h1; exact h1
  subst hvq
  obtain ⟨-, hvm⟩ := rec2IwN_trunc hv
  have ho1 : (o + 1).toNat = o.toNat + 1 := by
    have := hp.2; rw [UInt64.toNat_add]; simp; omega
  have hl1 : (l - 1).toNat = L := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
  refine ⟨v, x, rest, rfl, hw, hqb, ⟨by rw [hq']; exact hdx, fun c hc => ?_⟩, hrest, ?_⟩
  · rw [hq'] at hc; exact hx 0 hlpos v (by simpa using hvm) c hc
  · intro j hj c hc d hd
    rw [ho1] at hc; rw [hl1] at hj
    exact hx (j + 1) (by omega) c (by rw [show o.toNat + (j + 1) = o.toNat + 1 + j by omega]; exact hc) d hd

end L.Ind

end
