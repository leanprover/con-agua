module

public import ConAgua.Arena.RecClassSpec.CloseLams

@[expose] public section

/-!
# ClassMinorSlotW

`cmsGo_hits`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **What `class_minor_slot`'s scan says about the twin's hits**: their number is the count word,
and a single hit is the slot word with the `ihs` slice. -/
theorem cmsGo_hits (n : Nat) (m : Mem) (rd c cc : Word) (R : ClassRead) {x y z w : Word}
    (hR : decCR m rd.toNat = some R) (hcc : cc.toNat < 2 ^ 32) (hsz : (m.arr64 IW).size + 5 < 2 ^ 64)
    (hg : classMinorSlotGoW n m (rdW (m.arr64 IW) rd) (rdW (m.arr64 IW) (rd + 1)) 0 c cc 0 0 0 0 =
      some (x, y, z, w)) :
    x.toNat = (hitsFrom c.toNat (decI cc) 0 R.slots).length ∧
    ∀ s ihs, hitsFrom c.toNat (decI cc) 0 R.slots = [(s, ihs)] →
      y = UInt64.ofNat s ∧ decPL m (decNN m) z.toNat w.toNat = some ihs := by
  simp only [decCR, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hR
  obtain ⟨slots, hsl, rcs, -, hRe⟩ := hR
  subst hRe
  obtain ⟨o, l, ho, hl, hdec⟩ := decAt_some hsl
  simp only at *
  have hrd64 : rd.toNat < 2 ^ 64 := rd.toNat_lt
  have ho' := iwN_rdW ho hrd64
  rw [UInt64.ofNat_toNat] at ho'
  have hl' := iwN_off (k := 1) hl (by have := iwN_lt hl; omega)
  rw [show UInt64.ofNat 1 = 1 from rfl, UInt64.ofNat_toNat] at hl'
  have hl1 : rdW (m.arr64 IW) (rd + 1) = UInt64.ofNat l := hl'.2
  rw [ho'.1, hl1] at hg
  have hol : o + l < 2 ^ 64 := by
    rcases decPL_le hdec with h0 | h0
    · have : o < 2 ^ 64 := ho'.2
      omega
    · omega
  have hlz : l < 2 ^ 64 := (iwN_rdW hl (by have := iwN_lt hl; omega)).2
  have hos : o < 2 ^ 64 := ho'.2
  have hg2 := classMinorSlotGoW_ok n m (UInt64.ofNat o) (UInt64.ofNat l) 0 c cc 0 0 0 0 x y z w slots hg
    (by simpa [UInt64.toNat_ofNat_of_lt' hos, UInt64.toNat_ofNat_of_lt' hlz] using hdec) hcc hsz
    (by simp [UInt64.toNat_ofNat_of_lt' hos, UInt64.toNat_ofNat_of_lt' hlz]; omega)
    (by simp [UInt64.toNat_ofNat_of_lt' hlz]; omega) (by simp [UInt64.toNat_ofNat_of_lt' hlz]; omega)
  obtain ⟨g1, -, g3⟩ := hg2
  simp only [UInt64.toNat_zero, Nat.zero_add] at g1 g3
  refine ⟨g1, fun s ihs hh => ?_⟩
  rw [hh] at g3
  obtain ⟨e1, e2⟩ := g3 s ihs rfl
  exact ⟨by simpa using e1, by simpa using e2⟩

local notation "V" => ConLeche.CheckMode.verified

end L.Ind

end
