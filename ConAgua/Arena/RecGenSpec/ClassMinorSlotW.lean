import ConAgua.Arena.RecClassSpec.CloseLams

/-!
# ClassMinorSlotW

`classMinorSlotW_ok`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem classMinorSlotW_ok (n : Nat) (m : Mem) (rd c cc : Word) (R : ClassRead) (r : List Word)
    (hR : decCR m rd.toNat = some R) (hcc : cc.toNat < 2 ^ 32) (hsz : (m.arr64 IW).size + 5 < 2 ^ 64)
    (h : classMinorSlotW n m rd c cc = some r) :
    ∃ s ihs, (hitsFrom c.toNat (decI cc) 0 R.slots = [(s, ihs)]) ∧
      r.headD 0 = UInt64.ofNat s ∧ decPL m (decNN m) (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat = some ihs := by
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
  have hl2 : (rd + 1).toNat < (m.arr64 IW).size := hl'.1
  have ho2 : rd.toNat < (m.arr64 IW).size := iwN_lt ho
  simp only [classMinorSlotW, ho2, hl2, and_self, ite_true] at h
  rw [ho'.1, hl1] at h
  rcases hg : classMinorSlotGoW n m (UInt64.ofNat o) (UInt64.ofNat l) 0 c cc 0 0 0 0 with _ | ⟨x, y, z, w⟩ <;>
    simp only [hg, reduceCtorEq] at h
  obtain ⟨hx, h⟩ := of_ite_none h
  cases h
  have hx1 : x = 1 := by simpa using hx
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
  obtain ⟨g1, g2, g3⟩ := hg2
  simp only [UInt64.toNat_zero, Nat.zero_add] at g1 g2 g3
  rw [hx1] at g1
  have hlen : (hitsFrom c.toNat (decI cc) 0 slots).length = 1 := by
    have : (1 : Word).toNat = 1 := rfl
    omega
  match hh : hitsFrom c.toNat (decI cc) 0 slots, hlen with
  | [(s, ihs)], _ =>
    rw [hh] at g3
    obtain ⟨e1, e2⟩ := g3 s ihs rfl
    exact ⟨s, ihs, rfl, by simpa using e1, by simpa using e2⟩

local notation "V" => ConLeche.CheckMode.verified

end L.Ind

end
