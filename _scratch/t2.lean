import ConAgua.Arena.WhnfCore
open L L.Arena ConRon.Arena
open Std.WP
open scoped Lean.Order
set_option experimental.vcgen true
namespace L.Arena

theorem toUInt32_beq (a b : Word) (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32) :
    (a.toUInt32 == b.toUInt32) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · simp only [h, decide_false]
    apply Bool.eq_false_iff.mpr
    intro hb'
    apply h
    have := congrArg UInt32.toNat (eq_of_beq hb')
    rw [UInt64.toNat_toUInt32, UInt64.toNat_toUInt32, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
    exact UInt64.toNat_inj.mp this

theorem shr28_lt (e : Word) (he : HW e) : (e >>> 28).toNat < 2 ^ 32 := by
  rw [UInt64.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]; unfold HW at he; omega

theorem stuck_iff (e : Word) (he : HW e) :
    whnfCoreStuckTag (decE e) = decide (e >>> 28 ≠ 4 ∧ e >>> 28 ≠ 9 ∧ e >>> 28 ≠ 7 ∧ e >>> 28 ≠ 0) := by
  have h := shr28_lt e he
  simp only [whnfCoreStuckTag, decE_tag e he, ETag.app, ETag.proj, ETag.letE, ETag.bvar]
  rw [show (4 : UInt32) = (4 : Word).toUInt32 from rfl, toUInt32_beq _ _ h (by decide)]
  rw [show (9 : UInt32) = (9 : Word).toUInt32 from rfl, toUInt32_beq _ _ h (by decide)]
  rw [show (7 : UInt32) = (7 : Word).toUInt32 from rfl, toUInt32_beq _ _ h (by decide)]
  rw [show (0 : UInt32) = (0 : Word).toUInt32 from rfl, toUInt32_beq _ _ h (by decide)]
  by_cases h4 : e >>> 28 = 4 <;> by_cases h9 : e >>> 28 = 9 <;> by_cases h7 : e >>> 28 = 7 <;>
    by_cases h0 : e >>> 28 = 0 <;> simp_all

end L.Arena
