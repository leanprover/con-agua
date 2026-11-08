module

import ConAgua.Arena.IndSumSpec.DecHLTake
public import ConAgua.Arena.RecCheckSpec.EeW
import ConAgua.Arena.RecClassSpec.IhW
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndSim
import ConAgua.Arena.IndSumSpec.StructProjArgP

@[expose] public section

/-!
# EeW2

`eftF_ok`, `eeW_ok`, `HSl0.drop`, `HSl0.take`.
-/

noncomputable section

/-!
# `RecCheck`: `targetK53`, the relational side (lane `indproofs3`, helper `rec`)

The twin split at the L functions' boundaries (`tkTele`, `tkHeads`, `tkArgs`, verbatim pieces of
`targetK53`; `tk53_eq` puts them back together), each simulated by its word model.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `erase_each`, `target_k53_tele` simulated -/

section rel
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

theorem eftF_ok (n : Nat) {m m' : Mem} {a : AState} {e : Word} {r : List Word}
    (h : eftF n m e = some (r, m')) (hS : StageR vis fe m a) (he : H e) (hP : RcMR m) :
    ∃ a', (ConRon.Arena.eraseFVarTys (decE e)).run a = .ok (decE (r.headD 0), a') ∧ H (r.headD 0) ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ RcMR m' := by
  sorry

theorem eeW_ok (n : Nat) : ∀ {m m' : Mem} {a : AState} {o l : Word} {r : List Word} {xs : List EIdx},
    eeW n m o l = some (r, m') → StageR vis fe m a → HSl0 m o l xs → RcMR m →
    ∃ ys a', (xs.mapM fun b => ConRon.Arena.eraseFVarTys b).run a = .ok (ys, a') ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some ys ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ RcMR m' := by
  sorry

end rel

/-! ## Slices: `drop`, `take`; a `TargetMajor`'s fields -/

theorem HSl0.drop {k' : IdxKind} {m : Mem} {o l k : Word} {xs : List (Idx k')} (h : HSl0 m o l xs) :
    HSl0 m (if l < k then o else o + k) (if l < k then 0 else l - k) (xs.drop k.toNat) := by
  have hlen := h.len
  by_cases hlk : l < k
  · simp only [hlk, ite_true]
    have : xs.drop k.toNat = [] := List.drop_eq_nil_of_le (by rw [hlen]; exact Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp hlk))
    rw [this]; exact ⟨by simp [decHL, hslice?], .inl rfl⟩
  · simp only [hlk, ite_false]
    have hkl : k.toNat ≤ l.toNat := by
      have := UInt64.lt_iff_toNat_lt (a := l) (b := k); simp only [hlk, false_iff] at this; omega
    have hsub : (l - k).toNat = l.toNat - k.toNat := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hkl)
    by_cases h0 : l - k = 0
    · have : xs.drop k.toNat = [] := List.drop_eq_nil_of_le (by
        have := congrArg UInt64.toNat h0; rw [hsub] at this; simp at this; omega)
      rw [this, h0]; exact ⟨by simp [decHL, hslice?], .inl rfl⟩
    · have hl0 : l ≠ 0 := by intro e; apply h0; apply UInt64.toNat_inj.mp; rw [hsub]; subst e; simp
      have hb := h.2.resolve_left hl0
      have hok : (o + k).toNat = o.toNat + k.toNat := by
        rw [UInt64.toNat_add]; apply Nat.mod_eq_of_lt
        have ht : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
        omega
      refine HSl0.of ?_ (by rw [hok, hsub]; omega)
      rw [hok, hsub]; exact decHL_drop k.toNat h.1 hkl

theorem HSl0.take {k' : IdxKind} {m : Mem} {o l k : Word} {xs : List (Idx k')} (h : HSl0 m o l xs) :
    HSl0 m o (if l < k then l else k) (xs.take k.toNat) := by
  have hlen := h.len
  by_cases hlk : l < k
  · simp only [hlk, ite_true]
    rw [List.take_of_length_le (by rw [hlen]; exact Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp hlk))]; exact h
  · simp only [hlk, ite_false]
    have hkl : k.toNat ≤ l.toNat := by
      have := UInt64.lt_iff_toNat_lt (a := l) (b := k); simp only [hlk, false_iff] at this; omega
    refine ⟨decHL_take h.1 _ hkl, ?_⟩
    by_cases hk0 : k = 0
    · exact .inl hk0
    · have hl0 : l ≠ 0 := by intro e; subst e; apply hk0; apply UInt64.toNat_inj.mp; simp at hkl; simp [hkl]
      exact .inr (Nat.le_trans (by omega) (h.2.resolve_left hl0))

end L.Ind

end
end
