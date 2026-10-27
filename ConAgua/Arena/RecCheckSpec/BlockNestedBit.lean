import ConAgua.Arena.IndPosSpec.NestKeyMap
import ConAgua.Arena.RecCheck
import ConAgua.Arena.RecSim
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Bool
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# BlockNestedBit: `ConRon.Arena.blockNestedBit`

The refinement theorems `blockNestedBit_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `block_nested_bit` -/

/-- **The model of `block_nested_bit_go`.** -/
def nbGoW : Nat → Mem → Word → Word → Word → Option Word
  | 0, _, _, _, _ => none
  | n + 1, m, o, l, k =>
    if l = 0 then some 0
    else if k ≤ rdW (m.arr64 IW) (rdW (m.arr64 IW) o + 3) then some 1
    else nbGoW n m (o + 1) (l - 1) k

section arms
variable (n : Nat) (m : Mem) (o l k : Word)
theorem nbGoW_nil (h : l = 0) : nbGoW (n + 1) m o l k = some 0 := by simp [nbGoW, h]
theorem nbGoW_hit (h : l ≠ 0) (h2 : k ≤ rdW (m.arr64 IW) (rdW (m.arr64 IW) o + 3)) :
    nbGoW (n + 1) m o l k = some 1 := by simp [nbGoW, h, h2]
theorem nbGoW_next (h : l ≠ 0) (h2 : ¬ k ≤ rdW (m.arr64 IW) (rdW (m.arr64 IW) o + 3)) :
    nbGoW (n + 1) m o l k = nbGoW n m (o + 1) (l - 1) k := by simp [nbGoW, h, h2]
end arms

grind_pattern [ind_grind] nbGoW_nil => nbGoW (n + 1) m o l k
grind_pattern [ind_grind] nbGoW_hit => nbGoW (n + 1) m o l k
grind_pattern [ind_grind] nbGoW_next => nbGoW (n + 1) m o l k

theorem blockNestedBitGo_spec (p : Prog) (hp : p.lookup "block_nested_bit_go" = some blockNestedBitGo)
    (n : Nat) : ∀ (s₀ : St) (o l k : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_nested_bit_go" [o, l, k]
    ⦃fun r s' => s' = s₀ ∧ nbGoW n s₀.mem o l k = some (r.headD 0); ⊤⦄ := by
  induction n with
  | zero => intro s₀ o l k; rw [invoke_eq _ hp]; simp only [callFn, blockNestedBitGo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o l k
    rw [invoke_eq _ hp]; simp only [callFn, blockNestedBitGo]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
      finish (gen := 20) [rdW_eq]

theorem decRS_tgt {m : Mem} {p : Nat} {R : RecShape} (h : decRS m p = some R) :
    iwN m (p + 3) = some R.tgt := by
  simp only [decRS, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨q, hq, cv, hcv, rP, hrP, mI, hmI, tg, htg, rh, hrh, rfl⟩ := h
  exact htg

theorem nbGoW_ok (n : Nat) : ∀ (m : Mem) (o l k r : Word) (recs : List RecShape),
    (m.arr64 IW).size < 2 ^ 64 → decPL m (decRS m) o.toNat l.toNat = some recs →
    nbGoW n m o l k = some r → r = if recs.any (fun rc => !(rc.tgt < k.toNat)) then 1 else 0 := by
  induction n with
  | zero => intro m o l k r recs _ _ h; simp [nbGoW] at h
  | succ n ih =>
    intro m o l k r recs hsz hdec h
    by_cases hl : l = 0
    · rw [nbGoW_nil n m o l k hl] at h
      have : recs = [] := by
        have : l.toNat = 0 := by rw [hl]; rfl
        rw [this] at hdec; simpa [decPL] using hdec.symm
      subst this; simp at h; simp [h]
    obtain ⟨v, rc, rest, hv, hrc, hrest, rfl, hrd, hv64⟩ := decPL_step hsz hdec hl
    have ht := decRS_tgt hrc
    have hrt := iwN_rdW_at (w := UInt64.ofNat v) (k := 3) (m := m)
      (by rw [UInt64.toNat_ofNat_of_lt' hv64]; exact ht) hsz
    rw [show UInt64.ofNat 3 = (3 : Word) from rfl] at hrt
    by_cases hk : k ≤ rdW (m.arr64 IW) (rdW (m.arr64 IW) o + 3)
    · rw [nbGoW_hit n m o l k hl hk] at h
      simp only [Option.some.injEq] at h
      rw [hrd, hrt.1, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hrt.2] at hk
      have : (!decide (rc.tgt < k.toNat)) = true := by simp; omega
      simp [List.any_cons, this, ← h]
    · rw [nbGoW_next n m o l k hl hk] at h
      rw [hrd, hrt.1, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hrt.2] at hk
      rw [ih m _ _ k r rest hsz hrest h]
      have : (!decide (rc.tgt < k.toNat)) = false := by simp; omega
      simp [List.any_cons, this]

def nbK (n : Nat) (m : Mem) (q : Word) : Option Word → Option Word
  | none => none
  | some f => if f = 0 then some 1
    else nbGoW n m (rdW (m.arr64 IW) (q + 2)) (rdW (m.arr64 IW) (q + 3)) (rdW (m.arr64 IW) (q + 1))

/-- **The model of `block_nested_bit`.** -/
def nbW : Nat → Mem → Word → Word → Word → Option Word
  | 0, _, _, _, _ => none
  | n + 1, m, q, ko, kl => nbK n m q (kindsFlatOutW n m ko kl)

theorem nbW_eq (n : Nat) (m : Mem) (q ko kl : Word) : nbW (n + 1) m q ko kl = nbK n m q (kindsFlatOutW n m ko kl) := rfl
theorem nbK_zero (n : Nat) (m : Mem) (q f : Word) (h : f = 0) : nbK n m q (some f) = some 1 := by
  rw [nbK, ite_eq_left h]
theorem nbK_ne (n : Nat) (m : Mem) (q f : Word) (h : f ≠ 0) : nbK n m q (some f) =
    nbGoW n m (rdW (m.arr64 IW) (q + 2)) (rdW (m.arr64 IW) (q + 3)) (rdW (m.arr64 IW) (q + 1)) := by
  rw [nbK, ite_eq_right h]
grind_pattern [ind_grind] nbW_eq => nbW (n + 1) m q ko kl
grind_pattern [ind_grind] nbK_zero => nbK n m q (some f)
grind_pattern [ind_grind] nbK_ne => nbK n m q (some f)

theorem blockNestedBit_spec (p : Prog)
    (hf : p.lookup "nest_field_kind_flat" = some nestFieldKindFlat)
    (hi : p.lookup "nest_kinds_flat_inner" = some nestKindsFlatInner)
    (hm : p.lookup "nest_kinds_flat_mid" = some nestKindsFlatMid)
    (hk : p.lookup "nest_kinds_flat" = some nestKindsFlat)
    (hg : p.lookup "block_nested_bit_go" = some blockNestedBitGo)
    (hp : p.lookup "block_nested_bit" = some blockNestedBit) (n : Nat) (s₀ : St) (q ko kl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_nested_bit" [q, ko, kl]
    ⦃fun r s' => s' = s₀ ∧ nbW n s₀.mem q ko kl = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]; simp only [callFn, blockNestedBit]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        nestKindsFlat_spec p hf hi hm hk n, blockNestedBitGo_spec p hg n] <;>
      finish (gen := 20) [rdW_eq]

/-- **`block_nested_bit` refines `blockNestedBit`** (a pure twin). -/
@[refines ConRon.Arena.blockNestedBit]
theorem blockNestedBit_refines (p : Prog)
    (hf : p.lookup "nest_field_kind_flat" = some nestFieldKindFlat)
    (hi : p.lookup "nest_kinds_flat_inner" = some nestKindsFlatInner)
    (hm : p.lookup "nest_kinds_flat_mid" = some nestKindsFlatMid)
    (hk : p.lookup "nest_kinds_flat" = some nestKindsFlat)
    (hg : p.lookup "block_nested_bit_go" = some blockNestedBitGo)
    (hp : p.lookup "block_nested_bit" = some blockNestedBit) (n : Nat) (s₀ : St) (q ko kl : Word)
    (bs : BlockShape) (kss : List (List (List NestFieldKind)))
    (hsz : (s₀.mem.arr64 IW).size < 2 ^ 64) (hbs : decBS s₀.mem q.toNat = some bs)
    (hdec : decPL s₀.mem (decLH s₀.mem (decPL s₀.mem (decLH s₀.mem (decKL s₀.mem)))) ko.toNat kl.toNat = some kss) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_nested_bit" [q, ko, kl]
    ⦃fun r s' => s' = s₀ ∧ r.headD 0 = if ConRon.Arena.blockNestedBit bs kss then 1 else 0; ⊤⦄ := by
  refine triple_post (blockNestedBit_spec p hf hi hm hk hg hp n s₀ q ko kl) ?_
  rintro r s' ⟨rfl, h⟩
  refine ⟨rfl, ?_⟩
  obtain _ | n := n
  · simp [nbW] at h
  rw [nbW_eq] at h
  rcases h1 : kindsFlatOutW n s'.mem ko kl with _ | f <;> rw [h1] at h <;>
    try (simp only [nbK, reduceCtorEq] at h; done)
  have hf' := kindsFlatOutW_ok n _ _ _ kss f hsz hdec h1
  by_cases hfl : ConRon.Arena.nestKindsFlat kss = true
  · rw [ite_eq_left hfl] at hf'; subst hf'
    rw [nbK_ne n _ q 1 (by decide)] at h
    obtain ⟨hmem, hrecs, -⟩ := decBS_some hbs
    obtain ⟨o1, l1, ho1, hl1, hg1⟩ := decAt_some hmem
    obtain ⟨o2, l2, ho2, hl2, hg2⟩ := decAt_some hrecs
    have r1 := iwN_rdW_at (w := q) (k := 1) hl1 hsz
    have r2 := iwN_rdW_at (w := q) (k := 2) ho2 hsz
    have r3 := iwN_rdW_at (w := q) (k := 3) (by simpa [Nat.add_assoc] using hl2) hsz
    rw [show UInt64.ofNat 1 = (1 : Word) from rfl] at r1
    rw [show UInt64.ofNat 2 = (2 : Word) from rfl] at r2
    rw [show UInt64.ofNat 3 = (3 : Word) from rfl] at r3
    rw [r1.1, r2.1, r3.1] at h
    have hg2' : decPL s'.mem (decRS s'.mem) (UInt64.ofNat o2).toNat (UInt64.ofNat l2).toNat = some bs.recs := by
      rw [UInt64.toNat_ofNat_of_lt' r2.2, UInt64.toNat_ofNat_of_lt' r3.2]; exact hg2
    have := nbGoW_ok n _ _ _ _ _ bs.recs hsz hg2' h
    have hk' : (UInt64.ofNat l1).toNat = bs.k := by
      rw [UInt64.toNat_ofNat_of_lt' r1.2, BlockShape.k, decPL_length _ hg1]
    rw [hk'] at this
    rw [this]
    simp [ConRon.Arena.blockNestedBit, hfl]
  · have hf0 : f = 0 := by rw [hf']; simp [hfl]
    rw [nbK_zero n _ q f hf0] at h
    simp only [Option.some.injEq] at h
    rw [← h]
    simp [ConRon.Arena.blockNestedBit, hfl]

end L.Ind

end
