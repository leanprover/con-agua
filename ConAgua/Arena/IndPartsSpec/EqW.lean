module

public import ConAgua.Arena.IndPartsSpec.MemberNames
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import ConAgua.Arena.Env
import ConAgua.L.LocNF
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.IndIface

@[expose] public section

/-!
# EqW

`eqW`, `eqW_len`, `eqW_nil`, `eqW_ne`, `eqW_next`, `slEq_spec` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `sl_eq` -/

/-- The model of `sl_eq`. -/
def eqW : Nat → Mem → Word → Word → Word → Word → Option Word
  | 0, _, _, _, _, _ => none
  | n + 1, m, o1, l1, o2, l2 =>
    if l1 ≠ l2 then some 0
    else if l1 = 0 then some 1
    else if rdW (m.arr64 IW) o1 ≠ rdW (m.arr64 IW) o2 then some 0
    else eqW n m (o1 + 1) (l1 - 1) (o2 + 1) (l2 - 1)

section arms
variable (n : Nat) (m : Mem) (o1 l1 o2 l2 : Word)
theorem eqW_len (h : l1 ≠ l2) : eqW (n + 1) m o1 l1 o2 l2 = some 0 := by simp [eqW, h]
theorem eqW_nil (h : l1 = l2) (h0 : l1 = 0) : eqW (n + 1) m o1 l1 o2 l2 = some 1 := by
  subst h; simp [eqW, h0]
theorem eqW_ne (h : l1 = l2) (h0 : l1 ≠ 0) (hx : rdW (m.arr64 IW) o1 ≠ rdW (m.arr64 IW) o2) :
    eqW (n + 1) m o1 l1 o2 l2 = some 0 := by subst h; simp [eqW, h0, hx]
theorem eqW_next (h : l1 = l2) (h0 : l1 ≠ 0) (hx : rdW (m.arr64 IW) o1 = rdW (m.arr64 IW) o2) :
    eqW (n + 1) m o1 l1 o2 l2 = eqW n m (o1 + 1) (l1 - 1) (o2 + 1) (l2 - 1) := by
  subst h; simp [eqW, h0, hx]
end arms

grind_pattern [ind_grind] eqW_len => eqW (n + 1) m o1 l1 o2 l2
grind_pattern [ind_grind] eqW_nil => eqW (n + 1) m o1 l1 o2 l2
grind_pattern [ind_grind] eqW_ne => eqW (n + 1) m o1 l1 o2 l2
grind_pattern [ind_grind] eqW_next => eqW (n + 1) m o1 l1 o2 l2

section specs
variable (p : Prog) (hp : p.lookup "sl_eq" = some slEq)
include hp

theorem slEq_spec (n : Nat) : ∀ (s₀ : St) (o1 l1 o2 l2 : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "sl_eq" [o1, l1, o2, l2]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ eqW n s₀.mem o1 l1 o2 l2 = some (r.headD 0); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ o1 l1 o2 l2; rw [invoke_eq _ hp]; simp only [callFn, slEq]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ o1 l1 o2 l2
    rw [invoke_eq _ hp]
    simp only [callFn, slEq]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
      finish (gen := 20) [rdW_eq, LocEq]

end specs

theorem slR_length {m : Mem} {o l : Word} {ws : List Word} (h : SlR m o l ws) :
    ws.length = l.toNat := by
  induction h with
  | nil => rfl
  | @cons o l ws hl _ ih =>
    have : l.toNat ≠ 0 := fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
    have e : (l - 1).toNat = l.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp
    simp only [List.length_cons, ih, e]; omega

theorem eqW_ok (n : Nat) : ∀ (m : Mem) (o1 l1 o2 l2 r : Word) (ws1 ws2 : List Word),
    SlR m o1 l1 ws1 → SlR m o2 l2 ws2 → eqW n m o1 l1 o2 l2 = some r →
    r = if ws1 = ws2 then 1 else 0 := by
  induction n with
  | zero => intro m o1 l1 o2 l2 r ws1 ws2 _ _ h; simp [eqW] at h
  | succ n ih =>
    intro m o1 l1 o2 l2 r ws1 ws2 h1 h2 h
    cases h1 with
    | nil =>
      cases h2 with
      | nil => rw [eqW_nil n m o1 0 o2 0 rfl rfl] at h; simp at h; simp [h]
      | cons hl2 _ =>
        rw [eqW_len n m o1 0 o2 _ (Ne.symm hl2)] at h; simp at h; simp [← h]
    | @cons _ _ ws1' hl1 hs1 =>
      cases h2 with
      | nil =>
        rw [eqW_len n m o1 _ o2 0 hl1] at h; simp at h; simp [← h]
      | @cons _ _ ws2' hl2 hs2 =>
        by_cases hll : l1 = l2
        · by_cases hx : rdW (m.arr64 IW) o1 = rdW (m.arr64 IW) o2
          · rw [eqW_next n m o1 l1 o2 l2 hll hl1 hx] at h
            have := ih m _ _ _ _ r ws1' ws2' hs1 hs2 h
            rw [this, hx]
            simp
          · rw [eqW_ne n m o1 l1 o2 l2 hll hl1 hx] at h
            simp at h; subst h
            simp [hx]
        · rw [eqW_len n m o1 l1 o2 l2 hll] at h
          simp at h; subst h
          have e1 := slR_length (SlR.cons hl1 hs1)
          have e2 := slR_length (SlR.cons hl2 hs2)
          have hne : ¬ (rdW (m.arr64 IW) o1 :: ws1' = rdW (m.arr64 IW) o2 :: ws2') := by
            intro heq; rw [heq] at e1; apply hll
            exact UInt64.toNat_inj.mp (by rw [← e1, e2])
          simp [hne]

/-! ## `block_shape_lps` with the result's shape -/

theorem lpsW_two {n : Nat} {m m' : Mem} {p : Word} {r : List Word}
    (h : lpsW n m p = some (r, m')) : r = [r.headD 0, r.getD 1 0] := by
  cases n with
  | zero => simp [lpsW] at h
  | succ n =>
    by_cases hz : rdW (m.arr64 IW) (p + 1) = 0
    · rw [lpsW_nil n m p hz] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h; rfl
    · rw [lpsW_cons n m p hz] at h
      have := erToIwW_two h
      simpa using this

theorem blockShapeLps_spec2 (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc : p.lookup "er_copy" = some erCopy) (he : p.lookup "er_to_iw" = some erToIw)
    (hp : p.lookup "block_shape_lps" = some blockShapeLps) (n : Nat) (s₀ : St) (q : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "block_shape_lps" [q]
    ⦃fun r s' => LocEq s' s₀ ∧ lpsW n s₀.mem q = some (r, s'.mem) ∧ r = [r.headD 0, r.getD 1 0]; ⊤⦄ :=
  triple_post (blockShapeLps_spec p ha hc he hp n s₀ q) (fun _r _s' ⟨h1, h2⟩ => ⟨h1, h2, lpsW_two h2⟩)

end L.Ind

end
