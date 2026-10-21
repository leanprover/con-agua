import ConAgua.Arena.RecGen
import ConAgua.Arena.IndLibSpec

/-!
# Refinements of `RecGen` (lane `induct`, round 2)

`ClassSlot.isMinor` (a plain record-tag read, as `IndPartsSpec`'s `blockShapeK_refines`) and
`classMinorSlot` (now a small recursive helper, `classMinorSlotGo`, instead of its round-1 `while`
loop: its accumulator words are explicit parameters, so its refinement is plain induction on the
fuel, as `Walk.lean`'s `bbGo`/`bbNode` — not the subtler "the loop continues with the SAME
parameters, just shifted" argument `sl_contains`/`sl_nodup` need for their `while` loops, whose
varying state happens to be their own parameters).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `ClassSlot.isMinor` -/

/-- A decoded `ClassSlot`'s tag word is `1` exactly when it is `.isMinor`. -/
theorem decCS_tag {m : Mem} {p : Nat} {cs : ClassSlot} (h : decCS m p = some cs) :
    iwN m p = some (if cs.isMinor then 1 else 0) := by
  rw [decCS] at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨t, ht, h⟩ := h
  match t, h with
  | 0, h =>
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨q, -, h⟩ := h
    obtain ⟨k, -, rfl⟩ := h
    simp [ht, ClassSlot.isMinor]
  | 1, h =>
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨a, -, h⟩ := h
    obtain ⟨b, -, h⟩ := h
    obtain ⟨c2, -, rfl⟩ := h
    simp [ht, ClassSlot.isMinor]
  | (k + 2), h => simp at h

/-- **`class_slot_is_minor` is `ClassSlot.isMinor`.** -/
@[refines ConRon.Arena.ClassSlot.isMinor]
theorem classSlotIsMinor_refines (p : Prog) (hp : p.lookup "class_slot_is_minor" = some classSlotIsMinor)
    (n : Nat) (s₀ : St) (q : Word) (cs : ClassSlot) (hq : decCS s₀.mem q.toNat = some cs)
    (hq1 : q.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_slot_is_minor" [q]
    ⦃fun r s' => s' = s₀ ∧ (r.headD 0 != 0) = cs.isMinor; ⊤⦄ := by
  have key := iwN_rdW (decCS_tag hq) hq1
  rw [invoke_eq _ hp]
  simp only [callFn, classSlotIsMinor]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [UInt64.ofNat_toNat]

end L.Ind
