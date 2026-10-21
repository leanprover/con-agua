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
    simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨q, -, h⟩ := h
    obtain ⟨k, -, rfl⟩ := h
    simp [ht, ClassSlot.isMinor]
  | 1, h =>
    simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at h
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

/-! ## `classMinorSlotGo`

The exec spec: the recursive helper's result is its word model, at every fuel — as `Walk.lean`'s
`bbGo`, by induction on the fuel, the self-call handled by the induction hypothesis (no "the loop
continues with the same parameters, shifted" argument is needed, since every quantity the twin's
scan carries — the remaining count, the current index, the running hit count and the last hit's
fields — is an explicit parameter of `class_minor_slot_go` here, not a `while`-loop local). -/

/-- Slot `p`'s hit test: `.minor`, matching class `c` and constructor `cc`. -/
def classMinorSlotHit (m : Mem) (p c cc : Word) : Bool :=
  rdW (m.arr64 IW) p == 1 && rdW (m.arr64 IW) (p + 1) == c && rdW (m.arr64 IW) (p + 2) == cc

/-- **The word model of `class_minor_slot_go`.** `off` is the slots' fixed base; `j` the current
index (so the slot under test is at `off + j`). -/
def classMinorSlotGoW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (Word × Word × Word × Word)
  | 0, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, off, rem, j, c, cc, cnt, rS, rOff, rLen =>
    if rem = 0 then some (cnt, rS, rOff, rLen)
    else if classMinorSlotHit m (rdW (m.arr64 IW) (off + j)) c cc then
      classMinorSlotGoW n m off (rem - 1) (j + 1) c cc (cnt + 1) j
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) (off + j) + 3))
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) (off + j) + 4))
    else
      classMinorSlotGoW n m off (rem - 1) (j + 1) c cc cnt rS rOff rLen

section arms
variable (n : Nat) (m : Mem) (off rem j c cc cnt rS rOff rLen : Word)

theorem classMinorSlotGoW_base (hrem : rem = 0) :
    classMinorSlotGoW (n + 1) m off rem j c cc cnt rS rOff rLen = some (cnt, rS, rOff, rLen) := by
  simp [classMinorSlotGoW, hrem]

theorem classMinorSlotGoW_hit (hrem : rem ≠ 0)
    (hh : classMinorSlotHit m (rdW (m.arr64 IW) (off + j)) c cc = true) :
    classMinorSlotGoW (n + 1) m off rem j c cc cnt rS rOff rLen =
      classMinorSlotGoW n m off (rem - 1) (j + 1) c cc (cnt + 1) j
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) (off + j) + 3))
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) (off + j) + 4)) := by
  simp [classMinorSlotGoW, hrem, hh]

theorem classMinorSlotGoW_miss (hrem : rem ≠ 0)
    (hh : classMinorSlotHit m (rdW (m.arr64 IW) (off + j)) c cc = false) :
    classMinorSlotGoW (n + 1) m off rem j c cc cnt rS rOff rLen =
      classMinorSlotGoW n m off (rem - 1) (j + 1) c cc cnt rS rOff rLen := by
  simp [classMinorSlotGoW, hrem, hh]

end arms

grind_pattern [ind_grind] classMinorSlotGoW_base => classMinorSlotGoW (n + 1) m off rem j c cc cnt rS rOff rLen
grind_pattern [ind_grind] classMinorSlotGoW_hit => classMinorSlotGoW (n + 1) m off rem j c cc cnt rS rOff rLen
grind_pattern [ind_grind] classMinorSlotGoW_miss => classMinorSlotGoW (n + 1) m off rem j c cc cnt rS rOff rLen

/-
The exec spec (`class_minor_slot_go`'s result is `classMinorSlotGoW`, at every fuel, by induction
on `n` with the self-call discharged by `ih`, as `bbGo_spec`) is NOT in this round: `vcgen`'s
`grind`/`finish` backend reports "failed to create E-match local theorem" for `ih` — a 9-word
universally quantified triple has no head pattern for `grind`'s E-matching to trigger on (every
existing callee-spec use in this codebase we found quantifies over at most 3-4 words). Shrinking
the explicit state (e.g. packing `(cnt, rS, rOff, rLen)` into one `IW` record pointer, as
`classMinorSlotGoW`'s RESULT already does) is the likely fix; left for a follow-up. -/

end L.Ind
