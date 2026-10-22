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

/-- Slot `p`'s hit test with the L code's guards: `none` when a read it makes is out of bounds,
`some false` on a miss, `some true` on a hit (`.minor`, class `c`, ctor `cc`). -/
def classMinorSlotHit (a : Array Word) (p c cc : Word) : Option Bool :=
  if p.toNat < a.size then
    if rdW a p = 1 then
      if (p + 1).toNat < a.size then
        if rdW a (p + 1) = c then
          if (p + 2).toNat < a.size then
            if rdW a (p + 2) = cc then
              if (p + 3).toNat < a.size ∧ (p + 4).toNat < a.size then some true else none
            else some false
          else none
        else some false
      else none
    else some false
  else none

section hitlemmas
variable (a : Array Word) (p c cc : Word)
theorem hit_oob0 (h : ¬ p.toNat < a.size) : classMinorSlotHit a p c cc = none := by
  simp only [classMinorSlotHit, ↓reduceIte, h]
theorem hit_t (h : p.toNat < a.size) (h1 : rdW a p ≠ 1) : classMinorSlotHit a p c cc = some false := by
  simp only [classMinorSlotHit, ↓reduceIte, h, h1]
theorem hit_oob1 (h : p.toNat < a.size) (h1 : rdW a p = 1) (h2 : ¬ (p + 1).toNat < a.size) :
    classMinorSlotHit a p c cc = none := by
  simp only [classMinorSlotHit, ↓reduceIte, h, h1, h2]
theorem hit_c (h : p.toNat < a.size) (h1 : rdW a p = 1) (h2 : (p + 1).toNat < a.size)
    (h3 : rdW a (p + 1) ≠ c) : classMinorSlotHit a p c cc = some false := by
  simp only [classMinorSlotHit, ↓reduceIte, h, h1, h2, h3]
theorem hit_oob2 (h : p.toNat < a.size) (h1 : rdW a p = 1) (h2 : (p + 1).toNat < a.size)
    (h3 : rdW a (p + 1) = c) (h4 : ¬ (p + 2).toNat < a.size) :
    classMinorSlotHit a p c cc = none := by
  simp only [classMinorSlotHit, ↓reduceIte, h, h1, h2, h3, h4]
theorem hit_cc (h : p.toNat < a.size) (h1 : rdW a p = 1) (h2 : (p + 1).toNat < a.size)
    (h3 : rdW a (p + 1) = c) (h4 : (p + 2).toNat < a.size) (h5 : rdW a (p + 2) ≠ cc) :
    classMinorSlotHit a p c cc = some false := by
  simp only [classMinorSlotHit, ↓reduceIte, h, h1, h2, h3, h4, h5]
theorem hit_oob3 (h : p.toNat < a.size) (h1 : rdW a p = 1) (h2 : (p + 1).toNat < a.size)
    (h3 : rdW a (p + 1) = c) (h4 : (p + 2).toNat < a.size) (h5 : rdW a (p + 2) = cc)
    (h6 : ¬ ((p + 3).toNat < a.size ∧ (p + 4).toNat < a.size)) :
    classMinorSlotHit a p c cc = none := by
  simp only [classMinorSlotHit, ↓reduceIte, h, h1, h2, h3, h4, h5, h6]
theorem hit_hit (h : p.toNat < a.size) (h1 : rdW a p = 1) (h2 : (p + 1).toNat < a.size)
    (h3 : rdW a (p + 1) = c) (h4 : (p + 2).toNat < a.size) (h5 : rdW a (p + 2) = cc)
    (h6 : (p + 3).toNat < a.size) (h7 : (p + 4).toNat < a.size) :
    classMinorSlotHit a p c cc = some true := by
  simp only [classMinorSlotHit, ↓reduceIte, h, h1, h2, h3, h4, h5, h6, h7]
end hitlemmas

grind_pattern [ind_grind] hit_oob0 => classMinorSlotHit a p c cc
grind_pattern [ind_grind] hit_t => classMinorSlotHit a p c cc
grind_pattern [ind_grind] hit_oob1 => classMinorSlotHit a p c cc
grind_pattern [ind_grind] hit_c => classMinorSlotHit a p c cc
grind_pattern [ind_grind] hit_oob2 => classMinorSlotHit a p c cc
grind_pattern [ind_grind] hit_cc => classMinorSlotHit a p c cc
grind_pattern [ind_grind] hit_oob3 => classMinorSlotHit a p c cc
grind_pattern [ind_grind] hit_hit => classMinorSlotHit a p c cc

/-- **The word model of `class_minor_slot_go`.** `off` is the slots' fixed base; `j` the current
index (so the slot under test is at `off + j`). -/
def classMinorSlotGoW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (Word × Word × Word × Word)
  | 0, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, off, rem, j, c, cc, cnt, rS, rOff, rLen =>
    if rem = 0 then some (cnt, rS, rOff, rLen)
    else if (off + j).toNat < (m.arr64 IW).size then
      match classMinorSlotHit (m.arr64 IW) (rdW (m.arr64 IW) (off + j)) c cc with
      | none => none
      | some false => classMinorSlotGoW n m off (rem - 1) (j + 1) c cc cnt rS rOff rLen
      | some true => classMinorSlotGoW n m off (rem - 1) (j + 1) c cc (cnt + 1) j
          (rdW (m.arr64 IW) (rdW (m.arr64 IW) (off + j) + 3))
          (rdW (m.arr64 IW) (rdW (m.arr64 IW) (off + j) + 4))
    else none

section arms
variable (n : Nat) (m : Mem) (off rem j c cc cnt rS rOff rLen : Word)

theorem classMinorSlotGoW_base (hrem : rem = 0) :
    classMinorSlotGoW (n + 1) m off rem j c cc cnt rS rOff rLen = some (cnt, rS, rOff, rLen) := by
  simp only [classMinorSlotGoW, ↓reduceIte, hrem]

theorem classMinorSlotGoW_oob (hrem : rem ≠ 0) (hp : ¬ (off + j).toNat < (m.arr64 IW).size) :
    classMinorSlotGoW (n + 1) m off rem j c cc cnt rS rOff rLen = none := by
  simp only [classMinorSlotGoW, ↓reduceIte, hrem, hp]

theorem classMinorSlotGoW_oob2 (hrem : rem ≠ 0) (hp : (off + j).toNat < (m.arr64 IW).size)
    (hh : classMinorSlotHit (m.arr64 IW) (rdW (m.arr64 IW) (off + j)) c cc = none) :
    classMinorSlotGoW (n + 1) m off rem j c cc cnt rS rOff rLen = none := by
  simp only [classMinorSlotGoW, ↓reduceIte, hrem, hp, hh]

theorem classMinorSlotGoW_miss (hrem : rem ≠ 0) (hp : (off + j).toNat < (m.arr64 IW).size)
    (hh : classMinorSlotHit (m.arr64 IW) (rdW (m.arr64 IW) (off + j)) c cc = some false) :
    classMinorSlotGoW (n + 1) m off rem j c cc cnt rS rOff rLen =
      classMinorSlotGoW n m off (rem - 1) (j + 1) c cc cnt rS rOff rLen := by
  simp only [classMinorSlotGoW, ↓reduceIte, hrem, hp, hh]

theorem classMinorSlotGoW_hit (hrem : rem ≠ 0) (hp : (off + j).toNat < (m.arr64 IW).size)
    (hh : classMinorSlotHit (m.arr64 IW) (rdW (m.arr64 IW) (off + j)) c cc = some true) :
    classMinorSlotGoW (n + 1) m off rem j c cc cnt rS rOff rLen =
      classMinorSlotGoW n m off (rem - 1) (j + 1) c cc (cnt + 1) j
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) (off + j) + 3))
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) (off + j) + 4)) := by
  simp only [classMinorSlotGoW, ↓reduceIte, hrem, hp, hh]

end arms

grind_pattern [ind_grind] classMinorSlotGoW_base => classMinorSlotGoW (n + 1) m off rem j c cc cnt rS rOff rLen
grind_pattern [ind_grind] classMinorSlotGoW_oob => classMinorSlotGoW (n + 1) m off rem j c cc cnt rS rOff rLen
grind_pattern [ind_grind] classMinorSlotGoW_oob2 => classMinorSlotGoW (n + 1) m off rem j c cc cnt rS rOff rLen
grind_pattern [ind_grind] classMinorSlotGoW_miss => classMinorSlotGoW (n + 1) m off rem j c cc cnt rS rOff rLen
grind_pattern [ind_grind] classMinorSlotGoW_hit => classMinorSlotGoW (n + 1) m off rem j c cc cnt rS rOff rLen

theorem classMinorSlotGo_spec (p : Prog) (hp : p.lookup "class_minor_slot_go" = some classMinorSlotGo)
    (n : Nat) : ∀ (s₀ : St) (off rem j c cc cnt rS rOff rLen : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_minor_slot_go"
      [off, rem, j, c, cc, cnt, rS, rOff, rLen]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      ∃ x y z w, classMinorSlotGoW n s₀.mem off rem j c cc cnt rS rOff rLen = some (x, y, z, w) ∧
        r = [x, y, z, w]; ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ off rem j c cc cnt rS rOff rLen; rw [invoke_eq _ hp]; simp only [callFn, classMinorSlotGo]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ off rem j c cc cnt rS rOff rLen
    rw [invoke_eq _ hp]
    simp only [callFn, classMinorSlotGo]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
      finish (gen := 20)

end L.Ind
