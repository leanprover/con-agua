import ConAgua.Arena.IndRealSpine

/-!
# ClassMinorSlotHit

`classMinorSlotHit`, `hit_t`, `hit_c`, `hit_cc`, `hit_hit`, `classMinorSlotGoW` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

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
theorem hit_t (h : p.toNat < a.size) (h1 : rdW a p ≠ 1) : classMinorSlotHit a p c cc = some false := by
  simp only [classMinorSlotHit, ↓reduceIte, h, h1]
theorem hit_c (h : p.toNat < a.size) (h1 : rdW a p = 1) (h2 : (p + 1).toNat < a.size)
    (h3 : rdW a (p + 1) ≠ c) : classMinorSlotHit a p c cc = some false := by
  simp only [classMinorSlotHit, ↓reduceIte, h, h1, h2, h3]
theorem hit_cc (h : p.toNat < a.size) (h1 : rdW a p = 1) (h2 : (p + 1).toNat < a.size)
    (h3 : rdW a (p + 1) = c) (h4 : (p + 2).toNat < a.size) (h5 : rdW a (p + 2) ≠ cc) :
    classMinorSlotHit a p c cc = some false := by
  simp only [classMinorSlotHit, ↓reduceIte, h, h1, h2, h3, h4, h5]
theorem hit_hit (h : p.toNat < a.size) (h1 : rdW a p = 1) (h2 : (p + 1).toNat < a.size)
    (h3 : rdW a (p + 1) = c) (h4 : (p + 2).toNat < a.size) (h5 : rdW a (p + 2) = cc)
    (h6 : (p + 3).toNat < a.size) (h7 : (p + 4).toNat < a.size) :
    classMinorSlotHit a p c cc = some true := by
  simp only [classMinorSlotHit, ↓reduceIte, h, h1, h2, h3, h4, h5, h6, h7, and_self]
end hitlemmas

grind_pattern [ind_grind] hit_t => classMinorSlotHit a p c cc
grind_pattern [ind_grind] hit_c => classMinorSlotHit a p c cc
grind_pattern [ind_grind] hit_cc => classMinorSlotHit a p c cc
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
grind_pattern [ind_grind] classMinorSlotGoW_miss => classMinorSlotGoW (n + 1) m off rem j c cc cnt rS rOff rLen
grind_pattern [ind_grind] classMinorSlotGoW_hit => classMinorSlotGoW (n + 1) m off rem j c cc cnt rS rOff rLen

/-- The twin's hits of `classMinorSlot`, from index `j`. -/
def hitsFrom (c : Nat) (C : NIdx) : Nat → List ClassSlot → List (Nat × List (Nat × Nat))
  | _, [] => []
  | j, .motive _ :: sls => hitsFrom c C (j + 1) sls
  | j, .minor c' C' ihs :: sls =>
    if c' == c && C' == C then (j, ihs) :: hitsFrom c C (j + 1) sls else hitsFrom c C (j + 1) sls

/-- What the scan's result words say about the hits. -/
def GoRes (m : Mem) (hs : List (Nat × List (Nat × Nat))) (cnt rS rOff rLen x y z w : Word) : Prop :=
  x.toNat = cnt.toNat + hs.length ∧ (hs = [] → y = rS ∧ z = rOff ∧ w = rLen) ∧
  (∀ s ihs, hs.getLast? = some (s, ihs) →
    y = UInt64.ofNat s ∧ decPL m (decNN m) z.toNat w.toNat = some ihs)

/-! ## `class_minor_slot` -/

/-- The model of `class_minor_slot`. -/
def classMinorSlotW (n : Nat) (m : Mem) (rd c cc : Word) : Option (List Word) :=
  if rd.toNat < (m.arr64 IW).size ∧ (rd + 1).toNat < (m.arr64 IW).size then
    match classMinorSlotGoW n m (rdW (m.arr64 IW) rd) (rdW (m.arr64 IW) (rd + 1)) 0 c cc 0 0 0 0 with
    | none => none
    | some (x, y, z, w) => if x ≠ 1 then none else some [y, z, w]
  else none

/-! ## `class_leaf_at` -/

/-- The word model of `class_leaf_at`. -/
def leafAtW (m : Mem) (mm leaf : Word) : Option (List Word × Mem) :=
  match gafF m [CWF, leaf] with
  | none => none
  | some (r, m1) =>
    if r.headD 0 >>> 28 ≠ 3 then some ([0], m1)
    else if eViewW m1 (r.headD 0) = [] then none
    else some ([if (eViewW m1 (r.headD 0)).tail.headD 0 = rdW (m1.arr64 IW) mm then 1 else 0], m1)

local notation "V" => ConLeche.CheckMode.verified

end L.Ind

end
