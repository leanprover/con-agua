module

public import ConAgua.Arena.Pool
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.NatGrindAttr

@[expose] public section

/-!
# `Off`: the frame of an in-place pass over a pool window

`Off p q o n`: the pools `p` and `q` agree off the region `[o, o + n)`. The in-place passes of
`nat_divmod` (`NatDiv.lean`) and `nat_mul` (`NatMul.lean`) change only their window; this is
their frame, a named predicate with `grind` patterns, as `Agree` is for appending.
-/

namespace L.Arena

/-- `p` and `q` agree off the region `[o, o + n)`. -/
def Off (p q : Array Word) (o n : Nat) : Prop := ∀ j, (j < o ∨ o + n ≤ j) → p[j]? = q[j]?

theorem Off.refl (p : Array Word) (o n : Nat) : Off p p o n := fun _ _ => rfl
grind_pattern [arena_grind] Off.refl => Off p p o n

/-- Writing the limb just past the changed prefix extends it. -/
theorem Off.set (p q : Array Word) (o k k' j : Nat) (v : Word) (h : Off p q o k) (hj : j = o + k)
    (hk : k' = k + 1) : Off (p.set! j v) q o k' := by
  intro i hi
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  have : j ≠ i := by omega
  simp only [this, ite_false]
  exact h i (by omega)
grind_pattern [arena_grind] Off.set => Off (p.set! j v) q o k', Off p q o k

theorem Off.get (p q : Array Word) (o k j : Nat) (h : Off p q o k) (hj : o + k ≤ j)
    (hp : j < p.size) (hq : j < q.size) : p[j] = q[j] := by
  have := h j (Or.inr hj); simp [hp, hq] at this; exact this
grind_pattern [arena_grind] Off.get => Off p q o k, p[j]

theorem Off.pv_below (p q : Array Word) (o k o' l : Nat) (h : Off p q o k) (hl : o' + l ≤ o) :
    pv p o' l = pv q o' l := by
  induction l with
  | zero => rfl
  | succ l ih => simp only [pv, ih (by omega), h (o' + l) (Or.inl (by omega))]
grind_pattern [arena_grind] Off.pv_below => Off p q o k, pv p o' l

theorem Off.lv_below (p q : Array Word) (o k o' l i : Nat) (h : Off p q o k) (hl : o' + l ≤ o) :
    lv p o' l i = lv q o' l i := by
  simp only [lv]; split
  · rw [h (o' + i) (Or.inl (by omega))]
  · rfl
grind_pattern [arena_grind] Off.lv_below => Off p q o k, lv p o' l i

/-- An in-place pass over `[o, o + n)` inside a region `[t, t + m)` agrees with the pool off the
region. -/
theorem Off.widen (p q : Array Word) (o n t m : Nat) (h : Off p q o n) (h1 : t ≤ o)
    (h2 : o + n ≤ t + m) : Off p q t m := fun j hj => h j (by omega)

theorem Off.trans (p q r : Array Word) (o n : Nat) (h : Off p q o n) (h' : Off q r o n) :
    Off p r o n := fun j hj => (h j hj).trans (h' j hj)
grind_pattern [arena_grind] Off.trans => Off p q o n, Off q r o n

/-- A slice off the region keeps its value. -/
theorem Off.pv_disj (p q : Array Word) (o k o' l : Nat) (h : Off p q o k) (hl : o' + l ≤ o ∨ o + k ≤ o') :
    pv p o' l = pv q o' l := by
  induction l with
  | zero => rfl
  | succ l ih => simp only [pv, ih (by omega), h (o' + l) (by omega)]
grind_pattern [winop_grind] Off.pv_disj => Off p q o k, pv p o' l

theorem Off.symm (p q : Array Word) (o n : Nat) (h : Off p q o n) : Off q p o n :=
  fun j hj => (h j hj).symm

/-- A frame of a smaller region is one of a larger region. -/
theorem Off.mono (p q : Array Word) (o i n : Nat) (h : Off p q o i) (hi : i ≤ n) : Off p q o n :=
  fun j hj => h j (by omega)

theorem Agree.trans (p q r : Array Word) (t t' : Nat) (h : Agree p q t') (h' : Agree q r t)
    (ht : t ≤ t') : Agree p r t := fun j hj => (h j (by omega)).trans (h' j hj)

/-- `p` and `q` agree below `s` off the window `[o, o + w)`: the frame of `nat_mul`'s window
product (`NatMul.lean`), which writes its window and scratch space from `s` up. -/
def OffB (p q : Array Word) (o w s : Nat) : Prop := ∀ j, j < s → (j < o ∨ o + w ≤ j) → p[j]? = q[j]?

theorem OffB.of_off (p q : Array Word) (o w s : Nat) (h : Off p q o w) : OffB p q o w s :=
  fun j _ hj => h j hj

theorem OffB.of_agree (p q : Array Word) (o w s : Nat) (h : Agree p q s) : OffB p q o w s :=
  fun j hj _ => h j hj

theorem OffB.trans (p q r : Array Word) (o w s : Nat) (h : OffB p q o w s) (h' : OffB q r o w s) :
    OffB p r o w s := fun j hj hw => (h j hj hw).trans (h' j hj hw)

theorem OffB.widen (p q : Array Word) (o w s t m : Nat) (h : OffB p q o w s) (h1 : t ≤ o)
    (h2 : o + w ≤ t + m) : OffB p q t m s := fun j hj hw => h j hj (by omega)

theorem OffB.agree (p q : Array Word) (o w s t : Nat) (h : OffB p q o w s) (h1 : t ≤ o) (h2 : t ≤ s) :
    Agree p q t := fun j hj => h j (by omega) (Or.inl (by omega))

theorem Off.agree (p q : Array Word) (o w t : Nat) (h : Off p q o w) (h1 : t ≤ o) : Agree p q t :=
  fun j hj => h j (Or.inl (by omega))

theorem OffB.pv_disj (p q : Array Word) (o w s o' l : Nat) (h : OffB p q o w s) (hs : o' + l ≤ s)
    (hl : o' + l ≤ o ∨ o + w ≤ o') : pv p o' l = pv q o' l := by
  induction l with
  | zero => rfl
  | succ l ih =>
    have := ih (by omega) (by omega)
    simp only [pv, this, h (o' + l) (by omega) (by omega)]
grind_pattern [winop_grind] OffB.pv_disj => OffB p q o w s, pv p o' l

end L.Arena
