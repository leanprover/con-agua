module

public import ConLeche.SetTheory.Derive.LfpFam
@[expose] public section

/-!
# Least pre-fixed points of TUPLE functors (task #315)

The carrier of a block of `k` inductive families `T₀ … T_{k-1}` is the
simultaneous least pre-fixed point of its constructor-tower functor
acting on **tuples of families** — a meta-level tuple `X : Nat → V`
whose `m`-th component (`m < k`) is a family over member `m`'s own
index-tuple set `Is m` (`famSpace w (Is m)`), ordered componentwise
(`TupleLe`).  No member tag enters any index set: the tuple is a
meta-level object, its components are the members' own families.
This is `LfpFam.lean` componentwise:

    lfpTuple w k Is Φ m = famOf (i ↦ {x ∈ app (L₀ m) i | ∀ closed X, x ∈ app (X m) i}) (Is m)

over a classically chosen closed tuple `L₀` (the empty tuple when
there is none), a fibre that left `strictU w` dropped to `∅` (`dropTo`,
`LfpFam.lean`: an intersection of strict sets need not be strict) —
TOTAL, as `lfpFamSet` is.  Under a closed
tuple, monotonicity and `MapsTuple` nothing is dropped, the least pre-fixed tuple is a fixed point
(`lfpTuple_eq`) and supports simultaneous structural induction
(`lfpTuple_induction`).

Everything here is over the bare `SetTheory` interface; no syntax.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-! ## The tuple space and its order -/

/-- The tuple lies in the product of the members' family spaces
(positions `≥ k` are unconstrained junk). -/
def InTupleSpace (w k : Nat) (Is : Nat → V) (X : Nat → V) : Prop :=
  ∀ m, m < k → X m ∈ˢ famSpace w (Is m)

/-- The tuple is a tuple of families of TYPES: each member's fibres lie
in `univ w`, not necessarily in the strict universe (task #342).  It is
what a hole frame binds (the holes' type is `I → Sort w`); the tuple
space is inside it (`InTupleSpace.toU`). -/
def InTupleSpaceU (w k : Nat) (Is : Nat → V) (X : Nat → V) : Prop :=
  ∀ m, m < k → X m ∈ˢ famSpaceIn (univ w) (Is m)

theorem InTupleSpace.toU {w k : Nat} {Is X : Nat → V} (h : InTupleSpace w k Is X) :
    InTupleSpaceU w k Is X :=
  fun m hm => famSpace_subset_univ w (Is m) _ (h m hm)

/-- The componentwise order on tuples of families. -/
def TupleLe (k : Nat) (Is : Nat → V) (X Y : Nat → V) : Prop :=
  ∀ m, m < k → FamLe (Is m) (X m) (Y m)

theorem TupleLe.refl (k : Nat) (Is X : Nat → V) : TupleLe k Is X X :=
  fun m _ => FamLe.refl (Is m) (X m)

/-- A `Φ`-closed tuple: a pre-fixed point of `Φ` in the tuple space. -/
def IsClosedTuple (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V) (X : Nat → V) : Prop :=
  InTupleSpace w k Is X ∧ TupleLe k Is (Φ X) X

/-- Monotonicity of a tuple functor on the tuple space. -/
def MonoTuple (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V) : Prop :=
  ∀ X Y, InTupleSpace w k Is X → InTupleSpace w k Is Y → TupleLe k Is X Y →
    TupleLe k Is (Φ X) (Φ Y)

/-- The functor maps the tuple space into itself. -/
def MapsTuple (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V) : Prop :=
  ∀ X, InTupleSpace w k Is X → InTupleSpace w k Is (Φ X)

/-! ## The least pre-fixed tuple -/

open Classical in
/-- **The least pre-fixed tuple of `Φ`** — componentwise, fibrewise the
intersection of the closed tuples when there is one (separated from a
chosen closed tuple), dropped to `∅` if it left `strictU w`; the empty
tuple otherwise. -/
noncomputable def lfpTuple (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V) : Nat → V :=
  fun m =>
    if h : ∃ L, IsClosedTuple w k Is Φ L then
      famOf (fun i => dropTo (strictU w) (sep (app (Classical.choose h m) i)
        (fun x => ∀ X, IsClosedTuple w k Is Φ X → x ∈ˢ app (X m) i))) (Is m)
    else famOf (fun _ => empty) (Is m)

section Laws

variable {w k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V}

theorem lfpTuple_of_not (h : ¬ ∃ L, IsClosedTuple w k Is Φ L) (m : Nat) :
    lfpTuple w k Is Φ m = famOf (fun _ => empty) (Is m) := by
  unfold lfpTuple; exact dite_eq_right h

theorem forall_of_mem_app_lfpTuple (h : ∃ L, IsClosedTuple w k Is Φ L) {m : Nat} {i x : V}
    (hi : i ∈ˢ Is m) (hx : x ∈ˢ app (lfpTuple w k Is Φ m) i) :
    ∀ X, IsClosedTuple w k Is Φ X → x ∈ˢ app (X m) i := by
  unfold lfpTuple at hx
  rw [dite_eq_left h, app_famOf hi] at hx
  exact (mem_sep.mp (mem_of_mem_dropTo hx)).2

/-- A member of the level below every closed tuple's fibre is below the
least tuple's. -/
theorem subset_app_lfpTuple (h : ∃ L, IsClosedTuple w k Is Φ L) {m : Nat} (hm : m < k)
    {i Y : V} (hi : i ∈ˢ Is m) (hY : Y ∈ˢ (strictU w : V))
    (hYX : ∀ X, IsClosedTuple w k Is Φ X → Y ⊆ˢ app (X m) i) :
    Y ⊆ˢ app (lfpTuple w k Is Φ m) i := by
  unfold lfpTuple
  rw [dite_eq_left h, app_famOf hi]
  refine subset_dropTo (strictU_dropClosed w) (famSpace_app ((Classical.choose_spec h).1 m hm) hi)
    sep_subset hY fun x hx => mem_sep.mpr ⟨?_, fun X hX => hYX X hX x hx⟩
  exact hYX _ (Classical.choose_spec h) x hx

/-- **Leastness**: the least pre-fixed tuple lies below every closed
tuple. -/
theorem lfpTuple_le {X : Nat → V} (hX : IsClosedTuple w k Is Φ X) :
    TupleLe k Is (lfpTuple w k Is Φ) X :=
  fun _ _ _ hi _x hx => forall_of_mem_app_lfpTuple ⟨X, hX⟩ hi hx X hX

/-- **Formation, unconditional**: the least pre-fixed tuple is in the
tuple space. -/
theorem lfpTuple_mem (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V) :
    InTupleSpace w k Is (lfpTuple w k Is Φ) := by
  intro m _
  unfold lfpTuple
  split
  · exact famOf_mem_famSpace fun _ _ => dropTo_mem (empty_mem_strictU w) _
  · exact famOf_mem_famSpace fun _ _ => empty_mem_strictU w

/-- **Closure**: the least pre-fixed tuple is a pre-fixed point.  The
operator must map the tuple space into itself: a fibre dropped to `∅`
stays closed because the operator's fibre there, a member of the level
below the dropped set, is `∅` too (`DropClosed`). -/
theorem lfpTuple_closed (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ)
    (hmaps : MapsTuple w k Is Φ) :
    TupleLe k Is (Φ (lfpTuple w k Is Φ)) (lfpTuple w k Is Φ) := by
  intro m hm i hi
  refine subset_app_lfpTuple h hm hi
    (famSpace_app (hmaps _ (lfpTuple_mem w k Is Φ) m hm) hi) fun X hX => ?_
  exact Subset.trans (hmono _ _ (lfpTuple_mem w k Is Φ) hX.1 (lfpTuple_le hX) m hm i hi)
    (hX.2 m hm i hi)

/-- The least pre-fixed tuple is a post-fixed point. -/
theorem lfpTuple_fixed (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ)
    (hmaps : MapsTuple w k Is Φ) :
    TupleLe k Is (lfpTuple w k Is Φ) (Φ (lfpTuple w k Is Φ)) := by
  refine lfpTuple_le ⟨hmaps _ (lfpTuple_mem w k Is Φ), ?_⟩
  exact hmono _ _ (hmaps _ (lfpTuple_mem w k Is Φ)) (lfpTuple_mem w k Is Φ)
    (lfpTuple_closed h hmono hmaps)

/-- The fixed-point equation, componentwise and fibrewise. -/
theorem app_lfpTuple_eq (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ)
    (hmaps : MapsTuple w k Is Φ) {m : Nat} (hm : m < k) {i : V} (hi : i ∈ˢ Is m) :
    app (Φ (lfpTuple w k Is Φ) m) i = app (lfpTuple w k Is Φ m) i :=
  Subset.antisymm (lfpTuple_closed h hmono hmaps m hm i hi)
    (lfpTuple_fixed h hmono hmaps m hm i hi)

/-- The fixed-point equation, componentwise. -/
theorem lfpTuple_eq (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ)
    (hmaps : MapsTuple w k Is Φ) {m : Nat} (hm : m < k) :
    Φ (lfpTuple w k Is Φ) m = lfpTuple w k Is Φ m :=
  famSpace_ext (hmaps _ (lfpTuple_mem w k Is Φ) m hm) (lfpTuple_mem w k Is Φ m hm)
    fun _ hi => app_lfpTuple_eq h hmono hmaps hm hi

/-- The tuple of separations of the carrier by a per-member property,
a fibre that left `strictU w` dropped to `∅`. -/
noncomputable def sepTuple (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V)
    (P : Nat → V → V → Prop) : Nat → V :=
  fun m => famOf (fun i => dropTo (strictU w) (sep (app (lfpTuple w k Is Φ m) i) (P m i))) (Is m)

/-- The separated tuple is in the tuple space. -/
theorem sepTuple_mem (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V)
    (P : Nat → V → V → Prop) : InTupleSpace w k Is (sepTuple w k Is Φ P) := fun _ _ =>
  famOf_mem_famSpace fun _ _ => dropTo_mem (empty_mem_strictU w) _

/-- A member of the separated tuple is in the carrier and has the
property. -/
theorem mem_app_sepTuple_imp {P : Nat → V → V → Prop} {m : Nat} {i y : V} (hi : i ∈ˢ Is m)
    (hy : y ∈ˢ app (sepTuple w k Is Φ P m) i) :
    y ∈ˢ app (lfpTuple w k Is Φ m) i ∧ P m i y := by
  unfold sepTuple at hy
  rw [app_famOf hi] at hy
  exact mem_sep.mp (mem_of_mem_dropTo hy)

/-- The separated tuple lies below the carrier. -/
theorem sepTuple_le (w k : Nat) (Is : Nat → V) (Φ : (Nat → V) → Nat → V)
    (P : Nat → V → V → Prop) : TupleLe k Is (sepTuple w k Is Φ P) (lfpTuple w k Is Φ) :=
  fun _ _ _ hi _ hy => (mem_app_sepTuple_imp hi hy).1

/-- **Simultaneous structural induction**: a family of properties, one
per member, closed under the functor on the carrier holds on the whole
carrier. -/
theorem lfpTuple_induction (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ)
    (hmaps : MapsTuple w k Is Φ) (P : Nat → V → V → Prop)
    (hP : ∀ m, m < k → ∀ i, i ∈ˢ Is m → ∀ x,
      x ∈ˢ app (Φ (sepTuple w k Is Φ P) m) i → P m i x) :
    ∀ m, m < k → ∀ i, i ∈ˢ Is m → ∀ x, x ∈ˢ app (lfpTuple w k Is Φ m) i → P m i x := by
  intro m hm i hi x hx
  have hSmem := sepTuple_mem w k Is Φ P
  have hSle := sepTuple_le w k Is Φ P
  have hS : IsClosedTuple w k Is Φ (sepTuple w k Is Φ P) := by
    refine ⟨hSmem, fun m hm i hi => ?_⟩
    show _ ⊆ˢ app (famOf (fun i => dropTo (strictU w) (sep (app (lfpTuple w k Is Φ m) i) (P m i)))
      (Is m)) i
    rw [app_famOf hi]
    refine subset_dropTo (strictU_dropClosed w) (famSpace_app (lfpTuple_mem w k Is Φ m hm) hi)
      sep_subset (famSpace_app (hmaps _ hSmem m hm) hi) fun y hy => ?_
    refine mem_sep.mpr ⟨?_, hP m hm i hi y hy⟩
    exact lfpTuple_closed h hmono hmaps m hm i hi y
      (hmono _ _ hSmem (lfpTuple_mem w k Is Φ) hSle m hm i hi y hy)
  exact (mem_app_sepTuple_imp hi (lfpTuple_le hS m hm i hi x hx)).2

end Laws

/-! ## Congruence: the least tuple reads its operator and index sets below `k` only

A block's operator and index sets are DATA, read off whatever
presentation the consumer has; two presentations that agree on the `k`
components the tuple has agree on its carrier.  This is what lets a
reading be replaced by an equal one under the lfp without re-running
the fixed point.
-/

section Congr

variable {w k : Nat} {Is Is' : Nat → V} {Φ Φ' : (Nat → V) → Nat → V}

/-- Two presentations agreeing below `k` have the same closed tuples. -/
theorem isClosedTuple_congr (hIs : ∀ m, m < k → Is m = Is' m)
    (hΦ : ∀ X, InTupleSpace w k Is X → ∀ m, m < k → Φ X m = Φ' X m) {X : Nat → V} :
    IsClosedTuple w k Is Φ X ↔ IsClosedTuple w k Is' Φ' X := by
  have hsp : InTupleSpace w k Is X ↔ InTupleSpace w k Is' X := by
    constructor
    · intro h m hm; rw [← hIs m hm]; exact h m hm
    · intro h m hm; rw [hIs m hm]; exact h m hm
  constructor
  · rintro ⟨hX, hle⟩
    refine ⟨hsp.mp hX, fun m hm => ?_⟩
    rw [← hIs m hm, ← hΦ X hX m hm]; exact hle m hm
  · rintro ⟨hX, hle⟩
    have hX' := hsp.mpr hX
    refine ⟨hX', fun m hm => ?_⟩
    rw [hIs m hm, hΦ X hX' m hm]; exact hle m hm

/-- **The least tuple is a congruence** in the operator (on the tuple
space) and the index sets, below `k`. -/
theorem lfpTuple_congr (hIs : ∀ m, m < k → Is m = Is' m)
    (hΦ : ∀ X, InTupleSpace w k Is X → ∀ m, m < k → Φ X m = Φ' X m) {m : Nat} (hm : m < k) :
    lfpTuple w k Is Φ m = lfpTuple w k Is' Φ' m := by
  have hcl : (∃ L, IsClosedTuple w k Is Φ L) ↔ ∃ L, IsClosedTuple w k Is' Φ' L :=
    ⟨fun ⟨L, hL⟩ => ⟨L, (isClosedTuple_congr hIs hΦ).mp hL⟩,
      fun ⟨L, hL⟩ => ⟨L, (isClosedTuple_congr hIs hΦ).mpr hL⟩⟩
  by_cases h : ∃ L, IsClosedTuple w k Is Φ L
  · have h' := hcl.mp h
    refine famSpace_ext (lfpTuple_mem w k Is Φ m hm)
      (by rw [hIs m hm]; exact lfpTuple_mem w k Is' Φ' m hm) fun i hi => ?_
    have hi' : i ∈ˢ Is' m := by rw [← hIs m hm]; exact hi
    unfold lfpTuple
    rw [dite_eq_left h, dite_eq_left h', app_famOf hi, app_famOf hi']
    congr 1
    apply SetTheory.ext
    intro x
    rw [mem_sep, mem_sep]
    constructor
    · rintro ⟨-, hx⟩
      have hx' : ∀ X, IsClosedTuple w k Is' Φ' X → x ∈ˢ app (X m) i :=
        fun X hX => hx X ((isClosedTuple_congr hIs hΦ).mpr hX)
      exact ⟨hx' _ (Classical.choose_spec h'), hx'⟩
    · rintro ⟨-, hx⟩
      have hx' : ∀ X, IsClosedTuple w k Is Φ X → x ∈ˢ app (X m) i :=
        fun X hX => hx X ((isClosedTuple_congr hIs hΦ).mp hX)
      exact ⟨hx' _ (Classical.choose_spec h), hx'⟩
  · rw [lfpTuple_of_not h, lfpTuple_of_not (fun h' => h (hcl.mpr h')), hIs m hm]

end Congr

end ConLeche.SetTheory

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

end ConLeche.SetTheory
