module

public import ConLeche.Model.Claims
import ConLeche.Semantics.BasisType

public section

/-!
# `WellDenoted` at every built-in type (task #161, ENDGAME E)

Every pinned type's spelled type reading is graded
(`WellDenoted_bconst_type`) and a type (`IsTy_bconst_type`).

`WellDenoted`'s `.app` clause asks a slot `∃ v A B, f ∈ˢ piR v A B ∧
a ∈ˢ A ∧ (v = 0 → …) ∧ (v ≠ 0 → IsTy A)`.  At a basis constant's head
the slot is read off `bval_mem_type` at `BConst.typeAV`'s own binder:
the function space is `piV`, whose regime numeral `propN` comes with
its fibre fact (`propN_eq_zero`), so nothing is chosen
(`bconst_app_data`/`_data2`/`_data3`/`_data4`, `slot_of_mem_piV`).
The one bespoke supplier is `quotMk_mem_quot` (`Quot.ind`'s motive at a
`Quot.mk` spine).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term SetTheory

universe w

variable {V : Type w} [SetTheory V]

/-! ## The two grading predicates at every built-in type -/

variable (V)

/-! ## `lfpTuple k`'s type

The block carrier's constant is the one whose type is a *tower*, so its
grading is not the `simp` battery's: the family tower's grading needs
the ambient variable to be an index-set tuple — which is exactly what
the outer `Π`'s own clause hands it. -/

/-- **`lfpTuple k`'s type is graded**: the family tower's projections
are graded because the outer `Π`'s clause hands them an index-set
tuple. -/
theorem WellDenoted_lfpTuple (k : Nat) (us : List Nat) (ρ : Nat → V) :
    WellDenoted V ρ (BConst.typeAV (.lfpTuple k) us) := by
  show WellDenoted V ρ (.pi (tupleSortsAV k us)
    (.pi (.pi (tupleFamsAV k us 0) (tupleFamsAV k us 1)) (tupleFamsAV k us 1)))
  rw [WellDenoted_pi]
  refine ⟨(tupleSortsAV_facts V k us ρ).2,
    by rw [(tupleSortsAV_facts V k us ρ).1]; exact IsTy_tupleSortsSpace V k us,
    fun Is hIs => ?_, fun _ _ => IsTy_piV⟩
  rw [(tupleSortsAV_facts V k us ρ).1] at hIs
  have h0 : WellDenoted V (cons Is ρ) (tupleFamsAV k us 0) :=
    (tupleFamsAV_facts V (j := 0) (ρ := cons Is ρ) hIs).2
  have h1 : ∀ x : V, WellDenoted V (cons x (cons Is ρ)) (tupleFamsAV k us 1) :=
    fun x => (tupleFamsAV_facts V (j := 1) (ρ := cons x (cons Is ρ)) hIs).2
  have t0 : IsTy (interp V (cons Is ρ) (tupleFamsAV k us 0)) := by
    rw [(tupleFamsAV_facts V (j := 0) (ρ := cons Is ρ) hIs).1]
    exact IsTy_tupleFamsSpace V hIs
  have t1 : ∀ x : V, IsTy (interp V (cons x (cons Is ρ)) (tupleFamsAV k us 1)) := fun x => by
    rw [(tupleFamsAV_facts V (j := 1) (ρ := cons x (cons Is ρ)) hIs).1]
    exact IsTy_tupleFamsSpace V hIs
  rw [WellDenoted_pi]
  refine ⟨?_, IsTy_piV, fun F _ => h1 F, fun F _ => t1 F⟩
  rw [WellDenoted_pi]
  exact ⟨h0, t0, fun x _ => h1 x, fun x _ => t1 x⟩

/-- The slot of a member of a `piV` at an argument of its domain, the
domain a type: the numeral is `propN`'s, with its fibre fact. -/
theorem slot_of_mem_piV {f S a : V} {F : V → V} (hf : f ∈ˢ piV S F) (ha : a ∈ˢ S)
    (hS : IsTy S) :
    ∃ (w : Nat) (S' : V) (F' : V → V), f ∈ˢ piR w S' F' ∧
      a ∈ˢ S' ∧ (w = 0 → ∀ x, x ∈ˢ S' → F' x ∈ˢ (univZero : V)) ∧ (w ≠ 0 → IsTy S') :=
  ⟨propN S F, S, F, hf, ha, propN_eq_zero.mp, fun _ => hS⟩

/-- A member of a function space into one universe, applied on its
domain, is a type. -/
theorem IsTy_app_piV_univ {u : Nat} {f a S : V}
    (hf : f ∈ˢ piV S fun _ => (univ u : V)) (ha : a ∈ˢ S) : IsTy (app f a) :=
  IsTy_of_mem_univ (app_mem_piV hf ha)

/-- A member of a two-binder function space into one universe, applied
twice on its domains, is a type (a relation's value). -/
theorem IsTy_app2_piV_univ {u : Nat} {R a b A : V} {A2 : V → V}
    (hR : R ∈ˢ piV A fun x => piV (A2 x) fun _ => (univ u : V)) (ha : a ∈ˢ A)
    (hb : b ∈ˢ A2 a) : IsTy (app (app R a) b) := by
  have h1 : app R a ∈ˢ piV (A2 a) fun _ => (univ u : V) := app_mem_piV hR ha
  exact IsTy_of_mem_univ (app_mem_piV h1 hb)

/-- The slot of a two-binder member applied once (a relation applied to
its first argument). -/
theorem slot_app_piV {R a b A : V} {A2 : V → V} {B2 : V → V → V}
    (hR : R ∈ˢ piV A fun x => piV (A2 x) (B2 x)) (ha : a ∈ˢ A) (hb : b ∈ˢ A2 a)
    (hS : IsTy (A2 a)) :
    ∃ (w : Nat) (S' : V) (F' : V → V), app R a ∈ˢ piR w S' F' ∧
      b ∈ˢ S' ∧ (w = 0 → ∀ x, x ∈ˢ S' → F' x ∈ˢ (univZero : V)) ∧ (w ≠ 0 → IsTy S') :=
  slot_of_mem_piV V (app_mem_piV hR ha) hb hS

/-- **The `.app` clause's witness at a basis constant's head.**  The
function space is `typeAV`'s own outer binder's reading, the membership
is `bval_mem_type` at that binder. -/
theorem bconst_app_data (c : BConst) (us : List Nat) (ρ : Nat → V)
    {A B : Term} (h : BConst.typeAV c us = .pi A B)
    {a : V} (ha : a ∈ˢ interp V ρ A) (hS : IsTy (interp V ρ A)) :
    ∃ (w : Nat) (S : V) (F : V → V), bval V c us ∈ˢ piR w S F ∧
      a ∈ˢ S ∧ (w = 0 → ∀ x, x ∈ˢ S → F x ∈ˢ (univZero : V)) ∧ (w ≠ 0 → IsTy S) := by
  have hm := bval_mem_type V c us ρ
  rw [h, interp_pi] at hm
  exact slot_of_mem_piV V hm ha hS

/-- The same one binder in: a basis constant applied to its first
argument (`app_mem_piV`, no fibre premise). -/
theorem bconst_app_data2 (c : BConst) (us : List Nat) (ρ : Nat → V)
    {A A2 B2 : Term}
    (h : BConst.typeAV c us = .pi A (.pi A2 B2))
    {a1 : V} (ha1 : a1 ∈ˢ interp V ρ A)
    {a : V} (ha : a ∈ˢ interp V (cons a1 ρ) A2) (hS : IsTy (interp V (cons a1 ρ) A2)) :
    ∃ (w : Nat) (S : V) (F : V → V),
      app (bval V c us) a1 ∈ˢ piR w S F ∧
      a ∈ˢ S ∧ (w = 0 → ∀ x, x ∈ˢ S → F x ∈ˢ (univZero : V)) ∧ (w ≠ 0 → IsTy S) := by
  have hm := bval_mem_type V c us ρ
  rw [h, interp_pi] at hm
  have h1 := app_mem_piV hm ha1
  rw [interp_pi] at h1
  exact slot_of_mem_piV V h1 ha hS

/-- Two binders in: the constant applied to its first two arguments. -/
theorem bconst_app_data3 (c : BConst) (us : List Nat) (ρ : Nat → V)
    {A A2 A3 B3 : Term}
    (h : BConst.typeAV c us = .pi A (.pi A2 (.pi A3 B3)))
    {a1 : V} (ha1 : a1 ∈ˢ interp V ρ A)
    {a2 : V} (ha2 : a2 ∈ˢ interp V (cons a1 ρ) A2)
    {a : V} (ha : a ∈ˢ interp V (cons a2 (cons a1 ρ)) A3)
    (hS : IsTy (interp V (cons a2 (cons a1 ρ)) A3)) :
    ∃ (w : Nat) (S : V) (F : V → V),
      app (app (bval V c us) a1) a2 ∈ˢ piR w S F ∧
      a ∈ˢ S ∧ (w = 0 → ∀ x, x ∈ˢ S → F x ∈ˢ (univZero : V)) ∧ (w ≠ 0 → IsTy S) := by
  have hm := bval_mem_type V c us ρ
  rw [h, interp_pi] at hm
  have h1 := app_mem_piV hm ha1
  rw [interp_pi] at h1
  have h2 := app_mem_piV h1 ha2
  rw [interp_pi] at h2
  exact slot_of_mem_piV V h2 ha hS

/-- Three binders in: the constant applied to its first three
arguments.  The basis *recursors*' RHS towers apply their
head four and five deep (`Nat.rec`'s successor rule, `Quot.lift`). -/
theorem bconst_app_data4 (c : BConst) (us : List Nat) (ρ : Nat → V)
    {A A2 A3 A4 B4 : Term}
    (h : BConst.typeAV c us
      = .pi A (.pi A2 (.pi A3 (.pi A4 B4))))
    {a1 : V} (ha1 : a1 ∈ˢ interp V ρ A)
    {a2 : V} (ha2 : a2 ∈ˢ interp V (cons a1 ρ) A2)
    {a3 : V} (ha3 : a3 ∈ˢ interp V (cons a2 (cons a1 ρ)) A3)
    {a : V} (ha : a ∈ˢ interp V (cons a3 (cons a2 (cons a1 ρ))) A4)
    (hS : IsTy (interp V (cons a3 (cons a2 (cons a1 ρ))) A4)) :
    ∃ (w : Nat) (S : V) (F : V → V),
      app (app (app (bval V c us) a1) a2) a3 ∈ˢ piR w S F ∧
      a ∈ˢ S ∧ (w = 0 → ∀ x, x ∈ˢ S → F x ∈ˢ (univZero : V)) ∧ (w ≠ 0 → IsTy S) := by
  have hm := bval_mem_type V c us ρ
  rw [h, interp_pi] at hm
  have h1 := app_mem_piV hm ha1
  rw [interp_pi] at h1
  have h2 := app_mem_piV h1 ha2
  rw [interp_pi] at h2
  have h3 := app_mem_piV h2 ha3
  rw [interp_pi] at h3
  exact slot_of_mem_piV V h3 ha hS

/-- `Quot.mk`'s spine inhabits its quotient — the argument membership
`quotInd`'s and `quotSound`'s motive rows want. -/
theorem quotMk_mem_quot {u : Nat} {A R a : V} (hA : A ∈ˢ (univ u : V))
    (hR : R ∈ˢ relSpace V A) (ha : a ∈ˢ A) :
    app (app (app (quotMkV V u) A) R) a ∈ˢ app (app (quotV V u) A) R := by
  rw [quotMkV_app V hA hR ha, quotV_app V hA hR]
  exact quotClass_mem ha

set_option maxHeartbeats 4000000 in
theorem WellDenoted_bconst_type (c : BConst) (us : List Nat) (ρ : Nat → V) :
    WellDenoted V ρ (BConst.typeAV c us) := by
  cases c
  case lfpTuple k => exact WellDenoted_lfpTuple V k us ρ
  all_goals
    simp +contextual +decide only [BConst.typeAV, arrowA, relAV, negTyAV,
      natTyAV, natZeroAV, natSuccAV, punitAV, emptyT,
      psigmaAV, quotAV, quotMkAV, Term.mkAppN, Term.lift,
      Term.liftN, WellDenoted_pi, WellDenoted_app, WellDenoted_eqE,
      WellDenoted_bvar, WellDenoted_sort, WellDenoted_const,
      interp_pi, interp_app, interp_eqE, interp_sort,
      interp_const, interp_bvar, cons_zero, cons_succ,
      true_and, and_self, implies_true, ite_false]
  all_goals
    (repeat' first
      | exact IsTy_piV
      | exact IsTy_piR _ _ _
      | exact IsTy_univ _
      | exact IsTy_omega
      | exact IsTy_empty
      | exact IsTy_eqv _ _
      | exact IsTy_of_mem_univ ‹_›
      | exact IsTy_of_mem_univ (unitSetAt_mem_univ _)
      | exact IsTy_quotV_app V ‹_› ‹_›
      | exact IsTy_psigmaV_app V ‹_› ‹_›
      | exact IsTy_of_mem_univ (app_mem_piR_pos (Nat.succ_ne_zero _) ‹_› ‹_›)
      | exact IsTy_of_mem_univ (app_mem_piR_pos Nat.one_ne_zero ‹_› ‹_›)
      | exact IsTy_of_mem_univ (app_mem_piR_pos (Nat.succ_ne_zero _) ‹_› natzero_mem)
      | exact IsTy_of_mem_univ (app_mem_piR_pos (Nat.succ_ne_zero _) ‹_›
          (app_mem_piR_pos Nat.one_ne_zero (natSuccV_mem V) ‹_›))
      | exact IsTy_of_mem_univ (app_mem_piR_pos Nat.one_ne_zero ‹_›
          (quotMk_mem_quot V ‹_› ‹_› ‹_›))
      | (apply IsTy_app_piV_univ V <;> first
          | assumption | exact natzero_mem
          | exact app_mem_piR_pos Nat.one_ne_zero (natSuccV_mem V) (by assumption))
      | (apply IsTy_app2_piV_univ V <;> assumption)
      | (apply slot_app_piV V <;> first
          | assumption | exact IsTy_of_mem_univ (by assumption))
      | (apply slot_of_mem_piV V <;> first
          | assumption | exact natzero_mem
          | exact app_mem_piR_pos Nat.one_ne_zero (natSuccV_mem V) (by assumption)
          | exact IsTy_univ _ | exact IsTy_piV | exact IsTy_omega
          | exact IsTy_empty | exact IsTy_of_mem_univ (by assumption))
      | exact ⟨_, _, _, ‹_›, ‹_›, fun h => absurd h (Nat.succ_ne_zero _),
          fun _ => IsTy_of_mem_univ ‹_›⟩
      | refine ⟨_, _, _, ‹_›, ‹_›, fun h => absurd h (Nat.succ_ne_zero _), fun _ => ?_⟩
      | refine ⟨_, _, _, ‹_›, ‹_›, fun h => absurd h Nat.one_ne_zero, fun _ => ?_⟩
      | refine ⟨_, _, _, ‹_›, natzero_mem, fun h => absurd h (Nat.succ_ne_zero _),
          fun _ => ?_⟩
      | refine ⟨_, _, _, ‹_›, pt_mem_unitSet, fun h => absurd h (Nat.succ_ne_zero _),
          fun _ => ?_⟩
      | refine ⟨_, _, _, ‹_›,
          app_mem_piR_pos Nat.one_ne_zero (natSuccV_mem V) ‹_›,
          fun h => absurd h (Nat.succ_ne_zero _), fun _ => ?_⟩
      | refine ⟨_, _, _, ‹_›, ‹_›,
          fun hz _ _ => mem_univZero_of_zero V hz ‹_›, fun _ => ?_⟩
      | (refine bconst_app_data V _ _ ρ rfl ?_ ?_ <;>
          (first | assumption | exact IsTy_univ _ | exact IsTy_piV | exact IsTy_omega |
            exact IsTy_of_mem_univ ‹_›))
      | (refine bconst_app_data2 V _ _ ρ rfl ?_ ?_ ?_ <;>
          (first | assumption | exact IsTy_univ _ | exact IsTy_piV | exact IsTy_omega |
            exact IsTy_of_mem_univ ‹_›))
      | (refine bconst_app_data3 V _ _ ρ rfl ?_ ?_ ?_ ?_ <;>
          (first | assumption | exact IsTy_univ _ | exact IsTy_piV | exact IsTy_omega |
            exact IsTy_of_mem_univ ‹_›))
      | apply And.intro
      | intro _
      | trivial)
  -- `Quot.ind`'s motive applied at a `Quot.mk` spine, and at a class
  all_goals first
    | exact slot_of_mem_piV V ‹_› (quotMk_mem_quot V ‹_› ‹_› ‹_›) (IsTy_quotV_app V ‹_› ‹_›)
    | exact IsTy_app_piV_univ V ‹_› (quotMk_mem_quot V ‹_› ‹_› ‹_›)
    | exact slot_of_mem_piV V ‹_› ‹_› (IsTy_quotV_app V ‹_› ‹_›)

/-- **Every built-in constant's type reads to a type**: a
dependent function space, a universe, `ω` (`Nat.zero : Nat`) or a unit type
(`PUnit.unit : PUnit`). -/
theorem IsTy_bconst_type (c : BConst) (us : List Nat) (ρ : Nat → V) :
    IsTy (interp V ρ (BConst.typeAV c us)) := by
  cases c <;> first
    | exact IsTy_piV
    | exact IsTy_univ _
    | exact IsTy_omega
    | exact IsTy_of_mem_univ (unitSetAt_mem_univ _)

/-- **Every built-in constant's type is a graded type.** -/
theorem WellDenotedTy_bconst_type (c : BConst) (us : List Nat) (ρ : Nat → V) :
    WellDenotedTy V ρ (BConst.typeAV c us) :=
  ⟨WellDenoted_bconst_type V c us ρ, IsTy_bconst_type V c us ρ⟩

end ConLeche.Model
