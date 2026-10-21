module

public import ConLeche.SetTheory.Derive.Univ
import ConLeche.SetTheory.Derive.Lfp
@[expose] public section

/-!
# Least pre-fixed points of family functors (task #188, indexed)

The carrier of a directly installed recursive **family** `T : I → Sort w`
is the least pre-fixed point of its constructor-tower functor acting on
FAMILIES over the index-tuple set `I` with values in the strict
universe `strictU w` (`famSpace`), ordered pointwise (`FamLe`).  A
family is its graph over an inhabited `I` and the point over an empty
one (`famOf`), as the value reading has the type `I → Sort w`.
This is `Lfp.lean` fibrewise:

    lfpFamSet w I F = i ↦ {x ∈ L₀ i | ∀ closed X, x ∈ X i}

over a classically chosen closed family `L₀` (the empty family when
there is none — TOTAL, so the basis constant `lfpFam` needs no
certificate: `lfpFamSet_mem`).

**The fibre space is `strictU w`, not `univ w`** (task #342).  A sort
denotes the universe of types `univ w = tyU w`, which holds `{pt}` at
every level; a union of members of it (`{pt} ∪ ω`) or a member with `∅`
added (`{pt} ∪ {∅}`) need not be a type.  The strict universe is closed
under both (`strictU_famUnion_mem` for the unions),
and an inductive fibre above `Prop` is a set of tagged tuples, strict;
at `w = 0` the two universes agree.  A family of the space is a family
of types (`famSpace_app_univ`).

**A fibre space need not be closed under subsets.**  An intersection of
strict fibres can leave the strict universe: `F X i = if ∅ ∈ X i then
{ptTag, ∅} else {ptTag, {∅}}` has the closed fibres `{ptTag, ∅}` and
`{ptTag, {∅}}`, both strict, whose intersection `{ptTag}` is the point.
So the construction is stated over an arbitrary fibre space `C`
(`famSpaceIn`, `lfpFamIn`) and a fibre that leaves `C` is dropped to
`∅` (`dropTo`) — the value stays a family of `C` for EVERY functor.
What the laws read of `C` is `∅ ∈ C` and `DropClosed C`: a subset of a
member that is not a member has only `∅` among the members below it
(at the strict universe: such a subset is the point, and a type inside
the point is `∅`).  The drop is a no-op for a monotone functor mapping
the space into itself (the fibre is the raw intersection), which is every installed operator (`AccTuple.monoTuple`).

The same construction over `C = tg ℓ` is the recursor family's GRAPH
(`SetModel/GraphRec.lean`): a relation, whose fibres are sets of
values, not types.

Everything here is over the bare `SetTheory` interface; no syntax.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- The pointwise order on families over `I`. -/
def FamLe (I X Y : V) : Prop := ∀ i, i ∈ˢ I → app X i ⊆ˢ app Y i

theorem FamLe.refl (I X : V) : FamLe I X X := fun _ _ => Subset.refl _

theorem FamLe.trans {I X Y Z : V} (h₁ : FamLe I X Y) (h₂ : FamLe I Y Z) : FamLe I X Z :=
  fun i hi => Subset.trans (h₁ i hi) (h₂ i hi)

/-! ## Fibre spaces, and dropping a fibre that left the space -/

/-- `C` is closed under subsets. -/
def SubsetClosed (C : V) : Prop := ∀ y z, y ∈ˢ C → z ⊆ˢ y → z ∈ˢ C

/-- `C` is closed under subsets **up to a drop**: a subset `S` of a
member that is not itself a member has no member of `C` below it but
`∅`. -/
def DropClosed (C : V) : Prop :=
  ∀ Z S Y, Z ∈ˢ C → S ⊆ˢ Z → ¬ S ∈ˢ C → Y ∈ˢ C → Y ⊆ˢ S → Y = empty

theorem SubsetClosed.dropClosed {C : V} (h : SubsetClosed C) : DropClosed C :=
  fun _ _ _ hZ hSZ hS => absurd (h _ _ hZ hSZ) hS

open Classical in
/-- `S` if it is a member of `C`, `∅` otherwise. -/
noncomputable def dropTo (C S : V) : V := if S ∈ˢ C then S else empty

theorem dropTo_of_mem {C S : V} (h : S ∈ˢ C) : dropTo C S = S := by
  unfold dropTo; exact ite_eq_left h

theorem dropTo_mem {C : V} (hE : (empty : V) ∈ˢ C) (S : V) : dropTo C S ∈ˢ C := by
  unfold dropTo
  split
  · assumption
  · exact hE

theorem dropTo_subset (C S : V) : dropTo C S ⊆ˢ S := by
  unfold dropTo
  split
  · exact Subset.refl _
  · exact empty_subset _

theorem mem_of_mem_dropTo {C S x : V} (h : x ∈ˢ dropTo C S) : x ∈ˢ S := dropTo_subset C S x h

/-- **A member of `C` below a subset of a member is below its drop.** -/
theorem subset_dropTo {C Z S Y : V} (hD : DropClosed C) (hZ : Z ∈ˢ C) (hSZ : S ⊆ˢ Z)
    (hY : Y ∈ˢ C) (hYS : Y ⊆ˢ S) : Y ⊆ˢ dropTo C S := by
  by_cases hS : S ∈ˢ C
  · rw [dropTo_of_mem hS]; exact hYS
  · rw [hD Z S Y hZ hSZ hS hY hYS]; exact empty_subset _

/-! ## Families with fibres in a space

The least pre-fixed family of a functor on families over `I` with
fibres in `C`. -/

section In

open Classical in
/-- The families over `I` with fibres in `C`, as the value reading has
the type `I → C` (task #342, L16): the graphs over an inhabited `I`,
the point alone over an empty one (`SetModel/Ops`' `piV` over fibres
that are not truth values).  Over an empty index set a family is never
read, so nothing below depends on which single value it is; this one
makes a block's spelled families and its least fixed point agree. -/
noncomputable def famSpaceIn (C I : V) : V :=
  if ∃ i, i ∈ˢ I then piSet I fun _ => C else unitSet

open Classical in
/-- The family over `I` with fibres `G`: its graph over an inhabited
`I`, the point over an empty one (the value reading's abstraction
`lamV` at a body that is never the point, task #342, L16). -/
noncomputable def famOf (G : V → V) (I : V) : V :=
  if ∃ i, i ∈ˢ I then graph G I else pt

theorem famSpaceIn_of_ne {C I : V} (h : ∃ i, i ∈ˢ I) :
    famSpaceIn C I = piSet I fun _ => C := by
  unfold famSpaceIn; exact ite_eq_left h

theorem famSpaceIn_of_empty {C I : V} (h : ¬ ∃ i, i ∈ˢ I) : famSpaceIn C I = unitSet := by
  unfold famSpaceIn; exact ite_eq_right h

theorem famOf_of_ne {G : V → V} {I : V} (h : ∃ i, i ∈ˢ I) : famOf G I = graph G I := by
  unfold famOf; exact ite_eq_left h

theorem famOf_of_empty {G : V → V} {I : V} (h : ¬ ∃ i, i ∈ˢ I) : famOf G I = pt := by
  unfold famOf; exact ite_eq_right h

/-- β for a family, on the index set. -/
theorem app_famOf {G : V → V} {I i : V} (hi : i ∈ˢ I) : app (famOf G I) i = G i := by
  rw [famOf_of_ne ⟨i, hi⟩, app_graph hi]

theorem famOf_congr {G G' : V → V} {I : V} (h : ∀ i, i ∈ˢ I → G i = G' i) :
    famOf G I = famOf G' I := by
  unfold famOf; split
  · exact graph_congr h
  · rfl

/-- An `F`-closed family: a pre-fixed point of `app F` in the family
space. -/
def IsClosedFamIn (C I F X : V) : Prop :=
  X ∈ˢ famSpaceIn C I ∧ FamLe I (app F X) X

/-- Monotonicity of a family functor on the family space. -/
def MonoFamIn (C I F : V) : Prop :=
  ∀ X Y, X ∈ˢ famSpaceIn C I → Y ∈ˢ famSpaceIn C I → FamLe I X Y → FamLe I (app F X) (app F Y)

/-- The functor maps the family space into itself. -/
def MapsFamIn (C I F : V) : Prop :=
  ∀ X, X ∈ˢ famSpaceIn C I → app F X ∈ˢ famSpaceIn C I

theorem famSpaceIn_app {C I X i : V} (hX : X ∈ˢ famSpaceIn C I) (hi : i ∈ˢ I) : app X i ∈ˢ C := by
  rw [famSpaceIn_of_ne ⟨i, hi⟩] at hX
  exact app_mem_of_mem_piSet hX hi

/-- **η for a family**: a member of the family space is the family of
its applications. -/
theorem famOf_app_eq {C I X : V} (hX : X ∈ˢ famSpaceIn C I) : famOf (fun i => app X i) I = X := by
  by_cases h : ∃ i, i ∈ˢ I
  · rw [famSpaceIn_of_ne h] at hX
    rw [famOf_of_ne h]
    exact eq_graph_app_of_mem_piSet hX
  · rw [famSpaceIn_of_empty h, mem_unitSet_iff] at hX
    rw [famOf_of_empty h, hX]

/-- Members of the family space agreeing pointwise are equal. -/
theorem famSpaceIn_ext {C I X Y : V} (hX : X ∈ˢ famSpaceIn C I) (hY : Y ∈ˢ famSpaceIn C I)
    (h : ∀ i, i ∈ˢ I → app X i = app Y i) : X = Y := by
  rw [← famOf_app_eq hX, ← famOf_app_eq hY]
  exact famOf_congr h

/-- A family with fibres in `C` is in the family space. -/
theorem famOf_mem_famSpaceIn {C I : V} {G : V → V} (h : ∀ i, i ∈ˢ I → G i ∈ˢ C) :
    famOf G I ∈ˢ famSpaceIn C I := by
  by_cases hI : ∃ i, i ∈ˢ I
  · rw [famOf_of_ne hI, famSpaceIn_of_ne hI]
    exact graph_mem_piSet h
  · rw [famOf_of_empty hI, famSpaceIn_of_empty hI]
    exact mem_unitSet_iff.mpr rfl

/-- The family space grows with its fibre space. -/
theorem famSpaceIn_mono {C D I : V} (h : C ⊆ˢ D) : famSpaceIn C I ⊆ˢ famSpaceIn D I :=
  fun X hX => by
    rw [← famOf_app_eq hX]
    exact famOf_mem_famSpaceIn fun i hi => h _ (famSpaceIn_app hX hi)

open Classical in
/-- **The least pre-fixed family of `F` over `I`** — fibrewise the
intersection of the closed families when there is one (separated from
a chosen closed family), dropped to `∅` if it left `C`; the empty
family otherwise. -/
noncomputable def lfpFamIn (C I F : V) : V :=
  if h : ∃ L, IsClosedFamIn C I F L then
    famOf (fun i => dropTo C (sep (app (Classical.choose h) i)
      (fun x => ∀ X, IsClosedFamIn C I F X → x ∈ˢ app X i))) I
  else famOf (fun _ => empty) I

variable {C I F : V}

theorem forall_of_mem_app_lfpFamIn (h : ∃ L, IsClosedFamIn C I F L) {i x : V} (hi : i ∈ˢ I)
    (hx : x ∈ˢ app (lfpFamIn C I F) i) : ∀ X, IsClosedFamIn C I F X → x ∈ˢ app X i := by
  unfold lfpFamIn at hx
  rw [dite_eq_left h, app_famOf hi] at hx
  exact (mem_sep.mp (mem_of_mem_dropTo hx)).2

/-- A member of `C` below every closed family's fibre is below the
least family's. -/
theorem subset_app_lfpFamIn (hD : DropClosed C) (h : ∃ L, IsClosedFamIn C I F L) {i Y : V}
    (hi : i ∈ˢ I) (hY : Y ∈ˢ C) (hYX : ∀ X, IsClosedFamIn C I F X → Y ⊆ˢ app X i) :
    Y ⊆ˢ app (lfpFamIn C I F) i := by
  unfold lfpFamIn
  rw [dite_eq_left h, app_famOf hi]
  refine subset_dropTo hD (famSpaceIn_app (Classical.choose_spec h).1 hi) sep_subset hY
    fun x hx => mem_sep.mpr ⟨?_, fun X hX => hYX X hX x hx⟩
  exact hYX _ (Classical.choose_spec h) x hx

/-- **Leastness**: the least pre-fixed family lies in every closed
family. -/
theorem lfpFamIn_le {X : V} (hX : IsClosedFamIn C I F X) : FamLe I (lfpFamIn C I F) X :=
  fun _ hi _x hx => forall_of_mem_app_lfpFamIn ⟨X, hX⟩ hi hx X hX

/-- **Formation, unconditional**: the least pre-fixed family is in the
family space. -/
theorem lfpFamIn_mem (hE : (empty : V) ∈ˢ C) (I F : V) : lfpFamIn C I F ∈ˢ famSpaceIn C I := by
  unfold lfpFamIn
  split
  · exact famOf_mem_famSpaceIn fun _ _ => dropTo_mem hE _
  · exact famOf_mem_famSpaceIn fun _ _ => hE

/-- **Closure**: the least pre-fixed family is a pre-fixed point.  The
functor must map the space into itself: a fibre dropped to `∅` stays
closed because the functor's fibre there, a member of `C` below the
dropped set, is `∅` too. -/
theorem lfpFamIn_closed (hD : DropClosed C) (hE : (empty : V) ∈ˢ C)
    (h : ∃ L, IsClosedFamIn C I F L) (hmono : MonoFamIn C I F) (hmaps : MapsFamIn C I F) :
    FamLe I (app F (lfpFamIn C I F)) (lfpFamIn C I F) := by
  intro i hi
  refine subset_app_lfpFamIn hD h hi (famSpaceIn_app (hmaps _ (lfpFamIn_mem hE I F)) hi)
    fun X hX => ?_
  exact Subset.trans (hmono _ _ (lfpFamIn_mem hE I F) hX.1 (lfpFamIn_le hX) i hi) (hX.2 i hi)

/-- The least pre-fixed family is a post-fixed point. -/
theorem lfpFamIn_fixed (hD : DropClosed C) (hE : (empty : V) ∈ˢ C)
    (h : ∃ L, IsClosedFamIn C I F L) (hmono : MonoFamIn C I F) (hmaps : MapsFamIn C I F) :
    FamLe I (lfpFamIn C I F) (app F (lfpFamIn C I F)) := by
  have hmem := lfpFamIn_mem hE I F
  exact lfpFamIn_le ⟨hmaps _ hmem,
    hmono _ _ (hmaps _ hmem) hmem (lfpFamIn_closed hD hE h hmono hmaps)⟩

/-- The fixed-point equation, fibrewise. -/
theorem app_lfpFamIn_eq (hD : DropClosed C) (hE : (empty : V) ∈ˢ C)
    (h : ∃ L, IsClosedFamIn C I F L) (hmono : MonoFamIn C I F) (hmaps : MapsFamIn C I F)
    {i : V} (hi : i ∈ˢ I) :
    app (app F (lfpFamIn C I F)) i = app (lfpFamIn C I F) i :=
  Subset.antisymm (lfpFamIn_closed hD hE h hmono hmaps i hi)
    (lfpFamIn_fixed hD hE h hmono hmaps i hi)

end In

/-! ## The levels

What the family and tuple constructions (here, `LfpTuple.lean`, and the
accessibility construction `SetModel/Access.lean`) read of their fibre
space `strictU w`, beyond `∅ ∈ strictU w` (`empty_mem_strictU`): closure
under subsets up to a drop (`strictU_dropClosed`: a subset of a strict
set is strict or the point), unions of a family of members indexed by a
set of the axiomatic level (`strictU_famUnion_mem`: a union of strict
sets is strict), and adding `∅` as a member (`{∅}` is strict).
Nothing else of the level is read.  The universe of types `univ w` has
the first but not the other two. -/

/-- Every level of the axiomatic chain `tg` is closed under subsets. -/
theorem subsetClosed_tg (w : Nat) : SubsetClosed (tg w : V) :=
  fun _ _ hy hz => tg_mem_of_subset_mem hy hz

/-- A nonempty set inside the point is the point. -/
theorem eq_pt_of_subset_pt {Y y : V} (hY : Y ⊆ˢ pt) (hy : y ∈ˢ Y) : Y = pt := by
  refine Subset.antisymm hY fun z hz => ?_
  rw [mem_pt.mp hz, ← mem_pt.mp (hY y hy)]
  exact hy

/-- **The strict universe is closed under subsets up to a drop**: a
subset of a strict set that is not a type is the point, and the only
type inside the point is `∅`. -/
theorem strictU_dropClosed (w : Nat) : DropClosed (strictU w : V) := by
  intro Z S Y hZ hSZ hS hY hYS
  by_cases hw : w = 0
  · subst hw
    rw [strictU_zero, mem_univZero] at hZ hS
    exact absurd (hSZ.trans hZ) hS
  · obtain ⟨hZt, -, hZp⟩ := (mem_strictU_pos hw).mp hZ
    obtain ⟨-, hYne, -⟩ := (mem_strictU_pos hw).mp hY
    have hSpt : S = pt := Classical.byContradiction fun hne => hS ((mem_strictU_pos hw).mpr
      ⟨subsetClosed_tg w _ _ hZt hSZ, hne, fun h => hZp (hSZ _ h)⟩)
    subst hSpt
    exact Subset.antisymm (fun y hy => absurd (eq_pt_of_subset_pt hYS hy) hYne)
      (empty_subset _)

/-- **A union of strict types of a positive level**, indexed by a set
of the axiomatic level, is one: a union of strict sets is strict. -/
theorem strictU_famUnion_mem {w : Nat} (hw : w ≠ 0) {A : V} {F : V → V} (hA : A ∈ˢ (tg w : V))
    (hF : ∀ a, a ∈ˢ A → F a ∈ˢ (strictU w : V)) : sUnion (image F A) ∈ˢ (strictU w : V) := by
  refine (mem_strictU_pos hw).mpr ⟨(tg_isTGUniverse hw).famUnion_mem hA fun a ha =>
    ((mem_strictU_pos hw).mp (hF a ha)).1, fun he => ?_, fun hp => ?_⟩
  · have : (ptTag : V) ∈ˢ sUnion (image F A) := he ▸ ptTag_mem_pt
    obtain ⟨y, hy, hty⟩ := mem_sUnion.mp this
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hy
    exact ((mem_strictU_pos hw).mp (hF a ha)).2.1
      (eq_pt_of_subset_pt (fun z hz => he ▸ mem_sUnion.mpr ⟨_, hy, hz⟩) hty)
  · obtain ⟨y, hy, hpy⟩ := mem_sUnion.mp hp
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hy
    exact ((mem_strictU_pos hw).mp (hF a ha)).2.2 hpy

/-! ## Families of a level -/

/-- The family space over `I`: families into the strict universe
`strictU w`. -/
noncomputable def famSpace (w : Nat) (I : V) : V := famSpaceIn (strictU w) I

theorem famSpace_app {w : Nat} {I X i : V} (hX : X ∈ˢ famSpace w I) (hi : i ∈ˢ I) :
    app X i ∈ˢ (strictU w : V) :=
  famSpaceIn_app hX hi

/-- A family of the space is a family of types. -/
theorem famSpace_subset_univ (w : Nat) (I : V) : famSpace w I ⊆ˢ famSpaceIn (univ w) I :=
  famSpaceIn_mono (strictU_subset_univ w)

/-- A fibre of a family of the space is a type. -/
theorem famSpace_app_univ {w : Nat} {I X i : V} (hX : X ∈ˢ famSpace w I) (hi : i ∈ˢ I) :
    app X i ∈ˢ (univ w : V) :=
  mem_univ_of_mem_strictU (famSpace_app hX hi)

/-- Members of the family space agreeing pointwise are equal. -/
theorem famSpace_ext {w : Nat} {I X Y : V} (hX : X ∈ˢ famSpace w I) (hY : Y ∈ˢ famSpace w I)
    (h : ∀ i, i ∈ˢ I → app X i = app Y i) : X = Y :=
  famSpaceIn_ext hX hY h

/-- A family with fibres in `strictU w` is in the family space. -/
theorem famOf_mem_famSpace {w : Nat} {I : V} {G : V → V}
    (h : ∀ i, i ∈ˢ I → G i ∈ˢ (strictU w : V)) :
    famOf G I ∈ˢ famSpace w I :=
  famOf_mem_famSpaceIn h

/-- **The least pre-fixed family of `F` over `I`** at level `w`. -/
noncomputable def lfpFamSet (w : Nat) (I F : V) : V := lfpFamIn (strictU w) I F

/-- **Formation, unconditional**: the least pre-fixed family is in the
family space. -/
theorem lfpFamSet_mem (w : Nat) (I F : V) : lfpFamSet w I F ∈ˢ famSpace w I :=
  lfpFamIn_mem (empty_mem_strictU w) I F

end ConLeche.SetTheory
