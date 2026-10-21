module

public import ConLeche.Semantics.Inductives.HoleMono

@[expose] public section

/-!
# Accessibility in the holes, case by case

The twin of `HoleMono.lean` for the closure witness (W): a reading is ACCESSIBLE
along a frame relation `R` when every SMALL element (`x ∈ tg w`) has a
SUPPORT — a family, indexed by a subset of a BOUND `A ρ`, of ADMISSIBLE
items `(h, vs, y)` held by the frame (`Holds`: `y` lies in the value at
position `h` applied to the spine `vs`; admissible: `Q h vs.length`, a
hole at its full arity) — such that the element lies in the reading at
every related frame holding the items (`AccOn`).  At the top the
relation relates the hole frames of any two tuples of the space, and the
items are the tuple's occurrences: `SetModel/Access.lean`'s `AccTuple`,
which `closed_of_acc` turns into (W).

`R` is a relation of COMPARABLE frames (holes vary freely), not an
order: the support, not an inclusion of holes, carries the element to
the target frame.  Under a binder whose domain may read the holes the
relation is `FrameRel.underBoth` (the bound value in the domain at both
frames): a field telescope puts an earlier field's value into the target
frame by that value's own support.

**Sizes.**  The bound must be a set of the level (`SizeOn`), uniformly:
only small elements need a support (the element guard), so a Π's bound
glues its values' supports over its domain only where that domain is
small — which it is as soon as one small graph inhabits the Π.  The one
member that does not make the domain small is the point (a Π whose
fibres all hold it, over a domain of any size).  Its support is empty:
at a `Type`-valued block a reading holding the point at one frame holds
it at every related frame (`PtOn`), since the holes at their full arity
never hold the point there (`PtFreeOn`: their values are strict sets),
and a Π holds it exactly when every fibre does (`pt_mem_piV_iff`, the
fibres being types — the grading).

**At `w = 0`** (a `Prop`-valued block, task #327) nothing is sized: the
guard `SmallAt 0` is vacuous, every element has a support, and a Π glues
one support per domain value over a domain of any size.

**The value reading.**  A Π reads `piV`: its regime is its fibres'.  A
member transported to another frame lies in the Π there as soon as its
applications land in the fibres there and the fibres at both frames are
types (`mem_piV_of_app`); the caller supplies that from the grading of
the walked field (`FibTyOn`).

| case | accessibility | bound | the point |
|---|---|---|---|
| a hole-free reading | `ConstOn.accOn` | `∅` | `ConstOn.ptOn` |
| the `whnf` step | `AccOn.of_eqOn` | the reduct's | `PtOn.of_eqOn` |
| Π, hole-free domain | `AccOn.pi` | `piBound` | `PtOn.pi` |
| a hole at hole-free arguments | `AccOn.holeApp` | `{pt}` | `PtOn.holeApp` |

The bound is a FUNCTION of the frame: a Π's domain may read earlier
fields and binders.  Its uniformity across the tuples of the space is a
separate, all-frames fact (`InvOn`: the bound reads only given
positions), which the run inversion states off the walk's output and
`TeleAcc.lean` makes uniform along a field telescope.
-/

namespace ConLeche.Semantics
open ConLeche.Term (Term)
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## Support items and the predicate -/

/-- A support item: a frame position, an argument spine, a value. -/
abbrev Occ (V : Type uv) := Nat × List V × V

/-- **The frame holds the item**: the value lies in the position's value
applied to the spine. -/
def Holds (ρ : Nat → V) (o : Occ V) : Prop := o.2.2 ∈ˢ o.2.1.foldl app (ρ o.1)

/-- The admissible items: at the positions and spine lengths `Q`. -/
def Adm (Q : Nat → Nat → Prop) (o : Occ V) : Prop := Q o.1 o.2.1.length

/-- **Small at the level**: a member of `tg w` at a `Type`-valued
level; at `w = 0` nothing is asked (a `Prop`-valued block's fields range
over any universe, and no bound is sized there — task #327). -/
def SmallAt (w : Nat) (x : V) : Prop := w ≠ 0 → x ∈ˢ (tg w : V)

theorem SmallAt.zero (x : V) : SmallAt 0 x := fun h => absurd rfl h

/-- **Accessible along `R` with bound `A`, admissible items `Q`, at the
level `w`** (see the module docstring). -/
def AccOn (w : Nat) (Q : Nat → Nat → Prop) (R : FrameRel V) (A : (Nat → V) → V)
    (a : Term) : Prop :=
  ∀ ρ ρ₀, R ρ ρ₀ → ∀ x, SmallAt w x → x ∈ˢ interp V ρ a →
    ∃ (B : V) (g : V → Occ V), B ⊆ˢ A ρ ∧ (∀ b, b ∈ˢ B → Adm Q (g b) ∧ Holds ρ (g b)) ∧
      ∀ ρ', R ρ ρ' → (∀ b, b ∈ˢ B → Holds ρ' (g b)) → x ∈ˢ interp V ρ' a

/-- **The bound is a set of the level** at every frame of the relation. -/
def SizeOn (w : Nat) (R : FrameRel V) (A : (Nat → V) → V) : Prop :=
  ∀ ρ ρ₀, R ρ ρ₀ → SmallAt w (A ρ)

/-- **The bound reads only the positions `M`.** -/
def InvOn (M : Nat → Prop) (A : (Nat → V) → V) : Prop :=
  ∀ ρ ρ' : Nat → V, (∀ i, M i → ρ i = ρ' i) → A ρ = A ρ'

/-- **The point is stable**: a reading holding the point at a frame holds
it at every related frame. -/
def PtOn (R : FrameRel V) (a : Term) : Prop :=
  ∀ ρ ρ', R ρ ρ' → (pt : V) ∈ˢ interp V ρ a → (pt : V) ∈ˢ interp V ρ' a

/-- **Point-free holes**: an admissible position, applied at its arity,
never holds the point at a frame of the relation. -/
def PtFreeOn (Q : Nat → Nat → Prop) (R : FrameRel V) : Prop :=
  ∀ ρ ρ₀, R ρ ρ₀ → ∀ (i : Nat) (vs : List V), Q i vs.length → ¬ (pt : V) ∈ˢ vs.foldl app (ρ i)

/-- **The fibres are types** at both frames of every related pair (the
grading of a walked Π's body, at satisfying frames). -/
def FibTyOn (R : FrameRel V) (D B : Term) : Prop :=
  ∀ ρ ρ', R ρ ρ' → (∀ x, x ∈ˢ interp V ρ D → IsTy (interp V (cons x ρ) B)) ∧
    (∀ x, x ∈ˢ interp V ρ' D → IsTy (interp V (cons x ρ') B))

/-- The admissible items one binder down: never the bound variable. -/
def shiftQ (Q : Nat → Nat → Prop) : Nat → Nat → Prop
  | 0, _ => False
  | i + 1, n => Q i n

namespace FrameRel

/-- **Under a binder of domain `A`, the value in the domain at both
frames.** -/
def underBoth (R : FrameRel V) (A : Term) : FrameRel V :=
  fun σ σ' => ∃ x ρ ρ', σ = cons x ρ ∧ σ' = cons x ρ' ∧ R ρ ρ' ∧
    x ∈ˢ interp V ρ A ∧ x ∈ˢ interp V ρ' A

/-- A symmetric relation. -/
def Symm (R : FrameRel V) : Prop := ∀ ρ ρ', R ρ ρ' → R ρ' ρ

theorem AgreesOff.underBoth {R : FrameRel V} {P : Nat → Prop} (h : R.AgreesOff P)
    (A : Term) : (R.underBoth A).AgreesOff (shiftP P) := by
  rintro _ _ ⟨x, ρ, ρ', rfl, rfl, hR, -, -⟩
  exact agreeOff_cons (h ρ ρ' hR) x

theorem Symm.underBoth {R : FrameRel V} (h : R.Symm) (A : Term) : (R.underBoth A).Symm := by
  rintro _ _ ⟨x, ρ, ρ', rfl, rfl, hR, hx, hx'⟩
  exact ⟨x, ρ', ρ, rfl, rfl, h ρ ρ' hR, hx', hx⟩

end FrameRel

/-! ## Generic facts -/

/-- **Point-freeness survives a binder.** -/
theorem PtFreeOn.underBoth {Q : Nat → Nat → Prop} {R : FrameRel V} (h : PtFreeOn Q R)
    (A : Term) : PtFreeOn (shiftQ Q) (R.underBoth A) := by
  rintro _ _ ⟨x, ρ, ρ₀, rfl, rfl, hR, -, -⟩ i vs hQ
  cases i with
  | zero => exact hQ.elim
  | succ i => exact h ρ ρ₀ hR i vs hQ

/-! ## The cases: accessibility -/

theorem SizeOn.const {w : Nat} {R : FrameRel V} {c : V} (hc : c ∈ˢ (tg w : V)) :
    SizeOn w R (fun _ => c) := fun _ _ _ _ => hc

/-- **A hole-free reading** is accessible with the empty bound. -/
theorem ConstOn.accOn {w : Nat} {Q : Nat → Nat → Prop} {R : FrameRel V} {a : Term}
    (h : ConstOn R a) : AccOn w Q R (fun _ => empty) a := by
  intro ρ ρ₀ _ x _ hx
  refine ⟨empty, fun _ => (0, [], empty), Subset.refl _,
    fun b hb => absurd hb (not_mem_empty b), fun ρ' hR' _ => ?_⟩
  rw [← h ρ ρ' hR']
  exact hx

/-- **The `whnf` step.** -/
theorem AccOn.of_eqOn {w : Nat} {Q : Nat → Nat → Prop} {R : FrameRel V} {P : (Nat → V) → Prop}
    (hdom : ∀ ρ ρ', R ρ ρ' → P ρ ∧ P ρ') {A : (Nat → V) → V} {a b : Term}
    (heq : ∀ ρ, P ρ → interp V ρ a = interp V ρ b) (hb : AccOn w Q R A b) : AccOn w Q R A a := by
  intro ρ ρ₀ hR x hxw hx
  rw [heq ρ (hdom ρ ρ₀ hR).1] at hx
  obtain ⟨B, g, hB, hg, hs⟩ := hb ρ ρ₀ hR x hxw hx
  exact ⟨B, g, hB, hg, fun ρ' hR' h' => by rw [heq ρ' (hdom ρ ρ' hR').2]; exact hs ρ' hR' h'⟩

/-- Skolemisation of supports over a set of positions. -/
theorem skolem_occ {S : V} {Q : V → V → (V → Occ V) → Prop}
    (h : ∀ a, a ∈ˢ S → ∃ B g, Q a B g) :
    ∃ (Bf : V → V) (gf : V → V → Occ V), ∀ a, a ∈ˢ S → Q a (Bf a) (gf a) := by
  classical
  refine ⟨fun a => if h' : a ∈ˢ S then Classical.choose (h a h') else empty,
    fun a => if h' : a ∈ˢ S then Classical.choose (Classical.choose_spec (h a h'))
      else fun _ => (0, [], empty), fun a ha => ?_⟩
  simp only [dite_eq_left ha]
  exact Classical.choose_spec (Classical.choose_spec (h a ha))

/-- An item one binder down, seen above it. -/
def Occ.down (o : Occ V) : Occ V := (o.1 - 1, o.2)

theorem holds_cons_down {x : V} {ρ : Nat → V} {o : Occ V} (h0 : o.1 ≠ 0) :
    Holds (cons x ρ) o ↔ Holds ρ o.down := by
  obtain ⟨i, vs, y⟩ := o
  cases i with
  | zero => exact absurd rfl h0
  | succ i => rfl

/-- A small function's domain and values are small. -/
theorem small_of_mem_piSet {w : Nat} (hw : w ≠ 0) {D f : V} {F : V → V} (hf : f ∈ˢ piSet D F)
    (hfw : f ∈ˢ (tg w : V)) : D ∈ˢ (tg w : V) ∧ ∀ d, d ∈ˢ D → app f d ∈ˢ (tg w : V) := by
  have hU := tg_isTGUniverse (V := V) hw
  have hpair : ∀ d, d ∈ˢ D → kpair d (app f d) ∈ˢ f := by
    intro d hd
    rw [← eq_graph_app_of_mem_piSet hf]
    exact mem_graph.mpr ⟨d, hd, by rw [eq_graph_app_of_mem_piSet hf]⟩
  have hkp : ∀ d, d ∈ˢ D → kpair d (app f d) ∈ˢ (tg w : V) :=
    fun d hd => hU.transitive hfw (hpair d hd)
  refine ⟨?_, fun d hd => ?_⟩
  · refine hU.mem_of_subset_mem (hU.sUnion_mem (hU.sUnion_mem hfw)) fun d hd => ?_
    exact mem_sUnion.mpr ⟨sing d, mem_sUnion.mpr ⟨kpair d (app f d), hpair d hd,
      mem_upair_left _ _⟩, mem_sing.mpr rfl⟩
  · exact hU.transitive (hU.transitive (hkp d hd) (mem_upair_right _ _)) (mem_upair_right _ _)

/-- **The bound of a Π**: the glued bounds of the body over the domain,
where the domain is small. -/
noncomputable def piBound (w : Nat) (D : Term) (Bb : (Nat → V) → V) (ρ : Nat → V) : V :=
  open Classical in
  if SmallAt w (interp V ρ D) then sigmaPairs (interp V ρ D) fun d => Bb (cons d ρ) else empty

/-- The point is small. -/
theorem SmallAt.pt (w : Nat) : SmallAt w (pt : V) := fun hw =>
  (tg_isTGUniverse hw).transitive (unitSet_mem_tg w) pt_mem_unitSet

/-- **Π over a hole-free domain**: the support of a member over a small
domain is the glued supports of its values, the body's items one binder
down (the bound variable is no admissible position); a member over a
domain that is not small (`w ≠ 0`) is the point, whose membership needs
no item (`PtOn`).  At the target frame the member lies in the Π by
`mem_piV_of_app`, the fibres at both frames being types (`hT`, the
grading: "not pt" source (1)). -/
theorem AccOn.pi {w : Nat} {Q : Nat → Nat → Prop} {R : FrameRel V} {D B : Term}
    (hD : ConstOn R D)
    {Bb : (Nat → V) → V} (hB : AccOn w (shiftQ Q) (R.underBoth D) Bb B)
    (hT : FibTyOn R D B) (hP : w ≠ 0 → PtOn (R.underBoth D) B) :
    AccOn w Q R (piBound w D Bb) (.pi D B) := by
  intro ρ ρ₀ hR f hfw hf
  rw [interp_pi] at hf
  have hTy0 : ∀ x, x ∈ˢ interp V ρ D → IsTy (interp V (cons x ρ) B) := (hT ρ ρ₀ hR).1
  have hTy : ∀ ρ', R ρ ρ' → ∀ x, x ∈ˢ interp V ρ D → IsTy (interp V (cons x ρ') B) :=
    fun ρ' hR' x hx => (hT ρ ρ' hR').2 x (hD ρ ρ' hR' ▸ hx)
  by_cases hDw' : ¬ SmallAt w (interp V ρ D)
  · -- a domain that is not small: `w ≠ 0`, and the member is the point (a
    -- graph of the level has a small domain)
    have hw : w ≠ 0 := fun h0 => hDw' (h0 ▸ SmallAt.zero _)
    have hfp : f = pt := Classical.byContradiction fun hfp =>
      hDw' fun hw' => (small_of_mem_piSet hw' (mem_piSet_of_mem_piV hf hfp) (hfw hw')).1
    subst hfp
    refine ⟨empty, fun _ => (0, [], empty), fun b hb => absurd hb (not_mem_empty b),
      fun b hb => absurd hb (not_mem_empty b), fun ρ' hR' _ => ?_⟩
    rw [interp_pi, ← hD ρ ρ' hR']
    refine (pt_mem_piV_iff (hTy ρ' hR')).mpr fun d hd => ?_
    exact hP hw (cons d ρ) (cons d ρ') ⟨d, ρ, ρ', rfl, rfl, hR', hd, hD ρ ρ' hR' ▸ hd⟩
      ((pt_mem_piV_iff hTy0).mp hf d hd)
  have hDw : SmallAt w (interp V ρ D) := Classical.not_not.mp hDw'
  have happw : ∀ d, d ∈ˢ interp V ρ D → SmallAt w (app f d) := by
    intro d hd hw
    by_cases hfp : f = pt
    · rw [hfp, app_pt]; exact SmallAt.pt w hw
    · exact (small_of_mem_piSet hw (mem_piSet_of_mem_piV hf hfp) (hfw hw)).2 d hd
  obtain ⟨Bf, gf, hsk⟩ := skolem_occ (S := interp V ρ D)
    (Q := fun d B' g => B' ⊆ˢ Bb (cons d ρ) ∧
      (∀ b, b ∈ˢ B' → Adm (shiftQ Q) (g b) ∧ Holds (cons d ρ) (g b)) ∧
      ∀ σ', R.underBoth D (cons d ρ) σ' → (∀ b, b ∈ˢ B' → Holds σ' (g b)) →
        app f d ∈ˢ interp V σ' B)
    fun d hd => hB (cons d ρ) (cons d ρ₀) ⟨d, ρ, ρ₀, rfl, rfl, hR, hd, hD ρ ρ₀ hR ▸ hd⟩ _
      (happw d hd) (app_mem_piV hf hd)
  -- an admissible item of the body is never the bound variable
  have hne : ∀ d, d ∈ˢ interp V ρ D → ∀ b, b ∈ˢ Bf d → (gf d b).1 ≠ 0 := by
    intro d hd b hb h0
    have := ((hsk d hd).2.1 b hb).1
    unfold Adm at this
    rw [h0] at this
    exact this
  refine ⟨sigmaPairs (interp V ρ D) Bf, fun p => (gf (sfst p) (ssnd p)).down, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨d, hd, b, hb, rfl⟩ := mem_sigmaPairs.mp hp
    unfold piBound
    rw [ite_eq_left hDw]
    exact mem_sigmaPairs.mpr ⟨d, hd, b, (hsk d hd).1 b hb, rfl⟩
  · intro p hp
    obtain ⟨d, hd, b, hb, rfl⟩ := mem_sigmaPairs.mp hp
    simp only [sfst_kpair, ssnd_kpair]
    obtain ⟨hQ, hH⟩ := (hsk d hd).2.1 b hb
    refine ⟨?_, (holds_cons_down (hne d hd b hb)).mp hH⟩
    have h0 := hne d hd b hb
    unfold Adm at hQ ⊢
    generalize gf d b = o at hQ h0
    obtain ⟨i, vs, y⟩ := o
    cases i with
    | zero => exact absurd rfl h0
    | succ i => exact hQ
  · intro ρ' hR' h'
    rw [interp_pi, ← hD ρ ρ' hR']
    refine mem_piV_of_app hf hTy0 (hTy ρ' hR') fun d hd => ?_
    refine (hsk d hd).2.2 (cons d ρ') ⟨d, ρ, ρ', rfl, rfl, hR', hd, hD ρ ρ' hR' ▸ hd⟩
      fun b hb => ?_
    have := h' (kpair d b) (mem_sigmaPairs.mpr ⟨d, hd, b, hb, rfl⟩)
    simp only [sfst_kpair, ssnd_kpair] at this
    exact (holds_cons_down (hne d hd b hb)).mpr this

/-- The Π bound is a set of the level. -/
theorem SizeOn.pi {w : Nat} {R : FrameRel V} {D : Term} (hD : ConstOn R D)
    {Bb : (Nat → V) → V} (hB : SizeOn w (R.underBoth D) Bb) : SizeOn w R (piBound w D Bb) := by
  intro ρ ρ₀ hR hw
  unfold piBound
  split
  · rename_i hDw
    exact (tg_isTGUniverse hw).sigmaPairs_mem (hDw hw) fun d hd =>
      hB (cons d ρ) (cons d ρ₀) ⟨d, ρ, ρ₀, rfl, rfl, hR, hd, hD ρ ρ₀ hR ▸ hd⟩ hw
  · exact empty_mem_tg w

/-- **A member hole at its full arity, at hole-free arguments.** -/
theorem AccOn.holeApp {w : Nat} {Q : Nat → Nat → Prop} {R : FrameRel V} {h : Nat}
    {es : List Term} (hQ : Q h es.length) (hes : ∀ e ∈ es, ConstOn R e) :
    AccOn w Q R (fun _ => unitSet) (Term.mkAppN (.bvar h) es) := by
  intro ρ ρ₀ _ x _ hx
  rw [interp_mkAppN_foldl, interp_bvar] at hx
  refine ⟨unitSet, fun _ => (h, es.map (interp V ρ), x), Subset.refl _,
    fun _ _ => ⟨by unfold Adm; simpa using hQ, hx⟩, fun ρ' hR' h' => ?_⟩
  rw [interp_mkAppN_foldl, interp_bvar]
  have hmap : es.map (interp V ρ) = es.map (interp V ρ') :=
    List.map_congr_left fun e he => hes e he ρ ρ' hR'
  rw [← hmap]
  exact h' pt pt_mem_unitSet

/-! ## The cases: the point -/

theorem ConstOn.ptOn {R : FrameRel V} {a : Term} (h : ConstOn R a) : PtOn R a :=
  fun ρ ρ' hR hp => h ρ ρ' hR ▸ hp

theorem PtOn.of_eqOn {R : FrameRel V} {P : (Nat → V) → Prop}
    (hdom : ∀ ρ ρ', R ρ ρ' → P ρ ∧ P ρ') {a b : Term}
    (heq : ∀ ρ, P ρ → interp V ρ a = interp V ρ b) (hb : PtOn R b) : PtOn R a := by
  intro ρ ρ' hR hp
  rw [heq ρ' (hdom ρ ρ' hR).2]
  rw [heq ρ (hdom ρ ρ' hR).1] at hp
  exact hb ρ ρ' hR hp

/-- **A Π over a hole-free domain** holds the point exactly when every
fibre does (its fibres being types, `hT`), so it carries the point along
the relation as its body does. -/
theorem PtOn.pi {R : FrameRel V} {D B : Term} (hD : ConstOn R D)
    (hT : FibTyOn R D B) (hB : PtOn (R.underBoth D) B) : PtOn R (.pi D B) := by
  intro ρ ρ' hR hp
  rw [interp_pi] at hp ⊢
  rw [← hD ρ ρ' hR]
  refine (pt_mem_piV_iff fun x hx => (hT ρ ρ' hR).2 x (hD ρ ρ' hR ▸ hx)).mpr fun d hd => ?_
  exact hB (cons d ρ) (cons d ρ') ⟨d, ρ, ρ', rfl, rfl, hR, hd, hD ρ ρ' hR ▸ hd⟩
    ((pt_mem_piV_iff (hT ρ ρ' hR).1).mp hp d hd)

/-- **A hole at its full arity** never holds the point (`PtFreeOn`), so
it carries it vacuously. -/
theorem PtOn.holeApp {Q : Nat → Nat → Prop} {R : FrameRel V} (hfree : PtFreeOn Q R) {h : Nat}
    {es : List Term} (hQ : Q h es.length) : PtOn R (Term.mkAppN (.bvar h) es) := by
  intro ρ ρ' hR hp
  rw [interp_mkAppN_foldl, interp_bvar] at hp
  exact absurd hp (hfree ρ ρ' hR h (es.map (interp V ρ)) (by simpa using hQ))

/-! ## Bounds reading given positions -/

/-- The positions `M` seen one binder down, the bound variable read. -/
def liftM (M : Nat → Prop) : Nat → Prop
  | 0 => True
  | i + 1 => M i

omit [SetTheory V] in
theorem InvOn.const (M : Nat → Prop) (c : V) : InvOn M (fun _ : Nat → V => c) :=
  fun _ _ _ => rfl

/-- **The Π bound reads what its domain and its body's bound read.** -/
theorem InvOn.pi {w : Nat} {M : Nat → Prop} {D : Term} (hD : NoBVar (fun i => ¬ M i) D)
    {Bb : (Nat → V) → V} (hB : InvOn (liftM M) Bb) : InvOn M (piBound w D Bb) := by
  intro ρ ρ' hag
  have hD' : interp V ρ D = interp V ρ' D :=
    interp_congr_noBVar D hD fun i hi => hag i (Classical.byContradiction hi)
  have hb : ∀ d, Bb (cons d ρ) = Bb (cons d ρ') := by
    intro d
    refine hB _ _ fun i hi => ?_
    cases i with
    | zero => rfl
    | succ i => exact hag i hi
  unfold piBound
  rw [hD']
  simp only [hb]

end ConLeche.Semantics
