module

public import ConLeche.SetTheory.Derive.Univ

@[expose] public section

/-!
# Quotients

`quotSet u A R` is, for `u ≠ 0`, the set of equivalence classes of the
equivalence closure of "`app (app R a) b` is inhabited" on `A` (classes
by separation, the class set by replacement), each class **tagged** as
the pair `kpair ∅ (qclass A R a)` (task #342: a raw class can be the
point, see the end of the file; a tagged one is a pair, so the quotient
is strict); for `u = 0` the base
lives in `Prop`, everything collapses to the proof point, and the
quotient is `image (fun _ => pt) A` — the truth value `[A inhabited]`.

The lift (`quotLiftR`, `SetModel/Value.lean`) lifts `f` to the quotient as the graph of
`q ↦ app f (representative of q)` (representatives by choice) — except
when `f` is the proof point, where the lift is the proof point too.
That tag is what makes the beta law `app (quotLiftR …) (quotClass … a) =
app f a` hold with *no typing premise on `f`* (matching the interface):
a `pt`-tagged `f` beta-reduces to `pt` on both sides, any other `f`
goes through the representative and the invariance premise, with the
`u = 0` collapse handled by `A ⊆ {pt}` (from `A ∈ univ 0`).
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- The equivalence closure, on `A`, of "`app (app R a) b` is
inhabited". -/
inductive QuotRel (A R : V) : V → V → Prop where
  | base {a b : V} : a ∈ˢ A → b ∈ˢ A → (∃ w, w ∈ˢ app (app R a) b) →
      QuotRel A R a b
  | refl {a : V} : a ∈ˢ A → QuotRel A R a a
  | symm {a b : V} : QuotRel A R a b → QuotRel A R b a
  | trans {a b c : V} : QuotRel A R a b → QuotRel A R b c → QuotRel A R a c

/-- The `QuotRel`-class of `a` in `A`. -/
noncomputable def qclass (A R a : V) : V := sep A (fun b => QuotRel A R a b)

theorem mem_qclass {A R a b : V} :
    b ∈ˢ qclass A R a ↔ b ∈ˢ A ∧ QuotRel A R a b := mem_sep

theorem self_mem_qclass {A R a : V} (ha : a ∈ˢ A) : a ∈ˢ qclass A R a :=
  mem_qclass.mpr ⟨ha, QuotRel.refl ha⟩

theorem qclass_eq_of_rel {A R a b : V} (h : QuotRel A R a b) :
    qclass A R a = qclass A R b :=
  ext fun z => by
    rw [mem_qclass, mem_qclass]
    exact ⟨fun ⟨hz, hr⟩ => ⟨hz, (h.symm).trans hr⟩,
           fun ⟨hz, hr⟩ => ⟨hz, h.trans hr⟩⟩

theorem rel_of_qclass_eq {A R a b : V} (ha : a ∈ˢ A) (_hb : b ∈ˢ A)
    (h : qclass A R a = qclass A R b) : QuotRel A R a b :=
  (mem_qclass.mp (h ▸ self_mem_qclass ha)).2.symm

open Classical in
/-- The quotient (see module docs). -/
noncomputable def quotSet (u : Nat) (A R : V) : V :=
  if u = 0 then image (fun _ => pt) A else image (fun a => kpair empty (qclass A R a)) A

open Classical in
/-- The class of `a` in the quotient: at `u ≠ 0` the `QuotRel`-class,
tagged as a pair (`kpair ∅ ·`; `sing` would not do, as the class can be
`ptTag` itself and `sing ptTag = pt`). -/
noncomputable def quotClass (u : Nat) (A R a : V) : V :=
  if u = 0 then pt else kpair empty (qclass A R a)

theorem quotClass_mem {u : Nat} {A R a : V} (ha : a ∈ˢ A) :
    quotClass u A R a ∈ˢ quotSet u A R := by
  unfold quotClass quotSet
  split
  · exact mem_image.mpr ⟨a, ha, rfl⟩
  · exact mem_image.mpr ⟨a, ha, rfl⟩

theorem quotClass_surj {u : Nat} {A R q : V} (hq : q ∈ˢ quotSet u A R) :
    ∃ a, a ∈ˢ A ∧ q = quotClass u A R a := by
  unfold quotSet at hq
  unfold quotClass
  split at hq
  · next h =>
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hq
    exact ⟨a, ha, (ite_eq_left h).symm⟩
  · next h =>
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hq
    exact ⟨a, ha, (ite_eq_right h).symm⟩

/-- A class formed at ONE pair of parameters that lands in the quotient
of ANOTHER: its representative lies in the second parameter's carrier,
and the class is the second quotient's class of that same
representative.  Nothing relates the two parameter pairs — at a positive
level the first (tagged) class is a (tagged) `qclass` of the second's,
and at level zero
both classes are the point and the second carrier is inhabited because
the quotient is. -/
theorem quotClass_of_mem_quotSet {u : Nat} {Aset R A' R' a : V}
    (hAset : Aset ∈ˢ (univ u : V)) (hA' : A' ∈ˢ (univ u : V)) (ha : a ∈ˢ A')
    (hmem : quotClass u A' R' a ∈ˢ quotSet u Aset R) :
    a ∈ˢ Aset ∧ quotClass u A' R' a = quotClass u Aset R a := by
  obtain ⟨b, hb, hcls⟩ := quotClass_surj hmem
  by_cases hu : u = 0
  · subst hu
    refine ⟨?_, by unfold quotClass; rw [ite_eq_left rfl, ite_eq_left rfl]⟩
    rw [univ_zero] at hA' hAset
    rw [eq_pt_of_mem_univZero hA' ha, ← eq_pt_of_mem_univZero hAset hb]
    exact hb
  · unfold quotClass at hcls ⊢
    rw [ite_eq_right hu, ite_eq_right hu] at hcls
    rw [ite_eq_right hu, ite_eq_right hu]
    have hcls' := (kpair_inj hcls).2
    have hab : a ∈ˢ qclass Aset R b := by rw [← hcls']; exact self_mem_qclass ha
    obtain ⟨haA, hrel⟩ := mem_qclass.mp hab
    exact ⟨haA, hcls.trans (congrArg (kpair empty) (qclass_eq_of_rel hrel))⟩

/-- **`quotClass_of_mem_quotSet` across two positive levels**: a class
formed at one positive level and one pair of parameters that lands in
the quotient of another positive level and pair is, there, the class of
the same representative.  Above `Prop` the class reads no level. -/
theorem quotClass_of_mem_quotSet_pos {u u' : Nat} (hu : u ≠ 0) (hu' : u' ≠ 0)
    {Aset R A' R' a : V} (ha : a ∈ˢ A')
    (hmem : quotClass u' A' R' a ∈ˢ quotSet u Aset R) :
    a ∈ˢ Aset ∧ quotClass u' A' R' a = quotClass u Aset R a := by
  have hl : quotClass u' A' R' a = quotClass u A' R' a := by
    unfold quotClass; rw [ite_eq_right hu, ite_eq_right hu']
  rw [hl] at hmem ⊢
  obtain ⟨b, hb, hcls⟩ := quotClass_surj hmem
  unfold quotClass at hcls ⊢
  rw [ite_eq_right hu, ite_eq_right hu] at hcls
  rw [ite_eq_right hu, ite_eq_right hu]
  have hcls' := (kpair_inj hcls).2
  have hab : a ∈ˢ qclass Aset R b := by rw [← hcls']; exact self_mem_qclass ha
  obtain ⟨haA, hrel⟩ := mem_qclass.mp hab
  exact ⟨haA, hcls.trans (congrArg (kpair empty) (qclass_eq_of_rel hrel))⟩

theorem quotSound {u : Nat} {A R a b w : V} (ha : a ∈ˢ A) (hb : b ∈ˢ A)
    (hw : w ∈ˢ app (app R a) b) : quotClass u A R a = quotClass u A R b := by
  unfold quotClass
  split
  · rfl
  · exact congrArg (kpair empty) (qclass_eq_of_rel (QuotRel.base ha hb ⟨w, hw⟩))

open Classical in
/-- A representative of a quotient class, by choice. -/
noncomputable def qrep (u : Nat) (A R q : V) : V :=
  if h : ∃ a, a ∈ˢ A ∧ q = quotClass u A R a then Classical.choose h else empty

theorem qrep_spec {u : Nat} {A R q : V} (hq : q ∈ˢ quotSet u A R) :
    qrep u A R q ∈ˢ A ∧ q = quotClass u A R (qrep u A R q) := by
  unfold qrep
  rw [dite_eq_left (quotClass_surj hq)]
  exact Classical.choose_spec (quotClass_surj hq)

/-- The invariance premise extends from the base relation to its
equivalence closure. -/
theorem app_eq_of_rel {A R f a b : V}
    (hinv : ∀ a' b', a' ∈ˢ A → b' ∈ˢ A → (∃ w, w ∈ˢ app (app R a') b') →
      app f a' = app f b')
    (h : QuotRel A R a b) : app f a = app f b := by
  induction h with
  | base ha hb hw => exact hinv _ _ ha hb hw
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Equal classes have equal `f`-values: by closure invariance at
`u ≠ 0`, and by the `A ⊆ {pt}` collapse at `u = 0`. -/
theorem app_eq_of_quotClass_eq {u : Nat} {A R f a b : V}
    (hA : A ∈ˢ (univ u : V)) (ha : a ∈ˢ A) (hb : b ∈ˢ A)
    (hinv : ∀ a' b', a' ∈ˢ A → b' ∈ˢ A → (∃ w, w ∈ˢ app (app R a') b') →
      app f a' = app f b')
    (hq : quotClass u A R a = quotClass u A R b) : app f a = app f b := by
  unfold quotClass at hq
  split at hq
  · next h =>
    subst h
    rw [univ_zero] at hA
    rw [eq_pt_of_mem_univZero hA ha, eq_pt_of_mem_univZero hA hb]
  · exact app_eq_of_rel hinv (rel_of_qclass_eq ha hb (kpair_inj hq).2)

/-! ## The class is never the point above `Prop` (tasks #109, #342)

Raw classes are arbitrary nonempty subsets of the base, so with base
`ptTag` itself and a total relation the one class is `ptTag` and the
untagged class set is exactly `{ptTag} = pt` — for *any* singleton
proof point.  The base `ptTag`
is not the interpretation of any *writable* type; the obstruction is
semantic, in the ∀-A-R quantification of the model lemmas.  Up to task
#342 the classes were raw and this was the quotient itself; since then
a class above `Prop` is the pair `kpair ∅ (qclass A R a)`, so it is
never the point, and the quotient never is nor
contains it (`strict_quotSet`). -/

/-- Above `Prop` the quotient is strict: its members are pairs. -/
theorem strict_quotSet {u : Nat} (hu : u ≠ 0) (A R : V) : Strict (quotSet u A R) :=
  strict_of_kpairs fun z hz => by
    unfold quotSet at hz; rw [ite_eq_right hu] at hz
    obtain ⟨a, -, rfl⟩ := mem_image.mp hz
    exact ⟨_, _, rfl⟩

attribute [irreducible] quotSet quotClass

theorem quotSet_mem_univ {u : Nat} {A R : V} (hA : A ∈ˢ (univ u : V)) :
    quotSet u A R ∈ˢ (univ u : V) := by
  by_cases h : u = 0
  · subst h
    unfold quotSet
    rw [ite_eq_left rfl, univ_zero]
    refine mem_univZero.mpr fun z hz => ?_
    obtain ⟨-, -, rfl⟩ := mem_image.mp hz
    exact pt_mem_unitSet
  · refine mem_univ_of_tg_strict ?_ (strict_quotSet h A R)
    have hA' := mem_tg_of_mem_univ hA
    have hU := tg_isTGUniverse (V := V) h
    unfold quotSet
    rw [ite_eq_right h]
    exact hU.image_mem hA' fun a _ => hU.kpair_mem hA' (hU.empty_mem hA')
      (hU.mem_of_subset_mem hA' fun w hw => (mem_qclass.mp hw).1)

end ConLeche.SetTheory
