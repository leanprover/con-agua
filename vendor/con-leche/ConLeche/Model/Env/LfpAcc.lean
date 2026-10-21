module

public import ConLeche.Model.Env.BlockLfp
import ConLeche.Model.Env.BlockLfpTup
public import ConLeche.Semantics.Inductives.TeleAcc
import ConLeche.SetModel.Access

public section

/-!
# The hole fit is ACCESSIBLE, from its constructors' telescopes

The consumer side of accessibility: the hole fit of an lfp datum is
accessible (`LfpDatum.FitAcc`) with ONE set `A` — a set of the level at a
`Type`-valued block — as soon as every constructor's field telescope is
accessible along the ACCESSIBILITY RELATION at the hole frame (`accRel`:
the hole frames of any two tuples of the space), with a telescope bound
(`teleBound`) that reads no hole.  The operator's accessibility follows
through its fibre law (`FitAcc.accTuple`), hence (W) (`closed_of_acc`,
at `w = 0` `closedTuple_zero`) and monotonicity (task #327).

* **The relation** relates the hole frames of any two tuples; it is
  symmetric, reflexive on the space, agrees off the holes, and at a
  `Type`-valued block its holes at their full arity never hold the point
  (`accRel_ptFree`: the fibres are strict sets) — the fact the point's
  stability of the run inversion needs.
* **Items are occurrences**: a held member-hole item at its full arity is
  an occurrence of the tuple (`occOf`, `inTup_occOf`), and an occurrence
  held by another tuple holds the item at its frame (`holds_of_inTup`).
* **The assembly** (`fitAcc_holeOp`): a fitting spine's support is the
  spine's (`teleBound_support`), its bound the constructor's telescope
  bound, the same at every tuple (`teleBound_agr`); the bound of the fit
  is the finite union over the constructors.
-/

namespace ConLeche.Model
open ConLeche.Term (Term)
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower

open ConLeche (Name)

universe w

variable {V : Type w} [SetTheory V]

/-! ## A λ-tower at its full arity -/

theorem foldlApp_empty : ∀ (vs : List V), vs.foldl app (empty : V) = empty
  | [] => rfl
  | v :: vs => by
    show vs.foldl app (app empty v) = empty
    rw [app_empty]
    exact foldlApp_empty vs

theorem foldlApp_pt : ∀ (vs : List V), vs.foldl app (pt : V) = pt
  | [] => rfl
  | v :: vs => by
    show vs.foldl app (app pt v) = pt
    rw [app_pt]
    exact foldlApp_pt vs

/-- **A λ-tower applied to a spine of its full length** computes at a
fitting spine and is junk otherwise: `∅` where a graph is applied off its
domain, the point where a level is (no spine fits its telescope). -/
theorem holeFam_foldl_full :
    ∀ {ρ : Nat → V} {Fs : List Term} {vs : List V} (g : List V → V),
      vs.length = Fs.length →
      (SpineFit ρ Fs vs ∧ vs.foldl app (holeFam ρ Fs g) = g vs) ∨
        (¬ SpineFit ρ Fs vs ∧
          (vs.foldl app (holeFam ρ Fs g) = empty ∨ vs.foldl app (holeFam ρ Fs g) = pt))
  | _, [], [], _, _ => Or.inl ⟨trivial, rfl⟩
  | _, [], _ :: _, _, h => by simp at h
  | _, _ :: _, [], _, h => by simp at h
  | ρ, F :: Fs, a :: vs, g, h => by
    show (SpineFit ρ (F :: Fs) (a :: vs) ∧
        vs.foldl app (app (lamV (interp V ρ F) _) a) = g (a :: vs)) ∨
      (¬ SpineFit ρ (F :: Fs) (a :: vs) ∧ (vs.foldl app (app (lamV (interp V ρ F) _) a) = empty ∨
        vs.foldl app (app (lamV (interp V ρ F) _) a) = pt))
    by_cases ha : a ∈ˢ interp V ρ F
    · rw [app_lamV ha]
      rcases holeFam_foldl_full (ρ := cons a ρ) (Fs := Fs) (vs := vs) (fun as => g (a :: as))
          (by simpa using h) with ⟨hf, he⟩ | ⟨hn, he⟩
      · exact Or.inl ⟨⟨ha, hf⟩, he⟩
      · exact Or.inr ⟨fun hf => hn hf.2, he⟩
    · refine Or.inr ⟨fun hf => ha hf.1, ?_⟩
      by_cases hp : lamV (interp V ρ F)
          (fun x => holeFam (cons x ρ) Fs fun as => g (x :: as)) = pt
      · rw [hp, app_pt]
        exact Or.inr (foldlApp_pt vs)
      · rw [lamV_eq_graph hp, app_graph_of_not_mem ha]
        exact Or.inl (foldlApp_empty vs)

namespace LfpDatum

variable {D : LfpDatum V}

/-! ## The accessibility relation at the hole frame -/

variable (D) in
/-- **The accessibility relation** at the hole frame of `ρp`: the frames of
any two tuples of the space. -/
@[expose] def accRel (ψ : Name → Nat) (ρp : Nat → V) : FrameRel V :=
  fun σ σ' => ∃ X Y, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X ∧
    InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) Y ∧ σ = D.frame ψ ρp X ∧ σ' = D.frame ψ ρp Y

variable (D) in
/-- **The member holes at their full arity**: member `t`'s hole (position
`k - 1 - t` of the hole frame) at its indices. -/
@[expose] def MemberQ (ψ : Name → Nat) : Nat → Nat → Prop :=
  fun i n => ∃ t, t < D.k ∧ i = D.k - 1 - t ∧ n = (D.ids t ψ).length

theorem accRel_symm {ψ : Name → Nat} {ρp : Nat → V} : (D.accRel ψ ρp).Symm := by
  rintro _ _ ⟨X, Y, hX, hY, rfl, rfl⟩
  exact ⟨Y, X, hY, hX, rfl, rfl⟩

theorem accRel_refl {ψ : Name → Nat} {ρp X : Nat → V}
    (hX : InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X) :
    D.accRel ψ ρp (D.frame ψ ρp X) (D.frame ψ ρp X) :=
  ⟨X, X, hX, hX, rfl, rfl⟩

/-- The frames agree off the member holes. -/
theorem accRel_agreeOff {ψ : Name → Nat} {ρp : Nat → V} {σ σ' : Nat → V}
    (h : D.accRel ψ ρp σ σ') : ∀ i, D.k ≤ i → σ i = σ' i := by
  obtain ⟨X, Y, -, -, rfl, rfl⟩ := h
  intro i hi
  obtain ⟨j, rfl⟩ : ∃ j, i = j + D.k := ⟨i - D.k, by omega⟩
  rw [frame_param, frame_param]

/-! ## Items and occurrences -/

variable (D) in
/-- **The occurrence of a member-hole item**: the member, the index tuple
of the spine's indices, the value. -/
@[expose] noncomputable def occOf (ψ : Name → Nat) (o : Occ V) : Nat × V × V :=
  (D.k - 1 - o.1, tupW (D.u (D.k - 1 - o.1) ψ) o.2.1, o.2.2)

/-- **A held item at a fitting spine is an occurrence.** -/
theorem inTup_occOf (hkN : D.k ≤ D.N) {ψ : Name → Nat} {ρp X : Nat → V}
    {o : Occ V} (hQ : Adm (D.MemberQ ψ) o)
    (hfit : SpineFit ρp (D.ids (D.k - 1 - o.1) ψ) o.2.1)
    (hH : Holds (D.frame ψ ρp X) o) : InTup D.N (D.idx ψ ρp) X (D.occOf ψ o) := by
  obtain ⟨i, vs, y⟩ := o
  obtain ⟨t, ht, rfl, hlen⟩ := hQ
  unfold Holds at hH
  simp only at hH hlen hfit
  rw [frame_hole ht] at hH
  unfold holeVal at hH
  have ht' : D.k - 1 - (D.k - 1 - t) = t := by omega
  rw [ht'] at hfit
  unfold occOf
  simp only [ht']
  rw [holeFam_app _ hfit] at hH
  exact ⟨by omega, tupW_mem hfit, hH⟩

/-- **An occurrence held by another tuple holds the item at its frame**
(at a fitting spine). -/
theorem holds_of_inTup {ψ : Name → Nat} {ρp X' : Nat → V} {o : Occ V}
    (hQ : Adm (D.MemberQ ψ) o) (hfit : SpineFit ρp (D.ids (D.k - 1 - o.1) ψ) o.2.1)
    (hin : InTup D.N (D.idx ψ ρp) X' (D.occOf ψ o)) : Holds (D.frame ψ ρp X') o := by
  obtain ⟨i, vs, y⟩ := o
  obtain ⟨t, ht, rfl, hlen⟩ := hQ
  unfold Holds
  simp only at hlen hfit ⊢
  rw [frame_hole ht]
  unfold holeVal
  have ht' : D.k - 1 - (D.k - 1 - t) = t := by omega
  rw [ht'] at hfit
  obtain ⟨-, -, hy⟩ := hin
  unfold occOf at hy
  simp only [ht'] at hy
  rw [holeFam_app _ hfit]
  exact hy

/-- **Off a fitting spine an item is held alike at every tuple's frame**:
the hole's value there does not read the tuple (`holeFam_foldl_nofit`;
the tuple's fibres are strict sets or truth values, never the point). -/
theorem holds_of_nofit {ψ : Name → Nat} {ρp X X' : Nat → V}
    (hX : InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X) (hX' : InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X')
    (hkN : D.k ≤ D.N) {o : Occ V} (hQ : Adm (D.MemberQ ψ) o)
    (hn : ¬ SpineFit ρp (D.ids (D.k - 1 - o.1) ψ) o.2.1)
    (hH : Holds (D.frame ψ ρp X) o) : Holds (D.frame ψ ρp X') o := by
  obtain ⟨i, vs, y⟩ := o
  obtain ⟨t, ht, rfl, hlen⟩ := hQ
  unfold Holds at hH ⊢
  simp only at hlen hn hH ⊢
  rw [frame_hole ht] at hH ⊢
  unfold holeVal at hH ⊢
  have ht' : D.k - 1 - (D.k - 1 - t) = t := by omega
  rw [ht'] at hn
  have htN : t < D.N := by omega
  have hne : ∀ (Y : Nat → V), InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) Y →
      ∀ ws, SpineFit ρp (D.ids t ψ) ws → app (Y t) (tupW (D.u t ψ) ws) ≠ pt :=
    fun Y hY ws hws => (IsTy_of_mem_strictU (famSpace_app (hY t htN) (tupW_mem hws))).ne_pt
  rw [holeFam_foldl_nofit (hne X' hX') (hne X hX) hlen hn]
  exact hH

/-! ## Point-free holes -/

/-- **The member holes never hold the point** along the accessibility
relation (at a positive level): at a fitting spine a hole's value is a
fibre of the tuple, a strict set; elsewhere it is `∅` or the point,
which is not its own member. -/
theorem accRel_ptFree (hkN : D.k ≤ D.N) {ψ : Name → Nat} {ρp : Nat → V} (hw : D.w ψ ≠ 0) :
    PtFreeOn (D.MemberQ ψ) (D.accRel ψ ρp) := by
  rintro _ _ ⟨X, Y, hX, -, rfl, -⟩ i vs hQ hpt
  obtain ⟨t, ht, rfl, hlen⟩ := hQ
  have htN : t < D.N := by omega
  rw [frame_hole ht] at hpt
  unfold holeVal at hpt
  rcases holeFam_foldl_full (ρ := ρp) (Fs := D.ids t ψ) (vs := vs)
      (fun vs => app (X t) (tupW (D.u t ψ) vs)) hlen with ⟨hf, he⟩ | ⟨-, he | he⟩
  · rw [he] at hpt
    have hs := famSpace_app (hX t htN) (tupW_mem hf)
    exact (((mem_strictU_pos hw).mp hs).2).2 hpt
  · rw [he] at hpt
    exact not_mem_empty _ hpt
  · rw [he] at hpt
    exact not_mem_self _ hpt

/-! ## The assembly -/

/-- A finite union. -/
noncomputable def finUnion (f : Nat → V) : Nat → V
  | 0 => empty
  | n + 1 => binUnion (finUnion f n) (f n)

theorem subset_finUnion {f : Nat → V} : ∀ {n i : Nat}, i < n → f i ⊆ˢ finUnion f n
  | 0, _, h => absurd h (by omega)
  | n + 1, i, h => by
    intro x hx
    show x ∈ˢ binUnion (finUnion f n) (f n)
    by_cases hin : i = n
    · subst hin; exact mem_binUnion.mpr (Or.inr hx)
    · exact mem_binUnion.mpr (Or.inl (subset_finUnion (by omega) x hx))

theorem finUnion_mem {w' : Nat} (hw : w' ≠ 0) {f : Nat → V} :
    ∀ {n : Nat}, (∀ i, i < n → f i ∈ˢ (tg w' : V)) → finUnion f n ∈ˢ (tg w' : V)
  | 0, _ => empty_mem_tg w'
  | n + 1, h => (tg_isTGUniverse hw).binUnion_mem (empty_mem_tg w')
      (finUnion_mem hw fun i hi => h i (by omega)) (h n (by omega))

/-- **The hole fit is accessible with ONE bound**, a set of the level at
a `Type`-valued block: when every constructor's field telescope is
accessible along the accessibility relation at the member holes
(`TeleAccP`), each field's bound reads only the positions agreeing across
the tuples' hole frames and the ordinary slots (`hAf`), every ordinary
field's reading likewise (`hF`), and the result indices read alike at any
two hole frames under a spine fitting both (`hresC`). -/
theorem fitAcc_holeOp {ψ : Name → Nat} {ρp : Nat → V} (hkN : D.k ≤ D.N)
    (ord : Nat → Nat → Nat → Bool) (Af : Nat → Nat → Nat → (Nat → V) → V)
    (hAf : ∀ c, c < D.N → ∀ j, j < D.nctors c →
      ∀ l τ τ', TAgr D.k (ord c j) l τ τ' → Af c j l τ = Af c j l τ')
    (hF : ∀ c, c < D.N → ∀ j, j < D.nctors c → ∀ (i : Nat) (F : Term),
      (D.fields ψ c j)[i]? = some F → ord c j i = true →
        ∀ τ τ', TAgr D.k (ord c j) i τ τ' → interp V τ F = interp V τ' F)
    (htele : ∀ c, c < D.N → ∀ j, j < D.nctors c →
      TeleAccP (D.w ψ) (Af c j) 0 (D.MemberQ ψ) (D.accRel ψ ρp) (D.fields ψ c j))
    (hresC : ∀ c, c < D.N → ∀ j, j < D.nctors c → ∀ X X',
      InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X → InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X' →
      ∀ fs, SpineFit (D.frame ψ ρp X) (D.fields ψ c j) fs →
        SpineFit (D.frame ψ ρp X') (D.fields ψ c j) fs →
        ∀ e ∈ D.resIdx ψ c j,
          interp V (consList fs (D.frame ψ ρp X)) e = interp V (consList fs (D.frame ψ ρp X')) e) :
    ∃ A, SmallAt (D.w ψ) A ∧ D.FitAcc ψ ρp A := by
  let X₀ : Nat → V := AccIter.emptyTup (D.idx ψ ρp)
  have hX₀ : InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X₀ := AccIter.emptyTup_mem
  let TB : Nat → Nat → V := fun c j =>
    teleBound (D.w ψ) (ord c j) (Af c j) 0 (D.fields ψ c j) (D.frame ψ ρp X₀)
  refine ⟨finUnion (fun c => finUnion (TB c) (D.nctors c)) D.N,
    fun hw => finUnion_mem hw fun c _ => finUnion_mem hw fun j _ => teleBound_mem hw _ _ _ _ _, ?_⟩
  rintro X hX m hm i j fs ⟨hj, hsp, hidx⟩
  have hF0 : ∀ (i : Nat) (F : Term), (D.fields ψ m j)[i]? = some F →
      ord m j (0 + i) = true → ∀ τ τ', TAgr D.k (ord m j) (0 + i) τ τ' →
        interp V τ F = interp V τ' F := by
    intro i F h1 h2 τ τ' h3
    rw [Nat.zero_add] at h2 h3
    exact hF m hm j hj i F h1 h2 τ τ' h3
  obtain ⟨B, g, hB, hg, hs⟩ := teleBound_support (hAf m hm j hj) (D.fields ψ m j) 0 (D.MemberQ ψ)
    (D.accRel ψ ρp) hF0 (htele m hm j hj) (D.frame ψ ρp X) (accRel_refl hX) fs hsp
  -- the telescope's bound is the same at every tuple's hole frame
  have hagr : TAgr D.k (ord m j) 0 (D.frame ψ ρp X) (D.frame ψ ρp X₀) := by
    intro i'
    refine ⟨fun h => absurd h (by omega), fun h => ?_⟩
    obtain ⟨i'', rfl⟩ : ∃ i'', i' = i'' + D.k := ⟨i' - D.k, by omega⟩
    rw [frame_param, frame_param]
  have hTB : teleBound (D.w ψ) (ord m j) (Af m j) 0 (D.fields ψ m j) (D.frame ψ ρp X) = TB m j :=
    teleBound_agr (hAf m hm j hj) (D.fields ψ m j) 0 hF0 _ _ hagr
  -- the support's items at a fitting spine; the others are held alike at
  -- every tuple's frame (`holds_of_nofit`)
  classical
  let P : V → Prop := fun b => SpineFit ρp (D.ids (D.k - 1 - (g b).1) ψ) (g b).2.1
  refine ⟨sep B P, fun b => D.occOf ψ (g b), fun b hb => ?_, fun b hb => ?_,
    fun X' hX' hheld => ?_⟩
  · have := hB b (sep_subset b hb)
    rw [hTB] at this
    exact subset_finUnion (f := fun c => finUnion (TB c) (D.nctors c)) hm _
      (subset_finUnion hj _ this)
  · obtain ⟨hbB, hP⟩ := mem_sep.mp hb
    exact inTup_occOf hkN (hg b hbB).1 hP (hg b hbB).2
  · have hsp' : SpineFit (D.frame ψ ρp X') (D.fields ψ m j) fs :=
      hs (D.frame ψ ρp X') ⟨X, X', hX, hX', rfl, rfl⟩ fun b hb => by
        by_cases hP : P b
        · exact holds_of_inTup (hg b hb).1 hP (hheld b (mem_sep.mpr ⟨hb, hP⟩))
        · exact holds_of_nofit hX hX' hkN (hg b hb).1 hP (hg b hb).2
    refine ⟨hj, hsp', fun l hl => ?_⟩
    obtain ⟨e, he, hev⟩ := hidx l hl
    refine ⟨e, he, ?_⟩
    rw [← hresC m hm j hj X X' hX hX' fs hsp hsp' e (List.mem_of_getElem? he)]
    exact hev

end LfpDatum

end ConLeche.Model
