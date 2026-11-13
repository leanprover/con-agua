module

public import ConAgua.Arena.EnvRec

@[expose] public section

/-!
# A constant record's words: the decoders' facts

The facts about `decCV`, `decHint` and `decCI` (`Arena/EnvRec.lean`) that proofs use, stated over
the named offsets of `RecLayout/CV.lean` and `RecLayout/CI.lean`: what a decoded record says about
each of its words, kind by kind (`decCI_axiomInfo_iff`, …, `decCI_recInfo_iff`, and all kinds at
once, `decCI_cases`), its constant value (`decCI_cv`) and its name (`decCI_name`). At L's word
addresses (an `RdOK` reader): `CIDec.lean`. Proofs use these instead of unfolding a decoder or an
offset, so that a change of the layout ends here.
-/

open ConRon.Arena

namespace L.Arena

/-! ## One word -/

/-- A slice field's two words. -/
theorem hlist?_words {k : IdxKind} {R : Nat → Option Word} {i : Nat} {l : List (Idx k)}
    (h : hlist? R i = some l) :
    ∃ o c, R i = some o ∧ R (i + 1) = some c ∧ hslice? R o.toNat c.toNat = some l := by
  simp only [hlist?, nat?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, ⟨o, ho, rfl⟩, _, ⟨c, hc, rfl⟩, hs⟩ := h
  exact ⟨o, c, ho, hc, hs⟩

/-- A number field's word. -/
theorem nat?_word {R : Nat → Option Word} {i n : Nat} (h : nat? R i = some n) :
    ∃ w, R i = some w ∧ w.toNat = n := by
  simp only [nat?, Option.map_eq_some_iff] at h; exact h

/-- A flag field's word. -/
theorem bool?_word {R : Nat → Option Word} {i : Nat} {b : Bool} (h : bool? R i = some b) :
    ∃ w, R i = some w ∧ (w != 0) = b := by
  simp only [bool?, Option.map_eq_some_iff] at h; exact h

/-! ## The constant value -/

/-- **A decoded `IConstantVal`, word by word.** -/
theorem decCV_eq_some {R : Nat → Option Word} {q : Nat} {cv : IConstantVal} :
    decCV R q = some cv ↔
      hd? R q = some cv.name ∧ hlist? R (q + CV.lpsOff.toNat) = some cv.levelParams ∧
      hd? R (q + CV.type.toNat) = some cv.type := by
  rcases cv with ⟨n, l, t⟩
  simp only [decCV, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, IConstantVal.mk.injEq]
  constructor
  · rintro ⟨n', hn, l', hl, t', ht, rfl, rfl, rfl⟩; exact ⟨hn, hl, ht⟩
  · rintro ⟨hn, hl, ht⟩; exact ⟨_, hn, _, hl, _, ht, rfl, rfl, rfl⟩

/-- The value built from its words. -/
theorem decCV_of {R : Nat → Option Word} {q : Nat} {cv : IConstantVal}
    (hn : hd? R q = some cv.name) (hl : hlist? R (q + CV.lpsOff.toNat) = some cv.levelParams)
    (ht : hd? R (q + CV.type.toNat) = some cv.type) : decCV R q = some cv :=
  decCV_eq_some.mpr ⟨hn, hl, ht⟩

/-- A decoded value's name word. -/
theorem decCV_name {a : Nat → Option Word} {q : Nat} {cv : IConstantVal} (h : decCV a q = some cv) :
    ∃ w, a q = some w ∧ w.toNat < 2 ^ 32 ∧ cv.name = decI w := by
  have hn := (decCV_eq_some.mp h).1
  cases e : a q with
  | none => simp [hd?, e] at hn
  | some w => simp [hd?, e] at hn; exact ⟨w, rfl, hn.1, hn.2.symm⟩

/-! ## The reducibility hint -/

/-- **A decoded hint, word by word.** -/
theorem decHint_eq_some {R : Nat → Option Word} {q : Nat} {h : ConLeche.ReducibilityHint} :
    decHint R q = some h ↔
      (h = .opaque ∧ nat? R q = some 0) ∨ (h = .abbrev ∧ nat? R q = some 1) ∨
      (∃ n, h = .regular n ∧ nat? R q = some 2 ∧ nat? R (q + Hint.height.toNat) = some n) := by
  simp only [decHint, Option.bind_eq_bind, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨k, hk, e⟩
    match k, e with
    | 0, e => exact .inl ⟨(Option.some.inj e).symm, hk⟩
    | 1, e => exact .inr (.inl ⟨(Option.some.inj e).symm, hk⟩)
    | 2, e =>
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at e
      obtain ⟨n, hn, rfl⟩ := e
      exact .inr (.inr ⟨n, rfl, hk, hn⟩)
    | k + 3, e => simp at e
  · rintro (⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨n, rfl, hk, hn⟩)
    · exact ⟨0, hk, rfl⟩
    · exact ⟨1, hk, rfl⟩
    · exact ⟨2, hk, by simp [hn]⟩

/-! ## The constant record, kind by kind -/

/-- **A decoded constant record, all kinds**: the kind word, and per kind the words. -/
theorem decCI_cases {R : Nat → Option Word} {p : Nat} {x : IConstantInfo}
    (h : decCI R p = some x) :
    ∃ wk, R p = some wk ∧
      ((wk.toNat = 0 ∧ ∃ cv, decCV R (p + CI.cv.toNat) = some cv ∧ x = .axiomInfo cv) ∨
       (wk.toNat = 1 ∧ ∃ cv v hi, decCV R (p + CI.cv.toNat) = some cv ∧
          hd? R (p + CI.defnValue.toNat) = some v ∧ decHint R (p + CI.defnHint.toNat) = some hi ∧
          x = .defnInfo cv v hi) ∨
       (wk.toNat = 2 ∧ ∃ cv, decCV R (p + CI.cv.toNat) = some cv ∧ x = .thmInfo cv) ∨
       (wk.toNat = 3 ∧ ∃ cv caps, decCV R (p + CI.cv.toNat) = some cv ∧
          decCaps R (p + CI.indCaps.toNat) = some caps ∧ x = .indInfo cv caps) ∨
       (wk.toNat = 4 ∧ ∃ cv np nf fam, decCV R (p + CI.cv.toNat) = some cv ∧
          nat? R (p + CI.ctorNparams.toNat) = some np ∧ nat? R (p + CI.ctorNfields.toNat) = some nf ∧
          hd? R (p + CI.ctorInduct.toNat) = some fam ∧ x = .ctorInfo cv np nf fam) ∨
       (wk.toNat = 5 ∧ ∃ cv mi rp o c k rules, decCV R (p + CI.cv.toNat) = some cv ∧
          nat? R (p + CI.recMajor.toNat) = some mi ∧ nat? R (p + CI.recPrefix.toNat) = some rp ∧
          nat? R (p + CI.recRulesOff.toNat) = some o ∧ nat? R (p + CI.recRulesLen.toNat) = some c ∧
          bool? R (p + CI.recIsK.toNat) = some k ∧
          decRules R o c = some rules ∧ x = .recInfo cv mi rp k rules)) := by
  unfold decCI at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
  obtain ⟨k, hk, h⟩ := h
  simp only [nat?, Option.map_eq_some_iff] at hk
  obtain ⟨wk, e, rfl⟩ := hk
  refine ⟨wk, e, ?_⟩
  split at h
  · rename_i hh
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, rfl⟩ := h
    exact .inl ⟨hh, cv, hcv, rfl⟩
  · rename_i hh
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, v, hv, hi, hhi, rfl⟩ := h
    exact .inr (.inl ⟨hh, cv, v, hi, hcv, hv, hhi, rfl⟩)
  · rename_i hh
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, rfl⟩ := h
    exact .inr (.inr (.inl ⟨hh, cv, hcv, rfl⟩))
  · rename_i hh
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, caps, hcaps, rfl⟩ := h
    exact .inr (.inr (.inr (.inl ⟨hh, cv, caps, hcv, hcaps, rfl⟩)))
  · rename_i hh
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, np, hnp, nf, hnf, fam, hfam, rfl⟩ := h
    exact .inr (.inr (.inr (.inr (.inl ⟨hh, cv, np, nf, fam, hcv, hnp, hnf, hfam, rfl⟩))))
  · rename_i hh
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨cv, hcv, mi, hmi, rp, hrp, k, hkk, o, ho, c, hc, rules, hr, rfl⟩ := h
    exact .inr (.inr (.inr (.inr (.inr
      ⟨hh, cv, mi, rp, o, c, k, rules, hcv, hmi, hrp, ho, hc, hkk, hr, rfl⟩))))
  · simp at h

/-- **A decoded record's constant value** sits at `p + CI.cv` (every kind holds it inline, the
twin's pure `toConstantVal`). -/
theorem decCI_cv {R : Nat → Option Word} {p : Nat} {x : IConstantInfo}
    (h : decCI R p = some x) : decCV R (p + CI.cv.toNat) = some x.toConstantVal := by
  obtain ⟨_, _, hx⟩ := decCI_cases h
  rcases hx with ⟨-, cv, hcv, rfl⟩ | ⟨-, cv, _, _, hcv, -, -, rfl⟩ | ⟨-, cv, hcv, rfl⟩ |
    ⟨-, cv, _, hcv, -, rfl⟩ | ⟨-, cv, _, _, _, hcv, -, -, -, rfl⟩ |
    ⟨-, cv, _, _, _, _, _, _, hcv, -, -, -, -, -, -, rfl⟩ <;> exact hcv

/-- A decoded record's name word (its constant value's, at `p + CI.cv`). -/
theorem decCI_name {a : Nat → Option Word} {p : Nat} {ci : IConstantInfo} (h : decCI a p = some ci) :
    ∃ w, a (p + CI.cv.toNat) = some w ∧ w.toNat < 2 ^ 32 ∧ ci.name = decI w := by
  obtain ⟨w, h1, h2, h3⟩ := decCV_name (decCI_cv h)
  refine ⟨w, h1, h2, ?_⟩
  rw [← h3]; cases ci <;> rfl

/-- The kind word of a decoded record. -/
theorem decCI_kind {R : Nat → Option Word} {p : Nat} {x : IConstantInfo}
    (h : decCI R p = some x) : ∃ k, nat? R p = some k ∧ k ≤ 5 := by
  obtain ⟨wk, e, hx⟩ := decCI_cases h
  refine ⟨wk.toNat, by simp [nat?, e], ?_⟩
  rcases hx with ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ <;> omega

/-! ### One kind at a time (both directions) -/

/-- **An `axiomInfo` record, word by word.** -/
theorem decCI_axiomInfo_iff {R : Nat → Option Word} {p : Nat} {cv : IConstantVal} :
    decCI R p = some (.axiomInfo cv) ↔
      nat? R p = some 0 ∧ decCV R (p + CI.cv.toNat) = some cv := by
  constructor
  · intro h
    obtain ⟨wk, e, hx⟩ := decCI_cases h
    have hk : nat? R p = some wk.toNat := by simp [nat?, e]
    rcases hx with ⟨hk0, cv', hcv, ⟨⟩⟩ | ⟨hk0, cv', v', hi', hcv, hv, hh, ⟨⟩⟩ | ⟨hk0, cv', hcv, ⟨⟩⟩ |
      ⟨hk0, cv', caps', hcv, hc, ⟨⟩⟩ | ⟨hk0, cv', np', nf', fam', hcv, ha, hb, hf, ⟨⟩⟩ |
      ⟨hk0, cv', mi', rp', o, c, k', rules', hcv, ha, hb, ho, hn, hkk, hr, ⟨⟩⟩
    all_goals first | exact ⟨by rw [hk, hk0], hcv⟩ | skip
  · rintro ⟨hk, hcv⟩
    unfold decCI; simp [hk, hcv]

/-- **A `thmInfo` record, word by word.** -/
theorem decCI_thmInfo_iff {R : Nat → Option Word} {p : Nat} {cv : IConstantVal} :
    decCI R p = some (.thmInfo cv) ↔
      nat? R p = some 2 ∧ decCV R (p + CI.cv.toNat) = some cv := by
  constructor
  · intro h
    obtain ⟨wk, e, hx⟩ := decCI_cases h
    have hk : nat? R p = some wk.toNat := by simp [nat?, e]
    rcases hx with ⟨hk0, cv', hcv, ⟨⟩⟩ | ⟨hk0, cv', v', hi', hcv, hv, hh, ⟨⟩⟩ | ⟨hk0, cv', hcv, ⟨⟩⟩ |
      ⟨hk0, cv', caps', hcv, hc, ⟨⟩⟩ | ⟨hk0, cv', np', nf', fam', hcv, ha, hb, hf, ⟨⟩⟩ |
      ⟨hk0, cv', mi', rp', o, c, k', rules', hcv, ha, hb, ho, hn, hkk, hr, ⟨⟩⟩
    all_goals first | exact ⟨by rw [hk, hk0], hcv⟩ | skip
  · rintro ⟨hk, hcv⟩
    unfold decCI; simp [hk, hcv]

/-- **A `defnInfo` record, word by word.** -/
theorem decCI_defnInfo_iff {R : Nat → Option Word} {p : Nat} {cv : IConstantVal} {v : EIdx}
    {hi : ConLeche.ReducibilityHint} :
    decCI R p = some (.defnInfo cv v hi) ↔
      nat? R p = some 1 ∧ decCV R (p + CI.cv.toNat) = some cv ∧
      hd? R (p + CI.defnValue.toNat) = some v ∧ decHint R (p + CI.defnHint.toNat) = some hi := by
  constructor
  · intro h
    obtain ⟨wk, e, hx⟩ := decCI_cases h
    have hk : nat? R p = some wk.toNat := by simp [nat?, e]
    rcases hx with ⟨hk0, cv', hcv, ⟨⟩⟩ | ⟨hk0, cv', v', hi', hcv, hv, hh, ⟨⟩⟩ | ⟨hk0, cv', hcv, ⟨⟩⟩ |
      ⟨hk0, cv', caps', hcv, hc, ⟨⟩⟩ | ⟨hk0, cv', np', nf', fam', hcv, ha, hb, hf, ⟨⟩⟩ |
      ⟨hk0, cv', mi', rp', o, c, k', rules', hcv, ha, hb, ho, hn, hkk, hr, ⟨⟩⟩
    all_goals first | exact ⟨by rw [hk, hk0], hcv, hv, hh⟩ | skip
  · rintro ⟨hk, hcv, hv, hh⟩
    unfold decCI; simp [hk, hcv, hv, hh]

/-- **An `indInfo` record, word by word.** -/
theorem decCI_indInfo_iff {R : Nat → Option Word} {p : Nat} {cv : IConstantVal} {c : IIndCaps} :
    decCI R p = some (.indInfo cv c) ↔
      nat? R p = some 3 ∧ decCV R (p + CI.cv.toNat) = some cv ∧
      decCaps R (p + CI.indCaps.toNat) = some c := by
  constructor
  · intro h
    obtain ⟨wk, e, hx⟩ := decCI_cases h
    have hk : nat? R p = some wk.toNat := by simp [nat?, e]
    rcases hx with ⟨hk0, cv', hcv, ⟨⟩⟩ | ⟨hk0, cv', v', hi', hcv, hv, hh, ⟨⟩⟩ | ⟨hk0, cv', hcv, ⟨⟩⟩ |
      ⟨hk0, cv', caps', hcv, hc, ⟨⟩⟩ | ⟨hk0, cv', np', nf', fam', hcv, ha, hb, hf, ⟨⟩⟩ |
      ⟨hk0, cv', mi', rp', o, c, k', rules', hcv, ha, hb, ho, hn, hkk, hr, ⟨⟩⟩
    all_goals first | exact ⟨by rw [hk, hk0], hcv, hc⟩ | skip
  · rintro ⟨hk, hcv, hc⟩
    unfold decCI; simp [hk, hcv, hc]

/-- **A `ctorInfo` record, word by word.** -/
theorem decCI_ctorInfo_iff {R : Nat → Option Word} {p : Nat} {cv : IConstantVal} {np nf : Nat}
    {fam : NIdx} :
    decCI R p = some (.ctorInfo cv np nf fam) ↔
      nat? R p = some 4 ∧ decCV R (p + CI.cv.toNat) = some cv ∧
      nat? R (p + CI.ctorNparams.toNat) = some np ∧ nat? R (p + CI.ctorNfields.toNat) = some nf ∧
      hd? R (p + CI.ctorInduct.toNat) = some fam := by
  constructor
  · intro h
    obtain ⟨wk, e, hx⟩ := decCI_cases h
    have hk : nat? R p = some wk.toNat := by simp [nat?, e]
    rcases hx with ⟨hk0, cv', hcv, ⟨⟩⟩ | ⟨hk0, cv', v', hi', hcv, hv, hh, ⟨⟩⟩ | ⟨hk0, cv', hcv, ⟨⟩⟩ |
      ⟨hk0, cv', caps', hcv, hc, ⟨⟩⟩ | ⟨hk0, cv', np', nf', fam', hcv, ha, hb, hf, ⟨⟩⟩ |
      ⟨hk0, cv', mi', rp', o, c, k', rules', hcv, ha, hb, ho, hn, hkk, hr, ⟨⟩⟩
    all_goals first | exact ⟨by rw [hk, hk0], hcv, ha, hb, hf⟩ | skip
  · rintro ⟨hk, hcv, ha, hb, hf⟩
    unfold decCI; simp [hk, hcv, ha, hb, hf]

/-- **A `recInfo` record, word by word.** -/
theorem decCI_recInfo_iff {R : Nat → Option Word} {p : Nat} {cv : IConstantVal} {mi rp : Nat}
    {k : Bool} {rules : List IRecRule} :
    decCI R p = some (.recInfo cv mi rp k rules) ↔
      nat? R p = some 5 ∧ decCV R (p + CI.cv.toNat) = some cv ∧
      nat? R (p + CI.recMajor.toNat) = some mi ∧ nat? R (p + CI.recPrefix.toNat) = some rp ∧
      bool? R (p + CI.recIsK.toNat) = some k ∧
      ∃ o c, nat? R (p + CI.recRulesOff.toNat) = some o ∧
        nat? R (p + CI.recRulesLen.toNat) = some c ∧ decRules R o c = some rules := by
  constructor
  · intro h
    obtain ⟨wk, e, hx⟩ := decCI_cases h
    have hk : nat? R p = some wk.toNat := by simp [nat?, e]
    rcases hx with ⟨hk0, cv', hcv, ⟨⟩⟩ | ⟨hk0, cv', v', hi', hcv, hv, hh, ⟨⟩⟩ | ⟨hk0, cv', hcv, ⟨⟩⟩ |
      ⟨hk0, cv', caps', hcv, hc, ⟨⟩⟩ | ⟨hk0, cv', np', nf', fam', hcv, ha, hb, hf, ⟨⟩⟩ |
      ⟨hk0, cv', mi', rp', o, c, k', rules', hcv, ha, hb, ho, hn, hkk, hr, ⟨⟩⟩
    all_goals first | exact ⟨by rw [hk, hk0], hcv, ha, hb, hkk, o, c, ho, hn, hr⟩ | skip
  · rintro ⟨hk, hcv, ha, hb, hkk, o, c, ho, hn, hr⟩
    unfold decCI; simp [hk, hcv, ha, hb, hkk, ho, hn, hr]

end L.Arena
