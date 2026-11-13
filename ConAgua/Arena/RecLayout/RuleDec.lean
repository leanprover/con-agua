module

public import ConAgua.Arena.ErecRd

@[expose] public section

/-!
# A recursor rule record's words: the decoder's facts

The facts about `decRule` and `decRules` (`Arena/EnvRec.lean`) that proofs use, stated over the
named offsets of `RecLayout/Rule.lean`: what a decoded rule says about each word
(`decRule_eq_some`, `decRule_fields`, `decRule_fire`; at L's word addresses, `decRule_rd`), the
rule built from its words (`decRule_of`), a rule whose words are carried to another reader
(`decRule_congr`) or refired (`decRule_refire`), and a slice of rules one by one (`decRules_get`,
`decRules_succ`). Proofs use these instead of unfolding `decRule` or an offset, so that a change of
the layout ends here.

The constructor is at offset 0 (`Rule.ctor`), and L reads it as `EREC⦃q⦄`: the lemmas say `q`
there.
-/

open ConRon.Arena

namespace L.Arena

/-- **A rule's fire, at its words**: the kind word (`0` plain, `1` nested, `2` levels) and the
slices the kind has. -/
def RuleFireAt (R : Nat → Option Word) (q : Nat) : IRecRuleFire → Prop
  | .plain => nat? R (q + Rule.fire.toNat) = some 0
  | .nested lv ps => nat? R (q + Rule.fire.toNat) = some 1 ∧
      hlist? R (q + Rule.lvlsOff.toNat) = some lv ∧ hlist? R (q + Rule.pinsOff.toNat) = some ps
  | .levels lv => nat? R (q + Rule.fire.toNat) = some 2 ∧ hlist? R (q + Rule.lvlsOff.toNat) = some lv

theorem ctor_add (q : Nat) : q + Rule.ctor.toNat = q := rfl

/-- A slice field from its two words. -/
theorem hlist?_of {k : IdxKind} {R : Nat → Option Word} {i : Nat} {o l : Word} {xs : List (Idx k)}
    (ho : R i = some o) (hl : R (i + 1) = some l) (hs : hslice? R o.toNat l.toNat = some xs) :
    hlist? R i = some xs := by
  simp [hlist?, nat?, ho, hl, hs]

/-- **A decoded rule, word by word.** -/
theorem decRule_eq_some {R : Nat → Option Word} {q : Nat} {rl : IRecRule} :
    decRule R q = some rl ↔
      hd? R q = some rl.ctor ∧ nat? R (q + Rule.nfields.toNat) = some rl.nfields ∧
      hd? R (q + Rule.rhs.toNat) = some rl.rhs ∧ RuleFireAt R q rl.fire := by
  rcases rl with ⟨c, nf, f, r⟩
  unfold decRule
  rw [ctor_add]
  cases hk : nat? R (q + Rule.fire.toNat) with
  | none => cases f <;> simp [RuleFireAt, hk]
  | some k =>
    cases hl : hlist? (k := .level) R (q + Rule.lvlsOff.toNat) <;>
    cases hp : hlist? (k := .expr) R (q + Rule.pinsOff.toNat) <;>
    cases f <;>
    rcases k with _ | _ | _ | k <;>
    simp [RuleFireAt, hk, hl, hp, Option.bind_eq_some_iff, and_comm, and_left_comm, and_assoc]

/-- The rule built from its words. -/
theorem decRule_of {R : Nat → Option Word} {q : Nat} {rl : IRecRule}
    (hc : hd? R q = some rl.ctor) (hn : nat? R (q + Rule.nfields.toNat) = some rl.nfields)
    (hr : hd? R (q + Rule.rhs.toNat) = some rl.rhs) (hf : RuleFireAt R q rl.fire) :
    decRule R q = some rl :=
  decRule_eq_some.mpr ⟨hc, hn, hr, hf⟩

/-- The plain fields of a decoded rule. -/
theorem decRule_fields {R : Nat → Option Word} {q : Nat} {rl : IRecRule} (h : decRule R q = some rl) :
    hd? R q = some rl.ctor ∧ nat? R (q + Rule.nfields.toNat) = some rl.nfields ∧
      hd? R (q + Rule.rhs.toNat) = some rl.rhs :=
  let ⟨a, b, c, _⟩ := decRule_eq_some.mp h; ⟨a, b, c⟩

/-- A decoded rule's fire, at its words. -/
theorem decRule_fire {R : Nat → Option Word} {q : Nat} {rl : IRecRule} (h : decRule R q = some rl) :
    RuleFireAt R q rl.fire :=
  (decRule_eq_some.mp h).2.2.2

/-- A decoded rule's constructor word. -/
theorem decRule_ctorR {R : Nat → Option Word} {q : Nat} {rl : IRecRule} (h : decRule R q = some rl) :
    ∃ w, R q = some w ∧ w.toNat < 2 ^ 32 ∧ rl.ctor = decI w :=
  hd?_some (decRule_fields h).1

/-- A fire's kind word, as a number. -/
theorem RuleFireAt.kind {R : Nat → Option Word} {q : Nat} {f : IRecRuleFire} (h : RuleFireAt R q f) :
    ∃ w, R (q + Rule.fire.toNat) = some w ∧
      w.toNat = (match f with | .plain => 0 | .nested .. => 1 | .levels .. => 2) := by
  have hn : ∀ {n}, nat? R (q + Rule.fire.toNat) = some n → ∃ w, R (q + Rule.fire.toNat) = some w ∧
      w.toNat = n := fun hn => by simpa [nat?] using hn
  cases f with
  | plain => exact hn h
  | nested => exact hn h.1
  | levels => exact hn h.1

/-- A fire's words carried to another reader (each word of the record `R` reads at `q + j`, `R'`
reads at `q' + j`; the slices through `ArrExt`). -/
theorem RuleFireAt.congr {R R' : Nat → Option Word} {q q' : Nat} {f : IRecRuleFire}
    (w : ∀ j < Rule.size.toNat, ∀ v, R (q + j) = some v → R' (q' + j) = some v) (he : ArrExt R R')
    (h : RuleFireAt R q f) : RuleFireAt R' q' f := by
  have wn : ∀ i < Rule.size.toNat, ∀ {n}, nat? R (q + i) = some n → nat? R' (q' + i) = some n :=
    fun i hi n hn => by
      simp only [nat?, Option.map_eq_some_iff] at hn ⊢
      obtain ⟨v, hv, rfl⟩ := hn; exact ⟨v, w i hi v hv, rfl⟩
  have wl : ∀ {k : IdxKind} (i : Nat), i + 1 < Rule.size.toNat → ∀ {l : List (Idx k)},
      hlist? R (q + i) = some l → hlist? R' (q' + i) = some l := fun i hi l hl => by
    simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hl ⊢
    obtain ⟨o, ho, c, hc, hs⟩ := hl
    refine ⟨o, wn i (by omega) ho, c, ?_, he.hslice? hs⟩
    have := wn (i + 1) hi (n := c) (by rw [← Nat.add_assoc]; exact hc)
    rwa [← Nat.add_assoc] at this
  have hfi := Rule.fire_lt
  have hl : Rule.lvlsOff.toNat + 1 < Rule.size.toNat := by rw [← Rule.lvlsLen_toNat]; exact Rule.lvlsLen_lt
  have hp : Rule.pinsOff.toNat + 1 < Rule.size.toNat := by rw [← Rule.pinsLen_toNat]; exact Rule.pinsLen_lt
  cases f with
  | plain => exact wn _ hfi h
  | nested => exact ⟨wn _ hfi h.1, wl _ hl h.2.1, wl _ hp h.2.2⟩
  | levels => exact ⟨wn _ hfi h.1, wl _ hl h.2⟩

/-- **A rule's words carried to another reader** (each word `R` reads at `q + j`, `R'` reads at
`q' + j`; the fire's slices through `ArrExt`) decode the same rule. -/
theorem decRule_congr {R R' : Nat → Option Word} {q q' : Nat} {rl : IRecRule}
    (w : ∀ j < Rule.size.toNat, ∀ v, R (q + j) = some v → R' (q' + j) = some v) (he : ArrExt R R')
    (h : decRule R q = some rl) : decRule R' q' = some rl := by
  obtain ⟨hc, hn, hr, hf⟩ := decRule_eq_some.mp h
  have wd : ∀ {k : IdxKind} (i : Nat), i < Rule.size.toNat → ∀ {x : Idx k}, hd? R (q + i) = some x →
      hd? R' (q' + i) = some x := fun i hi x hx => by
    simp only [hd?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx ⊢
    obtain ⟨v, hv, hx⟩ := hx; exact ⟨v, w i hi v hv, hx⟩
  refine decRule_of (wd 0 Rule.ctor_lt hc) ?_ (wd _ Rule.rhs_lt hr) (hf.congr w he)
  simp only [nat?, Option.map_eq_some_iff] at hn ⊢
  obtain ⟨v, hv, e⟩ := hn; exact ⟨v, w _ Rule.nfields_lt v hv, e⟩

/-- A rule record's field offsets (the words a field-by-field copy carries). -/
def Rule.fields : List Word :=
  [Rule.ctor, Rule.nfields, Rule.fire, Rule.lvlsOff, Rule.lvlsLen, Rule.pinsOff, Rule.pinsLen, Rule.rhs]

/-- `RuleFireAt.congr` for a reader that agrees on the record's fields only. -/
theorem RuleFireAt.congrF {R R' : Nat → Option Word} {q q' : Nat} {f : IRecRuleFire}
    (w : ∀ o ∈ Rule.fields, ∀ v, R (q + o.toNat) = some v → R' (q' + o.toNat) = some v)
    (he : ArrExt R R') (h : RuleFireAt R q f) : RuleFireAt R' q' f := by
  have wn : ∀ o ∈ Rule.fields, ∀ {n}, nat? R (q + o.toNat) = some n → nat? R' (q' + o.toNat) = some n :=
    fun o ho n hn => by
      simp only [nat?, Option.map_eq_some_iff] at hn ⊢
      obtain ⟨v, hv, rfl⟩ := hn; exact ⟨v, w o ho v hv, rfl⟩
  have wl : ∀ {k : IdxKind} (o l : Word), o ∈ Rule.fields → l ∈ Rule.fields → l.toNat = o.toNat + 1 →
      ∀ {xs : List (Idx k)}, hlist? R (q + o.toNat) = some xs → hlist? R' (q' + o.toNat) = some xs :=
    fun o l ho hl e xs hx => by
      simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx ⊢
      obtain ⟨a, ha, c, hc, hs⟩ := hx
      refine ⟨a, wn o ho ha, c, ?_, he.hslice? hs⟩
      have := wn l hl (n := c) (by rw [e, ← Nat.add_assoc]; exact hc)
      rwa [e, ← Nat.add_assoc] at this
  cases f with
  | plain => exact wn _ (by simp [Rule.fields]) h
  | nested => exact ⟨wn _ (by simp [Rule.fields]) h.1,
      wl _ _ (by simp [Rule.fields]) (by simp [Rule.fields]) Rule.lvlsLen_toNat h.2.1,
      wl _ _ (by simp [Rule.fields]) (by simp [Rule.fields]) Rule.pinsLen_toNat h.2.2⟩
  | levels => exact ⟨wn _ (by simp [Rule.fields]) h.1,
      wl _ _ (by simp [Rule.fields]) (by simp [Rule.fields]) Rule.lvlsLen_toNat h.2⟩

/-- **`decRule_congr` for a reader that agrees on the record's fields only** (a field-by-field
copy: the words between the fields are not carried). -/
theorem decRule_congrF {R R' : Nat → Option Word} {q q' : Nat} {rl : IRecRule}
    (w : ∀ o ∈ Rule.fields, ∀ v, R (q + o.toNat) = some v → R' (q' + o.toNat) = some v)
    (he : ArrExt R R') (h : decRule R q = some rl) : decRule R' q' = some rl := by
  obtain ⟨hc, hn, hr, hf⟩ := decRule_eq_some.mp h
  have wd : ∀ {k : IdxKind} (o : Word), o ∈ Rule.fields → ∀ {x : Idx k},
      hd? R (q + o.toNat) = some x → hd? R' (q' + o.toNat) = some x := fun o ho x hx => by
    simp only [hd?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx ⊢
    obtain ⟨v, hv, hx⟩ := hx; exact ⟨v, w o ho v hv, hx⟩
  refine decRule_of (wd Rule.ctor (by simp [Rule.fields]) hc) ?_ (wd _ (by simp [Rule.fields]) hr)
    (hf.congrF w he)
  simp only [nat?, Option.map_eq_some_iff] at hn ⊢
  obtain ⟨v, hv, e⟩ := hn; exact ⟨v, w _ (by simp [Rule.fields]) v hv, e⟩

/-- **A rule refired**: its plain fields' words carried to `R'` at `q'`, its fire `f` at the words
there, decode the rule with the fire `f`. -/
theorem decRule_refire {R R' : Nat → Option Word} {q q' : Nat} {rl : IRecRule} {f : IRecRuleFire}
    (h : decRule R q = some rl) (h0 : R' q' = R q)
    (h1 : R' (q' + Rule.nfields.toNat) = R (q + Rule.nfields.toNat))
    (h8 : R' (q' + Rule.rhs.toNat) = R (q + Rule.rhs.toNat)) (hf : RuleFireAt R' q' f) :
    decRule R' q' = some { rl with fire := f } := by
  obtain ⟨hc, hn, hr⟩ := decRule_fields h
  exact decRule_of (by simpa only [hd?, h0] using hc) (by simpa only [nat?, h1] using hn)
    (by simpa only [hd?, h8] using hr) hf

/-- **A decoded rule at L's word addresses** `q + Rule.f` (any reader `R` with its word read `rd`:
the record pool, an array). The constructor at `q` (offset 0). -/
theorem decRule_rd {R : Nat → Option Word} {rd : Word → Word} {q : Word} {rl : IRecRule}
    (hR : RdOK R rd) (h : decRule R q.toNat = some rl) :
    (rd q).toNat < 2 ^ 32 ∧ rl.ctor = decI (rd q) ∧ rl.nfields = (rd (q + Rule.nfields)).toNat ∧
      (rd (q + Rule.fire) = 0 → rl.fire = .plain) ∧
      (rd (q + Rule.fire) = 1 → ∃ lv pins, rl.fire = .nested lv pins ∧
        hslice? R (rd (q + Rule.lvlsOff)).toNat (rd (q + Rule.lvlsLen)).toNat = some lv ∧
        hslice? R (rd (q + Rule.pinsOff)).toNat (rd (q + Rule.pinsLen)).toNat = some pins) ∧
      (rd (q + Rule.fire) = 2 → ∃ lv, rl.fire = .levels lv ∧
        hslice? R (rd (q + Rule.lvlsOff)).toNat (rd (q + Rule.lvlsLen)).toNat = some lv) ∧
      (rd (q + Rule.rhs)).toNat < 2 ^ 32 ∧ rl.rhs = decI (rd (q + Rule.rhs)) := by
  obtain ⟨hc, hn, hr, hf⟩ := decRule_eq_some.mp h
  obtain ⟨w0, hw0, hl0, e0⟩ := hd?_some hc
  obtain ⟨w8, hw8, hl8, e8⟩ := hd?_some hr
  obtain ⟨w1, hw1, e1⟩ : ∃ w, R (q.toNat + Rule.nfields.toNat) = some w ∧ w.toNat = rl.nfields := by
    simpa [nat?] using hn
  have sl : ∀ {k : IdxKind} (o l : Word), l.toNat = o.toNat + 1 → ∀ {xs : List (Idx k)},
      hlist? R (q.toNat + o.toNat) = some xs →
      hslice? R (rd (q + o)).toNat (rd (q + l)).toNat = some xs := fun o l hl xs hx => by
    simp only [hlist?, nat?, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at hx
    obtain ⟨_, ⟨wo, hwo, rfl⟩, _, ⟨wl, hwl, rfl⟩, hs⟩ := hx
    rw [hR.at _ rfl hwo, hR.at _ hl (by rw [← Nat.add_assoc]; exact hwl)]
    exact hs
  obtain ⟨wk, hwk, ek⟩ := hf.kind
  have e3 := hR.at _ rfl hwk
  rw [hR.rd _ _ hw0, hR.at _ rfl hw1, hR.at _ rfl hw8, e3]
  have kw : ∀ n : Nat, n < 2 ^ 64 → (wk = UInt64.ofNat n ↔ wk.toNat = n) := fun n hn => by
    constructor
    · rintro rfl; simp; omega
    · intro e; apply UInt64.toNat_inj.mp; simp; omega
  refine ⟨hl0, e0, e1.symm, ?_, ?_, ?_, hl8, e8⟩ <;> intro hw <;>
    have := (kw _ (by decide)).mp hw <;> clear hw <;>
    rcases rl with ⟨c, nf, f, r⟩ <;> cases f <;> dsimp only at ek hf this ⊢ <;>
    first | omega | rfl | skip
  · exact ⟨_, _, rfl, sl _ _ Rule.lvlsLen_toNat hf.2.1, sl _ _ Rule.pinsLen_toNat hf.2.2⟩
  · exact ⟨_, rfl, sl _ _ Rule.lvlsLen_toNat hf.2⟩

/-- A decoded rule's constructor (offset 0). -/
theorem decRule_ctor {R : Nat → Option Word} {q : Nat} {rl : IRecRule} (h : decRule R q = some rl) :
    hd? R q = some rl.ctor :=
  (decRule_fields h).1

/-- **A rule's fire datum at its words**: kind `0` plain; otherwise levels or nested, its levels
the slice at `Rule.lvlsOff`, `Rule.lvlsLen`. -/
theorem decRule_fireE {R : Nat → Option Word} {rd : Word → Word} {q : Word} {rl : IRecRule}
    (hR : RdOK R rd) (h : decRule R q.toNat = some rl) :
    (rd (q + Rule.fire) = 0 ∧ rl.fire = .plain) ∨
    (rd (q + Rule.fire) ≠ 0 ∧ ∃ lvls, (rl.fire = .levels lvls ∨ ∃ pins, rl.fire = .nested lvls pins) ∧
      hslice? R (rd (q + Rule.lvlsOff)).toNat (rd (q + Rule.lvlsLen)).toNat = some lvls) := by
  obtain ⟨-, -, -, h0, h1, h2, -, -⟩ := decRule_rd hR h
  obtain ⟨wk, hwk, ek⟩ := (decRule_fire h).kind
  have e3 := hR.at _ rfl hwk
  rcases rl with ⟨c, nf, f, r⟩
  cases f with
  | plain => exact .inl ⟨by rw [e3]; exact UInt64.toNat_inj.mp (by simpa using ek), rfl⟩
  | nested lv ps =>
    have e : rd (q + Rule.fire) = 1 := by rw [e3]; exact UInt64.toNat_inj.mp (by simpa using ek)
    obtain ⟨lv', ps', hf, hl, -⟩ := h1 e
    cases hf
    exact .inr ⟨by rw [e]; decide, lv, .inr ⟨ps, rfl⟩, hl⟩
  | levels lv =>
    have e : rd (q + Rule.fire) = 2 := by rw [e3]; exact UInt64.toNat_inj.mp (by simpa using ek)
    obtain ⟨lv', hf, hl⟩ := h2 e
    cases hf
    exact .inr ⟨by rw [e]; decide, lv, .inl rfl, hl⟩

/-- A rule whose fire kind word is not `1` is not nested. -/
theorem decRule_notNested {R : Nat → Option Word} {rd : Word → Word} {q : Word} {rl : IRecRule}
    (hR : RdOK R rd) (h : decRule R q.toNat = some rl) (h1 : rd (q + Rule.fire) ≠ 1) :
    rl.fire = .plain ∨ ∃ lvls, rl.fire = .levels lvls := by
  obtain ⟨wk, hwk, ek⟩ := (decRule_fire h).kind
  have e3 := hR.at _ rfl hwk
  rcases rl with ⟨c, nf, f, r⟩
  cases f with
  | plain => exact .inl rfl
  | nested => exact absurd (by rw [e3]; exact UInt64.toNat_inj.mp (by simpa using ek)) h1
  | levels lv => exact .inr ⟨lv, rfl⟩


/-! ## Rule slices -/

theorem decRules_succ (R : Nat → Option Word) (o n : Nat) :
    decRules R o (n + 1) = (do
      let r ← decRule R o
      let rs ← decRules R (o + Rule.size.toNat) n
      pure (r :: rs)) := by
  simp only [decRules, List.range_succ_eq_map, List.mapM_cons, List.mapM_map]
  congr 1; funext x; congr 1
  apply congrArg (fun f => List.mapM f (List.range n))
  funext j
  simp only [Function.comp]
  congr 1
  rw [Nat.mul_succ]; omega

/-- The rules of a decoded slice, one by one. -/
theorem decRules_get {R : Nat → Option Word} {off cnt : Nat} {rs : List IRecRule}
    (h : decRules R off cnt = some rs) :
    rs.length = cnt ∧ ∀ j, j < cnt → decRule R (off + Rule.size.toNat * j) = rs[j]? := by
  unfold decRules at h
  have key : ∀ (l : List Nat) (rs : List IRecRule),
      l.mapM (fun j => decRule R (off + Rule.size.toNat * j)) = some rs →
      rs.length = l.length ∧ ∀ j (hj : j < l.length),
        decRule R (off + Rule.size.toNat * l[j]) = rs[j]? := by
    intro l
    induction l with
    | nil => intro rs h; simp at h; subst h; simp
    | cons x l ih =>
      intro rs h
      simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨y, hy, ys, hys, h⟩ := h
      cases h
      obtain ⟨h1, h2⟩ := ih ys hys
      refine ⟨by simp [h1], fun j hj => ?_⟩
      cases j with
      | zero => simp [hy]
      | succ j => simpa using h2 j (by simpa using hj)
  obtain ⟨h1, h2⟩ := key _ _ h
  simp only [List.length_range] at h1
  refine ⟨h1, fun j hj => ?_⟩
  have := h2 j (by simpa using hj)
  rwa [List.getElem_range] at this

theorem decRules_length {R : Nat → Option Word} {o l : Nat} {xs : List IRecRule}
    (h : decRules R o l = some xs) : xs.length = l :=
  (decRules_get h).1

/-- A rule slice's address arithmetic does not wrap on a decoded record. -/
theorem rule_idx {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd) (ro i : Word)
    {rl : IRecRule} (h : decRule R (ro.toNat + Rule.size.toNat * i.toNat) = some rl) :
    (ro + Rule.size * i).toNat = ro.toNat + Rule.size.toNat * i.toNat := by
  obtain ⟨w, hw, -⟩ := decRule_ctorR h
  have hlt := hR.lt _ _ hw
  have := Rule.size_le
  rw [UInt64.toNat_add, UInt64.toNat_mul]
  rw [Nat.mod_eq_of_lt (a := Rule.size.toNat * i.toNat) (by omega)]
  omega

/-- The next rule's records, at the word address. -/
theorem decRules_shift {R : Nat → Option Word} {o : Word} {k : Nat} {rs : List IRecRule}
    (h : decRules R (o.toNat + Rule.size.toNat) k = some rs) (hR : ∀ i v, R i = some v → i < 2 ^ 64) :
    decRules R (o + Rule.size).toNat k = some rs := by
  cases k with
  | zero => simpa [decRules] using h
  | succ k =>
  have h' := h
  rw [decRules_succ] at h'
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h'
  obtain ⟨r0, hr0, -⟩ := h'
  obtain ⟨w, hw, -⟩ := hd?_some (decRule_ctor hr0)
  have := hR _ _ hw
  have := Rule.size_le
  have e : (o + Rule.size).toNat = o.toNat + Rule.size.toNat := by
    rw [UInt64.toNat_add]; omega
  rw [e]; exact h

/-! ## A rule's words, written field by field -/

/-- **A rule record's words** at `q` of a reader: each field's word (a writer's postcondition;
`decRule_of_words` decodes it, the fire from `RuleRecW.plain`/`levels`/`nested`). -/
structure RuleRecW (a : Nat → Option Word) (q : Nat) (c nf fk lo ll po pl rhs : Word) : Prop where
  ctor : a (q + Rule.ctor.toNat) = some c
  nf : a (q + Rule.nfields.toNat) = some nf
  fk : a (q + Rule.fire.toNat) = some fk
  lo : a (q + Rule.lvlsOff.toNat) = some lo
  ll : a (q + Rule.lvlsLen.toNat) = some ll
  po : a (q + Rule.pinsOff.toNat) = some po
  pl : a (q + Rule.pinsLen.toNat) = some pl
  rhs : a (q + Rule.rhs.toNat) = some rhs

/-- The record's words carried to another reader that holds the same `Rule.size` words. -/
theorem RuleRecW.shift {a b : Nat → Option Word} {q e : Nat} {w0 w1 w2 w3 w4 w5 w6 w7 : Word}
    (h : RuleRecW a q w0 w1 w2 w3 w4 w5 w6 w7)
    (hw : ∀ j < Rule.size.toNat, b (e + j) = a (q + j)) : RuleRecW b e w0 w1 w2 w3 w4 w5 w6 w7 :=
  ⟨(hw _ Rule.ctor_lt).trans h.ctor, (hw _ Rule.nfields_lt).trans h.nf,
    (hw _ Rule.fire_lt).trans h.fk, (hw _ Rule.lvlsOff_lt).trans h.lo,
    (hw _ Rule.lvlsLen_lt).trans h.ll, (hw _ Rule.pinsOff_lt).trans h.po,
    (hw _ Rule.pinsLen_lt).trans h.pl, (hw _ Rule.rhs_lt).trans h.rhs⟩

section words
variable {a : Nat → Option Word} {q : Nat} {c nf fk lo ll po pl rhs : Word}

/-- A `plain` fire's words. -/
theorem RuleRecW.plain (h : RuleRecW a q c nf fk lo ll po pl rhs) (hk : fk = 0) :
    RuleFireAt a q .plain := by
  simp [RuleFireAt, nat?, h.fk, hk]

/-- A `levels` fire's words. -/
theorem RuleRecW.levels (h : RuleRecW a q c nf fk lo ll po pl rhs) (hk : fk = 2)
    {lv : List LIdx} (hs : hslice? a lo.toNat ll.toNat = some lv) : RuleFireAt a q (.levels lv) := by
  have hl := h.ll
  rw [Rule.lvlsLen_toNat, ← Nat.add_assoc] at hl
  exact ⟨by simp [nat?, h.fk, hk], hlist?_of h.lo hl hs⟩

/-- A `nested` fire's words. -/
theorem RuleRecW.nested (h : RuleRecW a q c nf fk lo ll po pl rhs) (hk : fk = 1)
    {lv : List LIdx} {ps : List EIdx} (hs : hslice? a lo.toNat ll.toNat = some lv)
    (hp : hslice? a po.toNat pl.toNat = some ps) : RuleFireAt a q (.nested lv ps) := by
  have hl := h.ll
  rw [Rule.lvlsLen_toNat, ← Nat.add_assoc] at hl
  have hpl := h.pl
  rw [Rule.pinsLen_toNat, ← Nat.add_assoc] at hpl
  exact ⟨by simp [nat?, h.fk, hk], hlist?_of h.lo hl hs, hlist?_of h.po hpl hp⟩

/-- **A rule's words decode** (the fire given). -/
theorem decRule_of_words (h : RuleRecW a q c nf fk lo ll po pl rhs) (hc : c.toNat < 2 ^ 32)
    (hr : rhs.toNat < 2 ^ 32) {f : IRecRuleFire} (hf : RuleFireAt a q f) :
    decRule a q = some ⟨decI c, nf.toNat, f, decI rhs⟩ := by
  have hc' := h.ctor
  rw [ctor_add] at hc'
  exact decRule_of (by simp [hd?, hc', hc]) (by simp [nat?, h.nf]) (by simp [hd?, h.rhs, hr]) hf

end words

set_option linter.deprecated false in
/-- **A rule written field by field** (eight word stores into array `A` at `q + Rule.f`, in the
fields' order) holds its words. -/
theorem ruleRecW_set64 {m : Mem} {A : TieredArray} {q w0 w1 w2 w3 w4 w5 w6 w7 : Word}
    (hb : q.toNat + Rule.size.toNat ≤ (m.arr64 A).size) (h64 : q.toNat + Rule.size.toNat < 2 ^ 64) :
    RuleRecW (aread ((((((((((m.set64 A (q + Rule.ctor) w0).set64 A (q + Rule.nfields) w1).set64 A
      (q + Rule.fire) w2).set64 A (q + Rule.lvlsOff) w3).set64 A (q + Rule.lvlsLen) w4).set64 A
      (q + Rule.pinsOff) w5).set64 A (q + Rule.pinsLen) w6).set64 A (q + Rule.rhs) w7).arr64 A)))
      q.toNat w0 w1 w2 w3 w4 w5 w6 w7 := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩ := Rule.order
  have e : ∀ f : Word, f.toNat < Rule.size.toNat → (q + f).toNat = q.toNat + f.toNat := fun f hf => by
    rw [UInt64.toNat_add]; omega
  simp only [Mem.arr64_set64_same, e _ Rule.ctor_lt, e _ Rule.nfields_lt, e _ Rule.fire_lt,
    e _ Rule.lvlsOff_lt, e _ Rule.lvlsLen_lt, e _ Rule.pinsOff_lt, e _ Rule.pinsLen_lt,
    e _ Rule.rhs_lt]
  constructor <;> simp (disch := omega) only [aread_apply, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds, Array.size_setIfInBounds, if_pos, if_neg, ite_true]

end L.Arena
