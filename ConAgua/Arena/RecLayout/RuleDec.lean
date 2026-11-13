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

end L.Arena
