module

public import ConAgua.Arena.ErecRd

@[expose] public section

/-!
# An `IIndCaps` record's words: the decoder's facts

The facts about `decCaps` (`Arena/EnvRec.lean`) that proofs use, stated over the named offsets of
`RecLayout/Caps.lean`: what a decoded record says about each word (`decCaps_eq_some`, and at L's
word addresses, `decCaps_rd`), the record built from its words, two readers that agree on a
record's words decode it alike (`decCaps_congr`), and an `indInfo` record's capabilities
(`decCI_indInfo`). Proofs use these instead of unfolding `decCaps` or an offset, so that a
change of the layout ends here.
-/

open ConRon.Arena

namespace L.Caps

/-- **The fields' order** (the facts `omega` needs to keep two fields' words apart): the scalar
fields first, then each slice's offset word followed by its length word, the record's size last. -/
theorem order : eta.toNat < nIdx.toNat ∧ nIdx.toNat < neverZero.toNat ∧
    neverZero.toNat < allOff.toNat ∧ allLen.toNat = allOff.toNat + 1 ∧
    allLen.toNat < nparams.toNat ∧ nparams.toNat < ctorsOff.toNat ∧
    ctorsLen.toNat = ctorsOff.toNat + 1 ∧ ctorsLen.toNat < size.toNat := by
  simp [eta, nIdx, neverZero, allOff, allLen, nparams, ctorsOff, ctorsLen, size]

end L.Caps

namespace L.CI

/-- The capabilities follow the kind word and the constant value (4 words) directly. -/
theorem indCaps_toNat : indCaps.toNat = 5 := by simp [indCaps]

end L.CI

namespace L.Arena

/-- **A decoded `IIndCaps`, word by word.** -/
theorem decCaps_eq_some {R : Nat → Option Word} {q : Nat} {c : IIndCaps} :
    decCaps R q = some c ↔
      bool? R (q + Caps.eta.toNat) = some c.eta ∧ nat? R (q + Caps.nIdx.toNat) = some c.nIdx ∧
      hlist? R (q + Caps.allOff.toNat) = some c.all ∧
      nat? R (q + Caps.nparams.toNat) = some c.nparams ∧
      hlist? R (q + Caps.ctorsOff.toNat) = some c.ctors ∧
      bool? R (q + Caps.neverZero.toNat) = some c.neverZero := by
  rcases c with ⟨e, n, a, np, cs, nz⟩
  simp only [decCaps, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, IIndCaps.mk.injEq]
  constructor
  · rintro ⟨e', he, n', hn, a', ha, np', hnp, cs', hcs, nz', hnz, rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact ⟨he, hn, ha, hnp, hcs, hnz⟩
  · rintro ⟨he, hn, ha, hnp, hcs, hnz⟩
    exact ⟨_, he, _, hn, _, ha, _, hnp, _, hcs, _, hnz, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The record built from its words. -/
theorem decCaps_of {R : Nat → Option Word} {q : Nat} {c : IIndCaps}
    (he : bool? R (q + Caps.eta.toNat) = some c.eta) (hn : nat? R (q + Caps.nIdx.toNat) = some c.nIdx)
    (ha : hlist? R (q + Caps.allOff.toNat) = some c.all)
    (hnp : nat? R (q + Caps.nparams.toNat) = some c.nparams)
    (hcs : hlist? R (q + Caps.ctorsOff.toNat) = some c.ctors)
    (hnz : bool? R (q + Caps.neverZero.toNat) = some c.neverZero) : decCaps R q = some c :=
  decCaps_eq_some.mpr ⟨he, hn, ha, hnp, hcs, hnz⟩

/-- **An `IIndCaps` record's words** at `q` of a reader: each field's word (a writer's
postcondition; `decCaps_of_words` decodes it). -/
structure CapsRecW (a : Nat → Option Word) (q : Nat) (eta nIdx nz allO allL np ctO ctL : Word) :
    Prop where
  eta : a (q + Caps.eta.toNat) = some eta
  nIdx : a (q + Caps.nIdx.toNat) = some nIdx
  nz : a (q + Caps.neverZero.toNat) = some nz
  allO : a (q + Caps.allOff.toNat) = some allO
  allL : a (q + Caps.allLen.toNat) = some allL
  np : a (q + Caps.nparams.toNat) = some np
  ctO : a (q + Caps.ctorsOff.toNat) = some ctO
  ctL : a (q + Caps.ctorsLen.toNat) = some ctL

/-- The record's words carried to another reader that holds the same `Caps.size` words. -/
theorem CapsRecW.shift {a b : Nat → Option Word} {q e : Nat} {w0 w1 w2 w3 w4 w5 w6 w7 : Word}
    (h : CapsRecW a q w0 w1 w2 w3 w4 w5 w6 w7)
    (hw : ∀ j < Caps.size.toNat, b (e + j) = a (q + j)) : CapsRecW b e w0 w1 w2 w3 w4 w5 w6 w7 :=
  ⟨(hw _ Caps.eta_lt).trans h.eta, (hw _ Caps.nIdx_lt).trans h.nIdx,
    (hw _ Caps.neverZero_lt).trans h.nz, (hw _ Caps.allOff_lt).trans h.allO,
    (hw _ Caps.allLen_lt).trans h.allL, (hw _ Caps.nparams_lt).trans h.np,
    (hw _ Caps.ctorsOff_lt).trans h.ctO, (hw _ Caps.ctorsLen_lt).trans h.ctL⟩

/-- **A record's words decode** (the two slices given). -/
theorem decCaps_of_words {a : Nat → Option Word} {q : Nat} {w0 w1 w2 w3 w4 w5 w6 w7 : Word}
    {xs ys : List NIdx} (h : CapsRecW a q w0 w1 w2 w3 w4 w5 w6 w7)
    (hA : hslice? a w3.toNat w4.toNat = some xs) (hC : hslice? a w6.toNat w7.toNat = some ys) :
    decCaps a q = some (⟨w0 != 0, xs, w5.toNat, w1.toNat, ys, w2 != 0⟩ : IIndCaps) := by
  have hl : ∀ {o : Nat} {wo wl : Word} {zs : List NIdx}, a o = some wo → a (o + 1) = some wl →
      hslice? a wo.toNat wl.toNat = some zs → hlist? a o = some zs := fun ho hl hs => by
    simp only [hlist?, nat?, ho, hl, Option.map_some, Option.bind_eq_bind, Option.bind_some, hs]
  refine decCaps_of (by simp only [bool?, h.eta, Option.map_some])
    (by simp only [nat?, h.nIdx, Option.map_some]) (hl h.allO ?_ hA)
    (by simp only [nat?, h.np, Option.map_some]) (hl h.ctO ?_ hC)
    (by simp only [bool?, h.nz, Option.map_some])
  · rw [Nat.add_assoc, ← Caps.allLen_toNat]; exact h.allL
  · rw [Nat.add_assoc, ← Caps.ctorsLen_toNat]; exact h.ctL

set_option linter.deprecated false in
/-- **A record written field by field** (eight word stores into array `A` at `q + Caps.f`, in
the fields' order) holds its words. -/
theorem capsRecW_set64 {m : Mem} {A : TieredArray} {q w0 w1 w2 w3 w4 w5 w6 w7 : Word}
    (hb : q.toNat + Caps.size.toNat ≤ (m.arr64 A).size) (h64 : q.toNat + Caps.size.toNat < 2 ^ 64) :
    CapsRecW (aread ((((((((((m.set64 A (q + Caps.eta) w0).set64 A (q + Caps.nIdx) w1).set64 A
      (q + Caps.neverZero) w2).set64 A (q + Caps.allOff) w3).set64 A (q + Caps.allLen) w4).set64 A
      (q + Caps.nparams) w5).set64 A (q + Caps.ctorsOff) w6).set64 A (q + Caps.ctorsLen) w7).arr64 A)))
      q.toNat w0 w1 w2 w3 w4 w5 w6 w7 := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩ := Caps.order
  have e : ∀ f : Word, f.toNat < Caps.size.toNat → (q + f).toNat = q.toNat + f.toNat := fun f hf => by
    rw [UInt64.toNat_add]; omega
  simp only [Mem.arr64_set64_same, e _ Caps.eta_lt, e _ Caps.nIdx_lt, e _ Caps.neverZero_lt,
    e _ Caps.allOff_lt, e _ Caps.allLen_lt, e _ Caps.nparams_lt, e _ Caps.ctorsOff_lt,
    e _ Caps.ctorsLen_lt]
  have := Caps.ctorsLen_lt
  constructor <;> simp (disch := omega) only [aread_apply, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds, Array.size_setIfInBounds, if_pos, if_neg, ite_true]

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

/-- **A decoded `IIndCaps` at L's word addresses** `q + Caps.f` (any reader `R` with its word
read `rd`: the record pool, an array). -/
theorem decCaps_rd {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd) {q : Word}
    {c : IIndCaps} (h : decCaps R q.toNat = some c) :
    c.eta = (rd (q + Caps.eta) != 0) ∧ c.nIdx = (rd (q + Caps.nIdx)).toNat ∧
    c.neverZero = (rd (q + Caps.neverZero) != 0) ∧ c.nparams = (rd (q + Caps.nparams)).toNat ∧
    hslice? R (rd (q + Caps.allOff)).toNat (rd (q + Caps.allLen)).toNat = some c.all ∧
    hslice? R (rd (q + Caps.ctorsOff)).toNat (rd (q + Caps.ctorsLen)).toNat = some c.ctors := by
  obtain ⟨he, hn, ha, hnp, hcs, hnz⟩ := decCaps_eq_some.mp h
  obtain ⟨we, hwe, e1⟩ := bool?_word he
  obtain ⟨wn, hwn, e2⟩ := nat?_word hn
  obtain ⟨wz, hwz, e3⟩ := bool?_word hnz
  obtain ⟨wp, hwp, e4⟩ := nat?_word hnp
  obtain ⟨ao, al, hao, hal, has⟩ := hlist?_words ha
  obtain ⟨co, cl, hco, hcl, hcs⟩ := hlist?_words hcs
  rw [Nat.add_assoc, ← Caps.allLen_toNat] at hal
  rw [Nat.add_assoc, ← Caps.ctorsLen_toNat] at hcl
  rw [hR.at _ rfl hwe, hR.at _ rfl hwn, hR.at _ rfl hwz, hR.at _ rfl hwp, hR.at _ rfl hao,
    hR.at _ rfl hal, hR.at _ rfl hco, hR.at _ rfl hcl]
  exact ⟨e1.symm, e2.symm, e3.symm, e4.symm, has, hcs⟩

/-- **A record's words carried to another reader** (each word `R` reads at `q + j`, `R'` reads at
`q' + j`; the slices through `ArrExt`) decode the same `IIndCaps`. -/
theorem decCaps_congr {R R' : Nat → Option Word} {q q' : Nat} {c : IIndCaps}
    (w : ∀ j < Caps.size.toNat, ∀ v, R (q + j) = some v → R' (q' + j) = some v) (he : ArrExt R R')
    (h : decCaps R q = some c) : decCaps R' q' = some c := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := decCaps_eq_some.mp h
  have wb : ∀ f : Word, f.toNat < Caps.size.toNat → ∀ {b}, bool? R (q + f.toNat) = some b →
      bool? R' (q' + f.toNat) = some b := fun f hf b hb => by
    obtain ⟨v, hv, rfl⟩ := bool?_word hb
    simp [bool?, w _ hf v hv]
  have wn : ∀ f : Word, f.toNat < Caps.size.toNat → ∀ {n}, nat? R (q + f.toNat) = some n →
      nat? R' (q' + f.toNat) = some n := fun f hf n hn => by
    obtain ⟨v, hv, rfl⟩ := nat?_word hn
    simp [nat?, w _ hf v hv]
  have wl : ∀ {k : IdxKind} (f g : Word), f.toNat < Caps.size.toNat → g.toNat < Caps.size.toNat →
      g.toNat = f.toNat + 1 → ∀ {l : List (Idx k)}, hlist? R (q + f.toNat) = some l →
      hlist? R' (q' + f.toNat) = some l := fun f g hf hg hfg l hl => by
    simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hl ⊢
    obtain ⟨o, ho, c, hc, hs⟩ := hl
    refine ⟨o, wn f hf ho, c, ?_, he.hslice? hs⟩
    have := wn g hg (n := c) (by rw [hfg, ← Nat.add_assoc]; exact hc)
    rwa [hfg, ← Nat.add_assoc] at this
  exact decCaps_of (wb _ Caps.eta_lt h1) (wn _ Caps.nIdx_lt h2)
    (wl _ _ Caps.allOff_lt Caps.allLen_lt Caps.allLen_toNat h3) (wn _ Caps.nparams_lt h4)
    (wl _ _ Caps.ctorsOff_lt Caps.ctorsLen_lt Caps.ctorsLen_toNat h5) (wb _ Caps.neverZero_lt h6)

/-! ## In an `indInfo` constant record -/

/-- **An `indInfo` record's value and capabilities.** -/
theorem decCI_indInfo {R : Nat → Option Word} {p : Nat} {cv : IConstantVal} {c : IIndCaps}
    (h : decCI R p = some (.indInfo cv c)) :
    nat? R p = some 3 ∧ decCV R (p + 1) = some cv ∧ decCaps R (p + CI.indCaps.toNat) = some c := by
  unfold decCI at h
  cases hk : nat? R p with
  | none => simp [hk] at h
  | some k =>
    rw [hk] at h
    simp only [Option.bind_eq_bind, Option.bind_some] at h
    match k, h with
    | 0, h => simp [Option.bind_eq_some_iff] at h
    | 1, h => simp [Option.bind_eq_some_iff] at h
    | 2, h => simp [Option.bind_eq_some_iff] at h
    | 3, h =>
      simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
        IConstantInfo.indInfo.injEq] at h
      obtain ⟨y, hy, z, hz, rfl, rfl⟩ := h
      exact ⟨rfl, hy, hz⟩
    | 4, h => simp [Option.bind_eq_some_iff] at h
    | 5, h => simp [Option.bind_eq_some_iff] at h
    | k + 6, h => simp at h

/-- An `indInfo` record's capabilities start with a word that is read (a bound for the record's
addresses). -/
theorem decCI_indInfo_word {R : Nat → Option Word} {p : Nat} {cv : IConstantVal} {c : IIndCaps}
    (h : decCI R p = some (.indInfo cv c)) : ∃ v, R (p + CI.indCaps.toNat) = some v := by
  obtain ⟨-, -, hc⟩ := decCI_indInfo h
  obtain ⟨he, -⟩ := decCaps_eq_some.mp hc
  obtain ⟨w, hw, -⟩ := bool?_word he
  have := Caps.eta_lt
  exact ⟨w, by simpa [Caps.eta] using hw⟩

/-- An `indInfo` record's capabilities at L's word addresses `q + (CI.indCaps + Caps.f)`. -/
theorem decCI_indInfo_rd {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd) {q : Word}
    {cv : IConstantVal} {c : IIndCaps} (h : decCI R q.toNat = some (.indInfo cv c)) :
    c.eta = (rd (q + (CI.indCaps + Caps.eta)) != 0) ∧
    c.nIdx = (rd (q + (CI.indCaps + Caps.nIdx))).toNat ∧
    c.neverZero = (rd (q + (CI.indCaps + Caps.neverZero)) != 0) ∧
    c.nparams = (rd (q + (CI.indCaps + Caps.nparams))).toNat ∧
    hslice? R (rd (q + (CI.indCaps + Caps.allOff))).toNat
      (rd (q + (CI.indCaps + Caps.allLen))).toNat = some c.all ∧
    hslice? R (rd (q + (CI.indCaps + Caps.ctorsOff))).toNat
      (rd (q + (CI.indCaps + Caps.ctorsLen))).toNat = some c.ctors := by
  obtain ⟨-, -, hc⟩ := decCI_indInfo h
  obtain ⟨he, -⟩ := decCaps_eq_some.mp hc
  obtain ⟨w, hw, -⟩ := bool?_word he
  have hlt := hR.lt _ _ hw
  have e : (q + CI.indCaps).toNat = q.toNat + CI.indCaps.toNat := by
    rw [UInt64.toNat_add]; omega
  rw [← e] at hc
  simpa only [UInt64.add_assoc] using decCaps_rd hR hc

end L.Arena
