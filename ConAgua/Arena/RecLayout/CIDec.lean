module

public import ConAgua.Arena.RecLayout.CVDec
public import ConAgua.Arena.ErecRd
public import ConAgua.Arena.WhnfBase

@[expose] public section

/-!
# A constant record's words at L's addresses

The facts of `CVDec.lean` at L's word addresses `q + CV.f`, `p + CI.f` (`p + (CI.cv + CV.f)` for a
field of a record's constant value), for any reader `R` with its word read `rd` (`RdOK`: the
record pool and `erRd`, an array and `rdW`): the words a decoded constant value or constant record
was decoded from. Proofs use these instead of unfolding a decoder or an offset, so that a change of
the layout ends here.
-/

open ConRon.Arena

namespace L.Arena

variable {R : Nat → Option Word} {rd : Word → Word}

/-! ## One word -/

/-- A handle word. -/
theorem hd?_rd {k : IdxKind} (hR : RdOK R rd) {q f : Word} {x : Idx k}
    (h : hd? R (q.toNat + f.toNat) = some x) : x = decI (rd (q + f)) ∧ (rd (q + f)).toNat < 2 ^ 32 := by
  obtain ⟨w, hw, hlt, rfl⟩ := hd?_some h
  rw [hR.at f rfl hw]; exact ⟨rfl, hlt⟩

/-- A number word. -/
theorem nat?_rd (hR : RdOK R rd) {q f : Word} {n : Nat} (h : nat? R (q.toNat + f.toNat) = some n) :
    n = (rd (q + f)).toNat := by
  obtain ⟨w, hw, rfl⟩ := nat?_word h
  rw [hR.at f rfl hw]

/-- A flag word. -/
theorem bool?_rd (hR : RdOK R rd) {q f : Word} {b : Bool} (h : bool? R (q.toNat + f.toNat) = some b) :
    b = (rd (q + f) != 0) := by
  obtain ⟨w, hw, rfl⟩ := bool?_word h
  rw [hR.at f rfl hw]

/-- A slice's two words (the length word `g` right after the offset word `f`). -/
theorem hlist?_rd {k : IdxKind} (hR : RdOK R rd) {q f g : Word} (hg : g.toNat = f.toNat + 1)
    {l : List (Idx k)} (h : hlist? R (q.toNat + f.toNat) = some l) :
    hslice? R (rd (q + f)).toNat (rd (q + g)).toNat = some l := by
  obtain ⟨o, c, ho, hc, hs⟩ := hlist?_words h
  rw [hR.at f rfl ho, hR.at g (k := q.toNat + f.toNat + 1 - q.toNat) (by omega)
    (by rw [show q.toNat + (q.toNat + f.toNat + 1 - q.toNat) = q.toNat + f.toNat + 1 by omega]; exact hc)]
  exact hs

/-- A record's word read at `q + f` is at the address `q.toNat + f.toNat`. -/
theorem rd_off_toNat (hR : RdOK R rd) {q f : Word} {w : Word} (h : R (q.toNat + f.toNat) = some w) :
    (q + f).toNat = q.toNat + f.toNat :=
  off_add_toNat rfl (hR.lt _ _ h)

/-! ## A constant value -/

/-- **A decoded `IConstantVal` at L's word addresses** `q`, `q + CV.f`. -/
theorem decCV_rd (hR : RdOK R rd) {q : Word} {cv : IConstantVal} (h : decCV R q.toNat = some cv) :
    cv.name = decI (rd q) ∧ (rd q).toNat < 2 ^ 32 ∧
    hslice? R (rd (q + CV.lpsOff)).toNat (rd (q + CV.lpsLen)).toNat = some cv.levelParams ∧
    cv.levelParams.length = (rd (q + CV.lpsLen)).toNat ∧
    cv.type = decI (rd (q + CV.type)) ∧ (rd (q + CV.type)).toNat < 2 ^ 32 := by
  obtain ⟨hn, hl, ht⟩ := decCV_eq_some.mp h
  obtain ⟨w, hw, hlt, hnm⟩ := hd?_some hn
  have hs := hlist?_rd hR CV.lpsLen_toNat hl
  obtain ⟨e1, e2⟩ := hd?_rd hR ht
  refine ⟨by rw [hnm, hR.rd _ _ hw], by rw [hR.rd _ _ hw]; exact hlt, hs, ?_, e1, e2⟩
  simpa using hslice?_lenR hs

/-! ## A constant record -/

/-- The constant value of a decoded record at its word address `p + CI.cv`. -/
theorem decCI_cv_rd (hR : RdOK R rd) {p : Word} {x : IConstantInfo} (h : decCI R p.toNat = some x) :
    decCV R (p + CI.cv).toNat = some x.toConstantVal := by
  have hc := decCI_cv h
  obtain ⟨w, hw, -⟩ := decCV_name hc
  rw [rd_off_toNat hR hw]; exact hc

/-- **The constant value of a record at `p`**, at L's word addresses `p + (CI.cv + CV.f)`. -/
theorem decCV_rd_ci (hR : RdOK R rd) {p : Word} {cv : IConstantVal}
    (h : decCV R (p.toNat + CI.cv.toNat) = some cv) :
    HW (rd (p + (CI.cv + CV.name))) ∧ cv.name = decI (rd (p + (CI.cv + CV.name))) ∧
    hslice? R (rd (p + (CI.cv + CV.lpsOff))).toNat (rd (p + (CI.cv + CV.lpsLen))).toNat =
      some cv.levelParams ∧
    cv.levelParams.length = (rd (p + (CI.cv + CV.lpsLen))).toNat ∧
    HW (rd (p + (CI.cv + CV.type))) ∧ cv.type = decI (rd (p + (CI.cv + CV.type))) := by
  obtain ⟨w, hw, -⟩ := decCV_name h
  have e := rd_off_toNat hR hw
  rw [← e] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := decCV_rd hR h
  have a0 : p + CI.cv + 0 = p + CI.cv := by simp
  simp only [UInt64.add_assoc] at h1 h2 h3 h4 h5 h6
  have n0 : p + (CI.cv + CV.name) = p + CI.cv := by simp [CV.name]
  rw [n0]
  exact ⟨h2, h1, h3, h4, h6, h5⟩

/-- The kind word of a record decoded with kind `k`. -/
theorem rd_kind (hR : RdOK R rd) {p : Word} {k : Nat} (hk : nat? R p.toNat = some k) (hk64 : k < 2 ^ 64) :
    rd p = UInt64.ofNat k := by
  obtain ⟨w, hw, rfl⟩ := nat?_word hk
  rw [hR.rd _ _ hw]; simp

/-- **An `axiomInfo` record at L's addresses.** -/
theorem decCI_axiomInfo_rd (hR : RdOK R rd) {p : Word} {cv : IConstantVal}
    (h : decCI R p.toNat = some (.axiomInfo cv)) :
    rd p = 0 ∧ decCV R (p.toNat + CI.cv.toNat) = some cv := by
  obtain ⟨hk, hcv⟩ := decCI_axiomInfo_iff.mp h
  exact ⟨rd_kind hR hk (by decide), hcv⟩

/-- **A `thmInfo` record at L's addresses.** -/
theorem decCI_thmInfo_rd (hR : RdOK R rd) {p : Word} {cv : IConstantVal}
    (h : decCI R p.toNat = some (.thmInfo cv)) :
    rd p = 2 ∧ decCV R (p.toNat + CI.cv.toNat) = some cv := by
  obtain ⟨hk, hcv⟩ := decCI_thmInfo_iff.mp h
  exact ⟨rd_kind hR hk (by decide), hcv⟩

/-- **A `defnInfo` record at L's addresses.** -/
theorem decCI_defnInfo_rd (hR : RdOK R rd) {p : Word} {cv : IConstantVal} {v : EIdx}
    {hi : ConLeche.ReducibilityHint} (h : decCI R p.toNat = some (.defnInfo cv v hi)) :
    rd p = 1 ∧ decCV R (p.toNat + CI.cv.toNat) = some cv ∧
    v = decI (rd (p + CI.defnValue)) ∧ (rd (p + CI.defnValue)).toNat < 2 ^ 32 ∧
    decHint R (p.toNat + CI.defnHint.toNat) = some hi := by
  obtain ⟨hk, hcv, hv, hh⟩ := decCI_defnInfo_iff.mp h
  obtain ⟨e1, e2⟩ := hd?_rd hR hv
  exact ⟨rd_kind hR hk (by decide), hcv, e1, e2, hh⟩

/-- **An `indInfo` record at L's addresses** (its capabilities: `decCI_indInfo_rd`). -/
theorem decCI_indInfo_kind_rd (hR : RdOK R rd) {p : Word} {cv : IConstantVal} {c : IIndCaps}
    (h : decCI R p.toNat = some (.indInfo cv c)) :
    rd p = 3 ∧ decCV R (p.toNat + CI.cv.toNat) = some cv := by
  obtain ⟨hk, hcv, -⟩ := decCI_indInfo_iff.mp h
  exact ⟨rd_kind hR hk (by decide), hcv⟩

/-- **A `ctorInfo` record at L's addresses.** -/
theorem decCI_ctorInfo_rd (hR : RdOK R rd) {p : Word} {cv : IConstantVal} {np nf : Nat}
    {fam : NIdx} (h : decCI R p.toNat = some (.ctorInfo cv np nf fam)) :
    rd p = 4 ∧ decCV R (p.toNat + CI.cv.toNat) = some cv ∧
    np = (rd (p + CI.ctorNparams)).toNat ∧ nf = (rd (p + CI.ctorNfields)).toNat ∧
    fam = decI (rd (p + CI.ctorInduct)) ∧ (rd (p + CI.ctorInduct)).toNat < 2 ^ 32 := by
  obtain ⟨hk, hcv, ha, hb, hf⟩ := decCI_ctorInfo_iff.mp h
  obtain ⟨e1, e2⟩ := hd?_rd hR hf
  exact ⟨rd_kind hR hk (by decide), hcv, nat?_rd hR ha, nat?_rd hR hb, e1, e2⟩

/-- **A `recInfo` record at L's addresses.** -/
theorem decCI_recInfo_rd (hR : RdOK R rd) {p : Word} {cv : IConstantVal} {mi rp : Nat}
    {k : Bool} {rules : List IRecRule} (h : decCI R p.toNat = some (.recInfo cv mi rp k rules)) :
    rd p = 5 ∧ decCV R (p.toNat + CI.cv.toNat) = some cv ∧
    mi = (rd (p + CI.recMajor)).toNat ∧ rp = (rd (p + CI.recPrefix)).toNat ∧
    k = (rd (p + CI.recIsK) != 0) ∧
    decRules R (rd (p + CI.recRulesOff)).toNat (rd (p + CI.recRulesLen)).toNat = some rules := by
  obtain ⟨hk, hcv, ha, hb, hkk, o, c, ho, hc, hr⟩ := decCI_recInfo_iff.mp h
  refine ⟨rd_kind hR hk (by decide), hcv, nat?_rd hR ha, nat?_rd hR hb, bool?_rd hR hkk, ?_⟩
  rw [← nat?_rd hR ho, ← nat?_rd hR hc]; exact hr

/-- **A record by its kind word** (`1` definition, `3` inductive, `4` constructor): what it
decodes to, and that no other kind's word decodes to it. -/
theorem decCI_split (hR : RdOK R rd) {q : Word} {ci : IConstantInfo}
    (h : decCI R q.toNat = some ci) :
    (rd q = 1 → ∃ cv v hint, ci = .defnInfo cv v hint ∧
      decCV R (q.toNat + CI.cv.toNat) = some cv ∧
      v = decI (rd (q + CI.defnValue)) ∧ (rd (q + CI.defnValue)).toNat < 2 ^ 32) ∧
    (rd q ≠ 1 → ∀ cv v hint, ci ≠ .defnInfo cv v hint) ∧
    (rd q = 3 → ∃ cv caps, ci = .indInfo cv caps ∧ decCV R (q.toNat + CI.cv.toNat) = some cv) ∧
    (rd q ≠ 3 → ∀ cv caps, ci ≠ .indInfo cv caps) ∧
    (rd q = 4 → ∃ cv np nf fam, ci = .ctorInfo cv np nf fam ∧
      decCV R (q.toNat + CI.cv.toNat) = some cv) ∧
    (rd q ≠ 4 → ∀ cv np nf fam, ci ≠ .ctorInfo cv np nf fam) := by
  obtain ⟨wk, e, hx⟩ := decCI_cases h
  rw [hR.rd _ _ e]
  have eq : ∀ {n : Nat}, wk.toNat = n → n < 2 ^ 64 → wk = UInt64.ofNat n := fun hn hl =>
    UInt64.toNat_inj.mp (by simp; omega)
  rcases hx with ⟨hk, cv, hcv, rfl⟩ | ⟨hk, cv, v, hi, hcv, hv, -, rfl⟩ | ⟨hk, cv, hcv, rfl⟩ |
      ⟨hk, cv, caps, hcv, -, rfl⟩ | ⟨hk, cv, np, nf, fam, hcv, -, -, -, rfl⟩ |
      ⟨hk, cv, mi, rp, o, c, k, rules, hcv, -, -, -, -, -, -, rfl⟩
  all_goals
    obtain rfl := eq hk (by decide)
    refine ⟨fun h1 => ?_, fun h1 => ?_, fun h3 => ?_, fun h3 => ?_, fun h4 => ?_, fun h4 => ?_⟩
    all_goals first
      | (exfalso; revert h1; decide) | (exfalso; revert h3; decide) | (exfalso; revert h4; decide)
      | (intros; simp; done)
      | exact ⟨cv, _, _, rfl, hcv, (hd?_rd hR hv).1, (hd?_rd hR hv).2⟩
      | exact ⟨cv, _, rfl, hcv⟩
      | exact ⟨cv, _, _, _, rfl, hcv⟩

/-- `decCI_split` at the record pool and L's tagged read. -/
theorem decCI_splitE {m : Mem} {q : Word} {ci : IConstantInfo} (h : decCI (erecP m) q.toNat = some ci) :
    (erRd m q = 1 → ∃ cv v hint, ci = .defnInfo cv v hint ∧
      decCV (erecP m) (q.toNat + CI.cv.toNat) = some cv ∧
      v = decI (erRd m (q + CI.defnValue)) ∧ (erRd m (q + CI.defnValue)).toNat < 2 ^ 32) ∧
    (erRd m q ≠ 1 → ∀ cv v hint, ci ≠ .defnInfo cv v hint) ∧
    (erRd m q = 3 → ∃ cv caps, ci = .indInfo cv caps ∧
      decCV (erecP m) (q.toNat + CI.cv.toNat) = some cv) ∧
    (erRd m q ≠ 3 → ∀ cv caps, ci ≠ .indInfo cv caps) ∧
    (erRd m q = 4 → ∃ cv np nf fam, ci = .ctorInfo cv np nf fam ∧
      decCV (erecP m) (q.toNat + CI.cv.toNat) = some cv) ∧
    (erRd m q ≠ 4 → ∀ cv np nf fam, ci ≠ .ctorInfo cv np nf fam) :=
  decCI_split (erRdOK m) h

/-- **A recursor record by its kind word `5`** (and no other kind's word decodes to one). -/
theorem decCI_rec_rd (hR : RdOK R rd) {q : Word} {ci : IConstantInfo}
    (h : decCI R q.toNat = some ci) :
    (rd q = 5 → ∃ cv rules, ci = .recInfo cv (rd (q + CI.recMajor)).toNat
      (rd (q + CI.recPrefix)).toNat (rd (q + CI.recIsK) != 0) rules ∧
      decCV R (q.toNat + CI.cv.toNat) = some cv ∧
      decRules R (rd (q + CI.recRulesOff)).toNat (rd (q + CI.recRulesLen)).toNat = some rules) ∧
    (rd q ≠ 5 → ∀ cv mI rP isK rules, ci ≠ .recInfo cv mI rP isK rules) := by
  obtain ⟨wk, e, hx⟩ := decCI_cases h
  have hrd : rd q = wk := hR.rd _ _ e
  rw [hrd]
  constructor
  · intro h5
    subst h5
    rcases hx with ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ |
      ⟨-, cv, mi, rp, o, c, k, rules, hcv, ha, hb, ho, hc, hkk, hr, rfl⟩
    all_goals first | (exfalso; simp at hk) | skip
    refine ⟨cv, rules, ?_, hcv, ?_⟩
    · rw [← nat?_rd hR ha, ← nat?_rd hR hb, ← bool?_rd hR hkk]
    · rw [← nat?_rd hR ho, ← nat?_rd hR hc]; exact hr
  · intro hw cv mI rP isK rules hc
    subst hc
    rcases hx with ⟨-, -, -, ⟨⟩⟩ | ⟨-, -, -, -, -, -, -, ⟨⟩⟩ | ⟨-, -, -, ⟨⟩⟩ | ⟨-, -, -, -, -, ⟨⟩⟩ |
      ⟨-, -, -, -, -, -, -, -, -, ⟨⟩⟩ | ⟨hk, -⟩
    exact hw (UInt64.toNat_inj.mp (by rw [hk]; rfl))

/-- **A constructor record by its kind word `4`** (and no other kind's word decodes to one). -/
theorem decCI_ctorR (hR : RdOK R rd) {q : Word} {ci : IConstantInfo}
    (h : decCI R q.toNat = some ci) :
    (rd q = 4 → ∃ cv, ci = .ctorInfo cv (rd (q + CI.ctorNparams)).toNat
      (rd (q + CI.ctorNfields)).toNat (decI (rd (q + CI.ctorInduct))) ∧
      (rd (q + CI.ctorInduct)).toNat < 2 ^ 32) ∧
    (rd q ≠ 4 → ∀ cv np nf fam, ci ≠ .ctorInfo cv np nf fam) := by
  obtain ⟨wk, e, hx⟩ := decCI_cases h
  have hrd : rd q = wk := hR.rd _ _ e
  rw [hrd]
  constructor
  · intro h4
    subst h4
    rcases hx with ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ |
      ⟨-, cv, np, nf, fam, -, ha, hb, hf, rfl⟩ | ⟨hk, -⟩
    all_goals first | (exfalso; simp at hk) | skip
    obtain ⟨e1, e2⟩ := hd?_rd hR hf
    refine ⟨cv, ?_, e2⟩
    rw [← nat?_rd hR ha, ← nat?_rd hR hb, ← e1]
  · intro hw cv np nf fam hc
    subst hc
    rcases hx with ⟨-, -, -, ⟨⟩⟩ | ⟨-, -, -, -, -, -, -, ⟨⟩⟩ | ⟨-, -, -, ⟨⟩⟩ | ⟨-, -, -, -, -, ⟨⟩⟩ |
      ⟨hk, -⟩ | ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨⟩⟩
    exact hw (UInt64.toNat_inj.mp (by rw [hk]; rfl))

/-! ## A constant value's words, written field by field -/

/-- **An `IConstantVal` record's words** at `q` of a reader: each field's word (a writer's
postcondition; `decCV_of_words` decodes it). -/
structure CVRecW (a : Nat → Option Word) (q : Nat) (nm lo ll ty : Word) : Prop where
  name : a (q + CV.name.toNat) = some nm
  lo : a (q + CV.lpsOff.toNat) = some lo
  ll : a (q + CV.lpsLen.toNat) = some ll
  ty : a (q + CV.type.toNat) = some ty

/-- The record's words carried to another reader that holds the same `CV.size` words. -/
theorem CVRecW.shift {a b : Nat → Option Word} {q e : Nat} {nm lo ll ty : Word}
    (h : CVRecW a q nm lo ll ty) (hw : ∀ j < CV.size.toNat, b (e + j) = a (q + j)) :
    CVRecW b e nm lo ll ty :=
  ⟨(hw _ CV.name_lt).trans h.name, (hw _ CV.lpsOff_lt).trans h.lo,
    (hw _ CV.lpsLen_lt).trans h.ll, (hw _ CV.type_lt).trans h.ty⟩

/-- **A constant value's words decode** (the level-parameter slice and the two handles given). -/
theorem decCV_of_words {a : Nat → Option Word} {q : Nat} {nm lo ll ty : Word}
    {lps : List NIdx} (h : CVRecW a q nm lo ll ty) (hnm : nm.toNat < 2 ^ 32)
    (hty : ty.toNat < 2 ^ 32) (hs : hslice? a lo.toNat ll.toNat = some lps) :
    decCV a q = some ⟨decI nm, lps, decI ty⟩ := by
  have hn := h.name
  rw [CV.name_toNat, Nat.add_zero] at hn
  refine decCV_of (by simp [hd?, hn, hnm]) ?_ (by simp [hd?, h.ty, hty])
  have hl := h.ll
  rw [CV.lpsLen_toNat, ← Nat.add_assoc] at hl
  simp only [hlist?, nat?, h.lo, hl, Option.map_some, Option.bind_eq_bind, Option.bind_some, hs]

set_option linter.deprecated false in
/-- **A constant value written field by field** (four word stores into array `A` at
`q + CV.f`, in the fields' order) holds its words. -/
theorem cvRecW_set64 {m : Mem} {A : TieredArray} {q nm lo ll ty : Word}
    (hb : q.toNat + CV.size.toNat ≤ (m.arr64 A).size) (h64 : q.toNat + CV.size.toNat < 2 ^ 64) :
    CVRecW (aread (((((m.set64 A (q + CV.name) nm).set64 A (q + CV.lpsOff) lo).set64 A
      (q + CV.lpsLen) ll).set64 A (q + CV.type) ty).arr64 A)) q.toNat nm lo ll ty := by
  obtain ⟨o1, o2, o3, o4⟩ := CV.order
  have e : ∀ f : Word, f.toNat < CV.size.toNat → (q + f).toNat = q.toNat + f.toNat := fun f hf => by
    rw [UInt64.toNat_add]; omega
  simp only [Mem.arr64_set64_same, e _ CV.name_lt, e _ CV.lpsOff_lt, e _ CV.lpsLen_lt,
    e _ CV.type_lt]
  constructor <;> simp (disch := omega) only [aread_apply, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds, Array.size_setIfInBounds, if_pos, if_neg, ite_true]

end L.Arena
