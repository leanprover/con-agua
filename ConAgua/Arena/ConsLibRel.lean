import ConAgua.Arena.ConsLibSpec
import ConAgua.Arena.ViewL
import ConAgua.Arena.Frame

/-!
# The cons-table library: the relation and the user API (lane conslib)

A cons table `C` (`ConsLib.lean`) represents the arena's two `Tbl`s of one constructor (the twin's
`HashMap2`s: persistent and scratch) by **`ConsR C R m on P Q`**: both tiers hold the same nodes
in the same order (node `i` of tier `t` related to `nodes[i]` by the instance's record relation
`R`), the same key → handle map, the node counts at `CTL[ca + t]`, the scratch flag `CTL[1]` is
`on`; and the slots index the nodes (the slot layout, the probing and the growth state, which no
user sees). The L model of every `intern_X` is `consInternM C m ks` (`ConsLibSpec.lean`).

Both are irreducible outside this file: the lemmas below are the whole interface.

* **Reading the relation**: `ConsR.flag`, `ConsR.ctl`, `ConsR.cnt`, `ConsR.cap`, `ConsR.rec`,
  `ConsR.cons`, `ConsR.back`, `ConsR.recSize`, `ConsR.node`, `ConsR.cons_hit`.
* **Keeping it**: `ConsR.frame` (a writer apart from the table), `ConsR.setFlag` (`CTL[1]`),
  `ConsR.reset` (the scratch reset), `consR_init` (the all-zero memory), `ConsR.congr`.
* **An interning**: `consIntern_correct` (it refines the arena's hash-consing, from the
  instance's obligations `ConsKeyOK`), `consInternM_frame` (what it writes), `consInternM_word`,
  `consInternM_lt`, `consInternM_pw` (the handle word), `consInternM_out` (a hit, or the append
  of node `cntC`: the memory outside the slot array is `pushRec`).

An instance supplies `C.WF` (the schema's shape, the handle bases, the column, the push's room
and record length), `RFrame C.sch R C.hsM` (a node's relation and hash depend on its own words),
`ColFree C R` (the column does not matter to `R`) and, per query, `ConsKeyOK`.
-/

open ConRon.Arena

set_option linter.unusedSimpArgs false

namespace L.Arena

/-! ## A store relation across a writer apart from it (`Frame.lean`'s `Apart`) -/

section frame
variable {α δ : Type} {k : IdxKind} [BEq α] [Hashable α]
variable (S : Schema) (R : Mem → Word → Word → α → Prop) (hs : Mem → Word → Word → Word)

/-- **A table's relation survives a writer it is apart from.** -/
theorem storeR_frame (hS : S.WF) (A₀ : List ArrId) (C₀ : List Word) (hl : RLocal S R hs A₀ C₀)
    (A : List ArrId) (C : List Word) (hap : Apart S A₀ C₀ A C) (m m' : Mem) (hf : MemFrame A C m m') (on : Bool)
    (tbP tbS : Tbl α (Idx k) δ) (hR : StoreR S R hs m on tbP tbS) :
    StoreR S R hs m' on tbP tbS := by
  obtain ⟨hra, hsa, hA₀, hc0, hc1, h1, hscb, h0⟩ := hap
  obtain ⟨hfa, hfc, hfs, -⟩ := hf
  obtain ⟨⟨hctl, hb⟩, hfl, hT0, hT1, hG⟩ := hR
  have eb : ∀ t, baseW m' t = baseW m t := fun t => by simp only [baseW, hfc SCB hscb]
  have era := hfa S.ra hra hS.ra_ctl
  have esa := hfa S.sa hsa hS.sa_ctl
  have hloc := hl m m' era (fun b hb => hfa b (hA₀ b hb).1 (hA₀ b hb).2) (fun x hx => hfc x (h0 x hx))
  have ec : ∀ t : Word, t ≤ 1 → cntW S m' t = cntW S m t := by
    intro t ht
    simp only [cntW]
    apply hfc
    rcases word_le_one t ht with rfl | rfl
    · simpa using hc0
    · exact hc1
  refine ⟨⟨by rw [hfs]; exact hctl, by rw [hfc SCB hscb]; exact hb⟩, by rw [hfc 1 h1]; exact hfl, ?_, ?_, ?_⟩
  · exact tierR_mono S R hs m m' 0 tbP era esa (ec 0 (by decide)) (eb 0) (hloc.1 0) (hloc.2 0) hT0
  · exact tierR_mono S R hs m m' 1 tbS era esa (ec 1 (by decide)) (eb 1) (hloc.1 1) (hloc.2 1) hT1
  · exact growR_of_sa S m m' esa hG

end frame

/-! ## The schema as a store schema -/

/-- The store schema of a cons table (`StoreLib.lean`). -/
def ConsSch.sch (C : ConsSch) : Schema := ⟨C.ra, C.sa, C.w, C.st, C.ca, C.tag⟩

/-- The slot arrays' minimum length (`CapCheck.lean`, `consR_init`). -/
def consMinWords : Nat := 17

/-- **What the generic lemmas need of a cons table.** -/
structure ConsSch.WF (C : ConsSch) : Prop where
  sch : C.sch.WF
  P : C.P = hdW C.tag.toUInt64 0 0
  S : C.S = hdW C.tag.toUInt64 1 0
  col : ∀ A, C.col = some A → A ≠ C.ra ∧ A ≠ C.sa ∧ A ≠ CTL ∧
    ∀ (m : Mem) (k x t i : Word), C.hsM (m.set64 A k x) t i = C.hsM m t i
  room : ∀ (m : Mem) (t : Word), pushOKC C m t = true →
    C.st.toNat * ((cntC C m t).toNat + 1) ≤ (m.arr64 C.ra).size
  colRoom : ∀ A, C.col = some A → ∀ (m : Mem) (t : Word), t ≤ 1 → pushOKC C m t = true →
    (cntC C m t * 2 + t).toNat < (m.arr64 A).size
  vs : ∀ (ks : List Word) (h : Word), ks.length = C.nk →
    (C.vsM (pushArgs C ks h)).length = C.w.toNat

/-- The record relation `R` does not read the table's column. -/
def ColFree {α : Type} (C : ConsSch) (R : Mem → Word → Word → α → Prop) : Prop :=
  ∀ A, C.col = some A → ∀ (m : Mem) (k x t i : Word) (a : α), R m t i a → R (m.set64 A k x) t i a

theorem colFree_none {α : Type} {C : ConsSch} (R : Mem → Word → Word → α → Prop)
    (h : C.col = none) : ColFree C R := fun A hA => by rw [h] at hA; cases hA

section shape
variable {C : ConsSch} (hW : C.WF)
include hW

theorem ConsSch.WF.tag16 : C.tag.toUInt64.toNat < 16 := by
  have := hW.sch.tag; simpa [ConsSch.sch] using this

theorem ConsSch.WF.base (t : Word) (ht : t ≤ 1) (i : Word) :
    (if t = 0 then C.P else C.S) + i = hdW C.tag.toUInt64 t i := by
  rcases word_le_one t ht with rfl | rfl
  · simp only [↓reduceIte, hW.P, hdW]; grind
  · simp only [show (1 : Word) ≠ 0 by decide, ↓reduceIte, hW.S, hdW]; grind

theorem ConsSch.WF.base0 (i : Word) : C.P + i = hdW C.tag.toUInt64 0 i := by
  simpa using hW.base 0 (by decide) i

theorem ConsSch.WF.base1 (i : Word) : C.S + i = hdW C.tag.toUInt64 1 i := by
  simpa using hW.base 1 (by decide) i

theorem ConsSch.WF.room' (m : Mem) (t : Word) (h : pushOKC C m t = true) : PushRoom C.sch m t := by
  have h1 := hW.room m t h
  simp only [pushOKC, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨by have := h.1; simp only [cntC] at this; exact this, h1⟩

end shape

theorem hdW_toNat (g t i : Word) (hg : g.toNat < 16) (ht : t ≤ 1) (hi : i.toNat < 2 ^ 27) :
    (hdW g t i).toNat = g.toNat * 268435456 + t.toNat * 134217728 + i.toNat := by
  have ht' : t.toNat ≤ 1 := ht
  simp only [hdW, UInt64.toNat_add, UInt64.toNat_mul]
  have h1 : (0x10000000 : Word).toNat = 268435456 := rfl
  have h2 : (0x8000000 : Word).toNat = 134217728 := rfl
  rw [h1, h2]
  omega

/-! ## The relation -/

section rel
variable {α δ : Type} {k : IdxKind} [BEq α] [Hashable α]

/-- **A cons table represents the arena's two tables** `P` (persistent) and `Q` (scratch). -/
def ConsR (C : ConsSch) (R : Mem → Word → Word → α → Prop) (m : Mem) (on : Bool)
    (P Q : Tbl α (Idx k) δ) : Prop :=
  StoreR C.sch R C.hsM m on P Q

theorem consR_iff {C : ConsSch} {R : Mem → Word → Word → α → Prop} {m : Mem} {on : Bool}
    {P Q : Tbl α (Idx k) δ} : ConsR C R m on P Q ↔ StoreR C.sch R C.hsM m on P Q := Iff.rfl

variable {C : ConsSch} {R : Mem → Word → Word → α → Prop} {m : Mem} {on : Bool}
  {P Q : Tbl α (Idx k) δ}

/-- Two schemas with the same arrays, counts, tag and hash have the same relation. -/
theorem ConsR.congr {C' : ConsSch} (hs : C.sch = C'.sch) (hh : C.hsM = C'.hsM) :
    ConsR C R m on P Q ↔ ConsR C' R m on P Q := by
  simp only [consR_iff, hs, hh]

theorem ConsR.tier (h : ConsR C R m on P Q) (t : Word) (ht : t ≤ 1) :
    TierR C.sch R C.hsM m t (if t = 0 then P else Q) := by
  rcases word_le_one t ht with rfl | rfl
  · simpa using h.2.2.1
  · simpa using h.2.2.2.1

/-- The scratch flag `CTL[1]`. -/
theorem ConsR.flag (h : ConsR C R m on P Q) : (rdW (m.arr64 CTL) 1 != 0) = on := h.2.1

/-- The count words fit in `CTL`. -/
theorem ConsR.ctl (h : ConsR C R m on P Q) : C.ca.toNat + 2 ≤ (m.arr64 CTL).size := h.1.1

/-- **The count of tier `t` is its table's node count.** -/
theorem ConsR.cnt (h : ConsR C R m on P Q) (t : Word) (ht : t ≤ 1) :
    (cntC C m t).toNat = (if t = 0 then P else Q).nodes.size := (h.tier t ht).1

theorem ConsR.cntP (h : ConsR C R m on P Q) : (cntC C m 0).toNat = P.nodes.size := by
  simpa using h.cnt 0 (by decide)

theorem ConsR.cntS (h : ConsR C R m on P Q) : (cntC C m 1).toNat = Q.nodes.size := by
  simpa using h.cnt 1 (by decide)

theorem ConsR.cap (h : ConsR C R m on P Q) (t : Word) (ht : t ≤ 1) :
    (if t = 0 then P else Q).nodes.size ≤ 134217728 := (h.tier t ht).2.1

theorem ConsR.recSize (h : ConsR C R m on P Q) (t : Word) (ht : t ≤ 1) :
    C.st.toNat * (if t = 0 then P else Q).nodes.size ≤ (m.arr64 C.ra).size := (h.tier t ht).2.2.1

/-- Node `i` of tier `t` holds the table's node `i`. -/
theorem ConsR.rec (h : ConsR C R m on P Q) (t : Word) (ht : t ≤ 1) (i : Word) (a : α)
    (hi : (if t = 0 then P else Q).nodes[i.toNat]? = some a) : R m t i a :=
  (h.tier t ht).2.2.2.1 i a hi

/-- The table maps node `i`'s key to its handle. -/
theorem ConsR.cons (h : ConsR C R m on P Q) (t : Word) (ht : t ≤ 1) (i : Word) (a : α)
    (hi : (if t = 0 then P else Q).nodes[i.toNat]? = some a) :
    (if t = 0 then P else Q).cons[a]? = some (decI (hdW C.tag.toUInt64 t i)) :=
  (h.tier t ht).2.2.2.2.1 i a hi

/-- Every entry of the table's map points at a node with its key. -/
theorem ConsR.back (h : ConsR C R m on P Q) (t : Word) (ht : t ≤ 1) (a : α) (x : Idx k)
    (hc : (if t = 0 then P else Q).cons[a]? = some x) :
    (if t = 0 then P else Q).nodes[(hix x).toNat]? = some a :=
  (h.tier t ht).2.2.2.2.2.1 a x hc

/-- A node below the count is a node of the table. -/
theorem ConsR.node (h : ConsR C R m on P Q) (t : Word) (ht : t ≤ 1) (i : Word)
    (hi : i < cntC C m t) :
    ∃ x, (if t = 0 then P else Q).nodes[i.toNat]? = some x ∧ R m t i x := by
  have hlt : i.toNat < (if t = 0 then P else Q).nodes.size := by
    rw [← h.cnt t ht]; exact hi
  exact ⟨_, Array.getElem?_eq_getElem hlt, h.rec t ht _ _ (Array.getElem?_eq_getElem hlt)⟩

/-- **A cons hit of a tier names a node of that tier** with the probed record, and the handle
carries the schema's tag and the tier's bit. -/
theorem ConsR.cons_hit (hW : C.WF) (h : ConsR C R m on P Q) (t : Word) (ht : t ≤ 1) {a : α}
    {x : Idx k} (hc : (if t = 0 then P else Q).cons[a]? = some x) :
    (if t = 0 then P else Q).nodes[x.idxNat]? = some a ∧ x.tag = C.tag ∧
      x.isPersistent = (t == 0) := by
  have hg : C.tag.toNat < 16 := by have := hW.sch.tag; simpa [ConsSch.sch] using this
  have h6 := h.back t ht a x hc
  have hix_nat : (hix x).toNat = x.idxNat := by
    simp only [hix]
    have : x.idxNat < 2 ^ 27 := by
      simp only [Idx.idxNat, Idx.index]; have := UInt32.toNat_mod x.word 134217728
      simp at this ⊢; omega
    simp; omega
  rw [hix_nat] at h6
  refine ⟨h6, ?_⟩
  have h5 := h.cons t ht (hix x) a (by rw [hix_nat]; exact h6)
  rw [hc] at h5
  have hx := Option.some.inj h5
  have hi : x.idxNat < 2 ^ 27 := by
    simp only [Idx.idxNat, Idx.index]; simp; omega
  have ht' : t.toNat ≤ 1 := by rw [UInt64.le_iff_toNat_le] at ht; simpa using ht
  have hw : x.word.toNat = C.tag.toNat * 268435456 + t.toNat * 134217728 + x.idxNat := by
    have := congrArg Idx.word hx
    rw [this]
    simp only [decI, hdW, hix]
    simp [UInt64.toNat_toUInt32]
    omega
  constructor
  · apply UInt32.toNat_inj.mp
    simp only [Idx.tag, UInt32.toNat_div]; simp; omega
  · simp only [Idx.isPersistent, Idx.tier]
    have e1 : (x.word / 134217728 % 2 = 0) ↔ (t = 0) := by
      rw [← UInt32.toNat_inj, ← UInt64.toNat_inj]
      simp only [UInt32.toNat_mod, UInt32.toNat_div]; simp; omega
    rw [Bool.eq_iff_iff]; simp only [beq_iff_eq]; exact e1

theorem ConsR.cons_hitP (hW : C.WF) (h : ConsR C R m on P Q) {a : α} {x : Idx k}
    (hc : P.cons[a]? = some x) : P.nodes[x.idxNat]? = some a ∧ x.tag = C.tag ∧ x.isPersistent = true := by
  have := h.cons_hit hW 0 (by decide) (a := a) (x := x) (by simpa using hc)
  simpa using this

theorem ConsR.cons_hitS (hW : C.WF) (h : ConsR C R m on P Q) {a : α} {x : Idx k}
    (hc : Q.cons[a]? = some x) : Q.nodes[x.idxNat]? = some a ∧ x.tag = C.tag ∧ x.isPersistent = false := by
  have := h.cons_hit hW 1 (by decide) (a := a) (x := x) (by simpa using hc)
  simpa using this

/-- Both tiers' counts: the sizes, at most `2^27`. -/
theorem ConsR.sizes (h : ConsR C R m on P Q) :
    (rdW (m.arr64 CTL) (C.ca + 0)).toNat = P.size ∧ P.size ≤ 134217728 ∧
      (rdW (m.arr64 CTL) (C.ca + 1)).toNat = Q.size ∧ Q.size ≤ 134217728 := by
  have c0 := h.cnt 0 (by decide); have c1 := h.cnt 1 (by decide)
  have k0 := h.cap 0 (by decide); have k1 := h.cap 1 (by decide)
  simp only [ite_true, show (1 : Word) ≠ 0 by decide, ite_false, cntC] at c0 c1 k0 k1
  exact ⟨c0, k0, c1, k1⟩

/-! ## Keeping the relation -/

/-- **The relation survives any change that keeps the table's arrays, its `CTL` words (counts,
flag, scratch epoch) and every node's relation and hash** (e.g. the pool growing under `lit`). -/
theorem ConsR.mono {m' : Mem} (h : ConsR C R m on P Q) (hra : m'.arr64 C.ra = m.arr64 C.ra)
    (hsa : m'.arr64 C.sa = m.arr64 C.sa) (hsz : (m'.arr64 CTL).size = (m.arr64 CTL).size)
    (hc : ∀ x, x = 1 ∨ x = SCB ∨ x = C.ca ∨ x = C.ca + 1 → rdW (m'.arr64 CTL) x = rdW (m.arr64 CTL) x)
    (hR : ∀ t i a, R m t i a → R m' t i a) (hh : ∀ t i, C.hsM m' t i = C.hsM m t i) :
    ConsR C R m' on P Q := by
  obtain ⟨⟨h1, h2⟩, hfl, hT0, hT1, hG⟩ := h
  have tier : ∀ t (tb : Tbl α (Idx k) δ), t ≤ 1 → TierR C.sch R C.hsM m t tb →
      TierR C.sch R C.hsM m' t tb := fun t tb ht hT =>
    tierR_mono C.sch R C.hsM m m' t tb hra hsa
      (by simp only [cntW]; rcases word_le_one t ht with rfl | rfl
          · exact hc _ (.inr (.inr (.inl (by simp [ConsSch.sch]))))
          · exact hc _ (.inr (.inr (.inr rfl))))
      (by simp only [baseW, hc SCB (.inr (.inl rfl))]) (hR t) (hh t) hT
  exact ⟨⟨by rw [hsz]; exact h1, by rw [hc SCB (.inr (.inl rfl))]; exact h2⟩,
    by rw [hc 1 (.inl rfl)]; exact hfl, tier 0 P (by decide) hT0, tier 1 Q (by decide) hT1,
    growR_of_sa C.sch m m' hsa hG⟩

/-- **A table's relation survives a writer it is apart from** (`Frame.lean`'s `Apart`, `RLocal`). -/
theorem ConsR.frame (hW : C.WF) {A₀ : List ArrId} {C₀ : List Word}
    (hl : RLocal C.sch R C.hsM A₀ C₀) {A : List ArrId} {Cw : List Word}
    (hap : Apart C.sch A₀ C₀ A Cw) {m' : Mem} (hf : MemFrame A Cw m m')
    (h : ConsR C R m on P Q) : ConsR C R m' on P Q :=
  storeR_frame C.sch R C.hsM hW.sch A₀ C₀ hl A Cw hap m m' hf on P Q h

/-- **Writing the scratch flag `CTL[1]`.** -/
theorem ConsR.setFlag (hW : C.WF) (hfr : RFrame C.sch R C.hsM) (h : ConsR C R m on P Q)
    (w : Word) : ConsR C R (m.set64 CTL 1 w) (w != 0) P Q := by
  have hS := hW.sch
  obtain ⟨⟨hsz, hscb⟩, _, hP, hQ, hG⟩ := h
  have hsz' : ((m.set64 CTL 1 w).arr64 CTL).size = (m.arr64 CTL).size := size_set64 _ _ _ _ _
  have h1 : (1 : Word).toNat < (m.arr64 CTL).size := by
    have := hS.ca.1; simp; omega
  have hrd : ∀ x, x ≠ 1 → rdW ((m.set64 CTL 1 w).arr64 CTL) x = rdW (m.arr64 CTL) x := by
    intro x hx; rw [rdW_set64]; simp [Ne.symm hx]
  have hra : (m.set64 CTL 1 w).arr64 C.sch.ra = m.arr64 C.sch.ra :=
    Mem.arr64_set64_ne _ _ _ _ _ hS.ra_ctl
  have hsa : (m.set64 CTL 1 w).arr64 C.sch.sa = m.arr64 C.sch.sa :=
    Mem.arr64_set64_ne _ _ _ _ _ hS.sa_ctl
  have hout : OutEq C.sch m (m.set64 CTL 1 w) :=
    ⟨fun b _ _ hb => Mem.arr64_set64_ne _ _ _ _ _ hb, hrd 0 (by decide)⟩
  have hfld : ∀ t i f, f < C.sch.w → fld C.sch (m.set64 CTL 1 w) t i f = fld C.sch m t i f := by
    intro t i f _; simp only [fld, hra]
  have hscb' : SCB ≠ (1 : Word) := by decide
  have tier : ∀ (t : Word) (tb : Tbl α (Idx k) δ), t ≤ 1 → TierR C.sch R C.hsM m t tb →
      TierR C.sch R C.hsM (m.set64 CTL 1 w) t tb := by
    intro t tb ht hT
    refine tierR_mono C.sch R C.hsM m _ t tb hra hsa ?_ ?_
      (fun i a hr => ((hfr _ _ t i hout (hfld t i)).1 a hr)) (fun i => (hfr _ _ t i hout (hfld t i)).2) hT
    · simp only [cntW]
      apply hrd
      rcases word_le_one t ht with rfl | rfl
      · simpa using hS.scb.2.2.1
      · simpa using hS.scb.2.2.2
    · simp only [baseW, hrd SCB hscb']
  refine ⟨⟨by rw [hsz']; exact hsz, by rw [hrd SCB hscb']; exact hscb⟩, ?_,
    tier 0 P (by decide) hP, tier 1 Q (by decide) hQ, growR_of_sa C.sch m _ hsa hG⟩
  have h1' : 1 < (m.arr64 CTL).size := by simpa using h1
  rw [rdW_set64]; simp [h1']

/-- **The scratch reset** (`scratch_reset`): the arrays, the pool top and tier 0's count stay, the
scratch epoch `CTL[62]` rises by `2^32` (from below `2^62`), tier 1's count becomes `0`, the flag
becomes `on'`: tier 0 as before, tier 1 empty. -/
theorem ConsR.reset (hW : C.WF) (hfr : RFrame C.sch R C.hsM) (h : ConsR C R m on P Q) {m' : Mem}
    {on' : Bool} (harr : ∀ b, b ≠ CTL → m'.arr64 b = m.arr64 b)
    (hsz : (m'.arr64 CTL).size = (m.arr64 CTL).size)
    (h0 : rdW (m'.arr64 CTL) 0 = rdW (m.arr64 CTL) 0)
    (hc0 : cntC C m' 0 = cntC C m 0) (hc1 : cntC C m' 1 = 0)
    (hlo : (rdW (m.arr64 CTL) SCB).toNat < 2 ^ 62)
    (hb : rdW (m'.arr64 CTL) SCB = rdW (m.arr64 CTL) SCB + 4294967296)
    (hfl : (rdW (m'.arr64 CTL) 1 != 0) = on') :
    ConsR C R m' on' P (Tbl.empty : Tbl α (Idx k) δ) :=
  storeR_reset C.sch R C.hsM hW.sch hfr m m' on on' P Q h harr hsz h0 hc0 hc1 hlo hb hfl

/-- **The relation holds initially**: the all-zero memory, both tables empty. -/
theorem consR_init (hz : ∀ b x, rdW (m.arr64 b) x = 0) (hctl : C.ca.toNat + 2 ≤ (m.arr64 CTL).size)
    (hsa : consMinWords ≤ (m.arr64 C.sa).size ∧ (m.arr64 C.sa).size < 2 ^ 63) :
    ConsR C R m false (Tbl.empty : Tbl α (Idx k) δ) Tbl.empty := by
  have hT : ∀ t, TierR C.sch R C.hsM m t (Tbl.empty : Tbl α (Idx k) δ) := by
    intro t
    refine ⟨by simp [cntW, hz, Tbl.empty], by simp [Tbl.empty], by simp [Tbl.empty],
      fun i a h => by simp [Tbl.empty] at h, fun i a h => by simp [Tbl.empty] at h,
      fun a x h => by simp [Tbl.empty] at h, fun j _ => by simp [slotW, slotV, slotRd, hz],
      fun i hi => by simp [Tbl.empty] at hi⟩
  have hG : GrowR C.sch m := by
    have hg : gexpW C.sch.sa m = 0 := hz _ _
    have hn : (nSl C.sch m).toNat = 8 := by simp only [nSl, gnW, hg]; decide
    have := hsa.1
    simp only [consMinWords] at this
    refine ⟨by rw [hg]; decide, by omega, by simp [ConsSch.sch] at hn ⊢; omega, hsa.2,
      fun k _ _ => hz _ _⟩
  exact ⟨⟨hctl, by simp [hz]⟩, by simp [hz], hT 0, hT 1, hG⟩

/-! ## The probe and the append, from the model -/

theorem probeC_ok (C : ConsSch) (m : Mem) (ks : List Word) (h t : Word) :
    ProbeOKG C.sch m t (C.mtM m (ks ++ [h]) t) (homeS C.sch m h) (probeC C m ks h t) :=
  probe_homeG C.sch m t _ (cprobeW (m.arr64 C.sa) (C.mtM m (ks ++ [h]) t) t (baseW m t) (gnW C.sa m))
    (fun j d => by rw [cprobeW]; rfl) h

theorem wrRecK_eq (C : ConsSch) (t c : Word) :
    ∀ (vs : List Word) (m : Mem) (f : Word),
      wrRecK C.ra (c * C.st + t * C.w) m f vs = wrRec C.sch t c m f vs := by
  intro vs
  induction vs with
  | nil => intro m f; rfl
  | cons v vs ih =>
    intro m f
    simp only [wrRecK, wrRec, ih, Schema.ad, ConsSch.sch]

theorem pushMC_eq (C : ConsSch) (hra : C.ra ≠ CTL) (m : Mem) (t : Word) (vs : List Word)
    (j c : Word) : pushMC C m t vs j c = pushG C.sch m t vs j c := by
  simp only [pushMC, tailM, pushG, wrRecK_eq, baseW]
  rw [wrRec_arr_ne C.sch t c CTL (Ne.symm hra)]
  rfl

/-- A column write keeps the relation. -/
theorem storeR_set64col (hW : C.WF) (hcR : ColFree C R) {A : ArrId} (hA : C.col = some A)
    (kk x : Word) (h : StoreR C.sch R C.hsM m on P Q) :
    StoreR C.sch R C.hsM (m.set64 A kk x) on P Q := by
  obtain ⟨hra, hsa, hctl, hH⟩ := hW.col A hA
  have ec : (m.set64 A kk x).arr64 CTL = m.arr64 CTL := Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm hctl)
  have er : (m.set64 A kk x).arr64 C.sch.ra = m.arr64 C.sch.ra :=
    Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm hra)
  have es : (m.set64 A kk x).arr64 C.sch.sa = m.arr64 C.sch.sa :=
    Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm hsa)
  obtain ⟨⟨h1, h2⟩, hfl, hT0, hT1, hG⟩ := h
  have tier : ∀ t (tb : Tbl α (Idx k) δ), TierR C.sch R C.hsM m t tb →
      TierR C.sch R C.hsM (m.set64 A kk x) t tb := fun t tb hT =>
    tierR_mono C.sch R C.hsM m _ t tb er es (by simp only [cntW, ec]) (by simp only [baseW, ec])
      (fun i a hr => hcR A hA m kk x t i a hr) (fun i => hH m kk x t i) hT
  exact ⟨⟨by rw [ec]; exact h1, by rw [ec]; exact h2⟩, by rw [ec]; exact hfl, tier 0 P hT0,
    tier 1 Q hT1, growR_of_sa C.sch m _ es hG⟩

theorem storeR_colW (hW : C.WF) (hcR : ColFree C R) (t c x : Word)
    (h : StoreR C.sch R C.hsM m on P Q) : StoreR C.sch R C.hsM (colW C t c x m) on P Q := by
  unfold colW
  split
  · exact h
  · exact storeR_set64col hW hcR ‹_› _ _ h

/-! ## The query's obligations -/

/-- The record of node `c = cntW` of tier `t`: the words `vs` written, nothing else. -/
def newRecM (S : Schema) (m : Mem) (t : Word) (vs : List Word) : Mem := wrRec S t (cntW S m t) m 0 vs

/-- **The query's append obligation**: the record `vs` written as the new node of tier `t` holds
the key, with the query's hash. -/
def NewOKR (S : Schema) (R : Mem → Word → Word → α → Prop) (hs : Mem → Word → Word → Word)
    (m : Mem) (vs : List Word) (key : α) (qh : Word) : Prop :=
  ∀ t, t ≤ 1 → PushRoom S m t → R (newRecM S m t vs) t (cntW S m t) key ∧
    hs (newRecM S m t vs) t (cntW S m t) = qh

/-- A field of the new record, or the old. -/
theorem fld_recW (S : Schema) (hS : S.WF) (m : Mem) (t : Word) (vs : List Word) (t' i f : Word)
    (ht : t ≤ 1) (hc : (cntW S m t).toNat < 2 ^ 27) (ht' : t' ≤ 1) (hi : i.toNat < 2 ^ 27)
    (hf : f < S.w) (hl : vs.length = S.w.toNat) :
    fld S (newRecM S m t vs) t' i f =
      if t' = t ∧ i = cntW S m t ∧ (S.ad t (cntW S m t) f).toNat < (m.arr64 S.ra).size then
        vs.getD f.toNat 0
      else fld S m t' i f := by
  rw [fld, newRecM, wrRec_read S hS t _ t' i f ht hc ht' hi hf vs m 0 (by simp [hl])]
  simp only [fld, UInt64.toNat_zero, Nat.zero_le, true_and, Nat.sub_zero, Nat.zero_add, hl]
  grind

theorem newOK_of (S : Schema) {hs : Mem → Word → Word → Word} (hS : S.WF) (hfr : RFrame S R hs) (m : Mem) (vs : List Word)
    (key : α) (qh : Word) (h : NewOKR S R hs m vs key qh) : NewOK S R hs m vs key qh := by
  intro t j ht hroom
  obtain ⟨h1, h2⟩ := h t ht hroom
  have hra := hS.ra_ctl
  have hrs := hS.ra_sa
  have hca := hS.ca
  have hout : OutEq S (newRecM S m t vs) (pushG S m t vs j (cntW S m t)) := by
    refine ⟨fun b h1 h2 h3 => ?_, ?_⟩
    · simp only [pushG, newRecM, Mem.arr64_set64_ne _ _ _ _ _ h2, Mem.arr64_set64_ne _ _ _ _ _ h3]
    · simp only [pushG, newRecM]
      rw [rdW_set64, Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm hS.sa_ctl)]
      have : S.ca + (t &&& 1) ≠ 0 := by
        rcases word_le_one t ht with rfl | rfl
        · intro e; have := congrArg UInt64.toNat e; simp at this; omega
        · intro e; have := congrArg UInt64.toNat e
          simp [UInt64.toNat_add] at this; omega
      simp [this]
  have hfl : ∀ f, f < S.w → fld S (pushG S m t vs j (cntW S m t)) t (cntW S m t) f =
      fld S (newRecM S m t vs) t (cntW S m t) f := by
    intro f _
    simp only [fld, pushG, newRecM, Mem.arr64_set64_ne _ _ _ _ _ hra, Mem.arr64_set64_ne _ _ _ _ _ hrs]
  obtain ⟨e1, e2⟩ := hfr _ _ t (cntW S m t) hout hfl
  exact ⟨e1 key h1, by rw [e2]; exact h2⟩

/-- **The obligations of a query** `ks` for the arena key `key` in memory `m`: the key has `nk`
words, the match is key equality on the table's nodes, a matching node has the query's hash, and
the new record holds the key with that hash. -/
structure ConsKeyOK (C : ConsSch) (R : Mem → Word → Word → α → Prop) (m : Mem) (ks : List Word)
    (key : α) : Prop where
  hlen : ks.length = C.nk
  match_ : MatchOK R (C.mtM m (ks ++ [C.qhM m ks])) m key
  home : HomeOK C.hsM (C.mtM m (ks ++ [C.qhM m ks])) m (C.qhM m ks)
  new : NewOKR C.sch R C.hsM m (C.vsM (pushArgs C ks (C.qhM m ks))) key (C.qhM m ks)

/-! ## An interning -/

/-- Outside the table's records, counts and column, `pushRec` is the old memory. -/
theorem pushRec_arr (C : ConsSch) (m : Mem) (t : Word) (ks : List Word) (b : ArrId)
    (hb : b ≠ C.ra) (hc : b ≠ CTL) (hcol : C.col ≠ some b) :
    (pushRec C m t ks).arr64 b = m.arr64 b := by
  rw [pushRec, colW_arr C _ _ _ _ b hcol, Mem.arr64_set64_ne _ _ _ _ _ hc, wrRecK_eq,
    wrRec_arr_ne C.sch _ _ b hb]

/-- **The column after the append**: the new node's word at `2 c + t`. -/
theorem pushRec_col (C : ConsSch) (hW : C.WF) {A : ArrId} (hA : C.col = some A) (m : Mem)
    (t : Word) (ks : List Word) :
    (pushRec C m t ks).arr64 A = (m.arr64 A).set! (cntC C m t * 2 + t).toNat
      (C.colM m (pushArgs C ks (C.qhM m ks))) := by
  obtain ⟨hra, -, hc, -⟩ := hW.col A hA
  simp only [pushRec, colW, hA, Mem.arr64_set64_same]
  rw [Mem.arr64_set64_ne _ _ _ _ _ hc, wrRecK_eq, wrRec_arr_ne C.sch _ _ A hra]

/-- **The counts after the append**: tier `t`'s up by one. -/
theorem pushRec_cnt (C : ConsSch) (hW : C.WF) (m : Mem) (t : Word) (ht : t ≤ 1) (ks : List Word)
    (hctl : C.ca.toNat + 2 ≤ (m.arr64 CTL).size) (t' : Word) (ht' : t' ≤ 1) :
    cntC C (pushRec C m t ks) t' = if t' = t then cntC C m t + 1 else cntC C m t' := by
  have hcol : C.col ≠ some CTL := fun e => (hW.col CTL e).2.2.1 rfl
  have hca := hW.sch.ca
  simp only [ConsSch.sch] at hca
  simp only [cntC, pushRec, colW_arr C _ _ _ _ CTL hcol, rdW_set64, wrRecK_eq,
    wrRec_arr_ne C.sch _ _ CTL (Ne.symm hW.sch.ra_ctl)]
  rcases word_le_one t ht with rfl | rfl <;> rcases word_le_one t' ht' with rfl | rfl <;>
    simp [UInt64.toNat_add] <;> first | omega | (intro h; have := congrArg UInt64.toNat h; simp [UInt64.toNat_add] at this; omega)

/-- **An interning hits** (the memory is unchanged) **or appends** node `cntC` to tier `t`: the
handle is the tier's base plus the count, and outside the slot array the memory is `pushRec`. -/
theorem consInternM_out (hW : C.WF) {ks : List Word} {w : Word} {m' : Mem}
    (h : consInternM C m ks = some (w, m')) :
    m' = m ∨ ∃ t, t ≤ 1 ∧ pushOKC C m t = true ∧ w = (if t = 0 then C.P else C.S) + cntC C m t ∧
      (∀ b, b ≠ C.sa → m'.arr64 b = (pushRec C m t ks).arr64 b) ∧
      (∀ b, (m'.arr64 b).size = (m.arr64 b).size) ∧ m'.words.size = m.words.size :=
  consInternM_outA hW.sch.sa_ctl (fun A hA => (hW.col A hA).2.1) h

/-- **What an interning writes**: the table's two arrays, its column, its two counts. -/
theorem consInternM_frame (hW : C.WF) {ks : List Word} {w : Word} {m' : Mem}
    (h : consInternM C m ks = some (w, m')) :
    MemFrame (C.ra :: C.sa :: C.col.toList) [C.ca, C.ca + 1] m m' := by
  rcases consInternM_out hW h with rfl | ⟨t, ht, -, -, he, hs, hw⟩
  · exact MemFrame.refl _ _ _
  have hra := hW.sch.ra_ctl
  refine ⟨fun b hb hc => ?_, fun x hx => ?_, hs, hw⟩
  · simp only [List.mem_cons, not_or] at hb
    rw [he b hb.2.1, pushRec, colW_arr C _ _ _ _ b (fun e => hb.2.2 (by simp [e])),
      Mem.arr64_set64_ne _ _ _ _ _ hc, wrRecK_eq, wrRec_arr_ne C.sch _ _ b hb.1]
  · have hcol : C.col ≠ some CTL := fun e => (hW.col CTL e).2.2.1 rfl
    rw [he CTL hW.sch.sa_ctl.symm, pushRec, colW_arr C _ _ _ _ CTL hcol, rdW_set64,
      wrRecK_eq, wrRec_arr_ne C.sch _ _ CTL (Ne.symm hra)]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    have : C.ca + (t &&& 1) ≠ x := by
      rcases word_le_one t ht with rfl | rfl
      · simpa using Ne.symm hx.1
      · simpa using Ne.symm hx.2
    simp [this]

section word
variable (hW : C.WF) (hR : ConsR C R m on P Q)
include hW hR

/-- A hit's index is below the tier's node count, so below `2^27`. -/
theorem probeC_hit_lt (ks : List Word) (h t : Word) (ht : t ≤ 1) (hr : probeC C m ks h t ≠ [])
    (hh : (probeC C m ks h t).headD 0 ≠ 0) : ((probeC C m ks h t).tail.headD 0).toNat < 2 ^ 27 := by
  obtain ⟨-, hs2, hs3, hj⟩ := ((probeC_ok C m ks h t) hr).1 hh
  obtain ⟨hc, hcap, -, -, -, -, ⟨hsl, -⟩⟩ := hR.tier t ht
  have h1 := hsl _ hj
  rw [hs2] at h1
  have h3 : ((probeC C m ks h t).tail.headD 0 + 1).toNat ≠ 0 := fun e =>
    hs3 (by rw [hs2]; exact UInt64.toNat_inj.mp (by simpa using e))
  rw [UInt64.toNat_add] at h1 h3
  simp only [UInt64.toNat_one] at h1 h3
  have := ((probeC C m ks h t).tail.headD 0).toNat_lt
  omega

/-- **The handle word of an interning**: tag, tier `t` (`1` only with the scratch flag set),
index below `2^27`. -/
theorem consInternM_word {ks : List Word} {w : Word} {m' : Mem}
    (h : consInternM C m ks = some (w, m')) :
    ∃ t i, t ≤ 1 ∧ i.toNat < 2 ^ 27 ∧ w = hdW C.tag.toUInt64 t i ∧
      (rdW (m.arr64 CTL) 1 = 0 → t = 0) := by
  have hc : ∀ t, pushOKC C m t = true → (cntC C m t).toNat < 2 ^ 27 := fun t hp => by
    simp only [pushOKC, Bool.and_eq_true, decide_eq_true_eq] at hp
    exact hp.1
  have b0 := hW.base0
  have b1 := hW.base1
  simp only [consInternM, pushC] at h
  split at h
  · simp at h
  split at h
  · rename_i hn hh
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨0, _, by decide, probeC_hit_lt hW hR ks (C.qhM m ks) 0 (by decide)
      (fun e => hn ⟨hh.1, e⟩) hh.2, b0 _, fun _ => rfl⟩
  split at h
  · rename_i hfl
    split at h
    · simp at h
    split at h
    · rename_i hz hhit
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨1, _, by decide, probeC_hit_lt hW hR ks (C.qhM m ks) 1 (by decide) hz hhit, b1 _,
        fun h0 => absurd h0 hfl⟩
    split at h
    · rename_i hp
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact ⟨1, _, by decide, hc 1 hp, b1 _, fun h0 => absurd h0 hfl⟩
      · simp at h
    · simp at h
  split at h
  · rename_i hp
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨0, _, by decide, hc 0 hp, b0 _, fun _ => rfl⟩
    · simp at h
  · simp at h

/-- **An interned handle word is below `2^32`.** -/
theorem consInternM_lt {ks : List Word} {w : Word} {m' : Mem}
    (h : consInternM C m ks = some (w, m')) : w.toNat < 2 ^ 32 := by
  obtain ⟨t, i, ht, hi, rfl, -⟩ := consInternM_word hW hR h
  rw [hdW_toNat _ _ _ hW.tag16 ht hi]
  have := hW.tag16
  have ht' : t.toNat ≤ 1 := ht
  omega

/-- **With the flag clear, an interned handle word is persistent** (`PW`). -/
theorem consInternM_pw (hfl : rdW (m.arr64 CTL) 1 = 0) {ks : List Word} {w : Word} {m' : Mem}
    (h : consInternM C m ks = some (w, m')) : w.toNat < 2 ^ 32 ∧ tierW w = 0 := by
  refine ⟨consInternM_lt hW hR h, ?_⟩
  obtain ⟨t, i, ht, hi, rfl, h0⟩ := consInternM_word hW hR h
  obtain rfl := h0 hfl
  have e := hdW_toNat _ _ _ hW.tag16 ht hi
  have := hW.tag16
  apply UInt64.toNat_inj.mp
  rw [show tierW (hdW C.tag.toUInt64 0 i) = (hdW C.tag.toUInt64 0 i >>> 27) &&& 1 from rfl,
    bit27_toNat, e]
  simp only [UInt64.toNat_zero]
  omega

end word

/-! ## The refinement -/

/-- **An interning refines the arena's hash-consing**, for any table: if `consInternM` returns the
handle `w` and the memory `m'`, the arena operation `op` (whose run is `protoRun`) succeeds with
the handle `w`, in a state whose tables `m'` represents. -/
theorem consIntern_correct [LawfulBEq α] (hW : C.WF) (hfr : RFrame C.sch R C.hsM)
    (hcR : ColFree C R) (L : Lens α δ k) (a : AState)
    (hR : ConsR C R m (L.on a) (L.getP a) (L.getS a))
    (op : AM (Idx k)) (key : α) (pf : Option (Idx k)) (d : δ) (err : CheckError)
    (hrun : op.run a = protoRun L key C.tag pf d err a)
    (skB : Bool) (hpf : pf = if skB then none else (L.getP a).cons[key]?)
    (ks : List Word) (hsk : (skipC C m ks = 0) = (skB = false)) (hskon : skB = true → L.on a = true)
    (hK : ConsKeyOK C R m ks key) (w : Word) (m' : Mem) (hI : consInternM C m ks = some (w, m')) :
    AM.ok op a ∧
    ConsR C R m' (L.on (AM.st op a)) (L.getP (AM.st op a)) (L.getS (AM.st op a)) ∧
    AM.res op a = decI w := by
  have hS := hW.sch
  obtain ⟨⟨hctl, hb⟩, hflag, hT0, hT1, hG⟩ := id hR
  have hN := newOK_of C.sch hS hfr m _ key _ hK.new
  have hl := hW.vs ks (C.qhM m ks) hK.hlen
  have hP0 := probeC_ok C m ks (C.qhM m ks) 0
  have hP1 := probeC_ok C m ks (C.qhM m ks) 1
  have hit0 := tierR_hit C.sch R C.hsM m 0 _ hT0 _ key hK.match_ _ _ hP0
  have hit1 := tierR_hit C.sch R C.hsM m 1 _ hT1 _ key hK.match_ _ _ hP1
  have miss0 := tierR_miss C.sch R C.hsM m 0 _ hT0 _ key hK.match_ _ hK.home _ hP0
  have miss1 := tierR_miss C.sch R C.hsM m 1 _ hT1 _ key hK.match_ _ hK.home _ hP1
  have e0 := hW.base 0 (by decide)
  have e1 := hW.base 1 (by decide)
  simp only [show (0 : Word) = 0 from rfl, ↓reduceIte, show (1 : Word) ≠ 0 by decide] at e0 e1
  have hL := L.on_setP
  have htag : C.sch.tag = C.tag := rfl
  -- the append to tier `t` at slot `j`, then the column, then the growth
  have push : ∀ t, t ≤ 1 → ∀ (j : Word) (P' Q' : Tbl α (Idx k) δ) (m₂ : Mem),
      StoreR C.sch R C.hsM (pushG C.sch m t (C.vsM (pushArgs C ks (C.qhM m ks))) j (cntC C m t))
        (L.on a) P' Q' →
      growIf C.sa C.ca C.hsM m (pushMX C m t (C.vsM (pushArgs C ks (C.qhM m ks)))
        (C.colM m (pushArgs C ks (C.qhM m ks))) j (cntC C m t)) (cntC C m t) = some m₂ →
      StoreR C.sch R C.hsM m₂ (L.on a) P' Q' := by
    intro t ht j P' Q' m₂ hX hg
    rw [pushMX, pushMC_eq C hS.ra_ctl] at hg
    exact storeR_growIf C.sch R C.hsM hS hfr m _ m₂ _ _ _ _ (storeR_colW hW hcR _ _ _ hX) hg
  simp only [consInternM, pushC] at hI
  split at hI
  · simp at hI
  rename_i hn0
  split at hI
  · -- persistent hit
    rename_i hh0
    simp only [Option.some.injEq, Prod.mk.injEq] at hI
    obtain ⟨rfl, rfl⟩ := hI
    have hskB : skB = false := by rw [← hsk]; exact hh0.1
    have hpf' : pf = some (decI (hdW C.sch.tag.toUInt64 0
        ((probeC C m ks (C.qhM m ks) 0).tail.headD 0))) := by
      rw [hpf, hskB]; exact hit0 (fun e => hn0 ⟨hh0.1, e⟩) hh0.2
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ (hrun.trans (by rw [hpf']; rfl))
    refine ⟨hok, by rw [hst]; exact hR, by rw [hres, e0]; rfl⟩
  rename_i hh0
  -- the persistent probe misses or is skipped
  have hpf' : pf = none := by
    rw [hpf]
    cases hb' : skB
    · have hs0 : skipC C m ks = 0 := by rw [hsk]; exact hb'
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact miss0 (fun e => hn0 ⟨hs0, e⟩) (Classical.byContradiction fun hc => hh0 ⟨hs0, hc⟩)
    · simp
  subst hpf'
  split at hI
  · rename_i hfl
    have hon : L.on a = true := by rw [← hflag]; simpa using hfl
    split at hI
    · simp at hI
    rename_i hn1
    split at hI
    · -- scratch hit
      rename_i hh1
      simp only [Option.some.injEq, Prod.mk.injEq] at hI
      obtain ⟨rfl, rfl⟩ := hI
      obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _
        (hrun.trans (protoRun_hitS L key C.tag d err a _ hon (hit1 hn1 hh1)))
      refine ⟨hok, by rw [hst]; exact hR, by rw [hres, e1]; rfl⟩
    rename_i hh1
    have hz1 : (probeC C m ks (C.qhM m ks) 1).headD 0 = 0 := by simpa using hh1
    split at hI
    · -- scratch append
      rename_i hpk
      split at hI
      · rename_i m₂ hg
        simp only [Option.some.injEq, Prod.mk.injEq] at hI
        obtain ⟨rfl, rfl⟩ := hI
        have hroom := hW.room' m 1 hpk
        have hsz : (L.getS a).nodes.size < 134217728 := by
          have := hroom.1; rw [hT1.1] at this; simpa using this
        obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _
          (hrun.trans (protoRun_pushS L key C.tag d err a hon (miss1 hn1 hz1) hsz))
        have e : UInt64.ofNat (L.getS a).nodes.size = cntC C m 1 := by
          rw [← hT1.1]; exact UInt64.ofNat_toNat
        rw [e] at hst hres
        have hp1 := tierR_push C.sch R C.hsM hS hfr m 1 (by decide) _ hT1 _ key hK.match_ _ hK.home _
          hP1 hn1 hz1 hroom hctl hb _ hl hN d hG
        have hj : (probeC C m ks (C.qhM m ks) 1).tail.tail.headD 0 < nSl C.sch m :=
          ((hP1 hn1).2 hz1).2.1
        rw [hst, hres, L.on_setS, L.getP_setS, L.getS_setS]
        refine ⟨hok, push 1 (by decide) _ _ _ m₂ ?_ hg, by rw [e1]⟩
        refine storeR_push C.sch R C.hsM hS m 1 (by decide) _ _ hj _ _ _ _ _ hR ?_ hp1
        exact tierR_other C.sch R C.hsM hS hfr m 1 0 (by decide) (by decide) (by decide) _ hT0
          hroom hb _ hl _ hG hj
      · simp at hI
    · simp at hI
  rename_i hfl
  have hon : L.on a = false := by rw [← hflag]; simpa using hfl
  have hs0 : skipC C m ks = 0 := by
    rw [hsk]; cases hb' : skB
    · rfl
    · exact absurd (hskon hb') (by simp [hon])
  have hn0' : probeC C m ks (C.qhM m ks) 0 ≠ [] := fun e => hn0 ⟨hs0, e⟩
  have hz0 : (probeC C m ks (C.qhM m ks) 0).headD 0 = 0 :=
    Classical.byContradiction fun hc => hh0 ⟨hs0, hc⟩
  split at hI
  · -- persistent append
    rename_i hpk
    split at hI
    · rename_i m₂ hg
      simp only [Option.some.injEq, Prod.mk.injEq] at hI
      obtain ⟨rfl, rfl⟩ := hI
      have hroom := hW.room' m 0 hpk
      have hsz : (L.getP a).nodes.size < 134217728 := by
        have := hroom.1; rw [hT0.1] at this; simpa using this
      obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _
        (hrun.trans (protoRun_pushP L key C.tag d err a hon hsz))
      have e : UInt64.ofNat (L.getP a).nodes.size = cntC C m 0 := by
        rw [← hT0.1]; exact UInt64.ofNat_toNat
      rw [e] at hst hres
      have hp0 := tierR_push C.sch R C.hsM hS hfr m 0 (by decide) _ hT0 _ key hK.match_ _ hK.home _
        hP0 hn0' hz0 hroom hctl hb _ hl hN d hG
      have hj : (probeC C m ks (C.qhM m ks) 0).tail.tail.headD 0 < nSl C.sch m :=
        ((hP0 hn0').2 hz0).2.1
      rw [hst, hres, L.on_setP, L.getP_setP, L.getS_setP]
      refine ⟨hok, push 0 (by decide) _ _ _ m₂ ?_ hg, by rw [e0]⟩
      refine storeR_push C.sch R C.hsM hS m 0 (by decide) _ _ hj _ _ _ _ _ hR hp0 ?_
      exact tierR_other C.sch R C.hsM hS hfr m 0 1 (by decide) (by decide) (by decide) _ hT1
        hroom hb _ hl _ hG hj
    · simp at hI
  · simp at hI

end rel


/-- The relation is opaque outside the library: the lemmas above are its interface. -/
attribute [irreducible] ConsR

end L.Arena
