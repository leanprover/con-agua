import ConAgua.Arena.ConsLibSpec
import ConAgua.Arena.ViewL
import ConAgua.Arena.Frame
import ConAgua.Arena.StoreGrow
set_option linter.unusedSectionVars false

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


namespace L.Arena

/-! ## A store relation across a writer apart from it (`Frame.lean`'s `Apart`) -/

section frame
variable {α δ : Type} {k : IdxKind} [BEq α] [Hashable α]
variable (S : Schema) (R : Mem → Word → Word → α → Prop) (hs : Mem → Word → Word → Word)
  (KP : Mem → Word → Word → Word → Prop)

/-- The key-word predicate survives any change that keeps the records and the node hashes. -/
def KMono : Prop :=
  ∀ m m' t i, m'.arr64 (tierA S.ra t) = m.arr64 (tierA S.ra t) → hs m' t i = hs m t i →
    ∀ K, KP m t i K → KP m' t i K

/-- **A table's relation survives a writer it is apart from.** -/
theorem storeR_frame (hS : S.WF) (hkm : KMono S hs KP) (A₀ : List ArrId) (C₀ : List Word)
    (hl : RLocal S R hs A₀ C₀)
    (A : List ArrId) (C : List Word) (hap : Apart S A₀ C₀ A C) (m m' : Mem) (hf : MemFrame A C m m') (on : Bool)
    (tbP tbS : Tbl α (Idx k) δ) (hR : StoreR S R hs KP m on tbP tbS) :
    StoreR S R hs KP m' on tbP tbS := by
  obtain ⟨hra, hra', hsa, hsa', hA₀, hc0, hc1, h1, hscb, h0⟩ := hap
  obtain ⟨hfa, hfc, hfs, -⟩ := hf
  obtain ⟨⟨hctl, hb⟩, hfl, hT0, hT1, hG⟩ := hR
  have eb : ∀ t, baseW m' t = baseW m t := fun t => by simp only [baseW, hfc SCB hscb]
  have era : ∀ t, m'.arr64 (tierA S.ra t) = m.arr64 (tierA S.ra t) := fun t => by
    rcases tierA_cases' S.ra t with e | e <;> rw [e]
    · exact hfa _ hra hS.ra_ctl
    · exact hfa _ hra' (by simp [CTL])
  have esa : ∀ t, m'.arr64 (tierA S.sa t) = m.arr64 (tierA S.sa t) := fun t => by
    rcases tierA_cases' S.sa t with e | e <;> rw [e]
    · exact hfa _ hsa hS.sa_ctl
    · exact hfa _ hsa' (by simp [CTL])
  have hloc := hl m m' era (fun b hb => hfa b (hA₀ b hb).1 (hA₀ b hb).2) (fun x hx => hfc x (h0 x hx))
  have ec : ∀ t : Word, t ≤ 1 → cntW S m' t = cntW S m t := by
    intro t ht
    simp only [cntW]
    apply hfc
    rcases word_le_one t ht with rfl | rfl
    · simpa using hc0
    · exact hc1
  refine ⟨⟨by rw [hfs]; exact hctl, by rw [hfc SCB hscb]; exact hb⟩, by rw [hfc 1 h1]; exact hfl, ?_, ?_, ?_⟩
  · exact tierR_mono S R hs KP m m' 0 tbP (era 0) (esa 0) (ec 0 (by decide)) (eb 0) (hloc.1 0)
      (hloc.2 0) (fun i K h => hkm m m' 0 i (era 0) (hloc.2 0 i) K h) hT0
  · exact tierR_mono S R hs KP m m' 1 tbS (era 1) (esa 1) (ec 1 (by decide)) (eb 1) (hloc.1 1)
      (hloc.2 1) (fun i K h => hkm m m' 1 i (era 1) (hloc.2 1 i) K h) hT1
  · exact growR_of_sa S m m' esa hG

end frame

/-! ## The schema as a store schema -/

/-- The store schema of a cons table (`StoreLib.lean`). -/
def ConsSch.sch (C : ConsSch) : Schema := ⟨C.ra, C.sa, C.w, C.ca, C.tag⟩


/-- Key word `f` of node `i` of tier `t`: record word `f`, or (a packed record, `kpk`) the low
(`f = 0`) or high half of record word `0`. -/
def kfld (C : ConsSch) (m : Mem) (t i : Word) (f : Nat) : Word :=
  if C.kpk then (if f = 0 then fld C.sch m t i 0 &&& 4294967295 else fld C.sch m t i 0 >>> 32)
  else fld C.sch m t i (UInt64.ofNat f)

/-- The node's key words (`kfld`): its first `nk` record words, or the two halves of word `0`. -/
def fieldsL (C : ConsSch) (m : Mem) (t i : Word) : List Word :=
  (List.range C.nk).map (kfld C m t i)

/-- The number of record words the key fills: `1` packed, else `nk`. -/
def nkW (C : ConsSch) : Nat := if C.kpk then 1 else C.nk

/-- The record words of a key: the key, or (packed) its two words in one (`kwQ`). -/
def recK (C : ConsSch) (ks : List Word) : List Word := if C.kpk then [kwQ C ks 0] else ks

/-- **An exact table's facts**: at most two key words, inside the record (a packed record: two,
in word `0`); the match is equality of the key words; the node's hash is the key's hash of its
key words, which reads no memory; the pushed record starts with the key's record words. -/
structure ExactOK (C : ConsSch) : Prop where
  nk : C.nk ≤ 2
  nkw : nkW C ≤ C.w.toNat
  kpk : C.kpk = true → C.nk = 2
  mt : ∀ (m : Mem) (ks : List Word) (h t i : Word), ks.length = C.nk →
    (C.mtM m (ks ++ [h]) t i = true ↔ fieldsL C m t i = ks)
  hs : ∀ (m : Mem) (t i : Word), C.hsM m t i = C.qhM m (fieldsL C m t i)
  qh : ∀ (m m' : Mem) (ks : List Word), C.qhM m ks = C.qhM m' ks
  vs : ∀ (ks : List Word) (h : Word), ks.length = C.nk → ∀ f, f < nkW C →
    (C.vsM (pushArgs C ks h)).getD f 0 = (recK C ks).getD f 0

/-- **What the generic lemmas need of a cons table.** -/
structure ConsSch.WF (C : ConsSch) : Prop where
  sch : C.sch.WF
  P : C.P = hdW C.tag.toUInt64 0 0
  S : C.S = hdW C.tag.toUInt64 1 0
  col : ∀ A, C.col = some A → A ≠ C.ra ∧ A ≠ C.sa ∧ A ≠ CTL ∧
    ∀ (m : Mem) (u k x t i : Word), C.hsM (m.set64 (tierA A u) k x) t i = C.hsM m t i
  room : ∀ (m : Mem) (t : Word), pushOKC C m t = true →
    C.w.toNat * ((cntC C m t).toNat + 1) ≤ (m.arr64 (tierA C.ra t)).size
  colRoom : ∀ A, C.col = some A → ∀ (m : Mem) (t : Word), t ≤ 1 → pushOKC C m t = true →
    (cntC C m t).toNat < (m.arr64 (tierA A t)).size
  /-- The column is a tier-0 id (tier 1 is `+ 256`). -/
  colLt : ∀ A, C.col = some A → A < 256
  vs : ∀ (ks : List Word) (h : Word), ks.length = C.nk →
    (C.vsM (pushArgs C ks h)).length = C.w.toNat
  /-- An exact table's facts (`ExactOK`). -/
  ex : C.exact = true → ExactOK C

/-- The record relation `R` does not read the table's column. -/
def ColFree {α : Type} (C : ConsSch) (R : Mem → Word → Word → α → Prop) : Prop :=
  ∀ A, C.col = some A → ∀ (m : Mem) (u k x t i : Word) (a : α), R m t i a →
    R (m.set64 (tierA A u) k x) t i a

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

/-! ## The key words of a slot -/

/-- **The key words a slot of node `i` of tier `t` may hold**: an exact table's packed key words
(`kwQ`, two words below `2^32`), else the node's hash (a fingerprint). -/
def ConsSch.KP (C : ConsSch) (m : Mem) (t i K : Word) : Prop :=
  if C.exact then K = kwQ C (fieldsL C m t i) 0 ∧
    (C.nk = 2 → ∀ f : Nat, f < 2 → (kfld C m t i f).toNat < 2 ^ 32)
  else K = C.hsM m t i

theorem fieldsL_congr {C : ConsSch} {m m' : Mem} {t i : Word}
    (h : ∀ f : Nat, f < C.nk → kfld C m' t i f = kfld C m t i f) :
    fieldsL C m' t i = fieldsL C m t i := by
  unfold fieldsL; apply List.map_congr_left; intro f hf; exact h f (List.mem_range.mp hf)

/-- The key words depend only on the record words the key fills. -/
theorem kfld_congr {C : ConsSch} {m m' : Mem} {t i : Word}
    (h : ∀ g : Nat, g < nkW C → fld C.sch m' t i (UInt64.ofNat g) = fld C.sch m t i (UInt64.ofNat g))
    (f : Nat) (hf : f < C.nk) : kfld C m' t i f = kfld C m t i f := by
  unfold kfld
  cases hp : C.kpk
  · simp only [Bool.false_eq_true, ↓reduceIte]; exact h f (by simp [nkW, hp, hf])
  · have h0 : fld C.sch m' t i 0 = fld C.sch m t i 0 := h 0 (by simp [nkW, hp])
    simp only [↓reduceIte, h0]

theorem ConsSch.kp_mono (C : ConsSch) : KMono C.sch C.hsM C.KP := by
  intro m m' t i hra hh K hK
  have hf : ∀ f, fld C.sch m' t i f = fld C.sch m t i f := fun f => by simp only [fld, hra]
  have hk : ∀ f, kfld C m' t i f = kfld C m t i f := fun f => by simp only [kfld, hf]
  unfold ConsSch.KP at hK ⊢
  cases hx : C.exact
  · simp only [hx, Bool.false_eq_true, ↓reduceIte] at hK ⊢; rw [hh]; exact hK
  · simp only [hx, ↓reduceIte] at hK ⊢
    rw [fieldsL_congr (fun f _ => hk _)]; simp only [hk]; exact hK

theorem ConsSch.WF.kframe {C : ConsSch} (hW : C.WF) : KFrame C.sch C.hsM C.KP := by
  intro m m' t i hf hh K hK
  unfold ConsSch.KP at hK ⊢
  cases hx : C.exact
  · simp only [hx, Bool.false_eq_true, ↓reduceIte] at hK ⊢; rw [hh]; exact hK
  · have hE := hW.ex hx
    have hw := hW.sch.w_le
    have hg : ∀ g : Nat, g < nkW C →
        fld C.sch m' t i (UInt64.ofNat g) = fld C.sch m t i (UInt64.ofNat g) := fun g hg0 =>
      hf _ (by
        have := hE.nk
        have : nkW C ≤ 2 := by unfold nkW; split <;> omega
        rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
        have := hE.nkw; simp only [ConsSch.sch] at hw ⊢; omega)
    have hf' := kfld_congr hg
    simp only [hx, ↓reduceIte] at hK ⊢
    rw [fieldsL_congr hf']
    refine ⟨hK.1, fun h2 f hf2 => by rw [hf' f (by omega)]; exact hK.2 h2 f hf2⟩

/-! ## The relation -/

section rel
variable {α δ : Type} {k : IdxKind} [BEq α] [Hashable α]

/-- **A cons table represents the arena's two tables** `P` (persistent) and `Q` (scratch). -/
def ConsR (C : ConsSch) (R : Mem → Word → Word → α → Prop) (m : Mem) (on : Bool)
    (P Q : Tbl α (Idx k) δ) : Prop :=
  StoreR C.sch R C.hsM C.KP m on P Q

theorem consR_iff {C : ConsSch} {R : Mem → Word → Word → α → Prop} {m : Mem} {on : Bool}
    {P Q : Tbl α (Idx k) δ} : ConsR C R m on P Q ↔ StoreR C.sch R C.hsM C.KP m on P Q := Iff.rfl

variable {C : ConsSch} {R : Mem → Word → Word → α → Prop} {m : Mem} {on : Bool}
  {P Q : Tbl α (Idx k) δ}

/-- Two schemas with the same arrays, counts, tag, hash and key words have the same relation. -/
theorem ConsR.congr {C' : ConsSch} (hs : C.sch = C'.sch) (hh : C.hsM = C'.hsM)
    (he : C.exact = C'.exact := by rfl) (hn : C.nk = C'.nk := by rfl)
    (hp : C.kpk = C'.kpk := by rfl) :
    ConsR C R m on P Q ↔ ConsR C' R m on P Q := by
  have hkf : kfld C = kfld C' := by funext m t i f; simp only [kfld, hs, hp]
  have hk : C.KP = C'.KP := by
    funext m t i K; simp only [ConsSch.KP, fieldsL, hkf, kwQ, hh, he, hn]
  simp only [consR_iff, hs, hh, hk]

theorem ConsR.tier (h : ConsR C R m on P Q) (t : Word) (ht : t ≤ 1) :
    TierR C.sch R C.hsM C.KP m t (if t = 0 then P else Q) := by
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
    C.w.toNat * (if t = 0 then P else Q).nodes.size ≤ (m.arr64 (tierA C.ra t)).size :=
  (h.tier t ht).2.2.1

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

/-- `ConsR.mono` with the nodes' relation needed only for the nodes of the two tables (e.g. a
change of the pool tops under `scratch_reset`, after which only the persistent nodes are left). -/
theorem ConsR.mono' {m' : Mem} (h : ConsR C R m on P Q)
    (hra : ∀ t, m'.arr64 (tierA C.ra t) = m.arr64 (tierA C.ra t))
    (hsa : ∀ t, m'.arr64 (tierA C.sa t) = m.arr64 (tierA C.sa t)) (hsz : (m'.arr64 CTL).size = (m.arr64 CTL).size)
    (hc : ∀ x, x = 1 ∨ x = SCB ∨ x = C.ca ∨ x = C.ca + 1 → rdW (m'.arr64 CTL) x = rdW (m.arr64 CTL) x)
    (hR0 : ∀ (i : Word) a, P.nodes[i.toNat]? = some a → R m 0 i a → R m' 0 i a)
    (hR1 : ∀ (i : Word) a, Q.nodes[i.toNat]? = some a → R m 1 i a → R m' 1 i a)
    (hh : ∀ t i, C.hsM m' t i = C.hsM m t i) :
    ConsR C R m' on P Q := by
  obtain ⟨⟨h1, h2⟩, hfl, hT0, hT1, hG⟩ := h
  have hc0 : ∀ t, t ≤ 1 → cntW C.sch m' t = cntW C.sch m t := fun t ht => by
    simp only [cntW]; rcases word_le_one t ht with rfl | rfl
    · exact hc _ (.inr (.inr (.inl (by simp [ConsSch.sch]))))
    · exact hc _ (.inr (.inr (.inr rfl)))
  have hb : ∀ t, baseW m' t = baseW m t := fun t => by simp only [baseW, hc SCB (.inr (.inl rfl))]
  have hkp : ∀ t i K, C.KP m t i K → C.KP m' t i K := fun t i K hK => C.kp_mono m m' t i (hra t) (hh t i) K hK
  refine ⟨⟨by rw [hsz]; exact h1, by rw [hc SCB (.inr (.inl rfl))]; exact h2⟩,
    by rw [hc 1 (.inl rfl)]; exact hfl,
    tierR_mono' C.sch R C.hsM C.KP m m' 0 P (hra 0) (hsa 0) (hc0 0 (by decide)) (hb 0) hR0 (hh 0) (hkp 0) hT0,
    tierR_mono' C.sch R C.hsM C.KP m m' 1 Q (hra 1) (hsa 1) (hc0 1 (by decide)) (hb 1) hR1 (hh 1) (hkp 1) hT1,
    growR_of_sa C.sch m m' hsa hG⟩

/-- **The relation survives any change that keeps the table's arrays, its `CTL` words (counts,
flag, scratch epoch) and every node's relation and hash** (e.g. the pool growing under `lit`). -/
theorem ConsR.mono {m' : Mem} (h : ConsR C R m on P Q)
    (hra : ∀ t, m'.arr64 (tierA C.ra t) = m.arr64 (tierA C.ra t))
    (hsa : ∀ t, m'.arr64 (tierA C.sa t) = m.arr64 (tierA C.sa t)) (hsz : (m'.arr64 CTL).size = (m.arr64 CTL).size)
    (hc : ∀ x, x = 1 ∨ x = SCB ∨ x = C.ca ∨ x = C.ca + 1 → rdW (m'.arr64 CTL) x = rdW (m.arr64 CTL) x)
    (hR : ∀ t i a, R m t i a → R m' t i a) (hh : ∀ t i, C.hsM m' t i = C.hsM m t i) :
    ConsR C R m' on P Q := by
  obtain ⟨⟨h1, h2⟩, hfl, hT0, hT1, hG⟩ := h
  have tier : ∀ t (tb : Tbl α (Idx k) δ), t ≤ 1 → TierR C.sch R C.hsM C.KP m t tb →
      TierR C.sch R C.hsM C.KP m' t tb := fun t tb ht hT =>
    tierR_mono C.sch R C.hsM C.KP m m' t tb (hra t) (hsa t)
      (by simp only [cntW]; rcases word_le_one t ht with rfl | rfl
          · exact hc _ (.inr (.inr (.inl (by simp [ConsSch.sch]))))
          · exact hc _ (.inr (.inr (.inr rfl))))
      (by simp only [baseW, hc SCB (.inr (.inl rfl))]) (hR t) (hh t)
      (fun i K hK => C.kp_mono m m' t i (hra t) (hh t i) K hK) hT
  exact ⟨⟨by rw [hsz]; exact h1, by rw [hc SCB (.inr (.inl rfl))]; exact h2⟩,
    by rw [hc 1 (.inl rfl)]; exact hfl, tier 0 P (by decide) hT0, tier 1 Q (by decide) hT1,
    growR_of_sa C.sch m m' hsa hG⟩

/-- **A table's relation survives a writer it is apart from** (`Frame.lean`'s `Apart`, `RLocal`). -/
theorem ConsR.frame (hW : C.WF) {A₀ : List ArrId} {C₀ : List Word}
    (hl : RLocal C.sch R C.hsM A₀ C₀) {A : List ArrId} {Cw : List Word}
    (hap : Apart C.sch A₀ C₀ A Cw) {m' : Mem} (hf : MemFrame A Cw m m')
    (h : ConsR C R m on P Q) : ConsR C R m' on P Q :=
  storeR_frame C.sch R C.hsM C.KP hW.sch C.kp_mono A₀ C₀ hl A Cw hap m m' hf on P Q h

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
  have hra : ∀ t, (m.set64 CTL 1 w).arr64 (tierA C.sch.ra t) = m.arr64 (tierA C.sch.ra t) :=
    fun t => Mem.arr64_set64_ne _ _ _ _ _ (hS.ra_ctl' t)
  have hsa : ∀ t, (m.set64 CTL 1 w).arr64 (tierA C.sch.sa t) = m.arr64 (tierA C.sch.sa t) :=
    fun t => Mem.arr64_set64_ne _ _ _ _ _ (hS.sa_ctl' t)
  have hout : OutEq C.sch m (m.set64 CTL 1 w) :=
    ⟨fun b _ _ _ _ hb => Mem.arr64_set64_ne _ _ _ _ _ hb, hrd 0 (by decide)⟩
  have hfld : ∀ t i f, f < C.sch.w → fld C.sch (m.set64 CTL 1 w) t i f = fld C.sch m t i f := by
    intro t i f _; simp only [fld, hra]
  have hscb' : SCB ≠ (1 : Word) := by decide
  have tier : ∀ (t : Word) (tb : Tbl α (Idx k) δ), t ≤ 1 → TierR C.sch R C.hsM C.KP m t tb →
      TierR C.sch R C.hsM C.KP (m.set64 CTL 1 w) t tb := by
    intro t tb ht hT
    refine tierR_mono C.sch R C.hsM C.KP m _ t tb (hra t) (hsa t) ?_ ?_
      (fun i a hr => ((hfr _ _ t i hout (hfld t i)).1 a hr)) (fun i => (hfr _ _ t i hout (hfld t i)).2)
      (fun i K hK => C.kp_mono m _ t i (hra t) (hfr _ _ t i hout (hfld t i)).2 K hK) hT
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

/-- **The scratch reset** (`scratch_reset`): the record arrays and tier 0's slot array stay, tier
1's slot array keeps its size and its count and offset words, every slot of its table reads free
(`ConsR.free_raise`, `ConsR.free_zero`), tier 0's count and nodes stay, tier 1's count becomes `0`,
the flag becomes `on'`: tier 0 as before, tier 1 empty. -/
theorem ConsR.resetG (h : ConsR C R m on P Q) {m' : Mem} {on' : Bool}
    (hra : ∀ t, m'.arr64 (tierA C.ra t) = m.arr64 (tierA C.ra t))
    (hsa0 : m'.arr64 (tierA C.sa 0) = m.arr64 (tierA C.sa 0))
    (hsz1 : (m'.arr64 (tierA C.sa 1)).size = (m.arr64 (tierA C.sa 1)).size)
    (hw0 : rdW (m'.arr64 (tierA C.sa 1)) 0 = rdW (m.arr64 (tierA C.sa 1)) 0)
    (hw1 : rdW (m'.arr64 (tierA C.sa 1)) 1 = rdW (m.arr64 (tierA C.sa 1)) 1)
    (hfree : ∀ j : Word, j < nSl C.sch m 1 → slotW C.sch m' 1 j = 0)
    (hsz : (m'.arr64 CTL).size = (m.arr64 CTL).size)
    (hc0 : cntC C m' 0 = cntC C m 0) (hc1 : cntC C m' 1 = 0)
    (hb : (rdW (m'.arr64 CTL) SCB).toNat < 2 ^ 62 + 2 ^ 32)
    (hfl : (rdW (m'.arr64 CTL) 1 != 0) = on')
    (hR0 : ∀ i a, R m 0 i a → R m' 0 i a) (hh0 : ∀ i, C.hsM m' 0 i = C.hsM m 0 i) :
    ConsR C R m' on' P (Tbl.empty : Tbl α (Idx k) δ) :=
  storeR_resetG C.sch R C.hsM C.KP m m' on on' P Q h hra hsa0 hsz1 hw0 hw1 hfree hsz hc0 hc1
    hb hfl hR0 hh0 (fun i K hK => C.kp_mono m m' 0 i (hra 0) (hh0 i) K hK)

/-- The slots a base raised by `2^32` (from below `2^62`) leaves free: all of tier 1's. -/
theorem ConsR.free_raise (h : ConsR C R m on P Q) {m' : Mem}
    (hsa : m'.arr64 (tierA C.sa 1) = m.arr64 (tierA C.sa 1))
    (hlo : (rdW (m.arr64 CTL) SCB).toNat < 2 ^ 62)
    (hb : rdW (m'.arr64 CTL) SCB = rdW (m.arr64 CTL) SCB + 4294967296) :
    ∀ j : Word, j < nSl C.sch m 1 → slotW C.sch m' 1 j = 0 :=
  slotW_free_raise C.sch R C.hsM C.KP m m' Q h.2.2.2.1 hsa hlo hb

/-- The slots a zeroed scratch table leaves free: all of tier 1's. -/
theorem ConsR.free_zero (h : ConsR C R m on P Q) {m' : Mem}
    (hw1 : rdW (m'.arr64 (tierA C.sa 1)) 1 = rdW (m.arr64 (tierA C.sa 1)) 1)
    (hz : ∀ y : Word, (krW C.sa m 1).toNat ≤ y.toNat →
      y.toNat < (krW C.sa m 1).toNat + 2 * (knW C.sa m 1).toNat → rdW (m'.arr64 (tierA C.sa 1)) y = 0) :
    ∀ j : Word, j < nSl C.sch m 1 → slotW C.sch m' 1 j = 0 :=
  slotW_free_zero C.sch m m' h.2.2.2.2 hw1 hz

/-- The scratch table's layout, as numbers: at least 8 slots, a multiple of 8, from word `2 + o`
inside its array (below `2^61` words). -/
theorem ConsR.lay1 (h : ConsR C R m on P Q) :
    (m.arr64 (tierA C.sa 1)).size < 2 ^ 61 ∧ 8 ≤ (knW C.sa m 1).toNat ∧
    (knW C.sa m 1).toNat % 8 = 0 ∧
    2 + (koW C.sa m 1).toNat + 2 * (knW C.sa m 1).toNat ≤ (m.arr64 (tierA C.sa 1)).size :=
  let ⟨h1, h2, h3, h4, _⟩ := h.2.2.2.2.2
  ⟨h1, h2, h3, h4⟩

/-- **The relation holds initially**: the all-zero memory, both tables empty. -/
theorem consR_init (hz : ∀ b x, rdW (m.arr64 b) x = 0) (hctl : C.ca.toNat + 2 ≤ (m.arr64 CTL).size)
    (hsa : ∀ t, consMinWords ≤ (m.arr64 (tierA C.sa t)).size ∧ (m.arr64 (tierA C.sa t)).size < 2 ^ 61) :
    ConsR C R m false (Tbl.empty : Tbl α (Idx k) δ) Tbl.empty := by
  have hT : ∀ t, TierR C.sch R C.hsM C.KP m t (Tbl.empty : Tbl α (Idx k) δ) := by
    intro t
    refine ⟨by simp [cntW, hz, Tbl.empty], by simp [Tbl.empty], by simp [Tbl.empty],
      fun i a h => by simp [Tbl.empty] at h, fun i a h => by simp [Tbl.empty] at h,
      fun a x h => by simp [Tbl.empty] at h, fun j _ => by simp [slotW, slotV, slotRd, hz],
      fun j _ h => by simp [slotW, slotV, slotRd, hz] at h, fun i hi => by simp [Tbl.empty] at hi⟩
  have hn : ∀ t, (knW C.sch.sa m t).toNat = 8 := fun t => by simp only [knW, hz]; decide
  have ho : ∀ t, (koW C.sch.sa m t).toNat = 0 := fun t => by simp only [koW, hz]; rfl
  have h0 := hsa 0
  have h1 := hsa 1
  simp only [consMinWords] at h0 h1
  have hG : GrowR C.sch m := by
    refine ⟨⟨h0.2, ?_, ?_, ?_, fun _ => UInt64.toNat_inj.mp (ho 0)⟩,
      ⟨h1.2, ?_, ?_, ?_, fun _ => UInt64.toNat_inj.mp (ho 1)⟩⟩
    all_goals (try rw [hn]); all_goals (try rw [ho])
    all_goals first | omega | (left; rfl) | (simp only [ConsSch.sch]; omega)
  exact ⟨⟨hctl, by simp [hz]⟩, by simp [hz], hT 0, hT 1, hG⟩

/-! ## The probe and the append, from the model -/

theorem probeC_ok (C : ConsSch) (m : Mem) (ks : List Word) (h t : Word)
    (hn : 0 < nSl C.sch m t) :
    ProbeOKG C.sch m t (C.mtM m (ks ++ [h]) t) C.exact (kwQ C ks h) (homeS C.sch m t h)
      (probeC C m ks h t) :=
  probe_homeG C.sch m t _ _ _ (cprobeW (m.arr64 (tierA C.sa t)) (C.mtM m (ks ++ [h]) t) C.exact (kwQ C ks h)
    (baseW m t) (knW C.sa m t) (krW C.sa m t)) (fun j d => by rw [cprobeW]; rfl) h hn

theorem wrRecK_eq (C : ConsSch) (t c : Word) :
    ∀ (vs : List Word) (m : Mem) (f : Word),
      wrRecK (tierA C.ra t) (c * C.w) m f vs = wrRec C.sch t c m f vs := by
  intro vs
  induction vs with
  | nil => intro m f; rfl
  | cons v vs ih =>
    intro m f
    simp only [wrRecK, wrRec, ih, Schema.ad, ConsSch.sch]

theorem pushMC_eq (C : ConsSch) (hS : C.sch.WF) (m : Mem) (t : Word)
    (vs : List Word) (j c q : Word) : pushMC C m t vs j c q = pushG C.sch m t vs j c q := by
  have hk : krW C.sa (wrRec C.sch t c m 0 vs) t = krW C.sa m t := by
    simp only [krW, koW]; rw [wrRec_arr_ne C.sch t c (tierA C.sa t) (hS.ra_sa' t t).symm]
  simp only [pushMC, tailM, pushG, wrRecK_eq, baseW]
  rw [wrRec_arr_ne C.sch t c CTL (hS.ra_ctl' t).symm]
  simp only [hk]
  rfl

/-- A column write keeps the relation. -/
theorem storeR_set64col (hW : C.WF) (hcR : ColFree C R) {A : ArrId} (hA : C.col = some A)
    (u kk x : Word) (h : StoreR C.sch R C.hsM C.KP m on P Q) :
    StoreR C.sch R C.hsM C.KP (m.set64 (tierA A u) kk x) on P Q := by
  obtain ⟨hra, hsa, hctl, hH⟩ := hW.col A hA
  have hS := hW.sch
  have hAl := hW.colLt A hA
  have ec : (m.set64 (tierA A u) kk x).arr64 CTL = m.arr64 CTL :=
    Mem.arr64_set64_ne _ _ _ _ _ (by simpa using tierA_ne (show CTL < 256 by decide) hAl (Ne.symm hctl) 0 u)
  have er : ∀ t, (m.set64 (tierA A u) kk x).arr64 (tierA C.sch.ra t) = m.arr64 (tierA C.sch.ra t) :=
    fun t => Mem.arr64_set64_ne _ _ _ _ _ (tierA_ne hS.ra_lt hAl (Ne.symm hra) t u)
  have es : ∀ t, (m.set64 (tierA A u) kk x).arr64 (tierA C.sch.sa t) = m.arr64 (tierA C.sch.sa t) :=
    fun t => Mem.arr64_set64_ne _ _ _ _ _ (tierA_ne hS.sa_lt hAl (Ne.symm hsa) t u)
  obtain ⟨⟨h1, h2⟩, hfl, hT0, hT1, hG⟩ := h
  have tier : ∀ t (tb : Tbl α (Idx k) δ), TierR C.sch R C.hsM C.KP m t tb →
      TierR C.sch R C.hsM C.KP (m.set64 (tierA A u) kk x) t tb := fun t tb hT =>
    tierR_mono C.sch R C.hsM C.KP m _ t tb (er t) (es t) (by simp only [cntW, ec])
      (by simp only [baseW, ec])
      (fun i a hr => hcR A hA m u kk x t i a hr) (fun i => hH m u kk x t i)
      (fun i K hK => C.kp_mono m _ t i (er t) (hH m u kk x t i) K hK) hT
  exact ⟨⟨by rw [ec]; exact h1, by rw [ec]; exact h2⟩, by rw [ec]; exact hfl, tier 0 P hT0,
    tier 1 Q hT1, growR_of_sa C.sch m _ es hG⟩

theorem storeR_colW (hW : C.WF) (hcR : ColFree C R) (t c x : Word)
    (h : StoreR C.sch R C.hsM C.KP m on P Q) : StoreR C.sch R C.hsM C.KP (colW C t c x m) on P Q := by
  unfold colW
  split
  · exact h
  · exact storeR_set64col hW hcR ‹_› _ _ _ h

/-! ## The query's obligations -/

/-- The record of node `c = cntW` of tier `t`: the words `vs` written, nothing else. -/
def newRecM (S : Schema) (m : Mem) (t : Word) (vs : List Word) : Mem := wrRec S t (cntW S m t) m 0 vs

/-- **The query's append obligation**: the record `vs` written as the new node of tier `t` holds
the key, with the query's hash. -/
def NewOKR (S : Schema) (R : Mem → Word → Word → α → Prop) (hs : Mem → Word → Word → Word)
    (m : Mem) (vs : List Word) (key : α) (qh : Word) : Prop :=
  ∀ t, t ≤ 1 → PushRoom S m t → (t = 0 → rdW (m.arr64 CTL) 1 = 0) →
    R (newRecM S m t vs) t (cntW S m t) key ∧
    hs (newRecM S m t vs) t (cntW S m t) = qh

/-- A field of the new record, or the old. -/
theorem fld_newRecM (S : Schema) (hS : S.WF) (m : Mem) (t : Word) (vs : List Word) (t' i f : Word)
    (ht : t ≤ 1) (hc : (cntW S m t).toNat < 2 ^ 27) (ht' : t' ≤ 1) (hi : i.toNat < 2 ^ 27)
    (hf : f < S.w) (hl : vs.length = S.w.toNat) :
    fld S (newRecM S m t vs) t' i f =
      if t' = t ∧ i = cntW S m t ∧ (S.ad (cntW S m t) f).toNat < (m.arr64 (tierA S.ra t)).size then
        vs.getD f.toNat 0
      else fld S m t' i f := by
  by_cases htt : t' = t
  · subst htt
    rw [fld, newRecM, wrRec_read S hS t' _ i f hc hi hf vs m 0 (by simp [hl])]
    simp only [fld, UInt64.toNat_zero, Nat.zero_le, true_and, Nat.sub_zero, Nat.zero_add, hl]
    grind
  · rw [fld, newRecM, wrRec_arr_ne S t _ _ (hS.ra_ne ht' ht htt)]
    simp [htt, fld]

/-- Two words below `2^32`, packed. -/
theorem pack_toNat (a b : Word) (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32) :
    (a ||| b <<< 32).toNat = a.toNat + 2 ^ 32 * b.toNat := by
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft]
  have h32 : (32 : Word).toNat % 64 = 32 := rfl
  rw [h32, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), Nat.or_comm, Nat.mul_comm,
    ← Nat.two_pow_add_eq_or_of_lt ha]
  omega

theorem pack_lo (a b : Word) (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32) :
    (a ||| b <<< 32) &&& 4294967295 = a := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, pack_toNat a b ha hb, show (4294967295 : Word).toNat = 2 ^ 32 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem pack_hi (a b : Word) (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32) :
    (a ||| b <<< 32) >>> 32 = b := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftRight, pack_toNat a b ha hb, show (32 : Word).toNat % 64 = 32 from rfl,
    Nat.shiftRight_eq_div_pow]
  omega

/-- The key words below `2^32` when their `|` has no bit from 32 on (`ciChk`). -/
theorem small_of_or (a b : Word) (h : (a ||| b) >>> 32 = 0) :
    a.toNat < 2 ^ 32 ∧ b.toNat < 2 ^ 32 := by
  have e := congrArg UInt64.toNat h
  rw [UInt64.toNat_shiftRight, show (32 : Word).toNat % 64 = 32 from rfl,
    Nat.shiftRight_eq_div_pow, UInt64.toNat_or] at e
  simp only [UInt64.toNat_zero] at e
  have h1 : a.toNat ≤ a.toNat ||| b.toNat := Nat.left_le_or
  have h2 : b.toNat ≤ a.toNat ||| b.toNat := Nat.right_le_or
  constructor <;> omega

theorem fieldsL_length (C : ConsSch) (m : Mem) (t i : Word) : (fieldsL C m t i).length = C.nk := by
  simp [fieldsL]

theorem list_two {α : Type} (ks : List α) (h : ks.length = 2) : ∃ a b, ks = [a, b] := by
  match ks, h with
  | [a, b], _ => exact ⟨a, b, rfl⟩

theorem list_one {α : Type} (ks : List α) (h : ks.length = 1) : ∃ a, ks = [a] := by
  match ks, h with
  | [a], _ => exact ⟨a, rfl⟩

theorem list_zero {α : Type} (ks : List α) (h : ks.length = 0) : ks = [] := by
  match ks, h with
  | [], _ => rfl

/-- The key words of a list of `nk` words. -/
theorem list_eq_range (ks : List Word) (n : Nat) (h : ks.length = n) :
    (List.range n).map (fun f => ks.getD f 0) = ks := by
  subst h
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- **The key word of an exact key with small words is injective.** -/
theorem kwQ_inj (C : ConsSch) (hE : ExactOK C) (hx : C.exact = true) (ks ks' : List Word)
    (hl : ks.length = C.nk) (hl' : ks'.length = C.nk)
    (hs : C.nk = 2 → (ks.getD 0 0).toNat < 2 ^ 32 ∧ (ks.getD 1 0).toNat < 2 ^ 32)
    (hs' : C.nk = 2 → (ks'.getD 0 0).toNat < 2 ^ 32 ∧ (ks'.getD 1 0).toNat < 2 ^ 32)
    (h : kwQ C ks 0 = kwQ C ks' 0) : ks = ks' := by
  have hn := hE.nk
  simp only [kwQ, hx, ↓reduceIte] at h
  rcases (by omega : C.nk = 0 ∨ C.nk = 1 ∨ C.nk = 2) with hn0 | hn1 | hn2
  · rw [hn0] at hl hl'; rw [List.length_eq_zero_iff.mp hl, List.length_eq_zero_iff.mp hl']
  · rw [hn1] at hl hl' h
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hl
    obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp hl'
    simp at h; rw [h]
  · rw [hn2] at hl hl' h
    obtain ⟨a1, a2⟩ := hs hn2
    obtain ⟨b1, b2⟩ := hs' hn2
    have h' : ks.getD 0 0 ||| ks.getD 1 0 <<< 32 = ks'.getD 0 0 ||| ks'.getD 1 0 <<< 32 := h
    have e1 := congrArg (fun x : Word => x &&& 4294967295) h'
    have e2 := congrArg (fun x : Word => x >>> 32) h'
    simp only [pack_lo _ _ a1 a2, pack_lo _ _ b1 b2] at e1
    simp only [pack_hi _ _ a1 a2, pack_hi _ _ b1 b2] at e2
    match ks, ks', hl, hl' with
    | [x, y], [x', y'], _, _ => simp at e1 e2; rw [e1, e2]

/-- A key's small words, from the key check `intern_X` passed. -/
theorem small_of_bigK (C : ConsSch) (ks : List Word) (h : ¬ bigK C ks) (hx : C.exact = true) :
    C.nk = 2 → (ks.getD 0 0).toNat < 2 ^ 32 ∧ (ks.getD 1 0).toNat < 2 ^ 32 := by
  intro hn
  simp only [bigK, hx, hn, true_and, Classical.not_not] at h
  exact small_of_or _ _ h

theorem fieldsL_getD (C : ConsSch) (m : Mem) (t i : Word) (f : Nat) (hf : f < C.nk) :
    (fieldsL C m t i).getD f 0 = kfld C m t i f := by
  simp [fieldsL, List.getD_eq_getElem?_getD, hf]

omit [BEq α] [Hashable α] in
/-- **The new record admits the query's key word**, and holds the key with the query's hash. -/
theorem newOK_of {C : ConsSch} (hW : C.WF) (hfr : RFrame C.sch R C.hsM) (m : Mem) (ks : List Word)
    (hks : ks.length = C.nk) (hbig : ¬ bigK C ks) (key : α)
    (h : NewOKR C.sch R C.hsM m (C.vsM (pushArgs C ks (C.qhM m ks))) key (C.qhM m ks)) :
    NewOK C.sch R C.hsM C.KP m (C.vsM (pushArgs C ks (C.qhM m ks))) key (C.qhM m ks)
      (kwQ C ks (C.qhM m ks)) := by
  have hS := hW.sch
  intro t j ht hroom ht0
  obtain ⟨h1, h2⟩ := h t ht hroom ht0
  have hra := hS.ra_ctl
  have hrs := hS.ra_sa
  have hca := hS.ca
  generalize hvs : C.vsM (pushArgs C ks (C.qhM m ks)) = vs at h1 h2
  have hl : vs.length = C.sch.w.toNat := by rw [← hvs]; exact hW.vs ks _ hks
  have hout : OutEq C.sch (newRecM C.sch m t vs)
      (pushG C.sch m t vs j (cntW C.sch m t) (kwQ C ks (C.qhM m ks))) := by
    refine ⟨fun b h1 h1' h2 h2' h3 => ?_, ?_⟩
    · have hb : b ≠ tierA C.sch.sa t := fun e => by
        rcases tierA_cases' C.sch.sa t with e' | e' <;> rw [e'] at e <;> contradiction
      simp only [pushG, newRecM, Mem.arr64_set64_ne _ _ _ _ _ hb, Mem.arr64_set64_ne _ _ _ _ _ h3]
    · simp only [pushG, newRecM]
      rw [rdW_set64, Mem.arr64_set64_ne _ _ _ _ _ (hS.sa_ctl' t).symm,
        Mem.arr64_set64_ne _ _ _ _ _ (hS.sa_ctl' t).symm]
      have : C.sch.ca + (t &&& 1) ≠ 0 := by
        rcases word_le_one t ht with rfl | rfl
        · intro e; have := congrArg UInt64.toNat e; simp at this; omega
        · intro e; have := congrArg UInt64.toNat e
          simp [UInt64.toNat_add] at this; omega
      simp [this]
  have hfl : ∀ f, f < C.sch.w →
      fld C.sch (pushG C.sch m t vs j (cntW C.sch m t) (kwQ C ks (C.qhM m ks))) t (cntW C.sch m t) f =
      fld C.sch (newRecM C.sch m t vs) t (cntW C.sch m t) f := by
    intro f _
    simp only [fld, pushG, newRecM, Mem.arr64_set64_ne _ _ _ _ _ (hS.ra_ctl' t),
      Mem.arr64_set64_ne _ _ _ _ _ (hS.ra_sa' t t)]
  obtain ⟨e1, e2⟩ := hfr _ _ t (cntW C.sch m t) hout hfl
  refine ⟨e1 key h1, by rw [e2]; exact h2, ?_⟩
  unfold ConsSch.KP
  cases hx : C.exact
  · have ek : kwQ C ks (C.qhM m ks) = C.qhM m ks := by simp [kwQ, hx]
    rw [ek] at e2
    simp only [Bool.false_eq_true, ↓reduceIte, ek]; rw [e2, h2]
  · have hE := hW.ex hx
    have hw := hS.w_le
    have hnk := hE.nk
    have hsm := small_of_bigK C ks hbig hx
    -- the new node's record words that hold the key are the key's (`recK`)
    have hfk : ∀ g : Nat, g < nkW C →
        fld C.sch (pushG C.sch m t vs j (cntW C.sch m t) (kwQ C ks (C.qhM m ks))) t
          (cntW C.sch m t) (UInt64.ofNat g) = (recK C ks).getD g 0 := by
      intro g hg
      have hnkW : nkW C ≤ 2 := by unfold nkW; split <;> omega
      have hfw : UInt64.ofNat g < C.sch.w := by
        rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)]
        have := hE.nkw; simp only [ConsSch.sch] at hw ⊢; omega
      rw [hfl _ hfw, fld_newRecM C.sch hS m t vs t _ _ ht hroom.1 ht hroom.1 hfw hl]
      have hfn : (UInt64.ofNat g).toNat = g :=
        UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)
      have had : (C.sch.ad (cntW C.sch m t) (UInt64.ofNat g)).toNat <
          (m.arr64 (tierA C.sch.ra t)).size := by
        have hr2 := hroom.2
        rw [C.sch.ad_toNat hS _ _ hroom.1 hfw, hfn]
        have hwf : g < C.sch.w.toNat := by have := UInt64.lt_iff_toNat_lt.mp hfw; rwa [hfn] at this
        have : (cntW C.sch m t).toNat * C.sch.w.toNat + g <
            C.sch.w.toNat * ((cntW C.sch m t).toNat + 1) := by
          rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm C.sch.w.toNat]; omega
        omega
      simp only [had, and_self, ↓reduceIte, hfn]
      rw [← hvs]; exact hE.vs ks _ hks g hg
    -- the new node's key words are the key
    have hfk' : ∀ f : Nat, f < C.nk →
        kfld C (pushG C.sch m t vs j (cntW C.sch m t) (kwQ C ks (C.qhM m ks))) t
          (cntW C.sch m t) f = ks.getD f 0 := by
      intro f hf
      unfold kfld
      cases hp : C.kpk
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hfk f (by simp [nkW, hp, hf])]; simp [recK, hp]
      · have h2 := hE.kpk hp
        obtain ⟨s1, s2⟩ := hsm h2
        have h0 : fld C.sch (pushG C.sch m t vs j (cntW C.sch m t) (kwQ C ks (C.qhM m ks))) t
            (cntW C.sch m t) 0 = (recK C ks).getD 0 0 := hfk 0 (by simp [nkW, hp])
        simp only [↓reduceIte]
        rw [h0]
        simp only [recK, hp, ↓reduceIte, kwQ, hx, h2, List.getD_cons_zero]
        rcases (by omega : f = 0 ∨ f = 1) with rfl | rfl
        · simp only [↓reduceIte]; rw [pack_lo _ _ s1 s2]
        · simp only [Nat.one_ne_zero, ↓reduceIte]; rw [pack_hi _ _ s1 s2]
    have hfL : fieldsL C (pushG C.sch m t vs j (cntW C.sch m t) (kwQ C ks (C.qhM m ks))) t
        (cntW C.sch m t) = ks := by
      refine Eq.trans ?_ (list_eq_range ks C.nk hks)
      unfold fieldsL
      apply List.map_congr_left; intro f hf; exact hfk' f (List.mem_range.mp hf)
    simp only [↓reduceIte]
    refine ⟨?_, fun h2 f hf2 => ?_⟩
    · rw [hfL]; simp only [kwQ, hx, ↓reduceIte]
    · rw [hfk' f (by omega)]
      obtain ⟨s1, s2⟩ := hsm h2
      rcases (by omega : f = 0 ∨ f = 1) with rfl | rfl
      · exact s1
      · exact s2

/-- **The obligations of a query** `ks` for the arena key `key` in memory `m`: the key has `nk`
words, the match is key equality on the table's nodes, a matching node has the query's hash, and
the new record holds the key with that hash. -/
structure ConsKeyOK (C : ConsSch) (R : Mem → Word → Word → α → Prop) (m : Mem) (ks : List Word)
    (key : α) : Prop where
  hlen : ks.length = C.nk
  match_ : MatchOK R (C.mtM m (ks ++ [C.qhM m ks])) m key
  home : HomeOK C.hsM (C.mtM m (ks ++ [C.qhM m ks])) m (C.qhM m ks)
  new : NewOKR C.sch R C.hsM m (C.vsM (pushArgs C ks (C.qhM m ks))) key (C.qhM m ks)

omit [BEq α] [Hashable α] in
/-- **The query's key word** `kwQ`: on a matching node, the admissible key word is the query's;
an exact table's node with the query's key word matches. -/
theorem qkey_of {C : ConsSch} (hW : C.WF) {m : Mem} {ks : List Word} {key : α}
    (hK : ConsKeyOK C R m ks key) (hbig : ¬ bigK C ks) :
    QKeyOK C.KP (C.mtM m (ks ++ [C.qhM m ks])) m C.exact (kwQ C ks (C.qhM m ks)) := by
  intro t i K hKP
  unfold ConsSch.KP at hKP
  cases hx : C.exact
  · simp only [hx, Bool.false_eq_true, ↓reduceIte] at hKP
    refine ⟨fun hm => ?_, fun h => absurd h (by simp)⟩
    rw [hKP, hK.home t i hm]; simp [kwQ, hx]
  · have hE := hW.ex hx
    simp only [hx, ↓reduceIte] at hKP
    obtain ⟨hk1, hk2⟩ := hKP
    refine ⟨fun hm => ?_, fun _ hq => ?_⟩
    · have := (hE.mt m ks _ t i hK.hlen).mp hm
      rw [hk1, this]; simp only [kwQ, hx, ↓reduceIte]
    · apply (hE.mt m ks _ t i hK.hlen).mpr
      refine kwQ_inj C hE hx _ _ (fieldsL_length C m t i) hK.hlen ?_ (small_of_bigK C ks hbig hx) ?_
      · intro hn2
        rw [fieldsL_getD C m t i 0 (by omega), fieldsL_getD C m t i 1 (by omega)]
        exact ⟨hk2 hn2 0 (by omega), hk2 hn2 1 (by omega)⟩
      · rw [← hk1, hq]; simp only [kwQ, hx, ↓reduceIte]

/-- **The growth's hash of an admissible key word is the node's hash.** -/
theorem ghC_kp {C : ConsSch} (hW : C.WF) (m mi : Mem) (t i K : Word) (hK : C.KP m t i K) :
    ghC C mi K = C.hsM m t i := by
  unfold ConsSch.KP at hK
  unfold ghC
  cases hx : C.exact
  · simp only [hx, Bool.false_eq_true, ↓reduceIte] at hK ⊢; exact hK
  · have hE := hW.ex hx
    simp only [hx, ↓reduceIte] at hK ⊢
    obtain ⟨hk1, hk2⟩ := hK
    rw [hE.hs m t i, hE.qh mi m]
    congr 1
    rw [hk1]
    have hn := hE.nk
    rcases (by omega : C.nk = 0 ∨ C.nk = 1 ∨ C.nk = 2) with hn0 | hn1 | hn2
    · simp [fieldsL, kwQ, hx, hn0, unpackK]
    · simp [fieldsL, kwQ, hx, hn1, unpackK]
    · have e : fieldsL C m t i = [kfld C m t i 0, kfld C m t i 1] := by
        simp [fieldsL, hn2, List.range_succ]
      have s0 : (kfld C m t i 0).toNat < 2 ^ 32 := hk2 hn2 0 (by omega)
      have s1 : (kfld C m t i 1).toNat < 2 ^ 32 := hk2 hn2 1 (by omega)
      rw [e]
      simp only [kwQ, hx, hn2, ↓reduceIte, unpackK, List.getD_cons_zero, List.getD_cons_succ]
      rw [pack_lo _ _ s0 s1, pack_hi _ _ s0 s1]

/-! ## An interning -/

/-- A column's tier arrays are not `b` when neither of the column's ids is. -/
theorem col_tier_ne {C : ConsSch} {b : ArrId}
    (hcol : ∀ A, C.col = some A → A ≠ b ∧ A + 256 ≠ b) (t : Word) :
    ∀ A, C.col = some A → tierA A t ≠ b := fun A hA e => by
  rcases tierA_cases' A t with e' | e' <;> rw [e'] at e
  · exact (hcol A hA).1 e
  · exact (hcol A hA).2 e

/-- Outside the table's records (both tiers), counts and column, `pushRec` is the old memory. -/
theorem pushRec_arr (C : ConsSch) (m : Mem) (t : Word) (ks : List Word) (b : ArrId)
    (hb : b ≠ C.ra) (hb' : b ≠ C.ra + 256) (hc : b ≠ CTL)
    (hcol : ∀ A, C.col = some A → A ≠ b ∧ A + 256 ≠ b) :
    (pushRec C m t ks).arr64 b = m.arr64 b := by
  have hbt : b ≠ tierA C.ra t := fun e => by
    rcases tierA_cases' C.ra t with e' | e' <;> rw [e'] at e <;> contradiction
  rw [pushRec, colW_arr C _ _ _ _ b (col_tier_ne hcol t), Mem.arr64_set64_ne _ _ _ _ _ hc, wrRecK_eq,
    wrRec_arr_ne C.sch _ _ b hbt]

/-- **The column after the append**: the new node's word at `c` of tier `t`'s column array. -/
theorem pushRec_col (C : ConsSch) (hW : C.WF) {A : ArrId} (hA : C.col = some A) (m : Mem)
    (t : Word) (ks : List Word) :
    (pushRec C m t ks).arr64 (tierA A t) = (m.arr64 (tierA A t)).set! (cntC C m t).toNat
      (C.colM m (pushArgs C ks (C.qhM m ks))) := by
  obtain ⟨hra, -, hc, -⟩ := hW.col A hA
  have hAl := hW.colLt A hA
  simp only [pushRec, colW, hA, Mem.arr64_set64_same]
  rw [Mem.arr64_set64_ne _ _ _ _ _ (by simpa using tierA_ne hAl (show CTL < 256 by decide) hc t 0),
    wrRecK_eq, wrRec_arr_ne C.sch _ _ _ (tierA_ne hAl hW.sch.ra_lt hra t t)]

/-- **The counts after the append**: tier `t`'s up by one. -/
theorem pushRec_cnt (C : ConsSch) (hW : C.WF) (m : Mem) (t : Word) (ht : t ≤ 1) (ks : List Word)
    (hctl : C.ca.toNat + 2 ≤ (m.arr64 CTL).size) (t' : Word) (ht' : t' ≤ 1) :
    cntC C (pushRec C m t ks) t' = if t' = t then cntC C m t + 1 else cntC C m t' := by
  have hcol : ∀ A, C.col = some A → A ≠ CTL ∧ A + 256 ≠ CTL := fun A hA =>
    ⟨(hW.col A hA).2.2.1, by simp [CTL]⟩
  have hca := hW.sch.ca
  simp only [ConsSch.sch] at hca
  simp only [cntC, pushRec, colW_arr C _ _ _ _ CTL (col_tier_ne hcol t), rdW_set64, wrRecK_eq,
    wrRec_arr_ne C.sch _ _ CTL (hW.sch.ra_ctl' t).symm]
  rcases word_le_one t ht with rfl | rfl <;> rcases word_le_one t' ht' with rfl | rfl <;>
    simp [UInt64.toNat_add] <;> first | omega | (intro h; have := congrArg UInt64.toNat h; simp [UInt64.toNat_add] at this; omega)

/-- **An interning hits** (the memory is unchanged) **or appends** node `cntC` to tier `t`: the
handle is the tier's base plus the count, and outside tier `t`'s slot array the memory is
`pushRec`. -/
theorem consInternM_out (hW : C.WF) {ks : List Word} {w : Word} {m' : Mem}
    (h : consInternM C m ks = some (w, m')) :
    m' = m ∨ ∃ t, t ≤ 1 ∧ pushOKC C m t = true ∧ w = (if t = 0 then C.P else C.S) + cntC C m t ∧
      (∀ b, b ≠ tierA C.sa t → m'.arr64 b = (pushRec C m t ks).arr64 b) ∧
      (∀ b, (m'.arr64 b).size = (m.arr64 b).size) ∧ m'.words.size = m.words.size :=
  consInternM_outA hW.sch.sa_ctl (fun A hA => (hW.col A hA).2.1) ⟨hW.sch.sa_lt, hW.colLt⟩ h

/-- The arrays an interning of `C` writes: both tiers of its record and slot arrays and of its
column. -/
def ConsSch.wset (C : ConsSch) : List ArrId :=
  C.ra :: (C.ra + 256) :: C.sa :: (C.sa + 256) :: (C.col.toList ++ C.col.toList.map (· + 256))

/-- **What an interning writes**: the table's arrays and column (both tiers), its two counts. -/
theorem consInternM_frame (hW : C.WF) {ks : List Word} {w : Word} {m' : Mem}
    (h : consInternM C m ks = some (w, m')) :
    MemFrame C.wset [C.ca, C.ca + 1] m m' := by
  rcases consInternM_out hW h with rfl | ⟨t, ht, -, -, he, hs, hw⟩
  · exact MemFrame.refl _ _ _
  refine ⟨fun b hb hc => ?_, fun x hx => ?_, hs, hw⟩
  · simp only [ConsSch.wset, List.mem_cons, List.mem_append, List.mem_map, not_or] at hb
    have hbs : b ≠ tierA C.sa t := fun e => by
      rcases tierA_cases' C.sa t with e' | e' <;> rw [e'] at e
      · exact hb.2.2.1 e
      · exact hb.2.2.2.1 e
    rw [he b hbs]
    refine pushRec_arr C m t ks b hb.1 hb.2.1 hc (fun A hA => ⟨fun e => ?_, fun e => ?_⟩)
    · exact hb.2.2.2.2.1 (by simp [hA, e])
    · exact hb.2.2.2.2.2 ⟨A, by simp [hA], e⟩
  · have hcol : ∀ A, C.col = some A → A ≠ CTL ∧ A + 256 ≠ CTL := fun A hA =>
      ⟨(hW.col A hA).2.2.1, by simp [CTL]⟩
    rw [he CTL (hW.sch.sa_ctl' t).symm, pushRec, colW_arr C _ _ _ _ CTL (col_tier_ne hcol t), rdW_set64,
      wrRecK_eq, wrRec_arr_ne C.sch _ _ CTL (hW.sch.ra_ctl' t).symm]
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
  have hn0 : 0 < nSl C.sch m t := UInt64.lt_iff_toNat_lt.mpr (by
    have := (lay C.sch m hR.2.2.2.2 t ht).1; simp; omega)
  obtain ⟨-, hs2, hs3, hj⟩ := ((probeC_ok C m ks h t hn0) hr).1 hh
  obtain ⟨hc, hcap, -, -, -, -, ⟨hsl, -, -⟩⟩ := hR.tier t ht
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
  have hkf := hW.kframe
  obtain ⟨⟨hctl, hb⟩, hflag, hT0, hT1, hG⟩ := id hR
  simp only [consInternM, pushC] at hI
  split at hI
  · simp at hI
  rename_i hbig
  simp only [kwP_pushArgs C m ks hK.hlen] at hI
  have hQ := qkey_of hW hK hbig
  have hN := newOK_of hW hfr m ks hK.hlen hbig key hK.new
  have hl := hW.vs ks (C.qhM m ks) hK.hlen
  have hnz : ∀ t, t ≤ 1 → 0 < nSl C.sch m t := fun t ht =>
    UInt64.lt_iff_toNat_lt.mpr (by have := (lay C.sch m hG t ht).1; simp; omega)
  have hP0 := probeC_ok C m ks (C.qhM m ks) 0 (hnz 0 (by decide))
  have hP1 := probeC_ok C m ks (C.qhM m ks) 1 (hnz 1 (by decide))
  have hit0 := tierR_hit C.sch R C.hsM C.KP m 0 _ hT0 _ key hK.match_ _ _ hQ _ _ hP0
  have hit1 := tierR_hit C.sch R C.hsM C.KP m 1 _ hT1 _ key hK.match_ _ _ hQ _ _ hP1
  have miss0 := tierR_miss C.sch R C.hsM C.KP m 0 _ hT0 _ key hK.match_ _ _ hQ _ hK.home _ hP0
  have miss1 := tierR_miss C.sch R C.hsM C.KP m 1 _ hT1 _ key hK.match_ _ _ hQ _ hK.home _ hP1
  have e0 := hW.base 0 (by decide)
  have e1 := hW.base 1 (by decide)
  simp only [↓reduceIte, show (1 : Word) ≠ 0 by decide] at e0 e1
  have hL := L.on_setP
  have htag : C.sch.tag = C.tag := rfl
  -- the append to tier `t` at slot `j`, then the column, then the growth
  have push : ∀ t, t ≤ 1 → ∀ (j : Word) (P' Q' : Tbl α (Idx k) δ) (m₂ : Mem),
      StoreR C.sch R C.hsM C.KP (pushG C.sch m t (C.vsM (pushArgs C ks (C.qhM m ks))) j (cntC C m t)
        (kwQ C ks (C.qhM m ks))) (L.on a) P' Q' →
      kgrowIf C t m (pushMX C m t (C.vsM (pushArgs C ks (C.qhM m ks)))
        (C.colM m (pushArgs C ks (C.qhM m ks))) j (cntC C m t) (kwQ C ks (C.qhM m ks)))
        (cntC C m t) = some m₂ →
      StoreR C.sch R C.hsM C.KP m₂ (L.on a) P' Q' := by
    intro t ht j P' Q' m₂ hX hg
    rw [pushMX, pushMC_eq C hS] at hg
    have hX' := storeR_colW hW hcR t (cntC C m t) (C.colM m (pushArgs C ks (C.qhM m ks))) hX
    unfold kgrowIf at hg
    split at hg
    · exact storeR_kgrow C.sch R C.hsM C.KP hS hfr hkf (ghC C) _ m₂ t ht
        (fun mi _ i K hK => ghC_kp hW _ mi t i K hK) _ _ _ hX' hg
    · cases hg; exact hX'
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
        have hp1 := tierR_push C.sch R C.hsM C.KP hS hfr hkf m 1 (by decide) _ hT1 _ key hK.match_ _ _
          hQ _ hK.home _ hP1 hn1 hz1 hroom hctl hb _ hl hN (fun h => absurd h (by decide)) d hG
        have hj : (probeC C m ks (C.qhM m ks) 1).tail.tail.headD 0 < nSl C.sch m 1 :=
          ((hP1 hn1).2 hz1).2.1
        rw [hst, hres, L.on_setS, L.getP_setS, L.getS_setS]
        refine ⟨hok, push 1 (by decide) _ _ _ m₂ ?_ hg, by rw [e1]⟩
        refine storeR_push C.sch R C.hsM C.KP hS m 1 (by decide) _ _ _ hj _ _ _ _ _ hR ?_ hp1
        exact tierR_other C.sch R C.hsM C.KP hS hfr hkf m 1 0 (by decide) (by decide) (by decide) _
          hT0 hroom hb _ hl _ _ hG hj
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
      have hp0 := tierR_push C.sch R C.hsM C.KP hS hfr hkf m 0 (by decide) _ hT0 _ key hK.match_ _ _
        hQ _ hK.home _ hP0 hn0' hz0 hroom hctl hb _ hl hN (fun _ => by simpa using hfl) d hG
      have hj : (probeC C m ks (C.qhM m ks) 0).tail.tail.headD 0 < nSl C.sch m 0 :=
        ((hP0 hn0').2 hz0).2.1
      rw [hst, hres, L.on_setP, L.getP_setP, L.getS_setP]
      refine ⟨hok, push 0 (by decide) _ _ _ m₂ ?_ hg, by rw [e0]⟩
      refine storeR_push C.sch R C.hsM C.KP hS m 0 (by decide) _ _ _ hj _ _ _ _ _ hR hp0 ?_
      exact tierR_other C.sch R C.hsM C.KP hS hfr hkf m 0 1 (by decide) (by decide) (by decide) _
        hT1 hroom hb _ hl _ _ hG hj
    · simp at hI
  · simp at hI

end rel


-- The relation is opaque outside the library: the lemmas above are its interface.
attribute [irreducible] ConsR

end L.Arena
