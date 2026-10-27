import ConAgua.Arena.StoreRel
import ConAgua.Arena.SlotGrowSpec
import ConAgua.L.WriteSet
import ConAgua.Arena.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The store library: one relation for every open-addressing node table

con-ron's arena keeps each node constructor in a `Tbl α ι δ` per tier (records, derived words, a
cons `Std.HashMap`). Its L twin (the cons-table library, `ConsLib.lean`) is the same for every
constructor up to a **record schema** (`Schema`): a word array of records, `w` words per node and
tier, the two tiers interleaved (node `i` of tier `t` at `ra[i * st + t * w ..]`, `st = 2 w`); a word
array of slots (KSTP: one table per tier, its slot count and offset in words `2 t`, `2 t + 1`;
slot `j` the value word `r + 2 j`, `0` free or `B t + i + 1` node `i`, and the key word after it;
linear probing from `homeW`); the node count of tier `t` at `CTL[ca + t]`; the handle tag.

This file states the relation and proves the representation facts once, for any schema:

* **Reads and the append**: `fld`, `slotW`, `slotK`, `nSl`, `cntW`; the layout `GrowR` and its
  arithmetic (`lay`, `kslot_toNat`, `kslot_eq_iff`); `pushG` (the memory after an append) and one
  read equation per array.
* **The probe**: `ProbeOKG` for any match function and key word, from the probe's unfolding
  (`probe_homeG`).
* **The relation** `TierR` (one tier) and `StoreR` (two tiers, the scratch flag, the layout),
  parametric in the record relation `R`, the node hash `hs` and the key-word predicate `KP`
  (which key words a slot of node `i` may hold); `tierR_hit`, `tierR_miss`, `tierR_push`,
  `tierR_other`.
* **The arena protocol**: `protoRun`, the run of the arena's hash-consing, over a `Lens` on the
  two tables.

The growth is `StoreGrow.lean`'s. A table instance (`ConsLibRel.lean`) supplies the schema, its
record relation and hash, frame lemmas (`RFrame`, `KFrame`), and for each query the match facts
(`MatchOK`, `HomeOK`, `QKeyOK`) and the new record (`NewOK`).

**Parametric strides.** `grind` decides the address disequalities when strides are numerals
(`i * 8 + t * 4 + f`), not when they are variables (nonlinear). `Schema.ad_inj` (by hand, once)
is the one fact the generic proofs need; given it, `grind` does the rest.
-/

open ConRon.Arena


namespace L.Arena

/-! ## Schemas and addresses -/

/-- A record schema: the record array, the slot array (both tiered: tier `t` is `tierA ra t`,
`tierA sa t`), the words per record `w`, the `CTL` index of tier 0's node count, the handle
tag. -/
structure Schema where
  ra : ArrId
  sa : ArrId
  w : Word
  ca : Word
  tag : UInt32

/-- What the generic lemmas need of a schema. -/
structure Schema.WF (S : Schema) : Prop where
  w_le : S.w.toNat ≤ 256
  ca : 2 ≤ S.ca.toNat ∧ S.ca.toNat < 2 ^ 32
  ra_lt : S.ra < 256
  sa_lt : S.sa < 256
  ra_sa : S.ra ≠ S.sa
  ra_ctl : S.ra ≠ CTL
  sa_ctl : S.sa ≠ CTL
  tag : S.tag.toNat < 16
  scb : S.ca ≠ SCB ∧ S.ca + 1 ≠ SCB ∧ S.ca ≠ 1 ∧ S.ca + 1 ≠ 1

/-- The address of word `f` of node `i` (in its tier's record array). -/
def Schema.ad (S : Schema) (i f : Word) : Word := i * S.w + f

theorem Schema.ad_toNat (S : Schema) (hS : S.WF) (i f : Word)
    (hi : i.toNat < 2 ^ 27) (hf : f < S.w) :
    (S.ad i f).toNat = i.toNat * S.w.toNat + f.toNat := by
  have h2 := hS.w_le
  have : f.toNat < S.w.toNat := by grind
  have a1 : i.toNat * S.w.toNat ≤ 2 ^ 27 * 256 := Nat.mul_le_mul (by omega) (by omega)
  simp only [Schema.ad, UInt64.toNat_add, UInt64.toNat_mul]
  rw [Nat.mod_eq_of_lt (a := i.toNat * S.w.toNat) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- **Addresses are injective** on the fields of a schema: the fact `grind` cannot find itself
when the stride is a variable. -/
theorem Schema.ad_inj (S : Schema) (hS : S.WF) (i f i' f' : Word)
    (hi : i.toNat < 2 ^ 27) (hf : f < S.w) (hi' : i'.toNat < 2 ^ 27)
    (hf' : f' < S.w) (h : S.ad i f = S.ad i' f') : i = i' ∧ f = f' := by
  have e := congrArg UInt64.toNat h
  rw [S.ad_toNat hS i f hi hf, S.ad_toNat hS i' f' hi' hf'] at e
  have hf1 : f.toNat < S.w.toNat := by grind
  have hf2 : f'.toNat < S.w.toNat := by grind
  have q := congrArg (· / S.w.toNat) e
  simp only [Nat.mul_comm _ S.w.toNat, Nat.mul_add_div (show 0 < S.w.toNat by omega),
    Nat.div_eq_of_lt hf1, Nat.div_eq_of_lt hf2, Nat.add_zero] at q
  have hA : i.toNat * S.w.toNat = i'.toNat * S.w.toNat := by rw [q]
  refine ⟨UInt64.toNat_inj.mp q, UInt64.toNat_inj.mp (by omega)⟩

/-- The two tiers' arrays of a schema and `CTL` are pairwise different. -/
theorem Schema.WF.ra_ne {S : Schema} (_hS : Schema.WF S) {t t' : Word} (ht : t ≤ 1) (ht' : t' ≤ 1) (h : t ≠ t') :
    tierA S.ra t ≠ tierA S.ra t' := tierA_ne_tier _ ht ht' h

theorem Schema.WF.ra_sa' {S : Schema} (hS : Schema.WF S) (t t' : Word) : tierA S.ra t ≠ tierA S.sa t' :=
  tierA_ne hS.ra_lt hS.sa_lt hS.ra_sa t t'

theorem Schema.WF.ra_ctl' {S : Schema} (hS : Schema.WF S) (t : Word) : tierA S.ra t ≠ CTL := by
  have := tierA_ne hS.ra_lt (show CTL < 256 by decide) hS.ra_ctl t 0
  simpa using this

theorem Schema.WF.sa_ctl' {S : Schema} (hS : Schema.WF S) (t : Word) : tierA S.sa t ≠ CTL := by
  have := tierA_ne hS.sa_lt (show CTL < 256 by decide) hS.sa_ctl t 0
  simpa using this

/-! ## Reads -/

section reads
variable (S : Schema) (m : Mem)

/-- Word `f` of node `i` of tier `t`. -/
def fld (t i f : Word) : Word := rdW (m.arr64 (tierA S.ra t)) (S.ad i f)
/-- Slot `j` of tier `t`'s table, against the tier's slot base (`slotV`, `baseW`): `0` free,
`i + 1` node `i`. -/
def slotW (t j : Word) : Word := slotV (m.arr64 (tierA S.sa t)) (baseW m t) (krW S.sa m t + j * 2)
/-- The key word of slot `j` of tier `t`. -/
def slotK (t j : Word) : Word := rdW (m.arr64 (tierA S.sa t)) (krW S.sa m t + j * 2 + 1)
/-- The slot count of tier `t` (its count word plus `SN0`). -/
def nSl (t : Word) : Word := knW S.sa m t
/-- The node count of tier `t`. -/
def cntW (t : Word) : Word := rdW (m.arr64 CTL) (S.ca + t)
/-- The home slot of a hash in tier `t`. -/
def homeS (t h : Word) : Word := homeW h (nSl S m t)

/-- The room an append needs: a handle index and a record. -/
def PushRoom (t : Word) : Prop :=
  (cntW S m t).toNat < 2 ^ 27 ∧ S.w.toNat * ((cntW S m t).toNat + 1) ≤ (m.arr64 (tierA S.ra t)).size

/-- **Tier `t`'s table in its slot array**: the array below `2^61` words (so the growth's
addresses do not wrap), a multiple of 8 slots (at least 8), from word `2 + o` on (`o` the
offset word; the growth doubles the table where it is). Tier 0's offset is `0` (the offset word is
never written: zero at the start, kept by the append and the growth), so its table sits at word 2
(the truncation of a frozen table, `FreezeTruncStore.lean`). -/
def TierLay (t : Word) : Prop :=
  (m.arr64 (tierA S.sa t)).size < 2 ^ 61 ∧
  8 ≤ (knW S.sa m t).toNat ∧ (knW S.sa m t).toNat % 8 = 0 ∧
  2 + (koW S.sa m t).toNat + 2 * (knW S.sa m t).toNat ≤ (m.arr64 (tierA S.sa t)).size ∧
  (t = 0 → koW S.sa m t = 0)

/-- **The slot arrays' layout**: both tiers' tables in place. -/
def GrowR : Prop := TierLay S m 0 ∧ TierLay S m 1

end reads

attribute [store_grind] homeS

/-! ## The layout, as numbers -/

theorem le_one_cases (t : Word) (h : t ≤ 1) : t = 0 ∨ t = 1 := by
  have := UInt64.le_iff_toNat_le.mp h
  have h1 : t.toNat = 0 ∨ t.toNat = 1 := by simp at this; omega
  rcases h1 with h1 | h1
  · exact .inl (UInt64.toNat_inj.mp (by simpa using h1))
  · exact .inr (UInt64.toNat_inj.mp (by simpa using h1))

section lay
variable (S : Schema) (m : Mem)

theorem GrowR.tier (hG : GrowR S m) (t : Word) (ht : t ≤ 1) : TierLay S m t := by
  rcases le_one_cases t ht with rfl | rfl
  · exact hG.1
  · exact hG.2

theorem knW_toNat (hG : GrowR S m) (t : Word) (ht : t ≤ 1) :
    (knW S.sa m t).toNat < 2 ^ 60 ∧ (koW S.sa m t).toNat < 2 ^ 61 := by
  have := hG.tier S m t ht
  obtain ⟨a0, -, -, a4, -⟩ := this
  omega

/-- **Tier `t`'s table, as numbers**: at least 8 slots, from word `r ≥ 2`, inside its array. -/
theorem lay (hG : GrowR S m) (t : Word) (ht : t ≤ 1) :
    8 ≤ (nSl S m t).toNat ∧ 2 ≤ (krW S.sa m t).toNat ∧
    (krW S.sa m t).toNat + 2 * (nSl S m t).toNat ≤ (m.arr64 (tierA S.sa t)).size := by
  obtain ⟨a0, a1, -, a4, -⟩ := hG.tier S m t ht
  have e : (krW S.sa m t).toNat = (koW S.sa m t).toNat + 2 := by
    simp only [krW]; rw [UInt64.toNat_add]; simp; omega
  simp only [nSl, e]
  refine ⟨a1, by omega, by omega⟩

/-- A slot's two words, as numbers. -/
theorem kslot_toNat (hG : GrowR S m) (t : Word) (ht : t ≤ 1) (j : Word) (hj : j < nSl S m t) :
    (krW S.sa m t + j * 2).toNat = (krW S.sa m t).toNat + 2 * j.toNat ∧
    (krW S.sa m t + j * 2 + 1).toNat = (krW S.sa m t).toNat + 2 * j.toNat + 1 := by
  obtain ⟨-, -, l3⟩ := lay S m hG t ht
  have hs := (hG.tier S m t ht).1
  have hj' := UInt64.lt_iff_toNat_lt.mp hj
  have e1 : (krW S.sa m t + j * 2).toNat = (krW S.sa m t).toNat + 2 * j.toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_mul]; simp; omega
  refine ⟨e1, ?_⟩
  rw [UInt64.toNat_add, e1]; simp; omega

/-- One tier's slots are at different words. -/
theorem kslot_eq_iff (hG : GrowR S m) (t : Word) (ht : t ≤ 1) (j j' : Word)
    (hj : j < nSl S m t) (hj' : j' < nSl S m t) :
    (krW S.sa m t + j * 2 = krW S.sa m t + j' * 2) ↔ j = j' := by
  constructor
  · intro h
    have e := congrArg UInt64.toNat h
    rw [(kslot_toNat S m hG t ht j hj).1, (kslot_toNat S m hG t ht j' hj').1] at e
    exact UInt64.toNat_inj.mp (by omega)
  · rintro rfl; rfl

theorem kslot1_eq_iff (hG : GrowR S m) (t : Word) (ht : t ≤ 1) (j j' : Word)
    (hj : j < nSl S m t) (hj' : j' < nSl S m t) :
    (krW S.sa m t + j * 2 + 1 = krW S.sa m t + j' * 2 + 1) ↔ j = j' := by
  rw [← kslot_eq_iff S m hG t ht j j' hj hj']
  constructor
  · intro h; have := congrArg (· - 1) h; simpa using this
  · intro h; rw [h]

theorem kslot1_ne (hG : GrowR S m) (t : Word) (ht : t ≤ 1) (j j' : Word)
    (hj : j < nSl S m t) (hj' : j' < nSl S m t) :
    krW S.sa m t + j * 2 + 1 ≠ krW S.sa m t + j' * 2 := by
  intro h
  have e := congrArg UInt64.toNat h
  rw [(kslot_toNat S m hG t ht j hj).2, (kslot_toNat S m hG t ht j' hj').1] at e
  omega

/-- Slots are not the count and offset words (`0`, `1`). -/
theorem kslot_ne_meta (hG : GrowR S m) (t : Word) (ht : t ≤ 1) (j : Word) (hj : j < nSl S m t)
    (x : Word) (hx : x.toNat < 2) :
    krW S.sa m t + j * 2 ≠ x ∧ krW S.sa m t + j * 2 + 1 ≠ x := by
  have a := (lay S m hG t ht).2.1
  have e := kslot_toNat S m hG t ht j hj
  constructor <;> intro h <;> have := congrArg UInt64.toNat h <;> omega

end lay

/-! ## The append -/

/-- Write the words `vs` into node `c` of tier `t`, from word `f`. -/
def wrRec (S : Schema) (t c : Word) : Mem → Word → List Word → Mem
  | m, _, [] => m
  | m, f, v :: vs => wrRec S t c (m.set64 (tierA S.ra t) (S.ad c f) v) (f + 1) vs

theorem wrRec_arr_ne (S : Schema) (t c : Word) (b : ArrId) (hb : b ≠ tierA S.ra t) :
    ∀ (vs : List Word) (m : Mem) (f : Word), (wrRec S t c m f vs).arr64 b = m.arr64 b := by
  intro vs
  induction vs with
  | nil => intro m f; rfl
  | cons v vs ih => intro m f; rw [wrRec, ih, Mem.arr64_set64_ne _ _ _ _ _ hb]

theorem wrRec_size (S : Schema) (t c : Word) (b : ArrId) :
    ∀ (vs : List Word) (m : Mem) (f : Word),
      ((wrRec S t c m f vs).arr64 b).size = (m.arr64 b).size := by
  intro vs
  induction vs with
  | nil => intro m f; rfl
  | cons v vs ih => intro m f; rw [wrRec, ih, size_set64]

theorem wrRec_read (S : Schema) (hS : S.WF) (t c i f : Word) (hc : c.toNat < 2 ^ 27)
    (hi : i.toNat < 2 ^ 27) (hf : f < S.w) :
    ∀ (vs : List Word) (m : Mem) (f₀ : Word), f₀.toNat + vs.length ≤ S.w.toNat →
      rdW ((wrRec S t c m f₀ vs).arr64 (tierA S.ra t)) (S.ad i f) =
        if i = c ∧ f₀.toNat ≤ f.toNat ∧ f.toNat < f₀.toNat + vs.length ∧
            (S.ad c f).toNat < (m.arr64 (tierA S.ra t)).size
        then vs.getD (f.toNat - f₀.toNat) 0 else rdW (m.arr64 (tierA S.ra t)) (S.ad i f) := by
  have hw := hS.w_le
  intro vs
  induction vs with
  | nil => intro m f₀ _; simp only [wrRec, List.length_nil]; grind
  | cons v vs ih =>
    intro m f₀ hl
    simp only [List.length_cons] at hl
    have hf₀ : f₀ < S.w := by grind
    have e1 : (f₀ + 1).toNat = f₀.toNat + 1 := by grind
    rw [wrRec, ih _ (f₀ + 1) (by rw [e1]; omega), e1, rdW_set64, size_set64]
    have := S.ad_inj hS c f₀ i f hc hf₀ hi hf
    by_cases hf0 : f.toNat = f₀.toNat
    · have : f = f₀ := UInt64.toNat_inj.mp hf0
      subst this
      grind
    by_cases hlt : f.toNat < f₀.toNat
    · grind
    · have : f.toNat - f₀.toNat = f.toNat - (f₀.toNat + 1) + 1 := by omega
      simp only [List.length_cons, this, List.getD_cons_succ]
      grind

theorem wrRec_words (S : Schema) (t c : Word) :
    ∀ (vs : List Word) (m : Mem) (f : Word), (wrRec S t c m f vs).words.size = m.words.size := by
  intro vs
  induction vs with
  | nil => intro m f; rfl
  | cons v vs ih => intro m f; rw [wrRec, ih, Mem.words_size_set64]

/-- The memory after appending node `c` (record `vs`) to tier `t`, registered at slot `j` with the
key word `q`. -/
def pushG (S : Schema) (m : Mem) (t : Word) (vs : List Word) (j c q : Word) : Mem :=
  (((wrRec S t c m 0 vs).set64 (tierA S.sa t) (krW S.sa m t + j * 2) (baseW m t + c + 1)).set64
    (tierA S.sa t) (krW S.sa m t + j * 2 + 1) q).set64 CTL (S.ca + (t &&& 1)) (c + 1)

section push
variable (S : Schema) (hS : S.WF) (m : Mem) (t : Word) (vs : List Word) (j c q : Word)

theorem pushG_arr (b : ArrId) (h1 : b ≠ tierA S.ra t) (h2 : b ≠ tierA S.sa t) (h3 : b ≠ CTL) :
    (pushG S m t vs j c q).arr64 b = m.arr64 b := by
  rw [pushG, Mem.arr64_set64_ne _ _ _ _ _ h3, Mem.arr64_set64_ne _ _ _ _ _ h2,
    Mem.arr64_set64_ne _ _ _ _ _ h2, wrRec_arr_ne _ _ _ _ h1]

@[store_grind =] theorem pushG_size (b : ArrId) :
    ((pushG S m t vs j c q).arr64 b).size = (m.arr64 b).size := by
  rw [pushG, size_set64, size_set64, size_set64, wrRec_size]

@[store_grind =] theorem pushG_words : (pushG S m t vs j c q).words.size = m.words.size := by
  rw [pushG, Mem.words_size_set64, Mem.words_size_set64, Mem.words_size_set64, wrRec_words]

include hS in
@[store_grind =] theorem pushG_ctl (ht : t ≤ 1) (x : Word) :
    rdW ((pushG S m t vs j c q).arr64 CTL) x =
      if x = S.ca + t ∧ (S.ca + t).toNat < (m.arr64 CTL).size then c + 1
      else rdW (m.arr64 CTL) x := by
  rw [pushG, rdW_set64, rdW_set64, rdW_set64, size_set64, size_set64, wrRec_size,
    wrRec_arr_ne _ _ _ _ (hS.ra_ctl' t).symm, and_one_of_le t ht]
  have := hS.sa_ctl' t
  grind

include hS in
/-- Tier `t`'s slot array after the append: the key word and the value word, or the old word. -/
theorem pushG_sa (x : Word) :
    rdW ((pushG S m t vs j c q).arr64 (tierA S.sa t)) x =
      if krW S.sa m t + j * 2 + 1 = x ∧ (krW S.sa m t + j * 2 + 1).toNat < (m.arr64 (tierA S.sa t)).size
      then q
      else if krW S.sa m t + j * 2 = x ∧ (krW S.sa m t + j * 2).toNat < (m.arr64 (tierA S.sa t)).size
      then baseW m t + c + 1
      else rdW (m.arr64 (tierA S.sa t)) x := by
  rw [pushG]
  simp only [rdW_set64, size_set64, wrRec_size, wrRec_arr_ne _ _ _ _ (hS.ra_sa' t t).symm,
    eq_false (hS.sa_ctl' t), false_and, ↓reduceIte, true_and]

include hS in
/-- The other tier's slot array survives an append. -/
theorem pushG_sa_other (t' : Word) (ht : t ≤ 1) (ht' : t' ≤ 1) (hne : t' ≠ t) :
    (pushG S m t vs j c q).arr64 (tierA S.sa t') = m.arr64 (tierA S.sa t') :=
  pushG_arr S m t vs j c q _ (hS.ra_sa' t t').symm (tierA_ne_tier _ ht' ht hne) (hS.sa_ctl' t')

include hS in
/-- The slot bases survive an append (`CTL[62]` is not a count). -/
@[store_grind =] theorem baseW_pushG (ht : t ≤ 1) (t' : Word) :
    baseW (pushG S m t vs j c q) t' = baseW m t' := by
  have := hS.scb
  simp only [baseW]
  rw [pushG_ctl S hS m t vs j c q ht]
  have : SCB ≠ S.ca + t := by
    rcases le_one_cases t ht with rfl | rfl <;> grind
  simp [this]

/-- The new slot reads `c + 1` against its own base, when the base leaves room for the index
(`CTL[62] < 2^62 + 2^32`, a clause of `StoreR`). -/
@[store_grind =] theorem slotV_new (ht : t ≤ 1) (hb : (rdW (m.arr64 CTL) SCB).toNat < 2 ^ 62 + 2 ^ 32)
    (hc : c.toNat < 2 ^ 27) : slotRd (baseW m t + c + 1) (baseW m t) = c + 1 := by
  simp only [slotRd]
  have : (baseW m t).toNat < 2 ^ 63 := by
    simp only [baseW]
    rcases le_one_cases t ht with rfl | rfl <;> simp <;> omega
  grind

include hS in
/-- A field after the append: the new record's, or the old. -/
@[store_grind =] theorem fld_pushG (t' i f : Word) (ht : t ≤ 1) (hc : c.toNat < 2 ^ 27)
    (ht' : t' ≤ 1) (hi : i.toNat < 2 ^ 27) (hf : f < S.w) (hl : vs.length = S.w.toNat) :
    fld S (pushG S m t vs j c q) t' i f =
      if t' = t ∧ i = c ∧ (S.ad c f).toNat < (m.arr64 (tierA S.ra t)).size then vs.getD f.toNat 0
      else fld S m t' i f := by
  by_cases htt : t' = t
  · subst htt
    rw [fld, pushG, Mem.arr64_set64_ne _ _ _ _ _ (hS.ra_ctl' t'),
      Mem.arr64_set64_ne _ _ _ _ _ (hS.ra_sa' t' t'),
      Mem.arr64_set64_ne _ _ _ _ _ (hS.ra_sa' t' t'),
      wrRec_read S hS t' c i f hc hi hf vs m 0 (by simp [hl])]
    simp only [fld, UInt64.toNat_zero, Nat.zero_le, true_and, Nat.sub_zero, Nat.zero_add, hl]
    grind
  · rw [fld, pushG_arr S m t vs j c q _ (hS.ra_ne ht' ht htt) (hS.ra_sa' t' t) (hS.ra_ctl' t')]
    simp [htt, fld]

variable (hG : GrowR S m) (ht : t ≤ 1) (hj : j < nSl S m t)
include hS hG ht hj

/-- The count and offset words survive an append. -/
theorem meta_pushG (t' : Word) (ht' : t' ≤ 1) :
    knW S.sa (pushG S m t vs j c q) t' = knW S.sa m t' ∧
      koW S.sa (pushG S m t vs j c q) t' = koW S.sa m t' := by
  by_cases htt : t' = t
  · subst htt
    obtain ⟨b1, b2⟩ := kslot_ne_meta S m hG t' ht j hj 0 (by decide)
    obtain ⟨c1, c2⟩ := kslot_ne_meta S m hG t' ht j hj 1 (by decide)
    simp only [knW, koW, pushG_sa S hS, b1, c1, b2, c2, false_and, ↓reduceIte, and_self]
  · simp only [knW, koW, pushG_sa_other S hS m t vs j c q t' ht ht' htt, and_self]

theorem krW_pushG (t' : Word) (ht' : t' ≤ 1) :
    krW S.sa (pushG S m t vs j c q) t' = krW S.sa m t' := by
  obtain ⟨e1, e2⟩ := meta_pushG S hS m t vs j c q hG ht hj t' ht'
  simp only [krW, e2]

theorem nSl_pushG (t' : Word) (ht' : t' ≤ 1) : nSl S (pushG S m t vs j c q) t' = nSl S m t' :=
  (meta_pushG S hS m t vs j c q hG ht hj t' ht').1

/-- **An append keeps the layout.** -/
theorem growR_pushG : GrowR S (pushG S m t vs j c q) := by
  obtain ⟨h0, h1⟩ := hG
  have e0 := meta_pushG S hS m t vs j c q ⟨h0, h1⟩ ht hj 0 (by decide)
  have e1 := meta_pushG S hS m t vs j c q ⟨h0, h1⟩ ht hj 1 (by decide)
  refine ⟨?_, ?_⟩
  · simpa only [TierLay, e0.1, e0.2, pushG_size] using h0
  · simpa only [TierLay, e1.1, e1.2, pushG_size] using h1

/-- **A slot after an append**: the new node's at slot `j` of tier `t`, else the old. -/
theorem slotW_pushG (hb : (rdW (m.arr64 CTL) SCB).toNat < 2 ^ 62 + 2 ^ 32) (hc : c.toNat < 2 ^ 27)
    (t' j' : Word) (ht' : t' ≤ 1) (hj' : j' < nSl S m t') :
    slotW S (pushG S m t vs j c q) t' j' = if t' = t ∧ j' = j then c + 1 else slotW S m t' j' := by
  by_cases htt : t' = t
  · subst htt
    have hl := lay S m hG t' ht
    have e := kslot_toNat S m hG t' ht j hj
    simp only [slotW, slotV, krW_pushG S hS m t' vs j c q hG ht hj t' ht',
      baseW_pushG S hS m t' vs j c q ht, pushG_sa S hS]
    rw [ite_eq_right (fun h => kslot1_ne S m hG t' ht j j' hj hj' h.1)]
    have hjn := UInt64.lt_iff_toNat_lt.mp hj
    by_cases h : j' = j
    · subst h
      simp only [and_self, ↓reduceIte, show (krW S.sa m t' + j' * 2).toNat <
        (m.arr64 (tierA S.sa t')).size by omega, slotV_new m t' c ht hb hc]
    · simp only [h, and_false, ↓reduceIte]
      rw [ite_eq_right (fun h' => h ((kslot_eq_iff S m hG t' ht j j' hj hj').mp h'.1).symm)]
  · simp only [slotW, krW_pushG S hS m t vs j c q hG ht hj t' ht', baseW_pushG S hS m t vs j c q ht,
      pushG_sa_other S hS m t vs j c q t' ht ht' htt, htt, false_and, ↓reduceIte]

theorem slotK_pushG (t' j' : Word) (ht' : t' ≤ 1) (hj' : j' < nSl S m t') :
    slotK S (pushG S m t vs j c q) t' j' = if t' = t ∧ j' = j then q else slotK S m t' j' := by
  by_cases htt : t' = t
  · subst htt
    have hl := lay S m hG t' ht
    have e := kslot_toNat S m hG t' ht j hj
    have e' := kslot_toNat S m hG t' ht j' hj'
    simp only [slotK, krW_pushG S hS m t' vs j c q hG ht hj t' ht', pushG_sa S hS]
    have hjn := UInt64.lt_iff_toNat_lt.mp hj
    by_cases h : j' = j
    · subst h
      simp only [and_self, ↓reduceIte, show (krW S.sa m t' + j' * 2 + 1).toNat <
        (m.arr64 (tierA S.sa t')).size by omega]
    · simp only [h, and_false, ↓reduceIte]
      rw [ite_eq_right (fun h' => h ((kslot1_eq_iff S m hG t' ht j j' hj hj').mp h'.1).symm)]
      rw [ite_eq_right (fun h' => by
              have := congrArg UInt64.toNat h'.1
              rw [e.1, e'.2] at this
              omega)]
  · simp only [slotK, krW_pushG S hS m t vs j c q hG ht hj t' ht',
      pushG_sa_other S hS m t vs j c q t' ht ht' htt, htt, false_and, ↓reduceIte]

end push

/-! ## The probe -/

section probe
variable (S : Schema) (m : Mem) (t : Word) (mt : Word → Bool) (ex : Bool) (q : Word)

/-- One step of the probe of tier `t` for key word `q` and node match `mt` (not run when `ex`):
the shape of every `*_find` model. -/
def probeArm (P : Word → Word → List Word) (j d : Word) : List Word :=
  if d < nSl S m t then
    if slotW S m t j = 0 then [0, 0, j, d]
    else if slotK S m t j = q ∧ (ex = true ∨ mt (slotW S m t j - 1) = true) then
      [1, slotW S m t j - 1, j, d]
    else P ((j + 1) * (if j + 1 < nSl S m t then 1 else 0)) (d + 1)
  else []

/-- A slot the probe passes: occupied and no hit. -/
def PassG (j : Word) : Prop :=
  slotW S m t j ≠ 0 ∧ ¬ (slotK S m t j = q ∧ (ex = true ∨ mt (slotW S m t j - 1) = true))

/-- The probe passes the first `d` slots of the run from `x`. -/
def NoMatchG (x : Word) (d : Nat) : Prop :=
  ∀ e < d, PassG S m t mt ex q (walkW (nSl S m t) x e)

/-- What a result `rs` of the probe from slot `x` says: a hit (`rs[0] ≠ 0`) is node `rs[1]` in
slot `rs[2]` with the key word, matching (or the table exact); a miss is the free slot `rs[2]`,
step `rs[3]` of the run, after slots it passes. -/
def ProbeOKG (x : Word) (rs : List Word) : Prop :=
  rs ≠ [] →
    (rs.headD 0 ≠ 0 →
      (slotK S m t (rs.tail.tail.headD 0) = q ∧ (ex = true ∨ mt (rs.tail.headD 0) = true)) ∧
      slotW S m t (rs.tail.tail.headD 0) = rs.tail.headD 0 + 1 ∧
      slotW S m t (rs.tail.tail.headD 0) ≠ 0 ∧ rs.tail.tail.headD 0 < nSl S m t) ∧
    (rs.headD 0 = 0 →
      rs.tail.tail.headD 0 = walkW (nSl S m t) x (rs.tail.tail.tail.headD 0).toNat ∧
      rs.tail.tail.headD 0 < nSl S m t ∧ slotW S m t (rs.tail.tail.headD 0) = 0 ∧
      NoMatchG S m t mt ex q x (rs.tail.tail.tail.headD 0).toNat)

theorem probe_okG (P : Word → Word → List Word) (hP : ∀ j d, P j d = probeArm S m t mt ex q P j d)
    (x : Word) (hx : x < nSl S m t) :
    ∀ (k : Nat) (d : Word), (nSl S m t).toNat - d.toNat = k → NoMatchG S m t mt ex q x d.toNat →
      ProbeOKG S m t mt ex q x (P (walkW (nSl S m t) x d.toNat) d) := by
  intro k
  induction k with
  | zero => intro d hk _; rw [hP, probeArm]; grind [ProbeOKG]
  | succ k ih =>
    intro d hk hnm
    have := ih (d + 1)
    clear ih
    have hd : d < nSl S m t := by grind
    have hd1 : (d + 1).toNat = d.toNat + 1 := by grind
    specialize this (by grind)
    rw [hd1, walkW_succ] at this
    rw [hP, probeArm]
    by_cases h0 : slotW S m t (walkW (nSl S m t) x d.toNat) = 0
    · simp only [hd, h0, ↓reduceIte]; grind [store_grind, ProbeOKG]
    by_cases hm : slotK S m t (walkW (nSl S m t) x d.toNat) = q ∧
        (ex = true ∨ mt (slotW S m t (walkW (nSl S m t) x d.toNat) - 1) = true)
    · simp only [hd, h0, hm, ↓reduceIte, and_self]
      intro _
      refine ⟨fun _ => ⟨⟨hm.1, ?_⟩, ?_, h0, walkW_lt _ _ _ hx⟩, fun h => absurd h (by simp)⟩
      · simpa using hm.2
      · simp
    · simp only [hd, h0, hm, ↓reduceIte]
      exact this (fun e he => by
        by_cases hed : e = d.toNat
        · subst hed; exact ⟨h0, hm⟩
        · exact hnm e (by omega))

/-- The probe from the home slot of `h`. -/
theorem probe_homeG (P : Word → Word → List Word) (hP : ∀ j d, P j d = probeArm S m t mt ex q P j d)
    (h : Word) (hn : 0 < nSl S m t) :
    ProbeOKG S m t mt ex q (homeS S m t h) (P (homeS S m t h) 0) :=
  probe_okG S m t mt ex q P hP _ (homeW_lt _ _ hn) _ 0 rfl (by simp [NoMatchG])

end probe

/-! ## The relation -/

section rel
variable {α δ : Type} {k : IdxKind} [BEq α] [Hashable α]
variable (S : Schema) (R : Mem → Word → Word → α → Prop) (hs : Mem → Word → Word → Word)
  (KP : Mem → Word → Word → Word → Prop)

/-- The slots of tier `t` index its `c` nodes: every slot holds `0` or a node below `c`, with a key
word `KP` admits for the node, and node `i` lies on the run from its home slot (the home of its
hash `hs m t i`), after occupied slots: linear probing without deletion. -/
def SlotsOKG (m : Mem) (t : Word) (c : Nat) : Prop :=
  (∀ j : Word, j < nSl S m t → (slotW S m t j).toNat ≤ c) ∧
  (∀ j : Word, j < nSl S m t → slotW S m t j ≠ 0 → KP m t (slotW S m t j - 1) (slotK S m t j)) ∧
  ∀ i : Word, i.toNat < c → ∃ d : Nat,
    slotW S m t (walkW (nSl S m t) (homeS S m t (hs m t i)) d) = i + 1 ∧
    ∀ e < d, slotW S m t (walkW (nSl S m t) (homeS S m t (hs m t i)) e) ≠ 0

/-- **Tier `t` of an L table represents the arena table `tb`**: the same nodes in the same order
(node `i` holds `tb.nodes[i]` by `R`), the same key → handle map (each node's key maps to its
handle, each entry points at a node with its key), and the slots index the nodes. -/
def TierR (m : Mem) (t : Word) (tb : Tbl α (Idx k) δ) : Prop :=
  (cntW S m t).toNat = tb.nodes.size ∧ tb.nodes.size ≤ 134217728 ∧
  S.w.toNat * tb.nodes.size ≤ (m.arr64 (tierA S.ra t)).size ∧
  (∀ (i : Word) a, tb.nodes[i.toNat]? = some a → R m t i a) ∧
  (∀ (i : Word) a, tb.nodes[i.toNat]? = some a →
    tb.cons[a]? = some (decI (hdW S.tag.toUInt64 t i))) ∧
  (∀ a x, tb.cons[a]? = some x → tb.nodes[(hix x).toNat]? = some a) ∧
  SlotsOKG S hs KP m t tb.nodes.size

/-- **The relation of a two-tier table**: the counts fit in `CTL` and the scratch tier's slot base
`CTL[62]` leaves room for node indices, the scratch flag `CTL[1]` is `on`, both tiers represent
their tables, the slot array's layout holds. -/
def StoreR (m : Mem) (on : Bool) (tbP tbS : Tbl α (Idx k) δ) : Prop :=
  (S.ca.toNat + 2 ≤ (m.arr64 CTL).size ∧ (rdW (m.arr64 CTL) SCB).toNat < 2 ^ 62 + 2 ^ 32) ∧
  (rdW (m.arr64 CTL) 1 != 0) = on ∧
  TierR S R hs KP m 0 tbP ∧ TierR S R hs KP m 1 tbS ∧ GrowR S m

/-- `m'` agrees with `m` outside the table's arrays (both tiers) and `CTL`, and at the pool top
`CTL[0]`. -/
def OutEq (m m' : Mem) : Prop :=
  (∀ b, b ≠ S.ra → b ≠ tier1 S.ra → b ≠ S.sa → b ≠ tier1 S.sa → b ≠ CTL → m'.arr64 b = m.arr64 b) ∧
  rdW (m'.arr64 CTL) 0 = rdW (m.arr64 CTL) 0

/-- **The instance's frame obligation**: a node's relation and hash depend on its own words and
on memory outside the table. -/
def RFrame : Prop :=
  ∀ m m' t i, OutEq S m m' → (∀ f, f < S.w → fld S m' t i f = fld S m t i f) →
    (∀ a, R m t i a → R m' t i a) ∧ hs m' t i = hs m t i

/-- The key-word predicate depends on the node's own words and hash. -/
def KFrame : Prop :=
  ∀ m m' t i, (∀ f, f < S.w → fld S m' t i f = fld S m t i f) → hs m' t i = hs m t i →
    ∀ K, KP m t i K → KP m' t i K

/-- **The query's match obligation**: on a node of the table, the match is key equality. -/
def MatchOK (mt : Word → Word → Bool) (m : Mem) (key : α) : Prop :=
  ∀ t i a, R m t i a → (mt t i = true ↔ a = key)

/-- A matching node has the query's hash. -/
def HomeOK (mt : Word → Word → Bool) (m : Mem) (qh : Word) : Prop :=
  ∀ t i, mt t i = true → hs m t i = qh

/-- **The query's key word** `q`: a matching node's admissible key word is `q`, and (an exact
table, `ex`) a node with key word `q` matches. -/
def QKeyOK (mt : Word → Word → Bool) (m : Mem) (ex : Bool) (q : Word) : Prop :=
  ∀ t i K, KP m t i K → (mt t i = true → K = q) ∧ (ex = true → K = q → mt t i = true)

/-- **The query's append obligation**: the record `vs` written as the new node of tier `t` holds
the key, with the query's hash, and admits the key word `q`. -/
def NewOK (m : Mem) (vs : List Word) (key : α) (qh q : Word) : Prop :=
  ∀ t j, t ≤ 1 → PushRoom S m t → (t = 0 → rdW (m.arr64 CTL) 1 = 0) →
    R (pushG S m t vs j (cntW S m t) q) t (cntW S m t) key ∧
    hs (pushG S m t vs j (cntW S m t) q) t (cntW S m t) = qh ∧
    KP (pushG S m t vs j (cntW S m t) q) t (cntW S m t) q

theorem outEq_pushG (hS : S.WF) (m : Mem) (t : Word) (ht : t ≤ 1) (vs : List Word) (j c q : Word) :
    OutEq S m (pushG S m t vs j c q) := by
  have := hS.ca
  refine ⟨fun b h1 h1' h2 h2' h3 => pushG_arr S m t vs j c q b
    (by rcases tierA_cases' S.ra t with e | e <;> rw [e] <;> assumption)
    (by rcases tierA_cases' S.sa t with e | e <;> rw [e] <;> assumption) h3, ?_⟩
  rw [pushG_ctl S hS _ _ _ _ _ _ ht]
  grind

/-! ### Hit and miss -/

section tier
variable (m : Mem) (t : Word) (tb : Tbl α (Idx k) δ) (hT : TierR S R hs KP m t tb)
  (mt : Word → Word → Bool) (key : α) (hM : MatchOK R mt m key) (ex : Bool) (q : Word)
  (hQ : QKeyOK KP mt m ex q)

include hT hM hQ in
/-- A probe hit is the arena's cons hit, at the same handle. -/
theorem tierR_hit (x : Word) (rs : List Word) (hP : ProbeOKG S m t (mt t) ex q x rs)
    (hr : rs ≠ []) (hh : rs.headD 0 ≠ 0) :
    tb.cons[key]? = some (decI (hdW S.tag.toUInt64 t (rs.tail.headD 0))) := by
  obtain ⟨⟨hk, hm⟩, hs1, hs2, hj⟩ := (hP hr).1 hh
  obtain ⟨-, hcap, -, hrec, hsome, -, ⟨hsl, hkp, -⟩⟩ := hT
  have h1 := hsl _ hj
  rw [hs1] at h1
  have hi : (rs.tail.headD 0).toNat < tb.nodes.size := by grind
  obtain ⟨a, ha⟩ : ∃ a, tb.nodes[(rs.tail.headD 0).toNat]? = some a :=
    ⟨_, Array.getElem?_eq_getElem hi⟩
  have hK := hkp _ hj hs2
  rw [hs1, UInt64.add_sub_cancel] at hK
  have hmt : mt t (rs.tail.headD 0) = true := by
    rcases hm with he | hm
    · exact (hQ t _ _ hK).2 he hk
    · exact hm
  have := (hM t _ a (hrec _ a ha)).mp hmt
  subst this
  exact hsome _ _ ha

include hT hM hQ in
/-- A probe miss from the home slot: the key is not in the tier. -/
theorem tierR_miss (qh : Word) (hH : HomeOK hs mt m qh) (rs : List Word)
    (hP : ProbeOKG S m t (mt t) ex q (homeS S m t qh) rs) (hr : rs ≠ []) (hh : rs.headD 0 = 0) :
    tb.cons[key]? = none := by
  cases hc : tb.cons[key]? with
  | none => rfl
  | some x =>
    exfalso
    obtain ⟨-, hcap, -, hrec, -, hback, ⟨-, hkp, hrun⟩⟩ := hT
    have hn := hback key x hc
    have hR := hrec (hix x) key hn
    have hm := (hM t (hix x) key hR).mpr rfl
    have hq := hH t (hix x) hm
    have hlt : (hix x).toNat < tb.nodes.size := by
      have := Array.getElem?_eq_some_iff.mp hn; exact this.1
    obtain ⟨d, hd1, hd2⟩ := hrun (hix x) hlt
    obtain ⟨hJ, hJn, hJ0, hnm⟩ := (hP hr).2 hh
    rw [hq] at hd1 hd2
    generalize rs.tail.tail.tail.headD 0 = D at hJ hnm
    generalize rs.tail.tail.headD 0 = J at hJ hJn hJ0
    subst hJ
    have hn : 0 < nSl S m t := by
      have := UInt64.lt_iff_toNat_lt.mp hJn
      exact UInt64.lt_iff_toNat_lt.mpr (by simp; omega)
    rcases Nat.lt_trichotomy d D.toNat with h | h | h
    · obtain ⟨hp1, hp2⟩ := hnm d h
      have hw : walkW (nSl S m t) (homeS S m t qh) d < nSl S m t :=
        walkW_lt _ _ _ (homeW_lt _ _ hn)
      have hK := hkp _ hw hp1
      rw [hd1, UInt64.add_sub_cancel] at hK hp2
      exact hp2 ⟨(hQ t _ _ hK).1 hm, .inr hm⟩
    · subst h
      rw [hd1] at hJ0
      have := congrArg UInt64.toNat hJ0
      rw [UInt64.toNat_add] at this
      simp at this
      omega
    · exact hd2 _ h hJ0

end tier

/-! ### The append -/

theorem one_le_of_ne_zero {x : Word} (h : x ≠ 0) : 1 ≤ x := by
  rw [UInt64.le_iff_toNat_le]
  have : x.toNat ≠ 0 := fun h' => h (UInt64.toNat_inj.mp (by simpa using h'))
  simp; omega

theorem tierR_push [LawfulBEq α] (hS : S.WF) (hfr : RFrame S R hs) (hkf : KFrame S hs KP) (m : Mem)
    (t : Word) (ht : t ≤ 1) (tb : Tbl α (Idx k) δ) (hT : TierR S R hs KP m t tb)
    (mt : Word → Word → Bool) (key : α) (hM : MatchOK R mt m key) (ex : Bool) (q : Word)
    (hQ : QKeyOK KP mt m ex q) (qh : Word) (hH : HomeOK hs mt m qh) (rs : List Word)
    (hP : ProbeOKG S m t (mt t) ex q (homeS S m t qh) rs) (hr : rs ≠ []) (hh : rs.headD 0 = 0)
    (hroom : PushRoom S m t) (hctl : S.ca.toNat + 2 ≤ (m.arr64 CTL).size)
    (hb : (rdW (m.arr64 CTL) SCB).toNat < 2 ^ 62 + 2 ^ 32) (vs : List Word)
    (hl : vs.length = S.w.toNat) (hN : NewOK S R hs KP m vs key qh q)
    (ht0 : t = 0 → rdW (m.arr64 CTL) 1 = 0) (dd : δ) (hG : GrowR S m) :
    TierR S R hs KP (pushG S m t vs (rs.tail.tail.headD 0) (cntW S m t) q) t
      (tb.push key dd (decI (hdW S.tag.toUInt64 t (cntW S m t)))) := by
  have hmiss := tierR_miss S R hs KP m t tb hT mt key hM ex q hQ qh hH rs hP hr hh
  obtain ⟨hJ, hjn, hJ0, hnm⟩ := (hP hr).2 hh
  generalize rs.tail.tail.tail.headD 0 = D at hJ hnm
  generalize hJdef : rs.tail.tail.headD 0 = J at hJ hjn hJ0
  have hnS := nSl_pushG S hS m t vs J (cntW S m t) q hG ht hjn t ht
  have hnew := hN t J ht hroom ht0
  have hca := hS.ca
  have htag : S.tag.toUInt64 < 16 := by have := hS.tag; grind
  have hout := outEq_pushG S hS m t ht vs J (cntW S m t) q
  have hcnt : (cntW S m t).toNat < 2 ^ 27 := hroom.1
  have hsw := slotW_pushG S hS m t vs J (cntW S m t) q hG ht hjn hb hcnt t
  have hsk := slotK_pushG S hS m t vs J (cntW S m t) q hG ht hjn t
  obtain ⟨hc, hcap, hrs, hrec, hsome, hback, hsl, hkp, hrun⟩ := hT
  simp only [TierR, SlotsOKG, Tbl.push_nodes, Tbl.push_cons, Array.size_push]
  have hctr : (S.ca + t).toNat < (m.arr64 CTL).size := by grind
  have hfe : ∀ i : Word, i.toNat < tb.nodes.size → ∀ f, f < S.w →
      fld S (pushG S m t vs J (cntW S m t) q) t i f = fld S m t i f := by
    intro i hi f hf; rw [fld_pushG S hS] <;> grind [PushRoom]
  have hhs : ∀ i : Word, i.toNat < tb.nodes.size →
      hs (pushG S m t vs J (cntW S m t) q) t i = hs m t i :=
    fun i hi => (hfr m _ t i hout (hfe i hi)).2
  have hn0 : 0 < nSl S m t := by
    have := UInt64.lt_iff_toNat_lt.mp hjn; exact UInt64.lt_iff_toNat_lt.mpr (by simp; omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · clear hrec hsome hback hsl hrun hkp; grind [store_grind, cntW, PushRoom]
  · clear hrec hsome hback hsl hrun hkp; grind [store_grind, PushRoom]
  · clear hrec hsome hback hsl hrun hkp; grind [store_grind, PushRoom]
  · intro i a hk
    rw [Array.getElem?_push] at hk
    split at hk
    · cases hk
      have : i = cntW S m t := UInt64.toNat_inj.mp (by omega)
      subst this
      exact hnew.1
    · have hi : i.toNat < tb.nodes.size := by
        have := (Array.getElem?_eq_some_iff.mp hk).1; exact this
      exact (hfr m _ t i hout (hfe i hi)).1 a (hrec i a hk)
  · intro i a hk
    clear hrec hback hsl hrun hkp
    grind [store_grind, PushRoom]
  · intro a x hk
    clear hrec hsome hsl hrun hkp
    grind [store_grind, PushRoom]
  · intro j hj
    rw [hnS] at hj
    rw [hsw j ht hj]
    have := hsl j hj
    split <;> grind
  · intro j hj hne
    rw [hnS] at hj
    rw [hsw j ht hj] at hne ⊢
    rw [hsk j ht hj]
    by_cases hjJ : j = J
    · subst hjJ
      simp only [and_self, ↓reduceIte, UInt64.add_sub_cancel]
      exact hnew.2.2
    · simp only [hjJ, and_false, ↓reduceIte] at hne ⊢
      have hle := hsl j hj
      have hlt : (slotW S m t j - 1).toNat < tb.nodes.size := by
        have : slotW S m t j ≠ 0 := hne
        have := UInt64.toNat_sub_of_le _ _ (one_le_of_ne_zero this)
        grind
      exact hkf m _ t _ (hfe _ hlt) (hhs _ hlt) _ (hkp j hj hne)
  · intro i hi
    have hwl : ∀ x e, x < nSl S m t → walkW (nSl S m t) x e < nSl S m t :=
      fun x e hx => walkW_lt _ _ _ hx
    have hhl : ∀ h, homeS S m t h < nSl S m t := fun h => homeW_lt _ _ hn0
    by_cases hic : i = cntW S m t
    · subst hic
      refine ⟨D.toNat, ?_, fun e he => ?_⟩
      · simp only [hnS, homeS, hnew.2.1]
        rw [← homeS, ← hJ, hsw J ht hjn]; simp
      · simp only [hnS, homeS, hnew.2.1]
        rw [← homeS, hsw _ ht (hwl _ _ (hhl _))]
        have := (hnm e he).1
        split
        · rename_i h; rw [h.2, hJ0] at this; exact absurd rfl this
        · exact this
    · have hi' : i.toNat < tb.nodes.size := by
        have : i.toNat ≠ (cntW S m t).toNat := fun h => hic (UInt64.toNat_inj.mp h)
        omega
      obtain ⟨d, hd1, hd2⟩ := hrun i hi'
      refine ⟨d, ?_, fun e he => ?_⟩
      · simp only [hnS, homeS, hhs i hi']
        rw [← homeS, hsw _ ht (hwl _ _ (hhl _))]
        split
        · rename_i h; rw [h.2, hJ0] at hd1
          have := congrArg UInt64.toNat hd1; rw [UInt64.toNat_add] at this; simp at this; omega
        · exact hd1
      · simp only [hnS, homeS, hhs i hi']
        rw [← homeS, hsw _ ht (hwl _ _ (hhl _))]
        split
        · intro h0
          have := congrArg UInt64.toNat h0; rw [UInt64.toNat_add] at this; simp at this; omega
        · exact hd2 e he

/-- Appending to tier `t` leaves the other tier represented. -/
theorem tierR_other (hS : S.WF) (hfr : RFrame S R hs) (hkf : KFrame S hs KP) (m : Mem)
    (t t' : Word) (ht : t ≤ 1) (ht' : t' ≤ 1) (hne : t' ≠ t) (tb : Tbl α (Idx k) δ)
    (hT : TierR S R hs KP m t' tb) (hroom : PushRoom S m t)
    (hb : (rdW (m.arr64 CTL) SCB).toNat < 2 ^ 62 + 2 ^ 32) (vs : List Word)
    (hl : vs.length = S.w.toNat) (J q : Word) (hG : GrowR S m) (hJ : J < nSl S m t) :
    TierR S R hs KP (pushG S m t vs J (cntW S m t) q) t' tb := by
  have hca := hS.ca
  have hnS := nSl_pushG S hS m t vs J (cntW S m t) q hG ht hJ t' ht'
  have hout := outEq_pushG S hS m t ht vs J (cntW S m t) q
  have hsw := slotW_pushG S hS m t vs J (cntW S m t) q hG ht hJ hb hroom.1 t'
  have hsk := slotK_pushG S hS m t vs J (cntW S m t) q hG ht hJ t'
  obtain ⟨hc, hcap, hrs, hrec, hsome, hback, hsl, hkp, hrun⟩ := hT
  have hfe : ∀ i : Word, i.toNat < tb.nodes.size → ∀ f, f < S.w →
      fld S (pushG S m t vs J (cntW S m t) q) t' i f = fld S m t' i f := by
    intro i hi f hf; rw [fld_pushG S hS] <;> grind [PushRoom]
  have hhs : ∀ i : Word, i.toNat < tb.nodes.size →
      hs (pushG S m t vs J (cntW S m t) q) t' i = hs m t' i :=
    fun i hi => (hfr m _ t' i hout (hfe i hi)).2
  have hsw' : ∀ j, j < nSl S m t' → slotW S (pushG S m t vs J (cntW S m t) q) t' j = slotW S m t' j :=
    fun j hj => by rw [hsw j ht' hj]; simp [hne]
  have hsk' : ∀ j, j < nSl S m t' → slotK S (pushG S m t vs J (cntW S m t) q) t' j = slotK S m t' j :=
    fun j hj => by rw [hsk j ht' hj]; simp [hne]
  refine ⟨?_, hcap, ?_, ?_, hsome, hback, ?_, ?_, ?_⟩
  · clear hrec hsome hback hsl hrun hkp hfe hhs; grind [store_grind, cntW]
  · clear hrec hsome hback hsl hrun hkp hfe hhs; grind [store_grind]
  · intro i a hk
    exact (hfr m _ t' i hout (hfe i (Array.getElem?_eq_some_iff.mp hk).1)).1 a (hrec i a hk)
  · intro j hj; rw [hnS] at hj; rw [hsw' j hj]; exact hsl j hj
  · intro j hj hne'
    rw [hnS] at hj; rw [hsw' j hj] at hne' ⊢; rw [hsk' j hj]
    have hle := hsl j hj
    have hlt : (slotW S m t' j - 1).toNat < tb.nodes.size := by
      have := UInt64.toNat_sub_of_le _ _ (one_le_of_ne_zero hne')
      grind
    exact hkf m _ t' _ (hfe _ hlt) (hhs _ hlt) _ (hkp j hj hne')
  · intro i hi
    obtain ⟨d, hd1, hd2⟩ := hrun i hi
    have hn0 : 0 < nSl S m t' :=
      UInt64.lt_iff_toNat_lt.mpr (by have := (lay S m hG t' ht').1; simp; omega)
    refine ⟨d, ?_, fun e he => ?_⟩
    · simp only [hnS, homeS, hhs i hi]
      rw [hsw' _ (walkW_lt _ _ _ (homeW_lt _ _ hn0))]
      exact hd1
    · simp only [hnS, homeS, hhs i hi]
      rw [hsw' _ (walkW_lt _ _ _ (homeW_lt _ _ hn0))]
      exact hd2 e he

/-- A tier stays represented when its arrays, count and base stay and its nodes' relations and
hashes do (the pool growing under the `lit` table). -/
theorem tierR_mono (m m' : Mem) (t : Word) (tb : Tbl α (Idx k) δ)
    (hra : m'.arr64 (tierA S.ra t) = m.arr64 (tierA S.ra t))
    (hsa : m'.arr64 (tierA S.sa t) = m.arr64 (tierA S.sa t))
    (hc : cntW S m' t = cntW S m t) (hbase : baseW m' t = baseW m t)
    (hR : ∀ i a, R m t i a → R m' t i a)
    (hh : ∀ i, hs m' t i = hs m t i) (hKP : ∀ i K, KP m t i K → KP m' t i K)
    (hT : TierR S R hs KP m t tb) : TierR S R hs KP m' t tb := by
  obtain ⟨hc', hcap, hrs, hrec, hsome, hback, hsl, hkp, hrun⟩ := hT
  have hk : krW S.sa m' t = krW S.sa m t := by simp only [krW, koW, hsa]
  have hn : nSl S m' t = nSl S m t := by simp only [nSl, knW, hsa]
  have hsl' : ∀ j, slotW S m' t j = slotW S m t j := fun j => by simp only [slotW, hsa, hbase, hk]
  have hsk' : ∀ j, slotK S m' t j = slotK S m t j := fun j => by simp only [slotK, hsa, hk]
  refine ⟨by rw [hc]; exact hc', hcap, by rw [hra]; exact hrs,
    fun i a h => hR i a (hrec i a h), hsome, hback, ?_, ?_, ?_⟩
  · intro j hj; rw [hsl']; exact hsl j (by rw [← hn]; exact hj)
  · intro j hj hne
    rw [hsl'] at hne ⊢; rw [hsk']
    exact hKP _ _ (hkp j (by rw [← hn]; exact hj) hne)
  · intro i hi
    obtain ⟨d, h1, h2⟩ := hrun i hi
    exact ⟨d, by simp only [hsl', hn, homeS, hh]; exact h1,
      fun e he => by simp only [hsl', hn, homeS, hh]; exact h2 e he⟩

/-- `tierR_mono` with the nodes' relation needed only for the table's own nodes. -/
theorem tierR_mono' (m m' : Mem) (t : Word) (tb : Tbl α (Idx k) δ)
    (hra : m'.arr64 (tierA S.ra t) = m.arr64 (tierA S.ra t))
    (hsa : m'.arr64 (tierA S.sa t) = m.arr64 (tierA S.sa t))
    (hc : cntW S m' t = cntW S m t) (hbase : baseW m' t = baseW m t)
    (hR : ∀ (i : Word) a, tb.nodes[i.toNat]? = some a → R m t i a → R m' t i a)
    (hh : ∀ i, hs m' t i = hs m t i) (hKP : ∀ i K, KP m t i K → KP m' t i K)
    (hT : TierR S R hs KP m t tb) : TierR S R hs KP m' t tb := by
  obtain ⟨hc', hcap, hrs, hrec, hsome, hback, hsl, hkp, hrun⟩ := hT
  have hk : krW S.sa m' t = krW S.sa m t := by simp only [krW, koW, hsa]
  have hn : nSl S m' t = nSl S m t := by simp only [nSl, knW, hsa]
  have hsl' : ∀ j, slotW S m' t j = slotW S m t j := fun j => by simp only [slotW, hsa, hbase, hk]
  have hsk' : ∀ j, slotK S m' t j = slotK S m t j := fun j => by simp only [slotK, hsa, hk]
  refine ⟨by rw [hc]; exact hc', hcap, by rw [hra]; exact hrs,
    fun i a h => hR i a h (hrec i a h), hsome, hback, ?_, ?_, ?_⟩
  · intro j hj; rw [hsl']; exact hsl j (by rw [← hn]; exact hj)
  · intro j hj hne
    rw [hsl'] at hne ⊢; rw [hsk']
    exact hKP _ _ (hkp j (by rw [← hn]; exact hj) hne)
  · intro i hi
    obtain ⟨d, h1, h2⟩ := hrun i hi
    exact ⟨d, by simp only [hsl', hn, homeS, hh]; exact h1,
      fun e he => by simp only [hsl', hn, homeS, hh]; exact h2 e he⟩

/-! ## The scratch reset -/

/-- The empty scratch tier: no node, and every slot at or below the base. -/
theorem tierR_empty (m : Mem) (hc : cntW S m 1 = 0)
    (hsl : ∀ j : Word, j < nSl S m 1 → slotW S m 1 j = 0) :
    TierR S R hs KP m 1 (Tbl.empty : Tbl α (Idx k) δ) := by
  refine ⟨by simp [hc, Tbl.empty], by simp [Tbl.empty], by simp [Tbl.empty],
    fun i a h => by simp [Tbl.empty] at h, fun i a h => by simp [Tbl.empty] at h,
    fun a x h => by simp [Tbl.empty] at h, fun j hj => by simp [hsl j hj],
    fun j hj hne => absurd (hsl j hj) hne, ?_⟩
  intro i hi; simp [Tbl.empty] at hi

/-- **Raising the slot base frees every scratch slot**: a slot of tier 1 holds at most
`B + 2^27` (`SlotsOKG`, the cap `134217728`), so against a base raised by `2^32` (from below
`2^62`) it reads free. -/
theorem slotW_free_raise (m m' : Mem) (tbS : Tbl α (Idx k) δ) (hT1 : TierR S R hs KP m 1 tbS)
    (hsa : m'.arr64 (tierA S.sa 1) = m.arr64 (tierA S.sa 1))
    (hlo : (rdW (m.arr64 CTL) SCB).toNat < 2 ^ 62)
    (hb : rdW (m'.arr64 CTL) SCB = rdW (m.arr64 CTL) SCB + 4294967296) :
    ∀ j : Word, j < nSl S m 1 → slotW S m' 1 j = 0 := by
  have hk : krW S.sa m' 1 = krW S.sa m 1 := by simp only [krW, koW, hsa]
  have hB : (rdW (m'.arr64 CTL) SCB).toNat = (rdW (m.arr64 CTL) SCB).toNat + 4294967296 := by
    rw [hb, UInt64.toNat_add]; simp; omega
  obtain ⟨hc, hcap, -, -, -, -, hsl, -, -⟩ := hT1
  intro j hj
  have h1 := hsl j hj
  have hc' : (cntW S m 1).toNat ≤ 134217728 := by omega
  simp only [slotW, slotV, slotRd, baseW, hsa, hb, hk] at h1 ⊢
  simp only [UInt64.mul_one] at h1 ⊢
  split at h1 <;> split <;> first | rfl | (exfalso; grind)

/-- **Zeroing the scratch table frees every scratch slot** (the slot base's wrap): with its
offset word kept and the `2 n` words of its table zero, every slot of tier 1 reads free against
any base. -/
theorem slotW_free_zero (m m' : Mem) (hG : GrowR S m)
    (hw1 : rdW (m'.arr64 (tierA S.sa 1)) 1 = rdW (m.arr64 (tierA S.sa 1)) 1)
    (hz : ∀ y : Word, (krW S.sa m 1).toNat ≤ y.toNat →
      y.toNat < (krW S.sa m 1).toNat + 2 * (knW S.sa m 1).toNat → rdW (m'.arr64 (tierA S.sa 1)) y = 0) :
    ∀ j : Word, j < nSl S m 1 → slotW S m' 1 j = 0 := by
  intro j hj
  have hk : krW S.sa m' 1 = krW S.sa m 1 := by simp only [krW, koW, hw1]
  have e := (kslot_toNat S m hG 1 (by decide) j hj).1
  have hj' : j.toNat < (nSl S m 1).toNat := UInt64.lt_iff_toNat_lt.mp hj
  have h0 := hz (krW S.sa m 1 + j * 2) (by omega) (by simp only [nSl] at hj'; omega)
  simp only [slotW, slotV, slotRd, hk, h0]
  split
  · rfl
  · exact absurd UInt64.zero_le ‹_›

/-- **A scratch reset empties the scratch tier** (`scratch_reset`): the record arrays and tier 0's
slot array stay, tier 1's slot array keeps its size and its count and offset words, and every slot
of its table reads free (the slot base raised past every old slot, `slotW_free_raise`, or the
table zeroed and the base restarted at the wrap); tier 0's count and nodes stay, tier 1's count
becomes `0`, the flag becomes `on'`. -/
theorem storeR_resetG (m m' : Mem) (on on' : Bool) (tbP tbS : Tbl α (Idx k) δ)
    (hR : StoreR S R hs KP m on tbP tbS)
    (hra : ∀ t, m'.arr64 (tierA S.ra t) = m.arr64 (tierA S.ra t))
    (hsa0 : m'.arr64 (tierA S.sa 0) = m.arr64 (tierA S.sa 0))
    (hsz1 : (m'.arr64 (tierA S.sa 1)).size = (m.arr64 (tierA S.sa 1)).size)
    (hw0 : rdW (m'.arr64 (tierA S.sa 1)) 0 = rdW (m.arr64 (tierA S.sa 1)) 0)
    (hw1 : rdW (m'.arr64 (tierA S.sa 1)) 1 = rdW (m.arr64 (tierA S.sa 1)) 1)
    (hfree : ∀ j : Word, j < nSl S m 1 → slotW S m' 1 j = 0)
    (hsz : (m'.arr64 CTL).size = (m.arr64 CTL).size)
    (hc0 : cntW S m' 0 = cntW S m 0) (hc1 : cntW S m' 1 = 0)
    (hb : (rdW (m'.arr64 CTL) SCB).toNat < 2 ^ 62 + 2 ^ 32)
    (hfl : (rdW (m'.arr64 CTL) 1 != 0) = on')
    (hR0 : ∀ i a, R m 0 i a → R m' 0 i a) (hh0 : ∀ i, hs m' 0 i = hs m 0 i)
    (hK0 : ∀ i K, KP m 0 i K → KP m' 0 i K) :
    StoreR S R hs KP m' on' tbP (Tbl.empty : Tbl α (Idx k) δ) := by
  obtain ⟨⟨hctl, -⟩, -, hT0, -, hG⟩ := hR
  have hn : knW S.sa m' 1 = knW S.sa m 1 := by simp only [knW, hw0]
  have ho : koW S.sa m' 1 = koW S.sa m 1 := by simp only [koW, hw1]
  have hG' : GrowR S m' := by
    obtain ⟨hL0, hL1⟩ := hG
    refine ⟨by simpa only [TierLay, knW, koW, hsa0] using hL0, ?_⟩
    obtain ⟨a1, a2, a3, a4⟩ := hL1
    exact ⟨by rw [hsz1]; exact a1, by rw [hn]; exact a2, by rw [hn]; exact a3,
      by rw [hn, ho, hsz1]; exact a4⟩
  refine ⟨⟨by omega, hb⟩, hfl, ?_, ?_, hG'⟩
  · exact tierR_mono S R hs KP m m' 0 tbP (hra 0) hsa0 hc0 (by simp [baseW]) hR0 hh0 hK0 hT0
  · refine tierR_empty S R hs KP m' hc1 (fun j hj => hfree j ?_)
    simpa only [nSl, hn] using hj

/-- The growth state reads only the slot arrays. -/
theorem growR_of_sa (m m' : Mem) (h : ∀ t, m'.arr64 (tierA S.sa t) = m.arr64 (tierA S.sa t))
    (hG : GrowR S m) : GrowR S m' := by
  simpa only [GrowR, TierLay, knW, koW, h] using hG

/-- The relation after an append to tier `t`, from the two tiers'. -/
theorem storeR_push (hS : S.WF) (m : Mem) (t : Word) (ht : t ≤ 1) (vs : List Word)
    (j q : Word) (hj : j < nSl S m t) (on : Bool) (tbP tbS tbP' tbS' : Tbl α (Idx k) δ)
    (hR : StoreR S R hs KP m on tbP tbS)
    (h0 : TierR S R hs KP (pushG S m t vs j (cntW S m t) q) 0 tbP')
    (h1 : TierR S R hs KP (pushG S m t vs j (cntW S m t) q) 1 tbS') :
    StoreR S R hs KP (pushG S m t vs j (cntW S m t) q) on tbP' tbS' := by
  obtain ⟨⟨hctl, hb⟩, hfl, -, -, hG⟩ := hR
  have := hS.ca
  have := hS.scb
  refine ⟨⟨?_, ?_⟩, ?_, h0, h1, growR_pushG S hS m t vs j _ q hG ht hj⟩
  · grind [store_grind]
  · rw [pushG_ctl S hS _ _ _ _ _ _ ht]; grind
  · rw [pushG_ctl S hS _ _ _ _ _ _ ht]; grind

/-! ## The arena protocol -/

/-- The arena's two tables of one constructor (persistent and scratch) inside `AState`, and the
scratch flag that governs them. -/
structure Lens (α δ : Type) (k : IdxKind) [BEq α] [Hashable α] where
  on : AState → Bool
  getP : AState → Tbl α (Idx k) δ
  getS : AState → Tbl α (Idx k) δ
  setP : AState → Tbl α (Idx k) δ → AState
  setS : AState → Tbl α (Idx k) δ → AState
  on_setP : ∀ a t, on (setP a t) = on a
  on_setS : ∀ a t, on (setS a t) = on a
  getP_setP : ∀ a t, getP (setP a t) = t
  getS_setP : ∀ a t, getS (setP a t) = getS a
  getP_setS : ∀ a t, getP (setS a t) = getP a
  getS_setS : ∀ a t, getS (setS a t) = t

/-- **The run of the arena's hash-consing** of key `key` with tag `tag`: the persistent probe
`pf` (`none` when skipped), the scratch probe when the scratch tier is open, the capacity test,
the append (derived word `d`) to the tier the store is in. `internNodeE`, `internLNode`, … are
this, by an instance's unfolding lemma. -/
def protoRun (L : Lens α δ k) (key : α) (tag : UInt32) (pf : Option (Idx k)) (d : δ)
    (err : CheckError) (a : AState) : Except CheckError (Idx k × AState) :=
  match pf with
  | some h => .ok (h, a)
  | none =>
    if L.on a then
      match (L.getS a).cons[key]? with
      | some h => .ok (h, a)
      | none =>
        if (L.getS a).size < Idx.idxCap then
          .ok (Idx.mk tag Idx.tierS (UInt32.ofNat (L.getS a).size),
            L.setS a ((L.getS a).push key d (Idx.mk tag Idx.tierS (UInt32.ofNat (L.getS a).size))))
        else .error err
    else
      if (L.getP a).size < Idx.idxCap then
        .ok (Idx.mk tag Idx.tierP (UInt32.ofNat (L.getP a).size),
          L.setP a ((L.getP a).push key d (Idx.mk tag Idx.tierP (UInt32.ofNat (L.getP a).size))))
      else .error err

section protocol
variable (L : Lens α δ k) (key : α) (tag : UInt32) (d : δ) (err : CheckError)
  (a : AState) (y : Idx k)

theorem protoRun_hitP : protoRun L key tag (some y) d err a = .ok (y, a) := rfl

theorem protoRun_hitS (hs : L.on a = true) (h1 : (L.getS a).cons[key]? = some y) :
    protoRun L key tag none d err a = .ok (y, a) := by
  simp [protoRun, hs, h1]

theorem protoRun_pushS (hs : L.on a = true) (h1 : (L.getS a).cons[key]? = none)
    (hc : (L.getS a).nodes.size < 134217728) :
    protoRun L key tag none d err a =
      .ok (decI (hdW tag.toUInt64 1 (UInt64.ofNat (L.getS a).nodes.size)),
        L.setS a ((L.getS a).push key d
          (decI (hdW tag.toUInt64 1 (UInt64.ofNat (L.getS a).nodes.size))))) := by
  simp only [protoRun, hs, h1, ↓reduceIte, Tbl.size, Idx.idxCap, hc,
    show Idx.tierS = UInt32.ofNat 1 from rfl, mk_eq]
  rfl

theorem protoRun_pushP (hs : L.on a = false) (hc : (L.getP a).nodes.size < 134217728) :
    protoRun L key tag none d err a =
      .ok (decI (hdW tag.toUInt64 0 (UInt64.ofNat (L.getP a).nodes.size)),
        L.setP a ((L.getP a).push key d
          (decI (hdW tag.toUInt64 0 (UInt64.ofNat (L.getP a).nodes.size))))) := by
  simp only [protoRun, hs, Bool.false_eq_true, ↓reduceIte, Tbl.size, Idx.idxCap, hc,
    show Idx.tierP = UInt32.ofNat 0 from rfl, mk_eq]
  rfl

end protocol

end rel

end L.Arena
