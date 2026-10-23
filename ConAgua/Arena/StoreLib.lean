import ConAgua.Arena.StoreRel

/-!
# The store library: one relation for every open-addressing node table

con-ron's arena keeps each node constructor in a `Tbl α ι δ` per tier (records, derived words, a
cons `Std.HashMap`). Its L twin (`Store.lean`, `AppStore.lean`, `LevelStore.lean`) is the same for
every constructor up to a **record schema** (`Schema`): a word array of records, `w` words per
node and tier, the two tiers interleaved (node `i` of tier `t` at `ra[i * st + t * w ..]`, `st =
2 w`); a word array of slots (slot `j` of tier `t` at `sa[2 j + t]`, `0` free, `i + 1` node `i`,
linear probing from `homeW`); the node count of tier `t` at `CTL[ca + t]`; the handle tag.

This file states the relation and proves the representation facts once, for any schema:

* **Reads and the append**: `fld`, `slotW`, `nSl`, `cntW`; `pushG` (the memory after an append,
  the record written from a list of words) and one read equation per array.
* **The probe**: `ProbeOKG` for any match function, from the probe's unfolding (`probe_homeG`).
* **The relation** `TierR` (one tier) and `StoreR` (two tiers and the scratch flag), parametric in
  the record relation `R` and the node hash `hs`; `tierR_hit`, `tierR_miss`, `tierR_push`,
  `tierR_other`.
* **The arena protocol**: `protoRun`, the run of the arena's hash-consing (probe the persistent
  tier unless skipped, probe the scratch tier when open, append), over a `Lens` on the two tables;
  `internM`, the L model of an `intern_*` function; `intern_correctG`, the refinement of one by the
  other.

A table instance supplies: the schema, its record relation and hash, a frame lemma (`RFrame`),
and for each query the match facts (`MatchOK`) and the new record (`NewOK`).

**Parametric strides.** `grind` decides the address disequalities when strides are numerals
(`i * 8 + t * 4 + f`), not when they are variables (nonlinear). `Schema.ad_inj` (by hand, once)
is the one fact the generic proofs need; given it, `grind` does the rest.
-/

open ConRon.Arena

set_option linter.unusedSimpArgs false

namespace L.Arena

/-! ## Schemas and addresses -/

/-- A record schema: the record array, the slot array, the words per record `w`, the stride
`st = 2 w`, the `CTL` index of tier 0's node count, the handle tag. -/
structure Schema where
  ra : ArrId
  sa : ArrId
  w : Word
  st : Word
  ca : Word
  tag : UInt32

/-- What the generic lemmas need of a schema. -/
structure Schema.WF (S : Schema) : Prop where
  st : S.st.toNat = 2 * S.w.toNat
  w_le : S.w.toNat ≤ 256
  ca : 2 ≤ S.ca.toNat ∧ S.ca.toNat < 2 ^ 32
  ra_sa : S.ra ≠ S.sa
  ra_ctl : S.ra ≠ CTL
  sa_ctl : S.sa ≠ CTL
  tag : S.tag.toNat < 16
  scb : S.ca ≠ SCB ∧ S.ca + 1 ≠ SCB ∧ S.ca ≠ 1 ∧ S.ca + 1 ≠ 1

/-- The address of word `f` of node `i` of tier `t`. -/
def Schema.ad (S : Schema) (t i f : Word) : Word := i * S.st + t * S.w + f

theorem Schema.ad_toNat (S : Schema) (hS : S.WF) (t i f : Word) (ht : t ≤ 1)
    (hi : i.toNat < 2 ^ 27) (hf : f < S.w) :
    (S.ad t i f).toNat = (i.toNat * 2 + t.toNat) * S.w.toNat + f.toNat := by
  have h1 := hS.st
  have h2 := hS.w_le
  have : t.toNat ≤ 1 := by grind
  have : f.toNat < S.w.toNat := by grind
  have a1 : i.toNat * S.st.toNat ≤ 2 ^ 27 * 512 := Nat.mul_le_mul (by omega) (by omega)
  have a2 : t.toNat * S.w.toNat ≤ 1 * 256 := Nat.mul_le_mul (by omega) (by omega)
  simp only [Schema.ad, UInt64.toNat_add, UInt64.toNat_mul]
  rw [Nat.mod_eq_of_lt (a := i.toNat * S.st.toNat) (by omega),
    Nat.mod_eq_of_lt (a := t.toNat * S.w.toNat) (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), h1]
  grind

/-- **Addresses are injective** on the fields of a schema: the fact `grind` cannot find itself
when the stride is a variable. -/
theorem Schema.ad_inj (S : Schema) (hS : S.WF) (t i f t' i' f' : Word) (ht : t ≤ 1)
    (hi : i.toNat < 2 ^ 27) (hf : f < S.w) (ht' : t' ≤ 1) (hi' : i'.toNat < 2 ^ 27)
    (hf' : f' < S.w) (h : S.ad t i f = S.ad t' i' f') : t = t' ∧ i = i' ∧ f = f' := by
  have e := congrArg UInt64.toNat h
  rw [S.ad_toNat hS t i f ht hi hf, S.ad_toNat hS t' i' f' ht' hi' hf'] at e
  have hf1 : f.toNat < S.w.toNat := by grind
  have hf2 : f'.toNat < S.w.toNat := by grind
  have q := congrArg (· / S.w.toNat) e
  simp only [Nat.mul_comm _ S.w.toNat, Nat.mul_add_div (show 0 < S.w.toNat by omega),
    Nat.div_eq_of_lt hf1, Nat.div_eq_of_lt hf2] at q
  rw [show i.toNat * 2 + t.toNat = i'.toNat * 2 + t'.toNat by omega] at e
  have : t.toNat ≤ 1 := by grind
  have : t'.toNat ≤ 1 := by grind
  refine ⟨?_, ?_, ?_⟩ <;> apply UInt64.toNat_inj.mp <;> omega

/-! ## Reads -/

section reads
variable (S : Schema) (m : Mem)

/-- Word `f` of node `i` of tier `t`. -/
def fld (t i f : Word) : Word := rdW (m.arr64 S.ra) (S.ad t i f)
/-- Slot `j` of tier `t`, against the tier's slot base (`slotV`, `baseW`): `0` free, `i + 1` node
`i`. -/
def slotW (t j : Word) : Word := slotV (m.arr64 S.sa) (baseW m t) (j * 2 + t)
/-- The slot count of a tier: `G + SN0`, `G` the slot array's last word (`SlotGrowSpec.lean`). -/
def nSl : Word := gnW S.sa m
/-- The node count of tier `t`. -/
def cntW (t : Word) : Word := rdW (m.arr64 CTL) (S.ca + t)
/-- The home slot of a hash. -/
def homeS (h : Word) : Word := homeW h (nSl S m)

/-- The room an append needs: a handle index and a record. -/
def PushRoom (t : Word) : Prop :=
  (cntW S m t).toNat < 2 ^ 27 ∧ S.st.toNat * ((cntW S m t).toNat + 1) ≤ (m.arr64 S.ra).size

/-- **The slot array's growth state**: the slot count is a multiple of 8 below `2^62`, the two
tiers' slots and the last word fit, and the words between them are zero (no write reaches them). -/
def GrowR : Prop :=
  (gexpW S.sa m).toNat + 8 < 2 ^ 62 ∧ (nSl S m).toNat % 8 = 0 ∧
  2 * (nSl S m).toNat + 1 ≤ (m.arr64 S.sa).size ∧ (m.arr64 S.sa).size < 2 ^ 63 ∧
  ∀ k : Word, 2 * (nSl S m).toNat ≤ k.toNat → k.toNat + 1 < (m.arr64 S.sa).size →
    rdW (m.arr64 S.sa) k = 0

end reads

attribute [store_grind] homeS

/-! ## The append -/

/-- Write the words `vs` into node `c` of tier `t`, from word `f`. -/
def wrRec (S : Schema) (t c : Word) : Mem → Word → List Word → Mem
  | m, _, [] => m
  | m, f, v :: vs => wrRec S t c (m.set64 S.ra (S.ad t c f) v) (f + 1) vs

/-- The memory after appending node `c` (record `vs`) to tier `t`, registered at slot `j`. -/
def pushG (S : Schema) (m : Mem) (t : Word) (vs : List Word) (j c : Word) : Mem :=
  ((wrRec S t c m 0 vs).set64 S.sa (j * 2 + t) (baseW m t + c + 1)).set64 CTL (S.ca + (t &&& 1))
    (c + 1)

theorem wrRec_arr_ne (S : Schema) (t c : Word) (b : ArrId) (hb : b ≠ S.ra) :
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

theorem wrRec_read (S : Schema) (hS : S.WF) (t c t' i f : Word) (ht : t ≤ 1) (hc : c.toNat < 2 ^ 27)
    (ht' : t' ≤ 1) (hi : i.toNat < 2 ^ 27) (hf : f < S.w) :
    ∀ (vs : List Word) (m : Mem) (f₀ : Word), f₀.toNat + vs.length ≤ S.w.toNat →
      rdW ((wrRec S t c m f₀ vs).arr64 S.ra) (S.ad t' i f) =
        if t' = t ∧ i = c ∧ f₀.toNat ≤ f.toNat ∧ f.toNat < f₀.toNat + vs.length ∧
            (S.ad t c f).toNat < (m.arr64 S.ra).size
        then vs.getD (f.toNat - f₀.toNat) 0 else rdW (m.arr64 S.ra) (S.ad t' i f) := by
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
    have := S.ad_inj hS t c f₀ t' i f ht hc hf₀ ht' hi hf
    by_cases hf0 : f.toNat = f₀.toNat
    · have : f = f₀ := UInt64.toNat_inj.mp hf0
      subst this
      grind
    by_cases hlt : f.toNat < f₀.toNat
    · grind
    · have : f.toNat - f₀.toNat = f.toNat - (f₀.toNat + 1) + 1 := by omega
      simp only [List.length_cons, this, List.getD_cons_succ]
      grind

section push
variable (S : Schema) (hS : S.WF) (m : Mem) (t : Word) (vs : List Word) (j c : Word)

theorem pushG_arr (b : ArrId) (h1 : b ≠ S.ra) (h2 : b ≠ S.sa) (h3 : b ≠ CTL) :
    (pushG S m t vs j c).arr64 b = m.arr64 b := by
  rw [pushG, Mem.arr64_set64_ne _ _ _ _ _ h3, Mem.arr64_set64_ne _ _ _ _ _ h2,
    wrRec_arr_ne _ _ _ _ h1]

@[store_grind =] theorem pushG_size (b : ArrId) :
    ((pushG S m t vs j c).arr64 b).size = (m.arr64 b).size := by
  rw [pushG, size_set64, size_set64, wrRec_size]

theorem wrRec_words (S : Schema) (t c : Word) :
    ∀ (vs : List Word) (m : Mem) (f : Word), (wrRec S t c m f vs).words.size = m.words.size := by
  intro vs
  induction vs with
  | nil => intro m f; rfl
  | cons v vs ih => intro m f; rw [wrRec, ih, Mem.words_size_set64]

@[store_grind =] theorem pushG_words : (pushG S m t vs j c).words.size = m.words.size := by
  rw [pushG, Mem.words_size_set64, Mem.words_size_set64, wrRec_words]

include hS in
@[store_grind =] theorem pushG_ctl (ht : t ≤ 1) (x : Word) :
    rdW ((pushG S m t vs j c).arr64 CTL) x =
      if x = S.ca + t ∧ (S.ca + t).toNat < (m.arr64 CTL).size then c + 1
      else rdW (m.arr64 CTL) x := by
  rw [pushG, rdW_set64, rdW_set64, size_set64, wrRec_size, wrRec_arr_ne _ _ _ _ hS.ra_ctl.symm,
    and_one_of_le t ht]
  have := hS.sa_ctl
  grind

include hS in
@[store_grind =] theorem pushG_slot (x : Word) :
    rdW ((pushG S m t vs j c).arr64 S.sa) x =
      if x = j * 2 + t ∧ (j * 2 + t).toNat < (m.arr64 S.sa).size then baseW m t + c + 1
      else rdW (m.arr64 S.sa) x := by
  rw [pushG, rdW_set64, rdW_set64, wrRec_size, wrRec_arr_ne _ _ _ _ hS.ra_sa.symm]
  have := hS.sa_ctl
  grind

include hS in
/-- The slot bases survive an append (`CTL[62]` is not a count). -/
@[store_grind =] theorem baseW_pushG (ht : t ≤ 1) (t' : Word) :
    baseW (pushG S m t vs j c) t' = baseW m t' := by
  have := hS.scb
  simp only [baseW]
  rw [pushG_ctl S hS m t vs j c ht]
  have : SCB ≠ S.ca + t := by
    rcases (show t = 0 ∨ t = 1 by grind) with rfl | rfl <;> grind
  simp [this]

include hS in
/-- A slot word after the append, against any base. -/
@[store_grind =] theorem slotV_pushG (b x : Word) :
    slotV ((pushG S m t vs j c).arr64 S.sa) b x =
      if x = j * 2 + t ∧ (j * 2 + t).toNat < (m.arr64 S.sa).size then slotRd (baseW m t + c + 1) b
      else slotV (m.arr64 S.sa) b x := by
  simp only [slotV, pushG_slot S hS m t vs j c]
  split <;> rfl

/-- The new slot reads `c + 1` against its own base, when the base leaves room for the index
(`CTL[62] < 2^63`, a clause of `StoreR`). -/
@[store_grind =] theorem slotV_new (ht : t ≤ 1) (hb : (rdW (m.arr64 CTL) SCB).toNat < 2 ^ 63)
    (hc : c.toNat < 2 ^ 27) : slotRd (baseW m t + c + 1) (baseW m t) = c + 1 := by
  simp only [slotRd]
  have : (baseW m t).toNat < 2 ^ 63 := by
    simp only [baseW]
    rcases (show t = 0 ∨ t = 1 by grind) with rfl | rfl <;> simp [hb]
  grind

include hS in
/-- A field after the append: the new record's, or the old. -/
@[store_grind =] theorem fld_pushG (t' i f : Word) (ht : t ≤ 1) (hc : c.toNat < 2 ^ 27)
    (ht' : t' ≤ 1) (hi : i.toNat < 2 ^ 27) (hf : f < S.w) (hl : vs.length = S.w.toNat) :
    fld S (pushG S m t vs j c) t' i f =
      if t' = t ∧ i = c ∧ (S.ad t c f).toNat < (m.arr64 S.ra).size then vs.getD f.toNat 0
      else fld S m t' i f := by
  have := hS.ra_ctl
  have := hS.ra_sa
  rw [fld, pushG, Mem.arr64_set64_ne _ _ _ _ _ hS.ra_ctl, Mem.arr64_set64_ne _ _ _ _ _ hS.ra_sa,
    wrRec_read S hS t c t' i f ht hc ht' hi hf vs m 0 (by simp [hl])]
  simp only [fld, UInt64.toNat_zero, Nat.zero_le, true_and, Nat.sub_zero, Nat.zero_add, hl]
  grind

end push

/-! ## The slot count across an append -/

theorem nSl_toNat (S : Schema) (m : Mem) (hG : GrowR S m) :
    (nSl S m).toNat = (gexpW S.sa m).toNat + 8 := by
  have := hG.1
  simp only [nSl, gnW, SN0, UInt64.toNat_add]; simp; omega

section pushGrow
variable (S : Schema) (hS : S.WF) (m : Mem) (t : Word) (vs : List Word) (j c : Word)

include hS in
/-- An append's slot write lies below the exponent word and the zero words. -/
theorem pushG_slot_lt (hG : GrowR S m) (ht : t ≤ 1) (hj : j < nSl S m) :
    (j * 2 + t).toNat < 2 * (nSl S m).toNat ∧ (j * 2 + t).toNat = j.toNat * 2 + t.toNat := by
  have hn := nSl_toNat S m hG
  have := hG.1
  have hj' : j.toNat < (nSl S m).toNat := UInt64.lt_iff_toNat_lt.mp hj
  have : t.toNat ≤ 1 := UInt64.le_iff_toNat_le.mp ht
  have e : (j * 2 + t).toNat = j.toNat * 2 + t.toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_mul]; simp; omega
  omega

include hS in
/-- An append leaves the exponent word, so the slot count. -/
theorem gexpW_pushG (hG : GrowR S m) (ht : t ≤ 1) (hj : j < nSl S m) :
    gexpW S.sa (pushG S m t vs j c) = gexpW S.sa m := by
  have := pushG_slot_lt S hS m t j hG ht hj
  have h1 := hG.2.2.1
  have h2 := hG.2.2.2.1
  simp only [gexpW, len64_eq, pushG_size]
  rw [pushG_slot S hS]
  have hsz : (m.arr64 S.sa).size < UInt64.size := by simp only [UInt64.size]; omega
  have : (UInt64.ofNat (m.arr64 S.sa).size - 1).toNat = (m.arr64 S.sa).size - 1 := by
    rw [UInt64.toNat_sub_of_le]
    · rw [UInt64.toNat_ofNat_of_lt' hsz]; rfl
    · rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hsz]; simp; omega
  have : UInt64.ofNat (m.arr64 S.sa).size - 1 ≠ j * 2 + t := fun h => by
    have := congrArg UInt64.toNat h; omega
  simp [this]

include hS in
theorem nSl_pushG (hG : GrowR S m) (ht : t ≤ 1) (hj : j < nSl S m) :
    nSl S (pushG S m t vs j c) = nSl S m := by
  simp only [nSl, gnW]; rw [gexpW_pushG S hS m t vs j c hG ht hj]

include hS in
/-- An append keeps the growth state. -/
theorem growR_pushG (hG : GrowR S m) (ht : t ≤ 1) (hj : j < nSl S m) :
    GrowR S (pushG S m t vs j c) := by
  have hl := pushG_slot_lt S hS m t j hG ht hj
  have hn := nSl_pushG S hS m t vs j c hG ht hj
  obtain ⟨g1, g5, g2, g4, g3⟩ := hG
  refine ⟨by rw [gexpW_pushG S hS m t vs j c ⟨g1, g5, g2, g4, g3⟩ ht hj]; exact g1, by rw [hn]; exact g5,
    ?_, ?_, ?_⟩
  · rw [hn, pushG_size]; exact g2
  · rw [pushG_size]; exact g4
  · intro k hk1 hk2
    rw [hn] at hk1; rw [pushG_size] at hk2
    rw [pushG_slot S hS]
    have : k ≠ j * 2 + t := fun h => by subst h; omega
    simp only [this, false_and, ↓reduceIte]
    exact g3 k hk1 hk2

end pushGrow

/-! ## The probe -/

section probe
variable (S : Schema) (m : Mem) (t : Word) (mt : Word → Bool)

/-- One step of the probe of tier `t` for a node `mt` accepts, `P` the rest: the shape of every
`*_find` model. -/
def probeArm (P : Word → Word → List Word) (j d : Word) : List Word :=
  if d < nSl S m then
    if slotW S m t j = 0 then [0, 0, j, d]
    else if mt (slotW S m t j - 1) then [1, slotW S m t j - 1, j, d]
    else P ((j + 1) * (if j + 1 < nSl S m then 1 else 0)) (d + 1)
  else []

/-- The first `d` slots of the run from `x` hold nodes that do not match. -/
def NoMatchG (x : Word) (d : Nat) : Prop :=
  ∀ e < d, slotW S m t (walkW (nSl S m) x e) ≠ 0 ∧
    mt (slotW S m t (walkW (nSl S m) x e) - 1) = false

/-- What a result `rs` of the probe from slot `x` says: a hit (`rs[0] ≠ 0`) is a matching node
`rs[1]` in an occupied slot `rs[2]`; a miss is the free slot `rs[2]`, step `rs[3]` of the run,
after nodes that do not match. -/
def ProbeOKG (x : Word) (rs : List Word) : Prop :=
  rs ≠ [] →
    (rs.headD 0 ≠ 0 → mt (rs.tail.headD 0) = true ∧
      slotW S m t (rs.tail.tail.headD 0) = rs.tail.headD 0 + 1 ∧
      slotW S m t (rs.tail.tail.headD 0) ≠ 0 ∧ rs.tail.tail.headD 0 < nSl S m) ∧
    (rs.headD 0 = 0 →
      rs.tail.tail.headD 0 = walkW (nSl S m) x (rs.tail.tail.tail.headD 0).toNat ∧
      rs.tail.tail.headD 0 < nSl S m ∧
      slotW S m t (rs.tail.tail.headD 0) = 0 ∧ NoMatchG S m t mt x (rs.tail.tail.tail.headD 0).toNat)

theorem probe_okG (P : Word → Word → List Word) (hP : ∀ j d, P j d = probeArm S m t mt P j d)
    (x : Word) (hx : x < nSl S m) :
    ∀ (k : Nat) (d : Word), (nSl S m).toNat - d.toNat = k → NoMatchG S m t mt x d.toNat →
      ProbeOKG S m t mt x (P (walkW (nSl S m) x d.toNat) d) := by
  intro k
  induction k with
  | zero => intro d hk _; rw [hP, probeArm]; grind [ProbeOKG]
  | succ k ih =>
    intro d hk hnm
    have := ih (d + 1)
    clear ih
    have hd : d < nSl S m := by grind
    have hd1 : (d + 1).toNat = d.toNat + 1 := by grind
    specialize this (by grind)
    rw [hd1, walkW_succ] at this
    rw [hP, probeArm]
    by_cases h0 : slotW S m t (walkW (nSl S m) x d.toNat) = 0
    · simp only [hd, h0, ↓reduceIte]; grind [store_grind, ProbeOKG]
    by_cases hm : mt (slotW S m t (walkW (nSl S m) x d.toNat) - 1)
    · simp only [hd, h0, hm, ↓reduceIte]; grind [store_grind, ProbeOKG]
    · simp only [hd, h0, hm, ↓reduceIte, Bool.false_eq_true]
      exact this (by grind [NoMatchG])

/-- The probe from the home slot of `h`. -/
theorem probe_homeG (P : Word → Word → List Word) (hP : ∀ j d, P j d = probeArm S m t mt P j d)
    (h : Word) : ProbeOKG S m t mt (homeS S m h) (P (homeS S m h) 0) := by
  by_cases hn : nSl S m = 0
  · rw [hP, probeArm]; simp [hn, ProbeOKG]
  · exact probe_okG S m t mt P hP _ (homeW_lt _ _ (by grind)) _ 0 rfl (by simp [NoMatchG])

end probe

/-! ## The relation -/

section rel
variable {α δ : Type} {k : IdxKind} [BEq α] [Hashable α]
variable (S : Schema) (R : Mem → Word → Word → α → Prop) (hs : Mem → Word → Word → Word)

/-- The slots of tier `t` index its `c` nodes, and node `i` lies on the run from its home slot
(the home of its hash `hs m t i`), after occupied slots: linear probing without deletion. -/
def SlotsOKG (m : Mem) (t : Word) (c : Nat) : Prop :=
  (∀ j : Word, j < nSl S m → (slotW S m t j).toNat ≤ c) ∧
  ∀ i : Word, i.toNat < c → ∃ d : Nat,
    slotW S m t (walkW (nSl S m) (homeS S m (hs m t i)) d) = i + 1 ∧
    ∀ e < d, slotW S m t (walkW (nSl S m) (homeS S m (hs m t i)) e) ≠ 0

/-- **Tier `t` of an L table represents the arena table `tb`**: the same nodes in the same order
(node `i` holds `tb.nodes[i]` by `R`), the same key → handle map (each node's key maps to its
handle, each entry points at a node with its key), and the slots index the nodes. -/
def TierR (m : Mem) (t : Word) (tb : Tbl α (Idx k) δ) : Prop :=
  (cntW S m t).toNat = tb.nodes.size ∧ tb.nodes.size ≤ 134217728 ∧
  S.st.toNat * tb.nodes.size ≤ (m.arr64 S.ra).size ∧
  (∀ (i : Word) a, tb.nodes[i.toNat]? = some a → R m t i a) ∧
  (∀ (i : Word) a, tb.nodes[i.toNat]? = some a →
    tb.cons[a]? = some (decI (hdW S.tag.toUInt64 t i))) ∧
  (∀ a x, tb.cons[a]? = some x → tb.nodes[(hix x).toNat]? = some a) ∧
  SlotsOKG S hs m t tb.nodes.size

/-- **The relation of a two-tier table**: the counts fit in `CTL` and the scratch tier's slot base
`CTL[62]` leaves room for node indices, the scratch flag `CTL[1]` is `on`, both tiers represent
their tables. -/
def StoreR (m : Mem) (on : Bool) (tbP tbS : Tbl α (Idx k) δ) : Prop :=
  (S.ca.toNat + 2 ≤ (m.arr64 CTL).size ∧ (rdW (m.arr64 CTL) SCB).toNat < 2 ^ 63) ∧
  (rdW (m.arr64 CTL) 1 != 0) = on ∧
  TierR S R hs m 0 tbP ∧ TierR S R hs m 1 tbS ∧ GrowR S m

/-- `m'` agrees with `m` outside the table's arrays and `CTL`, and at the pool top `CTL[0]`. -/
def OutEq (m m' : Mem) : Prop :=
  (∀ b, b ≠ S.ra → b ≠ S.sa → b ≠ CTL → m'.arr64 b = m.arr64 b) ∧
  rdW (m'.arr64 CTL) 0 = rdW (m.arr64 CTL) 0

/-- **The instance's frame obligation**: a node's relation and hash depend on its own words and
on memory outside the table. -/
def RFrame : Prop :=
  ∀ m m' t i, OutEq S m m' → (∀ f, f < S.w → fld S m' t i f = fld S m t i f) →
    (∀ a, R m t i a → R m' t i a) ∧ hs m' t i = hs m t i

/-- **The query's match obligation**: on a node of the table, the match is key equality. -/
def MatchOK (mt : Word → Word → Bool) (m : Mem) (key : α) : Prop :=
  ∀ t i a, R m t i a → (mt t i = true ↔ a = key)

/-- A matching node has the query's hash. -/
def HomeOK (mt : Word → Word → Bool) (m : Mem) (qh : Word) : Prop :=
  ∀ t i, mt t i = true → hs m t i = qh

/-- **The query's append obligation**: the record `vs` written as the new node of tier `t` holds
the key, with the query's hash. -/
def NewOK (m : Mem) (vs : List Word) (key : α) (qh : Word) : Prop :=
  ∀ t j, t ≤ 1 → PushRoom S m t →
    R (pushG S m t vs j (cntW S m t)) t (cntW S m t) key ∧
    hs (pushG S m t vs j (cntW S m t)) t (cntW S m t) = qh

theorem outEq_pushG (hS : S.WF) (m : Mem) (t : Word) (ht : t ≤ 1) (vs : List Word) (j c : Word) :
    OutEq S m (pushG S m t vs j c) := by
  have := hS.ca
  refine ⟨fun b h1 h2 h3 => pushG_arr S m t vs j c b h1 h2 h3, ?_⟩
  rw [pushG_ctl S hS _ _ _ _ _ ht]
  grind

/-! ### Hit and miss -/

section tier
variable (m : Mem) (t : Word) (tb : Tbl α (Idx k) δ) (hT : TierR S R hs m t tb)
  (mt : Word → Word → Bool) (key : α) (hM : MatchOK R mt m key)

include hT hM in
/-- A probe hit is the arena's cons hit, at the same handle. -/
theorem tierR_hit (x : Word) (rs : List Word) (hP : ProbeOKG S m t (mt t) x rs) (hr : rs ≠ [])
    (hh : rs.headD 0 ≠ 0) :
    tb.cons[key]? = some (decI (hdW S.tag.toUInt64 t (rs.tail.headD 0))) := by
  obtain ⟨hm, hs1, hs2, hj⟩ := (hP hr).1 hh
  obtain ⟨-, hcap, -, hrec, hsome, -, ⟨hsl, -⟩⟩ := hT
  have h1 := hsl _ hj
  have hi : (rs.tail.headD 0).toNat < tb.nodes.size := by grind
  obtain ⟨a, ha⟩ : ∃ a, tb.nodes[(rs.tail.headD 0).toNat]? = some a :=
    ⟨_, Array.getElem?_eq_getElem hi⟩
  have := (hM t _ a (hrec _ a ha)).mp hm
  subst this
  exact hsome _ _ ha

include hT hM in
/-- A probe miss from the home slot: the key is not in the tier. -/
theorem tierR_miss (qh : Word) (hH : HomeOK hs mt m qh) (rs : List Word)
    (hP : ProbeOKG S m t (mt t) (homeS S m qh) rs) (hr : rs ≠ []) (hh : rs.headD 0 = 0) :
    tb.cons[key]? = none := by
  cases hc : tb.cons[key]? with
  | none => rfl
  | some x =>
    exfalso
    obtain ⟨-, hcap, -, hrec, -, hback, -, hrun⟩ := hT
    have hn := hback key x hc
    have hR := hrec (hix x) key hn
    have hm := (hM t (hix x) key hR).mpr rfl
    have hq := hH t (hix x) hm
    obtain ⟨d, hd1, hd2⟩ := hrun (hix x) (by grind)
    clear hrec hback hrun hM hH
    grind [ProbeOKG, NoMatchG]

end tier

/-! ### The append -/

theorem tierR_push [LawfulBEq α] (hS : S.WF) (hfr : RFrame S R hs) (m : Mem) (t : Word) (ht : t ≤ 1)
    (tb : Tbl α (Idx k) δ) (hT : TierR S R hs m t tb) (mt : Word → Word → Bool) (key : α)
    (hM : MatchOK R mt m key) (qh : Word) (hH : HomeOK hs mt m qh) (rs : List Word)
    (hP : ProbeOKG S m t (mt t) (homeS S m qh) rs) (hr : rs ≠ []) (hh : rs.headD 0 = 0)
    (hroom : PushRoom S m t) (hctl : S.ca.toNat + 2 ≤ (m.arr64 CTL).size)
    (hb : (rdW (m.arr64 CTL) SCB).toNat < 2 ^ 63) (vs : List Word)
    (hl : vs.length = S.w.toNat) (hN : NewOK S R hs m vs key qh) (dd : δ) (hG : GrowR S m) :
    TierR S R hs (pushG S m t vs (rs.tail.tail.headD 0) (cntW S m t)) t
      (tb.push key dd (decI (hdW S.tag.toUInt64 t (cntW S m t)))) := by
  have hmiss := tierR_miss S R hs m t tb hT mt key hM qh hH rs hP hr hh
  have hjn : rs.tail.tail.headD 0 < nSl S m := ((hP hr).2 hh).2.1
  have hnS := nSl_pushG S hS m t vs (rs.tail.tail.headD 0) (cntW S m t) hG ht hjn
  have hjl := pushG_slot_lt S hS m t (rs.tail.tail.headD 0) hG ht hjn
  have hG2 := hG.2.2.1
  have hnew := hN t (rs.tail.tail.headD 0) ht hroom
  have hca := hS.ca
  have hst := hS.st
  have htag : S.tag.toUInt64 < 16 := by have := hS.tag; grind
  have hout := outEq_pushG S hS m t ht vs (rs.tail.tail.headD 0) (cntW S m t)
  obtain ⟨hc, hcap, hrs, hrec, hsome, hback, hsl, hrun⟩ := hT
  simp only [TierR, SlotsOKG, Tbl.push_nodes, Tbl.push_cons, Array.size_push]
  have hctr : (S.ca + t).toNat < (m.arr64 CTL).size := by grind
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · clear hrec hsome hback hsl hrun; grind [store_grind, cntW, PushRoom]
  · clear hrec hsome hback hsl hrun; grind [store_grind, PushRoom]
  · clear hrec hsome hback hsl hrun; grind [store_grind, PushRoom]
  · intro i a hk
    rw [Array.getElem?_push] at hk
    split at hk
    · cases hk
      have : i = cntW S m t := UInt64.toNat_inj.mp (by omega)
      subst this
      exact hnew.1
    · have hi : i ≠ cntW S m t := fun h => by subst h; omega
      refine (hfr m _ t i hout (fun f hf => ?_)).1 a (hrec i a hk)
      rw [fld_pushG S hS] <;> grind [PushRoom]
  · intro i a hk
    clear hrec hback hsl hrun
    grind [store_grind, PushRoom]
  · intro a x hk
    clear hrec hsome hsl hrun
    grind [store_grind, PushRoom]
  · intro j hj
    clear hrec hsome hback hrun
    grind [store_grind, PushRoom, ProbeOKG, slotW]
  · intro i hi
    clear hsome hback hsl
    by_cases hic : i = cntW S m t
    · subst hic
      clear hrun hrec
      refine ⟨(rs.tail.tail.tail.headD 0).toNat, ?_, ?_⟩
      · grind [store_grind, PushRoom, ProbeOKG, slotW]
      · grind [store_grind, PushRoom, ProbeOKG, NoMatchG, slotW]
    · obtain ⟨d, hd1, hd2⟩ := hrun i (by grind)
      have hhs : hs (pushG S m t vs (rs.tail.tail.headD 0) (cntW S m t)) t i = hs m t i :=
        (hfr m _ t i hout (fun f hf => by rw [fld_pushG S hS] <;> grind [PushRoom])).2
      refine ⟨d, ?_, ?_⟩
      · clear hrec hrun; grind [store_grind, PushRoom, ProbeOKG, slotW]
      · clear hrec hrun; grind [store_grind, PushRoom, ProbeOKG, slotW]

/-- Appending to tier `t` leaves the other tier represented. -/
theorem tierR_other (hS : S.WF) (hfr : RFrame S R hs) (m : Mem) (t t' : Word) (ht : t ≤ 1)
    (ht' : t' ≤ 1) (hne : t' ≠ t) (tb : Tbl α (Idx k) δ) (hT : TierR S R hs m t' tb)
    (hroom : PushRoom S m t) (hb : (rdW (m.arr64 CTL) SCB).toNat < 2 ^ 63) (vs : List Word)
    (hl : vs.length = S.w.toNat) (J : Word) (hG : GrowR S m) (hJ : J < nSl S m) :
    TierR S R hs (pushG S m t vs J (cntW S m t)) t' tb := by
  have hca := hS.ca
  have hnS := nSl_pushG S hS m t vs J (cntW S m t) hG ht hJ
  have hjl := pushG_slot_lt S hS m t J hG ht hJ
  have hG2 := hG.2.2.1
  have hout := outEq_pushG S hS m t ht vs J (cntW S m t)
  obtain ⟨hc, hcap, hrs, hrec, hsome, hback, hsl, hrun⟩ := hT
  have hfe : ∀ i : Word, i.toNat < tb.nodes.size → ∀ f, f < S.w →
      fld S (pushG S m t vs J (cntW S m t)) t' i f = fld S m t' i f := by
    intro i hi f hf; rw [fld_pushG S hS] <;> grind [PushRoom]
  refine ⟨?_, hcap, ?_, ?_, hsome, hback, ?_, ?_⟩
  · clear hrec hsome hback hsl hrun hfe; grind [store_grind, cntW]
  · clear hrec hsome hback hsl hrun hfe; grind [store_grind]
  · intro i a hk
    exact (hfr m _ t' i hout (hfe i (by grind))).1 a (hrec i a hk)
  · intro j hj
    clear hrec hsome hback hrun hfe
    grind [store_grind, slotW]
  · intro i hi
    obtain ⟨d, hd1, hd2⟩ := hrun i (by grind)
    have hhs := (hfr m _ t' i hout (hfe i (by grind))).2
    clear hsome hback hsl hrun hrec hfe
    refine ⟨d, ?_, ?_⟩
    · grind [store_grind, slotW]
    · grind [store_grind, slotW]

/-- A tier stays represented when its arrays and count stay and its nodes' relations and hashes
do (the pool growing under the `lit` table). -/
theorem tierR_mono (m m' : Mem) (t : Word) (tb : Tbl α (Idx k) δ)
    (hra : m'.arr64 S.ra = m.arr64 S.ra) (hsa : m'.arr64 S.sa = m.arr64 S.sa)
    (hc : cntW S m' t = cntW S m t) (hbase : baseW m' t = baseW m t)
    (hR : ∀ i a, R m t i a → R m' t i a)
    (hh : ∀ i, hs m' t i = hs m t i) (hT : TierR S R hs m t tb) : TierR S R hs m' t tb := by
  obtain ⟨hc', hcap, hrs, hrec, hsome, hback, hsl, hrun⟩ := hT
  have hn : nSl S m' = nSl S m := by simp only [nSl, gnW, gexpW, len64_eq, hsa]
  have hsl' : ∀ j, slotW S m' t j = slotW S m t j := fun j => by simp only [slotW, hsa, hbase]
  refine ⟨by rw [hc]; exact hc', hcap, by rw [hra]; exact hrs,
    fun i a h => hR i a (hrec i a h), hsome, hback, ?_, ?_⟩
  · intro j hj; rw [hsl']; exact hsl j (by rw [← hn]; exact hj)
  · intro i hi
    obtain ⟨d, h1, h2⟩ := hrun i hi
    exact ⟨d, by simp only [hsl', hn, homeS, hh]; exact h1,
      fun e he => by simp only [hsl', hn, homeS, hh]; exact h2 e he⟩

/-! ## The scratch reset -/

/-- The empty scratch tier: no node, and every slot at or below the base. -/
theorem tierR_empty (m : Mem) (hc : cntW S m 1 = 0)
    (hsl : ∀ j : Word, j < nSl S m → slotW S m 1 j = 0) : TierR S R hs m 1 (Tbl.empty : Tbl α (Idx k) δ) := by
  refine ⟨by simp [hc, Tbl.empty], by simp [Tbl.empty], by simp [Tbl.empty],
    fun i a h => by simp [Tbl.empty] at h, fun i a h => by simp [Tbl.empty] at h,
    fun a x h => by simp [Tbl.empty] at h, fun j hj => by simp [hsl j hj], ?_⟩
  intro i hi; simp [Tbl.empty] at hi

/-- **A scratch reset empties the scratch tier without touching a slot** (`scratch_reset`): the
arrays, the pool top and tier 0's count stay, the slot base `CTL[62]` rises by `2^32` (from below
`2^62`), tier 1's count becomes `0`, the flag becomes `on'`. Every old scratch slot holds at most
`B + 2^27`, so it reads free against the new base. -/
theorem storeR_reset (hS : S.WF) (hfr : RFrame S R hs) (m m' : Mem) (on on' : Bool)
    (tbP tbS : Tbl α (Idx k) δ) (hR : StoreR S R hs m on tbP tbS)
    (harr : ∀ b, b ≠ CTL → m'.arr64 b = m.arr64 b)
    (hsz : (m'.arr64 CTL).size = (m.arr64 CTL).size)
    (h0 : rdW (m'.arr64 CTL) 0 = rdW (m.arr64 CTL) 0)
    (hc0 : cntW S m' 0 = cntW S m 0) (hc1 : cntW S m' 1 = 0)
    (hlo : (rdW (m.arr64 CTL) SCB).toNat < 2 ^ 62)
    (hb : rdW (m'.arr64 CTL) SCB = rdW (m.arr64 CTL) SCB + 4294967296)
    (hfl : (rdW (m'.arr64 CTL) 1 != 0) = on') :
    StoreR S R hs m' on' tbP (Tbl.empty : Tbl α (Idx k) δ) := by
  obtain ⟨⟨hctl, -⟩, -, hT0, hT1, hG⟩ := hR
  have hra := harr S.ra hS.ra_ctl
  have hsa := harr S.sa hS.sa_ctl
  have hG' : GrowR S m' := by
    simp only [GrowR, nSl, gnW, gexpW, len64_eq, hsa]; exact hG
  have hB : (rdW (m'.arr64 CTL) SCB).toNat = (rdW (m.arr64 CTL) SCB).toNat + 4294967296 := by
    rw [hb, UInt64.toNat_add]; simp; omega
  have hout : OutEq S m m' := ⟨fun b _ _ hc => harr b hc, h0⟩
  have hfld : ∀ t i f, f < S.w → fld S m' t i f = fld S m t i f := fun t i f _ => by
    simp only [fld, hra]
  refine ⟨⟨by omega, by omega⟩, hfl, ?_, ?_, hG'⟩
  · exact tierR_mono S R hs m m' 0 tbP hra hsa hc0 (by simp [baseW])
      (fun i a h => (hfr m m' 0 i hout (hfld 0 i)).1 a h) (fun i => (hfr m m' 0 i hout (hfld 0 i)).2) hT0
  · have hn : nSl S m' = nSl S m := by simp only [nSl, gnW, gexpW, len64_eq, hsa]
    obtain ⟨hc, hcap, -, -, -, -, hsl, -⟩ := hT1
    refine tierR_empty S R hs m' hc1 (fun j hj => ?_)
    rw [hn] at hj
    have h1 := hsl j hj
    have hc' : (cntW S m 1).toNat ≤ 134217728 := by omega
    simp only [slotW, slotV, slotRd, baseW, hsa, hb] at h1 ⊢
    simp only [UInt64.mul_one] at h1 ⊢
    split at h1 <;> split <;> first | rfl | (exfalso; grind)

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

/-- The append of the record `vs` to tier `t` at slot `j`, then the growth if the tier passed
half load (`growIf`, `H` the node hash): the handle and the memory, `none` where L aborts. -/
def pushM (S : Schema) (H : Mem → Word → Word → Word) (m : Mem) (t : Word) (vs : List Word)
    (j : Word) : Option (Word × Mem) :=
  match growIf S.sa S.ca H m (pushG S m t vs j (cntW S m t)) (cntW S m t) with
  | some m' => some (hdW S.tag.toUInt64 t (cntW S m t), m')
  | none => none

/-- **The L model of an `intern_*` function**: the persistent probe `rs₀` unless skipped
(`sk ≠ 0`), the scratch probe `rs₁` if the scratch tier is open, the append of the record `vs`
(`pk t`: `*_push`'s room checks; `H` the node hash of the growth). `none` where the L code
aborts. -/
def internM (S : Schema) (m : Mem) (sk : Word) (pk : Word → Bool) (vs rs₀ rs₁ : List Word)
    (H : Mem → Word → Word → Word) : Option (Word × Mem) :=
  if sk = 0 ∧ rs₀ = [] then none
  else if sk = 0 ∧ rs₀.headD 0 ≠ 0 then some (hdW S.tag.toUInt64 0 (rs₀.tail.headD 0), m)
  else if rdW (m.arr64 CTL) 1 ≠ 0 then
    if rs₁ = [] then none
    else if rs₁.headD 0 ≠ 0 then some (hdW S.tag.toUInt64 1 (rs₁.tail.headD 0), m)
    else if pk 1 then pushM S H m 1 vs (rs₁.tail.tail.headD 0)
    else none
  else if pk 0 then pushM S H m 0 vs (rs₀.tail.tail.headD 0)
  else none

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

/-- The growth state reads only the slot array. -/
theorem growR_of_sa (m m' : Mem) (h : m'.arr64 S.sa = m.arr64 S.sa) (hG : GrowR S m) :
    GrowR S m' := by
  simp only [GrowR, nSl, gnW, gexpW, len64_eq, h]; exact hG

/-- The relation after an append to tier `t`, from the two tiers'. -/
theorem storeR_push (hS : S.WF) (m : Mem) (t : Word) (ht : t ≤ 1) (vs : List Word)
    (j : Word) (hj : j < nSl S m) (on : Bool) (tbP tbS tbP' tbS' : Tbl α (Idx k) δ)
    (hR : StoreR S R hs m on tbP tbS)
    (h0 : TierR S R hs (pushG S m t vs j (cntW S m t)) 0 tbP')
    (h1 : TierR S R hs (pushG S m t vs j (cntW S m t)) 1 tbS') :
    StoreR S R hs (pushG S m t vs j (cntW S m t)) on tbP' tbS' := by
  obtain ⟨⟨hctl, hb⟩, hfl, -, -, hG⟩ := hR
  have := hS.ca
  have := hS.scb
  refine ⟨⟨?_, ?_⟩, ?_, h0, h1, growR_pushG S hS m t vs j _ hG ht hj⟩
  · grind [store_grind]
  · rw [pushG_ctl S hS _ _ _ _ _ ht]; grind
  · rw [pushG_ctl S hS _ _ _ _ _ ht]; grind

/-! ### The growth

The models of `SlotGrowSpec.lean`, read as the table relation: the zero loop clears the slot
words, the node loop (`NInv`) registers every node again, so the relation holds after the growth. -/

section grow

theorem rdW_oob (a : Array Word) (x : Word) (h : a.size ≤ x.toNat) : rdW a x = 0 := by
  simp [rdW, h]

theorem rdW_set64_zero (m : Mem) (a b : ArrId) (k x : Word) :
    rdW ((m.set64 a k 0).arr64 b) x = if b = a ∧ k = x then 0 else rdW (m.arr64 b) x := by
  rw [rdW_set64]
  by_cases h : b = a
  · subst h
    by_cases hk : k = x
    · subst hk
      by_cases hs : k.toNat < (m.arr64 b).size
      · simp [hs]
      · simp [hs, rdW_oob (m.arr64 b) k (by omega)]
    · simp [hk]
  · simp [h]

theorem zero8_arr (sa : ArrId) (k : Word) (m : Mem) (b : ArrId) (hb : b ≠ sa) :
    (zero8 sa k m).arr64 b = m.arr64 b := by
  simp only [zero8, Mem.arr64_set64_ne _ _ _ _ _ hb]

theorem zero8_size (sa : ArrId) (k : Word) (m : Mem) (b : ArrId) :
    ((zero8 sa k m).arr64 b).size = (m.arr64 b).size := by
  simp only [zero8, size_set64]

theorem zero8_rd (sa : ArrId) (k : Word) (m : Mem) (x : Word) (hk : k.toNat + 8 < 2 ^ 64) :
    rdW ((zero8 sa k m).arr64 sa) x =
      if k.toNat ≤ x.toNat ∧ x.toNat < k.toNat + 8 then 0 else rdW (m.arr64 sa) x := by
  simp only [zero8, rdW_set64_zero, true_and]
  have e : ∀ i : Nat, i < 8 → (k + UInt64.ofNat i).toNat = k.toNat + i := fun i hi => by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat']; omega
  have e1 := e 1 (by omega); have e2 := e 2 (by omega); have e3 := e 3 (by omega)
  have e4 := e 4 (by omega); have e5 := e 5 (by omega); have e6 := e 6 (by omega)
  have e7 := e 7 (by omega)
  simp only [UInt64.ofNat_one] at e1
  simp only [show UInt64.ofNat 2 = 2 from rfl, show UInt64.ofNat 3 = 3 from rfl,
    show UInt64.ofNat 4 = 4 from rfl, show UInt64.ofNat 5 = 5 from rfl,
    show UInt64.ofNat 6 = 6 from rfl, show UInt64.ofNat 7 = 7 from rfl] at *
  have hx : ∀ y : Word, (y = x) = (y.toNat = x.toNat) := fun y => by
    simp [UInt64.toNat_inj]
  simp only [hx, e1, e2, e3, e4, e5, e6, e7]
  grind (splits := 20)

/-- The zero loop zeroes `[k, N)` of `sa` (both multiples of 8) and changes nothing else. -/
theorem gzeroW_spec (sa : ArrId) (N : Word) (hN : N.toNat % 8 = 0) (hN' : N.toNat < 2 ^ 63) :
    ∀ (f : Nat) (k : Word) (m : Mem), N.toNat - k.toNat ≤ f → k.toNat % 8 = 0 →
      (∀ b, b ≠ sa → (gzeroW sa N k m).arr64 b = m.arr64 b) ∧
      ((gzeroW sa N k m).arr64 sa).size = (m.arr64 sa).size ∧
      ∀ x, rdW ((gzeroW sa N k m).arr64 sa) x =
        if k.toNat ≤ x.toNat ∧ x.toNat < N.toNat then 0 else rdW (m.arr64 sa) x := by
  intro f
  induction f with
  | zero =>
    intro k m hf hk
    rw [gzeroW]
    have : ¬ (k < N ∧ k.toNat + 8 < 2 ^ 64) := fun h => by
      have := UInt64.lt_iff_toNat_lt.mp h.1; omega
    rw [ite_eq_right_iff.mpr (fun h => absurd h this)]
    refine ⟨fun _ _ => rfl, rfl, fun x => ?_⟩
    grind
  | succ f ih =>
    intro k m hf hk
    rw [gzeroW]
    by_cases hlt : k.toNat < N.toNat
    · have hk8 : k.toNat + 8 < 2 ^ 64 := by omega
      have e8 : (k + 8).toNat = k.toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
      simp only [UInt64.lt_iff_toNat_lt.mpr hlt, hk8, and_self, ↓reduceIte]
      obtain ⟨i1, i2, i3⟩ := ih (k + 8) (zero8 sa k m) (by omega) (by omega)
      refine ⟨fun b hb => (i1 b hb).trans (zero8_arr sa k m b hb), by rw [i2, zero8_size], ?_⟩
      intro x; rw [i3, zero8_rd sa k m x hk8, e8]; grind
    · have : ¬ (k < N ∧ k.toNat + 8 < 2 ^ 64) := fun h => hlt (UInt64.lt_iff_toNat_lt.mp h.1)
      rw [ite_eq_right_iff.mpr (fun h => absurd h this)]
      refine ⟨fun _ _ => rfl, rfl, fun x => ?_⟩
      grind

/-- Value `v` lies on the run from slot `x` of tier `t` (among `n`), after nonzero slot words. -/
def FoundW (sl : Array Word) (n t x v : Word) : Prop :=
  ∃ d : Nat, rdW sl (walkW n x d * 2 + t) = v ∧ ∀ e < d, rdW sl (walkW n x e * 2 + t) ≠ 0

/-- The growth's probe: its result is the first zero slot word on the run. -/
theorem gprobeW_found (sl : Array Word) (t n x : Word) :
    ∀ (f : Nat) (d j : Word), n.toNat - d.toNat ≤ f →
      (∀ e < d.toNat, rdW sl (walkW n x e * 2 + t) ≠ 0) →
      gprobeW sl t n (walkW n x d.toNat) d = some j →
      ∃ D : Nat, j = walkW n x D ∧ rdW sl (j * 2 + t) = 0 ∧
        ∀ e < D, rdW sl (walkW n x e * 2 + t) ≠ 0 := by
  intro f
  induction f with
  | zero =>
    intro d j hf hd h
    rw [gprobeW] at h
    have hnd : n ≤ d := UInt64.le_iff_toNat_le.mpr (by omega)
    by_cases h0 : rdW sl (walkW n x d.toNat * 2 + t) = 0
    · simp only [h0, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨d.toNat, rfl, h0, hd⟩
    · simp [h0, hnd] at h
  | succ f ih =>
    intro d j hf hd h
    rw [gprobeW] at h
    by_cases h0 : rdW sl (walkW n x d.toNat * 2 + t) = 0
    · simp only [h0, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨d.toNat, rfl, h0, hd⟩
    by_cases hnd : n ≤ d
    · simp [h0, hnd] at h
    simp only [h0, hnd, ↓reduceIte] at h
    have hlt : d.toNat < n.toNat := by
      have := mt UInt64.le_iff_toNat_le.mpr hnd; omega
    have e1 : (d + 1).toNat = d.toNat + 1 := by
      have := n.toNat_lt; rw [UInt64.toNat_add]; simp; omega
    rw [← walkW_succ, ← e1] at h
    refine ih (d + 1) j (by omega) (fun e he => ?_) h
    rw [e1] at he
    by_cases hed : e = d.toNat
    · subst hed; exact h0
    · exact hd e (by omega)

/-- A write at a zero slot word keeps every nonzero value found. -/
theorem foundW_keep (sl sl' : Array Word) (n t x v p : Word) (h : FoundW sl n t x v) (hv : v ≠ 0)
    (hp : rdW sl p = 0) (hsl : ∀ y, y ≠ p → rdW sl' y = rdW sl y) : FoundW sl' n t x v := by
  obtain ⟨d, h1, h2⟩ := h
  refine ⟨d, ?_, fun e he => ?_⟩
  · rw [hsl _ (fun hy => by rw [hy, hp] at h1; exact hv h1.symm)]; exact h1
  · have := h2 e he
    rw [hsl _ (fun hy => by rw [hy] at this; exact this hp)]; exact this

theorem rdW_set64_in (m : Mem) (a : ArrId) (k v x : Word) (hk : k.toNat < (m.arr64 a).size) :
    rdW ((m.set64 a k v).arr64 a) x = if k = x then v else rdW (m.arr64 a) x := by
  rw [rdW_set64]; simp [hk]

/-- The node loop's invariant, from the memory `mr` before it: only tier `t`'s slot words below
`2 n` change, each reads `0` or a value of a node registered so far, and every node so far is
found from its home slot (`hh` its hash). -/
def NInv (sa : ArrId) (n t b : Word) (hh : Word → Word) (mr mi : Mem) (i : Word) : Prop :=
  (∀ a, a ≠ sa → mi.arr64 a = mr.arr64 a) ∧ (mi.arr64 sa).size = (mr.arr64 sa).size ∧
  (∀ x, (∀ j, j < n → x ≠ j * 2 + t) → rdW (mi.arr64 sa) x = rdW (mr.arr64 sa) x) ∧
  (∀ j, j < n → rdW (mi.arr64 sa) (j * 2 + t) = 0 ∨
    (b < rdW (mi.arr64 sa) (j * 2 + t) ∧
      (rdW (mi.arr64 sa) (j * 2 + t)).toNat ≤ b.toNat + i.toNat)) ∧
  (∀ i' : Word, i' < i → FoundW (mi.arr64 sa) n t (homeW (hh i') n) (b + i' + 1))

theorem gnodesW_inv (sa : ArrId) (H : Mem → Word → Word → Word) (n t b c : Word)
    (hh : Word → Word) (mr : Mem) (hn0 : 0 < n) (hn : 2 * n.toNat < (mr.arr64 sa).size)
    (hn' : n.toNat < 2 ^ 62) (ht : t ≤ 1) (hbc : b.toNat + c.toNat + 1 < 2 ^ 64)
    (hH : ∀ mi : Mem, (∀ a, a ≠ sa → mi.arr64 a = mr.arr64 a) → ∀ i, H mi t i = hh i) :
    ∀ (f : Nat) (i : Word) (mi mf : Mem), c.toNat - i.toNat ≤ f → i ≤ c →
      NInv sa n t b hh mr mi i → gnodesW sa H n t b c i mi = some mf →
      NInv sa n t b hh mr mf c := by
  intro f
  induction f with
  | zero =>
    intro i mi mf hf hic hI h
    rw [gnodesW] at h
    have hci : c = i := UInt64.toNat_inj.mp (by have := UInt64.le_iff_toNat_le.mp hic; omega)
    subst hci
    simp only [UInt64.lt_irrefl, ↓reduceIte, Option.some.injEq] at h
    subst h; exact hI
  | succ f ih =>
    intro i mi mf hf hic hI h
    rw [gnodesW] at h
    by_cases hlt' : ¬ i < c
    · have hlt := hlt'
      have hci : c = i := UInt64.toNat_inj.mp (by
        have := UInt64.le_iff_toNat_le.mp hic; have := mt UInt64.lt_iff_toNat_lt.mpr hlt; omega)
      subst hci
      simp only [UInt64.lt_irrefl, ↓reduceIte, Option.some.injEq] at h
      subst h; exact hI
    have hlt : i < c := Classical.not_not.mp hlt'
    simp only [hlt, ↓reduceIte] at h
    obtain ⟨h1, h2, h3, h4, h5⟩ := hI
    rw [hH mi h1 i] at h
    split at h
    · cases h
    rename_i j hj
    have hil : i.toNat < c.toNat := UInt64.lt_iff_toNat_lt.mp hlt
    have e1 : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hx : homeW (hh i) n < n := homeW_lt _ _ hn0
    obtain ⟨D, hD, hz, hfd⟩ := gprobeW_found (mi.arr64 sa) t n (homeW (hh i) n) _ 0 j
      (Nat.le_refl _) (by simp) hj
    have hjn : j < n := by rw [hD]; exact walkW_lt _ _ _ hx
    have hjn' := UInt64.lt_iff_toNat_lt.mp hjn
    have htn : t.toNat ≤ 1 := UInt64.le_iff_toNat_le.mp ht
    have ep : (j * 2 + t).toNat = j.toNat * 2 + t.toNat := by
      rw [UInt64.toNat_add, UInt64.toNat_mul]; simp; omega
    have hpin : (j * 2 + t).toNat < (mi.arr64 sa).size := by rw [h2]; omega
    have hv : (b + i + 1).toNat = b.toNat + i.toNat + 1 := by
      rw [UInt64.toNat_add, UInt64.toNat_add]; simp; omega
    have hrd := rdW_set64_in mi sa (j * 2 + t) (b + i + 1)
    refine ih (i + 1) _ mf (by omega) (UInt64.le_iff_toNat_le.mpr (by omega)) ?_ h
    refine ⟨fun a ha => by rw [Mem.arr64_set64_ne _ _ _ _ _ ha]; exact h1 a ha,
      by rw [size_set64]; exact h2, fun x hxs => ?_, fun j' hj' => ?_, fun i' hi' => ?_⟩
    · rw [hrd _ hpin, ite_eq_right (fun e => hxs j hjn e.symm)]; exact h3 x hxs
    · rw [hrd _ hpin]
      split
      · right; constructor
        · rw [UInt64.lt_iff_toNat_lt, hv]; omega
        · rw [hv, e1]; omega
      · rcases h4 j' hj' with h | h
        · left; exact h
        · right; rw [e1]; exact ⟨h.1, by omega⟩
    · have hi'' := UInt64.lt_iff_toNat_lt.mp hi'
      rw [e1] at hi''
      have hv' : (b + i' + 1).toNat = b.toNat + i'.toNat + 1 := by
        rw [UInt64.toNat_add, UInt64.toNat_add]; simp; omega
      by_cases hii : i' = i
      · subst hii
        refine ⟨D, ?_, fun e he => ?_⟩
        · rw [hrd _ hpin, ← hD]; simp
        · have := hfd e he
          rw [hrd _ hpin, ite_eq_right (fun hy => by rw [← hy] at this; exact this hz)]; exact this
      · refine foundW_keep _ _ n t _ _ (j * 2 + t) (h5 i' ?_) ?_ hz (fun y hy => ?_)
        · rw [UInt64.lt_iff_toNat_lt]; have := mt UInt64.toNat_inj.mp hii; omega
        · intro h0; have := congrArg UInt64.toNat h0; simp at this; omega
        · rw [hrd _ hpin, ite_eq_right (Ne.symm hy)]

/-- A slot word's index: no wrap below `2^62` slots. -/
theorem slotIx_toNat (j t : Word) (hj : j.toNat < 2 ^ 62) (ht : t ≤ 1) :
    (j * 2 + t).toNat = j.toNat * 2 + t.toNat := by
  have : t.toNat ≤ 1 := UInt64.le_iff_toNat_le.mp ht
  rw [UInt64.toNat_add, UInt64.toNat_mul]; simp; omega

theorem foundW_congr (sl sl' : Array Word) (n t x v : Word) (hx : x < n)
    (h : ∀ j, j < n → rdW sl' (j * 2 + t) = rdW sl (j * 2 + t)) (hf : FoundW sl n t x v) :
    FoundW sl' n t x v := by
  obtain ⟨d, h1, h2⟩ := hf
  exact ⟨d, by rw [h (walkW n x d) (walkW_lt _ _ _ hx)]; exact h1,
    fun e he => by rw [h (walkW n x e) (walkW_lt _ _ _ hx)]; exact h2 e he⟩

/-- What the growth's size check gives: room for the doubled table and a small exponent. -/
theorem grow_check (m : Mem) (hG : GrowR S m)
    (hc : ¬ (m.len64 S.sa - 1) >>> 1 < gnW S.sa m * 2) :
    4 * (nSl S m).toNat + 1 ≤ (m.arr64 S.sa).size ∧ (gexpW S.sa m).toNat < 58 ∧
      (gnW S.sa m * 2).toNat = 2 * (nSl S m).toNat ∧
      (m.len64 S.sa - 1).toNat = (m.arr64 S.sa).size - 1 := by
  have hn := nSl_toNat S m hG
  obtain ⟨g1, g2, g3, -⟩ := hG
  have hp : 2 ^ (gexpW S.sa m).toNat ≤ 2 ^ 58 := Nat.pow_le_pow_right (by omega) (by omega)
  have hsz : (m.arr64 S.sa).size < UInt64.size := by simp only [UInt64.size]; omega
  have hL : (m.len64 S.sa - 1).toNat = (m.arr64 S.sa).size - 1 := by
    rw [len64_eq, UInt64.toNat_sub_of_le]
    · rw [UInt64.toNat_ofNat_of_lt' hsz]; rfl
    · rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' hsz]; simp; omega
  have h2 : (gnW S.sa m * 2).toNat = 2 * (nSl S m).toNat := by
    rw [UInt64.toNat_mul]; simp only [nSl] at hn ⊢; simp; omega
  have hc' := mt UInt64.lt_iff_toNat_lt.mpr hc
  rw [UInt64.toNat_shiftRight, hL, h2] at hc'
  simp only [show (1 : Word).toNat % 64 = 1 from rfl, Nat.shiftRight_eq_div_pow, Nat.pow_one] at hc'
  have h4 : 4 * (nSl S m).toNat + 1 ≤ (m.arr64 S.sa).size := by omega
  refine ⟨h4, ?_, h2, hL⟩
  apply Nat.lt_of_not_le
  intro hge
  have : 2 ^ 58 ≤ 2 ^ (gexpW S.sa m).toNat := Nat.pow_le_pow_right (by omega) hge
  omega

/-- After the exponent write and the zero loop: every slot word reads `0`, the last word is the
new exponent, nothing else changed. -/
theorem grow_zero (m : Mem) (hG : GrowR S m)
    (hc : ¬ (m.len64 S.sa - 1) >>> 1 < gnW S.sa m * 2) (m2 : Mem)
    (hm2 : gzeroW S.sa (gnW S.sa m * 2) 0
      (m.set64 S.sa (m.len64 S.sa - 1) (gexpW S.sa m + 1)) = m2) :
    (∀ a, a ≠ S.sa → m2.arr64 a = m.arr64 a) ∧ (m2.arr64 S.sa).size = (m.arr64 S.sa).size ∧
      (∀ x : Word, x.toNat + 1 < (m.arr64 S.sa).size → rdW (m2.arr64 S.sa) x = 0) ∧
      rdW (m2.arr64 S.sa) (m.len64 S.sa - 1) = gexpW S.sa m + 1 := by
  subst hm2
  obtain ⟨h4, hg, h2, hL⟩ := grow_check S m hG hc
  have hn := nSl_toNat S m hG
  have hp : 2 ^ (gexpW S.sa m).toNat ≤ 2 ^ 57 := Nat.pow_le_pow_right (by omega) (by omega)
  obtain ⟨z1, z2, z3⟩ := gzeroW_spec S.sa (gnW S.sa m * 2) (by rw [h2, hn]; omega)
    (by rw [h2, hn]; omega) _ 0 (m.set64 S.sa (m.len64 S.sa - 1) (gexpW S.sa m + 1))
    (Nat.le_refl _) (by simp)
  have hLin : (m.len64 S.sa - 1).toNat < (m.arr64 S.sa).size := by omega
  have r1 := rdW_set64_in m S.sa (m.len64 S.sa - 1) (gexpW S.sa m + 1)
  refine ⟨fun a ha => by rw [z1 a ha, Mem.arr64_set64_ne _ _ _ _ _ ha], by rw [z2, size_set64],
    fun x hx => ?_, ?_⟩
  · rw [z3, r1 _ hLin]
    by_cases hx2 : x.toNat < 2 * (nSl S m).toNat
    · simp [h2, hx2]
    · have hne : m.len64 S.sa - 1 ≠ x := fun e => by rw [e] at hL; omega
      simp only [h2, hx2, and_false, ↓reduceIte, hne]
      exact hG.2.2.2 x (by omega) hx
  · rw [z3, r1 _ hLin]
    simp [h2, hL]
    omega

/-- The node loop's result as the table relation's slot clause. -/
theorem slotsOKG_of (m' : Mem) (t n b c : Word)
    (hh : Word → Word) (hn0 : 0 < n) (hb : baseW m' t = b) (hn : nSl S m' = n)
    (hhs : ∀ i, hs m' t i = hh i) (hbc : b.toNat + c.toNat + 1 < 2 ^ 64)
    (h4 : ∀ j, j < n → rdW (m'.arr64 S.sa) (j * 2 + t) = 0 ∨
      (b < rdW (m'.arr64 S.sa) (j * 2 + t) ∧
        (rdW (m'.arr64 S.sa) (j * 2 + t)).toNat ≤ b.toNat + c.toNat))
    (h5 : ∀ i', i' < c → FoundW (m'.arr64 S.sa) n t (homeW (hh i') n) (b + i' + 1)) :
    SlotsOKG S hs m' t c.toNat := by
  have hrd : ∀ j, slotW S m' t j = slotRd (rdW (m'.arr64 S.sa) (j * 2 + t)) b := fun j => by
    simp only [slotW, slotV, hb]
  refine ⟨fun j hj => ?_, fun i hi => ?_⟩
  · rw [hn] at hj
    rw [hrd, slotRd]
    rcases h4 j hj with h | h
    · simp [h]
    · have : ¬ rdW (m'.arr64 S.sa) (j * 2 + t) ≤ b := fun h' => by
        have := UInt64.le_iff_toNat_le.mp h'; have := UInt64.lt_iff_toNat_lt.mp h.1; omega
      simp only [this, ↓reduceIte]
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt h.1)]; omega
  · have hic : i < c := UInt64.lt_iff_toNat_lt.mpr hi
    obtain ⟨d, d1, d2⟩ := h5 i hic
    have hx : homeW (hh i) n < n := homeW_lt _ _ hn0
    refine ⟨d, ?_, fun e he => ?_⟩
    · rw [homeS, hn, hhs, hrd, d1, slotRd]
      have hv : (b + i + 1).toNat = b.toNat + i.toNat + 1 := by
        rw [UInt64.toNat_add, UInt64.toNat_add]; simp; omega
      have : ¬ b + i + 1 ≤ b := fun h' => by have := UInt64.le_iff_toNat_le.mp h'; omega
      simp only [this, ↓reduceIte]
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)), hv,
        UInt64.toNat_add]
      simp; omega
    · rw [homeS, hn, hhs, hrd, slotRd]
      have h0 := d2 e he
      rcases h4 _ (walkW_lt _ _ e hx) with h | h
      · exact absurd h h0
      · have : ¬ rdW (m'.arr64 S.sa) (walkW n (homeW (hh i) n) e * 2 + t) ≤ b := fun h' => by
          have := UInt64.le_iff_toNat_le.mp h'; have := UInt64.lt_iff_toNat_lt.mp h.1; omega
        simp only [this, ↓reduceIte]
        intro h'
        have h1 := congrArg UInt64.toNat h'
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt h.1), UInt64.toNat_zero] at h1
        have := UInt64.lt_iff_toNat_lt.mp h.1
        omega

/-- Words at or above `2 n` are no slot word of a tier. -/
theorem notSlot_hi (n t x : Word) (hn : n.toNat < 2 ^ 62) (ht : t ≤ 1)
    (hx : 2 * n.toNat ≤ x.toNat) : ∀ j, j < n → x ≠ j * 2 + t := fun j hj e => by
  have := UInt64.lt_iff_toNat_lt.mp hj
  have e1 := slotIx_toNat j t (by omega) ht
  have : t.toNat ≤ 1 := UInt64.le_iff_toNat_le.mp ht
  rw [← e] at e1; omega

/-- The tiers' slot words are disjoint. -/
theorem notSlot_par (n j t t' : Word) (hn : n.toNat < 2 ^ 62) (ht : t ≤ 1) (ht' : t' ≤ 1)
    (htt : t ≠ t') (hj : j < n) : ∀ j', j' < n → j * 2 + t ≠ j' * 2 + t' := fun j' hj' e => by
  have := UInt64.lt_iff_toNat_lt.mp hj
  have := UInt64.lt_iff_toNat_lt.mp hj'
  have e1 := slotIx_toNat j t (by omega) ht
  have e2 := slotIx_toNat j' t' (by omega) ht'
  have : t.toNat ≤ 1 := UInt64.le_iff_toNat_le.mp ht
  have : t'.toNat ≤ 1 := UInt64.le_iff_toNat_le.mp ht'
  have : t.toNat ≠ t'.toNat := fun h => htt (UInt64.toNat_inj.mp h)
  rw [e] at e1; omega

omit [BEq α] [Hashable α] in
/-- A change of the slot array only keeps every node's relation and hash. -/
theorem rframe_sa (hS : S.WF) (hfr : RFrame S R hs) (m mi : Mem)
    (hmi : ∀ a, a ≠ S.sa → mi.arr64 a = m.arr64 a) (t i : Word) :
    (∀ x, R m t i x → R mi t i x) ∧ hs mi t i = hs m t i :=
  hfr m mi t i ⟨fun b _ hb _ => hmi b hb, by rw [hmi CTL hS.sa_ctl.symm]⟩
    (fun f _ => by simp only [fld, hmi S.ra hS.ra_sa])

/-- A tier stays represented under a change of the slot array that keeps its slot clause. -/
theorem tierR_sa (hS : S.WF) (hfr : RFrame S R hs) (m m' : Mem) (t : Word)
    (tb : Tbl α (Idx k) δ) (hT : TierR S R hs m t tb)
    (hm : ∀ a, a ≠ S.sa → m'.arr64 a = m.arr64 a) (hsl : SlotsOKG S hs m' t tb.nodes.size) :
    TierR S R hs m' t tb := by
  obtain ⟨hc, hcap, hrs, hrec, hsome, hback, -⟩ := hT
  refine ⟨by simp only [cntW, hm CTL hS.sa_ctl.symm]; exact hc, hcap,
    by rw [hm S.ra hS.ra_sa]; exact hrs, fun i a h => ?_, hsome, hback, hsl⟩
  exact (rframe_sa S R hs hS hfr m m' hm t i).1 a (hrec i a h)

theorem storeR_growM (hS : S.WF) (hfr : RFrame S R hs) (m m' : Mem) (on : Bool)
    (tbP tbS : Tbl α (Idx k) δ) (hR : StoreR S R hs m on tbP tbS)
    (h : growM S.sa S.ca hs m = some m') : StoreR S R hs m' on tbP tbS := by
  obtain ⟨⟨hctl, hb⟩, hfl, hT0, hT1, hG⟩ := hR
  rw [growM] at h
  split at h
  · cases h
  rename_i hc
  obtain ⟨h4, hg, h2, hL⟩ := grow_check S m hG hc
  have hn := nSl_toNat S m hG
  have hp : 2 ^ (gexpW S.sa m).toNat ≤ 2 ^ 57 := Nat.pow_le_pow_right (by omega) (by omega)
  generalize hm2 : gzeroW S.sa (gnW S.sa m * 2) 0
    (m.set64 S.sa (m.len64 S.sa - 1) (gexpW S.sa m + 1)) = m2 at h
  obtain ⟨z1, z2, z3, z4⟩ := grow_zero S m hG hc m2 hm2
  generalize hn' : gnW S.sa m * 2 = n' at h h2
  have hpos : 0 < 2 ^ (gexpW S.sa m).toNat := Nat.two_pow_pos _
  have hn0 : 0 < n' := UInt64.lt_iff_toNat_lt.mpr (by rw [UInt64.toNat_zero]; omega)
  have hn62 : n'.toNat < 2 ^ 62 := by omega
  rw [gtiersW] at h
  simp only [show (0 : Word) < 2 from by decide, ↓reduceIte] at h
  split at h
  · cases h
  rename_i m3 h3
  rw [gtiersW] at h
  simp only [show (0 : Word) + 1 = 1 from rfl, show (1 : Word) < 2 from by decide,
    ↓reduceIte] at h
  split at h
  · cases h
  rename_i m4 h4'
  rw [gtiersW] at h
  simp only [show (1 : Word) + 1 = 2 from rfl, show ¬ (2 : Word) < 2 from by decide,
    ↓reduceIte, Option.some.injEq] at h
  subst h
  have hCTL2 : m2.arr64 CTL = m.arr64 CTL := z1 CTL hS.sa_ctl.symm
  rw [hCTL2] at h3
  have hsl : ∀ j t, j < n' → t ≤ 1 → (j * 2 + t).toNat + 1 < (m.arr64 S.sa).size :=
    fun j t hj ht => by
      have := UInt64.lt_iff_toNat_lt.mp hj
      have : t.toNat ≤ 1 := UInt64.le_iff_toNat_le.mp ht
      rw [slotIx_toNat j t (by omega) ht]; omega
  have hc0 : (cntW S m 0).toNat ≤ 134217728 := by have := hT0.1; have := hT0.2.1; omega
  have hc1 : (cntW S m 1).toNat ≤ 134217728 := by have := hT1.1; have := hT1.2.1; omega
  simp only [cntW] at hc0 hc1
  have hf0 := fun mi (hmi : ∀ a, a ≠ S.sa → mi.arr64 a = m2.arr64 a) i =>
    (rframe_sa S R hs hS hfr m mi (fun a ha => (hmi a ha).trans (z1 a ha)) 0 i).2
  obtain ⟨a1, a2, a3, a4, a5⟩ := gnodesW_inv S.sa hs n' 0 (rdW (m.arr64 CTL) SCB * 0)
    (rdW (m.arr64 CTL) (S.ca + 0)) (hs m 0) m2 hn0 (by rw [z2]; omega) hn62 (by decide)
    (by rw [UInt64.mul_zero, UInt64.toNat_zero]; omega) hf0 _ 0 m2 m3 (Nat.le_refl _) UInt64.zero_le
    ⟨fun _ _ => rfl, rfl, fun _ _ => rfl, fun j hj => Or.inl (z3 _ (hsl j 0 hj (by decide))),
      fun i' hi' => absurd (UInt64.lt_iff_toNat_lt.mp hi') (by simp)⟩ h3
  have hCTL3 : m3.arr64 CTL = m.arr64 CTL := (a1 CTL hS.sa_ctl.symm).trans hCTL2
  rw [hCTL3] at h4'
  have hf1 := fun mi (hmi : ∀ a, a ≠ S.sa → mi.arr64 a = m3.arr64 a) i =>
    (rframe_sa S R hs hS hfr m mi
      (fun a ha => ((hmi a ha).trans (a1 a ha)).trans (z1 a ha)) 1 i).2
  obtain ⟨b1, b2, b3, b4, b5⟩ := gnodesW_inv S.sa hs n' 1 (rdW (m.arr64 CTL) SCB * 1)
    (rdW (m.arr64 CTL) (S.ca + 1)) (hs m 1) m3 hn0 (by rw [a2, z2]; omega) hn62 (by decide)
    (by rw [UInt64.mul_one]; omega) hf1 _ 0 m3 m4 (Nat.le_refl _) UInt64.zero_le
    ⟨fun _ _ => rfl, rfl, fun _ _ => rfl, fun j hj => Or.inl (by
        rw [a3 _ (notSlot_par n' j 1 0 hn62 (by decide) (by decide) (by decide) hj)]
        exact z3 _ (hsl j 1 hj (by decide))),
      fun i' hi' => absurd (UInt64.lt_iff_toNat_lt.mp hi') (by simp)⟩ h4'
  have hm4 : ∀ a, a ≠ S.sa → m4.arr64 a = m.arr64 a := fun a ha =>
    ((b1 a ha).trans (a1 a ha)).trans (z1 a ha)
  have hsz4 : (m4.arr64 S.sa).size = (m.arr64 S.sa).size := by rw [b2, a2, z2]
  have hhi : ∀ x : Word, 2 * n'.toNat ≤ x.toNat →
      rdW (m4.arr64 S.sa) x = rdW (m2.arr64 S.sa) x := fun x hx => by
    rw [b3 x (notSlot_hi n' 1 x hn62 (by decide) hx), a3 x (notSlot_hi n' 0 x hn62 (by decide) hx)]
  have hlen : m4.len64 S.sa = m.len64 S.sa := by simp only [len64_eq, hsz4]
  have hexp : gexpW S.sa m4 = gexpW S.sa m + 1 := by
    show rdW (m4.arr64 S.sa) (m4.len64 S.sa - 1) = _
    rw [hlen, hhi _ (by rw [hL]; omega), z4]
  have hgt : (gexpW S.sa m + 1).toNat = (gexpW S.sa m).toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  have hnS : nSl S m4 = n' := by
    apply UInt64.toNat_inj.mp
    rw [show nSl S m4 = SN0 <<< gexpW S.sa m4 from rfl, hexp, shl_SN0_toNat _ (by omega), hgt,
      h2, hn, Nat.pow_succ]
    omega
  have h0eq : ∀ j, j < n' → rdW (m4.arr64 S.sa) (j * 2 + 0) = rdW (m3.arr64 S.sa) (j * 2 + 0) :=
    fun j hj => b3 _ (notSlot_par n' j 0 1 hn62 (by decide) (by decide) (by decide) hj)
  have hS0 := slotsOKG_of S hs m4 0 n' (rdW (m.arr64 CTL) SCB * 0) (rdW (m.arr64 CTL) (S.ca + 0))
    (hs m 0) hn0 (by simp only [baseW, hm4 CTL hS.sa_ctl.symm]) hnS
    (fun i => (rframe_sa S R hs hS hfr m m4 hm4 0 i).2)
    (by rw [UInt64.mul_zero, UInt64.toNat_zero]; omega)
    (fun j hj => by rw [h0eq j hj]; exact a4 j hj)
    (fun i' hi' => foundW_congr _ _ n' 0 _ _ (homeW_lt _ _ hn0) h0eq (a5 i' hi'))
  have hS1 := slotsOKG_of S hs m4 1 n' (rdW (m.arr64 CTL) SCB * 1) (rdW (m.arr64 CTL) (S.ca + 1))
    (hs m 1) hn0 (by simp only [baseW, hm4 CTL hS.sa_ctl.symm]) hnS
    (fun i => (rframe_sa S R hs hS hfr m m4 hm4 1 i).2)
    (by rw [UInt64.mul_one]; omega) b4 b5
  have hC := hm4 CTL hS.sa_ctl.symm
  refine ⟨⟨by rw [hC]; exact hctl, by rw [hC]; exact hb⟩, by rw [hC]; exact hfl,
    tierR_sa S R hs hS hfr m m4 0 tbP hT0 hm4 (by rw [← hT0.1]; exact hS0),
    tierR_sa S R hs hS hfr m m4 1 tbS hT1 hm4 (by rw [← hT1.1]; exact hS1),
    by rw [hexp, hgt]; omega, by rw [hnS, hsz4]; omega, by rw [hsz4]; exact hG.2.2.1,
    fun x hx1 hx2 => ?_⟩
  rw [hnS] at hx1; rw [hsz4] at hx2
  rw [hhi x hx1]; exact z3 x hx2

end grow

/-- **The growth keeps the relation** (`SlotGrowSpec.lean`'s `growIf`, with the relation's node
hash): the slot count doubles and every node of both tiers is registered again, so every node is
found again; nothing else changes. -/
theorem storeR_growIf (hS : S.WF) (hfr : RFrame S R hs) (m₀ m m' : Mem) (c : Word) (on : Bool)
    (tbP tbS : Tbl α (Idx k) δ) (hR : StoreR S R hs m on tbP tbS)
    (h : growIf S.sa S.ca hs m₀ m c = some m') : StoreR S R hs m' on tbP tbS := by
  by_cases hg : gnW S.sa m₀ < (c + 1) * 2
  · rw [growIf_grow _ _ _ _ _ _ hg] at h
    exact storeR_growM S R hs hS hfr m m' on tbP tbS hR h
  · rw [growIf_keep _ _ _ _ _ _ hg] at h
    cases h; exact hR

/-- `m'` is `m` up to the table: the arrays and the pool top of `OutEq`, and every size. -/
def SameOut (S : Schema) (m m' : Mem) : Prop :=
  OutEq S m m' ∧ m'.words.size = m.words.size ∧ ∀ b, (m'.arr64 b).size = (m.arr64 b).size

theorem pushM_some (S : Schema) (H : Mem → Word → Word → Word) (m : Mem) (t : Word)
    (vs : List Word) (j w : Word) (m' : Mem) (h : pushM S H m t vs j = some (w, m')) :
    w = hdW S.tag.toUInt64 t (cntW S m t) ∧
      growIf S.sa S.ca H m (pushG S m t vs j (cntW S m t)) (cntW S m t) = some m' := by
  unfold pushM at h; split at h <;> simp_all

theorem pushM_sameOut (S : Schema) (hS : S.WF) (H : Mem → Word → Word → Word) (m : Mem)
    (t : Word) (ht : t ≤ 1) (vs : List Word) (j w : Word) (m' : Mem)
    (h : pushM S H m t vs j = some (w, m')) : SameOut S m m' := by
  obtain ⟨-, hg⟩ := pushM_some S H m t vs j w m' h
  obtain ⟨g1, g2, g3⟩ := growIf_frame _ _ _ _ _ _ _ hg
  obtain ⟨o1, o2⟩ := outEq_pushG S hS m t ht vs j (cntW S m t)
  refine ⟨⟨fun b h1 h2 h3 => (g1 b h2).trans (o1 b h1 h2 h3), ?_⟩, ?_, fun b => ?_⟩
  · rw [g1 CTL hS.sa_ctl.symm]; exact o2
  · rw [g3]; exact pushG_words S m t vs j _
  · rw [g2 b]; exact pushG_size S m t vs j _ b

theorem internM_sameOut (S : Schema) (hS : S.WF) (m : Mem) (sk : Word) (pk : Word → Bool)
    (vs rs₀ rs₁ : List Word) {H : Mem → Word → Word → Word} (w : Word) (m' : Mem)
    (h : internM S m sk pk vs rs₀ rs₁ H = some (w, m')) : SameOut S m m' := by
  have : SameOut S m m := ⟨⟨fun _ _ _ _ => rfl, rfl⟩, rfl, fun _ => rfl⟩
  simp only [internM] at h
  split at h <;> try split at h <;> try split at h <;> try split at h <;> try split at h <;>
    try split at h
  all_goals first
    | exact pushM_sameOut S hS H m _ (by decide) vs _ w m' h
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact this)
    | simp at h

/-- **An `intern_*` model refines the arena's hash-consing**, for any table: if the L model
returns the handle `w` and the memory `m'`, the arena operation `op` (whose run is `protoRun`)
succeeds with the handle `w`, in a state whose tables `m'` represents. -/
theorem intern_correctG [LawfulBEq α] (hS : S.WF) (hfr : RFrame S R hs)
    (L : Lens α δ k) (a : AState) (m : Mem)
    (hR : StoreR S R hs m (L.on a) (L.getP a) (L.getS a))
    (op : AM (Idx k)) (key : α) (pf : Option (Idx k)) (d : δ) (err : CheckError)
    (hrun : op.run a = protoRun L key S.tag pf d err a)
    (skB : Bool) (hpf : pf = if skB then none else (L.getP a).cons[key]?)
    (sk : Word) (hsk : (sk = 0) = (skB = false)) (hskon : skB = true → L.on a = true)
    (mt : Word → Word → Bool) (qh : Word) (hM : MatchOK R mt m key) (hH : HomeOK hs mt m qh)
    (rs₀ rs₁ : List Word) (hP0 : ProbeOKG S m 0 (mt 0) (homeS S m qh) rs₀)
    (hP1 : ProbeOKG S m 1 (mt 1) (homeS S m qh) rs₁)
    (pk : Word → Bool) (hpk : ∀ t, pk t = true → PushRoom S m t)
    (vs : List Word) (hl : vs.length = S.w.toNat) (hN : NewOK S R hs m vs key qh)
    (w : Word) (m' : Mem) (hI : internM S m sk pk vs rs₀ rs₁ hs = some (w, m')) :
    AM.ok op a ∧
    StoreR S R hs m' (L.on (AM.st op a)) (L.getP (AM.st op a)) (L.getS (AM.st op a)) ∧
    AM.res op a = decI w := by
  obtain ⟨⟨hctl, hb⟩, hflag, hT0, hT1, hG⟩ := id hR
  have htag : S.tag.toUInt64 < 16 := by have := hS.tag; grind
  have hit0 := tierR_hit S R hs m 0 _ hT0 mt key hM _ _ hP0
  have hit1 := tierR_hit S R hs m 1 _ hT1 mt key hM _ _ hP1
  have miss0 := tierR_miss S R hs m 0 _ hT0 mt key hM qh hH _ hP0
  have miss1 := tierR_miss S R hs m 1 _ hT1 mt key hM qh hH _ hP1
  have hL := L.on_setP
  simp only [internM] at hI
  split at hI
  · simp at hI
  split at hI
  · -- persistent hit
    have hpf' : pf = some (decI (hdW S.tag.toUInt64 0 (rs₀.tail.headD 0))) := by
      grind
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ (hrun.trans (by rw [hpf']; rfl))
    grind
  have hpf' : pf = none := by grind
  subst hpf'
  split at hI
  · split at hI
    · simp at hI
    split at hI
    · -- scratch hit
      obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _
        (hrun.trans (protoRun_hitS L key S.tag d err a _ (by grind) (hit1 ‹_› ‹_›)))
      grind
    split at hI
    · -- scratch append
      have hsz : (L.getS a).nodes.size < 134217728 := by grind [PushRoom, TierR]
      obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _
        (hrun.trans (protoRun_pushS L key S.tag d err a (by grind) (miss1 ‹_› (by grind)) hsz))
      have e : UInt64.ofNat (L.getS a).nodes.size = cntW S m 1 := by grind [TierR]
      rw [e] at hst hres
      have hp1 := tierR_push S R hs hS hfr m 1 (by decide) _ hT1 mt key hM qh hH _ hP1 ‹_›
        (by grind) (hpk 1 ‹_›) hctl hb vs hl hN d hG
      have hj : rs₁.tail.tail.headD 0 < nSl S m := ((hP1 ‹_›).2 (by grind)).2.1
      obtain ⟨rfl, hg⟩ := pushM_some S hs m 1 vs _ w m' hI
      rw [hst, hres, L.on_setS, L.getP_setS, L.getS_setS]
      refine ⟨hok, storeR_growIf S R hs hS hfr m _ m' _ _ _ _
        (storeR_push S R hs hS m 1 (by decide) vs _ hj _ _ _ _ _ hR ?_ hp1) hg, rfl⟩
      exact tierR_other S R hs hS hfr m 1 0 (by decide) (by decide) (by decide) _ hT0
        (hpk 1 ‹_›) hb vs hl _ hG hj
    · simp at hI
  split at hI
  · -- persistent append
    have hsz : (L.getP a).nodes.size < 134217728 := by grind [PushRoom, TierR]
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _
      (hrun.trans (protoRun_pushP L key S.tag d err a (by grind) hsz))
    have e : UInt64.ofNat (L.getP a).nodes.size = cntW S m 0 := by grind [TierR]
    rw [e] at hst hres
    have hp0 := tierR_push S R hs hS hfr m 0 (by decide) _ hT0 mt key hM qh hH _ hP0
      (by grind) (by grind) (hpk 0 ‹_›) hctl hb vs hl hN d hG
    have hj : rs₀.tail.tail.headD 0 < nSl S m := ((hP0 (by grind)).2 (by grind)).2.1
    obtain ⟨rfl, hg⟩ := pushM_some S hs m 0 vs _ w m' hI
    rw [hst, hres, L.on_setP, L.getP_setP, L.getS_setP]
    refine ⟨hok, storeR_growIf S R hs hS hfr m _ m' _ _ _ _
      (storeR_push S R hs hS m 0 (by decide) vs _ hj _ _ _ _ _ hR hp0 ?_) hg, rfl⟩
    exact tierR_other S R hs hS hfr m 0 1 (by decide) (by decide) (by decide) _ hT1
      (hpk 0 ‹_›) hb vs hl _ hG hj
  · simp at hI

end rel

end L.Arena
