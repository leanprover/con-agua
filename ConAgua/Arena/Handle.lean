module

public import ConAgua.Arena.Refine
public import ConAgua.Arena.StoreFields
public import ConAgua.Arena.GrindAttr

@[expose] public section

/-!
# Handle words: encoding, decoding, and the bridge to the twin's `Idx`, proved once

A handle of con-ron (`ConRon/Arena/Handle.lean`, `Idx`) *is* its 32-bit word, in one of two
shapes (con-ron task #133): bit 31 the tier; bit 30 set for a WIDE word (an expression `app`,
`tier · 2^31 + 2^30 + index`), clear for a NARROW one (`tier · 2^31 + tag · 2^26 + index`). L
keeps the word: it hashes it, packs two into a cons key and compares handles with `==`. The
relation between an L word `w` and the twin's handle is `decI w` (`Idx.ofWord w.toUInt32`).

This file and the section "Handle words" of `StoreFields.lean` are the one place that knows
the encoding. Proofs use the names and laws below instead of unfolding the shifts, masks and powers
of two:

* **Encode and decode** (`StoreFields.lean`, plain words, usable in `module` files): `hdW g t i`
  (the narrow handle word of node `i` of tier `t` of tag `g`), `hdA t i` (the wide one of `app`
  node `i`), `tagW h` (the twin's `Idx.tag`), `tierW h` (bit 31), `idxW h` (a narrow word's
  index), `idxA h` (a wide word's); their values as numbers (`tagW_toNat`, `tierW_toNat'`,
  `idxW_toNat`, `idxA_toNat`, `mask32_toNat`), bounds (`tagW_lt`, `tierW_le`, `idxW_lt`, `mask_lt`)
  and the laws of `hdW`/`hdA` (`hdW_tag`, `hdW_tier`, `hdW_idx`, `hdW_lt`, `hdA_…`).
* **The bridge**: `decI_inj`/`decI_inj_iff`/`decI_beq`/`decI_bne` (two words below `2^32` decode to
  the same handle iff they are equal), `decI_mask` (only the low 32 bits count), `decI_tag`,
  `decI_tag_eq`, `decI_tag_beq`, `decI_isWide`, `decI_idx` (narrow), `decI_idxA` (wide),
  `isPersistent_decI`, `decI_word_self`, `decI_eq_iff`, `decI_word`, and the list forms
  `contains_map_decI`, `findIdx_map_decI`, `map_decI_inj`, `map_decI_beq`.
* **Expression tags**: `decE_tag`, `decE_tag_eq`, `decE_tag_beq`, `tag_beq_w` (any spelling of a
  small numeral), and one lemma per `ETag` constant a proof needs (`decE_tag_const`,
  `decE_tag_const_beq`, `decI_tag_const_beq`, …).

The tag lemmas are stated with `tagW h`, the term `vcgen` leaves for an L tag read `⟦h⟧.tag`.
Every proof goes through `toNat` and `omega`, as con-ron's `Handle.lean` does (no `bv_decide`).
-/

open ConRon.Arena

namespace L.Arena

/-! ## Encoding -/

/-- The handle of any kind a word encodes (`decE` at expressions). -/
def decI {k : IdxKind} (w : Word) : Idx k := Idx.ofWord w.toUInt32

theorem decE_eq (w : Word) : decE w = decI w := rfl

/-- The index of a handle, as a word. -/
def hix {k : IdxKind} (x : Idx k) : Word := UInt64.ofNat x.idxNat

theorem decI_word_toNat {k : IdxKind} (w : Word) : (decI w : Idx k).word.toNat = w.toNat % 2 ^ 32 := by
  simp [decI, UInt64.toNat_toUInt32]

/-- The shape of a decoded word: wide iff bit 30 is set. -/
theorem decI_isWide {k : IdxKind} (h : Word) :
    (decI h : Idx k).isWide = decide (h.toNat / 2 ^ 30 % 2 = 1) := by
  have e := decI_word_toNat (k := k) h
  simp only [Idx.isWide]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← UInt32.toNat_inj]
  simp only [UInt32.toNat_mod, UInt32.toNat_div, e]
  simp; omega

theorem decI_isWide_false {k : IdxKind} (h : Word) (hn : h.toNat / 2 ^ 30 % 2 = 0) :
    (decI h : Idx k).isWide = false := by
  rw [decI_isWide]; simp [hn]

theorem decI_isWide_true {k : IdxKind} (h : Word) (hw : h.toNat / 2 ^ 30 % 2 = 1) :
    (decI h : Idx k).isWide = true := by
  rw [decI_isWide]; simp [hw]

/-- The index of a narrow word. -/
theorem decI_idx {k : IdxKind} (h : Word) (hn : h.toNat / 2 ^ 30 % 2 = 0) :
    (decI h : Idx k).idxNat = (idxW h).toNat := by
  have e := decI_word_toNat (k := k) h
  simp only [Idx.idxNat, Idx.index, decI_isWide_false h hn, Bool.false_eq_true, ↓reduceIte,
    UInt32.toNat_mod, e, idxW_toNat_narrow h hn]
  simp

/-- The index of a wide word. -/
theorem decI_idxA {k : IdxKind} (h : Word) (hw : h.toNat / 2 ^ 30 % 2 = 1) :
    (decI h : Idx k).idxNat = (idxA h).toNat := by
  have e := decI_word_toNat (k := k) h
  simp only [Idx.idxNat, Idx.index, decI_isWide_true h hw, ↓reduceIte,
    UInt32.toNat_mod, e, idxA_toNat_wide h hw]
  simp

/-- The index of any word: con-ron's `Idx.idxNat` is `idxG`. -/
theorem decI_idxG {k : IdxKind} (h : Word) : (decI h : Idx k).idxNat = (idxG h).toNat := by
  rcases Nat.mod_two_eq_zero_or_one (h.toNat / 2 ^ 30) with hn | hw
  · rw [decI_idx h hn, idxG_narrow h hn]
  · rw [decI_idxA h hw, idxA_toNat_wide h hw, idxG_toNat, ite_eq_left hw]

theorem hix_hdW {k : IdxKind} (g t i : Word) (hg : g.toNat < 16) (ht : t ≤ 1)
    (hi : i.toNat < 2 ^ 26) : hix (decI (hdW g t i) : Idx k) = i := by
  simp only [hix]
  rw [decI_idx _ (hdW_narrow g t i hg ht hi), hdW_idx g t i hg ht hi]; simp
grind_pattern [store_grind] hix_hdW => hix (decI (hdW g t i) : Idx k)

theorem hix_hdA {k : IdxKind} (t i : Word) (ht : t ≤ 1) (hi : i.toNat < 2 ^ 30) :
    hix (decI (hdA t i) : Idx k) = i := by
  simp only [hix]
  rw [decI_idxA _ (hdA_wide t i ht hi), hdA_idx t i ht hi]; simp
grind_pattern [store_grind] hix_hdA => hix (decI (hdA t i) : Idx k)

/-- The arena's narrow handle of node `n` of tier `b` is the L handle word. -/
theorem mk_eq {k : IdxKind} (g : UInt32) (b n : Nat) :
    (Idx.mk g (UInt32.ofNat b) (UInt32.ofNat n) : Idx k) =
      decI (hdW g.toUInt64 (UInt64.ofNat b) (UInt64.ofNat n)) := by
  simp only [decI, hdW, Idx.mk]
  congr 1
  apply UInt32.toNat_inj.mp
  simp only [UInt64.toNat_toUInt32, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat',
    UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat', UInt32.toNat_toUInt64]
  simp only [show (2147483648 : UInt32).toNat = 2147483648 from rfl,
    show (67108864 : UInt32).toNat = 67108864 from rfl,
    show (0x80000000 : UInt64).toNat = 2147483648 from rfl,
    show (0x4000000 : UInt64).toNat = 67108864 from rfl]
  omega

/-- The arena's wide (`app`) handle of node `n` of tier `b` is the L handle word. -/
theorem mkWide_eq {k : IdxKind} (b n : Nat) :
    (Idx.mkWide (UInt32.ofNat b) (UInt32.ofNat n) : Idx k) =
      decI (hdA (UInt64.ofNat b) (UInt64.ofNat n)) := by
  simp only [decI, hdA, Idx.mkWide]
  congr 1
  apply UInt32.toNat_inj.mp
  simp only [UInt64.toNat_toUInt32, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat',
    UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat']
  simp only [show (2147483648 : UInt32).toNat = 2147483648 from rfl,
    show (1073741824 : UInt32).toNat = 1073741824 from rfl,
    show (0x80000000 : UInt64).toNat = 2147483648 from rfl,
    show (0x40000000 : UInt64).toNat = 1073741824 from rfl]
  omega

/-! ## Stores by shape

A store's handles are narrow with its tag, or wide (the expression `app` store). The generic
store library (`StoreLib`, `ConsLib`) is stated over the pair `(tag, wide)`. -/

/-- The handle word of node `i` of tier `t` of a store with tag `g` and shape `wide`. -/
def hdS (g : UInt32) (wide : Bool) (t i : Word) : Word := if wide then hdA t i else hdW g.toUInt64 t i

/-- A store's per-tier node capacity: con-ron's `Idx.wideCap` (`2^30`) for the wide store, else
`Idx.idxCap` (`2^26`). -/
def capS (wide : Bool) : Nat := if wide then 2 ^ 30 else 2 ^ 26

theorem capS_le (wide : Bool) : capS wide ≤ 2 ^ 30 := by cases wide <;> simp [capS]
grind_pattern capS_le => capS wide

theorem capS_eq (wide : Bool) : capS wide = if wide then Idx.wideCap else Idx.idxCap := by
  cases wide <;> rfl

/-- con-ron's handle constructor by shape: `Idx.mkWide` for the wide store, else `Idx.mk`. -/
def mkS {k : IdxKind} (g : UInt32) (wide : Bool) (tr n : UInt32) : Idx k :=
  if wide then Idx.mkWide tr n else Idx.mk g tr n

theorem mkS_eq {k : IdxKind} (g : UInt32) (wide : Bool) (b n : Nat) :
    (mkS g wide (UInt32.ofNat b) (UInt32.ofNat n) : Idx k) =
      decI (hdS g wide (UInt64.ofNat b) (UInt64.ofNat n)) := by
  cases wide
  · exact mk_eq g b n
  · exact mkWide_eq b n

section hdS
variable (g : UInt32) (wide : Bool) (t i : Word) (hg : g.toNat < 16) (ht : t ≤ 1)
  (hi : i.toNat < capS wide)
include hg ht hi

theorem hdS_lt : (hdS g wide t i).toNat < 2 ^ 32 := by
  cases wide
  · exact hdW_lt _ t i (by simpa using hg) ht (by simpa [capS] using hi)
  · exact hdA_lt t i ht (by simpa [capS] using hi)

theorem hdS_tier : tierW (hdS g wide t i) = t := by
  cases wide
  · exact hdW_tier _ t i (by simpa using hg) ht (by simpa [capS] using hi)
  · exact hdA_tier t i ht (by simpa [capS] using hi)

theorem hix_hdS {k : IdxKind} : hix (decI (hdS g wide t i) : Idx k) = i := by
  cases wide
  · exact hix_hdW _ t i (by simpa using hg) ht (by simpa [capS] using hi)
  · exact hix_hdA t i ht (by simpa [capS] using hi)

end hdS
grind_pattern [store_grind] hix_hdS => hix (decI (hdS g wide t i) : Idx k)

/-! ## The bridge: words below `2^32` and the twin's handles -/

theorem decI_word {k : IdxKind} (x : Idx k) : decI x.word.toUInt64 = x := by
  cases x; simp [decI]

theorem decI_word_self {k : IdxKind} (w : Word) (hw : w.toNat < 2 ^ 32) :
    (decI w : Idx k).word.toUInt64 = w := by
  apply UInt64.toNat_inj.mp; simp [decI]; omega

/-- A handle is the decoding of a word below `2^32` iff that word is the handle's. -/
theorem word_decI {k : IdxKind} (x : Idx k) (w : Word) (hw : w.toNat < 2 ^ 32) :
    (x.word.toUInt64 = w) = (x = decI w) := by
  cases x with | ofWord u =>
  simp only [decI, Idx.ofWord.injEq, eq_iff_iff]
  constructor
  · intro h; subst h; apply UInt32.toNat_inj.mp; simp
  · intro h; subst h; apply UInt64.toNat_inj.mp; simp; omega

theorem decI_eq_iff {k : IdxKind} (w : Word) (hw : w.toNat < 2 ^ 32) (n : Idx k) :
    (decI w = n) ↔ (w = n.word.toUInt64) := by
  constructor
  · rintro rfl; exact (decI_word_self w hw).symm
  · rintro rfl; exact decI_word _

theorem decI_inj {k : IdxKind} {v w : Word} (hv : v.toNat < 2 ^ 32) (hw : w.toNat < 2 ^ 32)
    (h : (decI v : Idx k) = decI w) : v = w := by
  rw [← decI_word_self v hv, ← decI_word_self w hw, h]

theorem decI_inj_iff {k : IdxKind} {v w : Word} (hv : v.toNat < 2 ^ 32) (hw : w.toNat < 2 ^ 32) :
    (decI v : Idx k) = decI w ↔ v = w :=
  ⟨decI_inj hv hw, fun h => h ▸ rfl⟩

theorem decI_beq {k : IdxKind} (v w : Word) (hv : v.toNat < 2 ^ 32) (hw : w.toNat < 2 ^ 32) :
    ((decI v : Idx k) == decI w) = decide (v = w) := by
  by_cases h : v = w
  · subst h; simp
  · simp [h, mt (decI_inj hv hw) h]

theorem decI_bne {k : IdxKind} (v w : Word) (hv : v.toNat < 2 ^ 32) (hw : w.toNat < 2 ^ 32) :
    ((decI v : Idx k) != decI w) = !decide (v = w) := by
  rw [bne, decI_beq v w hv hw]

/-- Only the low 32 bits of a word reach its handle. -/
theorem decI_mask {k : IdxKind} (w : Word) : (decI (w &&& 4294967295) : Idx k) = decI w := by
  simp only [decI]; congr 1
  apply UInt32.toNat_inj.mp
  simp only [UInt64.toNat_toUInt32, mask32_toNat]; omega

theorem decE_mask (y : Word) : decE (y &&& 4294967295) = decE y := decI_mask y

/-- The tag of a decoded word (con-ron's `Idx.tag`: `app`'s for a wide word). -/
theorem decI_tag {k : IdxKind} (h : Word) (hh : h.toNat < 2 ^ 32) :
    (decI h : Idx k).tag = (tagW h).toUInt32 := by
  have e := decI_word_toNat (k := k) h
  have t := tagW_toNat h
  apply UInt32.toNat_inj.mp
  simp only [Idx.tag, decI_isWide, UInt64.toNat_toUInt32]
  rcases Nat.mod_two_eq_zero_or_one (h.toNat / 2 ^ 30) with hw | hw
  · simp only [hw] at t ⊢
    simp [UInt32.toNat_mod, UInt32.toNat_div, e, t]
    omega
  · simp only [hw] at t ⊢
    simp [t]

theorem decI_tag_eq {k : IdxKind} (h : Word) (hh : h.toNat < 2 ^ 32) (g : Nat) (hg : g < 16) :
    ((decI h : Idx k).tag = UInt32.ofNat g) ↔ (tagW h = UInt64.ofNat g) := by
  rw [decI_tag h hh]
  have hgt := tagW_lt h hh
  constructor
  · intro e; apply UInt64.toNat_inj.mp
    have := congrArg UInt32.toNat e
    simp [UInt64.toNat_toUInt32] at this ⊢; omega
  · intro e; rw [e]; apply UInt32.toNat_inj.mp; simp

theorem decI_tag_beq {k : IdxKind} (h : Word) (hh : h.toNat < 2 ^ 32) (g : Nat) (hg : g < 16) :
    ((decI h : Idx k).tag == UInt32.ofNat g) = decide (tagW h = UInt64.ofNat g) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, decI_tag_eq h hh g hg]

/-- The tier bit of a handle word, at any handle kind. -/
theorem isPersistent_decI {k : IdxKind} (w : Word) (_hw : w.toNat < 2 ^ 32) :
    (decI w : Idx k).isPersistent = ((w >>> 31) &&& 1 == 0) := by
  have e := decI_word_toNat (k := k) w
  have := bit31_toNat w
  simp only [Idx.isPersistent, Idx.tier]
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← UInt32.toNat_inj, ← UInt64.toNat_inj]
  simp only [UInt32.toNat_div, e]
  simp; omega

/-- The tier bit of a handle word, at expression handles (as `app`'s skip test uses it). -/
theorem isPersistent_decE (w : Word) (hw : w.toNat < 2 ^ 32) :
    (decE w).isPersistent = ((w >>> 31) &&& 1 == 0) := by
  rw [decE_eq]; exact isPersistent_decI w hw

/-- The tier bit, at any handle kind, as `tierW`. -/
theorem decI_pers {k : IdxKind} (h : Word) (hh : h.toNat < 2 ^ 32) :
    (decI h : Idx k).isPersistent = (tierW h == 0) := by
  rw [isPersistent_decI h hh]; rfl

theorem decE_pers (h : Word) (hh : h.toNat < 2 ^ 32) : (decE h).isPersistent = (tierW h == 0) :=
  decI_pers h hh

/-- The tier bit, as `tierW`, for any word: only its low 32 bits reach the handle, and bit 31 is
one of them. -/
theorem decE_tierW (h : Word) : (decE h).isPersistent = (tierW h == 0) := by
  rw [← decE_mask h, decE_pers _ (mask_lt h)]
  congr 1
  apply UInt64.toNat_inj.mp
  rw [tierW_toNat', tierW_toNat', mask32_toNat]; omega

/-! ## Decoding a store's handle -/

section hdSdec
variable (g : UInt32) (wide : Bool) (t i : Word) (hg : g.toNat < 16) (ht : t ≤ 1)
  (hi : i.toNat < capS wide)
include hg ht hi

theorem decI_hdS_idx {k : IdxKind} : (decI (hdS g wide t i) : Idx k).idxNat = i.toNat := by
  have := congrArg UInt64.toNat (hix_hdS (k := k) g wide t i hg ht hi)
  have hlt : (decI (hdS g wide t i) : Idx k).idxNat < 2 ^ 32 := by
    simp only [Idx.idxNat]; exact (Idx.index _).toNat_lt
  simp only [hix, UInt64.toNat_ofNat'] at this
  omega

theorem decI_hdS_isWide {k : IdxKind} : (decI (hdS g wide t i) : Idx k).isWide = wide := by
  cases wide
  · exact decI_isWide_false _ (hdW_narrow _ t i (by simpa using hg) ht (by simpa [capS] using hi))
  · exact decI_isWide_true _ (hdA_wide t i ht (by simpa [capS] using hi))

theorem decI_hdS_pers {k : IdxKind} :
    (decI (hdS g wide t i) : Idx k).isPersistent = (t == 0) := by
  rw [decI_pers _ (hdS_lt g wide t i hg ht hi), hdS_tier g wide t i hg ht hi]

theorem decI_hdS_tag {k : IdxKind} (hwt : wide = true → g = 4) :
    (decI (hdS g wide t i) : Idx k).tag = g := by
  rw [decI_tag _ (hdS_lt g wide t i hg ht hi)]
  cases wide
  · simp only [hdS, Bool.false_eq_true, ↓reduceIte]
    rw [hdW_tag _ t i (by simpa using hg) ht (by simpa [capS] using hi)]; simp
  · simp only [hdS, ↓reduceIte]
    rw [hdA_tag t i ht (by simpa [capS] using hi), hwt rfl]; rfl

end hdSdec

/-! ## Tags of expression handles (`decE`, the `ETag` constants) -/

theorem decE_tag (h : Word) (hh : h.toNat < 2 ^ 32) : (decE h).tag = (tagW h).toUInt32 :=
  decI_tag h hh

theorem decE_idx (h : Word) (hn : h.toNat / 2 ^ 30 % 2 = 0) : (decE h).idxNat = (idxW h).toNat :=
  decI_idx h hn

theorem decE_idxA (h : Word) (hw : h.toNat / 2 ^ 30 % 2 = 1) : (decE h).idxNat = (idxA h).toNat :=
  decI_idxA h hw

theorem decE_tag_eq (e : Word) (hh : e.toNat < 2 ^ 32) (k : Nat) (hk : k < 16) :
    ((decE e).tag = UInt32.ofNat k) ↔ tagW e = UInt64.ofNat k := decI_tag_eq e hh k hk

theorem decE_tag_beq (e : Word) (hh : e.toNat < 2 ^ 32) (k : Nat) (hk : k < 16) :
    ((decE e).tag == UInt32.ofNat k) = decide (tagW e = UInt64.ofNat k) := decI_tag_beq e hh k hk

/-- The tag compared with a tag word `t`. -/
theorem decI_tag_eqW {k : IdxKind} (b : Word) (hb : b.toNat < 2 ^ 32) (t : Word) (ht : t.toNat < 16) :
    (decI b : Idx k).tag = t.toUInt32 ↔ tagW b = t := by
  have e := decI_tag_eq (k := k) b hb t.toNat ht
  rw [UInt64.ofNat_toNat] at e
  rw [← e]; constructor <;> intro h <;> rw [h] <;> apply UInt32.toNat_inj.mp <;> simp <;> omega

theorem decE_tag_eqW (b : Word) (hb : b.toNat < 2 ^ 32) (t : Word) (ht : t.toNat < 16) :
    (decE b).tag = t.toUInt32 ↔ tagW b = t := decI_tag_eqW b hb t ht

/-- The tag compared with any spelling `t` of a small numeral `k` (an `ETag` constant). -/
theorem tag_beq_w (h : Word) (hh : h.toNat < 2 ^ 32) (k : Nat) (hk : k < 16) (t : UInt32)
    (ht : t = UInt32.ofNat k) (w : Word) (hw : UInt64.ofNat k = w) :
    ((decE h).tag == t) = decide (tagW h = w) := by
  rw [ht, decE_tag_beq h hh k hk, hw]

section etags
variable (e : Word) (hh : e.toNat < 2 ^ 32)
include hh
theorem decE_tag_sort : (decE e).tag = ETag.sort ↔ tagW e = 2 := decE_tag_eq e hh 2 (by decide)
theorem decE_tag_const : (decE e).tag = ETag.const ↔ tagW e = 3 := decE_tag_eq e hh 3 (by decide)
theorem decE_tag_app : (decE e).tag = ETag.app ↔ tagW e = 4 := decE_tag_eq e hh 4 (by decide)
theorem decE_tag_forallE : (decE e).tag = ETag.forallE ↔ tagW e = 6 :=
  decE_tag_eq e hh 6 (by decide)
theorem decE_tag_lit : (decE e).tag = ETag.lit ↔ tagW e = 8 := decE_tag_eq e hh 8 (by decide)
theorem decE_tag_sort_beq : ((decE e).tag == ETag.sort) = decide (tagW e = 2) :=
  decE_tag_beq e hh 2 (by decide)
theorem decE_tag_const_beq : ((decE e).tag == ETag.const) = decide (tagW e = 3) :=
  decE_tag_beq e hh 3 (by decide)
theorem decE_tag_app_beq : ((decE e).tag == ETag.app) = decide (tagW e = 4) :=
  decE_tag_beq e hh 4 (by decide)
theorem decE_tag_lam_beq : ((decE e).tag == ETag.lam) = decide (tagW e = 5) :=
  decE_tag_beq e hh 5 (by decide)
theorem decE_tag_forallE_beq : ((decE e).tag == ETag.forallE) = decide (tagW e = 6) :=
  decE_tag_beq e hh 6 (by decide)
theorem decE_tag_lit_beq : ((decE e).tag == ETag.lit) = decide (tagW e = 8) :=
  decE_tag_beq e hh 8 (by decide)
theorem decI_tag_fvar_beq : ((decI e : EIdx).tag == ETag.fvar) = decide (tagW e = 1) :=
  decI_tag_beq e hh 1 (by decide)
theorem decI_tag_const_beq : ((decI e : EIdx).tag == ETag.const) = decide (tagW e = 3) :=
  decI_tag_beq e hh 3 (by decide)
theorem decI_tag_app_beq : ((decI e : EIdx).tag == ETag.app) = decide (tagW e = 4) :=
  decI_tag_beq e hh 4 (by decide)
theorem decI_tag_forallE_beq : ((decI e : EIdx).tag == ETag.forallE) = decide (tagW e = 6) :=
  decI_tag_beq e hh 6 (by decide)
end etags

/-! ## Lists of handle words -/

section lists
variable {k : IdxKind}

theorem contains_map_decI {k : IdxKind} (x : Word) (hx : x.toNat < 2 ^ 32) : ∀ (ws : List Word),
    (∀ w ∈ ws, w.toNat < 2 ^ 32) → (ws.map (decI : Word → Idx k)).contains (decI x) = ws.contains x
  | [], _ => rfl
  | w :: ws, h => by
    simp only [List.map_cons, List.contains_cons]
    rw [decI_beq x w hx (h w (by simp)), contains_map_decI x hx ws (fun v hv => h v (by simp [hv]))]
    by_cases e : w = x
    · subst e; simp
    · simp [Ne.symm e]

/-- Membership, as a proposition. -/
theorem contains_map_decI_iff {ws : List Word} (hws : ∀ w ∈ ws, w.toNat < 2 ^ 32) {x : Word}
    (hx : x.toNat < 2 ^ 32) :
    (ws.map (fun w => (decI w : Idx k))).contains (decI x) = true ↔ x ∈ ws := by
  rw [contains_map_decI x hx ws hws]; simp

theorem findIdx_map_decI {k : IdxKind} (x : Word) (hx : x.toNat < 2 ^ 32) :
    ∀ ws : List Word, (∀ w ∈ ws, w.toNat < 2 ^ 32) →
    (ws.map (decI : Word → Idx k)).findIdx? (fun p => p == decI x) = ws.findIdx? (· == x)
  | [], _ => rfl
  | w :: ws, h => by
    have e : ((decI w : Idx k) == decI x) = (w == x) := by
      rw [decI_beq w x (h w (by simp)) hx]; rfl
    have ih := findIdx_map_decI (k := k) x hx ws (fun v hv => h v (by simp [hv]))
    simp [List.findIdx?_cons, e, ih]

theorem map_decI_inj {k : IdxKind} : ∀ (ws vs : List Word), (∀ w ∈ ws, w.toNat < 2 ^ 32) →
    (∀ w ∈ vs, w.toNat < 2 ^ 32) → (ws.map (decI (k := k)) = vs.map decI ↔ ws = vs)
  | [], [], _, _ => by simp
  | [], _ :: _, _, _ => by simp
  | _ :: _, [], _, _ => by simp
  | w :: ws, v :: vs, hw, hv => by
    simp only [List.map_cons, List.cons.injEq]
    rw [map_decI_inj ws vs (fun x hx => hw x (by simp [hx])) (fun x hx => hv x (by simp [hx])),
      decI_inj_iff (hw w (by simp)) (hv v (by simp))]

theorem map_decI_beq (ws vs : List Word) (hw : ∀ w ∈ ws, w.toNat < 2 ^ 32)
    (hv : ∀ w ∈ vs, w.toNat < 2 ^ 32) :
    ((ws.map (decI : Word → Idx k)) == vs.map decI) = decide (ws = vs) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, map_decI_inj ws vs hw hv]

end lists

end L.Arena
