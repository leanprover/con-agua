import ConAgua.Arena.Refine
import ConAgua.Arena.StoreFields
import ConAgua.Arena.GrindAttr

/-!
# Handle words: encoding, decoding, and the bridge to the twin's `Idx`, proved once

A handle of con-ron (`ConRon/Arena/Handle.lean`, `Idx`) *is* its 32-bit word
`tag · 2^28 + tier · 2^27 + index`. L keeps the word: it hashes it, packs two into a cons key and
compares handles with `==`. The relation between an L word `w` and the twin's handle is
`decI w` (`Idx.ofWord w.toUInt32`).

This file is the one place that knows the encoding. Proofs use the names and laws below instead
of unfolding the shifts, masks and powers of two:

* **Encode and decode**: `hdW g t i` (the handle word of node `i` of tier `t` of tag `g`),
  `tagW h = h >>> 28`, `tierW h` (bit 27), `idxW h` (the low 27 bits); the laws
  `hdW_tag`, `hdW_tier`, `hdW_idx`, `hdW_lt`.
* **The bridge**: `decI_inj`/`decI_inj_iff`/`decI_beq`/`decI_bne` (two words below `2^32` decode to
  the same handle iff they are equal), `decI_mask` (only the low 32 bits count), `decI_tag`,
  `decI_tag_eq`, `decI_tag_beq`, `decI_idx`, `isPersistent_decI`, `decI_word_self`,
  `decI_eq_iff`, `decI_word`, and the list forms `contains_map_decI`, `findIdx_map_decI`,
  `map_decI_inj`, `map_decI_beq`.

The tag lemmas are stated with `h >>> 28`, the term `vcgen` leaves for an L tag test `h >> 28`.
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

theorem hix_hdW {k : IdxKind} (g t i : Word) (hi : i.toNat < 2 ^ 27) :
    hix (decI (hdW g t i) : Idx k) = i := by
  simp only [hix, decI, hdW, Idx.idxNat, Idx.index]
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_ofNat', UInt32.toNat_mod, UInt64.toNat_toUInt32, UInt64.toNat_add,
    UInt64.toNat_mul]
  grind
grind_pattern [store_grind] hix_hdW => hix (decI (hdW g t i) : Idx k)

/-- The arena's handle of node `n` of tier `b` is the L handle word. -/
theorem mk_eq {k : IdxKind} (g : UInt32) (b n : Nat) :
    (Idx.mk g (UInt32.ofNat b) (UInt32.ofNat n) : Idx k) =
      decI (hdW g.toUInt64 (UInt64.ofNat b) (UInt64.ofNat n)) := by
  simp only [decI, hdW, Idx.mk]
  congr 1
  apply UInt32.toNat_inj.mp
  simp only [UInt64.toNat_toUInt32, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat',
    UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat', UInt32.toNat_toUInt64]
  simp only [show (268435456 : UInt32).toNat = 268435456 from rfl,
    show (134217728 : UInt32).toNat = 134217728 from rfl,
    show (0x10000000 : UInt64).toNat = 268435456 from rfl,
    show (0x8000000 : UInt64).toNat = 134217728 from rfl]
  omega

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

theorem decI_tag {k : IdxKind} (h : Word) (hh : h.toNat < 2 ^ 32) :
    (decI h : Idx k).tag = (h >>> 28).toUInt32 := by
  simp only [decI, Idx.tag]
  apply UInt32.toNat_inj.mp
  simp [UInt32.toNat_div, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  omega

theorem decI_idx {k : IdxKind} (h : Word) : (decI h : Idx k).idxNat = (idxW h).toNat := by
  simp only [decI, Idx.idxNat, Idx.index]
  simp only [UInt32.toNat_mod, UInt64.toNat_toUInt32, idxW_toNat]
  simp

theorem decI_tag_eq {k : IdxKind} (h : Word) (hh : h.toNat < 2 ^ 32) (g : Nat) (hg : g < 16) :
    ((decI h : Idx k).tag = UInt32.ofNat g) ↔ (h >>> 28 = UInt64.ofNat g) := by
  rw [decI_tag h hh]
  have hgt := shr28_lt h hh
  constructor
  · intro e; apply UInt64.toNat_inj.mp
    have := congrArg UInt32.toNat e
    simp [UInt64.toNat_toUInt32] at this ⊢; omega
  · intro e; rw [e]; apply UInt32.toNat_inj.mp; simp

theorem decI_tag_beq {k : IdxKind} (h : Word) (hh : h.toNat < 2 ^ 32) (g : Nat) (hg : g < 16) :
    ((decI h : Idx k).tag == UInt32.ofNat g) = decide (h >>> 28 = UInt64.ofNat g) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, decI_tag_eq h hh g hg]

/-- The tier bit of a handle word, at any handle kind. -/
theorem isPersistent_decI {k : IdxKind} (w : Word) (hw : w.toNat < 2 ^ 32) :
    (decI w : Idx k).isPersistent = ((w >>> 27) &&& 1 == 0) := by
  simp only [decI, Idx.isPersistent, Idx.tier]
  have := bit27_toNat w
  have : (w.toUInt32 / 134217728 % 2).toNat = w.toNat / 2 ^ 27 % 2 := by
    simp [UInt32.toNat_mod, UInt32.toNat_div, UInt64.toNat_toUInt32]; omega
  grind

/-- The tier bit of a handle word, at expression handles (as `app`'s skip test uses it). -/
theorem isPersistent_decE (w : Word) (hw : w.toNat < 2 ^ 32) :
    (decE w).isPersistent = ((w >>> 27) &&& 1 == 0) := by
  rw [decE_eq]; exact isPersistent_decI w hw

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
