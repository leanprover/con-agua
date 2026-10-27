module

public import ConAgua.Scan.WordLink
public import ConAgua.Scan.Values
import ConAgua.Census.Attr
public import ConLeche.Frontend.Scan.Naive
import ConAgua.Scan.KeyLink
import ConAgua.Scan.LeafLink
import ConAgua.Scan.Link
import ConAgua.Scan.LitLink
import ConLeche.Frontend.Scan.Equiv.Scalars
import Std.Data.DTreeMap.Internal.Operations
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-!
# The value scanners against con-leche's originals

`slot_nat`, `scan_quoted_nat`, `scan_binder_info`, `scan_hints` (`ConAgua.Scan.Values`'s models,
against `ConLeche.Frontend.{slotNat omitted — inlined everywhere, scanQuotedNat, scanBinderInfo,
scanHints}`). Each proof follows the leaf links' style: `byteAt_lt_iff` is the one new bridging
fact (`byteAt_pos_iff`'s `byteAt`/`byteW` equality, plus the bound every model condition also
carries, `pos < len(IN.u8)`, which `byteAt`'s "`0` past the end" makes automatic either way), and
`matchLit_eq_N_words` is `LitLink.matchLitN_eq_isPrefixOf` reused against `WORDS` instead of
`LITS`. `scan_hints`' proof additionally composes `LeafLink.keyEnd_toUInt64_eq`,
`KeyLink.keyAt_eq_keyAtN`/`valueAt_eq_valueAtN`, and the two `keyEnd_ne_zero_*` facts that supply
`keyAt_eq_keyAtN`'s in-bounds hypothesis.

`scan_nat_list`'s link (end and item count) is `ConAgua.Scan.natList_link` in `RecordsLink.lean`.
-/

namespace ConAgua.Scan

open ConLeche.Frontend
open L (Word)
open L.Scan.Values (slotNatN quotedNatN binderInfoN hintsN WORDS natListN natListEntryN)
open L.Scan.Values.hintsN (hintsObjN hintsNumN)
open L.Scan.Lit (matchLitN)
open L.Scan.Key (keyAtN valueAtN)
open L.Scan.Leaves (numEndN skipDigitsN skipWsN keyEndN)
open L.Scan.Utf8 (byteW)

/-! ## The `WORDS` literal match, reusing `LitLink`'s generic `matchLitN_eq_isPrefixOf` -/

theorem WORDS_ne_zero : ∀ j (h : j < WORDS.length), WORDS[j] ≠ 0 := by decide

theorem matchLit_eq_N_words (b : ByteArray) (i : USize) (hsize : b.size < USize.size) (s : String)
    (o n : Nat) (hs : (WORDS.drop o).take n = lit s) (hL : o + n ≤ WORDS.length)
    (hlen : s.toUTF8.size < USize.size) :
    matchLit b i s.toUTF8 0 = matchLitN b.data i.toNat WORDS o n 0 := by
  rw [matchLit_lit b i s hlen, matchLitN_eq_isPrefixOf _ _ _ _ _ _ hL WORDS_ne_zero, ← hs]
  simp [tailAt, bytes_eq_of_size_lt hsize]

theorem lit_default : (WORDS.drop 0).take 8 = lit "default\"" := by rw [lit_eq_toByteArray]; rfl
theorem lit_implicit : (WORDS.drop 8).take 9 = lit "implicit\"" := by rw [lit_eq_toByteArray]; rfl
theorem lit_strictImplicit : (WORDS.drop 17).take 15 = lit "strictImplicit\"" := by
  rw [lit_eq_toByteArray]; rfl
theorem lit_instImplicit : (WORDS.drop 32).take 13 = lit "instImplicit\"" := by
  rw [lit_eq_toByteArray]; rfl
theorem lit_abbrev : (WORDS.drop 45).take 7 = lit "abbrev\"" := by rw [lit_eq_toByteArray]; rfl
theorem lit_opaque : (WORDS.drop 52).take 7 = lit "opaque\"" := by rw [lit_eq_toByteArray]; rfl

/-! ## `key_end`'s bound, needed for `key_at`'s precondition inside `scan_hints` -/

/-- A nonzero `keyEnd` is the position of the key's closing quote, inside the array (con-leche's
own recursion: it only ever returns `0` — out of bounds or a control byte — or the position `j`
where it found the quote, with `j < b.usize` already in hand at that step). -/
theorem keyEnd_ne_zero_lt (b : ByteArray) (j : USize) (hne : keyEnd b j ≠ 0) :
    keyEnd b j < b.usize := by
  fun_induction keyEnd b j with
  | case1 j h c hc => exact h
  | case2 j h c hc hb => exact absurd rfl hne
  | case3 j h c hc hb ih => exact ih hne
  | case4 j h => exact absurd rfl hne

/-- A nonzero `keyEnd b j` is at or past `j` (the recursion only ever steps forward). -/
theorem keyEnd_ne_zero_ge (b : ByteArray) (j : USize) (hne : keyEnd b j ≠ 0) :
    j ≤ keyEnd b j := by
  fun_induction keyEnd b j with
  | case1 j h c hc => rw [USize.le_iff_toNat_le]; omega
  | case2 j h c hc hb => exact absurd rfl hne
  | case3 j h c hc hb ih =>
    have hih := ih hne
    have hstep : j.toNat + 1 = (j + 1).toNat := (usizeStep b j h).symm
    rw [USize.le_iff_toNat_le] at hih ⊢
    omega
  | case4 j h => exact absurd rfl hne

/-- `Key.ctorIdx`, as a word, picks out `.kRegular` (`51`, `scan_hints`' only recognised key). -/
theorem key_ctorIdx_word_eq_regular_iff (k : Key) : UInt64.ofNat k.ctorIdx = 51 ↔ k = Key.kRegular := by
  cases k <;> decide

variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)

include h64 hsize in
/-- The bridge every byte compare in this file goes through: at a position `pos` whose word form
is `wpos` (equal `.toNat`), con-leche's `byteAt` agrees with a byte literal iff the model's
`byteW` does with its word form *and* `wpos` is in bounds — the bound is actually automatic either
way (`byteAt`/`byteW` both read `0` past the end, and no literal here is `0`), stated because
every model condition carries it. -/
theorem byteAt_lt_iff (pos : USize) (wpos : Word) (lit : Nat) (hlit0 : 0 < lit) (hlit256 : lit < 256)
    (heq : pos.toNat = wpos.toNat) :
    byteAt b pos = (OfNat.ofNat lit : UInt8) ↔
      (wpos < UInt64.ofNat b.data.size ∧ byteW b.data wpos = (OfNat.ofNat lit : Word)) := by
  have hsize64 : b.size < 2 ^ 64 := by omega
  constructor
  · intro h
    refine ⟨?_, (byteAt_pos_iff b h64 hsize64 pos wpos lit hlit256 heq).mp h⟩
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (show b.data.size < 2 ^ 64 by
      have : b.data.size = b.size := rfl; omega)]
    by_cases hb : wpos.toNat < b.data.size
    · exact hb
    · exfalso
      rw [byteAt_eq_getD b h64 hsize64, heq] at h
      rw [Array.getD, dite_eq_right hb] at h
      have := congrArg UInt8.toNat h
      simp only [UInt8.toNat_ofNat] at this
      omega
  · intro ⟨_, h⟩
    exact (byteAt_pos_iff b h64 hsize64 pos wpos lit hlit256 heq).mpr h

/-! ## `slot_nat` -/

/-! ## `scan_quoted_nat` -/

include h64 hsize in
/-- `scan_quoted_nat(i)`, through the model: `"digits"`. -/
@[refines_part ConLeche.Frontend.scanQuotedNat "validity"]
theorem scanQuotedNat_eq_quotedNatN (i : USize) :
    okW (scanQuotedNat b i) = quotedNatN b.data i.toUInt64 := by
  have hsize64 : b.size < 2 ^ 64 := by omega
  have hcond : byteAt b i = 34 ↔ (i.toUInt64 < UInt64.ofNat b.data.size ∧ byteW b.data i.toUInt64 = 34) :=
    byteAt_lt_iff b h64 hsize i i.toUInt64 34 (by decide) (by decide) (by rw [USize.toNat_toUInt64])
  have hskip_eq : (skipDigits b (i + 1)).toUInt64 =
      UInt64.ofNat (skipDigitsN b.data (i.toUInt64 + 1).toNat) := by
    have hi1 : (i + 1).toNat = (i.toUInt64 + 1).toNat := by
      simp only [USize.toNat_add, UInt64.toNat_add, USize.toNat_ofNat, UInt64.toNat_ofNat,
        USize.toNat_toUInt64, h64] <;> omega
    rw [skipDigits_toUInt64_eq b h64 hsize64, hi1]
  have heqcond : skipDigits b (i + 1) = i + 1 ↔
      UInt64.ofNat (skipDigitsN b.data (i.toUInt64 + 1).toNat) = i.toUInt64 + 1 := by
    have hi1' : (i + 1).toUInt64 = i.toUInt64 + 1 := by rw [add_toUInt64 h64, ofNat_toUInt64 h64]
    rw [← hskip_eq, ← hi1', eq_toUInt64_iff]
  have hcond2 : byteAt b (skipDigits b (i + 1)) = 34 ↔
      (UInt64.ofNat (skipDigitsN b.data (i.toUInt64 + 1).toNat) < UInt64.ofNat b.data.size ∧
        byteW b.data (UInt64.ofNat (skipDigitsN b.data (i.toUInt64 + 1).toNat)) = 34) := by
    rw [← hskip_eq]
    exact byteAt_lt_iff b h64 hsize (skipDigits b (i + 1)) (skipDigits b (i + 1)).toUInt64 34
      (by decide) (by decide) (by rw [USize.toNat_toUInt64])
  have hlast : (skipDigits b (i + 1) + 1).toUInt64 =
      UInt64.ofNat (skipDigitsN b.data (i.toUInt64 + 1).toNat) + 1 := by
    rw [add_toUInt64 h64, hskip_eq, ofNat_toUInt64 h64]
  unfold scanQuotedNat quotedNatN
  dsimp only
  simp only [apply_ite okW]
  unfold okW
  dsimp only
  by_cases h1 : byteAt b i = 34
  · obtain ⟨h1A, h1B⟩ := hcond.mp h1
    have h1b : (byteAt b i != 34) = false := by simpa using h1
    simp only [h1b]
    rw [ite_eq_left (⟨h1A, h1B⟩ : i.toUInt64 < UInt64.ofNat b.data.size ∧ byteW b.data i.toUInt64 = 34)]
    by_cases h2 : skipDigits b (i + 1) = i + 1
    · have h2b : (skipDigits b (i + 1) == i + 1) = true := by simpa using h2
      simp only [h2b, Bool.true_or, ite_true]
      rw [ite_eq_left (heqcond.mp h2)]
      simp
    · have h2b : (skipDigits b (i + 1) == i + 1) = false := by simpa using h2
      simp only [h2b, Bool.false_or]
      rw [ite_eq_right (fun hx => h2 (heqcond.mpr hx))]
      by_cases h3 : byteAt b (skipDigits b (i + 1)) = 34
      · obtain ⟨h3A, h3B⟩ := hcond2.mp h3
        have h3b : (byteAt b (skipDigits b (i + 1)) != 34) = false := by simpa using h3
        simp only [h3b]
        rw [ite_eq_left (⟨h3A, h3B⟩ :
          UInt64.ofNat (skipDigitsN b.data (i.toUInt64 + 1).toNat) < UInt64.ofNat b.data.size ∧
            byteW b.data (UInt64.ofNat (skipDigitsN b.data (i.toUInt64 + 1).toNat)) = 34)]
        simp [hlast]
      · have h3b : (byteAt b (skipDigits b (i + 1)) != 34) = true := by simpa using h3
        simp only [h3b, ite_true]
        rw [ite_eq_right (fun hx => h3 (hcond2.mpr hx))]
        simp
  · have h1b : (byteAt b i != 34) = true := by simpa using h1
    simp only [h1b, ite_true]
    rw [ite_eq_right (fun hx => h1 (hcond.mpr hx))]

/-! ## `scan_binder_info` -/

include h64 hsize in
/-- `scan_binder_info(i)`, through the model: the four `binderInfo` spellings. -/
theorem scanBinderInfo_eq_binderInfoN (i : USize) :
    (scanBinderInfo b i).toUInt64 = binderInfoN b.data i.toUInt64 := by
  have hsizeU : b.size < USize.size := by rw [USize.size_eq_two_pow, h64]; omega
  have hcond := byteAt_lt_iff b h64 hsize i i.toUInt64 34 (by decide) (by decide)
    (by rw [USize.toNat_toUInt64])
  have hi1 : (i + 1).toNat = (i.toUInt64 + 1).toNat := by
    simp only [USize.toNat_add, UInt64.toNat_add, USize.toNat_ofNat, UInt64.toNat_ofNat,
      USize.toNat_toUInt64, h64] <;> omega
  unfold scanBinderInfo binderInfoN
  rw [matchLit_eq_N_words b (i + 1) hsizeU "default\"" 0 8 lit_default (by decide)
        (size_toUTF8_lt "default\"" 8 rfl (by decide)),
      matchLit_eq_N_words b (i + 1) hsizeU "implicit\"" 8 9 lit_implicit (by decide)
        (size_toUTF8_lt "implicit\"" 9 rfl (by decide)),
      matchLit_eq_N_words b (i + 1) hsizeU "strictImplicit\"" 17 15 lit_strictImplicit (by decide)
        (size_toUTF8_lt "strictImplicit\"" 15 rfl (by decide)),
      matchLit_eq_N_words b (i + 1) hsizeU "instImplicit\"" 32 13 lit_instImplicit (by decide)
        (size_toUTF8_lt "instImplicit\"" 13 rfl (by decide)),
      hi1]
  simp only [apply_ite USize.toUInt64]
  by_cases h1 : byteAt b i = 34
  · obtain ⟨h1A, h1B⟩ := hcond.mp h1
    have h1b' : ¬ (byteAt b i != 34) = true := by simpa using h1
    rw [ite_eq_right h1b', ite_eq_left (⟨h1A, h1B⟩ : i.toUInt64 < UInt64.ofNat b.data.size ∧ byteW b.data i.toUInt64 = 34)]
    by_cases h2 : matchLitN b.data (i.toUInt64 + 1).toNat WORDS 0 8 0
    · simp only [h2, ite_true]
      rw [add_toUInt64 h64, ofNat_toUInt64 h64]
    · simp only [h2, Bool.false_eq_true, ite_false]
      by_cases h3 : matchLitN b.data (i.toUInt64 + 1).toNat WORDS 8 9 0
      · simp only [h3, ite_true]
        rw [add_toUInt64 h64, ofNat_toUInt64 h64]
      · simp only [h3, Bool.false_eq_true, ite_false]
        by_cases h4 : matchLitN b.data (i.toUInt64 + 1).toNat WORDS 17 15 0
        · simp only [h4, ite_true]
          rw [add_toUInt64 h64, ofNat_toUInt64 h64]
        · simp only [h4, Bool.false_eq_true, ite_false]
          by_cases h5 : matchLitN b.data (i.toUInt64 + 1).toNat WORDS 32 13 0
          · simp only [h5, ite_true]
            rw [add_toUInt64 h64, ofNat_toUInt64 h64]
          · simp only [h5, Bool.false_eq_true, ite_false]
            decide
  · have h1b' : (byteAt b i != 34) = true := by simpa using h1
    rw [ite_eq_left h1b', ite_eq_right (fun hx => h1 (hcond.mpr hx))]
    decide

/-! ## `scan_hints` -/

include h64 hsize in
/-- `scan_hints(i)`, through the model: validating only (the recovered `natVal`/the spelling
itself are dropped, as the model does). -/
theorem scanHints_eq_hintsN (i : USize) :
    okW (scanHints b i) = hintsN b.data i.toUInt64 := by
  have hsize64 : b.size < 2 ^ 64 := by omega
  have hsizeU : b.size < USize.size := by rw [USize.size_eq_two_pow, h64]; omega
  have hcond34 := byteAt_lt_iff b h64 hsize i i.toUInt64 34 (by decide) (by decide)
    (by rw [USize.toNat_toUInt64])
  have hcond123 := byteAt_lt_iff b h64 hsize i i.toUInt64 123 (by decide) (by decide)
    (by rw [USize.toNat_toUInt64])
  unfold scanHints hintsN
  simp only [apply_ite okW]
  unfold okW
  have hi1 : (i + 1).toNat = (i.toUInt64 + 1).toNat := by
    simp only [USize.toNat_add, UInt64.toNat_add, USize.toNat_ofNat, UInt64.toNat_ofNat,
      USize.toNat_toUInt64, h64] <;> omega
  rw [matchLit_eq_N_words b (i + 1) hsizeU "abbrev\"" 45 7 lit_abbrev (by decide)
        (size_toUTF8_lt "abbrev\"" 7 rfl (by decide)),
      matchLit_eq_N_words b (i + 1) hsizeU "opaque\"" 52 7 lit_opaque (by decide)
        (size_toUTF8_lt "opaque\"" 7 rfl (by decide)),
      hi1]
  by_cases h1 : byteAt b i = 34
  · have h1' : (byteAt b i == 34) = true := by simpa using h1
    rw [ite_eq_left h1', ite_eq_left (hcond34.mp h1)]
    by_cases h2 : matchLitN b.data (i.toUInt64 + 1).toNat WORDS 45 7 0
    · simp only [h2, ite_true]
      rw [add_toUInt64 h64, ofNat_toUInt64 h64]
    · simp only [h2, Bool.false_eq_true, ite_false]
      by_cases h3 : matchLitN b.data (i.toUInt64 + 1).toNat WORDS 52 7 0
      · simp only [h3, ite_true]
        rw [add_toUInt64 h64, ofNat_toUInt64 h64]
      · simp only [h3, Bool.false_eq_true, ite_false]
  · have h1' : ¬ (byteAt b i == 34) = true := by simpa using h1
    rw [ite_eq_right h1', ite_eq_right (fun hx => h1 (hcond34.mpr hx))]
    by_cases h4 : byteAt b i = 123
    · have h4' : (byteAt b i == 123) = true := by simpa using h4
      rw [ite_eq_left h4', ite_eq_left (hcond123.mp h4)]
      have hp_eq : (skipWs b (i + 1)).toUInt64 =
          UInt64.ofNat (skipWsN b.data (i.toUInt64 + 1).toNat) := by
        rw [skipWs_toUInt64_eq b h64 hsize64, hi1]
      rw [← hp_eq]
      unfold hintsObjN
      generalize hp_def : skipWs b (i + 1) = p
      have hcondP := byteAt_lt_iff b h64 hsize p p.toUInt64 34 (by decide) (by decide)
        (by rw [USize.toNat_toUInt64])
      by_cases h5 : byteAt b p = 34
      · have h5' : ¬ (byteAt b p != 34) = true := by simpa using h5
        obtain ⟨h5A, h5B⟩ := hcondP.mp h5
        rw [ite_eq_right h5', ite_eq_right (show ¬ ¬ (p.toUInt64 < UInt64.ofNat b.data.size ∧
          byteW b.data p.toUInt64 = 34) from fun hx => hx ⟨h5A, h5B⟩)]
        have hp1 : (p + 1).toNat = (p.toUInt64 + 1).toNat := by
          simp only [USize.toNat_add, UInt64.toNat_add, USize.toNat_ofNat, UInt64.toNat_ofNat,
            USize.toNat_toUInt64, h64] <;> omega
        have hke_eq : (keyEnd b (p + 1)).toUInt64 =
            UInt64.ofNat (keyEndN b.data (p.toUInt64 + 1).toNat) := by
          rw [keyEnd_toUInt64_eq b h64 hsize64, hp1]
        have hp_lt : p < b.usize := by
          rw [USize.lt_iff_toNat_lt, usize_toNat_eq b h64 hsize64]
          rw [UInt64.lt_iff_toNat_lt, USize.toNat_toUInt64] at h5A
          have : (UInt64.ofNat b.data.size).toNat = b.data.size := UInt64.toNat_ofNat_of_lt' hsize64
          have hbd : b.data.size = b.size := rfl
          omega
        have hpstep : (p + 1).toNat = p.toNat + 1 := usizeStep b p hp_lt
        by_cases h6 : keyEnd b (p + 1) = 0
        · have h6' : UInt64.ofNat (keyEndN b.data (p.toUInt64 + 1).toNat) = 0 := by
            rw [← hke_eq, h6]; rfl
          have h6b : (keyEnd b (p + 1) == 0) = true := by simpa using h6
          rw [ite_eq_left h6b, ite_eq_left h6']
        · have h6' : ¬ UInt64.ofNat (keyEndN b.data (p.toUInt64 + 1).toNat) = 0 := by
            rw [← hke_eq]
            exact fun hx => h6 ((eq_toUInt64_iff _ _).mpr (by rw [hx]; rfl))
          have h6b : ¬ (keyEnd b (p + 1) == 0) = true := by simpa using h6
          rw [ite_eq_right h6b, ite_eq_right h6']
          have hge := keyEnd_ne_zero_ge b (p + 1) h6
          have hlt := keyEnd_ne_zero_lt b (p + 1) h6
          rw [USize.le_iff_toNat_le] at hge
          rw [USize.lt_iff_toNat_lt, usize_toNat_eq b h64 hsize64] at hlt
          have hi' : p.toNat + 1 + (keyEnd b (p + 1) - (p + 1)).toNat < b.size := by
            rw [USize.toNat_sub_of_le _ _ hge]
            omega
          have hkl_eq : (keyEnd b (p + 1) - (p + 1)).toUInt64 =
              UInt64.ofNat (keyEndN b.data (p.toUInt64 + 1).toNat) - (p.toUInt64 + 1) := by
            rw [sub_toUInt64 h64, hke_eq, add_toUInt64 h64, ofNat_toUInt64 h64]
          have hkeyAt := keyAt_eq_keyAtN b h64 hsize p (keyEnd b (p + 1) - (p + 1)) hi'
          rw [hkl_eq] at hkeyAt
          by_cases h7 : keyAt b p (keyEnd b (p + 1) - (p + 1)) = Key.kRegular
          · have h7' : keyAtN b.data p.toUInt64
                (UInt64.ofNat (keyEndN b.data (p.toUInt64 + 1).toNat) - (p.toUInt64 + 1)) = 51 := by
              rw [← hkeyAt, h7]; rfl
            rw [ite_eq_right (show ¬ keyAtN b.data p.toUInt64
                (UInt64.ofNat (keyEndN b.data (p.toUInt64 + 1).toNat) - (p.toUInt64 + 1)) ≠ 51
              from fun hx => hx h7')]
            simp only [h7]
            have hv_eq := valueAt_eq_valueAtN b h64 hsize p (keyEnd b (p + 1))
            rw [hke_eq] at hv_eq
            by_cases h8 : valueAt b p (keyEnd b (p + 1)) = p
            · have h8' : valueAtN b.data p.toUInt64 (UInt64.ofNat (keyEndN b.data (p.toUInt64 + 1).toNat)) =
                  p.toUInt64 := by
                rw [← hv_eq, h8]
              have h8b : (valueAt b p (keyEnd b (p + 1)) == p) = true := by simpa using h8
              rw [h8b]
              simp only [h8', ite_true]
            · have h8' : ¬ valueAtN b.data p.toUInt64
                  (UInt64.ofNat (keyEndN b.data (p.toUInt64 + 1).toNat)) = p.toUInt64 := by
                rw [← hv_eq]
                intro hx; exact h8 ((eq_toUInt64_iff _ _).mpr hx)
              have h8b : (valueAt b p (keyEnd b (p + 1)) == p) = false := by simpa using h8
              rw [h8b]
              simp only [h8', ite_false]
              unfold hintsNumN
              have he_eq : (numEnd b (valueAt b p (keyEnd b (p + 1)))).toUInt64 =
                  UInt64.ofNat (numEndN b.data
                    (valueAt b p (keyEnd b (p + 1))).toUInt64.toNat) :=
                numEnd_toUInt64_eq b h64 hsize64 _
              rw [hv_eq] at he_eq
              by_cases h9 : numEnd b (valueAt b p (keyEnd b (p + 1))) = valueAt b p (keyEnd b (p + 1))
              · have h9' : UInt64.ofNat (numEndN b.data
                    (valueAtN b.data p.toUInt64 (UInt64.ofNat (keyEndN b.data (p.toUInt64 + 1).toNat))).toNat) =
                    valueAtN b.data p.toUInt64 (UInt64.ofNat (keyEndN b.data (p.toUInt64 + 1).toNat)) := by
                  rw [← he_eq, ← hv_eq, h9]
                have h9b : (numEnd b (valueAt b p (keyEnd b (p + 1))) ==
                    valueAt b p (keyEnd b (p + 1))) = true := by simpa using h9
                rw [h9b]
                simp only [h9', ite_true]
                rfl
              · have h9' : ¬ UInt64.ofNat (numEndN b.data
                    (valueAtN b.data p.toUInt64 (UInt64.ofNat (keyEndN b.data (p.toUInt64 + 1).toNat))).toNat) =
                    valueAtN b.data p.toUInt64 (UInt64.ofNat (keyEndN b.data (p.toUInt64 + 1).toNat)) := by
                  rw [← he_eq, ← hv_eq]
                  intro hx; exact h9 ((eq_toUInt64_iff _ _).mpr hx)
                have h9b : (numEnd b (valueAt b p (keyEnd b (p + 1))) ==
                    valueAt b p (keyEnd b (p + 1))) = false := by simpa using h9
                rw [h9b]
                simp only [h9', ite_false]
                have hq_eq : (skipWs b (numEnd b (valueAt b p (keyEnd b (p + 1))))).toUInt64 =
                    UInt64.ofNat (skipWsN b.data
                      (numEnd b (valueAt b p (keyEnd b (p + 1)))).toUInt64.toNat) :=
                  skipWs_toUInt64_eq b h64 hsize64 _
                rw [he_eq] at hq_eq
                have hcondQ := byteAt_lt_iff b h64 hsize
                  (skipWs b (numEnd b (valueAt b p (keyEnd b (p + 1)))))
                  (skipWs b (numEnd b (valueAt b p (keyEnd b (p + 1))))).toUInt64 125
                  (by decide) (by decide) (by rw [USize.toNat_toUInt64])
                by_cases h10 : byteAt b (skipWs b (numEnd b (valueAt b p (keyEnd b (p + 1))))) = 125
                · have h10' := hcondQ.mp h10
                  have h10b : (byteAt b (skipWs b (numEnd b (valueAt b p (keyEnd b (p + 1))))) == 125)
                      = true := by simpa using h10
                  rw [hq_eq] at h10'
                  rw [ite_eq_left h10b, ite_eq_left h10']
                  show (skipWs b (numEnd b (valueAt b p (keyEnd b (p + 1)))) + 1).toUInt64 = _
                  rw [add_toUInt64 h64, hq_eq, ofNat_toUInt64 h64]
                · have h10' : ¬ ((skipWs b (numEnd b (valueAt b p (keyEnd b (p + 1))))).toUInt64 <
                      UInt64.ofNat b.data.size ∧
                      byteW b.data (skipWs b (numEnd b (valueAt b p (keyEnd b (p + 1))))).toUInt64 = 125) :=
                    fun hx => h10 (hcondQ.mpr hx)
                  rw [hq_eq] at h10'
                  have h10b : ¬ (byteAt b (skipWs b (numEnd b (valueAt b p (keyEnd b (p + 1))))) == 125)
                      = true := by simpa using h10
                  rw [ite_eq_right h10b, ite_eq_right h10']
                  rfl
          · have h7' : ¬ keyAtN b.data p.toUInt64
                (UInt64.ofNat (keyEndN b.data (p.toUInt64 + 1).toNat) - (p.toUInt64 + 1)) = 51 := by
              rw [← hkeyAt]
              exact fun hx => h7 ((key_ctorIdx_word_eq_regular_iff _).mp hx)
            rw [ite_eq_left (show keyAtN b.data p.toUInt64
                (UInt64.ofNat (keyEndN b.data (p.toUInt64 + 1).toNat) - (p.toUInt64 + 1)) ≠ 51
              from h7')]
            cases hkc : keyAt b p (keyEnd b (p + 1) - (p + 1)) <;> simp_all
      · have h5' : (byteAt b p != 34) = true := by simpa using h5
        have h5'' : ¬ (p.toUInt64 < UInt64.ofNat b.data.size ∧ byteW b.data p.toUInt64 = 34) :=
          fun hx => h5 (hcondP.mpr hx)
        rw [ite_eq_left h5', ite_eq_left h5'']
    · have h4' : ¬ (byteAt b i == 123) = true := by simpa using h4
      rw [ite_eq_right h4', ite_eq_right (fun hx => h4 (hcond123.mpr hx))]

end ConAgua.Scan
