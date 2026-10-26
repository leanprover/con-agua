module

public import ConAgua.Front.FieldsDecl
public import ConAgua.Front.FieldsExprLink

@[expose] public section


/-!
# The fields of declaration lines, linked to con-leche

On con-leche's `ok` path, `rec_decl_line`'s words are the declaration record's fields
(`declLine_link`). One generic theorem (`dobj_link`) relates `rec_decl_obj`'s model `dobjN` to
a con-leche record loop that has the common shape (`DObjLoop`: whitespace, closing brace, comma,
key), given, at each key, one step (`dstepN`) that keeps a relation `R` between con-leche's loop
state and the words; each of the five loops instantiates it. The values: a number by `rdNat_link`,
a list by ``list_link` (`FieldsExprLink`)`, a flag by `scanBool_eq_N`, `hints` by `hkv_link`, a
string's raw body by `strCode_link`.
-/

namespace ConAgua.Front.FieldsLink
open ConLeche.Frontend ConAgua.Scan ConAgua.Scan.RecordsLink
open L (Word)
open L.Scan.Utf8 (byteW)
open L.Scan.Member
open L.Front.Fields
open L.Scan.Member (nextMemberN)
open L.Scan.Lit (encBool scanBoolN)

/-! ## Literals -/

/-- A literal match (`matchLitN`, a literal without `0` bytes) fixes the bytes it covers. -/
theorem matchLitN_get (a : Array UInt8) (i : Nat) (Lt : List UInt8) (o n : Nat)
    (hL : o + n ≤ Lt.length) (h0 : ∀ j (h : j < Lt.length), Lt[j] ≠ 0)
    (h : L.Scan.Lit.matchLitN a i Lt o n 0 = true) (j : Nat) (hj : j < n) :
    ∃ hb : i + j < a.size, a[i + j] = Lt[o + j]'(by omega) := by
  rw [ConAgua.Scan.matchLitN_eq_isPrefixOf _ _ _ _ _ _ hL h0] at h
  have hp := List.isPrefixOf_iff_prefix.mp h
  simp only [Nat.add_zero, Nat.sub_zero] at hp
  have hlen : ((Lt.drop o).take n).length = n := by simp; omega
  have hj' : j < ((Lt.drop o).take n).length := by omega
  have hl2 := hp.length_le
  rw [hlen] at hl2
  simp only [List.length_drop, Array.length_toList] at hl2
  refine ⟨by omega, ?_⟩
  have := hp.getElem hj'
  simp only [List.getElem_take, List.getElem_drop, Array.getElem_toList] at this
  exact this.symm

theorem matchLitN_getD (a : Array UInt8) (i : Nat) (Lt : List UInt8) (o n : Nat)
    (hL : o + n ≤ Lt.length) (h0 : ∀ j (h : j < Lt.length), Lt[j] ≠ 0)
    (h : L.Scan.Lit.matchLitN a i Lt o n 0 = true) (j : Nat) (hj : j < n) :
    i + j < a.size ∧ a.getD (i + j) 0 = Lt.getD (o + j) 0 := by
  obtain ⟨hb, he⟩ := matchLitN_get a i Lt o n hL h0 h j hj
  refine ⟨hb, ?_⟩
  simp [Array.getD, hb, he, List.getD_eq_getElem?_getD, show o + j < Lt.length by omega]



/-- `scan_bool`: its flag word and its end. -/
theorem boolV_link (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
    (v : USize) (x : Bool) (e : USize) (h : scanBool b v = .ok x e) :
    (encBool (scanBoolN b.data v.toUInt64.toNat) v.toUInt64).headD 0 ≠ 0 ∧
    (encBool (scanBoolN b.data v.toUInt64.toNat) v.toUInt64).tail.tail.headD 0 = e.toUInt64 ∧
    boolValN b.data v.toUInt64 = (if x then 1 else 0) := by
  have hl := scanBool_link b h64 hsize v
  rw [h] at hl
  have hq := scanBool_eq_N b v (by rw [USize.size_eq_two_pow, h64]; omega)
  rw [h] at hq
  rw [USize.toNat_toUInt64]
  cases hs : scanBoolN b.data v.toNat with
  | none => rw [hs] at hq; cases hq
  | some vp =>
    obtain ⟨y, p⟩ := vp
    rw [hs] at hq
    obtain ⟨rfl, -⟩ := ScanRes.ok.inj hq
    unfold L.Scan.Records.boolEndN at hl
    simp only [okW, boolValN, USize.toNat_toUInt64, hs, encBool, List.headD_cons, List.tail_cons] at hl ⊢
    simp only [show ((1 : Word) = 0) = False from by decide, ite_false] at hl
    exact ⟨by decide, hl.symm, trivial⟩
end ConAgua.Front.FieldsLink

namespace ConAgua.Front.FieldsLink
open ConLeche.Frontend ConAgua.Scan ConAgua.Scan.RecordsLink
open L (Word)
open L.Scan.Utf8 (byteW)
open L.Front.Fields
open L.Scan.Member (nextMemberN)

section kitH
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

theorem lt_of_byteAt_ne (i : USize) (h : byteAt b i ≠ 0) : i < b.usize := by
  refine Classical.byContradiction fun hn => ?_
  apply h; unfold byteAt; rw [dite_eq_right hn]

theorem byteW_of_byteAt (i : USize) (c : UInt8) (h : byteAt b i = c) :
    byteW b.data i.toUInt64 = c.toUInt64 := by rw [byteW_eq b h64 hsize, h]

/-- `hints_val` on a `hints` value con-leche reads. -/
theorem hkv_link (v : USize) (hr : HintsRec) (e : USize) (h : scanHints b v = .ok hr e) :
    HintsR hr (hkvN b.data v.toUInt64).1 (hkvN b.data v.toUInt64).2 := by
  have hb64 : b.size < 2 ^ 64 := by omega
  have hbs : b.data.size = b.size := rfl
  have hsU : b.size < USize.size := by rw [USize.size_eq_two_pow, h64]; omega
  have hU : UInt64.size = 2 ^ 64 := rfl
  unfold scanHints at h
  by_cases h34 : byteAt b v = 34
  · rw [ite_eq_left (by simp [h34])] at h
    have hv := lt_of_byteAt_ne b h64 hsize v (by rw [h34]; decide)
    have hvW := (lt_usize_iff b h64 hsize v).mp hv
    have hv1 : (v.toUInt64 + 1).toNat = v.toNat + 1 := by
      have := L.Scan.toNat_add_one_of_lt_ofNat hvW; simpa using this
    have hb34 : byteW b.data v.toUInt64 = 34 := by rw [byteW_of_byteAt b h64 hsize v 34 h34]; rfl
    unfold hkvN
    rw [ite_eq_right (by intro h'; exact absurd hvW (UInt64.not_lt.mpr h')), ite_eq_left hb34]
    rw [matchLit_eq_N_words b (v + 1) hsU "abbrev\"" 45 7 lit_abbrev (by decide)
        (size_toUTF8_lt "abbrev\"" 7 rfl (by decide)),
      matchLit_eq_N_words b (v + 1) hsU "opaque\"" 52 7 lit_opaque (by decide)
        (size_toUTF8_lt "opaque\"" 7 rfl (by decide))] at h
    have hv1' : (v + 1).toNat = v.toNat + 1 := usizeStep b v hv
    split at h
    · rename_i hm
      obtain ⟨rfl, -⟩ := ScanRes.ok.inj h
      obtain ⟨hlt, hbyte⟩ := matchLitN_getD b.data _ _ _ _ (by decide) WORDS_ne_zero hm 0 (by decide)
      simp only [Nat.add_zero, hv1'] at hlt hbyte
      rw [ite_eq_left]
      · rfl
      refine ⟨?_, ?_⟩
      · rw [UInt64.lt_iff_toNat_lt, hv1, UInt64.toNat_ofNat_of_lt' (by omega)]; omega
      · simp only [L.Scan.Utf8.byteW, hv1, hbyte]; decide
    split at h
    · rename_i _ hm
      obtain ⟨rfl, -⟩ := ScanRes.ok.inj h
      obtain ⟨hlt, hbyte⟩ := matchLitN_getD b.data _ _ _ _ (by decide) WORDS_ne_zero hm 0 (by decide)
      simp only [Nat.add_zero, hv1'] at hlt hbyte
      rw [ite_eq_right]
      · rfl
      rintro ⟨-, hb97⟩
      simp only [L.Scan.Utf8.byteW, hv1, hbyte] at hb97
      revert hb97; decide
    · cases h
  · rw [ite_eq_right (by simp [h34])] at h
    split at h
    · rename_i h123
      have h123' : byteAt b v = 123 := by simpa using h123
      have hv := lt_of_byteAt_ne b h64 hsize v (by rw [h123']; decide)
      have hvW := (lt_usize_iff b h64 hsize v).mp hv
      have hv1' : (v + 1).toNat = v.toNat + 1 := usizeStep b v hv
      have hb123 : byteW b.data v.toUInt64 = 123 := by rw [byteW_of_byteAt b h64 hsize v 123 h123']; rfl
      simp only at h
      split at h; cases h; rename_i hp34
      have hp34' : byteAt b (skipWs b (v + 1)) = 34 := by simpa using hp34
      generalize hp : skipWs b (v + 1) = p at h hp34'
      have hpU := lt_of_byteAt_ne b h64 hsize p (by rw [hp34']; decide)
      have hpW := (lt_usize_iff b h64 hsize p).mp hpU
      have hpN := usizeInBounds b p hpU
      have hpEq : UInt64.ofNat (L.Scan.Leaves.skipWsN b.data (v.toUInt64 + 1).toNat) = p.toUInt64 := by
        rw [← hp, skipWs_toUInt64_eq b h64 hb64, ← succ_toUInt64 b h64 hsize, USize.toNat_toUInt64]
      split at h; cases h; rename_i hke
      have hke' : keyEnd b (p + 1) ≠ 0 := by simpa using hke
      generalize hk : keyEnd b (p + 1) = ke at h hke'
      have hkeN := keyEnd_toNat_eq b h64 hb64 (p + 1)
      rw [hk] at hkeN
      have hkn0 : L.Scan.Leaves.keyEndN b.data (p + 1).toNat ≠ 0 := by
        intro h0; apply hke'; apply USize.toNat_inj.mp; rw [hkeN, h0]; rfl
      have hkb := keyEndN_bounds b.data _ hkn0
      have hp1 : (p + 1).toNat = p.toNat + 1 := usizeStep b p hpU
      have hkeEq : UInt64.ofNat (L.Scan.Leaves.keyEndN b.data (p.toUInt64 + 1).toNat) = ke.toUInt64 := by
        rw [← succ_toUInt64 b h64 hsize p, USize.toNat_toUInt64, ← keyEnd_toUInt64_eq b h64 hb64, hk]
      have hkeU : ke.toNat < b.size := by rw [hkeN]; exact hkb.2
      unfold hkvN
      rw [ite_eq_right (by intro h'; exact absurd hvW (UInt64.not_lt.mpr h')),
              ite_eq_right (by rw [hb123]; decide), hpEq, hkeEq]
      rw [ite_eq_right (by
                rw [UInt64.not_le, UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (by omega)]
                have : (p.toUInt64 + 1).toNat = p.toNat + 1 := by
                  rw [UInt64.toNat_add]; simp; omega
                rw [this]; omega),
              ite_eq_right (by
                            rw [UInt64.not_le, UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (by omega)]
                            rw [USize.toNat_toUInt64]; omega)]
      split at h
      · rename_i hreg
        try simp only at h
        split at h; cases h; rename_i hvp
        generalize hvv : valueAt b p ke = v' at h hvp
        split at h; cases h
        split at h
        · obtain ⟨rfl, -⟩ := ScanRes.ok.inj h
          have hvEq : L.Scan.Key.valueAtN b.data p.toUInt64 ke.toUInt64 = v'.toUInt64 := by
            rw [← hvv, valueAt_eq_valueAtN b h64 hsize]
          have hv'le : v'.toNat ≤ b.size := by
            have := L.Scan.Key.valueAtN_le b.data p.toUInt64 ke.toUInt64
              (by rw [USize.toNat_toUInt64]; omega) (by rw [USize.toNat_toUInt64]; omega) hsize
            rw [hvEq, USize.toNat_toUInt64] at this; exact this
          rw [hvEq, USize.toNat_toUInt64, ← numEnd_toUInt64_eq b h64 hb64]
          refine ⟨rfl, rdNat_link b h64 hsize v' (numEnd b v') ?_ (numEnd_le b h64 hsize v' hv'le)⟩
          have := numEnd_toNat_eq b h64 hb64 v'
          rw [USize.le_iff_toNat_le, this]; exact L.Scan.Values.numEndN_ge _ _
        · cases h
      all_goals cases h
    · cases h

omit h64 hsize in
theorem noEsc_of_hasEscapeN_decl (j e : Nat)
    (h : L.Scan.Leaves.hasEscapeN b.data j e = 0) : NoEsc b j e := by
  fun_induction L.Scan.Leaves.hasEscapeN b.data j e with
  | case1 j hj hlt hc => simp at h
  | case2 j hj hlt hc ih =>
    intro k hk1 hk2
    by_cases hkj : k = j
    · subst hkj; simp only [Array.getD, hj, dite_true]; exact hc
    · exact ih h k (by omega) hk2
  | case3 j hj hlt => intro k hk1 hk2; omega
  | case4 j hj =>
    intro k hk1 hk2
    simp only [Array.getD, show ¬ k < b.data.size by omega, dite_false]; decide

/-- A string body without a backslash that matches a literal of `DLITS` is that literal. -/
theorem str_lit (v : USize) (s : String) (e : USize) (h : ConLeche.Frontend.scanString b v = .ok s e)
    (o n : Nat) (bytes : Array UInt8) (hlit : (DLITS.drop o).take n = bytes.toList) (hon : o + n ≤ 19)
    (hesc : L.Scan.Leaves.hasEscapeN b.data (v.toUInt64 + 1).toNat (e.toUInt64 - 1).toNat = 0)
    (hlen : (e.toUInt64 - 1) - (v.toUInt64 + 1) = UInt64.ofNat n) (hn : n ≤ 4)
    (hm : L.Scan.Lit.matchLitN b.data (v.toUInt64 + 1).toNat DLITS o n 0 = true) :
    String.fromUTF8? ⟨bytes⟩ = some s := by
  have hS := scanString_strOK b h64 hsize v s e h (noEsc_of_hasEscapeN_decl b _ _ hesc)
  rw [← hS]
  congr 1
  have hpre := hm
  rw [ConAgua.Scan.matchLitN_eq_isPrefixOf _ _ _ _ _ _ (by simp [DLITS_length]; omega)
    (by decide)] at hpre
  simp only [Nat.add_zero, Nat.sub_zero] at hpre
  have hp := List.isPrefixOf_iff_prefix.mp hpre
  have hl : ((DLITS.drop o).take n).length = n := by simp [DLITS_length]; omega
  have hle := hp.length_le
  simp only [hl, List.length_drop, Array.length_toList] at hle
  have hc : (v.toUInt64 + 1).toNat + n = (e.toUInt64 - 1).toNat := by
    have h1 := congrArg UInt64.toNat hlen
    rw [UInt64.toNat_sub, UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)] at h1
    have hb := (v.toUInt64 + 1).toNat_lt
    have hb2 := (e.toUInt64 - 1).toNat_lt
    have hU : UInt64.size = 2 ^ 64 := rfl

    have : (b.data.size : Nat) = b.size := rfl
    omega
  apply ByteArray.ext
  apply Array.ext'
  rw [ByteArray.data_extract, Array.toList_extract, ← hlit, List.prefix_iff_eq_take.mp hp, hl,
    List.extract_eq_take_drop, ← hc, Nat.add_sub_cancel_left]

omit h64 hsize in
theorem hasEscapeN_eq_zero (j e : Nat)
    (h : ¬ UInt64.ofNat (L.Scan.Leaves.hasEscapeN b.data j e) ≠ 0) :
    L.Scan.Leaves.hasEscapeN b.data j e = 0 := by
  have : L.Scan.Leaves.hasEscapeN b.data j e = 0 ∨ L.Scan.Leaves.hasEscapeN b.data j e = 1 := by
    fun_induction L.Scan.Leaves.hasEscapeN b.data j e <;> simp_all
  rcases this with h0 | h1
  · exact h0
  · rw [h1] at h; simp at h

/-- `str_code`'s classification of a string con-leche reads: a `safety` of code `1` is
`"safe"`, and a `kind` of code `1`‥`4` is its literal. -/
theorem strCode_link (v : USize) (s : String) (e : USize)
    (h : ConLeche.Frontend.scanString b v = .ok s e) (k : Word) :
    (k = 54 → strCodeN b.data (v.toUInt64 + 1) (e.toUInt64 - 1) k = 1 → s = "safe") ∧
    (k ≠ 54 → QuotR s (strCodeN b.data (v.toUInt64 + 1) (e.toUInt64 - 1) k)) := by
  have lit := fun (o n : Nat) (bytes : Array UInt8) (t : String)
      (hlit : (DLITS.drop o).take n = bytes.toList) (hon : o + n ≤ 19) (hn : n ≤ 4)
      (ht : String.fromUTF8? ⟨bytes⟩ = some t)
      (hesc : L.Scan.Leaves.hasEscapeN b.data (v.toUInt64 + 1).toNat (e.toUInt64 - 1).toNat = 0)
      (hlen : (e.toUInt64 - 1) - (v.toUInt64 + 1) = UInt64.ofNat n)
      (hm : L.Scan.Lit.matchLitN b.data (v.toUInt64 + 1).toNat DLITS o n 0 = true) =>
    (Option.some.inj ((str_lit b h64 hsize v s e h o n bytes hlit hon hesc hlen hn hm).symm.trans ht))
  constructor
  · intro hk hc
    unfold strCodeN at hc
    split at hc
    · simp at hc
    split at hc
    · simp at hc
    rename_i hesc
    split at hc
    · rename_i hcond
      exact lit 0 4 #[115, 97, 102, 101] "safe" (by decide) (by decide) (by decide) (by decide)
        (hasEscapeN_eq_zero b _ _ hesc) hcond.1 hcond.2
    · simp at hc
  · intro hk
    unfold strCodeN
    split
    · simp [QuotR]
    split
    · simp [QuotR]
    rename_i hesc
    have hesc' := hasEscapeN_eq_zero b _ _ hesc
    try rw [if_neg hk]
    split
    · rename_i hcond
      have := lit 4 4 #[116, 121, 112, 101] "type" (by decide) (by decide) (by decide) (by decide)
        hesc' hcond.1 hcond.2
      simp [QuotR, this]
    split
    · rename_i hcond
      have := lit 8 4 #[99, 116, 111, 114] "ctor" (by decide) (by decide) (by decide) (by decide)
        hesc' hcond.1 hcond.2
      simp [QuotR, this]
    split
    · rename_i hcond
      have := lit 12 4 #[108, 105, 102, 116] "lift" (by decide) (by decide) (by decide) (by decide)
        hesc' hcond.1 hcond.2
      simp [QuotR, this]
    split
    · rename_i hcond
      have := lit 16 3 #[105, 110, 100] "ind" (by decide) (by decide) (by decide) (by decide)
        hesc' hcond.1 hcond.2
      simp [QuotR, this]
    · simp [QuotR]

end kitH
end ConAgua.Front.FieldsLink

namespace ConAgua.Front.FieldsLink
open ConLeche.Frontend ConAgua.Scan ConAgua.Scan.RecordsLink
open L (Word)
open L.Scan.Utf8 (byteW)
open L.Scan.Member
open L.Front.Fields
open L.Scan.Member (nextMemberN)

/-! ## The generic declaration-record loop -/

theorem dobjN_congr (b : Array UInt8) (i w j w' : Word) (f : DFld)
    (h : nextMemberN b i w = nextMemberN b j w') : dobjN b i w f = dobjN b j w' f := by
  conv => lhs; rw [dobjN]
  conv => rhs; rw [dobjN]
  simp only [h]

/-- The shape of a con-leche declaration-record loop `F` (state `σ`), on its `ok` path, against
`dobjN`: `R seen st f` relates con-leche's state to the words, `Fin d f` the record to them. -/
structure DObjLoop (b : ByteArray) {σ : Type} (F : USize → Bool → UInt32 → σ → ScanRes DeclRec)
    (R : UInt32 → σ → DFld → Prop) (Fin : DeclRec → DFld → Prop) : Prop where
  stop : ∀ i w seen st d e, ¬ i < b.usize → F i w seen st ≠ .ok d e
  ws : ∀ i w seen st, i < b.usize → isWs (byteAt b i) = true → F i w seen st = F (i + 1) w seen st
  close : ∀ i w seen st f d e, i < b.usize → byteAt b i = 125 → F i w seen st = .ok d e →
    R seen st f → e = i + 1 ∧ Fin d { f with pl := (i + 1).toUInt64 }
  comma : ∀ i w seen st d e, i < b.usize → byteAt b i = 44 → F i w seen st = .ok d e →
    w = false ∧ F (i + 1) true seen st = .ok d e
  quote : ∀ i w seen st d e, i < b.usize → byteAt b i = 34 → F i w seen st = .ok d e →
    w = true ∧ keyEnd b (i + 1) ≠ 0 ∧ valueAt b i (keyEnd b (i + 1)) ≠ i
  key : ∀ i seen st f d e, i < b.usize → byteAt b i = 34 → keyEnd b (i + 1) ≠ 0 →
    valueAt b i (keyEnd b (i + 1)) ≠ i → (valueAt b i (keyEnd b (i + 1))).toNat ≤ b.size →
    F i true seen st = .ok d e → R seen st f →
    ∃ (e' : USize) (seen' : UInt32) (st' : σ),
      (dstepN b.data i.toUInt64 (UInt64.ofNat (keyAt b i (keyEnd b (i + 1) - (i + 1))).ctorIdx)
        (valueAt b i (keyEnd b (i + 1))).toUInt64 f).1 = e'.toUInt64 ∧ i < e' ∧
      F e' false seen' st' = .ok d e ∧
      R seen' st' (dstepN b.data i.toUInt64 (UInt64.ofNat (keyAt b i (keyEnd b (i + 1) - (i + 1))).ctorIdx)
        (valueAt b i (keyEnd b (i + 1))).toUInt64 f).2
  other : ∀ i w seen st d e, i < b.usize → isWs (byteAt b i) = false → byteAt b i ≠ 125 →
    byteAt b i ≠ 44 → byteAt b i ≠ 34 → F i w seen st ≠ .ok d e

section generic
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

theorem dobj_link {σ : Type} (F : USize → Bool → UInt32 → σ → ScanRes DeclRec)
    (R : UInt32 → σ → DFld → Prop) (Fin : DeclRec → DFld → Prop) (H : DObjLoop b F R Fin)
    (i : USize) (w : Bool) (seen : UInt32) (st : σ) (f : DFld) (d : DeclRec) (e : USize)
    (h : F i w seen st = .ok d e) (hR : R seen st f) :
    (dobjN b.data i.toUInt64 (bw w) f).pl = e.toUInt64 ∧ Fin d (dobjN b.data i.toUInt64 (bw w) f) := by
  by_cases hi : i < b.usize
  · have hin := usizeInBounds b i hi
    have hi1 : (i + 1).toNat = i.toNat + 1 := usizeStep b i hi
    by_cases hws : isWs (byteAt b i) = true
    · rw [H.ws i w seen st hi hws] at h
      rw [dobjN_congr _ _ _ _ _ _ (nm_ws b h64 hsize i _ hi hws)]
      exact dobj_link F R Fin H (i + 1) w seen st f d e h hR
    by_cases h125 : byteAt b i = 125
    · obtain ⟨rfl, hF⟩ := H.close i w seen st f d e hi h125 h hR
      rw [dobjN_close _ _ _ _ (by rw [nm_close b h64 hsize i _ hi hws h125]),
        nm_close b h64 hsize i _ hi hws h125, ← succ_toUInt64 b h64 hsize]
      exact ⟨rfl, hF⟩
    by_cases h44 : byteAt b i = 44
    · obtain ⟨rfl, h'⟩ := H.comma i w seen st d e hi h44 h
      simp only [bw, Bool.false_eq_true, ite_false]
      rw [dobjN_congr _ _ _ _ _ _ (nm_comma b h64 hsize i hi hws h44)]
      exact dobj_link F R Fin H (i + 1) true seen st f d e h' hR
    by_cases h34 : byteAt b i = 34
    · obtain ⟨rfl, hk, hv⟩ := H.quote i w seen st d e hi h34 h
      have hm := nm_key b h64 hsize i hi h34 hk hv
      have hvle := nm_key_le b h64 hsize i hi h34 hk hv
      obtain ⟨e', seen', st', he', hie', h', hR'⟩ := H.key i seen st f d e hi h34 hk hv hvle h hR
      simp only [bw, ite_true]
      rw [dobjN_key _ _ _ _ (by rw [hm]; exact (by decide : (2 : Word) ≠ 0))
        (by rw [hm]; exact (by decide : (2 : Word) ≠ 1))]
      simp only [hm]
      rw [ite_eq_left (by rw [he']; exact (lt_toUInt64_iff _ _).mp hie'), he']
      exact dobj_link F R Fin H e' false seen' st' _ d e h' hR'
    · exact absurd h (H.other i w seen st d e hi (by simpa using hws) h125 h44 h34)
  · exact absurd h (H.stop i w seen st d e hi)
termination_by b.size - i.toNat
decreasing_by
  all_goals first
    | omega
    | (have := USize.lt_iff_toNat_lt.mp hie'; omega)

end generic
end ConAgua.Front.FieldsLink

namespace ConAgua.Front.FieldsLink
open ConLeche.Frontend ConAgua.Scan ConAgua.Scan.RecordsLink
open L (Word)
open L.Scan.Utf8 (byteW)
open L.Scan.Member
open L.Front.Fields
open L.Scan.Member (nextMemberN)

/-! ## Bits of `seen` -/

theorem bit_or_and (s a m : UInt32) (h : a &&& m = 0) : (s ||| a) &&& m = s &&& m := by
  apply UInt32.toBitVec_inj.mp
  have h' := congrArg UInt32.toBitVec h
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_or, UInt32.toBitVec_zero] at h' ⊢
  rw [BitVec.and_or_distrib_right, h', BitVec.or_zero]

/-- A list slot not yet seen, or seen and related. -/
def LpsR (b : ByteArray) (seen m : UInt32) (lw : Word) (lps : List Nat) : Prop :=
  ItemsR (listN b.data lw) lps ∨ seen &&& m = 0

theorem lpsR_or (b : ByteArray) (seen m a : UInt32) (lw : Word) (lps : List Nat)
    (h : LpsR b seen m lw lps) (ha : a &&& m = 0) : LpsR b (seen ||| a) m lw lps := by
  rcases h with h | h
  · exact .inl h
  · exact .inr (by rw [bit_or_and _ _ _ ha, h])

theorem lpsR_close (b : ByteArray) (seen m M : UInt32) (lw : Word) (lps : List Nat)
    (h : LpsR b seen m lw lps) (hM : seen &&& M = M) (hmM : M &&& m = m) (hm : m ≠ 0) :
    ItemsR (listN b.data lw) lps := by
  rcases h with h | h
  · exact h
  · exfalso; apply hm
    rw [← hmM, ← hM, UInt32.and_assoc, hmM, h]
end ConAgua.Front.FieldsLink

namespace ConAgua.Front.FieldsLink
open ConLeche.Frontend ConAgua.Scan ConAgua.Scan.RecordsLink
open L (Word)
open L.Front.Fields
open L.Scan.Member (nextMemberN)

section vals
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize


end vals


/-! ## The per-record proofs: tactics for the shared shape -/

set_option hygiene false in
/-- The arms of a `DObjLoop` other than the key and the closing brace. -/
macro "dloop_stop " f:ident : tactic => `(tactic| (
  intro i w seen st d e h; rw [$f:ident, dite_eq_right h]; simp))
set_option hygiene false in
macro "dloop_ws " f:ident : tactic => `(tactic| (
  intro i w seen st h hws; rw [$f:ident, dite_eq_left h]; simp only [uget_byteAt _ i h, hws, ite_true]))
set_option hygiene false in
macro "dloop_comma " f:ident : tactic => `(tactic| (
  intro i w seen st d e h hc hok
  rw [$f:ident, dite_eq_left h] at hok
  simp [uget_byteAt _ i h, hc, isWs] at hok
  split at hok; cases hok
  · exact ⟨by simpa using ‹¬w = true›, hok⟩))
set_option hygiene false in
macro "dloop_quote " f:ident : tactic => `(tactic| (
  intro i w seen st d e h hc hok
  rw [$f:ident, dite_eq_left h] at hok
  simp [uget_byteAt _ i h, hc, isWs] at hok
  split at hok; cases hok
  split at hok; cases hok
  split at hok; cases hok; rename_i hw hk hv
  exact ⟨by simpa using hw, hk, hv⟩))
set_option hygiene false in
macro "dloop_other " f:ident : tactic => `(tactic| (
  intro i w seen st d e h hws h1 h2 h3 hok
  rw [$f:ident, dite_eq_left h] at hok
  simp [uget_byteAt _ i h, hws, h1, h2, h3] at hok))
set_option hygiene false in
/-- The closing brace: the record and its relation. -/
macro "dloop_close " f:ident : tactic => `(tactic| (
  intro i w seen st f d e h hc hok hR
  rw [$f:ident, dite_eq_left h] at hok
  simp [uget_byteAt _ i h, hc, isWs] at hok
  split at hok; cases hok
  split at hok
  rotate_left
  · cases hok
  rename_i hM
  obtain ⟨rfl, rfl⟩ := ScanRes.ok.inj hok
  refine ⟨rfl, ?_⟩))
set_option hygiene false in
/-- A key's arm, entering it: the key's `seen` check passed. -/
macro "dloop_key " f:ident : tactic => `(tactic| (
  intro i seen st f d e h hc hk hv hvle hok hR
  rw [$f:ident, dite_eq_left h] at hok
  simp [uget_byteAt _ i h, hc, isWs, hk, hv] at hok
  generalize valueAt b i (keyEnd b (i + 1)) = v at hok hvle ⊢
  generalize keyAt b i (keyEnd b (i + 1) - (i + 1)) = K at hok ⊢
  cases K
  all_goals (try (simp at hok; done))))
set_option hygiene false in
/-- A number key (`numEnd`, `readNatAt`): leaves the relation for `st`. -/
macro "dkey_num " st:term : tactic => `(tactic| (
  simp only at hok
  split at hok
  rotate_left
  · cases hok
  split at hok; cases hok; rename_i hne
  split at hok
  rotate_left
  · cases hok
  rename_i hie
  obtain ⟨hsl, hRn⟩ := num_val b h64 hsize i v hne hie hvle
  refine ⟨_, _, $st, by simp [dstepN, dendN, hsl], hie, hok, ?_⟩
  simp (config := {decide := true}) only [dstepN, dnumN, dlpsN, dflagN, dhkN, dhnN, hsl, ↓reduceIte]))
set_option hygiene false in
/-- A key read by a `ScanRes` scanner `scan`, whose end link is `hlink`. -/
macro "dkey_res" : tactic => `(tactic| (
  simp only at hok
  split at hok
  rotate_left
  · cases hok
  split at hok; cases hok; rename_i x e' hx
  split at hok
  rotate_left
  · cases hok
  rename_i hie))


/-! ## `axiom` -/

section records
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

/-- The relation for an `axiom` record. -/
def AxR (b : ByteArray) (seen : UInt32) (st : Bool × List Nat × Nat × Nat) (f : DFld) : Prop :=
  f.flag = (if st.1 then 1 else 0) ∧ LpsR b seen 2 f.lps st.2.1 ∧ ItemR f.name st.2.2.1 ∧
    ItemR f.type st.2.2.2

theorem axiom_loop : DObjLoop b (fun i w seen (st : Bool × List Nat × Nat × Nat) =>
      scanAxiomDeclLoop b i w seen st.1 st.2.1 st.2.2.1 st.2.2.2) (AxR b)
    (fun d f => DeclR b d { f with pl := 20 }) := by
  constructor
  · dloop_stop scanAxiomDeclLoop
  · dloop_ws scanAxiomDeclLoop
  · dloop_close scanAxiomDeclLoop
    obtain ⟨hf, hl, hn, ht⟩ := hR
    exact ⟨rfl, ⟨hn, lpsR_close b _ _ _ _ _ hl hM (by decide) (by decide), ht⟩, hf⟩
  · dloop_comma scanAxiomDeclLoop
  · dloop_quote scanAxiomDeclLoop
  · dloop_key scanAxiomDeclLoop
    all_goals obtain ⟨hf, hl, hn, ht⟩ := hR
    case kName =>
      rw [show UInt64.ofNat Key.kName.ctorIdx = (34 : Word) from rfl]
      dkey_num (st.1, st.2.1, readNatAt b v (numEnd b v), st.2.2.2)
      exact ⟨hf, lpsR_or b _ _ _ _ _ hl (by decide), hRn, ht⟩
    case kType =>
      rw [show UInt64.ofNat Key.kType.ctorIdx = (61 : Word) from rfl]
      dkey_num (st.1, st.2.1, st.2.2.1, readNatAt b v (numEnd b v))
      exact ⟨hf, lpsR_or b _ _ _ _ _ hl (by decide), hn, hRn⟩
    case kLevelParams =>
      rw [show UInt64.ofNat Key.kLevelParams.ctorIdx = (31 : Word) from rfl]
      dkey_res
      have hend := scanNatList_link b h64 hsize v
      rw [hx] at hend
      refine ⟨e', _, (st.1, x, st.2.2.1, st.2.2.2), by simp [dstepN, dendN, ← hend, okW], hie, hok, ?_⟩
      simp (config := {decide := true}) only [dstepN, dnumN, dlpsN, dflagN, ↓reduceIte]
      exact ⟨hf, .inl (list_link b h64 hsize v x e' hx), hn, ht⟩
    case kIsUnsafe =>
      rw [show UInt64.ofNat Key.kIsUnsafe.ctorIdx = (26 : Word) from rfl]
      dkey_res
      obtain ⟨hh, hend, hval⟩ := boolV_link b h64 hsize v x e' hx
      refine ⟨e', _, (x, st.2.1, st.2.2.1, st.2.2.2), by simp (config := {decide := true}) only [dstepN, dendN, ↓reduceIte, hh, hend], hie, hok, ?_⟩
      simp (config := {decide := true}) only [dstepN, dnumN, dlpsN, dflagN, ↓reduceIte, hval]
      exact ⟨rfl, lpsR_or b _ _ _ _ _ hl (by decide), hn, ht⟩
  · dloop_other scanAxiomDeclLoop

/-! ## `thm` -/

/-- The relation for a `thm` record. -/
def ThmR (b : ByteArray) (seen : UInt32) (st : List Nat × Nat × Nat × Nat) (f : DFld) : Prop :=
  LpsR b seen 2 f.lps st.1 ∧ ItemR f.name st.2.1 ∧ ItemR f.type st.2.2.1 ∧ ItemR f.value st.2.2.2

theorem thm_loop : DObjLoop b (fun i w seen (st : List Nat × Nat × Nat × Nat) =>
      scanThmDeclLoop b i w seen st.1 st.2.1 st.2.2.1 st.2.2.2) (ThmR b)
    (fun d f => DeclR b d { f with pl := 22 }) := by
  constructor
  · dloop_stop scanThmDeclLoop
  · dloop_ws scanThmDeclLoop
  · dloop_close scanThmDeclLoop
    obtain ⟨hl, hn, ht, hvl⟩ := hR
    exact ⟨rfl, ⟨hn, lpsR_close b _ _ _ _ _ hl hM (by decide) (by decide), ht⟩, hvl⟩
  · dloop_comma scanThmDeclLoop
  · dloop_quote scanThmDeclLoop
  · dloop_key scanThmDeclLoop
    all_goals obtain ⟨hl, hn, ht, hvl⟩ := hR
    case kName =>
      rw [show UInt64.ofNat Key.kName.ctorIdx = (34 : Word) from rfl]
      dkey_num (st.1, readNatAt b v (numEnd b v), st.2.2.1, st.2.2.2)
      exact ⟨lpsR_or b _ _ _ _ _ hl (by decide), hRn, ht, hvl⟩
    case kType =>
      rw [show UInt64.ofNat Key.kType.ctorIdx = (61 : Word) from rfl]
      dkey_num (st.1, st.2.1, readNatAt b v (numEnd b v), st.2.2.2)
      exact ⟨lpsR_or b _ _ _ _ _ hl (by decide), hn, hRn, hvl⟩
    case kValue =>
      rw [show UInt64.ofNat Key.kValue.ctorIdx = (65 : Word) from rfl]
      dkey_num (st.1, st.2.1, st.2.2.1, readNatAt b v (numEnd b v))
      exact ⟨lpsR_or b _ _ _ _ _ hl (by decide), hn, ht, hRn⟩
    case kLevelParams =>
      rw [show UInt64.ofNat Key.kLevelParams.ctorIdx = (31 : Word) from rfl]
      dkey_res
      have hend := scanNatList_link b h64 hsize v
      rw [hx] at hend
      refine ⟨e', _, (x, st.2.1, st.2.2.1, st.2.2.2), by simp [dstepN, dendN, ← hend, okW], hie, hok, ?_⟩
      simp (config := {decide := true}) only [dstepN, dnumN, dlpsN, dflagN, ↓reduceIte]
      exact ⟨.inl (list_link b h64 hsize v x e' hx), hn, ht, hvl⟩
    case kAll =>
      rw [show UInt64.ofNat Key.kAll.ctorIdx = (1 : Word) from rfl]
      dkey_res
      have hend := scanNatList_link b h64 hsize v
      rw [hx] at hend
      refine ⟨e', _, st, by simp [dstepN, dendN, ← hend, okW], hie, hok, ?_⟩
      simp (config := {decide := true}) only [dstepN, dnumN, dlpsN, dflagN, ↓reduceIte]
      exact ⟨lpsR_or b _ _ _ _ _ hl (by decide), hn, ht, hvl⟩
  · dloop_other scanThmDeclLoop

/-! ## `opaque` -/

/-- The relation for an `opaque` record. -/
def OpqR (b : ByteArray) (seen : UInt32) (st : Bool × List Nat × Nat × Nat × Nat) (f : DFld) : Prop :=
  f.flag = (if st.1 then 1 else 0) ∧ LpsR b seen 4 f.lps st.2.1 ∧ ItemR f.name st.2.2.1 ∧
    ItemR f.type st.2.2.2.1 ∧ ItemR f.value st.2.2.2.2

theorem opaque_loop : DObjLoop b (fun i w seen (st : Bool × List Nat × Nat × Nat × Nat) =>
      scanOpaqueDeclLoop b i w seen st.1 st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2) (OpqR b)
    (fun d f => DeclR b d { f with pl := 23 }) := by
  constructor
  · dloop_stop scanOpaqueDeclLoop
  · dloop_ws scanOpaqueDeclLoop
  · dloop_close scanOpaqueDeclLoop
    obtain ⟨hf, hl, hn, ht, hvl⟩ := hR
    exact ⟨rfl, ⟨hn, lpsR_close b _ _ _ _ _ hl hM (by decide) (by decide), ht⟩, hvl, hf⟩
  · dloop_comma scanOpaqueDeclLoop
  · dloop_quote scanOpaqueDeclLoop
  · dloop_key scanOpaqueDeclLoop
    all_goals obtain ⟨hf, hl, hn, ht, hvl⟩ := hR
    case kName =>
      rw [show UInt64.ofNat Key.kName.ctorIdx = (34 : Word) from rfl]
      dkey_num (st.1, st.2.1, readNatAt b v (numEnd b v), st.2.2.2.1, st.2.2.2.2)
      exact ⟨hf, lpsR_or b _ _ _ _ _ hl (by decide), hRn, ht, hvl⟩
    case kType =>
      rw [show UInt64.ofNat Key.kType.ctorIdx = (61 : Word) from rfl]
      dkey_num (st.1, st.2.1, st.2.2.1, readNatAt b v (numEnd b v), st.2.2.2.2)
      exact ⟨hf, lpsR_or b _ _ _ _ _ hl (by decide), hn, hRn, hvl⟩
    case kValue =>
      rw [show UInt64.ofNat Key.kValue.ctorIdx = (65 : Word) from rfl]
      dkey_num (st.1, st.2.1, st.2.2.1, st.2.2.2.1, readNatAt b v (numEnd b v))
      exact ⟨hf, lpsR_or b _ _ _ _ _ hl (by decide), hn, ht, hRn⟩
    case kLevelParams =>
      rw [show UInt64.ofNat Key.kLevelParams.ctorIdx = (31 : Word) from rfl]
      dkey_res
      have hend := scanNatList_link b h64 hsize v
      rw [hx] at hend
      refine ⟨e', _, (st.1, x, st.2.2.1, st.2.2.2.1, st.2.2.2.2), by simp [dstepN, dendN, ← hend, okW],
        hie, hok, ?_⟩
      simp (config := {decide := true}) only [dstepN, dnumN, dlpsN, dflagN, ↓reduceIte]
      exact ⟨hf, .inl (list_link b h64 hsize v x e' hx), hn, ht, hvl⟩
    case kAll =>
      rw [show UInt64.ofNat Key.kAll.ctorIdx = (1 : Word) from rfl]
      dkey_res
      have hend := scanNatList_link b h64 hsize v
      rw [hx] at hend
      refine ⟨e', _, st, by simp [dstepN, dendN, ← hend, okW], hie, hok, ?_⟩
      simp (config := {decide := true}) only [dstepN, dnumN, dlpsN, dflagN, ↓reduceIte]
      exact ⟨hf, lpsR_or b _ _ _ _ _ hl (by decide), hn, ht, hvl⟩
    case kIsUnsafe =>
      rw [show UInt64.ofNat Key.kIsUnsafe.ctorIdx = (26 : Word) from rfl]
      dkey_res
      obtain ⟨hh, hend, hval⟩ := boolV_link b h64 hsize v x e' hx
      refine ⟨e', _, (x, st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2),
        by simp (config := {decide := true}) only [dstepN, dendN, ↓reduceIte, hh, hend], hie, hok, ?_⟩
      simp (config := {decide := true}) only [dstepN, dnumN, dlpsN, dflagN, ↓reduceIte, hval]
      exact ⟨rfl, lpsR_or b _ _ _ _ _ hl (by decide), hn, ht, hvl⟩
  · dloop_other scanOpaqueDeclLoop

/-! ## `quot` -/

/-- The relation for a `quot` record. -/
def QuotLR (b : ByteArray) (seen : UInt32) (st : String × List Nat × Nat × Nat) (f : DFld) : Prop :=
  QuotR st.1 f.flag ∧ LpsR b seen 2 f.lps st.2.1 ∧ ItemR f.name st.2.2.1 ∧ ItemR f.type st.2.2.2

theorem quot_loop : DObjLoop b (fun i w seen (st : String × List Nat × Nat × Nat) =>
      scanQuotDeclLoop b i w seen st.1 st.2.1 st.2.2.1 st.2.2.2) (QuotLR b)
    (fun d f => DeclR b d { f with pl := 24 }) := by
  constructor
  · dloop_stop scanQuotDeclLoop
  · dloop_ws scanQuotDeclLoop
  · dloop_close scanQuotDeclLoop
    obtain ⟨hf, hl, hn, ht⟩ := hR
    exact ⟨rfl, ⟨hn, lpsR_close b _ _ _ _ _ hl hM (by decide) (by decide), ht⟩, hf⟩
  · dloop_comma scanQuotDeclLoop
  · dloop_quote scanQuotDeclLoop
  · dloop_key scanQuotDeclLoop
    all_goals obtain ⟨hf, hl, hn, ht⟩ := hR
    case kName =>
      rw [show UInt64.ofNat Key.kName.ctorIdx = (34 : Word) from rfl]
      dkey_num (st.1, st.2.1, readNatAt b v (numEnd b v), st.2.2.2)
      exact ⟨hf, lpsR_or b _ _ _ _ _ hl (by decide), hRn, ht⟩
    case kType =>
      rw [show UInt64.ofNat Key.kType.ctorIdx = (61 : Word) from rfl]
      dkey_num (st.1, st.2.1, st.2.2.1, readNatAt b v (numEnd b v))
      exact ⟨hf, lpsR_or b _ _ _ _ _ hl (by decide), hn, hRn⟩
    case kLevelParams =>
      rw [show UInt64.ofNat Key.kLevelParams.ctorIdx = (31 : Word) from rfl]
      dkey_res
      have hend := scanNatList_link b h64 hsize v
      rw [hx] at hend
      refine ⟨e', _, (st.1, x, st.2.2.1, st.2.2.2), by simp [dstepN, dendN, ← hend, okW], hie, hok, ?_⟩
      simp (config := {decide := true}) only [dstepN, dnumN, dlpsN, dflagN, ↓reduceIte]
      exact ⟨hf, .inl (list_link b h64 hsize v x e' hx), hn, ht⟩
    case kKind =>
      rw [show UInt64.ofNat Key.kKind.ctorIdx = (28 : Word) from rfl]
      dkey_res
      have hend := scanString_link b h64 hsize v
      rw [hx] at hend
      have hq := (strCode_link b h64 hsize v x e' hx 28).2 (by decide)
      refine ⟨e', _, (x, st.2.1, st.2.2.1, st.2.2.2), by simp [dstepN, dendN, ← hend, okW], hie, hok, ?_⟩
      simp (config := {decide := true}) only [dstepN, dnumN, dlpsN, dflagN, ↓reduceIte, ← hend, okW]
      exact ⟨hq, lpsR_or b _ _ _ _ _ hl (by decide), hn, ht⟩
  · dloop_other scanQuotDeclLoop

/-! ## `def` -/

/-- The relation for a `def` record. -/
def DefR (b : ByteArray) (seen : UInt32) (st : HintsRec × List Nat × Nat × String × Nat × Nat)
    (f : DFld) : Prop :=
  HintsR st.1 f.hk f.hn ∧ LpsR b seen 4 f.lps st.2.1 ∧ ItemR f.name st.2.2.1 ∧
    (f.flag = 1 → st.2.2.2.1 = "safe") ∧ ItemR f.type st.2.2.2.2.1 ∧ ItemR f.value st.2.2.2.2.2

theorem def_loop : DObjLoop b (fun i w seen (st : HintsRec × List Nat × Nat × String × Nat × Nat) =>
      scanDefDeclLoop b i w seen st.1 st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2.1 st.2.2.2.2.2) (DefR b)
    (fun d f => DeclR b d { f with pl := 21 }) := by
  constructor
  · dloop_stop scanDefDeclLoop
  · dloop_ws scanDefDeclLoop
  · dloop_close scanDefDeclLoop
    obtain ⟨hh, hl, hn, hs, ht, hvl⟩ := hR
    exact ⟨rfl, ⟨hn, lpsR_close b _ _ _ _ _ hl hM (by decide) (by decide), ht⟩, hvl, hh, hs⟩
  · dloop_comma scanDefDeclLoop
  · dloop_quote scanDefDeclLoop
  · dloop_key scanDefDeclLoop
    all_goals obtain ⟨hh, hl, hn, hs, ht, hvl⟩ := hR
    case kName =>
      rw [show UInt64.ofNat Key.kName.ctorIdx = (34 : Word) from rfl]
      dkey_num (st.1, st.2.1, readNatAt b v (numEnd b v), st.2.2.2.1, st.2.2.2.2.1, st.2.2.2.2.2)
      exact ⟨hh, lpsR_or b _ _ _ _ _ hl (by decide), hRn, hs, ht, hvl⟩
    case kType =>
      rw [show UInt64.ofNat Key.kType.ctorIdx = (61 : Word) from rfl]
      dkey_num (st.1, st.2.1, st.2.2.1, st.2.2.2.1, readNatAt b v (numEnd b v), st.2.2.2.2.2)
      exact ⟨hh, lpsR_or b _ _ _ _ _ hl (by decide), hn, hs, hRn, hvl⟩
    case kValue =>
      rw [show UInt64.ofNat Key.kValue.ctorIdx = (65 : Word) from rfl]
      dkey_num (st.1, st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2.1, readNatAt b v (numEnd b v))
      exact ⟨hh, lpsR_or b _ _ _ _ _ hl (by decide), hn, hs, ht, hRn⟩
    case kLevelParams =>
      rw [show UInt64.ofNat Key.kLevelParams.ctorIdx = (31 : Word) from rfl]
      dkey_res
      have hend := scanNatList_link b h64 hsize v
      rw [hx] at hend
      refine ⟨e', _, (st.1, x, st.2.2.1, st.2.2.2.1, st.2.2.2.2.1, st.2.2.2.2.2),
        by simp [dstepN, dendN, ← hend, okW], hie, hok, ?_⟩
      simp (config := {decide := true}) only [dstepN, dnumN, dlpsN, dflagN, dhkN, dhnN, ↓reduceIte]
      exact ⟨hh, .inl (list_link b h64 hsize v x e' hx), hn, hs, ht, hvl⟩
    case kAll =>
      rw [show UInt64.ofNat Key.kAll.ctorIdx = (1 : Word) from rfl]
      dkey_res
      have hend := scanNatList_link b h64 hsize v
      rw [hx] at hend
      refine ⟨e', _, st, by simp [dstepN, dendN, ← hend, okW], hie, hok, ?_⟩
      simp (config := {decide := true}) only [dstepN, dnumN, dlpsN, dflagN, dhkN, dhnN, ↓reduceIte]
      exact ⟨hh, lpsR_or b _ _ _ _ _ hl (by decide), hn, hs, ht, hvl⟩
    case kHints =>
      rw [show UInt64.ofNat Key.kHints.ctorIdx = (15 : Word) from rfl]
      dkey_res
      have hend := scanHints_link b h64 hsize v
      rw [hx] at hend
      have hH := hkv_link b h64 hsize v x e' hx
      refine ⟨e', _, (x, st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2.1, st.2.2.2.2.2),
        by simp [dstepN, dendN, ← hend, okW], hie, hok, ?_⟩
      simp (config := {decide := true}) only [dstepN, dnumN, dlpsN, dflagN, dhkN, dhnN, ↓reduceIte]
      exact ⟨hH, lpsR_or b _ _ _ _ _ hl (by decide), hn, hs, ht, hvl⟩
    case kSafety =>
      rw [show UInt64.ofNat Key.kSafety.ctorIdx = (54 : Word) from rfl]
      dkey_res
      have hend := scanString_link b h64 hsize v
      rw [hx] at hend
      have hq := (strCode_link b h64 hsize v x e' hx 54).1 rfl
      refine ⟨e', _, (st.1, st.2.1, st.2.2.1, x, st.2.2.2.2.1, st.2.2.2.2.2),
        by simp [dstepN, dendN, ← hend, okW], hie, hok, ?_⟩
      simp (config := {decide := true}) only [dstepN, dnumN, dlpsN, dflagN, dhkN, dhnN, ↓reduceIte,
        ← hend, okW]
      exact ⟨hh, lpsR_or b _ _ _ _ _ hl (by decide), hn, hq, ht, hvl⟩
  · dloop_other scanDefDeclLoop

/-! ## The records' entries -/

theorem axEntry_link (v : USize) (d : DeclRec) (e : USize) (h : scanAxiomDecl b v = .ok d e) :
    (dobjEntryN b.data v.toUInt64).pl = e.toUInt64 ∧
      DeclR b d { dobjEntryN b.data v.toUInt64 with pl := 20 } := by
  unfold scanAxiomDecl at h
  split at h
  · rename_i hc
    unfold dobjEntryN; rw [← (obj_open b h64 hsize v hc).2]
    exact dobj_link b h64 hsize _ _ _ (axiom_loop b h64 hsize) (v + 1) true 0 (false, [], 0, 0)
      DFld.init d e h ⟨rfl, .inr rfl, itemR_zero, itemR_zero⟩
  · cases h

theorem defEntry_link (v : USize) (d : DeclRec) (e : USize) (h : scanDefDecl b v = .ok d e) :
    (dobjEntryN b.data v.toUInt64).pl = e.toUInt64 ∧
      DeclR b d { dobjEntryN b.data v.toUInt64 with pl := 21 } := by
  unfold scanDefDecl at h
  split at h
  · rename_i hc
    unfold dobjEntryN; rw [← (obj_open b h64 hsize v hc).2]
    exact dobj_link b h64 hsize _ _ _ (def_loop b h64 hsize) (v + 1) true 0
      (.regular 0, [], 0, "", 0, 0) DFld.init d e h
      ⟨⟨rfl, itemR_zero⟩, .inr rfl, itemR_zero, fun h => absurd h (by decide), itemR_zero, itemR_zero⟩
  · cases h

theorem thmEntry_link (v : USize) (d : DeclRec) (e : USize) (h : scanThmDecl b v = .ok d e) :
    (dobjEntryN b.data v.toUInt64).pl = e.toUInt64 ∧
      DeclR b d { dobjEntryN b.data v.toUInt64 with pl := 22 } := by
  unfold scanThmDecl at h
  split at h
  · rename_i hc
    unfold dobjEntryN; rw [← (obj_open b h64 hsize v hc).2]
    exact dobj_link b h64 hsize _ _ _ (thm_loop b h64 hsize) (v + 1) true 0 ([], 0, 0, 0)
      DFld.init d e h ⟨.inr rfl, itemR_zero, itemR_zero, itemR_zero⟩
  · cases h

theorem opaqueEntry_link (v : USize) (d : DeclRec) (e : USize) (h : scanOpaqueDecl b v = .ok d e) :
    (dobjEntryN b.data v.toUInt64).pl = e.toUInt64 ∧
      DeclR b d { dobjEntryN b.data v.toUInt64 with pl := 23 } := by
  unfold scanOpaqueDecl at h
  split at h
  · rename_i hc
    unfold dobjEntryN; rw [← (obj_open b h64 hsize v hc).2]
    exact dobj_link b h64 hsize _ _ _ (opaque_loop b h64 hsize) (v + 1) true 0 (false, [], 0, 0, 0)
      DFld.init d e h ⟨rfl, .inr rfl, itemR_zero, itemR_zero, itemR_zero⟩
  · cases h

theorem quotEntry_link (v : USize) (d : DeclRec) (e : USize) (h : scanQuotDecl b v = .ok d e) :
    (dobjEntryN b.data v.toUInt64).pl = e.toUInt64 ∧
      DeclR b d { dobjEntryN b.data v.toUInt64 with pl := 24 } := by
  unfold scanQuotDecl at h
  split at h
  · rename_i hc
    unfold dobjEntryN; rw [← (obj_open b h64 hsize v hc).2]
    exact dobj_link b h64 hsize _ _ _ (quot_loop b h64 hsize) (v + 1) true 0 ("", [], 0, 0)
      DFld.init d e h ⟨⟨fun h => absurd h (by decide), fun h => absurd h (by decide),
        fun h => absurd h (by decide), fun h => absurd h (by decide)⟩, .inr rfl, itemR_zero, itemR_zero⟩
  · cases h

omit h64 hsize in
/-- An inductive record con-leche reads is an `.ind`. -/
theorem indLoop_ind (i : USize) (w : Bool) (seen : UInt32) (c : List IndCtorRec) (r : List IndRecRec)
    (t : List IndTypeRec) (d : DeclRec) (e : USize) (h : scanIndDeclLoop b i w seen c r t = .ok d e) :
    ∃ x y z, d = .ind x y z := by
  fun_induction scanIndDeclLoop b i w seen c r t <;> (try simp_all) <;> (repeat' split at h) <;>
    first | (cases h; exact ⟨_, _, _, rfl⟩) | cases h | simp_all | skip
  all_goals (subst_vars; exact ⟨_, _, _, rfl⟩)

omit h64 hsize in
theorem ind_ind (v : USize) (d : DeclRec) (e : USize) (h : scanIndDecl b v = .ok d e) :
    ∃ x y z, d = .ind x y z := by
  unfold scanIndDecl at h
  split at h
  · exact indLoop_ind b _ _ _ _ _ _ d e h
  · cases h

/-! ## `rec_decl_line` -/

/-- What the line loop's words say about con-leche's payload so far. -/
def DPlR (b : ByteArray) : LinePayload → DFld → Prop
  | .absent, _ => True
  | .decl d, f => DeclR b d f
  | _, _ => False

omit h64 hsize in
theorem declN_congr (a : Array UInt8) (i w j w' : Word) (f : DFld)
    (h : nextMemberN a i w = nextMemberN a j w') : declN a i w f = declN a j w' f := by
  conv => lhs; rw [declN]
  conv => rhs; rw [declN]
  simp only [h]

/-- **The declaration fields pass, linked**: on con-leche's `ok` path, a declaration line's words
(`pl ≠ 0`) are its record's fields. -/
theorem declLine_link (i : USize) (w : Bool) (ik : UInt8) (idx : Nat) (pl : LinePayload) (f : DFld)
    (r : LineRec) (e : USize) (h : scanLineLoop b i w ik idx pl = .ok r e) (hP : DPlR b pl f) :
    (declN b.data i.toUInt64 (bw w) f).pl ≠ 0 → DRecR b r (declN b.data i.toUInt64 (bw w) f) := by
  rw [scanLineLoop.eq_def] at h
  by_cases hi : i < b.usize
  · have hin := usizeInBounds b i hi
    have hi1 : (i + 1).toNat = i.toNat + 1 := usizeStep b i hi
    rw [dite_eq_left hi] at h
    simp only [uget_byteAt _ i hi] at h
    by_cases hws : isWs (byteAt b i) = true
    · simp only [hws, ite_true] at h
      rw [declN_congr _ _ _ _ _ _ (nm_ws b h64 hsize i _ hi hws)]
      exact declLine_link (i + 1) w ik idx pl f r e h hP
    simp only [hws, Bool.false_eq_true, ite_false] at h
    by_cases h125 : byteAt b i = 125
    · simp only [h125, show ((125 : UInt8) == 125) = true from rfl, ite_true] at h
      rw [declN_close _ _ _ _ (by rw [nm_close b h64 hsize i _ hi hws h125])]
      split at h; cases h
      cases pl
      · simp at h
      · exact hP.elim
      · exact hP.elim
      · exact hP.elim
      · by_cases hk : ik = 0
        · subst hk; obtain ⟨rfl, rfl⟩ := ScanRes.ok.inj h
          exact fun _ => hP
        · simp [hk] at h
      · exact hP.elim
    simp only [show (byteAt b i == 125) = false by simpa using h125, Bool.false_eq_true,
      ite_false] at h
    by_cases h44 : byteAt b i = 44
    · simp only [h44, show ((44 : UInt8) == 44) = true from rfl, ite_true] at h
      split at h; cases h; rename_i hw
      have hw' : w = false := by simpa using hw
      subst hw'
      simp only [bw, Bool.false_eq_true, ite_false]
      rw [declN_congr _ _ _ _ _ _ (nm_comma b h64 hsize i hi hws h44)]
      exact declLine_link (i + 1) true ik idx pl f r e h hP
    simp only [show (byteAt b i == 44) = false by simpa using h44, Bool.false_eq_true,
      ite_false] at h
    by_cases h34 : byteAt b i = 34
    · simp only [h34, show ((34 : UInt8) == 34) = true from rfl, ite_true] at h
      split at h; cases h; rename_i hw
      have hw' : w = true := by simpa using hw
      subst hw'
      split at h; cases h; rename_i hk
      split at h; cases h; rename_i hv
      have hk' : keyEnd b (i + 1) ≠ 0 := by simpa using hk
      have hv' : valueAt b i (keyEnd b (i + 1)) ≠ i := by simpa using hv
      have hm := nm_key b h64 hsize i hi h34 hk' hv'
      simp only [bw, ite_true]
      rw [declN_key _ _ _ _ (by rw [hm]; exact (by decide : (2 : Word) ≠ 0))
        (by rw [hm]; exact (by decide : (2 : Word) ≠ 1))]
      simp only [hm]
      generalize valueAt b i (keyEnd b (i + 1)) = v at h
      generalize keyAt b i (keyEnd b (i + 1) - (i + 1)) = K at h
      cases K
      all_goals (try dsimp only at h)
      all_goals (try (cases h; done))
      all_goals simp (config := {decide := true}) only [dlvN, dendDN, dplN, dpickN, dnameN, declCode, ↓reduceIte, UInt64.not_lt_zero]
      all_goals (try exact fun h0 => absurd rfl h0)
      all_goals (try exact fun h0 => h0.elim)
      case kAxiom =>
        split at h; cases h
        split at h; cases h; rename_i d' e' hd
        split at h
        · rename_i hie
          obtain ⟨hpl, hD⟩ := axEntry_link b h64 hsize v d' e' hd
          rw [hpl, ite_eq_left ((lt_toUInt64_iff _ _).mp hie)]
          exact declLine_link e' false ik idx (.decl d') _ r e h hD
        · cases h
      case kDef =>
        split at h; cases h
        split at h; cases h; rename_i d' e' hd
        split at h
        · rename_i hie
          obtain ⟨hpl, hD⟩ := defEntry_link b h64 hsize v d' e' hd
          rw [hpl, ite_eq_left ((lt_toUInt64_iff _ _).mp hie)]
          exact declLine_link e' false ik idx (.decl d') _ r e h hD
        · cases h
      case kThm =>
        split at h; cases h
        split at h; cases h; rename_i d' e' hd
        split at h
        · rename_i hie
          obtain ⟨hpl, hD⟩ := thmEntry_link b h64 hsize v d' e' hd
          rw [hpl, ite_eq_left ((lt_toUInt64_iff _ _).mp hie)]
          exact declLine_link e' false ik idx (.decl d') _ r e h hD
        · cases h
      case kOpaque =>
        split at h; cases h
        split at h; cases h; rename_i d' e' hd
        split at h
        · rename_i hie
          obtain ⟨hpl, hD⟩ := opaqueEntry_link b h64 hsize v d' e' hd
          rw [hpl, ite_eq_left ((lt_toUInt64_iff _ _).mp hie)]
          exact declLine_link e' false ik idx (.decl d') _ r e h hD
        · cases h
      case kQuot =>
        split at h; cases h
        split at h; cases h; rename_i d' e' hd
        split at h
        · rename_i hie
          obtain ⟨hpl, hD⟩ := quotEntry_link b h64 hsize v d' e' hd
          rw [hpl, ite_eq_left ((lt_toUInt64_iff _ _).mp hie)]
          exact declLine_link e' false ik idx (.decl d') _ r e h hD
        · cases h
      case kInductive =>
        split at h; cases h
        split at h; cases h; rename_i d' e' hd
        split at h
        · rename_i hie
          have hpl := indD_link b h64 hsize v
          rw [hd] at hpl
          obtain ⟨x, y, z, rfl⟩ := ind_ind b v d' e' hd
          simp only [← hpl, okW, (lt_toUInt64_iff _ _).mp hie, ↓reduceIte]
          exact declLine_link e' false ik idx (.decl (.ind x y z)) _ r e h ⟨rfl, v, rfl, e', hd⟩
        · cases h

    · simp only [show (byteAt b i == 34) = false by simpa using h34, Bool.false_eq_true,
        ite_false] at h
      cases h
  · rw [dite_eq_right hi] at h; cases h
termination_by b.size - i.toNat
decreasing_by
  all_goals first
    | omega
    | (have := USize.lt_iff_toNat_lt.mp ‹i < numEnd b _›; omega)
    | (have := USize.lt_iff_toNat_lt.mp ‹i < _›; omega)

end records

end ConAgua.Front.FieldsLink
