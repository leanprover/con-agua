module

public import ConAgua.Scan.Str
import ConAgua.Census.Attr
public import ConLeche.Frontend.Scan.Fast
import ConAgua.Scan.Link
import ConAgua.Scan.Utf8Link
import Std.Data.DTreeMap.Internal.Operations
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-!
# `scan_string` against con-leche's `scanString`

con-leche's `unescape` collects the unescaped bytes and validates them with `String.fromUTF8?` at
the end; the validator's model `unescN` stores nothing and validates each raw run between escapes
on its own (`utf8ValidN`). This file proves the two agree.

* `utf8ValidN_eq`: `utf8_valid(s, e)` is `IsValidUTF8` of the bytes `[s, e)` (the decode loop
  `ByteArray.utf8Decode?.go` without output, `valid_go`, after `ConAgua.Scan.loop_go`).
* `valid_split`: the UTF-8 of one character (which begins with a lead byte, so its position is a
  character boundary) splits validity: `X ++ [c].utf8Encode ++ Y` is valid iff `X` and `Y` are.
  Hence (`valid_append`) the collected bytes `A ++ run`, where `A` ends with an escape's
  character (`EndsChar`), are valid iff `A` and the raw run are.
* `escCL`: con-leche's escape at a backslash as a function (`unescape_esc`); `unescN_esc`: the
  model at a backslash checks the run, then continues where `escCL` does (bytes via `byteAt_eq`,
  `hex4_eq`, `hex3_eq`; positions in `b` are `pw s n` for body position `n`).
* `unesc_main`: the induction; `unescape_isSome_iff`/`unescN_eq`: statement 2.
* `hasEscape_iff`, `scanString_eq`: statement 3.
-/

namespace ConAgua.Scan.StrLink
open L L.Scan.Utf8 L.Scan.Str ConLeche.Frontend ConAgua.Scan

/-! ## `utf8_valid` -/

theorem valid_go (b : Array UInt8) (k0 n : Word) (B : ByteArray)
    (hkn : n.toNat = k0.toNat + B.size) (hn : n.toNat + 4 < 2 ^ 64)
    (hB : ∀ t (h : t < B.size), b.getD (k0.toNat + t) 0 = B[t])
    (i : Nat) (acc : Array Char) (hi : i ≤ B.size) :
    utf8ValidN b (k0 + UInt64.ofNat i) n =
      if (ByteArray.utf8Decode?.go B i acc hi).isSome then 1 else 0 := by
  fun_induction ByteArray.utf8Decode?.go B i acc hi with
  | case1 i acc hi h1 h2 =>
    have hk := word_add k0 i (by omega)
    have hch := utf8CharN_eq b (k0 + UInt64.ofNat i) n B i h1 (by omega) hn
      (fun t ht => by rw [hk, Nat.add_assoc]; exact hB (i + t) ht)
    rw [h2] at hch
    rw [utf8ValidN, ite_eq_left (by rw [UInt64.lt_iff_toNat_lt, hk]; omega), hch]
    simp [encChar]
  | case2 i acc hi h1 c h2 ih =>
    have hk := word_add k0 i (by omega)
    have hsz := ByteArray.le_size_of_utf8DecodeChar?_eq_some h2
    have hpos := c.utf8Size_pos
    have h4 := c.utf8Size_le_four
    have hch := utf8CharN_eq b (k0 + UInt64.ofNat i) n B i h1 (by omega) hn
      (fun t ht => by rw [hk, Nat.add_assoc]; exact hB (i + t) ht)
    rw [h2] at hch
    simp only [encChar] at hch
    have hlen : (UInt64.ofNat c.utf8Size).toNat = c.utf8Size :=
      UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
    have hk' : k0 + UInt64.ofNat i + UInt64.ofNat c.utf8Size = k0 + UInt64.ofNat (i + c.utf8Size) := by
      rw [UInt64.ofNat_add, UInt64.add_assoc]
    have hstep : k0 + UInt64.ofNat i < k0 + UInt64.ofNat i + UInt64.ofNat c.utf8Size := by
      rw [UInt64.lt_iff_toNat_lt, hk', word_add k0 (i + c.utf8Size) (by omega), hk]; omega
    rw [utf8ValidN, ite_eq_left (by rw [UInt64.lt_iff_toNat_lt, hk]; omega), hch]
    simp only [show ¬ UInt64.ofNat c.utf8Size = 0 from fun h => by
      have := congrArg UInt64.toNat h; rw [hlen] at this; simp at this; omega, ite_false,
      hstep, ite_true]
    rw [hk', ih]
  | case3 i acc hi h1 =>
    have hk := word_add k0 i (by omega)
    rw [utf8ValidN, ite_eq_right (by rw [UInt64.lt_iff_toNat_lt, hk]; omega)]
    simp

/-- Statement 1: `utf8_valid(s, e)` is `String.fromUTF8?` on the bytes `[s, e)`. -/
theorem utf8ValidN_eq (b : ByteArray) (hsize : b.size < 2 ^ 63) (s e : Word)
    (he : e.toNat ≤ b.size) :
    utf8ValidN b.data s e = if (b.extract s.toNat e.toNat).IsValidUTF8 then 1 else 0 := by
  by_cases hse : s.toNat < e.toNat
  · generalize hB : b.extract s.toNat e.toNat = B
    have hBs : B.size = e.toNat - s.toNat := by rw [← hB, ByteArray.size_extract]; omega
    have hl := valid_go b.data s e B (by omega) (by omega)
      (fun t ht => by
        subst hB
        rw [ByteArray.getElem_extract]
        have := ByteArray.getElem_extract_aux ht
        simp [Array.getD, this]; rfl) 0 #[] (Nat.zero_le _)
    rw [show s + UInt64.ofNat 0 = s by simp] at hl
    rw [hl]
    have hd : B.utf8Decode? = ByteArray.utf8Decode?.go B 0 #[] (by simp) := rfl
    rw [← hd]
    by_cases hv : B.IsValidUTF8
    · simp [hv, ByteArray.isSome_utf8Decode?_iff.mpr hv]
    · rw [ite_eq_right hv, ite_eq_right (fun h => hv (ByteArray.isSome_utf8Decode?_iff.mp h))]
  · rw [utf8ValidN, ite_eq_right (by rw [UInt64.lt_iff_toNat_lt]; exact hse)]
    rw [(ByteArray.extract_eq_empty_iff.mpr (by omega))]
    simp

theorem utf8ValidN_eq_fromUTF8 (b : ByteArray) (hsize : b.size < 2 ^ 63) (s e : Word)
    (he : e.toNat ≤ b.size) :
    utf8ValidN b.data s e = if (String.fromUTF8? (b.extract s.toNat e.toNat)).isSome then 1 else 0 := by
  rw [utf8ValidN_eq b hsize s e he]
  simp [String.fromUTF8?]


/-! ## Valid UTF-8 around one encoded character -/

/-- The UTF-8 of one character splits a byte array: the bytes around it are valid on their own
exactly when the whole is (the character begins with a lead byte, so its position is a
character boundary). -/
theorem valid_split (X Y : ByteArray) (c : Char) :
    (X ++ [c].utf8Encode ++ Y).IsValidUTF8 ↔ X.IsValidUTF8 ∧ Y.IsValidUTF8 := by
  refine ⟨fun h => ?_, fun ⟨hX, hY⟩ => (hX.append ByteArray.isValidUTF8_utf8Encode).append hY⟩
  let str : String := ⟨_, h⟩
  have hcs : 0 < [c].utf8Encode.size := by
    simp [List.utf8Encode_singleton, Char.utf8Size_pos]
  have hsz : str.toByteArray.size = X.size + [c].utf8Encode.size + Y.size := by
    simp [str, ByteArray.size_append]
  have hlt : (⟨X.size⟩ : String.Pos.Raw) < str.rawEndPos := by
    simp only [String.Pos.Raw.lt_iff, String.byteIdx_rawEndPos, ← String.size_toByteArray, hsz]; omega
  have hp : (⟨X.size⟩ : String.Pos.Raw).IsValid str := by
    refine String.Pos.Raw.isValid_iff_isUTF8FirstByte.mpr (Or.inr ⟨hlt, ?_⟩)
    have hb : ∀ h, (X ++ [c].utf8Encode ++ Y)[X.size]'h = [c].utf8Encode[0]'hcs := by
      intro h
      rw [ByteArray.getElem_append_left (by simp [ByteArray.size_append]; omega),
        ByteArray.getElem_append_right (by simp)]
      simp
    simp only [String.getUTF8Byte, str, hb]
    exact List.isUTF8FirstByte_getElem_utf8Encode_singleton.mpr rfl
  have h1 := (String.Pos.Raw.isValidUTF8_extract_iff (s := str) 0 ⟨X.size⟩
    (by simp [String.Pos.Raw.le_iff]) (String.Pos.Raw.le_of_lt hlt)).mpr
    (Or.inr ⟨String.Pos.Raw.isValid_zero, hp⟩)
  have h2 := (String.Pos.Raw.isValidUTF8_extract_iff (s := str) ⟨X.size⟩ str.rawEndPos
    (String.Pos.Raw.le_of_lt hlt) String.Pos.Raw.le_refl).mpr
    (Or.inr ⟨hp, String.Pos.Raw.isValid_rawEndPos⟩)
  have e1 : str.toByteArray.extract (0 : String.Pos.Raw).byteIdx X.size = X := by
    simp only [str, ByteArray.append_assoc]
    exact ByteArray.extract_append_eq_left rfl
  have e2 : str.toByteArray.extract X.size str.rawEndPos.byteIdx = [c].utf8Encode ++ Y := by
    rw [String.byteIdx_rawEndPos, ← String.size_toByteArray]
    simp only [str, ByteArray.append_assoc]
    exact ByteArray.extract_append_eq_right rfl (by simp [ByteArray.size_append])
  rw [e1] at h1
  rw [e2] at h2
  exact ⟨h1, ByteArray.isValidUTF8_utf8Encode_singleton_append_iff.mp h2⟩

/-- The collected bytes so far end at a character boundary: empty, or ending with an escape's
character. -/
def EndsChar (A : ByteArray) : Prop := A = ByteArray.empty ∨ ∃ A' c, A = A' ++ [c].utf8Encode

theorem valid_append (A Y : ByteArray) (hA : EndsChar A) :
    (A ++ Y).IsValidUTF8 ↔ A.IsValidUTF8 ∧ Y.IsValidUTF8 := by
  rcases hA with rfl | ⟨A', c, rfl⟩
  · simp
  · have h1 := valid_split A' Y c
    have h2 := valid_split A' ByteArray.empty c
    simp only [ByteArray.append_empty] at h2
    rw [h1, h2]; simp


/-! ## Words and `USize` positions in the body -/

/-- The word position in `b` of the body position `n` (the body starts at `s`). -/
def pw (s : Word) (n : Nat) : Word := UInt64.ofNat (s.toNat + n)

theorem pw_addk (s : Word) (n k : Nat) : pw s n + UInt64.ofNat k = pw s (n + k) := by
  simp only [pw, ← UInt64.ofNat_add, Nat.add_assoc]
theorem pw_add1 (s : Word) (n : Nat) : pw s n + 1 = pw s (n + 1) := pw_addk s n 1
theorem pw_add2 (s : Word) (n : Nat) : pw s n + 2 = pw s (n + 2) := pw_addk s n 2
theorem pw_add3 (s : Word) (n : Nat) : pw s n + 3 = pw s (n + 3) := pw_addk s n 3
theorem pw_add6 (s : Word) (n : Nat) : pw s n + 6 = pw s (n + 6) := pw_addk s n 6

theorem pw_toNat (s : Word) (n : Nat) (h : s.toNat + n < 2 ^ 64) : (pw s n).toNat = s.toNat + n :=
  UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)

theorem uofs (n : Nat) : USize.ofNat n + 1 = USize.ofNat (n + 1) := by rw [USize.ofNat_add]; rfl

theorem usz (h64 : System.Platform.numBits = 64) (m : Nat) (hm : m < 2 ^ 64) :
    (USize.ofNat m).toNat = m :=
  USize.toNat_ofNat_of_lt' (by rw [usize_size_eq64 h64]; exact hm)

theorem uget_eq' (a : ByteArray) (i : USize) (h : i.toNat < a.size) : a.uget i h = a[i.toNat] := rfl

/-- An `Option UInt32` (con-leche's `hexVal`, `hex4`, `hex3`) as the model's `(ok, value)`. -/
def optW : Option UInt32 → Word × Word
  | some v => (1, v.toUInt64)
  | none => (0, 0)

@[refines ConLeche.Frontend.hexVal]
theorem hexVal_eq (c : UInt8) : hexValN c.toUInt64 = optW (ConLeche.Frontend.hexVal c) :=
  u8_all (P := fun c => hexValN c.toUInt64 = optW (ConLeche.Frontend.hexVal c)) (by decide +kernel) c

theorem hexVal_lt (c : UInt8) : (ConLeche.Frontend.hexVal c).all (·.toNat < 16) = true :=
  u8_all (P := fun c => (ConLeche.Frontend.hexVal c).all (·.toNat < 16) = true) (by decide +kernel) c

theorem hexVal_lt' (c : UInt8) (v : UInt32) (h : ConLeche.Frontend.hexVal c = some v) : v.toNat < 16 := by
  have := hexVal_lt c; rw [h] at this; simpa using this

theorem comb4 (a x y z : UInt32) (ha : a.toNat < 16) (hx : x.toNat < 16) (hy : y.toNat < 16) :
    ((a <<< 12) ||| (x <<< 8) ||| (y <<< 4) ||| z).toUInt64 =
      (a.toUInt64 <<< 12) ||| (x.toUInt64 <<< 8) ||| (y.toUInt64 <<< 4) ||| z.toUInt64 := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt32.toNat_or, UInt32.toNat_shiftLeft,
    UInt32.toNat_toUInt64, Nat.shiftLeft_eq]
  simp
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem comb3 (a x y : UInt32) (ha : a.toNat < 16) (hx : x.toNat < 16) :
    ((a <<< 8) ||| (x <<< 4) ||| y).toUInt64 =
      (a.toUInt64 <<< 8) ||| (x.toUInt64 <<< 4) ||| y.toUInt64 := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt32.toNat_or, UInt32.toNat_shiftLeft,
    UInt32.toNat_toUInt64, Nat.shiftLeft_eq]
  simp
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem hex4_comb (A X Y Z : Option UInt32) (hA : A.all (·.toNat < 16) = true)
    (hX : X.all (·.toNat < 16) = true) (hY : Y.all (·.toNat < 16) = true) :
    (if (optW A).1 = 0 ∨ (optW X).1 = 0 ∨ (optW Y).1 = 0 ∨ (optW Z).1 = 0 then ((0 : Word), (0 : Word))
      else (1, ((optW A).2 <<< 12) ||| ((optW X).2 <<< 8) ||| ((optW Y).2 <<< 4) ||| (optW Z).2)) =
    optW (do
      let a ← A
      let c ← X
      let d ← Y
      let e ← Z
      some ((a <<< 12) ||| (c <<< 8) ||| (d <<< 4) ||| e)) := by
  rcases A with _ | a <;> rcases X with _ | x <;> rcases Y with _ | y <;> rcases Z with _ | z
  all_goals first
    | (simp [optW]; done)
    | (simp only [Option.all_some, decide_eq_true_eq] at hA hX hY
       change _ = optW (some ((a <<< 12) ||| (x <<< 8) ||| (y <<< 4) ||| z))
       simp only [optW, comb4 a x y z hA hX hY]
       simp)

theorem hex3_comb (A X Y : Option UInt32) (hA : A.all (·.toNat < 16) = true)
    (hX : X.all (·.toNat < 16) = true) :
    (if (optW A).1 = 0 ∨ (optW X).1 = 0 ∨ (optW Y).1 = 0 then ((0 : Word), (0 : Word))
      else (1, ((optW A).2 <<< 8) ||| ((optW X).2 <<< 4) ||| (optW Y).2)) =
    optW (do
      let a ← A
      let c ← X
      let d ← Y
      some ((a <<< 8) ||| (c <<< 4) ||| d)) := by
  rcases A with _ | a <;> rcases X with _ | x <;> rcases Y with _ | y
  all_goals first
    | (simp [optW]; done)
    | (simp only [Option.all_some, decide_eq_true_eq] at hA hX
       change _ = optW (some ((a <<< 8) ||| (x <<< 4) ||| y))
       simp only [optW, comb3 a x y hA hX]
       simp)

section body
variable (h64 : System.Platform.numBits = 64) (b : ByteArray) (hsize : b.size < 2 ^ 63) (s e : Word)
    (hse : s.toNat ≤ e.toNat) (he : e.toNat ≤ b.size)
include h64 hsize hse he

omit h64 hsize hse in
theorem body_size : (b.extract s.toNat e.toNat).size = e.toNat - s.toNat := by
  rw [ByteArray.size_extract]; omega

theorem body_usize : (b.extract s.toNat e.toNat).usize.toNat = e.toNat - s.toNat := by
  rw [usize_toNat_eq _ h64 (by rw [body_size b s e he]; omega), body_size b s e he]

theorem byteAt_eq (m : Nat) (hm : m ≤ e.toNat - s.toNat + 16) :
    byteE b.data e (pw s m) = (byteAt (b.extract s.toNat e.toNat) (USize.ofNat m)).toUInt64 := by
  have hu := body_usize h64 b hsize s e hse he
  have hp := pw_toNat s m (by omega)
  have hm' := usz h64 m (by omega)
  unfold byteE byteAt
  by_cases hlt : m < e.toNat - s.toNat
  · have h1 : USize.ofNat m < (b.extract s.toNat e.toNat).usize :=
      USize.lt_iff_toNat_lt.mpr (by rw [hm', hu]; omega)
    have h2 : pw s m < e := UInt64.lt_iff_toNat_lt.mpr (by rw [hp]; omega)
    simp only [h1, h2, dite_true, ite_true]
    simp only [byteW, hp, uget_eq', hm', ByteArray.getElem_extract]
    simp [Array.getD, show s.toNat + m < b.size by omega]
    rfl
  · have h1 : ¬ USize.ofNat m < (b.extract s.toNat e.toNat).usize := fun h => by
      rw [USize.lt_iff_toNat_lt, hm', hu] at h; omega
    have h2 : ¬ pw s m < e := fun h => by rw [UInt64.lt_iff_toNat_lt, hp] at h; omega
    simp only [h1, h2, dite_false, ite_false]
    rfl

theorem byteW_eq (m : Nat) (hm : m < e.toNat - s.toNat) (h) :
    byteW b.data (pw s m) = ((b.extract s.toNat e.toNat).uget (USize.ofNat m) h).toUInt64 := by
  have hp := pw_toNat s m (by omega)
  have hm' := usz h64 m (by omega)
  simp only [byteW, hp, uget_eq', hm', ByteArray.getElem_extract]
  simp [Array.getD, show s.toNat + m < b.size by omega]
  rfl

theorem hex4_eq (m : Nat) (hm : m ≤ e.toNat - s.toNat + 12) :
    hex4N b.data e (pw s m) = optW (ConLeche.Frontend.hex4 (b.extract s.toNat e.toNat) (USize.ofNat m)) := by
  unfold hex4N ConLeche.Frontend.hex4
  simp only [pw_add1, pw_add2, pw_add3, uofs,
    byteAt_eq h64 b hsize s e hse he m (by omega), byteAt_eq h64 b hsize s e hse he (m + 1) (by omega),
    byteAt_eq h64 b hsize s e hse he (m + 2) (by omega), byteAt_eq h64 b hsize s e hse he (m + 3) (by omega),
    hexVal_eq, Nat.add_assoc]
  exact hex4_comb _ _ _ _ (hexVal_lt _) (hexVal_lt _) (hexVal_lt _)

theorem hex3_eq (m : Nat) (hm : m ≤ e.toNat - s.toNat + 12) :
    hex3N b.data e (pw s m) = optW (ConLeche.Frontend.hex3 (b.extract s.toNat e.toNat) (USize.ofNat m)) := by
  unfold hex3N ConLeche.Frontend.hex3
  simp only [pw_add1, pw_add2, uofs,
    byteAt_eq h64 b hsize s e hse he m (by omega), byteAt_eq h64 b hsize s e hse he (m + 1) (by omega),
    byteAt_eq h64 b hsize s e hse he (m + 2) (by omega), hexVal_eq, Nat.add_assoc]
  exact hex3_comb _ _ _ (hexVal_lt _) (hexVal_lt _)

end body


/-! ## con-leche's `unescape`, one escape at a time -/

/-- The escape at the backslash at `j` in con-leche's `unescape`: the code point it contributes
and where the body continues, `none` for a bad escape. -/
def escCL (B : ByteArray) (j : USize) : Option (UInt32 × USize) :=
  let d := byteAt B (j + 1)
  let simple : Option UInt32 :=
    if d == 34 then some 34
    else if d == 92 then some 92
    else if d == 47 then some 47
    else if d == 98 then some 8
    else if d == 102 then some 12
    else if d == 110 then some 10
    else if d == 114 then some 13
    else if d == 116 then some 9
    else none
  match simple with
  | some v => some (v, j + 1 + 1)
  | none =>
    if d != 117 then none
    else
      match ConLeche.Frontend.hex4 B (j + 1 + 1) with
      | none => none
      | some v =>
        let j6 := j + 1 + 1 + 1 + 1 + 1 + 1
        if v < 0xD800 || 0xE000 ≤ v then some (v, j6)
        else if 0xDC00 ≤ v then some (replacementChar, j6)
        else
          let cont :=
            byteAt B j6 == 92 && byteAt B (j6 + 1) == 117 &&
              (byteAt B (j6 + 1 + 1) == 100 || byteAt B (j6 + 1 + 1) == 68)
          match (if cont then ConLeche.Frontend.hex3 B (j6 + 1 + 1 + 1) else none) with
          | some v2 =>
            if v2 < 0xC00 then some (replacementChar, j6)
            else
              let j12 := j6 + 1 + 1 + 1 + 1 + 1 + 1
              let cv := (((v &&& 0x3FF) <<< 10) ||| (v2 &&& 0x3FF)) + 0x10000
              some (cv, j12)
          | none => some (replacementChar, j6)

theorem unescape_esc (h64 : System.Platform.numBits = 64) (B : ByteArray) (hB : B.size < 2 ^ 63)
    (n : Nat) (hn : n < B.size) (hc : B[n] = 92) (acc : ByteArray) :
    ConLeche.Frontend.unescape B (USize.ofNat n) B.usize acc =
      match escCL B (USize.ofNat n) with
      | none => none
      | some (v, j') => ConLeche.Frontend.unescape B j' B.usize (acc ++ utf8Of v) := by
  have hu := usize_toNat_eq B h64 (by omega)
  have hn' := usz h64 n (by omega)
  have h1 : USize.ofNat n < B.usize := USize.lt_iff_toNat_lt.mpr (by omega)
  have hlt : ∀ k, k < 16 → 0 < k → USize.ofNat n < USize.ofNat (n + k) := fun k hk hk0 =>
    USize.lt_iff_toNat_lt.mpr (by rw [hn', usz h64 _ (by omega)]; omega)
  rw [ConLeche.Frontend.unescape]
  simp only [h1, dite_true, ite_true, uofs, uget_eq', hn', hc, bne_self_eq_false, Bool.false_eq_true,
    ite_false, hlt 2 (by omega) (by omega), hlt 6 (by omega) (by omega), hlt 12 (by omega) (by omega)]
  unfold escCL
  simp only [uofs]
  split <;> rename_i heq <;> simp only [heq]
  by_cases hd : (byteAt B (USize.ofNat (n + 1)) != 117) = true
  · simp only [hd, ite_true]
  simp only [hd, Bool.false_eq_true, ite_false]
  cases ConLeche.Frontend.hex4 B (USize.ofNat (n + 1 + 1)) with
  | none => rfl
  | some v =>
    simp only
    by_cases hv1 : (decide (v < 55296) || decide (57344 ≤ v)) = true
    · simp only [hv1, ite_true]
    simp only [hv1, Bool.false_eq_true, ite_false]
    by_cases hv2 : 56320 ≤ v
    · simp only [hv2, ite_true]
    simp only [hv2, ite_false]
    split <;> rename_i heq2 <;> simp only [heq2]
    split <;> rfl


theorem u8eq (x : UInt8) (k : UInt64) : (x.toUInt64 = k) ↔ x.toNat = k.toNat := by
  rw [← UInt64.toNat_inj, UInt8.toNat_toUInt64]
theorem u8beq (x k : UInt8) : (x == k) = true ↔ x.toNat = k.toNat := by
  rw [beq_iff_eq, UInt8.toNat_inj]
theorem u8bne (x k : UInt8) : (x != k) = true ↔ ¬ x.toNat = k.toNat := by
  rw [bne_iff_ne, ne_eq, UInt8.toNat_inj]
theorem u32lt (v : UInt32) (k : UInt64) : (v.toUInt64 < k) ↔ v.toNat < k.toNat := by
  rw [UInt64.lt_iff_toNat_lt, UInt32.toNat_toUInt64]
theorem u32le (v : UInt32) (k : UInt64) : (k ≤ v.toUInt64) ↔ k.toNat ≤ v.toNat := by
  rw [UInt64.le_iff_toNat_le, UInt32.toNat_toUInt64]

theorem escCL_next (B : ByteArray) (n : Nat) (v : UInt32) (j' : USize)
    (h : escCL B (USize.ofNat n) = some (v, j')) :
    ∃ k, 2 ≤ k ∧ k ≤ 12 ∧ j' = USize.ofNat (n + k) := by
  unfold escCL at h
  simp only [uofs, Nat.add_assoc, Nat.reduceAdd] at h
  repeat' split at h
  all_goals first
    | (simp only [reduceCtorEq] at h; done)
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h
       exact ⟨_, by omega, by omega, h.2.symm⟩)

theorem utf8Of_eq (v : UInt32) : utf8Of v = [Char.ofNat v.toNat].utf8Encode := by
  simp only [utf8Of, String.toUTF8, String.toByteArray_singleton]

theorem extract_push (B : ByteArray) (r n : Nat) (hr : r ≤ n) (hn : n < B.size) :
    (B.extract r n).push B[n] = B.extract r (n + 1) := by
  rw [ByteArray.extract_eq_extract_append_extract (a := B) (i := r) (k := n + 1) n hr (by omega),
    ByteArray.extract_add_one (by omega),
    ByteArray.append_toByteArray_singleton]

section model
variable (h64 : System.Platform.numBits = 64) (b : ByteArray) (hsize : b.size < 2 ^ 63) (s e : Word)
    (hse : s.toNat ≤ e.toNat) (he : e.toNat ≤ b.size)
include h64 hsize hse he

/-- The model at a backslash: the raw run `[r, n)` is checked, then the escape is con-leche's
(`escCL`), and the model continues where con-leche does, with a new run. -/
theorem unescN_esc (n r : Nat) (hn : n < e.toNat - s.toNat) (hc : byteW b.data (pw s n) = 92) :
    unescN b.data (pw s n) e (pw s r) =
      if utf8ValidN b.data (pw s r) (pw s n) = 0 then 0
      else match escCL (b.extract s.toNat e.toNat) (USize.ofNat n) with
        | none => 0
        | some (_, j') => unescN b.data (pw s j'.toNat) e (pw s j'.toNat) := by
  have hp : ∀ k, k ≤ 16 → (pw s (n + k)).toNat = s.toNat + n + k := fun k hk => by
    rw [pw_toNat s _ (by omega)]; omega
  have hp0 := pw_toNat s n (by omega)
  have hds : b.data.size = b.size := rfl
  have hcond : pw s n < UInt64.ofNat b.data.size ∧ pw s n < e := by
    constructor <;> rw [UInt64.lt_iff_toNat_lt, hp0]
    · rw [UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)]; omega
    · omega
  have hlt : ∀ k, k ≤ 16 → 0 < k → pw s n < pw s (n + k) := fun k hk hk0 => by
    rw [UInt64.lt_iff_toNat_lt, hp0, hp k hk]; omega
  have hu : ∀ k, k ≤ 16 → (USize.ofNat (n + k)).toNat = n + k := fun k hk => usz h64 _ (by omega)
  rw [unescN]
  simp only [hcond, and_self, dite_true, hc, ne_eq, not_true_eq_false, ite_false]
  by_cases hv : utf8ValidN b.data (pw s r) (pw s n) = 0
  · simp only [hv, ite_true]
  simp only [hv, ite_false]
  unfold uNextN escCL
  simp only [uofs, pw_add1, pw_add2, pw_add3, pw_add6, Nat.add_assoc, Nat.reduceAdd,
    byteAt_eq h64 b hsize s e hse he (n + 1) (by omega),
    byteAt_eq h64 b hsize s e hse he (n + 6) (by omega),
    byteAt_eq h64 b hsize s e hse he (n + 7) (by omega),
    byteAt_eq h64 b hsize s e hse he (n + 8) (by omega),
    hex4_eq h64 b hsize s e hse he (n + 2) (by omega),
    hex3_eq h64 b hsize s e hse he (n + 9) (by omega)]
  have hl2 := hlt 2 (by omega) (by omega)
  have hl6 := hlt 6 (by omega) (by omega)
  have hl12 := hlt 12 (by omega) (by omega)
  have hu2 := hu 2 (by omega)
  have hu6 := hu 6 (by omega)
  have hu12 := hu 12 (by omega)
  generalize byteAt (b.extract s.toNat e.toNat) (USize.ofNat (n + 1)) = d
  generalize byteAt (b.extract s.toNat e.toNat) (USize.ofNat (n + 6)) = d6
  generalize byteAt (b.extract s.toNat e.toNat) (USize.ofNat (n + 7)) = d7
  generalize byteAt (b.extract s.toNat e.toNat) (USize.ofNat (n + 8)) = d8
  generalize ConLeche.Frontend.hex4 (b.extract s.toNat e.toNat) (USize.ofNat (n + 2)) = H4
  generalize ConLeche.Frontend.hex3 (b.extract s.toNat e.toNat) (USize.ofNat (n + 9)) = H3
  simp only [u8eq, u8beq, u8bne, UInt64.reduceToNat, UInt8.reduceToNat, Bool.or_eq_true, decide_eq_true_eq]
  by_cases h1 : d.toNat = 34
  · simp only [h1, true_or, ite_true, hl2, hu2]
  by_cases h2 : d.toNat = 92 ∨ d.toNat = 47 ∨ d.toNat = 98 ∨ d.toNat = 102 ∨ d.toNat = 110 ∨
      d.toNat = 114 ∨ d.toNat = 116
  · rcases h2 with h | h | h | h | h | h | h <;>
      simp only [h, true_or, or_true, ite_true, ite_false, hl2, hu2, Nat.reduceEqDiff]
  obtain ⟨h2, h3, h4, h5, h6, h7, h8⟩ := by simpa only [not_or] using h2
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, or_self, ite_false]
  by_cases h117 : ¬ d.toNat = 117
  · simp only [h117, not_false_eq_true, ite_true]
  simp only [h117, ite_false]
  rcases H4 with _ | v
  · simp [optW]
  simp only [optW, u32lt, u32le, UInt64.reduceToNat, UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le,
    UInt32.reduceToNat]
  have h10 : ((1 : Word) = 0) = False := by decide
  simp only [h10, ite_false]
  by_cases hv1 : v.toNat < 55296 ∨ 57344 ≤ v.toNat
  · simp only [hv1, ite_true, hl6, hu6]
  by_cases hv2 : 56320 ≤ v.toNat
  · simp only [hv1, hv2, ite_true, ite_false, hl6, hu6]
  simp only [hv1, hv2, ite_false]
  simp only [u8beq, Bool.and_eq_true, Bool.or_eq_true, UInt8.reduceToNat, and_assoc]
  by_cases hcont : d6.toNat = 92 ∧ d7.toNat = 117 ∧ (d8.toNat = 100 ∨ d8.toNat = 68)
  · obtain ⟨c1, c2, c3⟩ := hcont
    simp only [c1, c2, c3, true_and, ite_true]
    rcases H3 with _ | v2
    · have h00 : ((0 : Word) ≠ 0) = False := by decide
      simp only [h00, false_and, ite_false, hl6, ite_true, hu6]
    · have h10' : ((1 : Word) ≠ 0) = True := by decide
      simp only [h10', true_and, u32le, UInt64.reduceToNat]
      by_cases hv3 : 3072 ≤ v2.toNat
      · simp only [hv3, ite_true, show ¬ v2.toNat < 3072 by omega, ite_false, hl12, hu12]
      · simp only [hv3, ite_false, show v2.toNat < 3072 by omega, ite_true, hl6, hu6]
  · have hn' : ∀ P Q : Prop, ¬ (d6.toNat = 92 ∧ d7.toNat = 117 ∧ (d8.toNat = 100 ∨ d8.toNat = 68) ∧
        P ∧ Q) := fun _ _ h => hcont ⟨h.1, h.2.1, h.2.2.1⟩
    simp only [hn', hcont, ite_false, hl6, ite_true, hu6]

/-- The induction: con-leche's `unescape` on the body from `n` with the bytes `acc` collected so
far, `acc` = `A` (ending at a character boundary) followed by the raw run `[r, n)`, against the
model from `n` with the run start `r`. -/
theorem unesc_main (A : ByteArray) (hA : EndsChar A) (n r : Nat) (hr : r ≤ n)
    (hnL : n ≤ e.toNat - s.toNat + 12) (acc : ByteArray)
    (hacc : acc = A ++ (b.extract s.toNat e.toNat).extract r n) :
    (ConLeche.Frontend.unescape (b.extract s.toNat e.toNat) (USize.ofNat n)
        (b.extract s.toNat e.toNat).usize acc).isSome = true ↔
      (A.IsValidUTF8 ∧ unescN b.data (pw s n) e (pw s r) = 1) := by
  induction hm : e.toNat - s.toNat - n using Nat.strongRecOn generalizing A n r acc with
  | _ m ih =>
  have hBs := body_size b s e he
  have hu := body_usize h64 b hsize s e hse he
  have hds : b.data.size = b.size := rfl
  have hn' := usz h64 n (by omega)
  have hp0 := pw_toNat s n (by omega)
  have hpr := pw_toNat s r (by omega)
  -- the raw run `[r, n)` in the body is `[s + r, s + n)` in `b`
  have hrun : (b.extract s.toNat e.toNat).extract r n =
      b.extract (pw s r).toNat (min (pw s n).toNat e.toNat) := by
    rw [ByteArray.extract_extract, hpr, hp0]
  by_cases hnl : n < e.toNat - s.toNat
  · have h1 : USize.ofNat n < (b.extract s.toNat e.toNat).usize :=
      USize.lt_iff_toNat_lt.mpr (by omega)
    have hcond : pw s n < UInt64.ofNat b.data.size ∧ pw s n < e := by
      constructor <;> rw [UInt64.lt_iff_toNat_lt, hp0]
      · rw [UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)]; omega
      · omega
    have hbw := byteW_eq h64 b hsize s e hse he n hnl (by rw [hn', hBs]; exact hnl)
    by_cases hc : (b.extract s.toNat e.toNat)[n]'(by omega) = 92
    · -- an escape
      have hc' : byteW b.data (pw s n) = 92 := by rw [hbw, uget_eq']; simp only [hn', hc]; rfl
      rw [unescape_esc h64 _ (by omega) n (by omega) hc acc,
        unescN_esc h64 b hsize s e hse he n r hnl hc']
      have hv := utf8ValidN_eq b hsize (pw s r) (pw s n) (by rw [hp0]; omega)
      rw [Nat.min_eq_left (by omega : (pw s n).toNat ≤ e.toNat)] at hrun
      rw [hv, ← hrun]
      cases hE : escCL (b.extract s.toNat e.toNat) (USize.ofNat n) with
      | none => simp
      | some p =>
        obtain ⟨v, j'⟩ := p
        obtain ⟨k, hk2, hk12, rfl⟩ := escCL_next _ n v j' hE
        simp only
        rw [ih (e.toNat - s.toNat - (n + k)) (by omega) (acc ++ utf8Of v) (by
            rw [utf8Of_eq]; exact Or.inr ⟨acc, _, rfl⟩) (n + k) (n + k) (Nat.le_refl _) (by omega)
            (acc ++ utf8Of v) (by simp) rfl,
          usz h64 _ (by omega)]
        have hs := valid_split (A ++ (b.extract s.toNat e.toNat).extract r n) ByteArray.empty
          (Char.ofNat v.toNat)
        rw [ByteArray.append_empty] at hs
        rw [hacc, utf8Of_eq, hs, valid_append _ _ hA]
        by_cases hR : ((b.extract s.toNat e.toNat).extract r n).IsValidUTF8
        · simp [hR]
        · simp [hR]
    · -- a raw byte
      have hlt1 : USize.ofNat n < USize.ofNat (n + 1) :=
        USize.lt_iff_toNat_lt.mpr (by rw [hn', usz h64 _ (by omega)]; omega)
      have hc' : ((b.extract s.toNat e.toNat).uget (USize.ofNat n) (by rw [hn']; omega) != 92) = true := by
        rw [uget_eq']; simp only [hn']; simpa using hc
      rw [ConLeche.Frontend.unescape]
      simp only [h1, dite_true, ite_true, hc', uofs, hlt1]
      rw [unescN]
      simp only [hcond, and_self, dite_true, hbw, uget_eq', hn']
      have hne : ¬ ((b.extract s.toNat e.toNat)[n]'(by omega)).toUInt64 = 92 := by
        intro h; apply hc; rw [u8eq] at h; exact UInt8.toNat_inj.mp h
      simp only [ne_eq, hne, not_false_eq_true, ite_true, pw_add1]
      have hl1 : pw s n < pw s (n + 1) := by
        rw [UInt64.lt_iff_toNat_lt, hp0, pw_toNat s _ (by omega)]; omega
      simp only [hl1, ite_true]
      exact ih (e.toNat - s.toNat - (n + 1)) (by omega) A hA (n + 1) r (by omega) (by omega) _
        (by rw [hacc, ← ByteArray.append_toByteArray_singleton, ByteArray.append_assoc,
              ByteArray.append_toByteArray_singleton, extract_push _ r n hr (by omega)]) rfl
  · -- the end of the body
    have h1 : ¬ USize.ofNat n < (b.extract s.toNat e.toNat).usize := fun h => by
      rw [USize.lt_iff_toNat_lt] at h; omega
    rw [ConLeche.Frontend.unescape]
    simp only [h1, dite_false]
    have h2 : ¬ (pw s n < UInt64.ofNat b.data.size ∧ pw s n < e) := fun h => by
      have := h.2; rw [UInt64.lt_iff_toNat_lt, hp0] at this; omega
    rw [unescN]
    simp only [h2, dite_false]
    rw [utf8ValidN_eq b hsize (pw s r) e he,
      Nat.min_eq_right (by omega : e.toNat ≤ (pw s n).toNat)] at *
    rw [← hrun, hacc]
    simp only [String.fromUTF8?, Option.isSome_dite, valid_append _ _ hA]
    by_cases hR : ((b.extract s.toNat e.toNat).extract r n).IsValidUTF8
    · simp [hR]
    · simp [hR]

end model


/-! ## The models answer `0` or `1` -/

theorem utf8ValidN_01 (b : Array UInt8) (k n : Word) : utf8ValidN b k n = 0 ∨ utf8ValidN b k n = 1 := by
  fun_induction utf8ValidN b k n <;> simp_all

theorem unescN_01 (b : Array UInt8) (j e r : Word) : unescN b j e r = 0 ∨ unescN b j e r = 1 := by
  fun_induction unescN b j e r <;> simp_all [utf8ValidN_01]

/-- Statement 2: con-leche's `unescape` on the body `[s, e)` (sliced out) succeeds exactly when
the model answers `1`. -/
theorem unescape_isSome_iff (h64 : System.Platform.numBits = 64) (b : ByteArray)
    (hsize : b.size < 2 ^ 63) (s e : Word) (hse : s ≤ e) (he : e.toNat ≤ b.size) :
    (ConLeche.Frontend.unescape (b.extract s.toNat e.toNat) 0 (b.extract s.toNat e.toNat).usize
        ByteArray.empty).isSome = true ↔ unescN b.data s e s = 1 := by
  have h := unesc_main h64 b hsize s e (UInt64.le_iff_toNat_le.mp hse) he ByteArray.empty (Or.inl rfl)
    0 0 (Nat.le_refl _) (by omega) ByteArray.empty (by simp)
  have hs : pw s 0 = s := by simp [pw]
  have h0 : USize.ofNat 0 = 0 := rfl
  rw [hs, h0] at h
  simpa using h

theorem unescN_eq (h64 : System.Platform.numBits = 64) (b : ByteArray)
    (hsize : b.size < 2 ^ 63) (s e : Word) (hse : s ≤ e) (he : e.toNat ≤ b.size) :
    unescN b.data s e s =
      if (ConLeche.Frontend.unescape (b.extract s.toNat e.toNat) 0 (b.extract s.toNat e.toNat).usize
        ByteArray.empty).isSome then 1 else 0 := by
  have h := unescape_isSome_iff h64 b hsize s e hse he
  rcases unescN_01 b.data s e s with h0 | h1
  · rw [h0, ite_eq_right]; intro hc; rw [h.mp hc] at h0; cases h0
  · rw [h1, ite_eq_left (h.mpr h1)]

/-! ## `has_escape` -/

theorem hasEscapeN_01 (b : Array UInt8) (j e : Nat) :
    L.Scan.Leaves.hasEscapeN b j e = 0 ∨ L.Scan.Leaves.hasEscapeN b j e = 1 := by
  fun_induction L.Scan.Leaves.hasEscapeN b j e <;> simp_all

theorem hasEscape_iff (h64 : System.Platform.numBits = 64) (b : ByteArray) (hsize : b.size < 2 ^ 63)
    (j e : USize) :
    hasEscape b j e = true ↔ L.Scan.Leaves.hasEscapeN b.data j.toNat e.toNat = 1 := by
  fun_induction hasEscape b j e with
  | case1 j h hlt hc =>
    have hc' : b.data[j.toNat]'(usizeInBounds' b j h) = 92 := by
      have h2 : (b.uget j (usizeInBounds' b j h) == 92) = true := hc
      simpa [uget_eq] using h2
    simp [L.Scan.Leaves.hasEscapeN_hit b.data j.toNat e.toNat (usizeInBounds' b j h)
      (USize.lt_iff_toNat_lt.mp hlt) hc']
  | case2 j h hlt hc ih =>
    have hc' : b.data[j.toNat]'(usizeInBounds' b j h) ≠ 92 := by
      have h2 : ¬ (b.uget j (usizeInBounds' b j h) == 92) = true := hc
      simpa [uget_eq] using h2
    rw [ih, L.Scan.Leaves.hasEscapeN_miss b.data j.toNat e.toNat (j + 1).toNat (usizeStep b j h)
      (usizeInBounds' b j h) (USize.lt_iff_toNat_lt.mp hlt) hc']
  | case3 j h hlt =>
    simp [L.Scan.Leaves.hasEscapeN_past b.data j.toNat e.toNat (usizeInBounds' b j h)
      (Nat.le_of_not_lt (fun h' => hlt (USize.lt_iff_toNat_lt.mpr h')))]
  | case4 j h =>
    simp [L.Scan.Leaves.hasEscapeN_end b.data j.toNat e.toNat (usizeGe b j h64 (by omega) h)]

/-! ## `scan_string` -/

/-- A scanner's result as the validator's word: the position after it, or `0`. -/
def okW {α : Type} : ScanRes α → Word
  | .ok _ p => p.toUInt64
  | .err _ => 0

/-- Statement 3: the validator's `scan_string` model is con-leche's `scanString`, position for
position. -/
theorem scanString_eq (h64 : System.Platform.numBits = 64) (b : ByteArray) (hsize : b.size < 2 ^ 63)
    (i : USize) : okW (ConLeche.Frontend.scanString b i) = scanStringN b.data i.toUInt64 := by
  have hbs : b.data.size = b.size := rfl
  have hiu : i.toUInt64.toNat = i.toNat := USize.toNat_toUInt64 i
  have hbsz : (UInt64.ofNat b.data.size).toNat = b.size :=
    UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  unfold ConLeche.Frontend.scanString scanStringN
  by_cases hi : i.toNat < b.size
  · have hiU : i < b.usize :=
      USize.lt_iff_toNat_lt.mpr (by rw [usize_toNat_eq b h64 (by omega)]; exact hi)
    have hba : byteAt b i = b[i.toNat] := by simp only [byteAt, hiU, dite_true]; rfl
    have hbw : byteW b.data i.toUInt64 = b[i.toNat].toUInt64 := by
      simp only [byteW, hiu, Array.getD, hbs, hi, dite_true]; rfl
    have hc1 : i.toUInt64 < UInt64.ofNat b.data.size := by rw [UInt64.lt_iff_toNat_lt, hiu, hbsz]; exact hi
    have hi1 : (i + 1).toNat = i.toNat + 1 := usizeStep b i hiU
    have hi1' : (i.toUInt64 + 1).toNat = i.toNat + 1 := by
      rw [UInt64.toNat_add, hiu]; simp; omega
    simp only [hba, hbw, hc1, true_and, u8eq, u8bne, UInt64.reduceToNat, UInt8.reduceToNat, hi1']
    by_cases hq : ¬ b[i.toNat].toNat = 34
    · simp [hq, okW]
    simp only [hq, ite_false]
    have hsc := strClose_toNat_eq b h64 (by omega) (i + 1)
    rw [hi1] at hsc
    rw [← hsc]
    generalize strClose b (i + 1) = e at hsc ⊢
    have hE : UInt64.ofNat e.toNat = e.toUInt64 := by
      apply UInt64.toNat_inj.mp; rw [USize.toNat_toUInt64, UInt64.toNat_ofNat_of_lt'
        (by have := USize.toNat_lt_two_pow_numBits e; rw [h64] at this; simp [UInt64.size]; omega)]
    rw [hE]
    have hq' : b[i.toNat].toNat = 34 := Classical.not_not.mp hq
    simp only [hq', ite_true]
    by_cases he0 : e = 0
    · subst he0; simp [okW]
    have heN : L.Examples.strCloseN b.data (i.toNat + 1) ≠ 0 := fun h => he0 (USize.toNat_inj.mp (by
      rw [hsc, h]; rfl))
    obtain ⟨hb1, hb2⟩ := L.Examples.strCloseN_bounds b.data (i.toNat + 1) heN
    have hEne : ¬ e.toUInt64 = 0 := fun h => he0 (USize.toNat_inj.mp (by
      have := congrArg UInt64.toNat h; rw [USize.toNat_toUInt64] at this; rw [this]; rfl))
    have heq0 : (e == 0) = false := by simpa using he0
    have he1 : (e + 1).toUInt64 = e.toUInt64 + 1 := by
      apply UInt64.toNat_inj.mp
      rw [USize.toNat_toUInt64, UInt64.toNat_add, USize.toNat_toUInt64, USize.toNat_add]
      simp only [USize.toNat_one, UInt64.toNat_one, usize_size_eq64 h64]
    have hs1 : (i.toUInt64 + 1).toNat = (i + 1).toNat := by rw [hi1', hi1]
    simp only [heq0, hEne, Bool.false_eq_true, ite_false, USize.toNat_toUInt64]
    have hhe := hasEscape_iff h64 b hsize (i + 1) e
    rw [hi1] at hhe
    rcases hasEscapeN_01 b.data (i.toNat + 1) e.toNat with h0 | h1
    · have hf : hasEscape b (i + 1) e = false := by
        cases hh : hasEscape b (i + 1) e
        · rfl
        · rw [hhe.mp hh] at h0; cases h0
      have hv := utf8ValidN_eq_fromUTF8 b hsize (i.toUInt64 + 1) e.toUInt64
        (by rw [USize.toNat_toUInt64]; omega)
      rw [hs1, USize.toNat_toUInt64] at hv
      have h00 : UInt64.ofNat 0 = 0 := rfl
      simp only [hf, Bool.false_eq_true, ite_false, h0, h00, ne_eq, not_true_eq_false, hv]
      cases String.fromUTF8? (b.extract (i + 1).toNat e.toNat) <;> simp [okW, he1]
    · have ht : hasEscape b (i + 1) e = true := hhe.mpr h1
      have hu := unescN_eq h64 b hsize (i.toUInt64 + 1) e.toUInt64
        (by rw [UInt64.le_iff_toNat_le, hi1', USize.toNat_toUInt64]; omega)
        (by rw [USize.toNat_toUInt64]; omega)
      rw [hs1, USize.toNat_toUInt64] at hu
      have h10 : ¬ UInt64.ofNat 1 = 0 := by decide
      simp only [ht, ite_true, h1, ne_eq, h10, not_false_eq_true, hu]
      cases ConLeche.Frontend.unescape (b.extract (i + 1).toNat e.toNat) 0
        (b.extract (i + 1).toNat e.toNat).usize ByteArray.empty <;> simp [okW, he1]
  · have hiU : ¬ i < b.usize := fun h => by
      rw [USize.lt_iff_toNat_lt, usize_toNat_eq b h64 (by omega)] at h; exact hi h
    have hc1 : ¬ i.toUInt64 < UInt64.ofNat b.data.size := by
      rw [UInt64.lt_iff_toNat_lt, hiu, hbsz]; exact hi
    have hba0 : byteAt b i = 0 := by simp only [byteAt, hiU, dite_false]
    have hcond : ¬ (i.toUInt64 < UInt64.ofNat b.data.size ∧ byteW b.data i.toUInt64 = 34) :=
      fun h => hc1 h.1
    simp only [hcond, ite_false, hba0]
    simp [okW]

end ConAgua.Scan.StrLink
