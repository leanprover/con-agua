import ConAgua.Arena.StrLit
import ConAgua.Arena.WhnfBase
import ConAgua.Scan.Utf8Link
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# `str_utf8_char` decodes one character of a string literal's pool words

`str_utf8_char(k, n)` (`StrLit.lean`) is `utf8_char` (`Scan/Utf8.lean`) with each byte read
`IN.u8[x]` replaced by `POOL⦃x⦄ & 255`. Its spec `strUtf8Char_spec` is against the byte-level
model `utf8CharN` of `utf8_char` on the pool's words (the total view `tpool`) truncated to bytes
(`poolBytes`); a word
read masked to a byte is that byte (`byteW_poolBytes`), so it is one `vcgen` + `finish`.
`ConAgua.Scan.utf8CharN_eq` then relates the model to Lean's decoder: on the UTF-8 bytes of
`c :: cs`, one per word (`charWords`), the result is `(c.val, c.utf8Size)` (`strUtf8Char_callW`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order
open L.Scan.Utf8

namespace L.Arena

/-! ## Character lists as pool words -/

/-- The UTF-8 bytes of a character list, one per word. -/
noncomputable def charWords (l : List Char) : List Word := l.utf8Encode.data.toList.map UInt8.toUInt64

theorem charWords_eq (l : List Char) :
    charWords l = (l.flatMap String.utf8EncodeChar).map UInt8.toUInt64 := by
  simp [charWords, List.utf8Encode]

theorem charWords_cons (c : Char) (l : List Char) :
    charWords (c :: l) = (String.utf8EncodeChar c).map UInt8.toUInt64 ++ charWords l := by
  simp [charWords_eq]

theorem charWords_nil : charWords [] = [] := by simp [charWords_eq]

theorem strWords_eq (s : String) : strWords s = charWords s.toList := by
  simp only [strWords, charWords, String.utf8Encode_toList]

theorem charWords_length_cons (c : Char) (l : List Char) :
    (charWords (c :: l)).length = c.utf8Size + (charWords l).length := by
  simp [charWords_cons]

theorem utf8Size_le_charWords (c : Char) (l : List Char) :
    c.utf8Size ≤ (charWords (c :: l)).length := by
  rw [charWords_length_cons]; omega

/-! ## The spec against `utf8CharN` -/

/-- The pool's words truncated to bytes: what `str_utf8_char` reads. -/
def poolBytes (a : Array Word) : Array UInt8 := a.map UInt64.toUInt8

theorem byteW_poolBytes (a : Array Word) (k : Word) (h : k.toNat < a.size) :
    byteW (poolBytes a) k = a[k.toNat] &&& 255 := by
  simp only [byteW, poolBytes, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    Array.getElem?_eq_getElem h, Option.map_some, Option.getD_some]
  rw [← UInt64.toNat_inj]
  simp [UInt64.toNat_and]
  exact (Nat.and_two_pow_sub_one_eq_mod _ 8).symm

grind_pattern [lang_grind] byteW_poolBytes => byteW (poolBytes a) k, a[k.toNat]

/-- An L load `POOL⦃x⦄` masked to a byte is the byte of the total pool view. -/
theorem byteW_poolBytes_ld (m : Mem) (x : Word)
    (h : (x &&& 1099511627775).toNat < (m.arr64 (tierA POOL (x >>> 40))).size) :
    byteW (poolBytes (tpool m)) x = (m.arr64 (tierA POOL (x >>> 40)))[(x &&& 1099511627775).toNat] &&& 255 := by
  rw [byteW_poolBytes _ _ (by rw [tpool_size]; exact x.toNat_lt),
    ← tpool_ld m x h (by rw [tpool_size]; exact x.toNat_lt)]
grind_pattern [lang_grind] byteW_poolBytes_ld =>
  byteW (poolBytes (tpool m)) x, (m.arr64 (tierA POOL (x >>> 40)))[(x &&& 1099511627775).toNat]

section strUtf8Char
variable (p : Prog) (hp : p.lookup "str_utf8_char" = some strUtf8CharL) (a : Array Word)
include hp

attribute [local lang_grind] utf8CharN in
theorem strUtf8Char_spec (n : Nat) (s₀ : St) (hm : tpool s₀.mem = a) (k e : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "str_utf8_char" [k, e]
    ⦃fun r s' => s' = s₀ ∧
      r = [(utf8CharN (poolBytes a) k e).1, (utf8CharN (poolBytes a) k e).2]; ⊤⦄ := by
  subst hm
  rw [invoke_eq _ hp]
  simp only [callFn, strUtf8CharL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] => vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64] <;> finish

end strUtf8Char

/-! ## Against Lean's decoder -/

/-- The pool's bytes from `k` on are the UTF-8 bytes of `c :: cs`. -/
theorem poolBytes_getD (a : Array Word) (k n : Nat) (l : List Char)
    (hs : sliceL a k (n - k) = charWords l) (hn : n ≤ a.size) (t : Nat)
    (ht : t < l.utf8Encode.size) :
    (poolBytes a).getD (k + t) 0 = l.utf8Encode[t] := by
  have hlen := congrArg List.length hs
  simp only [sliceL_length, charWords, List.length_map, Array.length_toList,
    ByteArray.size_data] at hlen
  have h := congrArg (fun l => l[t]?) hs
  simp only [sliceL, charWords, List.getElem?_ofFn, List.getElem?_map, Array.getElem?_toList] at h
  rw [dite_eq_left (by omega), Array.getElem?_eq_getElem (by omega),
    Array.getElem?_eq_getElem (by simpa using ht)] at h
  simp only [Option.getD_some, Option.map_some, Option.some.injEq] at h
  simp only [poolBytes, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    Array.getElem?_eq_getElem (show k + t < a.size by omega), Option.map_some, Option.getD_some, h,
    UInt8.toUInt8_toUInt64]
  rfl

theorem strUtf8Char_callW (p : Prog) (hp : p.lookup "str_utf8_char" = some strUtf8CharL) (N : Nat)
    (m : Mem) (k n : Word) (c : Char) (cs : List Char)
    (hs : sliceL (tpool m) k.toNat (n.toNat - k.toNat) = charWords (c :: cs))
    (hkn : k.toNat ≤ n.toNat) (hn : n.toNat ≤ (tpool m).size) (hn64 : n.toNat + 4 < 2 ^ 64)
    (r : List Word) (m' : Mem) (h : callW p N "str_utf8_char" [k, n] m = some (r, m')) :
    m' = m ∧ r.headD 0 = c.val.toUInt64 ∧ r.tail.headD 0 = UInt64.ofNat c.utf8Size := by
  obtain ⟨s', hs', heq, hr⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (strUtf8Char_spec p hp (tpool m) N _ rfl k n) h
  subst heq
  have hlen := congrArg List.length hs
  simp only [sliceL_length, charWords, List.length_map, Array.length_toList,
    ByteArray.size_data] at hlen
  have hpos : 0 < (c :: cs).utf8Encode.size := by
    have h1 := utf8Size_le_charWords c cs
    have h2 := Char.utf8Size_pos c
    simp only [charWords, List.length_map, Array.length_toList, ByteArray.size_data] at h1
    omega
  have hE := ConAgua.Scan.utf8CharN_eq (poolBytes (tpool m)) k n (c :: cs).utf8Encode 0 hpos
    (by omega) hn64 (fun t ht => by
      simpa only [Nat.zero_add] using poolBytes_getD _ _ _ _ hs hn t (by omega))
  rw [List.utf8DecodeChar?_utf8Encode_cons] at hE
  refine ⟨hs'.symm, ?_, ?_⟩ <;> simp [hr, hE, ConAgua.Scan.encChar]
