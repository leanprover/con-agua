module

public import ConAgua.Scan.Leaves
import ConAgua.Census.Attr
public import ConLeche.Frontend.Scan.Fast
import ConAgua.Scan.Link
public import ConAgua.Scan.WordLink
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-!
# Linking the leaf models to con-leche's `USize`-position originals

`ConAgua.Scan.Leaves`'s `skipWsN`/`skipDigitsN`/`keyEndN`/`numEndN`/`hasEscapeN`/`newlineFromN`
are con-leche's `skipWs`/`skipDigits`/`keyEnd`/`numEnd`/`hasEscape`/`newlineFrom`
(`ConLeche/Frontend/Scan/Fast.lean`) with `Nat` positions over `Array UInt8` in place of `USize`
positions over `ByteArray`. This file proves each pair agrees, the same way `ConAgua.Scan.Link`
does for `strClose`/`skipBraced`: `fun_induction` on the con-leche function, one guarded equation
of the model per arm, `uget_eq` turning a `ByteArray` read into the `Array UInt8` read the model's
hypothesis names.

`hasEscape`/`newlineFrom` return `Bool`, the models `Nat` (`0`/`1`); rather than force a
`Bool`-valued model, the two are linked by an `↔` against `= true` — `hasEscape_iff`,
`newlineFrom_iff` — which is what every caller needs anyway (a `Bool` is tested, never compared
to `1`). `numEnd` is no loop (one call to `skip_digits`, two comparisons, exactly as
`L.Scan.Leaves.numEnd`'s spec proof treats it): the link rewrites the comparisons' conditions into
the model's rather than inducting.

Each `Nat`-level link also gets a `Word` form: `(skipWs b i).toUInt64 = UInt64.ofNat (skipWsN …)`
etc., via `WordLink.toUInt64_eq_ofNat` (`.toUInt64` is `UInt64.ofNat ∘ toNat` on every `USize`,
no `h64` needed) composed with the `Nat`-level link — what `ConAgua.Scan.KeyLink`/`ValuesLink`
actually rewrite with, since the Stage B models compute in `Word`.

`byteAt_eq_getD` (needed for `numEnd`, and reused by `ConAgua.Scan.KeyLink`/`ValuesLink`) is the
`Array UInt8`-level form of `WordLink.byteAt_toUInt64_eq`: con-leche's `byteAt` is the model's
`Array.getD … 0` read, both `0` past the end.
-/

namespace ConAgua.Scan

open ConLeche.Frontend
open L.Scan.Leaves
open L.Scan.Utf8 (byteW)

variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 64)

/-! ## `byte_at`, at the `Array UInt8` level -/

include h64 hsize in
/-- con-leche's `byteAt`, as the model reads it: `Array.getD … 0`, `0` past the end (the `UInt8`
form of `WordLink.byteAt_toUInt64_eq`, via injectivity of `UInt8.toUInt64`). -/
theorem byteAt_eq_getD (i : USize) : byteAt b i = b.data.getD i.toNat 0 := by
  have h := byteAt_toUInt64_eq b i h64 hsize
  unfold byteW at h
  rw [USize.toNat_toUInt64] at h
  apply UInt8.toNat_inj.mp
  have h' := congrArg UInt64.toNat h
  simpa only [UInt8.toNat_toUInt64] using h'

/-! ## `skip_ws` -/

include h64 hsize in
@[refines ConLeche.Frontend.skipWs]
theorem skipWs_toNat_eq (i : USize) : (skipWs b i).toNat = skipWsN b.data i.toNat := by
  fun_induction skipWs b i with
  | case1 i h hws ih =>
    have hws' : b.data[i.toNat]'(usizeInBounds' b i h) = 32 ∨
        b.data[i.toNat]'(usizeInBounds' b i h) = 9 ∨ b.data[i.toNat]'(usizeInBounds' b i h) = 13 := by
      simp only [isWs, Bool.or_eq_true, beq_iff_eq, or_assoc] at hws
      simpa [uget_eq] using hws
    rw [ih, usizeStep b i h]
    exact (skipWsN_ws b.data i.toNat (i.toNat + 1) rfl (usizeInBounds' b i h) hws').symm
  | case2 i h hws =>
    have hws' : ¬ (b.data[i.toNat]'(usizeInBounds' b i h) = 32 ∨
        b.data[i.toNat]'(usizeInBounds' b i h) = 9 ∨ b.data[i.toNat]'(usizeInBounds' b i h) = 13) := by
      simp only [isWs, Bool.or_eq_true, beq_iff_eq, or_assoc] at hws
      simpa [uget_eq] using hws
    exact (skipWsN_other b.data i.toNat (usizeInBounds' b i h) hws').symm
  | case3 i h =>
    exact (skipWsN_end b.data i.toNat (usizeGe b i h64 hsize h)).symm

include h64 hsize in
theorem skipWs_toUInt64_eq (i : USize) :
    (skipWs b i).toUInt64 = UInt64.ofNat (skipWsN b.data i.toNat) := by
  rw [toUInt64_eq_ofNat, skipWs_toNat_eq b h64 hsize]

/-! ## `skip_digits` -/

include h64 hsize in
@[refines ConLeche.Frontend.skipDigits]
theorem skipDigits_toNat_eq (i : USize) :
    (skipDigits b i).toNat = skipDigitsN b.data i.toNat := by
  fun_induction skipDigits b i with
  | case1 i h hd ih =>
    have hd' : 48 ≤ b.data[i.toNat]'(usizeInBounds' b i h) ∧
        b.data[i.toNat]'(usizeInBounds' b i h) ≤ 57 := by
      simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq] at hd
      simpa [uget_eq] using hd
    rw [ih, usizeStep b i h]
    exact (skipDigitsN_digit b.data i.toNat (i.toNat + 1) rfl (usizeInBounds' b i h) hd').symm
  | case2 i h hd =>
    have hd' : ¬ (48 ≤ b.data[i.toNat]'(usizeInBounds' b i h) ∧
        b.data[i.toNat]'(usizeInBounds' b i h) ≤ 57) := by
      simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq] at hd
      simpa [uget_eq] using hd
    exact (skipDigitsN_other b.data i.toNat (usizeInBounds' b i h) hd').symm
  | case3 i h =>
    exact (skipDigitsN_end b.data i.toNat (usizeGe b i h64 hsize h)).symm

include h64 hsize in
theorem skipDigits_toUInt64_eq (i : USize) :
    (skipDigits b i).toUInt64 = UInt64.ofNat (skipDigitsN b.data i.toNat) := by
  rw [toUInt64_eq_ofNat, skipDigits_toNat_eq b h64 hsize]

/-! ## `key_end` -/

include h64 hsize in
@[refines ConLeche.Frontend.keyEnd]
theorem keyEnd_toNat_eq (j : USize) : (keyEnd b j).toNat = keyEndN b.data j.toNat := by
  fun_induction keyEnd b j with
  | case1 j h c hc =>
    have hceq : c = b.uget j (usizeInBounds' b j h) := rfl
    have hc' : b.data[j.toNat]'(usizeInBounds' b j h) = 34 := by
      rw [hceq] at hc; simpa [uget_eq] using hc
    exact (keyEndN_quote b.data j.toNat (usizeInBounds' b j h) hc').symm
  | case2 j h c hc hb =>
    have hceq : c = b.uget j (usizeInBounds' b j h) := rfl
    have hc' : b.data[j.toNat]'(usizeInBounds' b j h) ≠ 34 := by
      rw [hceq] at hc; simpa [uget_eq] using hc
    have hb' : b.data[j.toNat]'(usizeInBounds' b j h) < 32 ∨
        b.data[j.toNat]'(usizeInBounds' b j h) = 92 := by
      rw [hceq] at hb
      simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hb
      simpa [uget_eq] using hb
    exact (keyEndN_ctrl b.data j.toNat (usizeInBounds' b j h) hc' hb').symm
  | case3 j h c hc hb ih =>
    have hceq : c = b.uget j (usizeInBounds' b j h) := rfl
    have hc' : b.data[j.toNat]'(usizeInBounds' b j h) ≠ 34 := by
      rw [hceq] at hc; simpa [uget_eq] using hc
    have hb' : ¬ (b.data[j.toNat]'(usizeInBounds' b j h) < 32 ∨
        b.data[j.toNat]'(usizeInBounds' b j h) = 92) := by
      rw [hceq] at hb
      simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hb
      simpa [uget_eq] using hb
    rw [ih, usizeStep b j h]
    exact (keyEndN_other b.data j.toNat (j.toNat + 1) rfl (usizeInBounds' b j h) hc' hb').symm
  | case4 j h =>
    exact (keyEndN_end b.data j.toNat (usizeGe b j h64 hsize h)).symm

include h64 hsize in
theorem keyEnd_toUInt64_eq (j : USize) :
    (keyEnd b j).toUInt64 = UInt64.ofNat (keyEndN b.data j.toNat) := by
  rw [toUInt64_eq_ofNat, keyEnd_toNat_eq b h64 hsize]

/-! ## `num_end`

No loop: a call to `skip_digits` and two comparisons (`L.Scan.Leaves.numEnd_spec` treats it the
same way). -/

include h64 hsize in
@[refines ConLeche.Frontend.numEnd]
theorem numEnd_toNat_eq (i : USize) :
    (ConLeche.Frontend.numEnd b i).toNat = numEndN b.data i.toNat := by
  unfold ConLeche.Frontend.numEnd numEndN
  dsimp only
  simp only [beq_iff_eq, Bool.and_eq_true, bne_iff_ne]
  have hskip := skipDigits_toNat_eq b h64 hsize i
  by_cases h1 : skipDigits b i = i
  · have h1' : skipDigitsN b.data i.toNat = i.toNat := by rw [← hskip, h1]
    rw [ite_eq_left h1, ite_eq_left h1']
  · have h1' : skipDigitsN b.data i.toNat ≠ i.toNat := fun hc => h1 (USize.toNat_inj.mp (hskip.trans hc))
    have hbounds := skipDigitsN_bounds b.data i.toNat h1'
    have hiu : i < b.usize := by rw [USize.lt_iff_toNat_lt, usize_toNat_eq b h64 hsize]; exact hbounds.1
    have hstep := usizeStep b i hiu
    have hgetd : byteAt b i = b.data.getD i.toNat 0 := byteAt_eq_getD b h64 hsize i
    rw [ite_eq_right h1, ite_eq_right h1']
    by_cases hb48 : byteAt b i = 48
    · by_cases he1 : skipDigits b i = i + 1
      · have he1' : skipDigitsN b.data i.toNat = i.toNat + 1 := by rw [← hskip, he1, hstep]
        rw [ite_eq_right (show ¬(byteAt b i = 48 ∧ skipDigits b i ≠ i + 1) by simp [he1]),
            ite_eq_right (show ¬(b.data.getD i.toNat 0 = 48 ∧
              skipDigitsN b.data i.toNat ≠ i.toNat + 1) by simp [he1'])]
        exact hskip
      · have he1' : skipDigitsN b.data i.toNat ≠ i.toNat + 1 := by
          intro hc; exact he1 (USize.toNat_inj.mp (by rw [hskip, hstep]; exact hc))
        rw [ite_eq_left (α := USize) ⟨hb48, he1⟩,
            ite_eq_left (α := Nat) (show b.data.getD i.toNat 0 = 48 ∧
              skipDigitsN b.data i.toNat ≠ i.toNat + 1 by rw [← hgetd]; exact ⟨hb48, he1'⟩)]
    · rw [ite_eq_right (show ¬(byteAt b i = 48 ∧ skipDigits b i ≠ i + 1) by simp [hb48]),
          ite_eq_right (show ¬(b.data.getD i.toNat 0 = 48 ∧
            skipDigitsN b.data i.toNat ≠ i.toNat + 1) by rw [← hgetd]; simp [hb48])]
      exact hskip

include h64 hsize in
theorem numEnd_toUInt64_eq (i : USize) :
    (ConLeche.Frontend.numEnd b i).toUInt64 = UInt64.ofNat (numEndN b.data i.toNat) := by
  rw [toUInt64_eq_ofNat, numEnd_toNat_eq b h64 hsize]

/-! ## `has_escape`

Returns `Bool`; linked by `↔` against the model's `= 1`, since every caller tests the `Bool`
rather than comparing it to `1`. -/

include h64 hsize in
@[refines ConLeche.Frontend.hasEscape]
theorem hasEscape_iff (j e : USize) :
    hasEscape b j e = true ↔ hasEscapeN b.data j.toNat e.toNat = 1 := by
  fun_induction hasEscape b j e with
  | case1 j h hlt hc =>
    have hc' : b.data[j.toNat]'(usizeInBounds' b j h) = 92 := by
      simpa [uget_eq] using (by simpa using hc : (b.uget j (usizeInBounds' b j h) == 92) = true)
    rw [hasEscapeN_hit b.data j.toNat e.toNat (usizeInBounds' b j h) hlt hc']
    simp
  | case2 j h hlt hc ih =>
    have hc' : b.data[j.toNat]'(usizeInBounds' b j h) ≠ 92 := by
      simpa [uget_eq] using (by simpa using hc : ¬ (b.uget j (usizeInBounds' b j h) == 92) = true)
    rw [usizeStep b j h] at ih
    rw [ih, hasEscapeN_miss b.data j.toNat e.toNat (j.toNat + 1) rfl (usizeInBounds' b j h) hlt hc']
  | case3 j h hlt =>
    rw [hasEscapeN_past b.data j.toNat e.toNat (usizeInBounds' b j h) (by
      rw [USize.lt_iff_toNat_lt] at hlt; omega)]
    simp
  | case4 j h =>
    rw [hasEscapeN_end b.data j.toNat e.toNat (usizeGe b j h64 hsize h)]
    simp

/-! ## `newline_from`

Returns `Bool`; linked the same way as `has_escape`. -/

include h64 hsize in
@[refines ConLeche.Frontend.newlineFrom]
theorem newlineFrom_iff (i : USize) :
    newlineFrom b i = true ↔ newlineFromN b.data i.toNat = 1 := by
  fun_induction newlineFrom b i with
  | case1 i h ih =>
    rw [usizeStep b i h] at ih
    by_cases hc : b.data[i.toNat]'(usizeInBounds' b i h) = 10
    · rw [newlineFromN_hit b.data i.toNat (usizeInBounds' b i h) hc]
      have : (b.uget i (usizeInBounds' b i h) == 10) = true := by simpa [uget_eq] using hc
      simp [this]
    · rw [newlineFromN_miss b.data i.toNat (i.toNat + 1) rfl (usizeInBounds' b i h) hc]
      have : ¬ (b.uget i (usizeInBounds' b i h) == 10) = true := by simpa [uget_eq] using hc
      simp [this, ih]
  | case2 i h =>
    rw [newlineFromN_end b.data i.toNat (usizeGe b i h64 hsize h)]
    simp

end ConAgua.Scan
