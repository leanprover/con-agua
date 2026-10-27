module

public import ConAgua.L.Examples
public import ConLeche.Frontend.Scan.Fast
import ConAgua.Census.Attr
public import ConLeche.Frontend.Scan.Equiv.Scalars
@[expose] public section

/-!
# Linking the Nat-position models to con-leche's `USize`-position originals

`L.Examples.strCloseN`/`skipBracedN` are con-leche's `ConLeche.Frontend.strClose`/`skipBraced`
with `Nat` positions over `Array UInt8` in place of `USize` positions over `ByteArray`. This file
proves the two agree, so that the `vcgen` spec against `strCloseN`/`skipBracedN`
(`L.Examples.strClose_spec`/`skipBraced_spec`) composes into a spec against the real con-leche
functions.

The proof mirrors `ConLeche.Frontend.strClose_eq`/`skipBraced_eq`
(`vendor/con-leche/ConLeche/Frontend/Scan/Equiv/{Scalars,Keys}.lean`): the same `fun_induction`,
the same case split (con-leche's cases line up with `strCloseN`'s/`skipBracedN`'s arms one for
one, since the model was written to match these functions directly), with con-leche's
`naiveStrBody`/`naiveSkipBraced` and `tailAt`'s list positions replaced by `strCloseN`/
`skipBracedN` and `Nat` positions via `uget`/`.toNat`.

`System.Platform.numBits = 64` (equivalently `USize.size = 2 ^ 64`) and `b.size < 2 ^ 64` are
needed only for the one place a `USize` position can run past the array without this: `ByteArray`
has no upper bound on `.size`, so `¬ i < b.usize` only gives `b.size ≤ i.toNat` once `b.usize.toNat`
is known to equal `b.size` outright, rather than `b.size % USize.size` (`usizeGe`). Every other
step (`usizeInBounds`, `usizeStep`, both imported from `ConLeche.Frontend.Scan.Fast`) holds on any
platform: a position inside the array never overflows regardless of the word width.
-/

namespace ConAgua.Scan

open ConLeche.Frontend L.Examples

/-! ## The bounds kit, lifted to `Array UInt8`/`Nat` -/

theorem usizeInBounds' (b : ByteArray) (i : USize) (h : i < b.usize) : i.toNat < b.data.size :=
  usizeInBounds b i h

/-- `b.usize.toNat` is `b.size % USize.size`, which is `b.size` itself once `b.size < 2 ^ 64`
and `USize.size = 2 ^ 64` (the platform hypothesis, task's "Link" step). -/
theorem usize_toNat_eq (b : ByteArray) (h64 : System.Platform.numBits = 64)
    (hsize : b.size < 2 ^ 64) : b.usize.toNat = b.size := by
  simp only [ByteArray.usize, USize.toNat_ofNat']
  rw [h64]; omega

theorem usizeGe (b : ByteArray) (i : USize) (h64 : System.Platform.numBits = 64)
    (hsize : b.size < 2 ^ 64) (h : ¬ i < b.usize) : b.data.size ≤ i.toNat := by
  have h' : ¬ i.toNat < b.usize.toNat := fun hc => h (USize.lt_iff_toNat_lt.mpr hc)
  rw [usize_toNat_eq b h64 hsize] at h'
  have : b.data.size = b.size := rfl
  omega

/-- `b.uget i h` is `b.data[i.toNat]`, so a boolean comparison against it is a comparison of the
model's `Array UInt8` access. -/
theorem uget_eq (b : ByteArray) (i : USize) (h : i.toNat < b.data.size) :
    b.uget i (by simpa using h) = b.data[i.toNat]'h := rfl

theorem usize_size_eq64 (h64 : System.Platform.numBits = 64) : USize.size = 2 ^ 64 := by
  unfold USize.size; rw [h64]

/-! ## `str_close` -/

section strClose
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 64)

include h64 hsize in
@[refines ConLeche.Frontend.strClose]
theorem strClose_toNat_eq (j : USize) :
    (strClose b j).toNat = strCloseN b.data j.toNat := by
  fun_induction strClose b j with
  | case1 j h c hc =>
    have hc' : b.data[j.toNat]'(usizeInBounds' b j h) = 34 := by
      have h2 : (b.uget j (usizeInBounds' b j h) == 34) = true := hc
      simpa [uget_eq] using h2
    rw [strCloseN_quote b.data j.toNat (usizeInBounds' b j h) hc']
  | case2 j h c hc hbEsc h2 hd =>
    have hbEsc' : b.data[j.toNat]'(usizeInBounds' b j h) = 92 := by
      have h2' : (b.uget j (usizeInBounds' b j h) == 92) = true := hbEsc
      simpa [uget_eq] using h2'
    have hstep := usizeStep b j h
    have hd' : b.data[(j + 1).toNat]'(usizeInBounds' b (j + 1) h2) < 32 := by
      have h2' : b.uget (j + 1) (usizeInBounds' b (j + 1) h2) < 32 := hd
      simpa [uget_eq] using h2'
    rw [show (0 : USize).toNat = 0 from rfl,
      strCloseN_esc_ctrl b.data j.toNat (j + 1).toNat hstep (usizeInBounds' b (j + 1) h2)
        hbEsc' hd']
  | case3 j h c hc hbEsc h2 hd ih =>
    have hbEsc' : b.data[j.toNat]'(usizeInBounds' b j h) = 92 := by
      have h2' : (b.uget j (usizeInBounds' b j h) == 92) = true := hbEsc
      simpa [uget_eq] using h2'
    have hstep := usizeStep b j h
    have hstep2 := usizeStep b (j + 1) h2
    have hd' : ¬ b.data[(j + 1).toNat]'(usizeInBounds' b (j + 1) h2) < 32 := by
      have h2' : ¬ b.uget (j + 1) (usizeInBounds' b (j + 1) h2) < 32 := hd
      simpa [uget_eq] using h2'
    have hkk : (j + 1 + 1).toNat = j.toNat + 2 := by omega
    rw [ih, hkk]
    exact (strCloseN_esc b.data j.toNat (j + 1).toNat (j.toNat + 2) hstep rfl
      (usizeInBounds' b (j + 1) h2) hbEsc' hd').symm
  | case4 j h c hc hbEsc h2 =>
    have hbEsc' : b.data[j.toNat]'(usizeInBounds' b j h) = 92 := by
      have h2' : (b.uget j (usizeInBounds' b j h) == 92) = true := hbEsc
      simpa [uget_eq] using h2'
    have hstep := usizeStep b j h
    have hend : b.data.size ≤ (j + 1).toNat := usizeGe b (j + 1) h64 hsize h2
    rw [show (0 : USize).toNat = 0 from rfl]
    exact (strCloseN_esc_end b.data j.toNat (usizeInBounds' b j h) hbEsc' (by omega)).symm
  | case5 j h c hc hbEsc hlt =>
    have hc' : b.data[j.toNat]'(usizeInBounds' b j h) ≠ 34 := by
      have h2' : ¬ (b.uget j (usizeInBounds' b j h) == 34) = true := hc
      simpa [uget_eq] using h2'
    have hb' : b.data[j.toNat]'(usizeInBounds' b j h) ≠ 92 := by
      have h2' : ¬ (b.uget j (usizeInBounds' b j h) == 92) = true := hbEsc
      simpa [uget_eq] using h2'
    have hlt' : b.data[j.toNat]'(usizeInBounds' b j h) < 32 := hlt
    rw [show (0 : USize).toNat = 0 from rfl]
    exact (strCloseN_ctrl b.data j.toNat (usizeInBounds' b j h) hc' hb' hlt').symm
  | case6 j h c hc hbEsc hlt ih =>
    have hc' : b.data[j.toNat]'(usizeInBounds' b j h) ≠ 34 := by
      have h2' : ¬ (b.uget j (usizeInBounds' b j h) == 34) = true := hc
      simpa [uget_eq] using h2'
    have hb' : b.data[j.toNat]'(usizeInBounds' b j h) ≠ 92 := by
      have h2' : ¬ (b.uget j (usizeInBounds' b j h) == 92) = true := hbEsc
      simpa [uget_eq] using h2'
    have hlt' : ¬ b.data[j.toNat]'(usizeInBounds' b j h) < 32 := hlt
    have hstep := usizeStep b j h
    rw [ih, hstep]
    exact (strCloseN_other b.data j.toNat (j.toNat + 1) rfl (usizeInBounds' b j h) hc' hb'
      hlt').symm
  | case7 j h =>
    rw [show (0 : USize).toNat = 0 from rfl]
    exact (strCloseN_end b.data j.toNat (usizeGe b j h64 hsize h)).symm

end strClose

/-! ## `skip_braced` -/

section skipBraced
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 64)



include h64 hsize in
@[refines ConLeche.Frontend.skipBraced]
theorem skipBraced_toNat_eq (i : USize) (depth : Nat) :
    (skipBraced b i depth).toNat = skipBracedN b.data i.toNat depth := by
  fun_induction skipBraced b i depth with
  | case1 i depth h c h34 e he =>
    have h34' : b.data[i.toNat]'(usizeInBounds' b i h) = 34 := by
      have h2 : (b.uget i (usizeInBounds' b i h) == 34) = true := h34
      simpa [uget_eq] using h2
    have he' : strClose b (i + 1) = 0 := by
      have h2 : (strClose b (i + 1) == 0) = true := he
      simpa using h2
    have hez : strCloseN b.data (i + 1).toNat = 0 := by
      have hlink := strClose_toNat_eq b h64 hsize (i + 1)
      rw [he'] at hlink; simpa using hlink.symm
    rw [show (0 : USize).toNat = 0 from rfl]
    exact (skipBracedN_str0 b.data i.toNat depth (i + 1).toNat (usizeStep b i h)
      (usizeInBounds' b i h) h34' hez).symm
  | case2 i depth h c h34 e he hlt ih =>
    have he_eq : e = strClose b (i + 1) := rfl
    simp only [he_eq] at hlt ih
    have h34' : b.data[i.toNat]'(usizeInBounds' b i h) = 34 := by
      have h2 : (b.uget i (usizeInBounds' b i h) == 34) = true := h34
      simpa [uget_eq] using h2
    have he' : strClose b (i + 1) ≠ 0 := by
      have h2 : ¬ (strClose b (i + 1) == 0) = true := he
      simpa using h2
    have hlink := strClose_toNat_eq b h64 hsize (i + 1)
    have heNat : strCloseN b.data (i + 1).toNat ≠ 0 := by
      intro hc0; apply he'; apply USize.toNat.inj; rw [hlink, hc0]; rfl
    have hbound := strCloseN_bounds b.data (i + 1).toNat heNat
    have hbd : b.data.size = b.size := rfl
    have hUsz := usize_size_eq64 h64
    have hstepE : (strClose b (i + 1) + 1).toNat = (strClose b (i + 1)).toNat + 1 :=
      usize_step_of_lt (by omega)
    have hstepI := usizeStep b i h
    rw [ih]
    exact (skipBracedN_str b.data i.toNat depth (i + 1).toNat (strClose b (i + 1) + 1).toNat
      hstepI (by omega) (usizeInBounds' b i h) h34' heNat).symm
  | case3 i depth h c h34 e he hlt =>
    exfalso
    have he_eq : e = strClose b (i + 1) := rfl
    simp only [he_eq] at hlt
    have he' : strClose b (i + 1) ≠ 0 := by
      have h2 : ¬ (strClose b (i + 1) == 0) = true := he
      simpa using h2
    have hlink := strClose_toNat_eq b h64 hsize (i + 1)
    have heNat : strCloseN b.data (i + 1).toNat ≠ 0 := by
      intro hc0; apply he'; apply USize.toNat.inj; rw [hlink, hc0]; rfl
    have hbound := strCloseN_bounds b.data (i + 1).toNat heNat
    have hbd : b.data.size = b.size := rfl
    have hUsz := usize_size_eq64 h64
    have hstepE : (strClose b (i + 1) + 1).toNat = (strClose b (i + 1)).toNat + 1 :=
      usize_step_of_lt (by omega)
    have hstepI := usizeStep b i h
    exact hlt (USize.lt_iff_toNat_lt.mpr (by omega))
  | case4 i depth h c h34 hnl =>
    have hnl' : b.data[i.toNat]'(usizeInBounds' b i h) = 10 := by
      have h2 : (b.uget i (usizeInBounds' b i h) == 10) = true := hnl
      simpa [uget_eq] using h2
    rw [show (0 : USize).toNat = 0 from rfl]
    exact (skipBracedN_nl b.data i.toNat depth (usizeInBounds' b i h) hnl').symm
  | case5 i depth h c h34 hnl hbr ih =>
    have hbr' : b.data[i.toNat]'(usizeInBounds' b i h) = 123
        ∨ b.data[i.toNat]'(usizeInBounds' b i h) = 91 := by
      have h2 : (b.uget i (usizeInBounds' b i h) == 123 || b.uget i (usizeInBounds' b i h) == 91)
          = true := hbr
      simpa [uget_eq, Bool.or_eq_true] using h2
    have hstep := usizeStep b i h
    rw [ih, hstep]
    exact (skipBracedN_open b.data i.toNat depth (i.toNat + 1) (depth + 1) rfl rfl
      (usizeInBounds' b i h) hbr').symm
  | case6 i h c h34 hnl hbr hcl =>
    have hcl' : b.data[i.toNat]'(usizeInBounds' b i h) = 125
        ∨ b.data[i.toNat]'(usizeInBounds' b i h) = 93 := by
      have h2 : (b.uget i (usizeInBounds' b i h) == 125 || b.uget i (usizeInBounds' b i h) == 93)
          = true := hcl
      simpa [uget_eq, Bool.or_eq_true] using h2
    have hstep := usizeStep b i h
    rw [hstep]
    exact (skipBracedN_close0 b.data i.toNat (usizeInBounds' b i h) hcl').symm
  | case7 i h c h34 hnl hbr hcl d ih =>
    have hcl' : b.data[i.toNat]'(usizeInBounds' b i h) = 125
        ∨ b.data[i.toNat]'(usizeInBounds' b i h) = 93 := by
      have h2 : (b.uget i (usizeInBounds' b i h) == 125 || b.uget i (usizeInBounds' b i h) == 93)
          = true := hcl
      simpa [uget_eq, Bool.or_eq_true] using h2
    have hstep := usizeStep b i h
    rw [ih, hstep]
    exact (skipBracedN_close b.data i.toNat (d + 1) (i.toNat + 1) d rfl rfl
      (usizeInBounds' b i h) hcl').symm
  | case8 i depth h c h34 hnl hbr hcl ih =>
    have h34' : b.data[i.toNat]'(usizeInBounds' b i h) ≠ 34 := by
      have h2 : ¬ (b.uget i (usizeInBounds' b i h) == 34) = true := h34
      simpa [uget_eq] using h2
    have hnl' : b.data[i.toNat]'(usizeInBounds' b i h) ≠ 10 := by
      have h2 : ¬ (b.uget i (usizeInBounds' b i h) == 10) = true := hnl
      simpa [uget_eq] using h2
    have hbr' : ¬ (b.data[i.toNat]'(usizeInBounds' b i h) = 123
        ∨ b.data[i.toNat]'(usizeInBounds' b i h) = 91) := by
      have h2 : ¬ (b.uget i (usizeInBounds' b i h) == 123 || b.uget i (usizeInBounds' b i h) == 91)
          = true := hbr
      simpa [uget_eq, Bool.or_eq_true] using h2
    have hcl' : ¬ (b.data[i.toNat]'(usizeInBounds' b i h) = 125
        ∨ b.data[i.toNat]'(usizeInBounds' b i h) = 93) := by
      have h2 : ¬ (b.uget i (usizeInBounds' b i h) == 125 || b.uget i (usizeInBounds' b i h) == 93)
          = true := hcl
      simpa [uget_eq, Bool.or_eq_true] using h2
    have hstep := usizeStep b i h
    rw [ih, hstep]
    exact (skipBracedN_other b.data i.toNat depth (i.toNat + 1) rfl (usizeInBounds' b i h)
      h34' hnl' (fun hx => hbr' (Or.inl hx)) (fun hx => hbr' (Or.inr hx))
      (fun hx => hcl' (Or.inl hx)) (fun hx => hcl' (Or.inr hx))).symm
  | case9 i depth h =>
    rw [show (0 : USize).toNat = 0 from rfl]
    exact (skipBracedN_end b.data i.toNat depth (usizeGe b i h64 hsize h)).symm

end skipBraced

end ConAgua.Scan

