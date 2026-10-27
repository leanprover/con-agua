module

public import ConAgua.Scan.Utf8
public import ConLeche.Frontend.Scan.Fast
public import ConAgua.Scan.Link
@[expose] public section

/-!
# The `USize → UInt64` kit

con-leche reads with `USize` positions; the Stage B models (`ConAgua.Scan.Leaves`,
`ConAgua.Scan.Key`, `ConAgua.Scan.Values`) compute with WORDS (`UInt64`), the type L's `Word`
abbreviates. Under `System.Platform.numBits = 64` (`h64`, i.e. `USize.size = 2 ^ 64`), `.toUInt64`
is an order- and ring-isomorphism `USize ≃ UInt64` — both have the same number of bits, so
`.toUInt64` is a bijection, and every one of `+`, `-`, numerals, `<`, `=` transports along it
(`USize.toNat_toUInt64 : x.toUInt64.toNat = x.toNat` is the one fact every proof below reduces
to, chasing both sides down to their `.toNat` and closing with `UInt64.toNat_add`/`toNat_sub`/
`toNat_ofNat` against `USize`'s own, under `h64` to match up the two moduli `2 ^ numBits` and
`2 ^ 64`).

`usize_toUInt64_eq`/`byteAt_toUInt64_eq` additionally need `hsize : b.size < 2 ^ 64`, exactly as
`ConAgua.Scan.Link`'s `usize_toNat_eq`/`usizeGe` do (and are proved from them): `ByteArray` has no
upper bound on `.size`, so without `hsize` a position past a huge array could wrap `b.usize`
itself.

`okW` reads the position out of a `ScanRes`, as a word, `0` for `.err` (never a valid position:
every scanner here starts past the opening delimiter it has already checked).
-/

namespace ConAgua.Scan

open ConLeche.Frontend
open L (Word)
open L.Scan.Utf8 (byteW)

/-! ## Transport along `.toUInt64` -/

/-- `.toUInt64` is a widening (`USize.size ≤ UInt64.size` on every platform): a `USize` value is
its own `.toNat` as a word, with no `h64` needed. The leaf links use this to turn a `.toNat`
equality against a model into a `.toUInt64` one. -/
theorem toUInt64_eq_ofNat (x : USize) : x.toUInt64 = UInt64.ofNat x.toNat := by
  apply UInt64.toNat_inj.mp
  rw [USize.toNat_toUInt64,
    UInt64.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le x.toNat_lt_size USize.size_le_uint64Size)]

theorem add_toUInt64 (h64 : System.Platform.numBits = 64) (a b : USize) :
    (a + b).toUInt64 = a.toUInt64 + b.toUInt64 := by
  apply UInt64.toNat_inj.mp
  simp only [USize.toNat_toUInt64, USize.toNat_add, UInt64.toNat_add]
  rw [h64]

theorem sub_toUInt64 (h64 : System.Platform.numBits = 64) (a b : USize) :
    (a - b).toUInt64 = a.toUInt64 - b.toUInt64 := by
  apply UInt64.toNat_inj.mp
  simp only [USize.toNat_toUInt64, USize.toNat_sub, UInt64.toNat_sub]
  rw [h64]

/-- Any numeral transports: `(97 : USize).toUInt64 = (97 : Word)`, `(2 : USize).toUInt64 =
(2 : Word)`, etc. -/
theorem ofNat_toUInt64 (h64 : System.Platform.numBits = 64) (n : Nat) :
    (OfNat.ofNat n : USize).toUInt64 = (OfNat.ofNat n : UInt64) := by
  apply UInt64.toNat_inj.mp
  rw [USize.toNat_toUInt64]
  simp only [USize.toNat_ofNat, UInt64.toNat_ofNat]
  rw [h64]

theorem lt_toUInt64_iff (a b : USize) : a < b ↔ a.toUInt64 < b.toUInt64 := by
  rw [USize.lt_iff_toNat_lt, UInt64.lt_iff_toNat_lt]
  simp [USize.toNat_toUInt64]

theorem eq_toUInt64_iff (a b : USize) : a = b ↔ a.toUInt64 = b.toUInt64 := by
  rw [← USize.toNat_inj, ← UInt64.toNat_inj]
  simp [USize.toNat_toUInt64]

/-! ## The array -/

/-- `b.usize` as a word is `b.size` itself (`usize_toNat_eq`, lifted along `.toUInt64`). -/
theorem usize_toUInt64_eq (b : ByteArray) (h64 : System.Platform.numBits = 64)
    (hsize : b.size < 2 ^ 64) : b.usize.toUInt64 = UInt64.ofNat b.size := by
  apply UInt64.toNat_inj.mp
  rw [USize.toNat_toUInt64, usize_toNat_eq b h64 hsize, UInt64.toNat_ofNat_of_lt' hsize]

/-- con-leche's `byteAt`, as a word, is the model's `byteW`: both are the byte at the position,
`0` past the end. -/
theorem byteAt_toUInt64_eq (b : ByteArray) (i : USize) (h64 : System.Platform.numBits = 64)
    (hsize : b.size < 2 ^ 64) : (byteAt b i).toUInt64 = byteW b.data i.toUInt64 := by
  unfold byteAt byteW
  have hbd : b.data.size = b.size := rfl
  split
  · next h =>
    rw [uget_eq b i (usizeInBounds' b i h)]
    have hlt : i.toNat < b.size := by rw [← hbd]; exact usizeInBounds' b i h
    simp [Array.getD, USize.toNat_toUInt64, hlt]
  · next h =>
    have hge := usizeGe b i h64 hsize h
    have hnlt : ¬ i.toNat < b.size := by omega
    simp [Array.getD, USize.toNat_toUInt64, hnlt]

/-! ## Scanner results -/

/-- The position a `ScanRes` carries, as a word; `0` for `.err` (never a position a scanner here
returns on success: every one of them starts past a delimiter it has already matched). -/
def okW {α : Type} : ScanRes α → Word
  | .ok _ p => p.toUInt64
  | .err _ => 0

end ConAgua.Scan
