module

public import ConAgua.L.Semantics

@[expose] public section

/-!
# Byte literals compared eight bytes at a time

`le64 b k` (`le64!(A.u8, k)`) is the little-endian word of the eight bytes at `k`. A literal `l`
of at most eight bytes is the word `litW l`, and `le64 b k &&& mskW l.length = litW l` holds
exactly when the bytes at `k` begin with `l` (`le64_lit`, for a literal without a zero byte: a
read past the end is `0`, so a match lies inside the array). The proof works on `encB`, the
base-256 number of a byte list, so no bit-level reasoning is needed: masking the low `n` bytes is
`% 256 ^ n`, and a base-256 number has one digit list of each length.
-/

namespace L

/-- The base-256 number of a byte list, least significant byte first. -/
def encB : List UInt8 → Nat
  | [] => 0
  | x :: xs => encB xs * 256 + x.toNat

/-- The word of a byte literal (at most eight bytes): what `le64` loads when the bytes match. -/
def litW (l : List UInt8) : Word := UInt64.ofNat (encB l)

/-- The mask of the low `n` bytes. -/
def mskW (n : Nat) : Word := UInt64.ofNat (256 ^ n - 1)

/-- The bytes `l` at position `p` of `b`. -/
structure LitAt (b : Array UInt8) (p : Word) (l : List UInt8) : Prop where
  fits : p.toNat + l.length ≤ b.size
  bytes : (List.range l.length).map (fun j => b[p.toNat + j]!) = l

theorem encB_lt : ∀ l : List UInt8, encB l < 256 ^ l.length
  | [] => by simp [encB]
  | x :: xs => by
    have h := encB_lt xs; have := x.toNat_lt
    simp only [encB, List.length_cons, Nat.pow_succ]
    have : (encB xs + 1) * 256 ≤ 256 ^ xs.length * 256 := Nat.mul_le_mul_right _ h
    rw [Nat.add_mul] at this
    omega

theorem encB_take : ∀ (l : List UInt8) (n : Nat), encB l % 256 ^ n = encB (l.take n)
  | [], n => by simp [encB]
  | x :: xs, 0 => by simp [encB, Nat.mod_one]
  | x :: xs, n + 1 => by
    simp only [encB, List.take_succ_cons, Nat.pow_succ]
    rw [← encB_take xs n]
    have := x.toNat_lt
    have h := Nat.div_add_mod (encB xs) (256 ^ n)
    have hp : 0 < 256 ^ n := Nat.pow_pos (by decide)
    have hm := Nat.mod_lt (encB xs) hp
    generalize encB xs / 256 ^ n = q at h
    generalize encB xs % 256 ^ n = r at h hm ⊢
    rw [← h]
    have : (256 ^ n * q + r) * 256 + x.toNat = (r * 256 + x.toNat) + 256 ^ n * 256 * q := by
      simp only [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm q 256]; omega
    rw [this, Nat.add_mul_mod_self_left]
    apply Nat.mod_eq_of_lt
    have : (r + 1) * 256 ≤ 256 ^ n * 256 := Nat.mul_le_mul_right _ hm
    rw [Nat.add_mul] at this
    omega

theorem encB_inj : ∀ (l l' : List UInt8), l.length = l'.length → encB l = encB l' → l = l'
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hl, h => by
    simp only [encB] at h
    have := x.toNat_lt; have := y.toNat_lt
    have hxy : x.toNat = y.toNat := by omega
    have hr : encB xs = encB ys := by omega
    rw [UInt8.toNat_inj.mp hxy, encB_inj xs ys (by simpa using hl) hr]

/-- `le64` is `encB` of the eight bytes. -/
theorem le64_encB (b : Array UInt8) (k : Nat) :
    le64 b k = UInt64.ofNat (encB ((List.range 8).map fun j => b[k + j]!)) := by
  unfold le64; congr 1

theorem range_map_take (f : Nat → UInt8) (m n : Nat) (h : n ≤ m) :
    ((List.range m).map f).take n = (List.range n).map f := by
  apply List.ext_getElem <;> simp [Nat.min_eq_left h]

theorem pow256 (n : Nat) : (256 : Nat) ^ n = 2 ^ (8 * n) := by
  rw [Nat.pow_mul]

/-- A literal's last byte is inside the array when the bytes there are the literal's and the
literal has no zero byte (a read past the end is `0`). -/
theorem fits_of_bytes (b : Array UInt8) (k : Nat) (l : List UInt8) (hne : l ≠ []) (h0 : 0 ∉ l)
    (h : (List.range l.length).map (fun j => b[k + j]!) = l) : k + l.length ≤ b.size := by
  have hn : 0 < l.length := List.length_pos_iff.mpr hne
  have hj := congrArg (·[l.length - 1]?) h
  simp only [List.getElem?_map, List.getElem?_range (by omega : l.length - 1 < l.length),
    Option.map_some, List.getElem?_eq_getElem (by omega : l.length - 1 < l.length),
    Option.some.injEq] at hj
  by_cases hk : k + (l.length - 1) < b.size
  · omega
  · rw [getElem!_neg b _ hk] at hj
    have hm := List.getElem_mem (l := l) (n := l.length - 1) (by omega)
    rw [← hj] at hm
    exact absurd hm h0

/-- **The literal compare**: the masked word at `p` is the literal's exactly when the bytes there
are the literal (no zero byte, at most eight; a read past the end is `0`, so a match is inside
the array). -/
theorem le64_lit (b : Array UInt8) (p : Word) (l : List UInt8) (hl : l.length ≤ 8)
    (hne : l ≠ []) (h0 : 0 ∉ l) :
    le64 b p.toNat &&& mskW l.length = litW l ↔ LitAt b p l := by
  have hpow : 256 ^ l.length ≤ 256 ^ 8 := Nat.pow_le_pow_right (by decide) hl
  have h64 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  have hs : UInt64.size = 2 ^ 64 := rfl
  have hE := encB_lt ((List.range 8).map fun j => b[p.toNat + j]!)
  have hL := encB_lt l
  simp only [List.length_map, List.length_range] at hE
  have hm : (mskW l.length).toNat = 2 ^ (8 * l.length) - 1 := by
    rw [mskW, UInt64.toNat_ofNat_of_lt' (by omega), pow256]
  rw [le64_encB, ← UInt64.toNat_inj, UInt64.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod,
    UInt64.toNat_ofNat_of_lt' (by omega), litW, UInt64.toNat_ofNat_of_lt' (by omega), ← pow256,
    encB_take, range_map_take _ _ _ hl]
  constructor
  · intro h
    have hb := encB_inj _ _ (by simp) h
    exact ⟨fits_of_bytes b p.toNat l hne h0 hb, hb⟩
  · intro h; rw [h.bytes]

/-- The same for a literal of eight bytes, compared without a mask. -/
theorem le64_lit8 (b : Array UInt8) (p : Word) (l : List UInt8) (hl : l.length = 8)
    (hne : l ≠ []) (h0 : 0 ∉ l) : le64 b p.toNat = litW l ↔ LitAt b p l := by
  rw [← le64_lit b p l (by omega) hne h0, hl]
  have hk : le64 b p.toNat &&& mskW 8 = le64 b p.toNat := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_and, show (mskW 8).toNat = 2 ^ 64 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)
  rw [hk]

/-- A byte of a literal. -/
theorem LitAt.get {b : Array UInt8} {p : Word} {l : List UInt8} (h : LitAt b p l) (j : Nat)
    (hj : j < l.length) : b[p.toNat + j]! = l[j] := by
  have := congrArg (·[j]?) h.bytes
  simp [hj] at this
  exact this

end L
