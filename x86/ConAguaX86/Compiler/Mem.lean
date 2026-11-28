module

public import Kraken.Mem
import all Kraken.Mem

@[expose] public section

/-!
# Words and bytes in Kraken's data memory

The compiler proof speaks about memory only through `rdW` (an 8-byte little-endian word) and
`get?` (a byte), at addresses `A x` for a natural number `x < 2^64`. Disjointness of two accesses
is then arithmetic on natural numbers.
-/

namespace L.Compiler

/-- The address of a natural number. -/
abbrev A (x : Nat) : BitVec 64 := BitVec.ofNat 64 x

/-- The word at `a`, as the machine's 8-byte load reads it. -/
def rdW (d : Mem 64) (a : BitVec 64) : Option UInt64 :=
  (Mem.loadInt d a 8).map fun i => UInt64.ofBitVec (BitVec.ofInt 64 i)

/-- The machine's 8-byte store of `v` at `a`. -/
def wrW (d : Mem 64) (a : BitVec 64) (v : BitVec 64) : Mem 64 := Mem.storeInt d a 8 v.toInt

theorem A_add (x j : Nat) : A x + BitVec.ofNat 64 j = A (x + j) := by
  simp [A, BitVec.ofNat_add]

theorem A_inj {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (h : A x = A y) : x = y := by
  have := congrArg BitVec.toNat h
  simpa [A, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using this

theorem A_ne {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (h : x ≠ y) : A x ≠ A y :=
  fun e => h (A_inj hx hy e)

theorem rdW_wrW_same (d : Mem 64) (a : BitVec 64) (v : BitVec 64) :
    rdW (wrW d a v) a = some (UInt64.ofBitVec v) := by
  simp only [rdW, wrW, Mem.loadInt_storeInt d a 8 _ (by decide), Option.map_some,
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl]

/-- A load reads only its eight bytes. -/
theorem rdW_congr {d d' : Mem 64} {a : BitVec 64}
    (h : ∀ j < 8, d'.get? (a + BitVec.ofNat 64 j) = d.get? (a + BitVec.ofNat 64 j)) :
    rdW d' a = rdW d a := by
  simp only [rdW, Mem.loadInt_congr h]

theorem get?_wrW_of_ne {d : Mem 64} {a b : BitVec 64} {v : BitVec 64}
    (h : ∀ j < 8, b ≠ a + BitVec.ofNat 64 j) : (wrW d a v).get? b = d.get? b :=
  Mem.get?_storeInt_of_ne d a b 8 _ h

/-- A byte outside a word store at `A x` keeps its value. -/
theorem get?_wrW_A {d : Mem 64} {x y : Nat} {v : BitVec 64} (hx : x + 8 ≤ 2 ^ 64) (hy : y < 2 ^ 64)
    (h : y < x ∨ x + 8 ≤ y) : (wrW d (A x) v).get? (A y) = d.get? (A y) :=
  get?_wrW_of_ne fun j hj => by
    rw [A_add]; exact A_ne hy (by omega) (by omega)

theorem get?_store1_A {d : Mem 64} {x y : Nat} {v : Int} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64)
    (h : y ≠ x) : (Mem.storeInt d (A x) 1 v).get? (A y) = d.get? (A y) :=
  Mem.get?_storeInt_of_ne d _ _ 1 v fun j hj => by
    rw [A_add]; exact A_ne hy (by omega) (by omega)

/-- A word store at `A x` leaves the word at `A y` alone when the two do not overlap. -/
theorem rdW_wrW_A {d : Mem 64} {x y : Nat} {v : BitVec 64} (hx : x + 8 ≤ 2 ^ 64) (hy : y + 8 ≤ 2 ^ 64)
    (h : y + 8 ≤ x ∨ x + 8 ≤ y) : rdW (wrW d (A x) v) (A y) = rdW d (A y) :=
  rdW_congr fun j hj => by
    rw [A_add]; exact get?_wrW_A hx (by omega) (by omega)

/-- The keys of a memory only grow under a store. -/
theorem isSome_get?_storeBytes {d : Mem 64} {a b : BitVec 64} {bs : List UInt8}
    (h : (d.get? b).isSome) : ((Mem.storeBytes d a bs).get? b).isSome := by
  simp only [Mem.storeBytes, Std.ExtHashMap.get?_eq_getElem?] at h ⊢
  rw [Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union]
  cases h' : (bs.At a)[b]? <;> simp_all

theorem isSome_get?_storeInt {d : Mem 64} {a b : BitVec 64} {n : Nat} {v : Int}
    (h : (d.get? b).isSome) : ((Mem.storeInt d a n v).get? b).isSome :=
  isSome_get?_storeBytes h

/-- A load succeeds when its bytes are mapped. -/
theorem isSome_loadInt {d : Mem 64} {a : BitVec 64} {n : Nat}
    (h : ∀ j < n, (d.get? (a + BitVec.ofNat 64 j)).isSome) : (Mem.loadInt d a n).isSome := by
  simp only [Mem.loadInt, Mem.loadBytes, Option.isSome_map]
  suffices ∀ (l : List Nat), (∀ j ∈ l, j < n) →
      (List.allSome (l.map fun i => d.get? (a + BitVec.ofNat 64 i))).isSome by
    exact this _ fun j hj => List.mem_range.mp hj
  intro l hl
  induction l with
  | nil => rfl
  | cons j l ih =>
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h j (hl j (List.mem_cons_self ..)))
    obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp (ih fun j hj => hl j (List.mem_cons_of_mem _ hj))
    simp only [List.allSome, List.map_cons, List.mapM_cons, id, hb] at hbs ⊢
    simp at hbs ⊢
    simp [hbs]

theorem isSome_rdW {d : Mem 64} {a : BitVec 64}
    (h : ∀ j < 8, (d.get? (a + BitVec.ofNat 64 j)).isSome) : (rdW d a).isSome := by
  simpa [rdW] using isSome_loadInt h

/-- A one-byte load. -/
theorem loadInt_one_of {d : Mem 64} {a : BitVec 64} {b : UInt8} (h : d.get? a = some b) :
    Mem.loadInt d a 1 = some (b.toNat : Int) := by
  rw [Mem.loadInt_one, h]; rfl

theorem int_ofBytes_nat (l : List UInt8) :
    Int.ofBytes l = ((l.foldr (fun x acc => acc * 256 + x.toNat) 0 : Nat) : Int) := by
  induction l with
  | nil => rfl
  | cons b l ih => rw [Int.ofBytes_cons, ih]; simp

theorem foldr_bytes_lt (l : List UInt8) : l.foldr (fun x acc => acc * 256 + x.toNat) 0 < 256 ^ l.length := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldr_cons, List.length_cons, Nat.pow_succ]
    have := b.toNat_lt; omega

/-- **An 8-byte load reads the little-endian word of its bytes** (lane blkcopy: `L.le64`). -/
theorem rdW_bytes {d : Mem 64} {X : Nat} {b : Array UInt8} {k : Nat}
    (h : ∀ j < 8, d.get? (A (X + j)) = some b[k + j]!) :
    rdW d (A X) = some (UInt64.ofNat (((List.range 8).map fun j => b[k + j]!).foldr
      (fun x acc => acc * 256 + x.toNat) 0)) := by
  unfold rdW Mem.loadInt Mem.loadBytes
  have e : (List.range 8).map (fun i => d.get? (A X + BitVec.ofNat 64 i)) =
      ((List.range 8).map fun j => b[k + j]!).map some := by
    rw [List.map_map]
    exact List.map_congr_left fun j hj => by rw [A_add]; exact h j (List.mem_range.mp hj)
  rw [e]
  have hs : List.allSome (((List.range 8).map fun j => b[k + j]!).map some) =
      some ((List.range 8).map fun j => b[k + j]!) := by
    simp only [List.allSome]
    induction ((List.range 8).map fun j => b[k + j]!) with
    | nil => rfl
    | cons x l ih => simp [List.mapM_cons, ih]
  rw [hs]
  simp only [Option.map_some, Option.some.injEq, int_ofBytes_nat]
  have hl := foldr_bytes_lt ((List.range 8).map fun j => b[k + j]!)
  simp only [List.length_map, List.length_range] at hl
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_ofBitVec, BitVec.toNat_ofInt]
  norm_cast


end L.Compiler
