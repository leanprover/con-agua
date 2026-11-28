module

public import ConAguaX86.Compiler.Mem
public import ConAgua.L.Semantics
import all Kraken.Mem

@[expose] public section

/-!
# 32-bit accesses to a word in Kraken's data memory (lane p32)

L's 32-bit elements (`L.ld32`, `L.st32`) are the halves of its words: element `i` of a word array
is half `i % 2` of word `i / 2`. The compiled code reads and writes them with 4-byte moves at byte
`4 i` of the array. On the machine's little-endian memory, the 4 bytes at `X + 4 h` of the word at
`X` are its half `h` (`load32_of_rdW`), and a 4-byte store there leaves the memory that an 8-byte
store of the word with that half replaced leaves (`store32_eq`): the simulation proofs then treat a
32-bit store as the word store `L.Mem.set32` is.
-/

namespace L.Compiler

open L

/-- Byte `i` of `Int.toBytes n v`. -/
theorem toBytes_getElem (n : Nat) (v : Int) (i : Nat) (hi : i < n) :
    (Int.toBytes n v)[i]'(by rw [Int.toBytes_length]; exact hi) = ((v / 256 ^ i) % 256).toNat.toUInt8 := by
  induction n generalizing v i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => simp [Int.toBytes, Int.take]
    | succ i =>
      simp only [Int.toBytes, List.getElem_cons_succ]
      rw [ih (v / 256) i (by omega), Int.ediv_ediv_of_nonneg (by decide), Int.pow_succ']

/-- A byte inside a store. -/
theorem get?_storeBytes_in {d : _root_.Mem 64} {x : Nat} {bs : List UInt8} {i : Nat}
    (hx : x + bs.length ≤ 2 ^ 64) (hi : i < bs.length) :
    (_root_.Mem.storeBytes d (A x) bs).get? (A (x + i)) = some bs[i] := by
  rw [Mem.storeBytes, Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.union_eq,
    Std.ExtHashMap.getElem?_union, ← Std.ExtHashMap.get?_eq_getElem?, ← A_add,
    get?_At_idx bs _ i (by omega) (by omega), List.getElem?_eq_getElem hi]
  rfl

/-- The bytes of a word that `rdW` reads. -/
theorem rdW_get? {d : _root_.Mem 64} {X : Nat} {w : Word} (h : rdW d (A X) = some w)
    (j : Nat) (hj : j < 8) : d.get? (A (X + j)) = some (UInt8.ofNat (w.toNat / 256 ^ j)) := by
  simp only [rdW, _root_.Mem.loadInt, _root_.Mem.loadBytes, Option.map_map, Option.map_eq_some_iff] at h
  obtain ⟨bs, hbs, hw⟩ := h
  have hl := List.allSome_eq_map_some hbs
  have hlen : bs.length = 8 := by simpa using (congrArg List.length hl).symm
  have hget : ∀ j < 8, d.get? (A (X + j)) = some bs[j]! := by
    intro j hj
    have := congrArg (·[j]?) hl
    simp only [List.getElem?_map, List.getElem?_range hj, Option.map_some] at this
    rw [List.getElem?_eq_getElem (show j < bs.length by omega)] at this
    rw [← A_add, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (show j < bs.length by omega)]; simpa using this
  rw [hget j hj]
  congr 1
  match bs, hlen with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ =>
    subst hw
    simp only [Function.comp, int_ofBytes_nat, List.foldr_cons, List.foldr_nil]
    have := b0.toNat_lt; have := b1.toNat_lt; have := b2.toNat_lt; have := b3.toNat_lt
    have := b4.toNat_lt; have := b5.toNat_lt; have := b6.toNat_lt; have := b7.toNat_lt
    apply UInt8.toNat_inj.mp
    simp only [UInt64.toNat_ofBitVec, BitVec.toNat_ofInt]
    obtain _|_|_|_|_|_|_|_|j := j <;> simp <;> omega


/-- **A 4-byte load reads a half of the word** (little-endian): at byte `X + 4 (i % 2)` of the
word at `X`, half `i % 2` (`L.half32`). -/
theorem load32_of_rdW {d : _root_.Mem 64} {X : Nat} {w : Word} (h : rdW d (A X) = some w) (i : Word) :
    _root_.Mem.loadInt d (A (X + 4 * (i.toNat % 2))) 4 = some ((half32 w i).toNat : Int) := by
  have hb := fun j hj => rdW_get? (X := X) h j hj
  have hl : (List.range 4).map (fun j => d.get? (A (X + 4 * (i.toNat % 2)) + BitVec.ofNat 64 j)) =
      ((List.range 4).map fun j => UInt8.ofNat (w.toNat / 256 ^ (4 * (i.toNat % 2) + j))).map some := by
    rw [List.map_map]
    refine List.map_congr_left fun j hj => ?_
    have := List.mem_range.mp hj
    rw [A_add, show X + 4 * (i.toNat % 2) + j = X + (4 * (i.toNat % 2) + j) by omega, hb _ (by omega)]
    rfl
  simp only [_root_.Mem.loadInt, _root_.Mem.loadBytes, hl, List.allSome_map_some, Option.map_some,
    Option.some.injEq, int_ofBytes_nat]
  have hw := w.toNat_lt
  simp only [half32]
  rcases Nat.mod_two_eq_zero_or_one i.toNat with h2 | h2
  · have : i % 2 = 0 := by apply UInt64.toNat_inj.mp; simp [h2]
    simp [this, h2, List.range_succ]
    omega
  · have : ¬ i % 2 = 0 := fun e => by have := congrArg UInt64.toNat e; simp at this; omega
    simp [this, h2, List.range_succ]
    omega


/-- **A 4-byte store is a word store of the word with that half replaced**: on the word `w` at
`X`, storing `v` at byte `X + 4 (i % 2)` leaves the memory that storing `setHalf32 w i v'` at
`X` leaves (`v'` the low 32 bits of `v`). -/
theorem store32_eq {d : _root_.Mem 64} {X : Nat} {w : Word} (hX : X + 8 ≤ 2 ^ 64) (h : rdW d (A X) = some w)
    (i : Word) (v : Int) :
    _root_.Mem.storeInt d (A (X + 4 * (i.toNat % 2))) 4 v =
      wrW d (A X) (setHalf32 w i (UInt64.ofNat (v % 4294967296).toNat)).toBitVec := by
  apply Std.ExtHashMap.ext_getElem?
  intro p
  rw [← Std.ExtHashMap.get?_eq_getElem?, ← Std.ExtHashMap.get?_eq_getElem?]
  have hp : p = A p.toNat := by simp [A]
  have hy := p.isLt
  generalize p.toNat = y at hp hy
  subst hp
  have hb := rdW_get? h
  have hH : X + 4 * (i.toNat % 2) + 4 ≤ 2 ^ 64 := by omega
  have hW := setHalf32_toNat w i (UInt64.ofNat (v % 4294967296).toNat)
  generalize setHalf32 w i (UInt64.ofNat (v % 4294967296).toNat) = W at hW
  have hwl := w.toNat_lt
  have hWl := W.toNat_lt
  have hv1 : (v % 4294967296).toNat < 2 ^ 64 := by omega
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hv1] at hW
  have hti : W.toBitVec.toInt = if 2 * W.toNat < 2 ^ 64 then (W.toNat : Int) else (W.toNat : Int) - 2 ^ 64 := by
    rw [BitVec.toInt_eq_toNat_cond]; simp
  unfold wrW
  by_cases hin : X + 4 * (i.toNat % 2) ≤ y ∧ y < X + 4 * (i.toNat % 2) + 4
  · obtain ⟨k, rfl⟩ : ∃ k, y = X + 4 * (i.toNat % 2) + k := ⟨y - (X + 4 * (i.toNat % 2)), by omega⟩
    rw [_root_.Mem.storeInt, get?_storeBytes_in (by rw [Int.toBytes_length]; omega) (by rw [Int.toBytes_length]; omega),
      _root_.Mem.storeInt, show X + 4 * (i.toNat % 2) + k = X + (4 * (i.toNat % 2) + k) by omega,
      get?_storeBytes_in (by rw [Int.toBytes_length]; omega) (by rw [Int.toBytes_length]; omega),
      toBytes_getElem, toBytes_getElem]
    congr 2
    rw [hti]
    rcases Nat.mod_two_eq_zero_or_one i.toNat with h2 | h2 <;>
      simp only [h2, ↓reduceIte, Nat.one_ne_zero] at hW ⊢ <;>
      obtain _|_|_|_|k := k <;> (try omega) <;>
      simp only [Nat.reduceAdd, Nat.reduceMul, Nat.reducePow, Int.reducePow, UInt8.toNat_ofNat'] <;>
      split <;> omega
    all_goals omega
  · rw [_root_.Mem.get?_storeInt_of_ne _ _ _ _ _ (fun j hj => by
      rw [A_add]; exact A_ne (by omega) (by omega) (by omega))]
    by_cases hw8 : X ≤ y ∧ y < X + 8
    · obtain ⟨k, rfl⟩ : ∃ k, y = X + k := ⟨y - X, by omega⟩
      rw [hb k (by omega), _root_.Mem.storeInt,
        get?_storeBytes_in (by rw [Int.toBytes_length]; omega) (by rw [Int.toBytes_length]; omega),
        toBytes_getElem]
      congr 1
      apply UInt8.toNat_inj.mp
      simp only [UInt8.toNat_ofNat', Nat.toUInt8_eq, hti]
      rcases Nat.mod_two_eq_zero_or_one i.toNat with h2 | h2 <;>
        simp only [h2, ↓reduceIte, Nat.one_ne_zero] at hW hin ⊢ <;>
        obtain _|_|_|_|_|_|_|_|k := k <;> (try omega) <;>
        simp only [Nat.reduceAdd, Nat.reduceMul, Nat.reducePow, Int.reducePow, UInt8.toNat_ofNat'] <;>
        split <;> omega
      all_goals omega
    · rw [_root_.Mem.get?_storeInt_of_ne _ _ _ _ _ (fun j hj => by
        rw [A_add]; exact A_ne (by omega) (by omega) (by omega))]

end L.Compiler
