module

public import ConAguaX86.Compiler.Abi
public import ConAguaX86.Compiler.Rel
import all Kraken.Mem
import Kraken.X64.Registers

@[expose] public section

/-!
# The entry stub's stores, on the machine

`sim_stores`: the stub's body `storesCode d vs` writes word `i` of `vs` at `r8 + d + 8i` and
changes no register but `rax` (and the flags). The values (`SVal.val`) are read from the registers
at the start.
-/

namespace L.Compiler

/-- The byte `j` of a word store. -/
theorem get?_wrW_byte {d : DataMem} {x j : Nat} {v : BitVec 64} (hj : j < 8) :
    (wrW d (A x) v).get? (A (x + j)) = (UInt64.ofBitVec v).toBytes[j]? := by
  have hA : A (x + j) = A x + BitVec.ofNat 64 j := (A_add x j).symm
  rw [hA]
  simp only [wrW, _root_.Mem.storeInt, _root_.Mem.storeBytes, Std.ExtHashMap.get?_eq_getElem?]
  rw [Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union]
  have h := get?_At_idx (Int.toBytes 8 v.toInt) (A x) j (by omega) (by simp [Int.toBytes_length])
  simp only [Std.ExtHashMap.get?_eq_getElem?] at h
  rw [h]
  have : (Int.toBytes 8 v.toInt)[j]?.isSome := by simp [Int.toBytes_length, hj]
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp this
  rw [hb]
  simp only [Option.some_or]
  rw [← hb]; rfl

/-- The word an `SVal` stands for, in registers `R`. -/
def SVal.val (R : Reg64s) : SVal → BitVec 64
  | .reg r => R.get64 r
  | .imm w => w.toBitVec
  | .addr off => off.toUInt64.toBitVec + R.get64 .r8

/-- The memory after the stores of `vs` from `[base + d]` on, with the values from `R`. -/
def stores (R : Reg64s) (base : Nat) : DataMem → Nat → List SVal → DataMem
  | m, _, [] => m
  | m, d, v :: vs => stores R base (wrW m (A (base + d)) (v.val R)) (d + 8) vs

/-- The registers `vs` reads are not `rax`. -/
def SVal.noRax : SVal → Prop
  | .reg r => r ≠ .rax
  | _ => True

theorem romVals_length : ∀ bs : List UInt8, (romVals bs).length = (bs.length + 7) / 8
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: bs => by
    simp only [romVals, List.length_cons, romVals_length bs]; omega
  | [] => rfl
  | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | [_, _, _, _, _, _]
  | [_, _, _, _, _, _, _] => by simp [romVals]

/-- Where the table-relative array (`Tab.tbl`) may lie: past the table (descriptors, constant data,
results, globals) and the trampoline's 32-byte save area, and its words (its minimum length) within
the first `2^31` bytes of the table's slot; it is a word array at the last position (which gets
no slot, `Tab.nslot`). -/
def abiTblOk (tab : Tab) : Bool :=
  match tab.tbl with
  | none => true
  | some (a, c) => (decide (16 + 24 * (tab.nb + tab.nw) + 8 * tab.romWords + 8 * tab.nxres + 8 * tab.ng + 32 ≤ c) &&
      decide (c + 8 * tab.min64 (TieredArray.t0 a) ≤ 2 ^ 31)) &&
      (tab.lmap.find (TieredArray.t0 a).code == some (tab.nb + tab.nw - 1) && decide (tab.nb < tab.nb + tab.nw))

/-- What the stub needs of the table: two byte arrays, the table within the first `2^31` bytes
(the stores' displacements are 32-bit), the region size below `2^64`, and every minimum length
(`Tab.min64`) below `2^31` (a slot has `abiWords`; `ca_check_b` compares with a 32-bit
immediate). -/
def abiTabOk (tab : Tab) : Bool :=
  (tab.nb == 2 && decide (16 + 24 * (tab.nb + tab.nw) + 8 * tab.romWords + 8 * tab.nxres + 8 * tab.ng + 32 ≤ 2 ^ 31) &&
    decide (abiNeed tab < 2 ^ 64)) && tab.mins.all (fun x => decide (x.2 < 2 ^ 31)) && abiTblOk tab

theorem abiVals_length (tab : Tab) :
    (abiVals tab).length = 2 + 3 * (tab.nb + tab.nw) + tab.romWords := by
  simp only [abiVals, List.length_append, List.length_cons, List.length_nil, romVals_length,
    Tab.romWords, ← tab.romLen_eq, List.length_map, List.length_range]
  omega

/-- The bytes of `romWord bs`: `bs`, then zeros. -/
theorem romWord_toBytes (bs : List UInt8) (h : bs.length ≤ 8) :
    (romWord bs).toBytes = bs ++ List.replicate (8 - bs.length) 0 := by
  rw [romWord, UInt64.toBytes_ofBytes _ (by simp; omega)]
  rw [List.take_of_length_le (by simp; omega)]

/-- Byte `i` of the constant data is byte `i % 8` of word `i / 8`. -/
theorem romVals_byte : ∀ (bs : List UInt8) (i : Nat) (hi : i < bs.length),
    ∃ w, (romVals bs)[i / 8]? = some (.imm w) ∧ w.toBytes[i % 8]? = some bs[i] := by
  intro bs
  induction bs using romVals.induct with
  | case1 b0 b1 b2 b3 b4 b5 b6 b7 rest ih =>
    intro i hi
    simp only [List.length_cons] at hi
    by_cases h8 : i < 8
    · refine ⟨romWord [b0, b1, b2, b3, b4, b5, b6, b7], ?_, ?_⟩
      · rw [Nat.div_eq_of_lt h8]; simp [romVals]
      · rw [romWord_toBytes _ (by simp), Nat.mod_eq_of_lt h8]
        have : (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest) = [b0, b1, b2, b3, b4, b5, b6, b7] ++ rest := rfl
        simp only [this, List.getElem_append_left (show i < [b0, b1, b2, b3, b4, b5, b6, b7].length by simp; omega)]
        rw [List.getElem?_append_left (by simp; omega)]
        simp [List.getElem?_eq_getElem (show i < [b0, b1, b2, b3, b4, b5, b6, b7].length by simp; omega)]
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 8 := ⟨i - 8, by omega⟩
      obtain ⟨w, h1, h2⟩ := ih j (by omega)
      refine ⟨w, ?_, ?_⟩
      · rw [show (j + 8) / 8 = j / 8 + 1 by omega]; simpa [romVals] using h1
      · rw [show (j + 8) % 8 = j % 8 by omega, h2]; simp
  | case2 => intro i hi; simp at hi
  | case3 bs h1 h2 =>
    intro i hi
    have hlen : bs.length < 8 := by
      match bs, h1, h2 with
      | [], _, _ | [_], _, _ | [_, _], _, _ | [_, _, _], _, _ | [_, _, _, _], _, _
      | [_, _, _, _, _], _, _ | [_, _, _, _, _, _], _, _ | [_, _, _, _, _, _, _], _, _ => simp
      | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, h, _ => exact absurd rfl (h _ _ _ _ _ _ _ _ _)
    refine ⟨romWord bs, ?_, ?_⟩
    · rw [romVals.eq_3 bs h1 h2, Nat.div_eq_of_lt (by omega)]; rfl
    · rw [romWord_toBytes _ (by omega), Nat.mod_eq_of_lt (by omega), List.getElem?_append_left hi]
      simp [hi]

theorem stores_only (R : Reg64s) (base : Nat) :
    ∀ (vs : List SVal) (m : DataMem) (d : Nat), base + d + 8 * vs.length ≤ 2 ^ 64 →
    Only (base + d) (base + d + 8 * vs.length) m (stores R base m d vs)
  | [], m, d, _ => by simpa [stores] using Only.refl _ _ m
  | v :: vs, m, d, h => by
    simp only [List.length_cons] at h
    simp only [stores, List.length_cons]
    exact Only.union (Only.wrW (by omega)) (stores_only R base vs _ (d + 8) (by omega))
      (by omega) (by omega) (by omega) (by omega)

theorem stores_rdW (R : Reg64s) (base : Nat) :
    ∀ (vs : List SVal) (m : DataMem) (d i : Nat) (hi : i < vs.length), base + d + 8 * vs.length ≤ 2 ^ 64 →
    rdW (stores R base m d vs) (A (base + d + 8 * i)) = some (UInt64.ofBitVec (vs[i].val R))
  | [], _, _, _, hi, _ => absurd hi (by simp)
  | v :: vs, m, d, i, hi, h => by
    simp only [List.length_cons] at h hi
    simp only [stores]
    cases i with
    | zero =>
      rw [(stores_only R base vs _ (d + 8) (by omega)).rdW_eq (by omega) (by omega)]
      simpa using rdW_wrW_same _ _ _
    | succ i =>
      have := stores_rdW R base vs (wrW m (A (base + d)) (v.val R)) (d + 8) i (by omega) (by omega)
      rw [show base + (d + 8) + 8 * i = base + d + 8 * (i + 1) by omega] at this
      simpa using this

theorem stores_byte (R : Reg64s) (base : Nat) :
    ∀ (vs : List SVal) (m : DataMem) (d i j : Nat) (hi : i < vs.length), j < 8 →
    base + d + 8 * vs.length ≤ 2 ^ 64 →
    (stores R base m d vs).get? (A (base + d + 8 * i + j)) = (UInt64.ofBitVec (vs[i].val R)).toBytes[j]?
  | [], _, _, _, _, hi, _, _ => absurd hi (by simp)
  | v :: vs, m, d, i, j, hi, hj, h => by
    simp only [List.length_cons] at h hi
    simp only [stores]
    cases i with
    | zero =>
      rw [(stores_only R base vs _ (d + 8) (by omega)).same _ (by omega) (by omega)]
      simpa using get?_wrW_byte hj
    | succ i =>
      have := stores_byte R base vs (wrW m (A (base + d)) (v.val R)) (d + 8) i j (by omega) hj (by omega)
      rw [show base + (d + 8) + 8 * i + j = base + d + 8 * (i + 1) + j by omega] at this
      simpa using this

theorem abiTabOk_spec {tab : Tab} (h : abiTabOk tab = true) :
    tab.nb = 2 ∧ 16 + 24 * (tab.nb + tab.nw) + 8 * tab.romWords + 8 * tab.nxres + 8 * tab.ng + 32 ≤ 2 ^ 31 ∧
      abiNeed tab < 2 ^ 64 := by
  have h' := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp h).1).1
  simpa [Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h'

/-- Every minimum length is below `2^31`. -/
theorem abiTabOk_minLt {tab : Tab} (h : abiTabOk tab = true) (s : TieredArray) : tab.min64 s < 2 ^ 31 :=
  Tab.min64_lt (by decide) ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp h).1).2 s

theorem Tab.tbl64_some {tab : Tab} {s : TieredArray} {c : Nat} (h : tab.tbl64 s = some c) :
    ∃ a, tab.tbl = some (a, c) ∧ s = TieredArray.t0 a := by
  unfold Tab.tbl64 at h
  split at h
  · rename_i a c' e
    split at h
    · rename_i hs
      cases h
      refine ⟨a, e, ?_⟩
      rcases s with ⟨x, _ | _⟩ <;> simp_all [TieredArray.t0]
    · cases h
  · cases h

/-- The table-relative array (`Tab.tbl64 s = some c`) lies past the table and the save area, its
words within the first `2^31` bytes. -/
theorem abiTabOk_tbl {tab : Tab} (h : abiTabOk tab = true) {s : TieredArray} {c : Nat} (hc : tab.tbl64 s = some c) :
    16 + 24 * (tab.nb + tab.nw) + 8 * tab.romWords + 8 * tab.nxres + 8 * tab.ng + 32 ≤ c ∧
      c + 8 * tab.min64 s ≤ 2 ^ 31 := by
  have h2 := ((Bool.and_eq_true _ _).mp h).2
  obtain ⟨a, ht, rfl⟩ := Tab.tbl64_some hc
  simp only [abiTblOk, ht, Bool.and_eq_true, decide_eq_true_eq] at h2
  exact h2.1

/-- The table-relative array is a word array at the last position. -/
theorem abiTabOk_tblPos {tab : Tab} (h : abiTabOk tab = true) {s : TieredArray} {c : Nat} (hc : tab.tbl64 s = some c) :
    tab.dom64 s = true ∧ tab.pos64 s = tab.nb + tab.nw - 1 := by
  have h2 := ((Bool.and_eq_true _ _).mp h).2
  obtain ⟨a, ht, rfl⟩ := Tab.tbl64_some hc
  simp only [abiTblOk, ht, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h2
  exact ⟨tab.dom64_of_find h2.2.1 (by omega), tab.pos64_eq h2.2.1⟩

/-- Every minimum length fits a slot. -/
theorem abiTabOk_min {tab : Tab} (h : abiTabOk tab = true) (s : TieredArray) : tab.min64 s ≤ abiWords := by
  have := abiTabOk_minLt h s; simp only [abiWords]; omega

theorem abiVals_noRax (tab : Tab) : ∀ v ∈ abiVals tab, v.noRax := by
  intro v hv
  simp only [abiVals, List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hv
  have hrom : ∀ bs : List UInt8, ∀ v ∈ romVals bs, v.noRax := by
    intro bs
    induction bs using romVals.induct with
    | case1 _ _ _ _ _ _ _ _ _ ih =>
      intro v hv; simp only [romVals, List.mem_cons] at hv
      rcases hv with rfl | hv
      · trivial
      · exact ih v hv
    | case2 => intro v hv; simp [romVals] at hv
    | case3 bs h1 h2 =>
      intro v hv
      rw [romVals.eq_3 bs h1 h2] at hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      subst hv; trivial
  rcases hv with ((((h | h) | h) | h) | h) | h
  · subst h; trivial
  · subst h; trivial
  · obtain ⟨p, _, rfl⟩ := h
    simp only [abiBase]; split
    · split <;> simp [SVal.noRax]
    · split <;> trivial
  · obtain ⟨p, _, rfl⟩ := h
    simp only [abiLen]; split
    · split <;> simp [SVal.noRax]
    · split <;> trivial
  · obtain ⟨p, _, rfl⟩ := h
    simp only [abiLen32]; split <;> trivial
  · exact hrom _ v h

theorem flatMap_pair_getElem? {α : Type} (f g : Nat → α) :
    ∀ n a, a < n → ((List.range n).flatMap fun a => [f a, g a])[2 * a]? = some (f a) ∧
      ((List.range n).flatMap fun a => [f a, g a])[2 * a + 1]? = some (g a)
  | 0, _, h => absurd h (by omega)
  | n + 1, a, h => by
    have hl : ((List.range n).flatMap fun a => [f a, g a]).length = 2 * n := by
      simp [List.length_flatMap, List.map_const']; omega
    rw [List.range_succ, List.flatMap_append]
    by_cases ha : a < n
    · obtain ⟨h1, h2⟩ := flatMap_pair_getElem? f g n a ha
      rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
      exact ⟨h1, h2⟩
    · obtain rfl : a = n := by omega
      rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), hl]
      simp

theorem flatMap_pair_length {α : Type} (f g : Nat → α) (n : Nat) :
    ((List.range n).flatMap fun a => [f a, g a]).length = 2 * n := by
  simp [List.length_flatMap, List.map_const']; omega

/-- The table words, by descriptor position: position `p`'s base at `2 + p`, its length at
`2 + (nb + nw) + p`, its length in 32-bit elements at `2 + 2 (nb + nw) + p`, then the constant
data. -/
theorem abiVals_getElem? (tab : Tab) :
    (abiVals tab)[0]? = some (.addr (abiSlot + abiStack)) ∧ (abiVals tab)[1]? = some (.addr abiSlot) ∧
    (∀ p < tab.nb + tab.nw, (abiVals tab)[2 + p]? = some (abiBase tab p) ∧
      (abiVals tab)[2 + (tab.nb + tab.nw) + p]? = some (abiLen tab p) ∧
      (abiVals tab)[2 + 2 * (tab.nb + tab.nw) + p]? = some (abiLen32 tab p)) ∧
    (∀ i, (abiVals tab)[2 + 3 * (tab.nb + tab.nw) + i]? = (romVals tab.rom)[i]?) := by
  refine ⟨rfl, rfl, fun p hp => ⟨?_, ?_, ?_⟩, fun i => ?_⟩
  · simp only [abiVals]
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega),
      List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp)]
    simp only [List.length_cons, List.length_nil, show 2 + p - (0 + 1 + 1) = p by omega,
      List.getElem?_map, List.getElem?_range hp, Option.map_some]
  · simp only [abiVals]
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega),
      List.getElem?_append_right (by simp; omega)]
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_map, List.length_range,
      show 2 + (tab.nb + tab.nw) + p - (0 + 1 + 1 + (tab.nb + tab.nw)) = p by omega,
      List.getElem?_map, List.getElem?_range hp, Option.map_some]
  · simp only [abiVals]
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp; omega)]
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_map, List.length_range,
      show 2 + 2 * (tab.nb + tab.nw) + p - (0 + 1 + 1 + (tab.nb + tab.nw) + (tab.nb + tab.nw)) = p by omega,
      List.getElem?_map, List.getElem?_range hp, Option.map_some]
  · simp only [abiVals]
    rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_map, List.length_range]
    congr 1; omega

/-- The word an address store writes. -/
theorem addr_val (R : Reg64s) (off : Nat) (_h : R.r8.toNat + off < 2 ^ 64) :
    UInt64.ofBitVec ((SVal.addr off).val R) = UInt64.ofNat (R.r8.toNat + off) := by
  apply UInt64.toNat_inj.mp
  simp only [SVal.val, Reg64s.get64_r8, UInt64.toNat_ofBitVec, BitVec.toNat_add, UInt64.toNat_toBitVec,
    UInt64.toNat_ofNat', Nat.toUInt64]
  omega

/-- A word of `stores`, by position. -/
theorem stores_rdW? (R : Reg64s) (base : Nat) (vs : List SVal) (m : DataMem) (i : Nat) (v : SVal)
    (hv : vs[i]? = some v) (h : base + 8 * vs.length ≤ 2 ^ 64) :
    rdW (stores R base m 0 vs) (A (base + 8 * i)) = some (UInt64.ofBitVec (v.val R)) := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hv
  simpa using stores_rdW R base vs m 0 i hi (by simpa using h)

/-! ## The layout the stub sets up

The stub gives descriptor position `p` (past the two buffers) the slot `p`, or (the table-relative
array, at the last position) its place inside slot `0`. -/

theorem Tab.slotOf_eq {tab : Tab} (h : tab.nb = 2) (p : Nat) : tab.slotOf p = p := by
  simp [Tab.slotOf, Tab.nbuf, h]

/-- The layout of the stub's partition: the table at `base`, the L stack in slot `1`, positions
`0`/`1` (the byte arrays of a two-byte-array table) the caller's buffers `[inp, inp + n)`,
`[pins, pins + np)`, position `p ≥ 2` in slot `p` (as `abiVals` fills it) with `abiSz` words: a
whole slot, or for the table-relative array its minimum length inside slot `0` (`abiOff`). -/
def abiLayout (tab : Tab) (base inp n pins np : Nat) : Layout where
  tab
  T := base
  b p := if p = 0 then inp else if p = 1 then pins else base + abiOff tab p
  s p := if p = 0 then n else if p = 1 then np else abiSz tab (tab.wAt p)
  lo := base + abiSlot
  hi := base + abiSlot + abiStack
  nargs := 0

section
variable (tab : Tab) (base inp n pins np : Nat)
@[simp] theorem abiLayout_tab : (abiLayout tab base inp n pins np).tab = tab := rfl
@[simp] theorem abiLayout_T : (abiLayout tab base inp n pins np).T = base := rfl
theorem abiLayout_b64 {p : Nat} (hp : 2 ≤ p) :
    (abiLayout tab base inp n pins np).b p = base + abiOff tab p := by
  simp [abiLayout, show p ≠ 0 by omega, show p ≠ 1 by omega]
theorem abiLayout_s64 {p : Nat} (hp : 2 ≤ p) :
    (abiLayout tab base inp n pins np).s p = abiSz tab (tab.wAt p) := by
  simp [abiLayout, show p ≠ 0 by omega, show p ≠ 1 by omega]
@[simp] theorem abiLayout_lo : (abiLayout tab base inp n pins np).lo = base + abiSlot := rfl
@[simp] theorem abiLayout_hi : (abiLayout tab base inp n pins np).hi = base + abiSlot + abiStack := rfl
@[simp] theorem abiLayout_nargs : (abiLayout tab base inp n pins np).nargs = 0 := rfl
@[simp] theorem abiLayout_b8_0 : (abiLayout tab base inp n pins np).b 0 = inp := rfl
@[simp] theorem abiLayout_b8_1 : (abiLayout tab base inp n pins np).b 1 = pins := rfl
@[simp] theorem abiLayout_s8_0 : (abiLayout tab base inp n pins np).s 0 = n := rfl
@[simp] theorem abiLayout_s8_1 : (abiLayout tab base inp n pins np).s 1 = np := rfl
end

/-- Byte `x` is in slot `j` of the region at `base`. -/
def InSlot (base j x : Nat) : Prop := base + abiSlot * j ≤ x ∧ x < base + abiSlot * j + abiSlot

theorem InSlot.eq {base j j' x : Nat} (h : InSlot base j x) (h' : InSlot base j' x) : j = j' := by
  rcases Nat.lt_trichotomy j j' with h1 | h1 | h1
  · have : abiSlot * j + abiSlot ≤ abiSlot * j' := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h1
    unfold InSlot at *; omega
  · exact h1
  · have : abiSlot * j' + abiSlot ≤ abiSlot * j := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h1
    unfold InSlot at *; omega

theorem InSlot.lt {base j x : Nat} (h : InSlot base j x) {n : Nat} (hj : j < n) :
    x < base + abiSlot * n := by
  have : abiSlot * j + abiSlot ≤ abiSlot * n := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  unfold InSlot at h; omega

theorem InSlot.ge {base j x : Nat} (h : InSlot base j x) {n : Nat} (hj : n ≤ j) :
    base + abiSlot * n ≤ x := by
  have : abiSlot * n ≤ abiSlot * j := Nat.mul_le_mul_left _ hj
  unfold InSlot at h; omega

/-- Byte `x` is past the table of the region at `base` and its save area (the table without entry
arguments), within the first `2^31` bytes of slot `0`: where the table-relative array lies. -/
def InTbl (tab : Tab) (base x : Nat) : Prop :=
  base + (16 + 24 * (tab.nb + tab.nw) + 8 * tab.romWords + 8 * tab.nxres + 8 * tab.ng + 32) ≤ x ∧
    x < base + 2 ^ 31

theorem InTbl.slot0 {tab : Tab} {base x : Nat} (h : InTbl tab base x) : InSlot base 0 x := by
  unfold InTbl at h; unfold InSlot abiSlot; omega

theorem InTbl.not_slot {tab : Tab} {base x j : Nat} (h : InTbl tab base x) (hj : 1 ≤ j) : ¬ InSlot base j x := by
  intro h'; have := InSlot.eq h.slot0 h'; omega

/-- The table-relative array (`Tab.tbl64 (tab.wAt p) = some c`) at `base + c`, with its minimum
length, lies in `InTbl`. -/
theorem abiTabOk_inTbl {tab : Tab} (hok : abiTabOk tab = true) {p c base x : Nat}
    (hc : tab.tbl64 (tab.wAt p) = some c) (h1 : base + c ≤ x) (h2 : x < base + c + 8 * tab.min64 (tab.wAt p)) :
    InTbl tab base x := by
  have := abiTabOk_tbl hok hc
  unfold InTbl; omega

theorem abiOff_tbl {tab : Tab} {p c : Nat} (hc : tab.tbl64 (tab.wAt p) = some c) : abiOff tab p = c := by
  simp only [abiOff, hc]

theorem abiOff_slot {tab : Tab} {p : Nat} (hc : tab.tbl64 (tab.wAt p) = none) :
    abiOff tab p = abiSlot * tab.slotOf p := by
  simp only [abiOff, hc]

theorem abiSz_tbl {tab : Tab} {s : TieredArray} {c : Nat} (hc : tab.tbl64 s = some c) : abiSz tab s = tab.min64 s := by
  simp only [abiSz, hc]

theorem abiSz_slot {tab : Tab} {s : TieredArray} (hc : tab.tbl64 s = none) : abiSz tab s = abiWords := by
  simp only [abiSz, hc]

theorem abiSz_le {tab : Tab} (hok : abiTabOk tab = true) (s : TieredArray) : abiSz tab s ≤ abiWords := by
  unfold abiSz; split
  · exact abiTabOk_min hok s
  · exact Nat.le_refl _

theorem min64_le_abiSz {tab : Tab} (hok : abiTabOk tab = true) (s : TieredArray) : tab.min64 s ≤ abiSz tab s := by
  unfold abiSz; split
  · exact Nat.le_refl _
  · exact abiTabOk_min hok s

/-- The table-relative array of `tab.tbl = some (a, c)` is `↑a`, at offset `c`. -/
theorem Tab.tbl64_t0 {tab : Tab} {a : ArrId} {c : Nat} (h : tab.tbl = some (a, c)) :
    tab.tbl64 (TieredArray.t0 a) = some c := by
  simp [Tab.tbl64, h]

/-- The position holding the table-relative array is the last one. -/
theorem tbl_pos_last {tab : Tab} (hok : abiTabOk tab = true) {p c : Nat} (hp : p < tab.nb + tab.nw)
    (h : tab.tbl64 (tab.wAt p) = some c) : p = tab.nb + tab.nw - 1 := by
  obtain ⟨hd, hpos⟩ := abiTabOk_tblPos hok h
  have := tab.wAt_inj hp (q := tab.pos64 (tab.wAt p)) (tab.pos64_lt hd).2 (tab.wAt_pos64 hd).symm
  omega

/-- Two positions holding the table-relative array are one. -/
theorem tbl_pos_eq {tab : Tab} (hok : abiTabOk tab = true) {p q c c' : Nat} (hp : p < tab.nb + tab.nw)
    (hq : q < tab.nb + tab.nw) (h : tab.tbl64 (tab.wAt p) = some c) (h' : tab.tbl64 (tab.wAt q) = some c') :
    p = q := by
  rw [tbl_pos_last hok hp h, tbl_pos_last hok hq h']

/-- A position that is not the table-relative array's has a slot. -/
theorem slot_lt_nslot {tab : Tab} (hok : abiTabOk tab = true) (hnb : tab.nb = 2) {p : Nat}
    (hp : p < tab.nb + tab.nw) (h : tab.tbl64 (tab.wAt p) = none) : p < tab.nslot := by
  simp only [Tab.nslot, Tab.slotOf_eq hnb]
  cases ht : tab.tbl with
  | none => simp; omega
  | some ac =>
    obtain ⟨a, c⟩ := ac
    obtain ⟨hd, hpos⟩ := abiTabOk_tblPos hok (Tab.tbl64_t0 ht)
    have hne : p ≠ tab.nb + tab.nw - 1 := by
      intro e; subst e; rw [← hpos, tab.wAt_pos64 hd, Tab.tbl64_t0 ht] at h; cases h
    simp; omega

/-- The region has the table's and the stack's slots. -/
theorem two_le_nslot {tab : Tab} (hok : abiTabOk tab = true) : 2 ≤ tab.nslot := by
  obtain ⟨hnb, -, -⟩ := abiTabOk_spec hok
  simp only [Tab.nslot, Tab.slotOf_eq hnb]
  cases ht : tab.tbl with
  | none => simp; omega
  | some ac =>
    obtain ⟨a, c⟩ := ac
    obtain ⟨hd, hpos⟩ := abiTabOk_tblPos hok (Tab.tbl64_t0 ht)
    have := tab.pos64_lt hd
    simp; omega

/-- The region has at least two slots. -/
theorem abiNeed_ge {tab : Tab} (hok : abiTabOk tab = true) : 2 ^ 36 ≤ abiNeed tab := by
  have := Nat.mul_le_mul_left abiSlot (two_le_nslot hok); simp only [abiNeed, abiSlot] at *; omega

/-- The region holds the slots `[0, nslot)`. -/
theorem abiNeed_eq (tab : Tab) : abiNeed tab = abiSlot * tab.nslot := rfl

/-- A byte of position `p ≥ 2` in `ca_setup`'s layout: in `p`'s own slot (below `nslot`), or (the
table-relative array) in `InTbl`. -/
theorem abiLayout_in64 {tab : Tab} (hok : abiTabOk tab = true) {base inp n pins np p x : Nat}
    (hp2 : 2 ≤ p) (hp : p < tab.nb + tab.nw) (h : (abiLayout tab base inp n pins np).In64 p x) :
    (tab.tbl64 (tab.wAt p) = none ∧ p < tab.nslot ∧ InSlot base p x) ∨ InTbl tab base x := by
  obtain ⟨hnb, -, -⟩ := abiTabOk_spec hok
  obtain ⟨h1, h2⟩ := h
  rw [abiLayout_b64 _ _ _ _ _ _ hp2] at h1 h2; rw [abiLayout_s64 _ _ _ _ _ _ hp2] at h2
  cases hc : tab.tbl64 (tab.wAt p) with
  | none =>
    rw [abiOff_slot hc, Tab.slotOf_eq hnb] at h1 h2; rw [abiSz_slot hc] at h2
    exact .inl ⟨rfl, slot_lt_nslot hok hnb hp hc, h1, by simp only [abiSlot, abiWords] at h2 ⊢; omega⟩
  | some c =>
    rw [abiOff_tbl hc] at h1 h2; rw [abiSz_tbl hc] at h2
    exact .inr (abiTabOk_inTbl hok hc h1 h2)

/-- A byte of a word array in `ca_setup`'s layout lies past the table and its save area and inside
the region the stub needs (`abiNeed`). -/
theorem abiLayout_in64_bounds {tab : Tab} (hok : abiTabOk tab = true) {base inp n pins np p x : Nat}
    (hp2 : 2 ≤ p) (hp : p < tab.nb + tab.nw) (h : (abiLayout tab base inp n pins np).In64 p x) :
    base + (16 + 24 * (tab.nb + tab.nw) + 8 * tab.romWords + 8 * tab.nxres + 8 * tab.ng + 32) ≤ x ∧
      x < base + abiNeed tab := by
  obtain ⟨hnb, htab, -⟩ := abiTabOk_spec hok
  rcases abiLayout_in64 hok hp2 hp h with ⟨-, hs, hx⟩ | ⟨h1, h2⟩
  · have := hx.lt hs; have := hx.ge hp2
    simp only [abiNeed]; simp only [abiSlot] at *; omega
  · have : 1 ≤ tab.nslot := by simp only [Tab.nslot, Tab.slotOf_eq hnb]; split <;> omega
    have : abiSlot * 1 ≤ abiSlot * tab.nslot := Nat.mul_le_mul_left _ this
    simp only [abiNeed]; simp only [abiSlot] at *; omega

/-- The caller's side of the stub's layout: the region `[base, base + blen)` is large enough and
in the address space, the buffers are in the address space, apart from the region and from each
other. -/
structure AbiGeom (tab : Tab) (base blen inp n pins np : Nat) : Prop where
  need : abiNeed tab ≤ blen
  fits : base + blen < 2 ^ 64
  inEnd : inp + n < 2 ^ 64
  pinsEnd : pins + np < 2 ^ 64
  inDisj : ∀ x, inp ≤ x → x < inp + n → x < base ∨ base + blen ≤ x
  pinsDisj : ∀ x, pins ≤ x → x < pins + np → x < base ∨ base + blen ≤ x
  bufDisj : ∀ x, inp ≤ x → x < inp + n → ¬ (pins ≤ x ∧ x < pins + np)

/-- A byte of position `p` in `ca_setup`'s layout: in the input buffer, in the pin-data buffer,
or (a word position) in its slot or `InTbl`. -/
theorem abiLayout_in {tab : Tab} (hok : abiTabOk tab = true) {base inp n pins np p x : Nat}
    (hp : p < tab.nb + tab.nw) (h : (abiLayout tab base inp n pins np).In p x) :
    (p = 0 ∧ inp ≤ x ∧ x < inp + n) ∨ (p = 1 ∧ pins ≤ x ∧ x < pins + np) ∨
      (2 ≤ p ∧ ((tab.tbl64 (tab.wAt p) = none ∧ p < tab.nslot ∧ InSlot base p x) ∨ InTbl tab base x)) := by
  obtain ⟨hnb, -, -⟩ := abiTabOk_spec hok
  rcases (by omega : p = 0 ∨ p = 1 ∨ 2 ≤ p) with rfl | rfl | h2
  · have := Layout.In.to8 (G := abiLayout tab base inp n pins np) (by simp [hnb]) h
    exact .inl ⟨rfl, this⟩
  · have := Layout.In.to8 (G := abiLayout tab base inp n pins np) (by simp [hnb]) h
    exact .inr (.inl ⟨rfl, this⟩)
  · exact .inr (.inr ⟨h2, abiLayout_in64 hok h2 hp (Layout.In.to64 (by simp [hnb]; omega) h)⟩)

theorem abiLayout_ok {tab : Tab} (hok : abiTabOk tab = true) {base blen inp n pins np : Nat}
    (hg : AbiGeom tab base blen inp n pins np) : (abiLayout tab base inp n pins np).Ok := by
  obtain ⟨hnb, htab, -⟩ := abiTabOk_spec hok
  have hneed := hg.need
  have hfits := hg.fits
  simp only [abiNeed] at hneed
  have hns1 : 2 ≤ tab.nslot := two_le_nslot hok
  have hslot1 : 2 ^ 36 ≤ blen := by
    have := Nat.mul_le_mul_left abiSlot hns1; simp only [abiSlot] at this hneed; omega
  -- a byte of the region's slots `[0, nslot)` is in the region
  have hin : ∀ j x, j < tab.nslot → InSlot base j x → x < base + blen := fun j x hj h => by
    have := h.lt hj; simp only [abiSlot] at this hneed; omega
  -- every array byte: a buffer (outside the region), or past the table, inside the region
  have hreg : ∀ p < tab.nb + tab.nw, ∀ x, (abiLayout tab base inp n pins np).In p x →
      (p < 2 ∧ (x < base ∨ base + blen ≤ x)) ∨
      (2 ≤ p ∧ base + (16 + 24 * (tab.nb + tab.nw) + 8 * tab.romWords + 8 * tab.nxres + 8 * tab.ng + 32) ≤ x ∧
        x < base + blen ∧ (InTbl tab base x ∨ base + abiSlot * 2 ≤ x)) := by
    intro p hp x hx
    rcases abiLayout_in hok hp hx with ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ | ⟨h2, ⟨-, hs, hsl⟩ | ht⟩
    · exact .inl ⟨by omega, hg.inDisj x h1 h2⟩
    · exact .inl ⟨by omega, hg.pinsDisj x h1 h2⟩
    · have := hsl.ge h2; have := hin p x hs hsl
      refine .inr ⟨h2, ?_, this, .inr (by assumption)⟩
      simp only [abiSlot] at *; omega
    · have : 1 ≤ tab.nslot := by simp only [Tab.nslot, Tab.slotOf_eq hnb]; split <;> omega
      have := hin 0 x (by omega) ht.slot0
      exact .inr ⟨h2, ht.1, this, .inl ht⟩
  constructor
  · simp only [Layout.tabEnd, abiLayout_T, abiLayout_tab, abiLayout_nargs]; omega
  · simp only [abiLayout_hi, abiSlot, abiStack]; omega
  · simp only [abiLayout_lo, abiLayout_hi]; omega
  · intro p hp
    simp only [abiLayout_tab] at hp ⊢
    rcases (by omega : p = 0 ∨ p = 1 ∨ 2 ≤ p) with rfl | rfl | h2
    · simpa [Tab.wd, hnb] using hg.inEnd
    · simpa [Tab.wd, hnb] using hg.pinsEnd
    · rw [abiLayout_b64 _ _ _ _ _ _ h2, abiLayout_s64 _ _ _ _ _ _ h2,
        show tab.wd p = 8 by simp [Tab.wd, hnb]; omega]
      cases hc : tab.tbl64 (tab.wAt p) with
      | none =>
        rw [abiOff_slot hc, abiSz_slot hc, Tab.slotOf_eq hnb]
        have := slot_lt_nslot hok hnb hp hc
        have : abiSlot * p + abiSlot ≤ abiSlot * tab.nslot := by
          rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ this
        simp only [abiSlot, abiWords] at *; omega
      | some c =>
        rw [abiOff_tbl hc, abiSz_tbl hc]
        have := abiTabOk_tbl hok hc; omega
  · intro x ⟨h1, h2'⟩ ⟨h3, h4⟩
    simp only [Layout.tabEnd, abiLayout_T, abiLayout_tab, abiLayout_nargs, abiLayout_lo, abiLayout_hi,
      abiSlot] at h1 h2' h3 h4; omega
  · intro x ⟨h1, h2'⟩ ⟨p, hp, hx⟩
    simp only [Layout.tabEnd, abiLayout_T, abiLayout_tab, abiLayout_nargs] at h1 h2' hp
    rcases hreg p hp x hx with ⟨-, h⟩ | ⟨-, h, -⟩ <;> omega
  · intro x ⟨h1, h2'⟩ ⟨p, hp, hx⟩
    simp only [abiLayout_lo, abiLayout_hi, abiSlot, abiStack] at h1 h2'
    simp only [abiLayout_tab] at hp
    rcases hreg p hp x hx with ⟨-, h⟩ | ⟨-, -, -, ht | h⟩
    · omega
    · unfold InTbl at ht; omega
    · unfold abiSlot at h; omega
  · intro p hp q hq hpq x hxp hxq
    simp only [abiLayout_tab] at hp hq
    rcases abiLayout_in hok hp hxp with ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ | ⟨hp2, hpi⟩ <;>
    rcases abiLayout_in hok hq hxq with ⟨rfl, h3, h4⟩ | ⟨rfl, h3, h4⟩ | ⟨hq2, hqi⟩
    · exact hpq rfl
    · exact hg.bufDisj x h1 h2 ⟨h3, h4⟩
    · rcases hreg q hq x hxq with ⟨h, -⟩ | ⟨-, -, hb, -⟩
      · omega
      · have := hreg q hq x hxq; rcases hg.inDisj x h1 h2 with h | h <;>
          rcases this with ⟨h', -⟩ | ⟨-, h5, -, -⟩ <;> omega
    · exact hg.bufDisj x h3 h4 ⟨h1, h2⟩
    · exact hpq rfl
    · have := hreg q hq x hxq; rcases hg.pinsDisj x h1 h2 with h | h <;>
        rcases this with ⟨h', -⟩ | ⟨-, h5, h6, -⟩ <;> omega
    · have := hreg p hp x hxp; rcases hg.inDisj x h3 h4 with h | h <;>
        rcases this with ⟨h', -⟩ | ⟨-, h5, h6, -⟩ <;> omega
    · have := hreg p hp x hxp; rcases hg.pinsDisj x h3 h4 with h | h <;>
        rcases this with ⟨h', -⟩ | ⟨-, h5, h6, -⟩ <;> omega
    · rcases hpi with ⟨hcp, -, hsp⟩ | htp <;> rcases hqi with ⟨hcq, -, hsq⟩ | htq
      · exact hpq (InSlot.eq hsp hsq)
      · exact htq.not_slot (by omega) hsp
      · exact htp.not_slot (by omega) hsq
      · -- both in `InTbl`: both hold the table-relative array
        have hcp : (tab.tbl64 (tab.wAt p)).isSome := by
          cases hc : tab.tbl64 (tab.wAt p) with
          | some _ => rfl
          | none =>
            rcases abiLayout_in hok hp hxp with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, ⟨-, -, hs⟩ | -⟩
            · omega
            · omega
            · exact absurd hs (htp.not_slot (by omega))
            · obtain ⟨h1, h2⟩ := Layout.In.to64 (G := abiLayout tab base inp n pins np) (by simp [hnb]; omega) hxp
              rw [abiLayout_b64 _ _ _ _ _ _ hp2, abiOff_slot hc, Tab.slotOf_eq hnb] at h1
              have : abiSlot * 2 ≤ abiSlot * p := Nat.mul_le_mul_left _ hp2
              unfold InTbl at htp; simp only [abiSlot] at this h1 htp; omega
        have hcq : (tab.tbl64 (tab.wAt q)).isSome := by
          cases hc : tab.tbl64 (tab.wAt q) with
          | some _ => rfl
          | none =>
            obtain ⟨h1, h2⟩ := Layout.In.to64 (G := abiLayout tab base inp n pins np) (by simp [hnb]; omega) hxq
            rw [abiLayout_b64 _ _ _ _ _ _ hq2, abiOff_slot hc, Tab.slotOf_eq hnb] at h1
            have : abiSlot * 2 ≤ abiSlot * q := Nat.mul_le_mul_left _ hq2
            unfold InTbl at htq; simp only [abiSlot] at this h1 htq; omega
        obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hcp
        obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hcq
        exact hpq (tbl_pos_eq hok hp hq hc hc')
  · intro s hs
    simp only [abiLayout_tab] at hs ⊢
    have := tab.pos64_lt hs
    rw [abiLayout_s64 _ _ _ _ _ _ (by omega), tab.wAt_pos64 hs]; exact min64_le_abiSz hok s
  · intro s c hs hc
    simp only [abiLayout_tab, abiLayout_T] at hs hc ⊢
    have := tab.pos64_lt hs
    rw [abiLayout_b64 _ _ _ _ _ _ (by omega), abiOff_tbl (by rw [tab.wAt_pos64 hs]; exact hc)]

section
variable [Host]

theorem sim_stores (Q : MachineState → Prop) (R : Reg64s) (base : Nat) (hb : R.r8.toNat = base) :
    ∀ (vs : List SVal) (d k : Nat) (s : MachineData), Code (storesCode d vs) k →
    (∀ r, r ≠ .rax → s.regs.get64 r = R.get64 r) → (∀ v ∈ vs, v.noRax) →
    d + 8 * vs.length ≤ 2 ^ 31 → base + d + 8 * vs.length ≤ 2 ^ 64 →
    (∀ j < 8 * vs.length, (s.dmem.get? (A (base + d + j))).isSome) →
    (∀ s', s'.dmem = stores R base s.dmem d vs → (∀ r, r ≠ .rax → s'.regs.get64 r = R.get64 r) →
      Ev Q s' (at_ (k + (storesCode d vs).length))) →
    Ev Q s (at_ k) := by
  intro vs
  induction vs with
  | nil =>
    intro d k s _ hR _ _ _ _ hK
    exact ev_congr (hK s rfl hR) (by simp [storesCode])
  | cons v vs ih =>
    intro d k s hc hR hno hd hend hmap hK
    simp only [List.length_cons] at hd hend hmap
    have hr8 : (s.regs.get64 .r8).toNat = base := by
      rw [hR .r8 (by decide)]; simpa using hb
    have hoff : SmallOff ((d : Nat) : Int) := ⟨by omega, by omega⟩
    have hcell : (rdW s.dmem (A (base + d))).isSome :=
      isSome_rdW fun j hj => by rw [A_add]; exact hmap j (by omega)
    have hmap' : ∀ (m : DataMem), (∀ y, (s.dmem.get? y).isSome → (m.get? y).isSome) →
        ∀ j < 8 * vs.length, (m.get? (A (base + (d + 8) + j))).isSome :=
      fun m hm j hj => hm _ (by rw [show base + (d + 8) + j = base + d + (8 + j) by omega]; exact hmap _ (by omega))
    simp only [storesCode] at hc
    have hrest := hc.right
    cases v with
    | reg r =>
      have hnr : r ≠ .rax := hno _ List.mem_cons_self
      simp only [SVal.code, List.length_cons, List.length_nil] at hrest hc
      refine ev_movMR hc.left.head hoff (by rw [hr8]; simpa using hcell) ?_
      refine ih (d + 8) (k + 1) _ hrest hR (fun v hv => hno v (List.mem_cons_of_mem _ hv)) (by omega) (by omega)
        (hmap' _ fun y hy => isSome_get?_storeInt hy) ?_
      intro s' hs' hR'
      refine ev_congr (hK s' ?_ hR') (by simp [storesCode, SVal.code]; omega)
      rw [hs']; simp only [stores, SVal.val, hr8, Int.toNat_natCast, hR r hnr]
    | imm w =>
      simp only [SVal.code, List.length_cons, List.length_nil] at hrest hc
      refine ev_movRI hc.left.head ?_
      refine ev_movMR hc.left.tail.head hoff ?_ ?_
      · simp only [Reg64s.set64_rax, Reg64s.get64_r8] at hr8 ⊢; rw [hr8]; simpa using hcell
      refine ih (d + 8) (k + 1 + 1) _ hrest ?_ (fun v hv => hno v (List.mem_cons_of_mem _ hv)) (by omega) (by omega)
        (hmap' _ fun y hy => isSome_get?_storeInt hy) ?_
      · intro r hr; rw [← hR r hr]; cases r <;> first | exact absurd rfl hr | rfl
      intro s' hs' hR'
      refine ev_congr (hK s' ?_ hR') (by simp [storesCode, SVal.code]; omega)
      rw [hs']; simp only [stores, SVal.val, Reg64s.set64_rax, Reg64s.get64_r8, Reg64s.get64_rax] at hr8 ⊢
      rw [hr8]; simp
    | addr off =>
      simp only [SVal.code, List.length_cons, List.length_nil] at hrest hc
      refine ev_movRI hc.left.head ?_
      refine ev_binO (op := .add) (o := oR .r8) rfl hc.left.tail.head
        (Or.inr (Or.inr ⟨.r8, rfl, rfl⟩)) ?_
      intro st
      refine ev_movMR hc.left.tail.tail.head hoff ?_ ?_
      · simp only [Reg64s.set64_rax, Reg64s.get64_r8] at hr8 ⊢; rw [hr8]; simpa using hcell
      refine ih (d + 8) (k + 1 + 1 + 1) _ hrest ?_ (fun v hv => hno v (List.mem_cons_of_mem _ hv)) (by omega) (by omega)
        (hmap' _ fun y hy => isSome_get?_storeInt hy) ?_
      · intro r hr; rw [← hR r hr]; cases r <;> first | exact absurd rfl hr | rfl
      intro s' hs' hR'
      refine ev_congr (hK s' ?_ hR') (by simp [storesCode, SVal.code]; omega)
      rw [hs']; simp only [stores, SVal.val, Reg64s.set64_rax, Reg64s.get64_r8, Reg64s.get64_rax] at hr8 ⊢
      have h8 := hR .r8 (by decide)
      simp only [Reg64s.get64_r8] at h8
      rw [hr8]; simp [BinOp.eval, h8]

omit [Host] in
/-- A word whose signed value is not negative is below `2^63`. -/
theorem toNat_lt_of_not_toInt_neg (x : UInt64) (h : ¬ x.toBitVec.toInt < (0 : UInt64).toBitVec.toInt) :
    x.toNat < 2 ^ 63 := by
  have hx := x.toNat_lt
  rw [BitVec.toInt_eq_toNat_cond] at h
  simp only [UInt64.toNat_toBitVec, UInt64.toBitVec_zero, BitVec.toInt_zero] at h
  split at h <;> omega

/-- **The stub.** From `ca_setup`, with the region's first table words mapped: if `base_len`
(`r9`) is below `abiNeed`, or `in_len` (`rsi`) or `pins_len` (`rcx`) is `2^63` or more, the stub
returns with `rdx = 1`; otherwise it writes the table's words (`stores … (abiVals tab)`) and jumps
to `ca_enter` with `rdi = base`, `rsi = abiFuelM`, the other registers but `rax` unchanged. -/
theorem sim_abiStub (tab : Tab) (hok : abiTabOk tab = true) (k0 : Nat) (hc : Code (abiStub tab) k0)
    (Q : MachineState → Prop) (s : MachineData) (ra : Word)
    (hmap : abiNeed tab ≤ s.regs.r9.toNat →
      ∀ j < 8 * (abiVals tab).length, (s.dmem.get? (A (s.regs.r8.toNat + j))).isSome)
    (hend : abiNeed tab ≤ s.regs.r9.toNat → s.regs.r8.toNat + 8 * (abiVals tab).length ≤ 2 ^ 64)
    (hra : rdW s.dmem s.regs.rsp.toBitVec = some ra)
    (hdec : ∀ st : MachineState, st.pc = Int64.ofBitVec ra.toBitVec → st.data.regs.rdx = 1 →
      st.data.regs.rsp.toBitVec = s.regs.rsp.toBitVec + 8 → st.data.regs.rbp = s.regs.rbp →
      st.data.regs.r14 = s.regs.r14 → st.data.regs.r15 = s.regs.r15 → st.data.regs.rbx = s.regs.rbx →
      st.data.regs.r12 = s.regs.r12 → st.data.regs.r13 = s.regs.r13 → st.data.dmem = s.dmem → Q st)
    (hgo : abiNeed tab ≤ s.regs.r9.toNat → s.regs.rsi.toNat < 2 ^ 63 → s.regs.rcx.toNat < 2 ^ 63 →
      ∀ s' : MachineData,
      s'.dmem = stores s.regs s.regs.r8.toNat s.dmem 0 (abiVals tab) →
      s'.regs.rdi = s.regs.r8 → s'.regs.rsi.toNat = abiFuelM →
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → s'.regs.get64 r = s.regs.get64 r) →
      Ev Q s' (label enterL)) :
    Ev Q s (label abiSetupL) := by
  obtain ⟨hnb, htab, hneed⟩ := abiTabOk_spec hok
  have hlen := abiVals_length tab
  have hcH := hc.left.left
  have hcS := hc.left.right
  have hcT := hc.right
  simp only [abiHead] at hcH
  simp only [abiTail] at hcT
  rw [Code.label (i := 0) hcH rfl]
  refine ev_label (Code.get (i := 0) hcH rfl) ?_
  refine ev_movRI (Code.get (i := 1) hcH rfl) ?_
  refine ev_cmpRO (r := .r9) (o := oR .rax) (v := (abiNeed tab).toUInt64) (Code.get (i := 2) hcH rfl)
    (Or.inr (Or.inr ⟨.rax, rfl, rfl⟩)) ?_
  -- the decline: `rdx = 1`, the caller's registers but `rax`, `rdx` and the flags
  have hdecl : ∀ s0 : MachineData, s0.regs.rsp = s.regs.rsp → s0.regs.rbp = s.regs.rbp →
      s0.regs.r14 = s.regs.r14 → s0.regs.r15 = s.regs.r15 → s0.regs.rbx = s.regs.rbx →
      s0.regs.r12 = s.regs.r12 → s0.regs.r13 = s.regs.r13 → s0.dmem = s.dmem →
      Ev Q s0 (label abiDeclineL) := by
    intro s0 hsp hbp h14 h15 hbx h12 h13 hdm
    rw [Code.label (i := 3) hcT rfl]
    refine ev_label (Code.get (i := 3) hcT rfl) ?_
    refine ev_movRI (Code.get (i := 4) hcT rfl) ?_
    refine ev_movRI (Code.get (i := 5) hcT rfl) ?_
    refine ev_ret (Code.get (i := 6) hcT rfl) (ra := ra)
      (by simpa [Reg64s.set64_rax, Reg64s.set64_rdx, hsp, hdm] using hra) ?_
    exact Eventually.done _ (hdec _ rfl (by simp [Reg64s.set64_rax, Reg64s.set64_rdx, Reg64s.set64_rsp])
      (by simp [Reg64s.set64_rax, Reg64s.set64_rdx, Reg64s.set64_rsp, hsp])
      (by simp [Reg64s.set64_rax, Reg64s.set64_rdx, Reg64s.set64_rsp, hbp])
      (by simp [Reg64s.set64_rax, Reg64s.set64_rdx, Reg64s.set64_rsp, h14])
      (by simp [Reg64s.set64_rax, Reg64s.set64_rdx, Reg64s.set64_rsp, h15])
      (by simp [Reg64s.set64_rax, Reg64s.set64_rdx, Reg64s.set64_rsp, hbx])
      (by simp [Reg64s.set64_rax, Reg64s.set64_rdx, Reg64s.set64_rsp, h12])
      (by simp [Reg64s.set64_rax, Reg64s.set64_rdx, Reg64s.set64_rsp, h13]) hdm)
  refine ev_jcc (Code.get (i := 3) hcH rfl) (fun _ => hdecl _ rfl rfl rfl rfl rfl rfl rfl rfl) (fun hge => ?_)
  simp only [CondCode.interp, cmpFlags_cf, decide_eq_false_iff_not, Reg64s.get64_r9, Reg64s.set64_rax,
    UInt64.toNat_toBitVec, Nat.not_lt] at hge
  have hge' : abiNeed tab ≤ s.regs.r9.toNat := by
    simpa [Nat.toUInt64, UInt64.toNat_ofNat, Nat.mod_eq_of_lt hneed] using hge
  -- the buffer lengths: the top bit of `rsi`, then of `rcx`
  refine ev_cmpRO (r := .rsi) (o := oI 0) (v := 0) (Code.get (i := 4) hcH rfl) (Or.inl rfl) ?_
  refine ev_jcc (Code.get (i := 5) hcH rfl) (fun _ => hdecl _ rfl rfl rfl rfl rfl rfl rfl rfl) (fun hsi => ?_)
  refine ev_cmpRO (r := .rcx) (o := oI 0) (v := 0) (Code.get (i := 6) hcH rfl) (Or.inl rfl) ?_
  refine ev_jcc (Code.get (i := 7) hcH rfl) (fun _ => hdecl _ rfl rfl rfl rfl rfl rfl rfl rfl) (fun hcx => ?_)
  simp only [CondCode.interp, cmpFlags_sf_of, decide_eq_false_iff_not, Reg64s.get64_rsi, Reg64s.get64_rcx,
    Reg64s.set64_rax] at hsi hcx
  have hsi' : s.regs.rsi.toNat < 2 ^ 63 := toNat_lt_of_not_toInt_neg _ hsi
  have hcx' : s.regs.rcx.toNat < 2 ^ 63 := toNat_lt_of_not_toInt_neg _ hcx
  refine sim_stores Q s.regs s.regs.r8.toNat rfl (abiVals tab) 0 _ _ hcS ?_ (abiVals_noRax tab)
    (by omega) (by simpa using hend hge') (by simpa using hmap hge') ?_
  · intro r hr; cases r <;> first | exact absurd rfl hr | rfl
  intro s1 hs1 hR1
  have hk : k0 + 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + (storesCode 0 (abiVals tab)).length =
      k0 + (abiHead tab ++ storesCode 0 (abiVals tab)).length := by simp [abiHead]; omega
  rw [hk]
  refine ev_movRR (Code.get (i := 0) hcT rfl) ?_
  refine ev_movRI (Code.get (i := 1) hcT rfl) ?_
  refine ev_jmp (Code.get (i := 2) hcT rfl) ?_
  refine hgo hge' hsi' hcx' _ (by simpa using hs1) ?_ ?_ ?_
  · have := hR1 .r8 (by decide); simp at this
    simp [Reg64s.set64_rdi, Reg64s.set64_rsi, this]
  · simp [Reg64s.set64_rdi, Reg64s.set64_rsi, abiFuelM, abiFuel, abiInl]; rfl
  · intro r h1 h2 h3
    rw [← hR1 r h1]
    cases r <;> first | exact absurd rfl h1 | exact absurd rfl h2 | exact absurd rfl h3 | rfl


omit [Host] in
/-- **A word written before the stores reads as written after them**, when it is outside the
stores' range: the stores and the write commute, byte by byte. -/
theorem stores_wrW_get (R : Reg64s) (base : Nat) (vs : List SVal) (m : DataMem) (g : Nat)
    (v : BitVec 64) (hg : g + 8 ≤ 2 ^ 64) (hend : base + 8 * vs.length ≤ 2 ^ 64)
    (hdisj : g + 8 ≤ base ∨ base + 8 * vs.length ≤ g) (x : Nat) (hx : x < 2 ^ 64) :
    (stores R base (wrW m (A g) v) 0 vs).get? (A x) = (wrW (stores R base m 0 vs) (A g) v).get? (A x) := by
  have hO := stores_only R base vs (wrW m (A g) v) 0 (by simpa using hend)
  have hO' := stores_only R base vs m 0 (by simpa using hend)
  simp only [Nat.add_zero] at hO hO'
  by_cases hin : base ≤ x ∧ x < base + 8 * vs.length
  · obtain ⟨h1, h2⟩ := hin
    have hi : (x - base) / 8 < vs.length := by omega
    have hj : (x - base) % 8 < 8 := Nat.mod_lt _ (by omega)
    have e : x = base + 0 + 8 * ((x - base) / 8) + (x - base) % 8 := by omega
    rw [(Only.wrW hg).same x hx (by omega), e, stores_byte R base vs _ 0 _ _ hi hj (by simpa using hend),
      stores_byte R base vs _ 0 _ _ hi hj (by simpa using hend)]
  · rw [hO.same x hx (by omega)]
    by_cases hw : g ≤ x ∧ x < g + 8
    · obtain ⟨h1, h2⟩ := hw
      have e : x = g + (x - g) := by omega
      rw [e, get?_wrW_byte (by omega), get?_wrW_byte (by omega)]
    · rw [(Only.wrW hg).same x hx (by omega), (Only.wrW hg).same x hx (by omega), hO'.same x hx (by omega)]

end

end L.Compiler
