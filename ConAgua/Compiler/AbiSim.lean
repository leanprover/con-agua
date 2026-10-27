module

public import ConAgua.Compiler.Abi
public import ConAgua.Compiler.Rel
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

/-- What the stub needs of the table: two byte arrays, the table within the first `2^31` bytes
(the stores' displacements are 32-bit), and the region size below `2^64`. -/
def abiTabOk (tab : Tab) : Bool :=
  tab.nb == 2 && decide (16 + 16 * (tab.nb + tab.nw) + 8 * tab.romWords + 8 * tab.nxres + 8 * tab.ng + 32 ≤ 2 ^ 31) &&
    decide (abiNeed tab < 2 ^ 64)

theorem abiVals_length (tab : Tab) (h : tab.nb = 2) :
    (abiVals tab).length = 6 + 2 * tab.nw + tab.romWords := by
  simp only [abiVals, h, List.length_append, List.length_cons, List.length_nil, romVals_length,
    Tab.romWords, ← tab.romLen_eq]
  simp [List.length_flatMap, List.map_const']
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
    tab.nb = 2 ∧ 16 + 16 * (tab.nb + tab.nw) + 8 * tab.romWords + 8 * tab.nxres + 8 * tab.ng + 32 ≤ 2 ^ 31 ∧
      abiNeed tab < 2 ^ 64 := by
  simpa [abiTabOk, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h

theorem abiVals_noRax (tab : Tab) : ∀ v ∈ abiVals tab, v.noRax := by
  intro v hv
  simp only [abiVals, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_map, List.not_mem_nil, or_false] at hv
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
  rcases hv with (((((h | h | h | h) | h) | h) | h) | h) | h
  · subst h; trivial
  · subst h; trivial
  · subst h; simp [SVal.noRax]
  · subst h; simp [SVal.noRax]
  · split at h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> simp [SVal.noRax]
    · simp at h
  · obtain ⟨a, _, h | h⟩ := h <;> subst h <;> trivial
  · obtain ⟨a, _, rfl⟩ := h; trivial
  · obtain ⟨a, _, rfl⟩ := h; trivial
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

/-- The table words of a two-byte-array table, by position: word array `a`'s base at
`6 + wpos a`, its length at `6 + nw + wpos a`. -/
theorem abiVals_getElem? (tab : Tab) (h : tab.nb = 2) :
    (abiVals tab)[0]? = some (.addr (abiSlot + abiStack)) ∧ (abiVals tab)[1]? = some (.addr abiSlot) ∧
    (abiVals tab)[2]? = some (.reg .rdi) ∧ (abiVals tab)[3]? = some (.reg .rsi) ∧
    (abiVals tab)[4]? = some (.reg .rdx) ∧ (abiVals tab)[5]? = some (.reg .rcx) ∧
    (∀ a < tab.nw, (abiVals tab)[6 + tab.wpos a]? = some (.addr (abiSlot * abiSlot64 tab a)) ∧
      (abiVals tab)[6 + tab.nw + tab.wpos a]? = some (.imm abiWords.toUInt64)) ∧
    (∀ i, (abiVals tab)[6 + 2 * tab.nw + i]? = (romVals tab.rom)[i]?) := by
  have he : abiVals tab = [.addr (abiSlot + abiStack), .addr abiSlot, .reg .rdi, .reg .rsi, .reg .rdx, .reg .rcx] ++
      (List.range tab.nw).map (fun p => .addr (abiSlot * abiSlot64 tab (tab.wposInv p))) ++
      (List.range tab.nw).map (fun _ => .imm abiWords.toUInt64) ++
      romVals tab.rom := by
    simp [abiVals, h, show (List.range 2).drop 2 = [] from rfl]
  rw [he]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun a ha => ?_, fun i => ?_⟩
  · have hw := tab.wpos_lt ha
    constructor
    · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega),
        List.getElem?_append_right (by simp)]
      simp only [List.length_cons, List.length_nil, show 6 + tab.wpos a - (0 + 1 + 1 + 1 + 1 + 1 + 1) = tab.wpos a by omega,
        List.getElem?_map, List.getElem?_range hw, Option.map_some, tab.wposInv_wpos ha]
    · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp; omega)]
      simp only [List.length_append, List.length_cons, List.length_nil, List.length_map, List.length_range,
        show 6 + tab.nw + tab.wpos a - (0 + 1 + 1 + 1 + 1 + 1 + 1 + tab.nw) = tab.wpos a by omega,
        List.getElem?_map, List.getElem?_range hw, Option.map_some]
  · rw [List.getElem?_append_right (by simp; omega)]
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

/-! ## The layout the stub sets up -/

/-- The layout of the stub's partition: the table at `base`, the L stack in slot `1`, byte arrays
`0`/`1` the caller's buffers `[inp, inp + n)`, `[pins, pins + np)`, word array `a` in slot
`abiSlot64 tab a` with `abiWords` words. -/
def abiLayout (tab : Tab) (base inp n pins np : Nat) : Layout where
  tab
  T := base
  b8 a := if a = 0 then inp else if a = 1 then pins else base + abiSlot * abiSlot8 a
  s8 a := if a = 0 then n else if a = 1 then np else abiSlot
  b64 a := base + abiSlot * abiSlot64 tab a
  s64 _ := abiWords
  lo := base + abiSlot
  hi := base + abiSlot + abiStack
  nargs := 0

section
variable (tab : Tab) (base inp n pins np : Nat)
@[simp] theorem abiLayout_tab : (abiLayout tab base inp n pins np).tab = tab := rfl
@[simp] theorem abiLayout_T : (abiLayout tab base inp n pins np).T = base := rfl
@[simp] theorem abiLayout_b64 (a : Nat) : (abiLayout tab base inp n pins np).b64 a = base + abiSlot * abiSlot64 tab a := rfl
@[simp] theorem abiLayout_s64 (a : Nat) : (abiLayout tab base inp n pins np).s64 a = abiWords := rfl
@[simp] theorem abiLayout_lo : (abiLayout tab base inp n pins np).lo = base + abiSlot := rfl
@[simp] theorem abiLayout_hi : (abiLayout tab base inp n pins np).hi = base + abiSlot + abiStack := rfl
@[simp] theorem abiLayout_nargs : (abiLayout tab base inp n pins np).nargs = 0 := rfl
@[simp] theorem abiLayout_b8_0 : (abiLayout tab base inp n pins np).b8 0 = inp := rfl
@[simp] theorem abiLayout_b8_1 : (abiLayout tab base inp n pins np).b8 1 = pins := rfl
@[simp] theorem abiLayout_s8_0 : (abiLayout tab base inp n pins np).s8 0 = n := rfl
@[simp] theorem abiLayout_s8_1 : (abiLayout tab base inp n pins np).s8 1 = np := rfl
end

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

theorem abiLayout_ok {tab : Tab} (hok : abiTabOk tab = true) {base blen inp n pins np : Nat}
    (hg : AbiGeom tab base blen inp n pins np) : (abiLayout tab base inp n pins np).Ok := by
  obtain ⟨hnb, htab, -⟩ := abiTabOk_spec hok
  have hneed := hg.need
  have hfits := hg.fits
  simp only [abiNeed, hnb, abiSlot] at hneed
  have h2 : ∀ a, a < 2 → a = 0 ∨ a = 1 := by omega
  -- the bytes of byte array `a < 2` are outside the region
  have hb8 : ∀ a < 2, ∀ x, (abiLayout tab base inp n pins np).In8 a x → x < base ∨ base + blen ≤ x := by
    intro a ha x ⟨h3, h4⟩
    rcases h2 a ha with rfl | rfl
    · simp only [abiLayout_b8_0, abiLayout_s8_0] at h3 h4; exact hg.inDisj x h3 h4
    · simp only [abiLayout_b8_1, abiLayout_s8_1] at h3 h4; exact hg.pinsDisj x h3 h4
  constructor
  · simp only [Layout.tabEnd, abiLayout_T, abiLayout_tab, abiLayout_nargs]; omega
  · simp only [abiLayout_hi, abiSlot, abiStack]; omega
  · simp only [abiLayout_lo, abiLayout_hi]; omega
  · intro a ha; simp only [abiLayout_tab, hnb] at ha
    rcases h2 a ha with rfl | rfl
    · simpa using hg.inEnd
    · simpa using hg.pinsEnd
  · intro a ha
    simp only [abiLayout_tab] at ha
    simp only [abiLayout_b64, abiLayout_s64, abiSlot64, hnb, abiSlot, abiWords]; omega
  · intro x ⟨h1, h2'⟩ ⟨h3, h4⟩
    simp only [Layout.tabEnd, abiLayout_T, abiLayout_tab, abiLayout_nargs, abiLayout_lo, abiLayout_hi,
      abiSlot] at h1 h2' h3 h4; omega
  · intro x ⟨h1, h2'⟩ hx
    simp only [Layout.tabEnd, abiLayout_T, abiLayout_tab, abiLayout_nargs] at h1 h2'
    rcases hx with ⟨a, ha, hin⟩ | ⟨a, ha, h3, h4⟩
    · simp only [abiLayout_tab, hnb] at ha
      rcases hb8 a ha x hin with h | h <;> omega
    · simp only [abiLayout_tab] at ha
      simp only [abiLayout_b64, abiLayout_s64, abiSlot64, hnb, abiSlot, abiWords] at h3 h4; omega
  · intro x ⟨h1, h2'⟩ hx
    simp only [abiLayout_lo, abiLayout_hi, abiSlot, abiStack] at h1 h2'
    rcases hx with ⟨a, ha, hin⟩ | ⟨a, ha, h3, h4⟩
    · simp only [abiLayout_tab, hnb] at ha
      rcases hb8 a ha x hin with h | h <;> omega
    · simp only [abiLayout_tab] at ha
      simp only [abiLayout_b64, abiLayout_s64, abiSlot64, hnb, abiSlot, abiWords] at h3 h4; omega
  · intro a ha b hb hab x ⟨h3, h4⟩ ⟨h5, h6⟩
    simp only [abiLayout_tab, hnb] at ha hb
    rcases h2 a ha with rfl | rfl <;> rcases h2 b hb with rfl | rfl
    · exact hab rfl
    · simp only [abiLayout_b8_0, abiLayout_s8_0, abiLayout_b8_1, abiLayout_s8_1] at h3 h4 h5 h6
      exact hg.bufDisj x h3 h4 ⟨h5, h6⟩
    · simp only [abiLayout_b8_0, abiLayout_s8_0, abiLayout_b8_1, abiLayout_s8_1] at h3 h4 h5 h6
      exact hg.bufDisj x h5 h6 ⟨h3, h4⟩
    · exact hab rfl
  · intro a ha b hb hab x ⟨h3, h4⟩ ⟨h5, h6⟩
    simp only [abiLayout_b64, abiLayout_s64, abiSlot64, hnb, abiSlot, abiWords] at h3 h4 h5 h6
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · have : 2 ^ 35 * (2 + (2 - 2) + a) + 2 ^ 35 ≤ 2 ^ 35 * (2 + (2 - 2) + b) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
      omega
    · have : 2 ^ 35 * (2 + (2 - 2) + b) + 2 ^ 35 ≤ 2 ^ 35 * (2 + (2 - 2) + a) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
      omega
  · intro a ha b hb x hin ⟨h5, h6⟩
    simp only [abiLayout_tab, hnb] at ha hb
    simp only [abiLayout_b64, abiLayout_s64, abiSlot64, hnb, abiSlot, abiWords] at h5 h6
    rcases hb8 a ha x hin with h | h <;> omega

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
to `ca_enter` with `rdi = base`, `rsi = abiFuel`, the other registers but `rax` unchanged. -/
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
      s'.regs.rdi = s.regs.r8 → s'.regs.rsi.toNat = abiFuel →
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → s'.regs.get64 r = s.regs.get64 r) →
      Ev Q s' (label enterL)) :
    Ev Q s (label abiSetupL) := by
  obtain ⟨hnb, htab, hneed⟩ := abiTabOk_spec hok
  have hlen := abiVals_length tab hnb
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
  · simp [Reg64s.set64_rdi, Reg64s.set64_rsi, abiFuel]; rfl
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
