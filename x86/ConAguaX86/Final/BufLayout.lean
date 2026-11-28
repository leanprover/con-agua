module

public import ConAgua.Arena.FreezeRel
public import ConAguaX86.Compiler.AbiSim

@[expose] public section

/-!
# The threads' entry 2: `ca_check_b`'s layout and memory (lane parmode)

`ca_check_b(buf, buf_len, j, region, region_len)` (`parStub`, `ConAgua/Compiler/Abi.lean`) lays out
one call of `check` on a worker region `[base, base + blen)` and the read-only frozen buffer
`[buf, buf + 8·|B|)` holding the words `B`:

* `bufLayout`: the table at `base` (slot `0`), the L stack in slot `1`, frozen array `fz[i]` at
  `buf + 8·off_i` with `len_i` words (the buffer's header entry `i`, `bufEntry B i`), owned array
  `own[k]` in slot `1 + k` with `abiWords` words (`own[0]`, the table-relative array, inside slot
  `0`), every other array (and both byte arrays)
  `(0, 0)`. `bufLayout_ok` under `BufGeom` (the buffer's header inside the buffer, its entries
  inside the buffer and pairwise apart, the buffer apart from the region).
* `RegionRel tab base own r d`: what the call needs of the region's memory `d`: the owned arrays and
  the globals of the L memory `r` in place. A zero region holds the zero memory; a region a call
  left holds that call's final memory (`RegionRel.of_memRel`).
* `bufMemG`: the L memory of one call (generic in the frozen and owned lists and the globals;
  `bufMem` of `ConAgua/Arena/FreezeRel.lean` is `bufMemG frozenIdsL parOwnedL PLO PHI MODE`).
* `qwrs`: word writes at `T + 8q` (the stub's table stores, in any order), and `buf_memRel`: after
  the stores of every table word (`bufVal`), the region and the buffer hold `bufMemG`'s memory
  before the globals.
-/

namespace ConAgua.Final

open L L.Compiler L.Arena

/-! ## Word writes at `T + 8q` -/

/-- The memory after writing `val q` at `T + 8q` for `q` in `qs`, in order. -/
def qwrs (T : Nat) (val : Nat → BitVec 64) : DataMem → List Nat → DataMem
  | d, [] => d
  | d, q :: qs => qwrs T val (wrW d (A (T + 8 * q)) (val q)) qs

section
variable {T : Nat} {val : Nat → BitVec 64}

theorem qwrs_append (d : DataMem) (l₁ l₂ : List Nat) :
    qwrs T val d (l₁ ++ l₂) = qwrs T val (qwrs T val d l₁) l₂ := by
  induction l₁ generalizing d with
  | nil => rfl
  | cons q qs ih => exact ih _

theorem qwrs_grows : ∀ (qs : List Nat) (d : DataMem) y, (d.get? y).isSome → ((qwrs T val d qs).get? y).isSome
  | [], _, _, h => h
  | _ :: qs, _, y, h => qwrs_grows qs _ y (isSome_get?_storeInt h)

theorem qwrs_out : ∀ (qs : List Nat) (d : DataMem) (x : Nat), x < 2 ^ 64 → (∀ q ∈ qs, T + 8 * q + 8 ≤ 2 ^ 64) →
    (∀ q ∈ qs, x < T + 8 * q ∨ T + 8 * q + 8 ≤ x) → (qwrs T val d qs).get? (A x) = d.get? (A x)
  | [], _, _, _, _, _ => rfl
  | q :: qs, d, x, hx, hfit, hout => by
    simp only [qwrs]
    rw [qwrs_out qs _ x hx (fun q h => hfit q (List.mem_cons_of_mem _ h))
      (fun q h => hout q (List.mem_cons_of_mem _ h))]
    exact get?_wrW_A (hfit q List.mem_cons_self) hx (hout q List.mem_cons_self)

theorem qwrs_byte : ∀ (qs : List Nat) (d : DataMem) (q₀ j : Nat), q₀ ∈ qs → j < 8 →
    (∀ q ∈ qs, T + 8 * q + 8 ≤ 2 ^ 64) →
    (qwrs T val d qs).get? (A (T + 8 * q₀ + j)) = (UInt64.ofBitVec (val q₀)).toBytes[j]?
  | [], _, _, _, h, _, _ => absurd h (by simp)
  | q :: qs, d, q₀, j, hq, hj, hfit => by
    simp only [qwrs]
    by_cases hm : q₀ ∈ qs
    · exact qwrs_byte qs _ q₀ j hm hj fun q h => hfit q (List.mem_cons_of_mem _ h)
    · have e : q = q₀ := by
        rcases List.mem_cons.mp hq with h | h
        · exact h.symm
        · exact absurd h hm
      subst e
      have h0 := hfit q List.mem_cons_self
      rw [qwrs_out qs _ _ (by omega) (fun q h => hfit q (List.mem_cons_of_mem _ h)) ?_]
      · exact get?_wrW_byte hj
      · intro q' hq'
        have : q' ≠ q := fun h => hm (h ▸ hq')
        rcases Nat.lt_or_gt_of_ne this with h | h <;> omega

theorem qwrs_rdW (qs : List Nat) (d : DataMem) (q₀ : Nat) (hq : q₀ ∈ qs)
    (hfit : ∀ q ∈ qs, T + 8 * q + 8 ≤ 2 ^ 64) :
    rdW (qwrs T val d qs) (A (T + 8 * q₀)) = some (UInt64.ofBitVec (val q₀)) := by
  rw [← rdW_wrW_same d (A (T + 8 * q₀)) (val q₀)]
  refine rdW_congr fun j hj => ?_
  rw [A_add, qwrs_byte qs d q₀ j hq hj hfit, get?_wrW_byte hj]

theorem qwrs_only (qs : List Nat) (d : DataMem) (N : Nat) (hN : T + 8 * N ≤ 2 ^ 64) (hq : ∀ q ∈ qs, q < N) :
    Only T (T + 8 * N) d (qwrs T val d qs) :=
  ⟨qwrs_grows qs d, fun x hx hout => qwrs_out qs d x hx (fun q h => by have := hq q h; omega)
    (fun q h => by have := hq q h; omega)⟩

end

/-! ## The layout -/

/-- Word array `a`'s base in `ca_check_b`'s layout. -/
def bufB (tab : Tab) (B : Array Word) (buf base : Nat) (fz own : List TieredArray) (a : TieredArray) : Nat :=
  match fz.idxOf? a with
  | some i => buf + 8 * (bufEntry B i).1
  | none =>
    match own.idxOf? a with
    | some k => base + ownOff tab a k
    | none => 0

/-- Word array `a`'s length in `ca_check_b`'s layout. -/
def bufL (tab : Tab) (B : Array Word) (fz own : List TieredArray) (a : TieredArray) : Nat :=
  match fz.idxOf? a with
  | some i => (bufEntry B i).2
  | none =>
    match own.idxOf? a with
    | some _ => abiSz tab a
    | none => 0

/-- **`ca_check_b`'s layout**: the table at `base`, the stack in slot `1`, frozen array `fz[i]` at
the buffer's entry `i`, owned array `own[k]` in slot `1 + k` (the table-relative one, `own[0]`,
inside slot `0`, `ownOff`); descriptor position `p` holds the word array `tab.wAt p`. -/
def bufLayout (tab : Tab) (buf : Nat) (B : Array Word) (base : Nat) (fz own : List TieredArray) :
    L.Compiler.Layout where
  tab
  T := base
  b p := if p < tab.nb then 0 else bufB tab B buf base fz own (tab.wAt p)
  s p := if p < tab.nb then 0 else bufL tab B fz own (tab.wAt p)
  lo := base + abiSlot
  hi := base + abiSlot + abiStack
  nargs := 0

section
variable (tab : Tab) (buf : Nat) (B : Array Word) (base : Nat) (fz own : List TieredArray)
@[simp] theorem bufLayout_tab : (bufLayout tab buf B base fz own).tab = tab := rfl
@[simp] theorem bufLayout_T : (bufLayout tab buf B base fz own).T = base := rfl
theorem bufLayout_b8 {p : Nat} (hp : p < tab.nb) : (bufLayout tab buf B base fz own).b p = 0 := by
  simp [bufLayout, hp]
theorem bufLayout_s8 {p : Nat} (hp : p < tab.nb) : (bufLayout tab buf B base fz own).s p = 0 := by
  simp [bufLayout, hp]
theorem bufLayout_b64 {p : Nat} (hp : tab.nb ≤ p) :
    (bufLayout tab buf B base fz own).b p = bufB tab B buf base fz own (tab.wAt p) := by
  simp [bufLayout, show ¬ p < tab.nb by omega]
theorem bufLayout_s64 {p : Nat} (hp : tab.nb ≤ p) :
    (bufLayout tab buf B base fz own).s p = bufL tab B fz own (tab.wAt p) := by
  simp [bufLayout, show ¬ p < tab.nb by omega]
@[simp] theorem bufLayout_lo : (bufLayout tab buf B base fz own).lo = base + abiSlot := rfl
@[simp] theorem bufLayout_hi : (bufLayout tab buf B base fz own).hi = base + abiSlot + abiStack := rfl
@[simp] theorem bufLayout_nargs : (bufLayout tab buf B base fz own).nargs = 0 := rfl
end

/-- **The geometry of one `ca_check_b` call**: the region `[base, base + blen)` holds the table,
the stack and the owned arrays and is in the address space; the buffer `[buf, buf + 8·|B|)` is
in the address space and apart from the region; its header (words `8 + 2i`, `9 + 2i`) is inside
it, and its entries are inside it and pairwise apart (or empty). -/
structure BufGeom (tab : Tab) (fz own : List TieredArray) (B : Array Word) (buf base blen : Nat) : Prop where
  need : workerNeed own ≤ blen
  fits : base + blen < 2 ^ 64
  bend : buf + 8 * B.size < 2 ^ 64
  hdr : ∀ i < fz.length, 9 + 2 * i < B.size
  ent : ∀ i < fz.length, (bufEntry B i).1 + (bufEntry B i).2 ≤ B.size
  disj : ∀ i < fz.length, ∀ i' < fz.length, i ≠ i' →
    (bufEntry B i).1 + (bufEntry B i).2 ≤ (bufEntry B i').1 ∨
    (bufEntry B i').1 + (bufEntry B i').2 ≤ (bufEntry B i).1 ∨ (bufEntry B i).2 = 0 ∨ (bufEntry B i').2 = 0
  apart : ∀ x, buf ≤ x → x < buf + 8 * B.size → x < base ∨ base + blen ≤ x

theorem idxOf?_lt {l : List TieredArray} {a : TieredArray} {i : Nat} (h : l.idxOf? a = some i) :
    i < l.length := by
  have := List.idxOf?_eq_some_iff.mp h
  exact this.1

theorem idxOf?_inj {l : List TieredArray} {a b : TieredArray} {i : Nat} (ha : l.idxOf? a = some i) (hb : l.idxOf? b = some i) :
    a = b := by
  obtain ⟨hl, e1, -⟩ := List.idxOf?_eq_some_iff.mp ha
  obtain ⟨hl', e2, -⟩ := List.idxOf?_eq_some_iff.mp hb
  exact e1.symm.trans e2

/-- **The minimum lengths in `ca_check_b`'s layout, statically**: an array with a minimum length
(`Tab.min64`) is frozen (its length is the buffer's, which the stub tests: `bufMinChk`) or owned
(a slot of `abiWords` words); every other array gets no memory. Positions the layout gives no
array (`dom64`) are skipped. The table-relative array (`Tab.tbl`) is owned, the first of `own`,
and not frozen: the stub places it inside the table's slot, so `own[k]` for `k ≥ 1` takes slot
`1 + k` (`ownOff`). Without a table-relative array nothing is owned. -/
def bufMinOk (tab : Tab) (fz own : List TieredArray) : Bool :=
  ((List.range (tab.nb + tab.nw)).all fun p =>
    !tab.dom64 (tab.wAt p) || tab.min64 (tab.wAt p) == 0 || fz.contains (tab.wAt p) ||
      own.contains (tab.wAt p)) &&
  match tab.tbl with
  | none => own.isEmpty
  | some (a, _) => own.head? == some (TieredArray.t0 a) && !fz.contains (TieredArray.t0 a)

theorem bufMinOk_tbl {tab : Tab} {fz own : List TieredArray} (h : bufMinOk tab fz own = true)
    {s : TieredArray} {c : Nat} (hc : tab.tbl64 s = some c) : own.contains s = true ∧ fz.contains s = false := by
  obtain ⟨a, ht, rfl⟩ := Tab.tbl64_some hc
  have h2 := ((Bool.and_eq_true _ _).mp h).2
  simp only [ht, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h2
  refine ⟨?_, h2.2⟩
  cases own with
  | nil => simp at h2
  | cons b l => simp only [List.head?_cons, Option.some.injEq] at h2; simp [h2.1]

/-- An owned array outside the table's slot is not `own[0]`. -/
theorem bufMinOk_pos {tab : Tab} {fz own : List TieredArray} (h : bufMinOk tab fz own = true)
    {s : TieredArray} {k : Nat} (hk : own.idxOf? s = some k) (hs : tab.tbl64 s = none) : 1 ≤ k := by
  obtain ⟨hl, e, -⟩ := List.idxOf?_eq_some_iff.mp hk
  refine Nat.pos_of_ne_zero fun h0 => ?_
  subst h0
  have h2 := ((Bool.and_eq_true _ _).mp h).2
  cases own with
  | nil => simp at hl
  | cons b l =>
    simp only [List.getElem_cons_zero] at e
    subst e
    cases ht : tab.tbl with
    | none => simp [ht] at h2
    | some ac =>
      obtain ⟨a, c⟩ := ac
      simp only [ht, Bool.and_eq_true, beq_iff_eq, List.head?_cons, Option.some.injEq] at h2
      rw [h2.1, Tab.tbl64_t0 ht] at hs; cases hs

theorem ownOff_slot {tab : Tab} {s : TieredArray} {k : Nat} (h : tab.tbl64 s = none) :
    ownOff tab s k = abiSlot * (1 + k) := by simp only [ownOff, h]

theorem ownOff_tbl {tab : Tab} {s : TieredArray} {k c : Nat} (h : tab.tbl64 s = some c) :
    ownOff tab s k = c := by simp only [ownOff, h]

/-- The bytes of `InTbl` are in the worker's region. -/
theorem _root_.L.Compiler.InTbl.region {tab : Tab} {fz own : List TieredArray} {B : Array Word} {buf base blen x : Nat}
    (hg : BufGeom tab fz own B buf base blen) (h : InTbl tab base x) : base ≤ x ∧ x < base + blen := by
  have hn := hg.need; unfold workerNeed at hn; unfold InTbl at h
  simp only [abiSlot] at hn; omega

/-- The bytes of owned array `s` (number `k`): in slot `1 + k`, or (the table-relative array) in
`InTbl`. -/
theorem own_bytes {tab : Tab} (hok : abiTabOk tab = true) {s : TieredArray} {k base x : Nat}
    (h1 : base + ownOff tab s k ≤ x) (h2 : x < base + ownOff tab s k + 8 * abiSz tab s) :
    (tab.tbl64 s = none ∧ InSlot base (1 + k) x) ∨ ((∃ c, tab.tbl64 s = some c) ∧ InTbl tab base x) := by
  cases hc : tab.tbl64 s with
  | none =>
    rw [ownOff_slot hc] at h1 h2; rw [abiSz_slot hc] at h2
    exact .inl ⟨rfl, h1, by simp only [abiSlot, abiWords] at h2 ⊢; omega⟩
  | some c =>
    rw [ownOff_tbl hc] at h1 h2; rw [abiSz_tbl hc] at h2
    have := abiTabOk_tbl hok hc
    exact .inr ⟨⟨c, rfl⟩, by omega, by omega⟩

theorem idxOf?_of_contains {l : List TieredArray} {a : TieredArray} (h : l.contains a = true) :
    ∃ k, l.idxOf? a = some k := by
  have hm : a ∈ l := by simpa using h
  exact Option.isSome_iff_exists.mp (by simpa [List.isSome_idxOf?] using hm)

theorem idxOf?_of_not_contains {l : List TieredArray} {a : TieredArray} (h : ¬ l.contains a = true) :
    l.idxOf? a = none := by
  have hm : a ∉ l := by simpa using h
  simpa [List.idxOf?_eq_none_iff] using hm

section
variable {tab : Tab} {fz own : List TieredArray} {B : Array Word} {buf base blen : Nat}

/-- A byte of the word array at position `p` is in the buffer (frozen), or in the region's slot
`1 + k` or (the table-relative array) in `InTbl` (owned). -/
theorem buf_in64 (hok : abiTabOk tab = true) (_hg : BufGeom tab fz own B buf base blen) {p x : Nat}
    (hp : tab.nb ≤ p) (h : (bufLayout tab buf B base fz own).In64 p x) :
    (∃ i, fz.idxOf? (tab.wAt p) = some i ∧ buf + 8 * (bufEntry B i).1 ≤ x ∧
        x < buf + 8 * ((bufEntry B i).1 + (bufEntry B i).2)) ∨
      (fz.idxOf? (tab.wAt p) = none ∧ ∃ k, own.idxOf? (tab.wAt p) = some k ∧
        ((tab.tbl64 (tab.wAt p) = none ∧ InSlot base (1 + k) x) ∨
          ((∃ c, tab.tbl64 (tab.wAt p) = some c) ∧ InTbl tab base x))) := by
  unfold Layout.In64 at h
  simp only [bufLayout_b64 _ _ _ _ _ _ hp, bufLayout_s64 _ _ _ _ _ _ hp] at h
  generalize tab.wAt p = a at h ⊢
  simp only [bufB, bufL] at h
  split at h
  · rename_i i hi
    exact Or.inl ⟨i, hi, by omega, by omega⟩
  · rename_i hn
    split at h
    · rename_i k hk
      exact Or.inr ⟨hn, k, hk, own_bytes hok h.1 h.2⟩
    · omega

theorem buf_inTab (hok : abiTabOk tab = true) {x : Nat}
    (h : (bufLayout tab buf B base fz own).InTab x) : InSlot base 0 x ∧
      x < base + (16 + 24 * (tab.nb + tab.nw) + 8 * tab.romWords + 8 * tab.nxres + 8 * tab.ng) := by
  obtain ⟨-, htab, -⟩ := abiTabOk_spec hok
  unfold Layout.InTab Layout.tabEnd at h
  simp only [bufLayout_T, bufLayout_tab, bufLayout_nargs] at h
  unfold InSlot abiSlot; omega

theorem buf_inStack {x : Nat} (h : (bufLayout tab buf B base fz own).InStack x) : InSlot base 1 x := by
  unfold Layout.InStack at h
  simp only [bufLayout_lo, bufLayout_hi] at h
  unfold InSlot; simp only [abiSlot, abiStack] at h ⊢; omega

theorem buf_notIn8 {p x : Nat} (hp : p < tab.nb) : ¬ (bufLayout tab buf B base fz own).In p x := by
  unfold Layout.In; rw [bufLayout_b8 _ _ _ _ _ _ hp, bufLayout_s8 _ _ _ _ _ _ hp]; omega

/-- A byte of the layout's arrays: at a word position. -/
theorem buf_inArr {x : Nat} (h : (bufLayout tab buf B base fz own).InArr x) :
    ∃ p, tab.nb ≤ p ∧ p < tab.nb + tab.nw ∧ (bufLayout tab buf B base fz own).In64 p x := by
  obtain ⟨p, hp, hx⟩ := h
  simp only [bufLayout_tab] at hp
  by_cases hb : p < tab.nb
  · exact absurd hx (buf_notIn8 hb)
  · exact ⟨p, by omega, hp, Layout.In.to64 (by simp only [bufLayout_tab]; omega) hx⟩

/-- Bytes of the region's slots `< 2 + (|own| - 1)` are in the region. -/
theorem _root_.L.Compiler.InSlot.region (hg : BufGeom tab fz own B buf base blen) {j x : Nat} (h : InSlot base j x)
    (hj : j < 2 + (own.length - 1)) : base ≤ x ∧ x < base + blen := by
  have := h.lt hj
  have hn := hg.need
  unfold workerNeed at hn
  unfold InSlot at h
  omega

/-- An owned array's bytes are in the region. -/
theorem own_region (hg : BufGeom tab fz own B buf base blen) {k x : Nat} (hk : k < own.length)
    (h : (InSlot base (1 + k) x) ∨ InTbl tab base x) : base ≤ x ∧ x < base + blen := by
  rcases h with h | h
  · exact h.region hg (by omega)
  · exact h.region hg

/-- A byte of the layout's table, stack or an owned array is in the region; a frozen byte is in
the buffer. -/
theorem buf_part (hok : abiTabOk tab = true) (hg : BufGeom tab fz own B buf base blen) {x : Nat}
    (h : (bufLayout tab buf B base fz own).InStack x ∨ (bufLayout tab buf B base fz own).InArr x ∨
      (bufLayout tab buf B base fz own).InTab x) :
    (base ≤ x ∧ x < base + blen) ∨ (buf ≤ x ∧ x < buf + 8 * B.size) := by
  rcases h with h | h | h
  · exact Or.inl ((buf_inStack h).region hg (by omega))
  · obtain ⟨p, hp1, -, h⟩ := buf_inArr h
    rcases buf_in64 hok hg hp1 h with ⟨i, hi, h1, h2⟩ | ⟨-, k, hk, hs⟩
    · have := hg.ent i (idxOf?_lt hi); right; omega
    · exact Or.inl (own_region hg (idxOf?_lt hk) (hs.imp (fun h => h.2) (fun h => h.2)))
  · exact Or.inl ((buf_inTab hok h).1.region hg (by omega))

/-- The trampoline's save area (the 32 bytes past the table) is in the region's table slot, in
no array and not in the L stack. -/
theorem buf_save (hok : abiTabOk tab = true) (hg : BufGeom tab fz own B buf base blen) {x : Nat}
    (h1 : (bufLayout tab buf B base fz own).tabEnd ≤ x) (h2 : x < (bufLayout tab buf B base fz own).tabEnd + 32) :
    base ≤ x ∧ x < base + blen ∧ ¬ (bufLayout tab buf B base fz own).InStack x ∧
      ¬ (bufLayout tab buf B base fz own).InArr x := by
  obtain ⟨-, htab, -⟩ := abiTabOk_spec hok
  have hn := hg.need
  unfold workerNeed at hn
  simp only [Layout.tabEnd, bufLayout_T, bufLayout_tab, bufLayout_nargs] at h1 h2
  have hx : x < base + 2 ^ 31 := by omega
  refine ⟨by omega, by simp only [abiSlot] at hn; omega, fun h => ?_, fun h => ?_⟩
  · have := buf_inStack h
    unfold InSlot abiSlot at this; omega
  · obtain ⟨p, hp1, -, h⟩ := buf_inArr h
    · rcases buf_in64 hok hg hp1 h with ⟨i, hi, h3, h4⟩ | ⟨-, k, -, ⟨-, h3⟩ | ⟨-, h3⟩⟩
      · have := hg.ent i (idxOf?_lt hi)
        rcases hg.apart x (by omega) (by omega) with h5 | h5
        · omega
        · simp only [abiSlot] at hn; omega
      · have : abiSlot * 1 ≤ abiSlot * (1 + k) := Nat.mul_le_mul_left _ (by omega)
        unfold InSlot at h3; simp only [abiSlot] at this h3; omega
      · unfold InTbl at h3; omega

theorem bufLayout_ok (hok : abiTabOk tab = true) (hg : BufGeom tab fz own B buf base blen)
    (hmo : bufMinOk tab fz own = true)
    (hmin : ∀ i (h : i < fz.length), tab.min64 fz[i] ≤ (bufEntry B i).2) :
    (bufLayout tab buf B base fz own).Ok := by
  obtain ⟨hnb, htab, -⟩ := abiTabOk_spec hok
  have hn := hg.need
  have hf := hg.fits
  have hbe := hg.bend
  unfold workerNeed at hn
  constructor
  · simp only [Layout.tabEnd, bufLayout_T, bufLayout_tab, bufLayout_nargs]; simp only [abiSlot] at hn; omega
  · simp only [bufLayout_hi, abiSlot, abiStack]; simp only [abiSlot] at hn; omega
  · simp only [bufLayout_lo, bufLayout_hi]; omega
  · intro a ha
    simp only [bufLayout_tab] at ha ⊢
    by_cases hb : a < tab.nb
    · rw [bufLayout_b8 _ _ _ _ _ _ hb, bufLayout_s8 _ _ _ _ _ _ hb]; omega
    rw [bufLayout_b64 _ _ _ _ _ _ (by omega), bufLayout_s64 _ _ _ _ _ _ (by omega),
      show tab.wd a = 8 by simp [Tab.wd, hb]]
    generalize tab.wAt a = s
    simp only [bufB, bufL]
    split
    · rename_i i hi
      have := hg.ent i (idxOf?_lt hi); omega
    · split
      · rename_i k hk
        have hk' := idxOf?_lt hk
        cases hc : tab.tbl64 s with
        | none =>
          rw [ownOff_slot hc, abiSz_slot hc]
          have hle : abiSlot * (1 + k) + abiSlot ≤ abiSlot * (2 + (own.length - 1)) := by
            rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
          simp only [abiSlot, abiWords] at hle hn ⊢; omega
        | some c =>
          rw [ownOff_tbl hc, abiSz_tbl hc]
          have := abiTabOk_tbl hok hc; simp only [abiSlot] at hn; omega
      · simp
  · intro x h1 h2
    exact absurd (InSlot.eq (buf_inTab hok h1).1 (buf_inStack h2)) (by omega)
  · intro x h1 h2
    obtain ⟨p, hp1, -, h⟩ := buf_inArr h2
    · have ht := (buf_inTab hok h1).1.region hg (by omega)
      have ht2 := (buf_inTab hok h1).2
      rcases buf_in64 hok hg hp1 h with ⟨i, hi, q1, q2⟩ | ⟨-, k, hk, ⟨-, hs⟩ | ⟨-, hs⟩⟩
      · have := hg.ent i (idxOf?_lt hi)
        rcases hg.apart x (by omega) (by omega) with h' | h' <;> omega
      · exact absurd (InSlot.eq (buf_inTab hok h1).1 hs) (by omega)
      · unfold InTbl at hs; omega
  · intro x h1 h2
    obtain ⟨p, hp1, -, h⟩ := buf_inArr h2
    · have ht := (buf_inStack h1).region hg (by omega)
      rcases buf_in64 hok hg hp1 h with ⟨i, hi, q1, q2⟩ | ⟨-, k, hk, ⟨hc, hs⟩ | ⟨-, hs⟩⟩
      · have := hg.ent i (idxOf?_lt hi)
        rcases hg.apart x (by omega) (by omega) with h' | h' <;> omega
      · have := bufMinOk_pos hmo hk hc
        exact absurd (InSlot.eq (buf_inStack h1) hs) (by omega)
      · exact hs.not_slot (Nat.le_refl _) (buf_inStack h1)
  · intro a ha b hb hab' x h1 h2
    simp only [bufLayout_tab] at ha hb
    by_cases hba : a < tab.nb
    · exact absurd h1 (buf_notIn8 hba)
    by_cases hbb : b < tab.nb
    · exact absurd h2 (buf_notIn8 hbb)
    replace h1 := Layout.In.to64 (by simp only [bufLayout_tab]; omega) h1
    replace h2 := Layout.In.to64 (by simp only [bufLayout_tab]; omega) h2
    have hab : tab.wAt a ≠ tab.wAt b := fun e => hab' (tab.wAt_inj ha hb e)
    rcases buf_in64 hok hg (by omega) h1 with ⟨i, hi, p1, p2⟩ | ⟨hn1, k, hk, hs⟩ <;>
      rcases buf_in64 hok hg (by omega) h2 with ⟨i', hi', p3, p4⟩ | ⟨hn2, k', hk', hs'⟩
    · have hii : i ≠ i' := fun e => hab (idxOf?_inj hi (e ▸ hi'))
      rcases hg.disj i (idxOf?_lt hi) i' (idxOf?_lt hi') hii with h | h | h | h <;> omega
    · have := hg.ent i (idxOf?_lt hi)
      have hr := own_region hg (idxOf?_lt hk') (hs'.imp (fun h => h.2) (fun h => h.2))
      rcases hg.apart x (by omega) (by omega) with h' | h' <;> omega
    · have := hg.ent i' (idxOf?_lt hi')
      have hr := own_region hg (idxOf?_lt hk) (hs.imp (fun h => h.2) (fun h => h.2))
      rcases hg.apart x (by omega) (by omega) with h' | h' <;> omega
    · rcases hs with ⟨-, hs⟩ | ⟨⟨c, hc⟩, ht⟩ <;> rcases hs' with ⟨-, hs'⟩ | ⟨⟨c', hc'⟩, ht'⟩
      · have e := InSlot.eq hs hs'
        exact hab (idxOf?_inj hk (by rw [show k = k' by omega]; exact hk'))
      · exact ht'.not_slot (by omega) hs
      · exact ht.not_slot (by omega) hs'
      · obtain ⟨a1, e1, s1⟩ := Tab.tbl64_some hc
        obtain ⟨a2, e2, s2⟩ := Tab.tbl64_some hc'
        rw [e1] at e2; cases e2
        exact hab (s1.trans s2.symm)
  · intro s hs
    simp only [bufLayout_tab] at hs ⊢
    have hps := tab.pos64_lt hs
    have hp := List.all_eq_true.mp ((Bool.and_eq_true _ _).mp hmo).1 _ (List.mem_range.mpr hps.2)
    rw [bufLayout_s64 _ _ _ _ _ _ hps.1]
    rw [tab.wAt_pos64 hs] at hp ⊢
    simp only [bufL]
    split
    · rename_i i hi
      obtain ⟨hl, e1, -⟩ := List.idxOf?_eq_some_iff.mp hi
      have := hmin i hl
      rwa [e1] at this
    · rename_i hn
      split
      · exact min64_le_abiSz hok s
      · rename_i hn'
        simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hp
        rcases hp with ((hp | hp) | hp) | hp
        · rw [hs] at hp; cases hp
        · exact Nat.le_of_eq hp
        · obtain ⟨k, hk⟩ := idxOf?_of_contains hp; rw [hn] at hk; cases hk
        · obtain ⟨k, hk⟩ := idxOf?_of_contains hp; rw [hn'] at hk; cases hk
  · intro s c hs hc
    simp only [bufLayout_tab, bufLayout_T] at hs hc ⊢
    rw [bufLayout_b64 _ _ _ _ _ _ (tab.pos64_lt hs).1, tab.wAt_pos64 hs]
    obtain ⟨ho, hf⟩ := bufMinOk_tbl hmo hc
    obtain ⟨k, hk⟩ := idxOf?_of_contains ho
    simp only [bufB, idxOf?_of_not_contains (by rw [hf]; decide), hk, ownOff_tbl hc]

end

/-! ## The memory -/

/-- **What a call needs of the region's memory `d`**: the owned arrays and the globals of the L
memory `r` in place (`own[k]` at `ownOff`, in slot `1 + k` or the table-relative array inside the
table's slot, with `abiSz` words; the globals in the table at `base`). -/
structure RegionRel (tab : Tab) (base : Nat) (own : List TieredArray) (r : Mem) (d : DataMem) : Prop where
  size : ∀ s, tab.dom64 s = true → ∀ k, own.idxOf? s = some k → (r.arr64 s).size = abiSz tab s
  get : ∀ s, tab.dom64 s = true → ∀ k, own.idxOf? s = some k → ∀ i (h : i < (r.arr64 s).size),
    rdW d (A (base + ownOff tab s k + 8 * i)) = some (r.arr64 s)[i]
  glob : ∀ g : GVar, g.id < tab.ng → rdW d (A (base + (tab.globOff g).toNat)) = some (r.glob g)

/-- `ca_check_b`'s memory before the globals: frozen array `fz[i]` is the buffer's entry `i`, the
owned arrays are `r`'s, every other array is empty; `r`'s globals. -/
def bufMem0 (fz own : List TieredArray) (B : Array Word) (r : Mem) : Mem where
  bytes _ := #[]
  words s := match fz.idxOf? s with
    | some i => bufImg B i
    | none => if own.contains s then r.arr64 s else #[]
  glob := r.glob

/-- **The L memory of one `ca_check_b` call** (generic `bufMem`): `bufMem0` with `plo := j`,
`phi := j + 1`, `mode := 2`. -/
def bufMemG (fz own : List TieredArray) (plo phi mode : GVar) (B : Array Word) (r : Mem) (j : Word) : Mem :=
  { bufMem0 fz own B r with
    glob := fun g => if g = plo then j else if g = phi then j + 1 else if g = mode then 2 else r.glob g }

theorem bufMem_eq (B : Array Word) (r : Mem) (j : Word) :
    bufMem B r j = bufMemG frozenIdsL parOwnedL PLO PHI MODE B r j := by rfl

/-- `bufMemG` is the stub's three global stores on `bufMem0`, for distinct globals. -/
theorem bufMemG_eq_setG {fz own : List TieredArray} {plo phi mode : GVar} (h1 : plo ≠ phi) (h2 : plo ≠ mode)
    (h3 : phi ≠ mode) (B : Array Word) (r : Mem) (j : Word) :
    bufMemG fz own plo phi mode B r j = (((bufMem0 fz own B r).setG plo j).setG phi (j + 1)).setG mode 2 := by
  simp only [bufMemG, Mem.setG, bufMem0, Mem.mk.injEq, true_and]
  funext g
  by_cases ha : g = plo
  · subst ha; simp [h1, h2]
  · by_cases hb : g = phi
    · subst hb; simp [ha, h3]
    · by_cases hc : g = mode
      · subst hc; simp [ha, hb]
      · simp [ha, hb, hc]

/-- The words the stub's constant data writes (word `i`). -/
def romBits (rom : List UInt8) (i : Nat) : BitVec 64 :=
  match (romVals rom)[i]? with
  | some (.imm w) => w.toBitVec
  | _ => 0

/-- The number of table words the stub writes. -/
def bufN (tab : Tab) : Nat := 2 + 3 * (tab.nb + tab.nw) + tab.romWords

/-- **Table word `q` as `ca_check_b` writes it**: the stack top and limit, the bases, the
lengths and the lengths in 32-bit elements of `bufLayout`'s positions, the constant data. -/
def bufVal (tab : Tab) (buf : Nat) (B : Array Word) (base : Nat) (fz own : List TieredArray) (q : Nat) :
    BitVec 64 :=
  if q = 0 then (UInt64.ofNat (base + abiSlot + abiStack)).toBitVec
  else if q = 1 then (UInt64.ofNat (base + abiSlot)).toBitVec
  else if q < 2 + (tab.nb + tab.nw) then (UInt64.ofNat ((bufLayout tab buf B base fz own).b (q - 2))).toBitVec
  else if q < 2 + 2 * (tab.nb + tab.nw) then
    (UInt64.ofNat ((bufLayout tab buf B base fz own).s (q - 2 - (tab.nb + tab.nw)))).toBitVec
  else if q < 2 + 3 * (tab.nb + tab.nw) then
    (UInt64.ofNat (2 * (bufLayout tab buf B base fz own).s (q - 2 - 2 * (tab.nb + tab.nw)))).toBitVec
  else romBits tab.rom (q - 2 - 3 * (tab.nb + tab.nw))

theorem bufMem0_arr8 (fz own : List TieredArray) (B : Array Word) (r : Mem) (a : Nat) :
    (bufMem0 fz own B r).arr8 a = #[] := rfl

theorem bufMem0_arr64 (fz own : List TieredArray) (B : Array Word) (r : Mem) (s : TieredArray) :
    (bufMem0 fz own B r).arr64 s = match fz.idxOf? s with
      | some i => bufImg B i
      | none => if own.contains s then r.arr64 s else #[] := rfl

section
variable {tab : Tab} {fz own : List TieredArray} {B : Array Word} {buf base blen : Nat}

/-- **The stub's table stores, on a region that holds `r` and beside the buffer holding `B`,
relate the memory to `bufMem0`** in `ca_check_b`'s layout (`qs`: the table words, in any
order). -/
theorem buf_memRel (hok : abiTabOk tab = true) (hg : BufGeom tab fz own B buf base blen) (r : Mem)
    (d : DataMem) (hr : RegionRel tab base own r d)
    (hB : ∀ i (h : i < B.size), rdW d (A (buf + 8 * i)) = some B[i])
    (hmap : ∀ x, base ≤ x → x < base + blen → (d.get? (A x)).isSome)
    (qs : List Nat) (hq : ∀ q < bufN tab, q ∈ qs) (hq' : ∀ q ∈ qs, q < bufN tab) :
    MemRel (bufLayout tab buf B base fz own) (bufMem0 fz own B r)
      (qwrs base (bufVal tab buf B base fz own) d qs) := by
  obtain ⟨hnb, htab, -⟩ := abiTabOk_spec hok
  have hn := hg.need
  have hf := hg.fits
  have hbe := hg.bend
  unfold workerNeed at hn
  have hN : base + 8 * bufN tab ≤ base + 2 ^ 31 := by simp only [bufN]; omega
  have hNr : base + 2 ^ 31 ≤ base + blen := by simp only [abiSlot] at hn; omega
  have hfit : ∀ q ∈ qs, base + 8 * q + 8 ≤ 2 ^ 64 := fun q h => by have := hq' q h; omega
  have hO := qwrs_only (T := base) (val := bufVal tab buf B base fz own) qs d (bufN tab) (by omega) hq'
  -- word `q` of the stores
  have hW : ∀ q, q < bufN tab → rdW (qwrs base (bufVal tab buf B base fz own) d qs) (A (base + 8 * q)) =
      some (UInt64.ofBitVec (bufVal tab buf B base fz own q)) := fun q h => qwrs_rdW qs d q (hq q h) hfit
  constructor
  · intro a ha
    simp only [bufLayout_tab] at ha ⊢
    rw [bufLayout_s8 _ _ _ _ _ _ (tab.pos8_lt ha)]; simp [bufMem0_arr8]
  · intro a ha
    simp only [bufLayout_tab] at ha ⊢
    rw [bufMem0_arr64 fz own B r, bufLayout_s64 _ _ _ _ _ _ (tab.pos64_lt ha).1, tab.wAt_pos64 ha]
    rcases hfz : fz.idxOf? a with _ | i
    · simp only [bufL, hfz]
      by_cases hc : own.contains a = true
      · obtain ⟨k, hk⟩ := idxOf?_of_contains hc
        simp only [hc, ite_true, hk]; exact hr.size a ha k hk
      · simp only [hc, idxOf?_of_not_contains hc]; rfl
    · have := hg.ent i (idxOf?_lt hfz)
      simp only [bufL, hfz, bufImg, Array.size_extract]
      rw [Nat.min_eq_left this]; omega
  · intro a _ i hi; simp [bufMem0_arr8] at hi
  · intro a ha i hi
    simp only [bufLayout_tab] at ha ⊢
    have e := bufMem0_arr64 fz own B r a
    rw [bufLayout_b64 _ _ _ _ _ _ (tab.pos64_lt ha).1, tab.wAt_pos64 ha]
    rcases hfz : fz.idxOf? a with _ | i'
    · simp only [e, hfz] at hi ⊢
      simp only [bufB, hfz]
      by_cases hc : own.contains a = true
      · obtain ⟨k, hk⟩ := idxOf?_of_contains hc
        have hk' := idxOf?_lt hk
        have hs := hr.size a ha k hk
        simp only [hc, ite_true] at hi ⊢
        simp only [hk]
        -- the word's first and last byte: past the table's words, inside the region
        have hb : ∀ j < 8, base + 8 * bufN tab ≤ base + ownOff tab a k + 8 * i + j ∧
            base + ownOff tab a k + 8 * i + j < base + blen := by
          intro j hj
          have hx := own_bytes hok (s := a) (k := k) (base := base) (x := base + ownOff tab a k + 8 * i + j)
            (by omega) (by rw [← hs]; omega)
          refine ⟨?_, (own_region hg hk' (hx.imp (fun h => h.2) (fun h => h.2))).2⟩
          rcases hx with ⟨-, h3⟩ | ⟨-, h3⟩
          · unfold InSlot at h3; simp only [bufN, abiSlot] at hN h3 ⊢; omega
          · unfold InTbl at h3; simp only [bufN] at h3 ⊢; omega
        have hb0 := hb 0 (by omega); have hb7 := hb 7 (by omega)
        rw [hO.rdW_eq (by omega) (Or.inr (by omega))]
        exact hr.get a ha k hk i hi
      · simp only [hc] at hi; simp at hi
    · simp only [e, hfz] at hi ⊢
      simp only [bufB, hfz]
      have hent := hg.ent i' (idxOf?_lt hfz)
      have hi2 : i < (bufEntry B i').2 := by
        simp only [bufImg, Array.size_extract] at hi; rw [Nat.min_eq_left hent] at hi; omega
      rw [show buf + 8 * (bufEntry B i').1 + 8 * i = buf + 8 * ((bufEntry B i').1 + i) by omega,
        hO.rdW_eq (by omega) (by
          rcases hg.apart (buf + 8 * ((bufEntry B i').1 + i) + 7) (by omega) (by omega) with h | h
          · left; omega
          · right; simp only [abiSlot] at hn; omega),
        hB _ (by omega)]
      simp [bufImg]
  · have := hW 1 (by simp only [bufN]; omega)
    simpa [bufVal, bufLayout_T, bufLayout_lo] using this
  · intro p hp
    simp only [bufLayout_tab] at hp
    have := hW (2 + p) (by simp only [bufN]; omega)
    simp only [bufLayout_T, Tab.dbase]
    rw [show (16 + 8 * (p : Int)).toNat = 8 * (2 + p) by omega, this]
    simp only [bufVal, show 2 + p ≠ 0 by omega, show 2 + p ≠ 1 by omega,
      show 2 + p < 2 + (tab.nb + tab.nw) by omega, ite_false, ite_true,
      show 2 + p - 2 = p by omega, UInt64.ofBitVec_toBitVec]
  · intro p hp
    simp only [bufLayout_tab] at hp
    have := hW (2 + (tab.nb + tab.nw) + p) (by simp only [bufN]; omega)
    simp only [bufLayout_T, bufLayout_tab, Tab.dlen]
    rw [show (16 + 8 * ((tab.nb : Int) + (tab.nw : Int)) + 8 * (p : Int)).toNat =
      8 * (2 + (tab.nb + tab.nw) + p) by omega, this]
    simp only [bufVal, show 2 + (tab.nb + tab.nw) + p ≠ 0 by omega, show 2 + (tab.nb + tab.nw) + p ≠ 1 by omega,
      show ¬ 2 + (tab.nb + tab.nw) + p < 2 + (tab.nb + tab.nw) by omega,
      show 2 + (tab.nb + tab.nw) + p < 2 + 2 * (tab.nb + tab.nw) by omega, ite_false, ite_true,
      show 2 + (tab.nb + tab.nw) + p - 2 - (tab.nb + tab.nw) = p by omega, UInt64.ofBitVec_toBitVec]
  · intro p _ hp
    simp only [bufLayout_tab] at hp
    have := hW (2 + 2 * (tab.nb + tab.nw) + p) (by simp only [bufN]; omega)
    simp only [bufLayout_T, bufLayout_tab, Tab.dlen32]
    rw [show (16 + 16 * ((tab.nb : Int) + (tab.nw : Int)) + 8 * (p : Int)).toNat =
      8 * (2 + 2 * (tab.nb + tab.nw) + p) by omega, this]
    simp only [bufVal, show 2 + 2 * (tab.nb + tab.nw) + p ≠ 0 by omega,
      show 2 + 2 * (tab.nb + tab.nw) + p ≠ 1 by omega,
      show ¬ 2 + 2 * (tab.nb + tab.nw) + p < 2 + (tab.nb + tab.nw) by omega,
      show ¬ 2 + 2 * (tab.nb + tab.nw) + p < 2 + 2 * (tab.nb + tab.nw) by omega,
      show 2 + 2 * (tab.nb + tab.nw) + p < 2 + 3 * (tab.nb + tab.nw) by omega, ite_false, ite_true,
      show 2 + 2 * (tab.nb + tab.nw) + p - 2 - 2 * (tab.nb + tab.nw) = p by omega, UInt64.ofBitVec_toBitVec]
  · intro i hi
    simp only [bufLayout_tab] at hi
    simp only [bufLayout_T, bufLayout_tab]
    obtain ⟨w, hw1, hw2⟩ := romVals_byte tab.rom i hi
    have hlt : i / 8 < tab.romWords := by
      have := tab.rom_length_le; simp only [Tab.romWords] at this ⊢; omega
    have hq0 : 2 + 3 * (tab.nb + tab.nw) + i / 8 < bufN tab := by simp only [bufN]; omega
    rw [show base + 16 + 24 * (tab.nb + tab.nw) + i = base + 8 * (2 + 3 * (tab.nb + tab.nw) + i / 8) + i % 8 by omega,
      qwrs_byte qs d _ _ (hq _ hq0) (Nat.mod_lt _ (by omega)) hfit]
    simp only [bufVal, show 2 + 3 * (tab.nb + tab.nw) + i / 8 ≠ 0 by omega,
      show 2 + 3 * (tab.nb + tab.nw) + i / 8 ≠ 1 by omega,
      show ¬ 2 + 3 * (tab.nb + tab.nw) + i / 8 < 2 + (tab.nb + tab.nw) by omega,
      show ¬ 2 + 3 * (tab.nb + tab.nw) + i / 8 < 2 + 2 * (tab.nb + tab.nw) by omega,
      show ¬ 2 + 3 * (tab.nb + tab.nw) + i / 8 < 2 + 3 * (tab.nb + tab.nw) by omega, ite_false,
      show 2 + 3 * (tab.nb + tab.nw) + i / 8 - 2 - 3 * (tab.nb + tab.nw) = i / 8 by omega, romBits, hw1,
      UInt64.ofBitVec_toBitVec]
    exact hw2
  · intro x hx
    have := (buf_inStack hx).region hg (by omega)
    exact qwrs_grows qs d _ (hmap x this.1 this.2)
  · intro x hx
    have := (buf_inTab hok hx.tab).1.region hg (by omega)
    exact qwrs_grows qs d _ (hmap x this.1 this.2)
  · intro g hg'
    simp only [bufLayout_tab] at hg'
    rw [← Layout.globAddr_toNat]
    simp only [bufLayout_T, bufLayout_tab]
    rw [hO.rdW_eq (by simp only [Tab.globOff, Tab.globBase] at *; omega)
      (Or.inr (by simp only [bufN, Tab.globOff, Tab.globBase]; omega))]
    exact hr.glob g hg'

end

end ConAgua.Final
