import ConAgua.Final.DrvAbi
import ConAgua.Arena.FreezeRel

/-!
# The threads' entry 2: `ca_check_b`'s layout and memory (lane parmode)

`ca_check_b(buf, buf_len, j, region, region_len)` (`parStub`, `ConAgua/Compiler/Abi.lean`) lays out
one call of `check` on a worker region `[base, base + blen)` and the read-only frozen buffer
`[buf, buf + 8·|B|)` holding the words `B`:

* `bufLayout`: the table at `base` (slot `0`), the L stack in slot `1`, frozen array `fz[i]` at
  `buf + 8·off_i` with `len_i` words (the buffer's header entry `i`, `bufEntry B i`), owned array
  `own[k]` in slot `2 + k` with `abiWords` words, every other array (and both byte arrays)
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
def bufB (B : Array Word) (buf base : Nat) (fz own : List ArrId) (a : ArrId) : Nat :=
  match fz.idxOf? a with
  | some i => buf + 8 * (bufEntry B i).1
  | none =>
    match own.idxOf? a with
    | some k => base + abiSlot * (2 + k)
    | none => 0

/-- Word array `a`'s length in `ca_check_b`'s layout. -/
def bufL (B : Array Word) (fz own : List ArrId) (a : ArrId) : Nat :=
  match fz.idxOf? a with
  | some i => (bufEntry B i).2
  | none =>
    match own.idxOf? a with
    | some _ => abiWords
    | none => 0

/-- **`ca_check_b`'s layout**: the table at `base`, the stack in slot `1`, frozen array `fz[i]` at
the buffer's entry `i`, owned array `own[k]` in slot `2 + k`. -/
def bufLayout (tab : Tab) (buf : Nat) (B : Array Word) (base : Nat) (fz own : List ArrId) :
    L.Compiler.Layout where
  tab
  T := base
  b8 _ := 0
  s8 _ := 0
  b64 := bufB B buf base fz own
  s64 := bufL B fz own
  lo := base + abiSlot
  hi := base + abiSlot + abiStack
  nargs := 0

section
variable (tab : Tab) (buf : Nat) (B : Array Word) (base : Nat) (fz own : List ArrId)
@[simp] theorem bufLayout_tab : (bufLayout tab buf B base fz own).tab = tab := rfl
@[simp] theorem bufLayout_T : (bufLayout tab buf B base fz own).T = base := rfl
@[simp] theorem bufLayout_b8 (a : Nat) : (bufLayout tab buf B base fz own).b8 a = 0 := rfl
@[simp] theorem bufLayout_s8 (a : Nat) : (bufLayout tab buf B base fz own).s8 a = 0 := rfl
@[simp] theorem bufLayout_b64 (a : Nat) : (bufLayout tab buf B base fz own).b64 a = bufB B buf base fz own a := rfl
@[simp] theorem bufLayout_s64 (a : Nat) : (bufLayout tab buf B base fz own).s64 a = bufL B fz own a := rfl
@[simp] theorem bufLayout_lo : (bufLayout tab buf B base fz own).lo = base + abiSlot := rfl
@[simp] theorem bufLayout_hi : (bufLayout tab buf B base fz own).hi = base + abiSlot + abiStack := rfl
@[simp] theorem bufLayout_nargs : (bufLayout tab buf B base fz own).nargs = 0 := rfl
end

/-- **The geometry of one `ca_check_b` call**: the region `[base, base + blen)` holds the table,
the stack and the owned arrays and is in the address space; the buffer `[buf, buf + 8·|B|)` is
in the address space and apart from the region; its header (words `8 + 2i`, `9 + 2i`) is inside
it, and its entries are inside it and pairwise apart (or empty). -/
structure BufGeom (tab : Tab) (fz own : List ArrId) (B : Array Word) (buf base blen : Nat) : Prop where
  need : workerNeed own ≤ blen
  fits : base + blen < 2 ^ 64
  bend : buf + 8 * B.size < 2 ^ 64
  hdr : ∀ i < fz.length, 9 + 2 * i < B.size
  ent : ∀ i < fz.length, (bufEntry B i).1 + (bufEntry B i).2 ≤ B.size
  disj : ∀ i < fz.length, ∀ i' < fz.length, i ≠ i' →
    (bufEntry B i).1 + (bufEntry B i).2 ≤ (bufEntry B i').1 ∨
    (bufEntry B i').1 + (bufEntry B i').2 ≤ (bufEntry B i).1 ∨ (bufEntry B i).2 = 0 ∨ (bufEntry B i').2 = 0
  apart : ∀ x, buf ≤ x → x < buf + 8 * B.size → x < base ∨ base + blen ≤ x

theorem idxOf?_lt {l : List ArrId} {a i : Nat} (h : l.idxOf? a = some i) : i < l.length := by
  have := List.idxOf?_eq_some_iff.mp h
  exact this.1

theorem idxOf?_inj {l : List ArrId} {a b i : Nat} (ha : l.idxOf? a = some i) (hb : l.idxOf? b = some i) :
    a = b := by
  obtain ⟨hl, e1, -⟩ := List.idxOf?_eq_some_iff.mp ha
  obtain ⟨hl', e2, -⟩ := List.idxOf?_eq_some_iff.mp hb
  exact e1.symm.trans e2

section
variable {tab : Tab} {fz own : List ArrId} {B : Array Word} {buf base blen : Nat}

/-- A byte of word array `a` is in the buffer (frozen) or in the region's slot `2 + k` (owned). -/
theorem buf_in64 (_hg : BufGeom tab fz own B buf base blen) {a x : Nat}
    (h : (bufLayout tab buf B base fz own).In64 a x) :
    (∃ i, fz.idxOf? a = some i ∧ buf + 8 * (bufEntry B i).1 ≤ x ∧
        x < buf + 8 * ((bufEntry B i).1 + (bufEntry B i).2)) ∨
      (fz.idxOf? a = none ∧ ∃ k, own.idxOf? a = some k ∧ InSlot base (2 + k) x) := by
  unfold Layout.In64 at h
  simp only [bufLayout_b64, bufLayout_s64, bufB, bufL] at h
  split at h
  · rename_i i hi
    exact Or.inl ⟨i, hi, by omega, by omega⟩
  · rename_i hn
    split at h
    · rename_i k hk
      refine Or.inr ⟨hn, k, hk, ?_⟩
      unfold InSlot; simp only [abiWords, abiSlot] at h ⊢; omega
    · omega

theorem buf_inTab (hok : abiTabOk tab = true) {x : Nat}
    (h : (bufLayout tab buf B base fz own).InTab x) : InSlot base 0 x := by
  obtain ⟨-, htab, -⟩ := abiTabOk_spec hok
  unfold Layout.InTab Layout.tabEnd at h
  simp only [bufLayout_T, bufLayout_tab, bufLayout_nargs] at h
  unfold InSlot abiSlot; omega

theorem buf_inStack {x : Nat} (h : (bufLayout tab buf B base fz own).InStack x) : InSlot base 1 x := by
  unfold Layout.InStack at h
  simp only [bufLayout_lo, bufLayout_hi] at h
  unfold InSlot; simp only [abiSlot, abiStack] at h ⊢; omega

theorem buf_notIn8 {a x : Nat} : ¬ (bufLayout tab buf B base fz own).In8 a x := by
  unfold Layout.In8; simp

/-- Bytes of the region's slots `< 2 + |own|` are in the region. -/
theorem InSlot.region (hg : BufGeom tab fz own B buf base blen) {j x : Nat} (h : InSlot base j x)
    (hj : j < 2 + own.length) : base ≤ x ∧ x < base + blen := by
  have := h.lt hj
  have hn := hg.need
  unfold workerNeed at hn
  unfold InSlot at h
  omega

/-- A byte of the layout's table, stack or an owned array is in the region; a frozen byte is in
the buffer. -/
theorem buf_part (hok : abiTabOk tab = true) (hg : BufGeom tab fz own B buf base blen) {x : Nat}
    (h : (bufLayout tab buf B base fz own).InStack x ∨ (bufLayout tab buf B base fz own).InArr x ∨
      (bufLayout tab buf B base fz own).InTab x) :
    (base ≤ x ∧ x < base + blen) ∨ (buf ≤ x ∧ x < buf + 8 * B.size) := by
  rcases h with h | (⟨a, _, h⟩ | ⟨a, ha, h⟩) | h
  · exact Or.inl ((buf_inStack h).region hg (by omega))
  · exact absurd h buf_notIn8
  · rcases buf_in64 hg h with ⟨i, hi, h1, h2⟩ | ⟨-, k, hk, hs⟩
    · have := hg.ent i (idxOf?_lt hi); right; omega
    · exact Or.inl (hs.region hg (by have := idxOf?_lt hk; omega))
  · exact Or.inl ((buf_inTab hok h).region hg (by omega))

theorem bufLayout_ok (hok : abiTabOk tab = true) (hg : BufGeom tab fz own B buf base blen) :
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
  · intro a _; simp
  · intro a ha
    simp only [bufLayout_b64, bufLayout_s64, bufB, bufL]
    split
    · rename_i i hi
      have := hg.ent i (idxOf?_lt hi); omega
    · split
      · rename_i k hk
        have hk' := idxOf?_lt hk
        have hle : abiSlot * (2 + k) + abiSlot ≤ abiSlot * (2 + own.length) := by
          rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
        simp only [abiSlot, abiWords] at hle hn ⊢; omega
      · simp
  · intro x h1 h2
    exact absurd (InSlot.eq (buf_inTab hok h1) (buf_inStack h2)) (by omega)
  · intro x h1 h2
    rcases h2 with ⟨a, _, h⟩ | ⟨a, _, h⟩
    · exact buf_notIn8 h
    · have ht := (buf_inTab hok h1).region hg (by omega)
      rcases buf_in64 hg h with ⟨i, hi, q1, q2⟩ | ⟨-, k, hk, hs⟩
      · have := hg.ent i (idxOf?_lt hi)
        rcases hg.apart x (by omega) (by omega) with h' | h' <;> omega
      · exact absurd (InSlot.eq (buf_inTab hok h1) hs) (by omega)
  · intro x h1 h2
    rcases h2 with ⟨a, _, h⟩ | ⟨a, _, h⟩
    · exact buf_notIn8 h
    · have ht := (buf_inStack h1).region hg (by omega)
      rcases buf_in64 hg h with ⟨i, hi, q1, q2⟩ | ⟨-, k, hk, hs⟩
      · have := hg.ent i (idxOf?_lt hi)
        rcases hg.apart x (by omega) (by omega) with h' | h' <;> omega
      · exact absurd (InSlot.eq (buf_inStack h1) hs) (by omega)
  · intro a _ b _ _ x h; exact absurd h buf_notIn8
  · intro a _ b _ hab x h1 h2
    rcases buf_in64 hg h1 with ⟨i, hi, p1, p2⟩ | ⟨hn1, k, hk, hs⟩ <;>
      rcases buf_in64 hg h2 with ⟨i', hi', p3, p4⟩ | ⟨hn2, k', hk', hs'⟩
    · have hii : i ≠ i' := fun e => hab (idxOf?_inj hi (e ▸ hi'))
      rcases hg.disj i (idxOf?_lt hi) i' (idxOf?_lt hi') hii with h | h | h | h <;> omega
    · have := hg.ent i (idxOf?_lt hi)
      have hr := hs'.region hg (by have := idxOf?_lt hk'; omega)
      rcases hg.apart x (by omega) (by omega) with h' | h' <;> omega
    · have := hg.ent i' (idxOf?_lt hi')
      have hr := hs.region hg (by have := idxOf?_lt hk; omega)
      rcases hg.apart x (by omega) (by omega) with h' | h' <;> omega
    · have e := InSlot.eq hs hs'
      exact hab (idxOf?_inj hk (by rw [show k = k' by omega]; exact hk'))
  · intro a _ b _ x h; exact absurd h buf_notIn8

end

end ConAgua.Final
