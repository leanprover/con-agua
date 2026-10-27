import ConAgua.Arena.MemoLibRel
import ConLeche.Frontend.Scan.Types
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# The parse state's id tables: a dense array plus a sparse overflow (`IdTable`)

con-ron's `StateD` (`vendor/con-ron/ConRon/Arena/Frontend/ExportC.lean:99`) keeps its name, level
and expression tables as con-leche's `IdTable` (`ConLeche/Frontend/Scan/Types.lean:330`): a dense
`Array` that grows by `push` at its frontier, and a sparse `Std.HashMap Nat` for a gap or an
out-of-order id. Here, for table `b` (`NID` 64, `LID` 65, `EID` 66):

* the dense part is word array `b` (its capacity fixed by the harness) with its size in
  `CTL[szC b]` (`70`, `71`, `72`); entry `i < size` is the handle word, stored at 32 bits: the
  half `i & 1` of word `i >> 1` (bits `32 * (i & 1)` … `+ 31`; con-ron's handles are `u32`), so
  the capacity in entries is twice the array's length; a write is a read-modify-write of the word;
* the sparse part is a memo-library table (`MemoLib.lean`, open addressing, one-word keys) at array
  `b + 8` (`72`, `73`, `74`), stamp and count `CTL[2b - 64]`, `CTL[2b - 63]` (`64‥69`).

The L functions, generic in the table (the memo's `find`/`put` named by the instance):
* `tbl_get(i)` (`StateD.name`/`level`/`expr`, through `IdTable.get?`): the dense entry below the
  size, else the sparse probe's value; abort if unbound.
* `tbl_fresh(i)` (`StateD.freshName`/…, through `IdTable.bound`): abort if bound.
* `tbl_put(i, h)` (`IdTable.insert`): at the frontier (and below the capacity) a push, below it an
  overwrite, else the sparse map.

Two differences from the twin, both outside its reachable behaviour: an id word `TOMB = NONE =
2^64 - 1` (what `read_nat` returns past 18 digits) is refused on the sparse path, and the dense
array stops growing at its capacity, where the twin's `push` would reallocate (the ids go to the
sparse map then, which accepts them up to its own load limit). `IdTable.bound`'s shortcut
(`sparse.isEmpty` skips the hash) is not mirrored: the memo keeps a count, but nothing relates it
to the map's emptiness; `tbl_fresh` probes (one slot when the map is empty). Listed in
`docs/deviations.md`.

Each spec's post is an equation about a named model (`tblOK`, `tblW`, `tblFresh`, `tblPutW`); the
relation `TblR` and its lemmas are in `StateDR.lean`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order
open L.Arena
open ConRon.Arena

namespace L.Front

/-- The `CTL` word holding table `b`'s dense size. -/
def szC (b : ArrId) : Word := UInt64.ofNat (b + 6)

/-- Table `b`'s sparse overflow: array `b + 8`, stamp `CTL[2b - 64]`, count `CTL[2b - 63]`. -/
def spS (b : ArrId) : MemoSch := ⟨b + 8, UInt64.ofNat (2 * b - 64)⟩

/-! ## Models -/

/-- The dense size of table `b`. -/
def szW (m : Mem) (b : ArrId) : Word := rdW (m.arr64 CTL) (szC b)

/-- The sparse probe of table `b` for id `i`. -/
def spF (m : Mem) (b : ArrId) (i : Word) : List Word := mfindG (spS b) m i 0

/-- The bit offset of dense entry `i`'s half in its word. -/
def dSh (i : Word) : Word := (i &&& 1) <<< 5

/-- Dense entry `i` of word array `a`: the 32-bit half `i & 1` of word `i >> 1`. -/
def dnW (a : Array Word) (i : Word) : Word := (rdW a (i >>> 1) >>> dSh i) &&& (0xFFFFFFFF : Word)

/-- Word `w` with the half of entry `i` replaced by `h` (a 32-bit word). -/
def dnSet (w i h : Word) : Word :=
  (w &&& ((0xFFFFFFFF00000000 : Word) >>> dSh i)) ||| (h <<< dSh i)

/-- Id `i` of table `b` is bound (the L code returns rather than aborts). -/
def tblOK (m : Mem) (b : ArrId) (i : Word) : Bool :=
  if i < szW m b then decide ((i >>> 1).toNat < (m.arr64 b).size)
  else i != TOMB && decide (spF m b i ≠ []) && (spF m b i).headD 0 != 0

/-- The handle word id `i` of table `b` holds. -/
def tblW (m : Mem) (b : ArrId) (i : Word) : Word :=
  if i < szW m b then dnW (m.arr64 b) i else mvG (spS b) m ((spF m b i).tail.headD 0)

/-- Id `i` of table `b` is unbound (and not `TOMB`). -/
def tblFresh (m : Mem) (b : ArrId) (i : Word) : Bool :=
  !decide (i < szW m b) && i != TOMB && decide (spF m b i ≠ []) && (spF m b i).headD 0 == 0

/-- The memory after binding id `i` of table `b` to handle word `h` (`IdTable.insert`), `none`
where the L code aborts. -/
def tblPutW (m : Mem) (b : ArrId) (i h : Word) : Option Mem :=
  if i = szW m b ∧ i >>> 1 < m.len64 b then
    some ((m.set64 b (i >>> 1) (dnSet (rdW (m.arr64 b) (i >>> 1)) i h)).set64 CTL (szC b) (i + 1))
  else if i < szW m b then
    (if (i >>> 1).toNat < (m.arr64 b).size then
      some (m.set64 b (i >>> 1) (dnSet (rdW (m.arr64 b) (i >>> 1)) i h)) else none)
  else if i = TOMB then none
  else msetG (spS b) m i 0 h

/-- After an interning returned `(h, m')`: bind id `i` of table `b` to `h` (`h` must be a 32-bit
handle). -/
def putK (b : ArrId) (i : Word) : Option (Word × Mem) → Option Mem
  | some (h, m') => if h < 0x100000000 then tblPutW m' b i h else none
  | none => none

@[arena_grind =] theorem putK_some (b : ArrId) (i h : Word) (m' : Mem) :
    putK b i (some (h, m')) = if h < 0x100000000 then tblPutW m' b i h else none :=
  rfl

/-! ## The L functions -/

/-- `tbl_get(i)` of table `b`, the sparse probe `fnd`.
con-leche: ConLeche/Frontend/Scan/Types.lean:334-336 ConLeche.Frontend.IdTable.get? -/
def tblGetG (b : ArrId) (fnd : FnName) : FunDecl :=
  let _sa : ArrId := b + 8
  lfn (i) locals (fd, j, d) {
    if i < CTL.u64[⟪szC b⟫] { return (b.u64[i >> 1] >> ((i & 1) << 5)) & 0xFFFFFFFF };
    if i == ⟪TOMB⟫ { abort };
    ⟪.call [1, 2, 3] fnd [.var 0, .const 0]⟫;
    if fd == 0 { abort };
    return _sa.u64[j * 4 + 3]
  }

/-- `tbl_fresh(i)` of table `b`, the sparse probe `fnd`.
con-leche: ConLeche/Frontend/Scan/Types.lean:351-360 ConLeche.Frontend.IdTable.bound -/
def tblFreshG (b : ArrId) (fnd : FnName) : FunDecl := lfn (i) locals (fd, j, d) {
  if i < CTL.u64[⟪szC b⟫] { abort };
  if i == ⟪TOMB⟫ { abort };
  ⟪.call [1, 2, 3] fnd [.var 0, .const 0]⟫;
  if fd != 0 { abort };
  return 0
}

/-- `tbl_put(i, h)` of table `b`, the sparse probe `fnd` and put `pt`.
con-leche: ConLeche/Frontend/Scan/Types.lean:338-345 ConLeche.Frontend.IdTable.insert -/
def tblPutG (b : ArrId) (fnd pt : FnName) : FunDecl := lfn (i, h) locals (s, fd, j, d, z) {
  s := CTL.u64[⟪szC b⟫];
  if i == s && i >> 1 < len(b.u64) {
    z := (i & 1) << 5;
    b.u64[i >> 1] := (b.u64[i >> 1] & (0xFFFFFFFF00000000 >> z)) | (h << z);
    CTL.u64[⟪szC b⟫] := i + 1;
    return 0
  };
  if i < s {
    z := (i & 1) << 5;
    b.u64[i >> 1] := (b.u64[i >> 1] & (0xFFFFFFFF00000000 >> z)) | (h << z);
    return 0
  };
  if i == ⟪TOMB⟫ { abort };
  ⟪.call [3, 4, 5] fnd [.var 0, .const 0]⟫;
  ⟪.call [6] pt [.var 0, .const 0, .var 1, .var 3, .var 4]⟫;
  return 0
}

/-! ## The specs -/

section specs
variable (p : Prog) (b : ArrId) (fnd pt : FnName)
  (hf : p.lookup fnd = some (memoFindG (spS b)))

include hf

theorem tblGetG_spec (f : FnName) (hp : p.lookup f = some (tblGetG b fnd)) (n : Nat) (s₀ : St)
    (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) f [i]
    ⦃fun r s' => s' = s₀ ∧ tblOK s₀.mem b i = true ∧ r = [tblW s₀.mem b i]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, tblGetG]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        memoFindG_spec (spS b) p fnd hf n] <;>
      finish [tblOK, tblW, szW, spF, mvG, spS, dnW, dSh, BinOp.eval]

theorem tblFreshG_spec (f : FnName) (hp : p.lookup f = some (tblFreshG b fnd)) (n : Nat)
    (s₀ : St) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) f [i]
    ⦃fun _ s' => s' = s₀ ∧ tblFresh s₀.mem b i = true; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, tblFreshG]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        memoFindG_spec (spS b) p fnd hf n] <;>
      finish [tblFresh, szW, spF]

theorem tblPutG_spec (hpt : p.lookup pt = some (memoPutG (spS b))) (f : FnName)
    (hp : p.lookup f = some (tblPutG b fnd pt)) (n : Nat) (s₀ : St) (i h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) f [i, h]
    ⦃fun _ s' => LocEq s' s₀ ∧ tblPutW s₀.mem b i h = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, tblPutG]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        memoFindG_spec (spS b) p fnd hf n, memoPutG_spec (spS b) p pt hpt n] <;>
      finish [tblPutW, szW, msetG, dnSet, dSh, BinOp.eval]

end specs

/-! ## The relation: table `b` represents an `IdTable` -/

/-- The three tables. -/
def TblIx (b : ArrId) : Prop := b = 64 ∨ b = 65 ∨ b = 66

/-- The tables' arrays: dense `64‥66`, sparse `72‥74`. -/
def idArrs : List ArrId := [64, 65, 66, 72, 73, 74]

/-- The tables' `CTL` words: sparse stamps and counts `64‥69`, dense sizes `70‥72`. -/
def idCtl : List Word := [64, 65, 66, 67, 68, 69, 70, 71, 72]

/-- The sparse maps' keys: the id word, second word `0`. -/
def idKey : MemoKey Nat where
  dk k1 _ := k1.toNat
  ek x := (x.toUInt64, 0)
  ok k1 k2 := k1 ≠ TOMB ∧ k2 = 0
  ek_dk k1 k2 h := by simp [h.2]
  ok_tomb _ _ h := h.1

/-- A sparse value word denotes a handle: the word is below `2^32`. -/
def hVR {k : IdxKind} (_ : Mem) (w : Word) (v : Idx k) : Prop := v = decI w ∧ w.toNat < 2 ^ 32

theorem hVR_stable {k : IdxKind} (S : MemoSch) : VStable S (hVR (k := k)) := fun _ _ _ _ _ h => h

/-- **Table `b` of `m` represents `t`** at every word id: below the dense size the dense entry
(a 32-bit half word, `dnW`), at or above it the sparse map `sp` (`MemoRV`), which the twin's `get?`
reaches through its own dense-then-sparse order. -/
structure TblR {k : IdxKind} (m : Mem) (b : ArrId) (t : ConLeche.Frontend.IdTable (Idx k)) :
    Prop where
  size : (m.arr64 b).size < 2 ^ 63
  ctl : (szC b).toNat < (m.arr64 CTL).size
  sz : (szW m b).toNat ≤ 2 * (m.arr64 b).size
  dense : ∀ i : Word, i < szW m b →
    t.get? i.toNat = some (decI (dnW (m.arr64 b) i)) ∧ (dnW (m.arr64 b) i).toNat < 2 ^ 32
  sparse : ∃ sp : Std.HashMap Nat (Idx k), MemoRV (spS b) idKey hVR m sp ∧
    ∀ i : Word, ¬ i < szW m b → t.get? i.toNat = sp[i.toNat]?

section tbl
variable {k : IdxKind}

theorem toNat_ofNat_size (n : Nat) (h : n < 2 ^ 63) : (UInt64.ofNat n).toNat = n := by
  rw [UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)]

theorem spS_wf (b : ArrId) (hb : TblIx b) : (spS b).WF := by
  rcases hb with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩

theorem tomb_toNat : TOMB.toNat = 2 ^ 64 - 1 := rfl

/-! ### Dense entries at 32 bits -/

theorem dnW_lt (a : Array Word) (i : Word) : (dnW a i).toNat < 2 ^ 32 := by
  unfold dnW
  rw [UInt64.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

/-! The bits of the two masks and of a two-halves word (no `bv_decide`: its native axioms would
reach the final theorems). -/

theorem lo32_getLsbD (k : Nat) : (4294967295#64).getLsbD k = decide (k < 32) := by
  rw [BitVec.getLsbD_ofNat]
  have : (4294967295 : Nat) = 2^32-1 := rfl
  rw [this, Nat.testBit_two_pow_sub_one]; by_cases k < 32 <;> simp_all <;> omega

theorem hi32_getLsbD (k : Nat) :
    (18446744069414584320#64).getLsbD k = decide (32 ≤ k ∧ k < 64) := by
  have : (18446744069414584320#64) = ~~~(4294967295#64) := by decide
  rw [this, BitVec.getLsbD_not, lo32_getLsbD]
  by_cases k < 32 <;> by_cases k < 64 <;> simp_all <;> omega

theorem lo32_getElem (k : Nat) (hk : k < 64) : (4294967295#64)[k] = decide (k < 32) := by
  rw [← BitVec.getLsbD_eq_getElem, lo32_getLsbD]

theorem hi32_getElem (k : Nat) (hk : k < 64) : (18446744069414584320#64)[k] = decide (32 ≤ k) := by
  rw [← BitVec.getLsbD_eq_getElem, hi32_getLsbD]; simp [hk]

/-- A 32-bit `h` written to the half at bit `si` of `w`, read back from the half at bit `sj`. -/
theorem half_core (w h : Word) (hh : h < 0x100000000) (si sj : Word) (hi : si = 0 ∨ si = 32)
    (hj : sj = 0 ∨ sj = 32) :
    (((w &&& ((0xFFFFFFFF00000000 : Word) >>> si)) ||| (h <<< si)) >>> sj) &&& (0xFFFFFFFF : Word)
    = if sj = si then h else (w >>> sj) &&& (0xFFFFFFFF : Word) := by
  have hn : (32 : Word) ≠ 0 := by decide
  have hb : ∀ k, 32 ≤ k → h.toBitVec.getLsbD k = false := fun k h32 => by
    rw [BitVec.getLsbD, UInt64.toNat_toBitVec]
    apply Nat.testBit_lt_two_pow
    have : h.toNat < 2^32 := UInt64.lt_iff_toNat_lt.mp hh
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by omega) h32)
  have hbe : ∀ k (hk : k < 64), 32 ≤ k → h.toBitVec[k] = false := fun k hk h32 => by
    rw [← BitVec.getLsbD_eq_getElem, hb k h32]
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
    simp only [hn, hn.symm, ite_true, ite_false] <;>
    apply UInt64.toBitVec_inj.mp <;> simp <;> ext k hk <;> simp only [← BitVec.getLsbD_eq_getElem]
  all_goals (try simp [lo32_getLsbD, hi32_getLsbD, hk])
  all_goals
    by_cases h32 : k < 32
    · have a1 : ¬ 32 ≤ k := by omega
      have a2 : 32 + k < 64 := by omega
      have a3 : ¬ 32 + k < 32 := by omega
      have a4 := hbe (32 + k) a2 (by omega)
      simp [h32, a1, a2, a3, a4, lo32_getElem, hi32_getElem]
    · have a1 : 32 ≤ k := by omega
      have a2 := hbe k hk a1
      simp [h32, a1, a2, lo32_getElem, hi32_getElem]

theorem and1_toNat (i : Word) : (i &&& 1).toNat = i.toNat % 2 := by
  rw [UInt64.toNat_and]; simp [Nat.and_one_is_mod]

theorem dSh_eq (i : Word) : dSh i = if i.toNat % 2 = 0 then 0 else 32 := by
  unfold dSh
  rcases Nat.mod_two_eq_zero_or_one i.toNat with h | h
  · have : i &&& 1 = 0 := UInt64.toNat_inj.mp (by rw [and1_toNat, h]; rfl)
    rw [this, ite_eq_left h]; decide
  · have : i &&& 1 = 1 := UInt64.toNat_inj.mp (by rw [and1_toNat, h]; rfl)
    rw [this, ite_eq_right (by omega)]; decide

theorem shr1_toNat (i : Word) : (i >>> 1).toNat = i.toNat / 2 := by
  rw [UInt64.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]

theorem dSh_cases (i : Word) : dSh i = 0 ∨ dSh i = 32 := by
  rw [dSh_eq]; split <;> simp

theorem eq_iff_dSh (i j : Word) (hj : j >>> 1 = i >>> 1) : dSh j = dSh i ↔ j = i := by
  have h1 := congrArg UInt64.toNat hj
  rw [shr1_toNat, shr1_toNat] at h1
  constructor
  · intro h
    rw [dSh_eq, dSh_eq] at h
    apply UInt64.toNat_inj.mp
    split at h <;> split at h <;> first | omega | (exfalso; revert h; decide)
  · intro h; rw [h]

/-- The half-word update: entry `j` of the word `i >> 1` after writing `h` to entry `i`. -/
theorem dnSet_get (w i j h : Word) (hh : h < 0x100000000) (hj : j >>> 1 = i >>> 1) :
    (dnSet w i h >>> dSh j) &&& (0xFFFFFFFF : Word) =
      if j = i then h else (w >>> dSh j) &&& (0xFFFFFFFF : Word) := by
  unfold dnSet
  rw [half_core w h hh _ _ (dSh_cases i) (dSh_cases j)]
  simp only [eq_iff_dSh i j hj]

/-- Distinct entries in distinct words, or distinct halves. -/
theorem dnW_set (a : Array Word) (i j h : Word) (hh : h.toNat < 2 ^ 32) :
    dnW (a.set! (i >>> 1).toNat (dnSet (rdW a (i >>> 1)) i h)) j =
      if j = i ∧ (i >>> 1).toNat < a.size then h else dnW a j := by
  have hh' : h < 0x100000000 := UInt64.lt_iff_toNat_lt.mpr (by simpa using hh)
  unfold dnW
  rw [rdW_set!]
  by_cases hj : j >>> 1 = i >>> 1
  · by_cases hi : (i >>> 1).toNat < a.size
    · rw [ite_eq_left ⟨by rw [hj], hi⟩, dnSet_get _ _ _ _ hh' hj]
      by_cases e : j = i
      · rw [ite_eq_left e, ite_eq_left ⟨e, hi⟩]
      · rw [ite_eq_right e, ite_eq_right (fun c => e c.1), hj]
    · rw [ite_eq_right (fun c => hi c.2), ite_eq_right (fun c => hi c.2)]
  · have hne : j ≠ i := fun e => hj (by rw [e])
    have : (i >>> 1).toNat ≠ (j >>> 1).toNat := fun e => hj (UInt64.toNat_inj.mp e).symm
    rw [ite_eq_right (fun c => this c.1), ite_eq_right (fun c => hne c.1)]

/-- An id below a dense size that fits in `2^63` is not `TOMB`. -/
theorem ne_tomb_of_lt {i s : Word} (h : i < s) : i ≠ TOMB := by
  intro e; subst e; have := UInt64.lt_iff_toNat_lt.mp h; have := s.toNat_lt; rw [tomb_toNat] at *
  omega

theorem TblR.read (m : Mem) (b : ArrId) (t : ConLeche.Frontend.IdTable (Idx k)) (h : TblR m b t)
    (i : Word) (hok : tblOK m b i = true) :
    t.get? i.toNat = some (decI (tblW m b i)) ∧ (tblW m b i).toNat < 2 ^ 32 := by
  unfold tblOK at hok
  unfold tblW
  by_cases hs : i < szW m b
  · simp only [hs, ↓reduceIte]; exact h.dense i hs
  · simp only [hs, ↓reduceIte, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hok ⊢
    obtain ⟨⟨ht, hr⟩, hh⟩ := hok
    obtain ⟨sp, hR, hg⟩ := h.sparse
    obtain ⟨v, hv, hv1, hv2⟩ := memoRV_hit (spS b) idKey hVR m sp hR i 0 hr hh ⟨ht, rfl⟩
    rw [hg i hs]
    simp only [idKey] at hv
    rw [hv, hv1]
    exact ⟨rfl, hv2⟩

theorem TblR.fresh (m : Mem) (b : ArrId) (t : ConLeche.Frontend.IdTable (Idx k)) (h : TblR m b t)
    (i : Word) (hf : tblFresh m b i = true) : t.get? i.toNat = none := by
  unfold tblFresh at hf
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, bne_iff_ne, ne_eq,
    decide_eq_true_eq, beq_iff_eq] at hf
  obtain ⟨⟨⟨hs, ht⟩, hr⟩, hh⟩ := hf
  obtain ⟨sp, hR, hg⟩ := h.sparse
  rw [hg i hs]
  exact memoRV_miss (spS b) idKey hVR m sp hR i 0 ⟨ht, rfl⟩ hr hh

/-- A bound id is not `NONE` (`TOMB`). -/
theorem tblOK_ne_tomb {m : Mem} {b : ArrId} (i : Word) (hok : tblOK m b i = true) : i ≠ TOMB := by
  unfold tblOK at hok
  by_cases hs : i < szW m b
  · exact ne_tomb_of_lt hs
  · simp only [hs, ↓reduceIte, Bool.and_eq_true, bne_iff_ne] at hok; exact hok.1.1

/-- An unbound id is not `NONE` (`TOMB`). -/
theorem tblFresh_ne_tomb {m : Mem} {b : ArrId} (i : Word) (hf : tblFresh m b i = true) :
    i ≠ TOMB := by
  unfold tblFresh at hf
  simp only [Bool.and_eq_true, bne_iff_ne] at hf; exact hf.1.1.2

/-- What `tblOK`, `tblW`, `tblFresh` read of table `b`. -/
structure TblSame (m m' : Mem) (b : ArrId) : Prop where
  d : m'.arr64 b = m.arr64 b
  s : m'.arr64 (b + 8) = m.arr64 (b + 8)
  z : rdW (m'.arr64 CTL) (szC b) = rdW (m.arr64 CTL) (szC b)
  e : rdW (m'.arr64 CTL) (spS b).cs = rdW (m.arr64 CTL) (spS b).cs

theorem TblSame.of_frameD {A : List ArrId} {C : List Word} {m m' : Mem} {b : ArrId}
    (hf : MemFrame A C m m') (hb : TblIx b) (hbA : b ∉ A) (hb8 : b + 8 ∉ A) (hzC : szC b ∉ C)
    (heC : (spS b).cs ∉ C) : TblSame m m' b :=
  ⟨hf.1 b hbA (by rcases hb with rfl | rfl | rfl <;> decide),
    hf.1 _ hb8 (by rcases hb with rfl | rfl | rfl <;> decide), hf.2.1 _ hzC, hf.2.1 _ heC⟩

/-- Table `b`'s arrays and all of `CTL` unchanged. -/
theorem TblSame.of_eq {m m' : Mem} {b : ArrId} (h : m'.arr64 b = m.arr64 b)
    (h8 : m'.arr64 (b + 8) = m.arr64 (b + 8)) (hc : m'.arr64 CTL = m.arr64 CTL) :
    TblSame m m' b := ⟨h, h8, by rw [hc], by rw [hc]⟩

/-- Table `b`'s arrays and `CTL` words are outside a frame of arrays outside `idArrs` and `CTL`
words outside `idCtl`. -/
theorem tbl_apart {A : List ArrId} {C : List Word} {b : ArrId} (hb : TblIx b)
    (hA : ∀ x ∈ A, x ∉ idArrs) (hC : ∀ x ∈ C, x ∉ idCtl) :
    b ∉ A ∧ b + 8 ∉ A ∧ szC b ∉ C ∧ (spS b).cs ∉ C :=
  ⟨fun h => by have := hA b h; revert this; rcases hb with rfl | rfl | rfl <;> simp [idArrs],
    fun h => by have := hA _ h; revert this; rcases hb with rfl | rfl | rfl <;> simp [idArrs],
    fun h => by have := hC _ h; rcases hb with rfl | rfl | rfl <;> simp [szC, idCtl] at this,
    fun h => by have := hC _ h; rcases hb with rfl | rfl | rfl <;> simp [spS, idCtl] at this⟩

theorem TblSame.of_frame {A : List ArrId} {C : List Word} {m m' : Mem} {b : ArrId}
    (hf : MemFrame A C m m') (hb : TblIx b) (hA : ∀ x ∈ A, x ∉ idArrs)
    (hC : ∀ x ∈ C, x ∉ idCtl) : TblSame m m' b :=
  have h := tbl_apart hb hA hC
  TblSame.of_frameD hf hb h.1 h.2.1 h.2.2.1 h.2.2.2

theorem spF_congr {m m' : Mem} {b : ArrId} (h : TblSame m m' b) (i : Word) :
    spF m' b i = spF m b i := by
  exact mfindG_eq_of (spS b) h.s h.e i 0

theorem szW_congr {m m' : Mem} {b : ArrId} (h : TblSame m m' b) : szW m' b = szW m b := by
  simp only [szW, h.z]

theorem tblOK_congr {m m' : Mem} {b : ArrId} (h : TblSame m m' b) (i : Word) :
    tblOK m' b i = tblOK m b i := by
  unfold tblOK; rw [spF_congr h, szW_congr h, h.d]

theorem tblW_congr {m m' : Mem} {b : ArrId} (h : TblSame m m' b) (i : Word) :
    tblW m' b i = tblW m b i := by
  unfold tblW; rw [spF_congr h, szW_congr h, h.d]; simp only [mvG, spS, h.s]

/-- **The relation survives a writer of other arrays and `CTL` words.** -/
theorem TblR.frameD {A : List ArrId} {C : List Word} {m m' : Mem} {b : ArrId}
    {t : ConLeche.Frontend.IdTable (Idx k)} (h : TblR m b t) (hf : MemFrame A C m m')
    (hb : TblIx b) (hbA : b ∉ A) (hb8 : b + 8 ∉ A) (hzC : szC b ∉ C) (heC : (spS b).cs ∉ C) :
    TblR m' b t := by
  have hS := TblSame.of_frameD hf hb hbA hb8 hzC heC
  have hz : szW m' b = szW m b := szW_congr hS
  obtain ⟨sp, hR, hg⟩ := h.sparse
  refine ⟨by rw [hS.d]; exact h.size, by rw [hf.2.2.1]; exact h.ctl, by rw [hz, hS.d]; exact h.sz,
    fun i hi => ?_, ⟨sp, ?_, ?_⟩⟩
  · rw [hS.d]; exact h.dense i (hz ▸ hi)
  · exact memoRV_frame (spS b) (spS_wf b hb) idKey hVR A C hb8 heC m m' hf (fun _ _ h => h) sp hR
  · intro i hi; exact hg i (hz ▸ hi)

/-- **The relation survives a writer of arrays outside `idArrs` and `CTL` words outside `idCtl`.** -/
theorem TblR.frame {A : List ArrId} {C : List Word} {m m' : Mem} {b : ArrId}
    {t : ConLeche.Frontend.IdTable (Idx k)} (h : TblR m b t) (hf : MemFrame A C m m')
    (hb : TblIx b) (hA : ∀ x ∈ A, x ∉ idArrs) (hC : ∀ x ∈ C, x ∉ idCtl) :
    TblR m' b t :=
  have ha := tbl_apart hb hA hC
  h.frameD hf hb ha.1 ha.2.1 ha.2.2.1 ha.2.2.2

/-- **All-zero tables represent the empty table.** -/
theorem TblR.zero (m : Mem) (b : ArrId) (hb : TblIx b) (hz : ∀ b x, rdW (m.arr64 b) x = 0)
    (hs : (m.arr64 b).size < 2 ^ 63) (hctl : 73 ≤ (m.arr64 CTL).size) :
    TblR m b ({} : ConLeche.Frontend.IdTable (Idx k)) := by
  have hz0 : szW m b = 0 := hz _ _
  refine ⟨hs, by rcases hb with rfl | rfl | rfl <;> simp [szC] <;> omega, by rw [hz0]; simp,
    fun i hi => by rw [hz0] at hi; exact absurd hi (by simp), ⟨∅, ?_, fun i _ => by
      simp [ConLeche.Frontend.IdTable.get?]⟩⟩
  exact memoRV_zero (spS b) idKey hVR m hz (by rcases hb with rfl | rfl | rfl <;> simp [spS] <;> omega)

/-- The arrays and `CTL` words `tbl_put` writes. -/
theorem tblPutW_frame {m m' : Mem} {b : ArrId} (hb : TblIx b) {i w : Word}
    (h : tblPutW m b i w = some m') : MemFrame [b, b + 8] [szC b, (spS b).cs + 1] m m' := by
  have hbC : b ≠ CTL := by rcases hb with rfl | rfl | rfl <;> decide
  unfold tblPutW at h
  split at h
  · cases h
    exact ((MemFrame.set64 m b hbC _ _).mono (by simp) (by simp)).trans
      ((MemFrame.setCtl _ _ _).mono (by simp) (by simp))
  split at h
  · split at h
    · cases h; exact (MemFrame.set64 m b hbC _ _).mono (by simp) (by simp)
    · cases h
  split at h
  · cases h
  · exact (msetG_frame (spS b) (spS_wf b hb) m m' i 0 w h).mono (by simp [spS]) (by simp)

/-- **`tbl_put` binds the id**: from `t` to the table `t'` that is `t` with `i` bound to `w`. -/
theorem TblR.put {m m' : Mem} {b : ArrId} {t t' : ConLeche.Frontend.IdTable (Idx k)}
    (h : TblR m b t) (hb : TblIx b) (i w : Word) (hw : w.toNat < 2 ^ 32)
    (hp : tblPutW m b i w = some m')
    (ht' : ∀ j, t'.get? j = if j = i.toNat then some (decI w) else t.get? j) :
    TblR m' b t' := by
  have hbC : b ≠ CTL := by rcases hb with rfl | rfl | rfl <;> decide
  have hzs : szC b ≠ (spS b).cs := by rcases hb with rfl | rfl | rfl <;> decide
  have hS := spS_wf b hb
  have hsA : (spS b).arr ∉ [b] := by rcases hb with rfl | rfl | rfl <;> decide
  obtain ⟨sp, hR, hg⟩ := h.sparse
  have hsize := h.size
  have hsz := h.sz
  have hctl := h.ctl
  have hsA' : (spS b).arr ∉ ([b] : List ArrId) := hsA
  have hcs : (spS b).cs ∉ ([szC b] : List Word) := by simpa using hzs.symm
  have hcs0 : (spS b).cs ∉ ([] : List Word) := by simp
  unfold tblPutW at hp
  split at hp
  · -- the push at the frontier
    rename_i hc
    cases hp
    generalize hv : dnSet (rdW (m.arr64 b) (i >>> 1)) i w = v
    have hv' : (m.arr64 b).set! (i >>> 1).toNat v =
        (m.arr64 b).set! (i >>> 1).toNat (dnSet (rdW (m.arr64 b) (i >>> 1)) i w) := by rw [hv]
    obtain ⟨hi, hl⟩ := hc
    have hl' : (i >>> 1).toNat < (m.arr64 b).size := by
      have := UInt64.lt_iff_toNat_lt.mp hl; rw [len64_eq, toNat_ofNat_size _ hsize] at this; exact this
    have hl2 := shr1_toNat i
    have hi1 : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hctl' : (szC b).toNat < ((m.set64 b (i >>> 1) v).arr64 CTL).size := by
      rw [size_set64]; exact hctl
    have hz' : szW ((m.set64 b (i >>> 1) v).set64 CTL (szC b) (i + 1)) b = i + 1 := by
      simp only [szW, rdW_set64, hctl', and_self, ↓reduceIte]
    have hd : ((m.set64 b (i >>> 1) v).set64 CTL (szC b) (i + 1)).arr64 b =
        (m.set64 b (i >>> 1) v).arr64 b :=
      Mem.arr64_set64_ne _ _ _ _ _ hbC
    have hfr : MemFrame [b] [szC b] m ((m.set64 b (i >>> 1) v).set64 CTL (szC b) (i + 1)) :=
      ((MemFrame.set64 m b hbC (i >>> 1) v).mono (by simp) (by simp)).trans
        ((MemFrame.setCtl _ _ _).mono (by simp) (by simp))
    refine ⟨by rw [hd, size_set64]; exact hsize, by rw [size_set64, size_set64]; exact hctl,
      by rw [hz', hd, size_set64, hi1]; omega, fun j hj => ?_, ⟨sp, ?_, ?_⟩⟩
    · rw [hz', UInt64.lt_iff_toNat_lt, hi1] at hj
      rw [hd, Mem.arr64_set64_same, hv', dnW_set _ _ _ _ hw, ht']
      by_cases hji : j.toNat = i.toNat
      · have : j = i := UInt64.toNat_inj.mp hji
        subst this; simp only [↓reduceIte, hl', and_self]; exact ⟨trivial, hw⟩
      · have hji' : j ≠ i := fun e => hji (by rw [e])
        simp only [hji, ↓reduceIte, hji', false_and]
        exact h.dense j (by rw [UInt64.lt_iff_toNat_lt, ← hi]; omega)
    · exact memoRV_frame (spS b) hS idKey hVR [b] [szC b] hsA' hcs m _ hfr (fun _ _ h => h) sp hR
    · intro j hj
      rw [hz', UInt64.lt_iff_toNat_lt, hi1] at hj
      have hji : j.toNat ≠ i.toNat := by omega
      rw [ht', ite_eq_right hji]
      exact hg j (by rw [UInt64.lt_iff_toNat_lt, ← hi]; omega)
  split at hp
  · -- an overwrite below the frontier
    rename_i hs
    split at hp
    · rename_i hl'
      cases hp
      generalize hv : dnSet (rdW (m.arr64 b) (i >>> 1)) i w = v
      have hv' : (m.arr64 b).set! (i >>> 1).toNat v =
          (m.arr64 b).set! (i >>> 1).toNat (dnSet (rdW (m.arr64 b) (i >>> 1)) i w) := by rw [hv]
      have hz' : szW (m.set64 b (i >>> 1) v) b = szW m b := by
        simp only [szW]; rw [Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm hbC)]
      have hfr : MemFrame [b] [] m (m.set64 b (i >>> 1) v) := MemFrame.set64 m b hbC (i >>> 1) v
      refine ⟨by rw [size_set64]; exact hsize, by rw [size_set64]; exact hctl,
        by rw [hz', size_set64]; exact hsz, fun j hj => ?_, ⟨sp, ?_, ?_⟩⟩
      · rw [hz'] at hj
        rw [Mem.arr64_set64_same, hv', dnW_set _ _ _ _ hw, ht']
        by_cases hji : j.toNat = i.toNat
        · have : j = i := UInt64.toNat_inj.mp hji
          subst this; simp only [↓reduceIte, hl', and_self]; exact ⟨trivial, hw⟩
        · have hji' : j ≠ i := fun e => hji (by rw [e])
          simp only [hji, ↓reduceIte, hji', false_and]
          exact h.dense j hj
      · exact memoRV_frame (spS b) hS idKey hVR [b] [] hsA' hcs0 m _ hfr (fun _ _ h => h) sp hR
      · intro j hj
        rw [hz'] at hj
        have hji : j.toNat ≠ i.toNat := fun e => by
          rw [UInt64.toNat_inj.mp e] at hj; exact hj hs
        rw [ht', ite_eq_right hji]
        exact hg j hj
    · cases hp
  split at hp
  · cases hp
  · -- the sparse map
    rename_i _ hs ht
    have hfr := msetG_frame (spS b) hS m m' i 0 w hp
    have hd : m'.arr64 b = m.arr64 b :=
      hfr.1 b (by rcases hb with rfl | rfl | rfl <;> decide) hbC
    have hz' : szW m' b = szW m b := by
      simp only [szW]
      exact hfr.2.1 _ (by rcases hb with rfl | rfl | rfl <;> decide)
    have hR' := memoRV_set (spS b) hS idKey hVR (hVR_stable _) m sp hR i 0 w ⟨ht, rfl⟩ (decI w)
      ⟨rfl, hw⟩ m' hp
    refine ⟨by rw [hd]; exact hsize, by rw [hfr.2.2.1]; exact hctl, by rw [hz', hd]; exact hsz,
      fun j hj => ?_, ⟨_, hR', ?_⟩⟩
    · rw [hz'] at hj
      have hji : j.toNat ≠ i.toNat := fun e => by
        rw [UInt64.toNat_inj.mp e] at hj; exact hs hj
      rw [hd, ht', ite_eq_right hji]
      exact h.dense j hj
    · intro j hj
      rw [hz'] at hj
      rw [ht', Std.HashMap.getElem?_insert]
      simp only [idKey, beq_iff_eq]
      by_cases hji : j.toNat = i.toNat
      · simp [hji]
      · rw [ite_eq_right hji, ite_eq_right (Ne.symm hji)]; exact hg j hj

end tbl

end L.Front
