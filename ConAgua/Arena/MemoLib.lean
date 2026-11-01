module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
public import ConAgua.Arena.SlotGrow
public import ConAgua.L.Logic
public import ConAgua.L.Notation
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.LdRd
import ConAgua.L.GrindAttr
import Std.Data.DTreeMap.Internal.Operations
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import ConAgua.Front.Preserve

@[expose] public section

/-!
# The memo library: per-call memo tables with two-word keys and epoch stamps

con-ron's arena keeps six per-call memos keyed `(EIdx × Nat)` (`inst1C`, `instLC`, `liftC`,
`abs1C`, `inst1LC`, `instLPC`), two keyed `EIdx` (`bvarBC`, `fvarBC`) and two level ones
(`Arena/Monad.lean`'s `Memos`); con-ron's Rust keeps them in `HashMap2` (`ron/hashmap2.rs`): open
addressing, linear probing, an **epoch stamp** per slot so that `clear` is `epoch += 1`.

A memo here is a **schema** `MemoSch`: a word array `arr` and a `CTL` index `cs` (`CTL[cs]` is the
live stamp minus one, `CTL[cs + 1]` the live count). Four words per slot: the stamp, the key's two
words, the value. A one-word key (`bvarBC`) is the two-word key with second word `0`. Slot `j` is
**live** iff its stamp is `CTL[cs] + 1`; anything else is free space, so all-zero memory is an
empty memo.

The L code is **generic in the schema**: `memoFindG S`, `memoPutG S`, `memoClearG S` are Lean
functions producing L functions with the schema's array and `CTL` words spliced in (`S.arr.u64[…]`,
`CTL.u64[⟪S.cs⟫]`), and their `vcgen` specs are proved once, for a variable schema. An instance is
three entries of the program (`("bm_find", memoFindG bmSch)`, …) and no proof.

* `X_find(k1, k2)`: the probe from `mhome k1 k2 n`, the high word of `((k1 + k2 * golden) * golden) * n`
  (a multiplicative hash), returning `(found, slot, steps)`. Both halves of `k2` enter the hash:
  banked memos (`MemoBank.genW`), the eager bit and `rrSch` keep a second component in `k2`'s high
  half (lane `rfhash`: with only `k2 << 32` it was shifted out, and all banks' entries for one `k1`
  shared one probe cluster).
* `X_put(k1, k2, v, fd, j)`: given the probe's `fd`, `j` **on the current memory**, write the
  value (and on a miss, the stamp and the key, growing the table past 3/4 load, con-ron's `HashMap2` load factor). Callers probe right
  before (`set` = `find; put`); a walk that recursed since its first probe probes again.
* `X_clear()`: `CTL[cs] += 1`, `CTL[cs + 1] := 0`, aborting where the stamp would wrap.
* `X_clear_fit()`: `X_clear()` that also sizes the next round's region, as the twin's
  `HashMap2::clear_fit` (below).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- A memo table: its slot array and the `CTL` index of its stamp (`cs`) and count (`cs + 1`). -/
structure MemoSch where
  arr : ArrId
  cs : Word

/-- The live stamp, `CTL[cs] + 1`. -/
def epG (S : MemoSch) (m : Mem) : Word := rdW (m.arr64 CTL) S.cs + 1

/-- The default region's slot count. -/
def MN0 : Word := 16384

/-- The default region's size on an array of `l` words: `MN0` slots after the header slot, or as
many as fit. -/
def dfltN (l : Word) : Word :=
  if MN0 < (l >>> 2) - (if (0 : Word) < l >>> 2 then 1 else 0) then MN0
  else (l >>> 2) - (if (0 : Word) < l >>> 2 then 1 else 0)

/-- `dfltN` as the L code computes it: the cap first, so that a large array takes one branch. -/
theorem dfltN_alt (l : Word) :
    dfltN l = if MN0 < l >>> 2 then MN0 else (l >>> 2) - (if (0 : Word) < l >>> 2 then 1 else 0) := by
  unfold dfltN
  generalize l >>> 2 = L
  have hM : MN0.toNat = 16384 := rfl
  by_cases h0 : L = 0
  · subst h0; decide
  · have hL : L.toNat ≠ 0 := fun h => h0 (UInt64.toNat_inj.mp (by simpa using h))
    have hp : (0 : Word) < L := UInt64.lt_iff_toNat_lt.mpr (by simp; omega)
    have hs : (L - 1).toNat = L.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp
    simp only [hp, ↓reduceIte]
    by_cases h1 : MN0 < L - 1
    · have : MN0 < L := UInt64.lt_iff_toNat_lt.mpr (by have := UInt64.lt_iff_toNat_lt.mp h1; omega)
      simp [h1, this]
    · by_cases h2 : MN0 < L
      · simp only [h1, h2, ↓reduceIte]
        apply UInt64.toNat_inj.mp
        have a := UInt64.lt_iff_toNat_lt.mp h2
        have b := mt UInt64.lt_iff_toNat_lt.mpr h1
        omega
      · simp [h1, h2]

/-- The header (slot 0) names the region: its first word is the live stamp. -/
def hdG (S : MemoSch) (m : Mem) : Prop := rdW (m.arr64 S.arr) 0 = epG S m

/-- The region's first slot: the header's word 1, or slot `1`. -/
def mbG (S : MemoSch) (m : Mem) : Word :=
  if rdW (m.arr64 S.arr) 0 = epG S m then rdW (m.arr64 S.arr) 1 else 1

/-- The region's slot count: the header's word 2, or the default. -/
def nG (S : MemoSch) (m : Mem) : Word :=
  if rdW (m.arr64 S.arr) 0 = epG S m then rdW (m.arr64 S.arr) 2 else dfltN (m.len64 S.arr)

/-- The live count, `CTL[cs + 1]` (only the load limit reads it). -/
def cntG (S : MemoSch) (m : Mem) : Word := rdW (m.arr64 CTL) (S.cs + 1)

/-- The hash of a two-word key: every bit of `k2` reaches the high bits of `k2 * golden`, and the
second multiplication spreads `k1` (and that sum) into the high bits, which `mhome` reads. -/
def kh (k1 k2 : Word) : Word := (k1 + k2 * golden) * golden

/-- The home slot of key `(k1, k2)` in a region of `n` slots: the high word of `kh k1 k2 * n`. -/
def mhome (k1 k2 n : Word) : Word := UInt64.ofNat ((kh k1 k2).toNat * n.toNat / 2 ^ 64)

theorem mhome_lt (k1 k2 n : Word) (hn : 0 < n) : mhome k1 k2 n < n := by
  simp only [mhome]
  have hx := (kh k1 k2).toNat_lt
  have hn' := n.toNat_lt
  have : (kh k1 k2).toNat * n.toNat / 2 ^ 64 < n.toNat :=
    Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_pos_right hx (by grind))
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; exact this

/-! ## `X_find(k1, k2)`: the probe -/

/-- The model of the probe loop in the region from slot `b` of `n` slots, from its slot `j` after
`d` steps, live stamp `e`; slots are reported by their index in the array, `b + j`. -/
def mprobeG (mm : Array Word) (k1 k2 e b n j d : Word) : List Word :=
  if d < n then
    if rdW mm ((b + j) * 4) ≠ e then [0, b + j, d]
    else if rdW mm ((b + j) * 4 + 1) = k1 ∧ rdW mm ((b + j) * 4 + 2) = k2 then [1, b + j, d]
    else mprobeG mm k1 k2 e b n ((j + 1) * (if j + 1 < n then 1 else 0)) (d + 1)
  else []
termination_by n.toNat - d.toNat
decreasing_by
  have : d.toNat < n.toNat := by simpa [UInt64.lt_iff_toNat_lt] using ‹d < n›
  have := n.toNat_lt
  have : (d + 1).toNat = d.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  omega

section probeArms
variable (mm : Array Word) (k1 k2 e b n j d : Word)

theorem mprobeG_free (a : Nat) (hd : d < n) (ha : a = ((b + j) * 4).toNat) (has : a < mm.size)
    (hv : mm[a] ≠ e) : mprobeG mm k1 k2 e b n j d = [0, b + j, d] := by
  rw [mprobeG]; simp only [hd, ↓reduceIte, rdW_eq mm _ a ha has, hv, ne_eq, not_false_eq_true]

theorem mprobeG_hit (a a1 a2 : Nat) (hd : d < n) (ha : a = ((b + j) * 4).toNat) (has : a < mm.size)
    (hb : a1 = ((b + j) * 4 + 1).toNat) (hbs : a1 < mm.size) (hc : a2 = ((b + j) * 4 + 2).toNat)
    (hcs : a2 < mm.size) (hv : mm[a] = e) (hk : mm[a1] = k1) (hk2 : mm[a2] = k2) :
    mprobeG mm k1 k2 e b n j d = [1, b + j, d] := by
  rw [mprobeG]; simp only [hd, ↓reduceIte, rdW_eq mm _ a ha has, rdW_eq mm _ a1 hb hbs,
    rdW_eq mm _ a2 hc hcs, hv, hk, hk2, ne_eq, not_true_eq_false, and_self]

theorem mprobeG_next1 (a a1 : Nat) (j' d' : Word) (hd : d < n) (ha : a = ((b + j) * 4).toNat)
    (has : a < mm.size) (hb : a1 = ((b + j) * 4 + 1).toNat) (hbs : a1 < mm.size) (hv : mm[a] = e)
    (hk : mm[a1] ≠ k1) (hj' : j' = (j + 1) * (if j + 1 < n then 1 else 0)) (hd' : d' = d + 1) :
    mprobeG mm k1 k2 e b n j d = mprobeG mm k1 k2 e b n j' d' := by
  subst hj' hd'
  rw [mprobeG]; simp only [hd, ↓reduceIte, rdW_eq mm _ a ha has, rdW_eq mm _ a1 hb hbs, hv, hk,
    ne_eq, not_true_eq_false, false_and]

theorem mprobeG_next2 (a a1 a2 : Nat) (j' d' : Word) (hd : d < n) (ha : a = ((b + j) * 4).toNat)
    (has : a < mm.size) (hb : a1 = ((b + j) * 4 + 1).toNat) (hbs : a1 < mm.size)
    (hc : a2 = ((b + j) * 4 + 2).toNat) (hcs : a2 < mm.size) (hv : mm[a] = e)
    (hk : mm[a1] = k1) (hk2 : mm[a2] ≠ k2) (hj' : j' = (j + 1) * (if j + 1 < n then 1 else 0))
    (hd' : d' = d + 1) :
    mprobeG mm k1 k2 e b n j d = mprobeG mm k1 k2 e b n j' d' := by
  subst hj' hd'
  rw [mprobeG]; simp only [hd, ↓reduceIte, rdW_eq mm _ a ha has, rdW_eq mm _ a1 hb hbs,
    rdW_eq mm _ a2 hc hcs, hv, hk, hk2, ne_eq, not_true_eq_false, true_and]

theorem mprobeG_end (hd : ¬ d < n) : mprobeG mm k1 k2 e b n j d = [] := by
  rw [mprobeG]; simp only [hd, ↓reduceIte]

end probeArms

grind_pattern [arena_grind] mprobeG_free => mprobeG mm k1 k2 e b n j d, mm[a]
grind_pattern [arena_grind] mprobeG_hit => mprobeG mm k1 k2 e b n j d, mm[a], mm[a1], mm[a2]
grind_pattern [arena_grind] mprobeG_next1 =>
  mprobeG mm k1 k2 e b n j d, mm[a], mm[a1], mprobeG mm k1 k2 e b n j' d'
grind_pattern [arena_grind] mprobeG_next2 =>
  mprobeG mm k1 k2 e b n j d, mm[a], mm[a1], mm[a2], mprobeG mm k1 k2 e b n j' d'

def mfindLoopG (S : MemoSch) : Stmt := lblk (k1, k2, n, e, j, d, b) {
  for d < n {
    if S.arr.u64[(b + j) * 4] != e { return (0, b + j, d) };
    if S.arr.u64[(b + j) * 4 + 1] == k1 && S.arr.u64[(b + j) * 4 + 2] == k2 { return (1, b + j, d) };
    j := (j + 1) * u64(j + 1 < n)
  }
}

/-- con-ron: none — the memo library (open addressing over fixed arrays; the twin's `Std.HashMap` caches) -/
@[no_expose] def memoFindG (S : MemoSch) : FunDecl := lfn (k1, k2) locals (n, e, j, d, b) {
  e := CTL.u64[⟪S.cs⟫] + 1;
  if S.arr.u64[0] == e {
    b := S.arr.u64[1];
    n := S.arr.u64[2]
  } else {
    b := 1;
    n := len(S.arr.u64) >> 2;
    if n > ⟪MN0⟫ { n := ⟪MN0⟫ } else { n := n - u64(n > 0) }
  };
  j := k2 * ⟪golden⟫;
  j := (j + k1) * ⟪golden⟫;
  j := mulhi(j, n);
  ⟪mfindLoopG S⟫;
  abort
}

section find
variable (S : MemoSch) (p : Prog)

theorem mfindLoopG_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n (mfindLoopG S)
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (mprobeG (s₀.mem.arr64 S.arr) (s₀.loc 0) (s₀.loc 1) (s₀.loc 3) (s₀.loc 6)
        (s₀.loc 2) (s₀.loc 4) (s₀.loc 5)) =
      mprobeG (s₀.mem.arr64 S.arr) (s₀.loc 0) (s₀.loc 1) (s₀.loc 3) (s₀.loc 6) (s₀.loc 2)
        (s₀.loc 4) (s₀.loc 5); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := mfindLoopG S) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;> finish

theorem mfindLoopG_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mfindLoopG S)
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (mprobeG (s₀.mem.arr64 S.arr) (s₀.loc 0) (s₀.loc 1) (s₀.loc 3) (s₀.loc 6)
        (s₀.loc 2) (s₀.loc 4) (s₀.loc 5)) =
      mprobeG (s₀.mem.arr64 S.arr) (s₀.loc 0) (s₀.loc 1) (s₀.loc 3) (s₀.loc 6) (s₀.loc 2)
        (s₀.loc 4) (s₀.loc 5); ⊤⦄ :=
  Triple.step_exec (mfindLoopG_spec S p (n + 1) s₀)

/-- The probe of the memo for key `(k1, k2)`. -/
def mfindG (m : Mem) (k1 k2 : Word) : List Word :=
  mprobeG (m.arr64 S.arr) k1 k2 (epG S m) (mbG S m) (nG S m) (mhome k1 k2 (nG S m)) 0

/-- The probe reads the memo's array and its stamp only. -/
theorem mfindG_eq_of {m₁ m₂ : Mem} (ha : m₂.arr64 S.arr = m₁.arr64 S.arr)
    (hc : rdW (m₂.arr64 CTL) S.cs = rdW (m₁.arr64 CTL) S.cs) (k1 k2 : Word) :
    mfindG S m₂ k1 k2 = mfindG S m₁ k1 k2 := by
  have he : epG S m₂ = epG S m₁ := by simp only [epG, hc]
  simp only [mfindG, nG, mbG, Mem.len64]
  rw [ha, he]

theorem memoFindG_spec (f : FnName) (hp : p.lookup f = some (memoFindG S)) (n : Nat) (s₀ : St)
    (k1 k2 : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) f [k1, k2]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧ r = mfindG S s₀.mem k1 k2; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, memoFindG]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64_rd_spec, mfindLoopG_step_spec S p n]
    all_goals subst_vars
    all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, Locals.init_cons_zero, Locals.init_cons_succ,
      Cmp.eval, BinOp.eval, Nat.reduceEqDiff, reduceIte, beq_iff_eq, decide_eq_true_eq] at *)
    all_goals grind [lang_grind, arena_grind, mfindG, nG, mbG, hdG, epG, dfltN_alt, mhome, kh, Mem.len64]

end find

/-! ## `X_put(k1, k2, v, fd, j)`

On a miss that would fill the region past 3/4 of its slots, `put` first **grows** the table: it
moves the live slots (not the tombstones) into a fresh region of twice the size right above the
current one, names the new region in the header (stamp, first slot, slot count) and probes the new
region for the key. Regions only move up within one stamp, so a fresh region holds no live slot;
`clear` (a new stamp) invalidates the header and so returns to the default region. The map the
memo represents is unchanged by a growth: con-ron's `Std.HashMap` grows, too. -/

/-- The first key word of a deleted slot (`X_erase`, below). -/
def TOMB : Word := 0xFFFFFFFFFFFFFFFF

/-- The four words of slot `s`: stamp, key, value. -/
def mput4 (S : MemoSch) (m : Mem) (s e x y w : Word) : Mem :=
  (((m.set64 S.arr (s * 4) e).set64 S.arr (s * 4 + 1) x).set64 S.arr (s * 4 + 2) y).set64 S.arr
    (s * 4 + 3) w

/-- The probe for a free slot for key `(x, y)` in the region from slot `b` of `n` slots. -/
def mslotG (mm : Array Word) (x y e b n : Word) : List Word :=
  mprobeG mm x y e b n (mhome x y n) 0

/-- The model of the rehash loop: from old slot `i`, moved count `c`; `none` where L aborts. -/
def mrehashG (S : MemoSch) (e nb nn : Word) (i c : Word) (m : Mem) : Option (Mem × Word) :=
  if i < nb then
    if rdW (m.arr64 S.arr) (i * 4) = e ∧ rdW (m.arr64 S.arr) (i * 4 + 1) ≠ TOMB then
      if mslotG (m.arr64 S.arr) (rdW (m.arr64 S.arr) (i * 4 + 1)) (rdW (m.arr64 S.arr) (i * 4 + 2))
          e nb nn ≠ [] ∧
        (mslotG (m.arr64 S.arr) (rdW (m.arr64 S.arr) (i * 4 + 1)) (rdW (m.arr64 S.arr) (i * 4 + 2))
          e nb nn).headD 0 = 0 then
        mrehashG S e nb nn (i + 1) (c + 1)
          (mput4 S m ((mslotG (m.arr64 S.arr) (rdW (m.arr64 S.arr) (i * 4 + 1))
            (rdW (m.arr64 S.arr) (i * 4 + 2)) e nb nn).tail.headD 0) e
            (rdW (m.arr64 S.arr) (i * 4 + 1)) (rdW (m.arr64 S.arr) (i * 4 + 2))
            (rdW (m.arr64 S.arr) (i * 4 + 3)))
      else none
    else mrehashG S e nb nn (i + 1) c m
  else some (m, c)
termination_by nb.toNat - i.toNat
decreasing_by
  all_goals
    have : i.toNat < nb.toNat := by simpa [UInt64.lt_iff_toNat_lt] using ‹i < nb›
    have := nb.toNat_lt
    have : (i + 1).toNat = i.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; omega
    omega

/-- The model of the growth of the region from slot `b` of `n` slots at live stamp `e`: the
memory and the moved count, `none` where L aborts. -/
def mgrowAt (S : MemoSch) (e b n : Word) (m : Mem) : Option (Mem × Word) :=
  if n * 2 = 0 then none
  else if (m.len64 S.arr >>> 2) < b + n + n * 2 then none
  else match mrehashG S e (b + n) (n * 2) b 0 m with
    | none => none
    | some (m', c) =>
      some ((((m'.set64 S.arr 0 e).set64 S.arr 1 (b + n)).set64 S.arr 2 (n * 2)).set64 CTL
        (S.cs + 1) c, c)

/-- The memory after `X_put`'s writes at slot `j` (`fd ≠ 0`: the key is there), with stamp `e`
and count `c` (the count before). -/
def mputMemE (S : MemoSch) (m : Mem) (fd j k1 k2 v e c : Word) : Mem :=
  if fd = 0 then
    ((((m.set64 S.arr (j * 4) e).set64 S.arr (j * 4 + 1) k1).set64 S.arr (j * 4 + 2)
      k2).set64 CTL (S.cs + 1) (c + 1)).set64 S.arr (j * 4 + 3) v
  else m.set64 S.arr (j * 4 + 3) v

/-- The memory after `X_put` at slot `j` (`fd ≠ 0`: the key is there). -/
def mputMem (S : MemoSch) (m : Mem) (fd j k1 k2 v : Word) : Mem :=
  mputMemE S m fd j k1 k2 v (epG S m) (cntG S m)

/-- The model of `X_put`: the memory after, `none` where the L code aborts. -/
def mputG (S : MemoSch) (m : Mem) (k1 k2 v fd j : Word) : Option Mem :=
  if fd = 0 ∧ nG S m * 3 < (cntG S m + 1) * 4 then
    match mgrowAt S (epG S m) (mbG S m) (nG S m) m with
    | none => none
    | some (m₁, c) =>
      if mslotG (m₁.arr64 S.arr) k1 k2 (epG S m) (mbG S m + nG S m) (nG S m * 2) ≠ [] ∧
        (mslotG (m₁.arr64 S.arr) k1 k2 (epG S m) (mbG S m + nG S m) (nG S m * 2)).headD 0 = 0 then
        some (mputMemE S m₁ 0 ((mslotG (m₁.arr64 S.arr) k1 k2 (epG S m) (mbG S m + nG S m)
          (nG S m * 2)).tail.headD 0) k1 k2 v (epG S m) c)
      else none
  else some (mputMem S m fd j k1 k2 v)

/-- `set` = `find; put`: the model of a probe followed by a put on the same memory. -/
def msetG (S : MemoSch) (m : Mem) (k1 k2 v : Word) : Option Mem :=
  if mfindG S m k1 k2 = [] then none
  else mputG S m k1 k2 v ((mfindG S m k1 k2).headD 0) ((mfindG S m k1 k2).tail.headD 0)

/-- The free-slot probe loop of the growth (variables of `memoPutG`): key `(x, y)` (10, 11),
region `b`, `n` (7, 8; the new region while growing), stamp `e` (6), slot `j` (4), step `d` (9).
A live slot with the key aborts. -/
def mslotLoopG (S : MemoSch) : Stmt :=
  lblk (k1, k2, v, fd, j, c, e, b, n, d, x, y, w) {
  while d < n && S.arr.u64[(b + j) * 4] == e {
    if S.arr.u64[(b + j) * 4 + 1] == x && S.arr.u64[(b + j) * 4 + 2] == y { abort };
    j := (j + 1) * u64(j + 1 < n);
    d += 1
  }
}

/-- A free slot for key `(x, y)` in the region `b`, `n`, into `j`; aborts if there is none. -/
def mslotBlkG (S : MemoSch) : Stmt :=
  lblk (k1, k2, v, fd, j, c, e, b, n, d, x, y, w) {
  j := y * ⟪golden⟫;
  j := (j + x) * ⟪golden⟫;
  j := mulhi(j, n);
  d := 0;
  ⟪mslotLoopG S⟫;
  if d >= n { abort };
  j := b + j
}

/-- Move the live slot `fd` to a free slot of the region `b`, `n`; count it in `c`. -/
def mmoveG (S : MemoSch) : Stmt :=
  lblk (k1, k2, v, fd, j, c, e, b, n, d, x, y, w) {
  x := S.arr.u64[fd * 4 + 1];
  y := S.arr.u64[fd * 4 + 2];
  w := S.arr.u64[fd * 4 + 3];
  ⟪mslotBlkG S⟫;
  S.arr.u64[j * 4] := e;
  S.arr.u64[j * 4 + 1] := x;
  S.arr.u64[j * 4 + 2] := y;
  S.arr.u64[j * 4 + 3] := w;
  c += 1
}

/-- One step of the rehash loop: move slot `fd` if it is live and not a tombstone. -/
def mstepG (S : MemoSch) : Stmt :=
  lblk (k1, k2, v, fd, j, c, e, b, n, d, x, y, w) {
  if S.arr.u64[fd * 4] == e && S.arr.u64[fd * 4 + 1] != ⟪TOMB⟫ { ⟪mmoveG S⟫ };
  fd += 1
}

/-- The rehash loop: every live slot `fd` of the old region (up to `b`, the new region's first
slot) that is not a tombstone moves to a free slot of the new region `b`, `n`; `c` counts them. -/
def mrehashLoopG (S : MemoSch) : Stmt :=
  lblk (k1, k2, v, fd, j, c, e, b, n, d, x, y, w) {
  while fd < b { ⟪mstepG S⟫ }
}

/-- The growth (variables of `memoPutG`): rehash the region `b`, `n` into `b + n`, `2 n` (from
here on `fd` is the old slot and `b`, `n` the new region), name it in the header, set the count,
and find the free slot `j` for the key `(k1, k2)` there. -/
def mgrowBlkG (S : MemoSch) : Stmt :=
  lblk (k1, k2, v, fd, j, c, e, b, n, d, x, y, w) {
  fd := b;
  b := b + n;
  n := n * 2;
  if n == 0 { abort };
  if (len(S.arr.u64) >> 2) < b + n { abort };
  c := 0;
  ⟪mrehashLoopG S⟫;
  S.arr.u64[0] := e;
  S.arr.u64[1] := b;
  S.arr.u64[2] := n;
  CTL.u64[⟪S.cs + 1⟫] := c;
  x := k1;
  y := k2;
  ⟪mslotBlkG S⟫
}

/-- con-ron: none — the memo library (open addressing over fixed arrays; the twin's `Std.HashMap` caches)

A leaf with 13 locals: the growth reuses `fd`, `j` and the region's `b`, `n`, so that the leaf
register allocation keeps the common path (no growth) in registers; `fd` also holds `4 j` for the
key's three stores. -/
@[no_expose] def memoPutG (S : MemoSch) : FunDecl :=
  lfn (k1, k2, v, fd, j) locals (c, e, b, n, d, x, y, w) {
  if fd == 0 {
    c := CTL.u64[⟪S.cs + 1⟫];
    e := CTL.u64[⟪S.cs⟫] + 1;
    if S.arr.u64[0] == e {
      b := S.arr.u64[1];
      n := S.arr.u64[2]
    } else {
      b := 1;
      n := len(S.arr.u64) >> 2;
      if n > ⟪MN0⟫ { n := ⟪MN0⟫ } else { n := n - u64(n > 0) }
    };
    if n * 3 < (c + 1) * 4 { ⟪mgrowBlkG S⟫ };
    fd := j * 4;
    S.arr.u64[fd] := e;
    S.arr.u64[fd + 1] := k1;
    S.arr.u64[fd + 2] := k2;
    CTL.u64[⟪S.cs + 1⟫] := c + 1
  };
  S.arr.u64[j * 4 + 3] := v;
  return 0
}

section put
variable (S : MemoSch) (p : Prog)

theorem mslotLoopG_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n (mslotLoopG S)
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧ (∀ z, z ≠ 4 → z ≠ 9 → s'.loc z = s₀.loc z) ∧
      mprobeG (s₀.mem.arr64 S.arr) (s₀.loc 10) (s₀.loc 11) (s₀.loc 6) (s₀.loc 7) (s₀.loc 8)
        (s₀.loc 4) (s₀.loc 9) =
      if s'.loc 9 < s₀.loc 8 then [0, s₀.loc 7 + s'.loc 4, s'.loc 9] else []; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := mslotLoopG S) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;> finish [mprobeG_end]

theorem mslotLoopG_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mslotLoopG S)
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧ (∀ z, z ≠ 4 → z ≠ 9 → s'.loc z = s₀.loc z) ∧
      mprobeG (s₀.mem.arr64 S.arr) (s₀.loc 10) (s₀.loc 11) (s₀.loc 6) (s₀.loc 7) (s₀.loc 8)
        (s₀.loc 4) (s₀.loc 9) =
      if s'.loc 9 < s₀.loc 8 then [0, s₀.loc 7 + s'.loc 4, s'.loc 9] else []; ⊤⦄ :=
  Triple.step_exec (mslotLoopG_spec S p (n + 1) s₀)

theorem mslotBlkG_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mslotBlkG S)
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧ (∀ z, z ≠ 4 → z ≠ 9 → s'.loc z = s₀.loc z) ∧
      mslotG (s₀.mem.arr64 S.arr) (s₀.loc 10) (s₀.loc 11) (s₀.loc 6) (s₀.loc 7) (s₀.loc 8) ≠ [] ∧
      (mslotG (s₀.mem.arr64 S.arr) (s₀.loc 10) (s₀.loc 11) (s₀.loc 6) (s₀.loc 7)
        (s₀.loc 8)).headD 0 = 0 ∧
      s'.loc 4 = (mslotG (s₀.mem.arr64 S.arr) (s₀.loc 10) (s₀.loc 11) (s₀.loc 6) (s₀.loc 7)
        (s₀.loc 8)).tail.headD 0; ⊤⦄ := by
  simp only [mslotBlkG]
  sym only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalC, evalArgs, setLoc, mslotLoopG_step_spec S p] <;>
    finish [mslotG, mhome, kh]

section rehashArms
variable (S : MemoSch) (e nb nn i c : Word) (m : Mem)

theorem mrehashG_end (h : ¬ i < nb) : mrehashG S e nb nn i c m = some (m, c) := by
  rw [mrehashG]; simp only [h, ↓reduceIte]

theorem mrehashG_skip (h : i < nb)
    (hl : ¬ (rdW (m.arr64 S.arr) (i * 4) = e ∧ rdW (m.arr64 S.arr) (i * 4 + 1) ≠ TOMB)) :
    mrehashG S e nb nn i c m = mrehashG S e nb nn (i + 1) c m := by
  rw [mrehashG]; simp only [h, hl, ↓reduceIte]

theorem mrehashG_move (h : i < nb)
    (hl : rdW (m.arr64 S.arr) (i * 4) = e ∧ rdW (m.arr64 S.arr) (i * 4 + 1) ≠ TOMB)
    (hs : mslotG (m.arr64 S.arr) (rdW (m.arr64 S.arr) (i * 4 + 1)) (rdW (m.arr64 S.arr) (i * 4 + 2))
          e nb nn ≠ [] ∧
        (mslotG (m.arr64 S.arr) (rdW (m.arr64 S.arr) (i * 4 + 1)) (rdW (m.arr64 S.arr) (i * 4 + 2))
          e nb nn).headD 0 = 0) :
    mrehashG S e nb nn i c m = mrehashG S e nb nn (i + 1) (c + 1)
      (mput4 S m ((mslotG (m.arr64 S.arr) (rdW (m.arr64 S.arr) (i * 4 + 1))
        (rdW (m.arr64 S.arr) (i * 4 + 2)) e nb nn).tail.headD 0) e
        (rdW (m.arr64 S.arr) (i * 4 + 1)) (rdW (m.arr64 S.arr) (i * 4 + 2))
        (rdW (m.arr64 S.arr) (i * 4 + 3))) := by
  rw [mrehashG, ite_eq_left h, ite_eq_left hl, ite_eq_left hs]

end rehashArms

theorem mmoveG_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mmoveG S)
    ⦃fun r s' => r = .normal ∧ (∀ z, z < 9 → z ≠ 4 → z ≠ 5 → s'.loc z = s₀.loc z) ∧
      s'.loc 5 = s₀.loc 5 + 1 ∧
      mslotG (s₀.mem.arr64 S.arr) (rdW (s₀.mem.arr64 S.arr) (s₀.loc 3 * 4 + 1))
        (rdW (s₀.mem.arr64 S.arr) (s₀.loc 3 * 4 + 2)) (s₀.loc 6) (s₀.loc 7) (s₀.loc 8) ≠ [] ∧
      (mslotG (s₀.mem.arr64 S.arr) (rdW (s₀.mem.arr64 S.arr) (s₀.loc 3 * 4 + 1))
        (rdW (s₀.mem.arr64 S.arr) (s₀.loc 3 * 4 + 2)) (s₀.loc 6) (s₀.loc 7)
        (s₀.loc 8)).headD 0 = 0 ∧
      s'.mem = mput4 S s₀.mem ((mslotG (s₀.mem.arr64 S.arr) (rdW (s₀.mem.arr64 S.arr) (s₀.loc 3 * 4 + 1))
        (rdW (s₀.mem.arr64 S.arr) (s₀.loc 3 * 4 + 2)) (s₀.loc 6) (s₀.loc 7)
        (s₀.loc 8)).tail.headD 0) (s₀.loc 6)
        (rdW (s₀.mem.arr64 S.arr) (s₀.loc 3 * 4 + 1)) (rdW (s₀.mem.arr64 S.arr) (s₀.loc 3 * 4 + 2))
        (rdW (s₀.mem.arr64 S.arr) (s₀.loc 3 * 4 + 3)); ⊤⦄ := by
  simp only [mmoveG]
  sym only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalC, evalArgs, setLoc, ld64, st64, mslotBlkG_step_spec S p] <;>
    finish [mput4]

theorem mstepG_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mstepG S)
    ⦃fun r s' => r = .normal ∧ (∀ z, z < 9 → z ≠ 3 → z ≠ 4 → z ≠ 5 → s'.loc z = s₀.loc z) ∧
      s'.loc 3 = s₀.loc 3 + 1 ∧
      (s₀.loc 3 < s₀.loc 7 →
        mrehashG S (s₀.loc 6) (s₀.loc 7) (s₀.loc 8) (s₀.loc 3) (s₀.loc 5) s₀.mem =
          mrehashG S (s₀.loc 6) (s₀.loc 7) (s₀.loc 8) (s'.loc 3) (s'.loc 5) s'.mem); ⊤⦄ := by
  simp only [mstepG]
  sym only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalC, evalArgs, setLoc, ld64, mmoveG_step_spec S p] <;>
    finish [mrehashG_skip, mrehashG_move]

theorem mrehashLoopG_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n (mrehashLoopG S)
    ⦃fun r s' => r = .normal ∧ (∀ z, z < 9 → z ≠ 3 → z ≠ 4 → z ≠ 5 → s'.loc z = s₀.loc z) ∧
      mrehashG S (s₀.loc 6) (s₀.loc 7) (s₀.loc 8) (s₀.loc 3) (s₀.loc 5) s₀.mem =
        some (s'.mem, s'.loc 5); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := mrehashLoopG S) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, ih, mstepG_step_spec S p] <;>
      finish [mrehashG_end]

theorem mrehashLoopG_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mrehashLoopG S)
    ⦃fun r s' => r = .normal ∧ (∀ z, z < 9 → z ≠ 3 → z ≠ 4 → z ≠ 5 → s'.loc z = s₀.loc z) ∧
      mrehashG S (s₀.loc 6) (s₀.loc 7) (s₀.loc 8) (s₀.loc 3) (s₀.loc 5) s₀.mem =
        some (s'.mem, s'.loc 5); ⊤⦄ :=
  Triple.step_exec (mrehashLoopG_spec S p (n + 1) s₀)

end put

theorem mgrowBlkG_step_spec (S : MemoSch) (p : Prog) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mgrowBlkG S)
    ⦃fun r s' => r = .normal ∧ s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧
      s'.loc 6 = s₀.loc 6 ∧
      mgrowAt S (s₀.loc 6) (s₀.loc 7) (s₀.loc 8) s₀.mem = some (s'.mem, s'.loc 5) ∧
      mslotG (s'.mem.arr64 S.arr) (s₀.loc 0) (s₀.loc 1) (s₀.loc 6) (s₀.loc 7 + s₀.loc 8)
        (s₀.loc 8 * 2) ≠ [] ∧
      (mslotG (s'.mem.arr64 S.arr) (s₀.loc 0) (s₀.loc 1) (s₀.loc 6) (s₀.loc 7 + s₀.loc 8)
        (s₀.loc 8 * 2)).headD 0 = 0 ∧
      s'.loc 4 = (mslotG (s'.mem.arr64 S.arr) (s₀.loc 0) (s₀.loc 1) (s₀.loc 6)
        (s₀.loc 7 + s₀.loc 8) (s₀.loc 8 * 2)).tail.headD 0; ⊤⦄ := by
  simp only [mgrowBlkG]
  sym only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalC, evalArgs, setLoc, st64, mrehashLoopG_step_spec S p,
      mslotBlkG_step_spec S p] <;>
    finish [mgrowAt]

theorem memoPutG_spec (S : MemoSch) (p : Prog) (f : FnName) (hp : p.lookup f = some (memoPutG S))
    (n : Nat) (s₀ : St) (k1 k2 v fd j : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) f [k1, k2, v, fd, j]
    ⦃fun _ s' => LocEq s' s₀ ∧ mputG S s₀.mem k1 k2 v fd j = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, memoPutG]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        mgrowBlkG_step_spec S p n] <;>
      finish [mputG, mputMem, mputMemE, nG, mbG, hdG, epG, cntG, dfltN_alt]

/-! ## `X_clear()` -/

/-- The memory after `X_clear()`. -/
def mclearG (S : MemoSch) (m : Mem) : Mem :=
  (m.set64 CTL S.cs (rdW (m.arr64 CTL) S.cs + 1)).set64 CTL (S.cs + 1) 0

/-- con-ron: none — the memo library (open addressing over fixed arrays; the twin's `Std.HashMap` caches) -/
@[no_expose] def memoClearG (S : MemoSch) : FunDecl := lfn () locals () {
  if CTL.u64[⟪S.cs⟫] + 2 == 0 { abort };
  CTL.u64[⟪S.cs⟫] := CTL.u64[⟪S.cs⟫] + 1;
  CTL.u64[⟪S.cs + 1⟫] := 0;
  return 0
}

theorem memoClearG_spec (S : MemoSch) (p : Prog) (f : FnName)
    (hp : p.lookup f = some (memoClearG S)) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) f []
    ⦃fun _ s' => LocEq s' s₀ ∧ rdW (s₀.mem.arr64 CTL) S.cs + 2 ≠ 0 ∧
      s'.mem = mclearG S s₀.mem; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, memoClearG]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64, st64] <;>
      finish [mclearG]

/-! ## `X_clear()` with a capacity policy (`X_clear_fit`)

con-ron's `HashMap2::clear_fit` (`ron/hashmap2.rs`): the clear also sizes the next round's table
to twice a **decaying high-water mark** `hw` of the entries, `hw := max(entries, hw - hw / 8)`,
rounded up to a power of two (`pow2_at_least(2 hw + 1, MIN_CAPACITY)`), and re-makes the table
when that size is above the current one or more than 64 times below it. Here the mark is the
header's word 3 (the header slot's value word, which no region covers), and "re-made" is a new
header: the stamp of the new epoch, region from slot `1` of the chosen size (at most the slots the
array has after the header). The floor is the default region's `MN0` slots (the twin's
`MIN_CAPACITY` is 32, a size L's measurements do not favour), so a mark of at most `FITLO`
(`2 hw + 1 ≤ MN0`) sizes the default region, and the clear leaves the header stale (the epoch bump
alone, as `X_clear`) and the mark `0`. -/

/-- The largest mark whose next round fits the default region: `2 · FITLO + 1 = MN0 - 1`. -/
def FITLO : Word := 8191

/-- The decayed mark at a clear, from the stored mark `h` and the count `c`:
`max(c, h - h / 8)`. -/
def mfitHW (h c : Word) : Word := if h - (h >>> 3) < c then c else h - (h >>> 3)

/-- `pow2_at_least(x, w)`: double `w` until it reaches `x` (or `2^62`). -/
def mpow2 (x w : Word) : Word :=
  if w < x ∧ w < 4611686018427387904 ∧ 0 < w then mpow2 x (w + w) else w
termination_by 4611686018427387904 - w.toNat
decreasing_by
  obtain ⟨-, h1, h2⟩ := ‹w < x ∧ w < 4611686018427387904 ∧ 0 < w›
  have a := UInt64.lt_iff_toNat_lt.mp h1
  have b := UInt64.lt_iff_toNat_lt.mp h2
  have : (w + w).toNat = w.toNat + w.toNat := by
    rw [UInt64.toNat_add]; simp at a ⊢; omega
  simp at a b; omega

/-- The slots after the header: the cap of a re-made region. -/
def mfitL (S : MemoSch) (m : Mem) : Word :=
  (m.len64 S.arr >>> 2) - (if (0 : Word) < m.len64 S.arr >>> 2 then 1 else 0)

/-- The current slot count at stamp `e` (`nG` at the stamp before the clear). -/
def mfitCur (S : MemoSch) (m : Mem) (e : Word) : Word :=
  if rdW (m.arr64 S.arr) 0 = e then rdW (m.arr64 S.arr) 2
  else if MN0 < mfitL S m then MN0 else mfitL S m

/-- The twin's policy: keep the size `n` unless the wanted `w` is above it or more than 64 times
below it. -/
def mfitPol (n w : Word) : Word := if n < w ∨ w < n >>> 6 then w else n

/-- The next round's slot count at mark `h`, current stamp `e`: the policy at
`mpow2 (2 h + 1) MN0`, capped at `mfitL`. -/
def mfitNE (S : MemoSch) (m : Mem) (e h : Word) : Word :=
  if mfitL S m < mfitPol (mfitCur S m e) (mpow2 (h + h + 1) MN0) then mfitL S m
  else mfitPol (mfitCur S m e) (mpow2 (h + h + 1) MN0)

/-- The re-made header, at the old stamp word `s` (new live stamp `s + 2`) and mark `h`. -/
def mfitHdr (S : MemoSch) (m : Mem) (s h : Word) : Mem :=
  (((m.set64 S.arr 0 (s + 2)).set64 S.arr 1 1).set64 S.arr 2 (mfitNE S m (s + 1) h)).set64 S.arr 3 h

/-- The mark and the header after the epoch bump, from the old stamp word `s` and the count `c`
before the clear. -/
def mfitTail (S : MemoSch) (m : Mem) (s c : Word) : Mem :=
  if rdW (m.arr64 S.arr) 3 = 0 ∧ c ≤ FITLO then m
  else if mfitHW (rdW (m.arr64 S.arr) 3) c ≤ FITLO then m.set64 S.arr 3 0
  else mfitHdr S m s (mfitHW (rdW (m.arr64 S.arr) 3) c)

/-- The memory after `X_clear_fit()`: the epoch bump, then the mark and the header. -/
def mclearFitG (S : MemoSch) (m : Mem) : Mem :=
  mfitTail S (mclearG S m) (rdW (m.arr64 CTL) S.cs) (cntG S m)

/-- The doubling loop (variables of `memoClearFitG`: mark `h` 2, size `w` 4). -/
def mfitLoopG : Stmt := lblk (s, c, h, n, w, l) {
  while w < h + h + 1 && w < 4611686018427387904 { w := w + w }
}

/-- The re-make (variables of `memoClearFitG`): the cap `l`, the current size `n`, the doubling,
the policy, and the new header. -/
def mfitBlkG (S : MemoSch) : Stmt := lblk (s, c, h, n, w, l) {
  l := len(S.arr.u64) >> 2;
  l := l - u64(l > 0);
  if S.arr.u64[0] == s + 1 { n := S.arr.u64[2] } else {
    n := l;
    if n > ⟪MN0⟫ { n := ⟪MN0⟫ }
  };
  w := ⟪MN0⟫;
  ⟪mfitLoopG⟫;
  if n < w || (n >> 6) > w { n := w };
  if n > l { n := l };
  S.arr.u64[0] := s + 2;
  S.arr.u64[1] := 1;
  S.arr.u64[2] := n;
  S.arr.u64[3] := h
}

/-- The mark and the re-make (variables of `memoClearFitG`: old stamp word `s`, count `c`). -/
def mfitTailG (S : MemoSch) : Stmt := lblk (s, c, h, n, w, l) {
  h := S.arr.u64[3];
  if h != 0 || c > ⟪FITLO⟫ {
    h := h - (h >> 3);
    if c > h { h := c };
    if h > ⟪FITLO⟫ { ⟪mfitBlkG S⟫ } else { S.arr.u64[3] := 0 }
  }
}

/-- con-ron: none — the memo library (open addressing over fixed arrays; the twin's `Std.HashMap` caches) -/
@[no_expose] def memoClearFitG (S : MemoSch) : FunDecl := lfn () locals (s, c, h, n, w, l) {
  s := CTL.u64[⟪S.cs⟫];
  if s + 2 == 0 { abort };
  c := CTL.u64[⟪S.cs + 1⟫];
  CTL.u64[⟪S.cs⟫] := s + 1;
  CTL.u64[⟪S.cs + 1⟫] := 0;
  ⟪mfitTailG S⟫;
  return 0
}

section clearFit
variable (S : MemoSch) (p : Prog)

theorem mpow2_step (x w : Word) (h : w < x ∧ w < 4611686018427387904) :
    mpow2 x w = mpow2 x (w + w) := by
  by_cases h0 : 0 < w
  · rw [mpow2]; simp only [h.1, h.2, h0, and_self, ↓reduceIte]
  · have : w = 0 := by
      apply UInt64.toNat_inj.mp; have := mt UInt64.lt_iff_toNat_lt.mpr h0; simp at this ⊢; omega
    subst this; rfl

theorem mpow2_end (x w : Word) (h : ¬ (w < x ∧ w < 4611686018427387904)) : mpow2 x w = w := by
  rw [mpow2]; split
  · rename_i h'; exact absurd ⟨h'.1, h'.2.1⟩ h
  · rfl

theorem mfitLoopG_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n mfitLoopG
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧ (∀ z, z ≠ 4 → s'.loc z = s₀.loc z) ∧
      s'.loc 4 = mpow2 (s₀.loc 2 + s₀.loc 2 + 1) (s₀.loc 4); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := mfitLoopG) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih] <;> finish [mpow2_step, mpow2_end]

theorem mfitLoopG_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) mfitLoopG
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧ (∀ z, z ≠ 4 → s'.loc z = s₀.loc z) ∧
      s'.loc 4 = mpow2 (s₀.loc 2 + s₀.loc 2 + 1) (s₀.loc 4); ⊤⦄ :=
  Triple.step_exec (mfitLoopG_spec p (n + 1) s₀)

theorem mfitBlkG_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mfitBlkG S)
    ⦃fun r s' => r = .normal ∧ s'.mem = mfitHdr S s₀.mem (s₀.loc 0) (s₀.loc 2); ⊤⦄ := by
  simp only [mfitBlkG]
  sym only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalC, evalArgs, setLoc, ld64, st64, mfitLoopG_step_spec p] <;>
    finish [mfitHdr, mfitNE, mfitPol, mfitCur, mfitL]

theorem mfitTailG_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mfitTailG S)
    ⦃fun r s' => r = .normal ∧ s'.mem = mfitTail S s₀.mem (s₀.loc 0) (s₀.loc 1); ⊤⦄ := by
  simp only [mfitTailG]
  sym only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalC, evalArgs, setLoc, ld64, st64, mfitBlkG_step_spec S p] <;>
    finish [mfitTail, mfitHW]

theorem memoClearFitG_spec (f : FnName) (hp : p.lookup f = some (memoClearFitG S)) (n : Nat)
    (s₀ : St) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) f []
    ⦃fun _ s' => LocEq s' s₀ ∧ rdW (s₀.mem.arr64 CTL) S.cs + 2 ≠ 0 ∧
      s'.mem = mclearFitG S s₀.mem; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, memoClearFitG]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64, st64, mfitTailG_step_spec S p n] <;>
      finish [mclearFitG, mclearG, cntG]

/-- **The fast path**: with no stored mark and a round within the floor's mark, `clear_fit` is
the epoch bump. A caller tests this and calls `X_clear` (a leaf, inlined), and `X_clear_fit`
only otherwise. -/
theorem mclearFitG_fast (m : Mem) (ha : (S.arr : TieredArray) ≠ CTL)
    (h3 : rdW (m.arr64 S.arr) 3 = 0) (hc : cntG S m ≤ FITLO) : mclearFitG S m = mclearG S m := by
  have : (mclearG S m).arr64 S.arr = m.arr64 S.arr := by
    simp only [mclearG]; rw [Mem.arr64_set64_ne _ _ _ _ _ ha, Mem.arr64_set64_ne _ _ _ _ _ ha]
  simp [mclearFitG, mfitTail, this, h3, hc]

end clearFit

/-- `set` is `put` after a probe that returned. -/
theorem msetG_eq (S : MemoSch) (m : Mem) (k1 k2 v : Word) (h : mfindG S m k1 k2 ≠ []) :
    msetG S m k1 k2 v =
      mputG S m k1 k2 v ((mfindG S m k1 k2).headD 0) ((mfindG S m k1 k2).tail.headD 0) := by
  simp [msetG, h]

grind_pattern [arena_grind] msetG_eq => msetG S m k1 k2 v

/-! ## `X_erase(j)`: a tombstone

Deletion in an open-addressing table must not break the runs of the keys behind the deleted one.
`X_erase(j)` overwrites the first key word of the live slot `j` (found by a probe) with `TOMB`: the
slot stays live, so probes run past it, and no valid key has first word `TOMB` (`MemoKey.ok_tomb`),
so it never matches. Tombstones are not reused; they go at the next `clear`. -/

/-! ## Banks: generations in the key

con-ron's `takeModeMemos`/`putModeMemos` run an eager comparison on emptied mode tables and put
the caller's back afterwards. A memo with **generation-tagged keys** does this without copying:
the key's second word carries a generation `g` in its high half (`genKey`), the current
generation is `CTL[c + 1]`, the last allocated one `CTL[c]`. `X_bank_enter()` allocates a fresh
generation (aborting at `2^32`), makes it current and returns the caller's; `X_bank_leave(s)`
makes `s` current again. A fresh generation has no entries (the empty bank), and the caller's
entries are untouched (its bank, put back). Entries of finished generations stay until the
memo's `clear`. -/

/-- The memory after `X_bank_enter()`: counter and current generation `CTL[c] + 1`. -/
def benterG (c : Word) (m : Mem) : Mem :=
  (m.set64 CTL c (rdW (m.arr64 CTL) c + 1)).set64 CTL (c + 1) (rdW (m.arr64 CTL) c + 1)

/-- con-ron: none — the memo library (open addressing over fixed arrays; the twin's `Std.HashMap` caches) -/
@[no_expose] def bankEnterG (c : Word) : FunDecl := lfn () locals (s, g) {
  s := CTL.u64[⟪c + 1⟫];
  g := CTL.u64[⟪c⟫] + 1;
  if g >= 4294967296 { abort };
  CTL.u64[⟪c⟫] := g;
  CTL.u64[⟪c + 1⟫] := g;
  return s
}

/-- con-ron: none — the memo library (open addressing over fixed arrays; the twin's `Std.HashMap` caches) -/
@[no_expose] def bankLeaveG (c : Word) : FunDecl := lfn (s) locals () {
  CTL.u64[⟪c + 1⟫] := s;
  return 0
}

theorem bankEnterG_spec (c : Word) (p : Prog) (f : FnName) (hp : p.lookup f = some (bankEnterG c))
    (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) f []
    ⦃fun r s' => LocEq s' s₀ ∧ r = [rdW (s₀.mem.arr64 CTL) (c + 1)] ∧
      (rdW (s₀.mem.arr64 CTL) c + 1).toNat < 2 ^ 32 ∧ s'.mem = benterG c s₀.mem; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, bankEnterG]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64, st64] <;> finish [benterG]

theorem bankLeaveG_spec (c : Word) (p : Prog) (f : FnName) (hp : p.lookup f = some (bankLeaveG c))
    (n : Nat) (s₀ : St) (s : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) f [s]
    ⦃fun _ s' => LocEq s' s₀ ∧ s'.mem = s₀.mem.set64 CTL (c + 1) s; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, bankLeaveG]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, st64] <;> finish

/-! ## The instances -/

/-- `bvarBC`: array 24, stamp `CTL[24]`, count `CTL[25]`. -/
abbrev bmSch : MemoSch := ⟨BMEMO, 24⟩

/-- `liftC`: array 41, stamp `CTL[42]`, count `CTL[43]`. -/
abbrev lfSch : MemoSch := ⟨LMEMO, 42⟩

/-- `inst1C`: array 47, stamp `CTL[44]`, count `CTL[45]`. -/
abbrev imSch : MemoSch := ⟨IMEMO, 44⟩

/-- `fvarBC`: array 48, stamp `CTL[46]`, count `CTL[47]`. -/
abbrev frSch : MemoSch := ⟨FRMEMO, 46⟩

end L.Arena
