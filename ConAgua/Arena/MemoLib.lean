module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
public import ConAgua.Arena.SlotGrow
public import ConAgua.L.Logic
public import ConAgua.L.Notation
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Data.DTreeMap.Internal.Operations
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

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

* `X_find(k1, k2)`: the probe from `homeW (k1 ^ (k2 << 32) ^ (k2 >> 32) * golden)`, returning
  `(found, slot, steps)`. Both halves of `k2` enter the hash: banked memos (`MemoBank.genW`), the
  eager bit and `rrSch` keep a second component in `k2`'s high half (lane `rfhash`: with only
  `k2 << 32` it was shifted out, and all banks' entries for one `k1` shared one probe cluster).
* `X_put(k1, k2, v, fd, j)`: given the probe's `fd`, `j` **on the current memory**, write the
  value (and on a miss, the stamp and the key, growing the table past 3/4 load, con-ron's `HashMap2` load factor). Callers probe right
  before (`set` = `find; put`); a walk that recursed since its first probe probes again.
* `X_clear()`: `CTL[cs] += 1`, `CTL[cs + 1] := 0`, aborting where the stamp would wrap.
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

/-- The hash input of a two-word key. -/
def kh (k1 k2 : Word) : Word := (k1 ^^^ (k2 <<< 32)) ^^^ ((k2 >>> 32) * golden)

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
  while d < n {
    if S.arr.u64[(b + j) * 4] != e { return (0, b + j, d) };
    if S.arr.u64[(b + j) * 4 + 1] == k1 && S.arr.u64[(b + j) * 4 + 2] == k2 { return (1, b + j, d) };
    j := (j + 1) * u64(j + 1 < n);
    d += 1
  }
}

/-- con-ron: none — the memo library (open addressing over fixed arrays; the twin's `Std.HashMap` caches) -/
def memoFindG (S : MemoSch) : FunDecl := lfn (k1, k2) locals (n, e, j, d, b) {
  e := CTL.u64[⟪S.cs⟫] + 1;
  if S.arr.u64[0] == e {
    b := S.arr.u64[1];
    n := S.arr.u64[2]
  } else {
    b := 1;
    n := len(S.arr.u64) >> 2;
    n := n - u64(n > 0);
    if n > ⟪MN0⟫ { n := ⟪MN0⟫ }
  };
  j := (k1 ^ (k2 << 32)) ^ ((k2 >> 32) * ⟪golden⟫);
  j := mulhi((j * ⟪golden⟫) ^ ((j * ⟪golden⟫) >> 32), n);
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
  mprobeG (m.arr64 S.arr) k1 k2 (epG S m) (mbG S m) (nG S m) (homeW (kh k1 k2) (nG S m)) 0

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
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64, mfindLoopG_step_spec S p n] <;>
      finish [mfindG, nG, mbG, hdG, epG, dfltN, homeW, kh]

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
  mprobeG mm x y e b n (homeW (kh x y) n) 0

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

/-- The free-slot probe loop of the growth (variables of `memoPutG`): key `(x, y)` (12, 13),
region `nb`, `nn` (9, 10), stamp `e` (6), slot `q` (14), step `d` (15). A live slot with the key
aborts. -/
def mslotLoopG (S : MemoSch) : Stmt :=
  lblk (k1, k2, v, fd, j, c, e, b, n, nb, nn, i, x, y, q, d, w) {
  while d < nn && S.arr.u64[(nb + q) * 4] == e {
    if S.arr.u64[(nb + q) * 4 + 1] == x && S.arr.u64[(nb + q) * 4 + 2] == y { abort };
    q := (q + 1) * u64(q + 1 < nn);
    d += 1
  }
}

/-- A free slot for key `(x, y)` in the region `nb`, `nn`, into `q`; aborts if there is none. -/
def mslotBlkG (S : MemoSch) : Stmt :=
  lblk (k1, k2, v, fd, j, c, e, b, n, nb, nn, i, x, y, q, d, w) {
  q := (x ^ (y << 32)) ^ ((y >> 32) * ⟪golden⟫);
  q := mulhi((q * ⟪golden⟫) ^ ((q * ⟪golden⟫) >> 32), nn);
  d := 0;
  ⟪mslotLoopG S⟫;
  if d >= nn { abort };
  q := nb + q
}

/-- Move the live slot `i` to a free slot of the region `nb`, `nn`; count it in `c`. -/
def mmoveG (S : MemoSch) : Stmt :=
  lblk (k1, k2, v, fd, j, c, e, b, n, nb, nn, i, x, y, q, d, w) {
  x := S.arr.u64[i * 4 + 1];
  y := S.arr.u64[i * 4 + 2];
  w := S.arr.u64[i * 4 + 3];
  ⟪mslotBlkG S⟫;
  S.arr.u64[q * 4] := e;
  S.arr.u64[q * 4 + 1] := x;
  S.arr.u64[q * 4 + 2] := y;
  S.arr.u64[q * 4 + 3] := w;
  c += 1
}

/-- One step of the rehash loop: move slot `i` if it is live and not a tombstone. -/
def mstepG (S : MemoSch) : Stmt :=
  lblk (k1, k2, v, fd, j, c, e, b, n, nb, nn, i, x, y, q, d, w) {
  if S.arr.u64[i * 4] == e && S.arr.u64[i * 4 + 1] != ⟪TOMB⟫ { ⟪mmoveG S⟫ };
  i += 1
}

/-- The rehash loop: every live slot `i` of the region `[b, nb)` that is not a tombstone moves to a
free slot of the region `nb`, `nn`; `c` counts them. -/
def mrehashLoopG (S : MemoSch) : Stmt :=
  lblk (k1, k2, v, fd, j, c, e, b, n, nb, nn, i, x, y, q, d, w) {
  while i < nb { ⟪mstepG S⟫ }
}

/-- The growth (variables of `memoPutG`): rehash the region `b`, `n` into `b + n`, `2 n`, name it
in the header, set the count, and find the free slot `j` for the key `(k1, k2)` there. -/
def mgrowBlkG (S : MemoSch) : Stmt :=
  lblk (k1, k2, v, fd, j, c, e, b, n, nb, nn, i, x, y, q, d, w) {
  nb := b + n;
  nn := n * 2;
  if nn == 0 { abort };
  if (len(S.arr.u64) >> 2) < nb + nn { abort };
  c := 0;
  i := b;
  ⟪mrehashLoopG S⟫;
  S.arr.u64[0] := e;
  S.arr.u64[1] := nb;
  S.arr.u64[2] := nn;
  CTL.u64[⟪S.cs + 1⟫] := c;
  x := k1;
  y := k2;
  ⟪mslotBlkG S⟫;
  j := q
}

/-- con-ron: none — the memo library (open addressing over fixed arrays; the twin's `Std.HashMap` caches) -/
def memoPutG (S : MemoSch) : FunDecl :=
  lfn (k1, k2, v, fd, j) locals (c, e, b, n, nb, nn, i, x, y, q, d, w) {
  if fd == 0 {
    c := CTL.u64[⟪S.cs + 1⟫];
    e := CTL.u64[⟪S.cs⟫] + 1;
    if S.arr.u64[0] == e {
      b := S.arr.u64[1];
      n := S.arr.u64[2]
    } else {
      b := 1;
      n := len(S.arr.u64) >> 2;
      n := n - u64(n > 0);
      if n > ⟪MN0⟫ { n := ⟪MN0⟫ }
    };
    if n * 3 < (c + 1) * 4 { ⟪mgrowBlkG S⟫ };
    S.arr.u64[j * 4] := e;
    S.arr.u64[j * 4 + 1] := k1;
    S.arr.u64[j * 4 + 2] := k2;
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
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧ (∀ z, z ≠ 14 → z ≠ 15 → s'.loc z = s₀.loc z) ∧
      mprobeG (s₀.mem.arr64 S.arr) (s₀.loc 12) (s₀.loc 13) (s₀.loc 6) (s₀.loc 9) (s₀.loc 10)
        (s₀.loc 14) (s₀.loc 15) =
      if s'.loc 15 < s₀.loc 10 then [0, s₀.loc 9 + s'.loc 14, s'.loc 15] else []; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := mslotLoopG S) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;> finish [mprobeG_end]

theorem mslotLoopG_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mslotLoopG S)
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧ (∀ z, z ≠ 14 → z ≠ 15 → s'.loc z = s₀.loc z) ∧
      mprobeG (s₀.mem.arr64 S.arr) (s₀.loc 12) (s₀.loc 13) (s₀.loc 6) (s₀.loc 9) (s₀.loc 10)
        (s₀.loc 14) (s₀.loc 15) =
      if s'.loc 15 < s₀.loc 10 then [0, s₀.loc 9 + s'.loc 14, s'.loc 15] else []; ⊤⦄ :=
  Triple.step_exec (mslotLoopG_spec S p (n + 1) s₀)

theorem mslotBlkG_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mslotBlkG S)
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧ (∀ z, z ≠ 14 → z ≠ 15 → s'.loc z = s₀.loc z) ∧
      mslotG (s₀.mem.arr64 S.arr) (s₀.loc 12) (s₀.loc 13) (s₀.loc 6) (s₀.loc 9) (s₀.loc 10) ≠ [] ∧
      (mslotG (s₀.mem.arr64 S.arr) (s₀.loc 12) (s₀.loc 13) (s₀.loc 6) (s₀.loc 9)
        (s₀.loc 10)).headD 0 = 0 ∧
      s'.loc 14 = (mslotG (s₀.mem.arr64 S.arr) (s₀.loc 12) (s₀.loc 13) (s₀.loc 6) (s₀.loc 9)
        (s₀.loc 10)).tail.headD 0; ⊤⦄ := by
  simp only [mslotBlkG]
  sym only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalC, evalArgs, setLoc, mslotLoopG_step_spec S p] <;>
    finish [mslotG, homeW, kh]

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
    ⦃fun r s' => r = .normal ∧ (∀ z, z ≠ 5 → z < 12 → s'.loc z = s₀.loc z) ∧ s'.loc 5 = s₀.loc 5 + 1 ∧
      mslotG (s₀.mem.arr64 S.arr) (rdW (s₀.mem.arr64 S.arr) (s₀.loc 11 * 4 + 1))
        (rdW (s₀.mem.arr64 S.arr) (s₀.loc 11 * 4 + 2)) (s₀.loc 6) (s₀.loc 9) (s₀.loc 10) ≠ [] ∧
      (mslotG (s₀.mem.arr64 S.arr) (rdW (s₀.mem.arr64 S.arr) (s₀.loc 11 * 4 + 1))
        (rdW (s₀.mem.arr64 S.arr) (s₀.loc 11 * 4 + 2)) (s₀.loc 6) (s₀.loc 9)
        (s₀.loc 10)).headD 0 = 0 ∧
      s'.mem = mput4 S s₀.mem ((mslotG (s₀.mem.arr64 S.arr) (rdW (s₀.mem.arr64 S.arr) (s₀.loc 11 * 4 + 1))
        (rdW (s₀.mem.arr64 S.arr) (s₀.loc 11 * 4 + 2)) (s₀.loc 6) (s₀.loc 9)
        (s₀.loc 10)).tail.headD 0) (s₀.loc 6)
        (rdW (s₀.mem.arr64 S.arr) (s₀.loc 11 * 4 + 1)) (rdW (s₀.mem.arr64 S.arr) (s₀.loc 11 * 4 + 2))
        (rdW (s₀.mem.arr64 S.arr) (s₀.loc 11 * 4 + 3)); ⊤⦄ := by
  simp only [mmoveG]
  sym only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalC, evalArgs, setLoc, ld64, st64, mslotBlkG_step_spec S p] <;>
    finish [mput4]

theorem mstepG_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) (mstepG S)
    ⦃fun r s' => r = .normal ∧ (∀ z, z ≠ 5 → z < 11 → s'.loc z = s₀.loc z) ∧
      s'.loc 11 = s₀.loc 11 + 1 ∧
      (s₀.loc 11 < s₀.loc 9 →
        mrehashG S (s₀.loc 6) (s₀.loc 9) (s₀.loc 10) (s₀.loc 11) (s₀.loc 5) s₀.mem =
          mrehashG S (s₀.loc 6) (s₀.loc 9) (s₀.loc 10) (s'.loc 11) (s'.loc 5) s'.mem); ⊤⦄ := by
  simp only [mstepG]
  sym only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalC, evalArgs, setLoc, ld64, mmoveG_step_spec S p] <;>
    finish [mrehashG_skip, mrehashG_move]

theorem mrehashLoopG_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n (mrehashLoopG S)
    ⦃fun r s' => r = .normal ∧ (∀ z, z ≠ 5 → z < 11 → s'.loc z = s₀.loc z) ∧
      mrehashG S (s₀.loc 6) (s₀.loc 9) (s₀.loc 10) (s₀.loc 11) (s₀.loc 5) s₀.mem =
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
    ⦃fun r s' => r = .normal ∧ (∀ z, z ≠ 5 → z < 11 → s'.loc z = s₀.loc z) ∧
      mrehashG S (s₀.loc 6) (s₀.loc 9) (s₀.loc 10) (s₀.loc 11) (s₀.loc 5) s₀.mem =
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
      finish [mputG, mputMem, mputMemE, nG, mbG, hdG, epG, cntG, dfltN]

/-! ## `X_clear()` -/

/-- The memory after `X_clear()`. -/
def mclearG (S : MemoSch) (m : Mem) : Mem :=
  (m.set64 CTL S.cs (rdW (m.arr64 CTL) S.cs + 1)).set64 CTL (S.cs + 1) 0

/-- con-ron: none — the memo library (open addressing over fixed arrays; the twin's `Std.HashMap` caches) -/
def memoClearG (S : MemoSch) : FunDecl := lfn () locals () {
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
def bankEnterG (c : Word) : FunDecl := lfn () locals (s, g) {
  s := CTL.u64[⟪c + 1⟫];
  g := CTL.u64[⟪c⟫] + 1;
  if g >= 4294967296 { abort };
  CTL.u64[⟪c⟫] := g;
  CTL.u64[⟪c + 1⟫] := g;
  return s
}

/-- con-ron: none — the memo library (open addressing over fixed arrays; the twin's `Std.HashMap` caches) -/
def bankLeaveG (c : Word) : FunDecl := lfn (s) locals () {
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
