module

public import ConAgua.Arena.Store
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store

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

* `X_find(k1, k2)`: the probe from `homeW (k1 ^ (k2 << 32))`, returning `(found, slot, steps)`.
* `X_put(k1, k2, v, fd, j)`: given the probe's `fd`, `j` **on the current memory**, write the
  value (and on a miss, the stamp and the key, aborting past a 3/4 load). Callers probe right
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

/-- The slot count. -/
def nG (S : MemoSch) (m : Mem) : Word := m.len64 S.arr >>> 2

/-- The live count, `CTL[cs + 1]` (only the load limit reads it). -/
def cntG (S : MemoSch) (m : Mem) : Word := rdW (m.arr64 CTL) (S.cs + 1)

/-- The hash input of a two-word key. -/
def kh (k1 k2 : Word) : Word := k1 ^^^ (k2 <<< 32)

/-! ## `X_find(k1, k2)`: the probe -/

/-- The model of the probe loop, from slot `j` after `d` steps, live stamp `e`. -/
def mprobeG (mm : Array Word) (k1 k2 e n j d : Word) : List Word :=
  if d < n then
    if rdW mm (j * 4) ≠ e then [0, j, d]
    else if rdW mm (j * 4 + 1) = k1 ∧ rdW mm (j * 4 + 2) = k2 then [1, j, d]
    else mprobeG mm k1 k2 e n ((j + 1) * (if j + 1 < n then 1 else 0)) (d + 1)
  else []
termination_by n.toNat - d.toNat
decreasing_by
  have : d.toNat < n.toNat := by simpa [UInt64.lt_iff_toNat_lt] using ‹d < n›
  have := n.toNat_lt
  have : (d + 1).toNat = d.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  omega

section probeArms
variable (mm : Array Word) (k1 k2 e n j d : Word)

theorem mprobeG_free (a : Nat) (hd : d < n) (ha : a = (j * 4).toNat) (has : a < mm.size)
    (hv : mm[a] ≠ e) : mprobeG mm k1 k2 e n j d = [0, j, d] := by
  rw [mprobeG]; simp only [hd, ↓reduceIte, rdW_eq mm _ a ha has, hv, ne_eq, not_false_eq_true]

theorem mprobeG_hit (a b c : Nat) (hd : d < n) (ha : a = (j * 4).toNat) (has : a < mm.size)
    (hb : b = (j * 4 + 1).toNat) (hbs : b < mm.size) (hc : c = (j * 4 + 2).toNat)
    (hcs : c < mm.size) (hv : mm[a] = e) (hk : mm[b] = k1) (hk2 : mm[c] = k2) :
    mprobeG mm k1 k2 e n j d = [1, j, d] := by
  rw [mprobeG]; simp only [hd, ↓reduceIte, rdW_eq mm _ a ha has, rdW_eq mm _ b hb hbs,
    rdW_eq mm _ c hc hcs, hv, hk, hk2, ne_eq, not_true_eq_false, and_self]

theorem mprobeG_next1 (a b : Nat) (j' d' : Word) (hd : d < n) (ha : a = (j * 4).toNat)
    (has : a < mm.size) (hb : b = (j * 4 + 1).toNat) (hbs : b < mm.size) (hv : mm[a] = e)
    (hk : mm[b] ≠ k1) (hj' : j' = (j + 1) * (if j + 1 < n then 1 else 0)) (hd' : d' = d + 1) :
    mprobeG mm k1 k2 e n j d = mprobeG mm k1 k2 e n j' d' := by
  subst hj' hd'
  rw [mprobeG]; simp only [hd, ↓reduceIte, rdW_eq mm _ a ha has, rdW_eq mm _ b hb hbs, hv, hk,
    ne_eq, not_true_eq_false, false_and]

theorem mprobeG_next2 (a b c : Nat) (j' d' : Word) (hd : d < n) (ha : a = (j * 4).toNat)
    (has : a < mm.size) (hb : b = (j * 4 + 1).toNat) (hbs : b < mm.size)
    (hc : c = (j * 4 + 2).toNat) (hcs : c < mm.size) (hv : mm[a] = e)
    (hk : mm[b] = k1) (hk2 : mm[c] ≠ k2) (hj' : j' = (j + 1) * (if j + 1 < n then 1 else 0))
    (hd' : d' = d + 1) :
    mprobeG mm k1 k2 e n j d = mprobeG mm k1 k2 e n j' d' := by
  subst hj' hd'
  rw [mprobeG]; simp only [hd, ↓reduceIte, rdW_eq mm _ a ha has, rdW_eq mm _ b hb hbs,
    rdW_eq mm _ c hc hcs, hv, hk, hk2, ne_eq, not_true_eq_false, true_and]

end probeArms

grind_pattern [arena_grind] mprobeG_free => mprobeG mm k1 k2 e n j d, mm[a]
grind_pattern [arena_grind] mprobeG_hit => mprobeG mm k1 k2 e n j d, mm[a], mm[b], mm[c]
grind_pattern [arena_grind] mprobeG_next1 =>
  mprobeG mm k1 k2 e n j d, mm[a], mm[b], mprobeG mm k1 k2 e n j' d'
grind_pattern [arena_grind] mprobeG_next2 =>
  mprobeG mm k1 k2 e n j d, mm[a], mm[b], mm[c], mprobeG mm k1 k2 e n j' d'

def mfindLoopG (S : MemoSch) : Stmt := lblk (k1, k2, n, e, j, d) {
  while d < n {
    if S.arr.u64[j * 4] != e { return (0, j, d) };
    if S.arr.u64[j * 4 + 1] == k1 && S.arr.u64[j * 4 + 2] == k2 { return (1, j, d) };
    j := (j + 1) * u64(j + 1 < n);
    d += 1
  }
}

/-- con-ron: none — the memo library (open addressing over fixed arrays; the twin's `Std.HashMap` caches) -/
def memoFindG (S : MemoSch) : FunDecl := lfn (k1, k2) locals (n, e, j, d) {
  n := len(S.arr.u64) >> 2;
  e := CTL.u64[⟪S.cs⟫] + 1;
  j := k1 ^ (k2 << 32);
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
      r.retOr (mprobeG (s₀.mem.arr64 S.arr) (s₀.loc 0) (s₀.loc 1) (s₀.loc 3) (s₀.loc 2)
        (s₀.loc 4) (s₀.loc 5)) =
      mprobeG (s₀.mem.arr64 S.arr) (s₀.loc 0) (s₀.loc 1) (s₀.loc 3) (s₀.loc 2) (s₀.loc 4)
        (s₀.loc 5); ⊤⦄ := by
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
      r.retOr (mprobeG (s₀.mem.arr64 S.arr) (s₀.loc 0) (s₀.loc 1) (s₀.loc 3) (s₀.loc 2)
        (s₀.loc 4) (s₀.loc 5)) =
      mprobeG (s₀.mem.arr64 S.arr) (s₀.loc 0) (s₀.loc 1) (s₀.loc 3) (s₀.loc 2) (s₀.loc 4)
        (s₀.loc 5); ⊤⦄ :=
  Triple.step_exec (mfindLoopG_spec S p (n + 1) s₀)

/-- The probe of the memo for key `(k1, k2)`. -/
def mfindG (m : Mem) (k1 k2 : Word) : List Word :=
  mprobeG (m.arr64 S.arr) k1 k2 (epG S m) (nG S m) (homeW (kh k1 k2) (nG S m)) 0

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
      vcgen [exec, step, evalE, evalArgs, setLoc, ld64, mfindLoopG_step_spec S p n] <;>
      finish [mfindG, nG, epG, homeW, kh]

end find

/-! ## `X_put(k1, k2, v, fd, j)` -/

/-- The memory after `X_put` at slot `j` (`fd ≠ 0`: the key is there). -/
def mputMem (S : MemoSch) (m : Mem) (fd j k1 k2 v : Word) : Mem :=
  if fd = 0 then
    ((((m.set64 S.arr (j * 4) (epG S m)).set64 S.arr (j * 4 + 1) k1).set64 S.arr (j * 4 + 2)
      k2).set64 CTL (S.cs + 1) (cntG S m + 1)).set64 S.arr (j * 4 + 3) v
  else m.set64 S.arr (j * 4 + 3) v

/-- The model of `X_put`: the memory after, `none` where the L code aborts. -/
def mputG (S : MemoSch) (m : Mem) (k1 k2 v fd j : Word) : Option Mem :=
  if fd = 0 ∧ (nG S m >>> 2) * 3 < cntG S m + 1 then none
  else some (mputMem S m fd j k1 k2 v)

/-- `set` = `find; put`: the model of a probe followed by a put on the same memory. -/
def msetG (S : MemoSch) (m : Mem) (k1 k2 v : Word) : Option Mem :=
  if mfindG S m k1 k2 = [] then none
  else mputG S m k1 k2 v ((mfindG S m k1 k2).headD 0) ((mfindG S m k1 k2).tail.headD 0)

/-- con-ron: none — the memo library (open addressing over fixed arrays; the twin's `Std.HashMap` caches) -/
def memoPutG (S : MemoSch) : FunDecl := lfn (k1, k2, v, fd, j) locals (c, e) {
  if fd == 0 {
    c := CTL.u64[⟪S.cs + 1⟫];
    e := CTL.u64[⟪S.cs⟫] + 1;
    if ((len(S.arr.u64) >> 2) >> 2) * 3 < c + 1 { abort };
    S.arr.u64[j * 4] := e;
    S.arr.u64[j * 4 + 1] := k1;
    S.arr.u64[j * 4 + 2] := k2;
    CTL.u64[⟪S.cs + 1⟫] := c + 1
  };
  S.arr.u64[j * 4 + 3] := v;
  return 0
}

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
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64] <;>
      finish [mputG, mputMem, nG, epG, cntG]

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

/-- The first key word of a deleted slot. -/
def TOMB : Word := 0xFFFFFFFFFFFFFFFF

/-- The memory after `X_erase(j)`. -/
def meraseG (S : MemoSch) (m : Mem) (j : Word) : Mem := m.set64 S.arr (j * 4 + 1) TOMB

/-- con-ron: none — the memo library (open addressing over fixed arrays; the twin's `Std.HashMap` caches) -/
def memoEraseG (S : MemoSch) : FunDecl := lfn (j) locals () {
  S.arr.u64[j * 4 + 1] := ⟪TOMB⟫;
  return 0
}

theorem memoEraseG_spec (S : MemoSch) (p : Prog) (f : FnName)
    (hp : p.lookup f = some (memoEraseG S)) (n : Nat) (s₀ : St) (j : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) f [j]
    ⦃fun _ s' => LocEq s' s₀ ∧ s'.mem = meraseG S s₀.mem j; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, memoEraseG]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, st64] <;> finish [meraseG]

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

/-- The slots of `bvarBound`'s memo (`bvarBC`, one-word keys). -/
abbrev BMEMO : ArrId := 24

/-- `bvarBC`: array 24, stamp `CTL[24]`, count `CTL[25]`. -/
abbrev bmSch : MemoSch := ⟨BMEMO, 24⟩

/-- The slots of `liftLooseBVars`' memo (`liftC`, keys `(handle, cutoff)`). -/
abbrev LMEMO : ArrId := 41

/-- `liftC`: array 41, stamp `CTL[42]`, count `CTL[43]`. -/
abbrev lfSch : MemoSch := ⟨LMEMO, 42⟩

/-- The slots of `instantiate1`'s memo (`inst1C`, keys `(handle, depth)`). -/
abbrev IMEMO : ArrId := 47

/-- `inst1C`: array 47, stamp `CTL[44]`, count `CTL[45]`. -/
abbrev imSch : MemoSch := ⟨IMEMO, 44⟩

/-- The slots of `fvarRange`'s memo (`fvarBC`, one-word keys, `bvarBC`'s codec: `bmKey`). -/
abbrev FRMEMO : ArrId := 48

/-- `fvarBC`: array 48, stamp `CTL[46]`, count `CTL[47]`. -/
abbrev frSch : MemoSch := ⟨FRMEMO, 46⟩

end L.Arena
