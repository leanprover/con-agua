module

public import ConAgua.Arena.Store
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store

@[expose] public section

/-!
# A per-call memo table in L: open addressing with an epoch stamp

The arena keeps the memo of the loose-bvar-bound walk (`bvarBoundGo`, `Arena/ExprOps.lean:1404`)
as `a.memos.bvarBC : Std.HashMap EIdx Nat`, cleared at the walk's entry and exit
(`bvarBoundMemo`). con-ron's Rust keeps it in a `HashMap2` (`ron/hashmap2.rs`): open addressing,
linear probing, and an **epoch stamp** per slot, so that `clear` is `epoch += 1`, O(1). The L
table follows it:

* **Slots.** Word array `BMEMO`, four words per slot: the stamp, the key (the handle word), the
  value, one unused word (so that the slot count is `len >> 2`; L has no division). Slot `j` is
  **live** iff its stamp is the live stamp `CTL[24] + 1`; any other stamp is free space. An
  all-zero memory is therefore an empty table.
* **Clear** (`memo_clear`): `CTL[24] += 1`, and the live count `CTL[25] := 0`. It aborts where the
  stamp would wrap (after `2^64 - 2` clears), as `HashMap2` restarts its `u32` epoch.
* **Find** (`memo_find(k)`): the probe from `homeW k n`, returning `(found, slot, steps)`.
* **Set** (`memo_set(k, v)`): the probe; on a free slot, stamp it and write the key (aborting past
  a load of 3/4, as the stores do); then write the value. A key already present is overwritten,
  as `Std.HashMap.insert` does.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The memo slots of the loose-bvar-bound walk, four words per slot. -/
abbrev BMEMO : ArrId := 24

/-- The live stamp, `CTL[24] + 1`. -/
def epW (m : Mem) : Word := rdW (m.arr64 CTL) 24 + 1

/-- The slot count of the memo. -/
def nM (m : Mem) : Word := m.len64 BMEMO >>> 2

/-- The live count, `CTL[25]` (only the load limit reads it). -/
def bmcnt (m : Mem) : Word := rdW (m.arr64 CTL) 25

/-! ## `memo_find(k)`: the probe -/

/-- The model of the probe loop, from slot `j` after `d` steps, live stamp `e`. -/
def bmprobeW (mm : Array Word) (k e n j d : Word) : List Word :=
  if d < n then
    if rdW mm (j * 4) ≠ e then [0, j, d]
    else if rdW mm (j * 4 + 1) = k then [1, j, d]
    else bmprobeW mm k e n ((j + 1) * (if j + 1 < n then 1 else 0)) (d + 1)
  else []
termination_by n.toNat - d.toNat
decreasing_by
  have : d.toNat < n.toNat := by simpa [UInt64.lt_iff_toNat_lt] using ‹d < n›
  have := n.toNat_lt
  have : (d + 1).toNat = d.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  omega

section probeArms
variable (mm : Array Word) (k e n j d : Word)

theorem bmprobeW_free (a : Nat) (hd : d < n) (ha : a = (j * 4).toNat) (has : a < mm.size)
    (hv : mm[a] ≠ e) : bmprobeW mm k e n j d = [0, j, d] := by
  rw [bmprobeW]; simp only [hd, ↓reduceIte, rdW_eq mm _ a ha has, hv, ne_eq, not_false_eq_true]

theorem bmprobeW_hit (a b : Nat) (hd : d < n) (ha : a = (j * 4).toNat) (has : a < mm.size)
    (hb : b = (j * 4 + 1).toNat) (hbs : b < mm.size) (hv : mm[a] = e) (hk : mm[b] = k) :
    bmprobeW mm k e n j d = [1, j, d] := by
  rw [bmprobeW]; simp only [hd, ↓reduceIte, rdW_eq mm _ a ha has, rdW_eq mm _ b hb hbs, hv, hk,
    ne_eq, not_true_eq_false]

theorem bmprobeW_next (a b : Nat) (j' d' : Word) (hd : d < n) (ha : a = (j * 4).toNat)
    (has : a < mm.size) (hb : b = (j * 4 + 1).toNat) (hbs : b < mm.size) (hv : mm[a] = e)
    (hk : mm[b] ≠ k) (hj' : j' = (j + 1) * (if j + 1 < n then 1 else 0)) (hd' : d' = d + 1) :
    bmprobeW mm k e n j d = bmprobeW mm k e n j' d' := by
  subst hj' hd'
  rw [bmprobeW]; simp only [hd, ↓reduceIte, rdW_eq mm _ a ha has, rdW_eq mm _ b hb hbs, hv, hk,
    ne_eq, not_true_eq_false]

end probeArms

grind_pattern [arena_grind] bmprobeW_free => bmprobeW mm k e n j d, mm[a]
grind_pattern [arena_grind] bmprobeW_hit => bmprobeW mm k e n j d, mm[a], mm[b]
grind_pattern [arena_grind] bmprobeW_next =>
  bmprobeW mm k e n j d, mm[a], mm[b], bmprobeW mm k e n j' d'

def bmfindLoop : Stmt := lblk (k, n, e, j, d) {
  while d < n {
    if BMEMO.u64[j * 4] != e { return (0, j, d) };
    if BMEMO.u64[j * 4 + 1] == k { return (1, j, d) };
    j := (j + 1) * u64(j + 1 < n);
    d += 1
  }
}

def memoFind : FunDecl := lfn (k) locals (n, e, j, d) {
  n := len(BMEMO.u64) >> 2;
  e := CTL.u64[24] + 1;
  j := mulhi((k * ⟪golden⟫) ^ ((k * ⟪golden⟫) >> 32), n);
  ⟪bmfindLoop⟫;
  abort
}

section find
variable (p : Prog) (hp : p.lookup "memo_find" = some memoFind)

theorem bmfindLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n bmfindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (bmprobeW (s₀.mem.arr64 BMEMO) (s₀.loc 0) (s₀.loc 2) (s₀.loc 1) (s₀.loc 3)
        (s₀.loc 4)) =
      bmprobeW (s₀.mem.arr64 BMEMO) (s₀.loc 0) (s₀.loc 2) (s₀.loc 1) (s₀.loc 3) (s₀.loc 4); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := bmfindLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;> finish

theorem bmfindLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) bmfindLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (bmprobeW (s₀.mem.arr64 BMEMO) (s₀.loc 0) (s₀.loc 2) (s₀.loc 1) (s₀.loc 3)
        (s₀.loc 4)) =
      bmprobeW (s₀.mem.arr64 BMEMO) (s₀.loc 0) (s₀.loc 2) (s₀.loc 1) (s₀.loc 3) (s₀.loc 4); ⊤⦄ :=
  Triple.step_exec (bmfindLoop_spec p (n + 1) s₀)

/-- The probe of the memo for key `k`. -/
def mfindW (m : Mem) (k : Word) : List Word :=
  bmprobeW (m.arr64 BMEMO) k (epW m) (nM m) (homeW k (nM m)) 0

include hp in
theorem memoFind_spec (n : Nat) (s₀ : St) (k : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "memo_find" [k]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧ r = mfindW s₀.mem k; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, memoFind]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLoc, ld64, bmfindLoop_step_spec p n] <;>
      finish [mfindW, nM, epW, homeW]

end find

/-! ## `memo_set(k, v)` -/

/-- The memory after `memo_set(k, v)` when the probe stopped at slot `j` (`fd ≠ 0`: the key is
there). -/
def msetMem (m : Mem) (fd j k v : Word) : Mem :=
  if fd = 0 then
    (((m.set64 BMEMO (j * 4) (epW m)).set64 BMEMO (j * 4 + 1) k).set64 CTL 25 (bmcnt m + 1)).set64
      BMEMO (j * 4 + 2) v
  else m.set64 BMEMO (j * 4 + 2) v

/-- The model of `memo_set(k, v)`: the memory after, or `none` where the L code aborts. -/
def msetW (m : Mem) (k v : Word) : Option Mem :=
  if mfindW m k = [] then none
  else if (mfindW m k).headD 0 = 0 ∧ (nM m >>> 2) * 3 < bmcnt m + 1 then none
  else some (msetMem m ((mfindW m k).headD 0) ((mfindW m k).tail.headD 0) k v)

def memoSet : FunDecl := lfn (k, v) locals (fd, j, d, c) {
  (fd, j, d) := call memo_find(k);
  if fd == 0 {
    c := CTL.u64[25];
    if ((len(BMEMO.u64) >> 2) >> 2) * 3 < c + 1 { abort };
    BMEMO.u64[j * 4] := CTL.u64[24] + 1;
    BMEMO.u64[j * 4 + 1] := k;
    CTL.u64[25] := c + 1
  };
  BMEMO.u64[j * 4 + 2] := v;
  return 0
}

section set
variable (p : Prog) (hpf : p.lookup "memo_find" = some memoFind)
  (hp : p.lookup "memo_set" = some memoSet)

include hpf hp in
theorem memoSet_spec (n : Nat) (s₀ : St) (k v : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "memo_set" [k, v]
    ⦃fun _ s' => LocEq s' s₀ ∧ msetW s₀.mem k v = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, memoSet]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        memoFind_spec p hpf n] <;>
      finish [msetW, msetMem, nM, epW, bmcnt]

end set

/-! ## `memo_clear()` -/

/-- The memory after `memo_clear()`. -/
def mclearMem (m : Mem) : Mem := (m.set64 CTL 24 (rdW (m.arr64 CTL) 24 + 1)).set64 CTL 25 0

def memoClear : FunDecl := lfn () locals () {
  if CTL.u64[24] + 2 == 0 { abort };
  CTL.u64[24] := CTL.u64[24] + 1;
  CTL.u64[25] := 0;
  return 0
}

section clear
variable (p : Prog) (hp : p.lookup "memo_clear" = some memoClear)

include hp in
theorem memoClear_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "memo_clear" []
    ⦃fun _ s' => LocEq s' s₀ ∧ rdW (s₀.mem.arr64 CTL) 24 + 2 ≠ 0 ∧ s'.mem = mclearMem s₀.mem; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, memoClear]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64, st64] <;>
      finish [mclearMem]

end clear

/-- The memo functions, as one `#eval`-able program. -/
def memoProg : Prog :=
  [("memo_find", memoFind), ("memo_set", memoSet), ("memo_clear", memoClear)]

/-- A memory with 8 memo slots (arrays 0‥23 empty). -/
def memoMem : Mem :=
  { words := (Array.replicate 24 #[]).set! 1 (Array.replicate 26 0) ++ #[Array.replicate 32 0] }

/-- Run `f` and return the first result and the memory. -/
def memoRun (f : FnName) (args : List Word) (m : Mem) : Option (Word × Mem) :=
  match run memoProg 100 f args m with
  | .ok (r, m') => some (r.headD 0, m')
  | .error _ => none

/- Set `7 ↦ 3`, `9 ↦ 4`, `7 ↦ 5`; find `7` (found), clear, find `7` (not found). -/
#guard
  match memoRun "memo_set" [7, 3] memoMem with
  | some (_, m) => match memoRun "memo_set" [9, 4] m with
    | some (_, m) => match memoRun "memo_set" [7, 5] m with
      | some (_, m) =>
        let r := mfindW m 7
        r.headD 0 == 1 && rdW (m.arr64 BMEMO) (r.tail.headD 0 * 4 + 2) == 5 && bmcnt m == 2 &&
        (match memoRun "memo_clear" [] m with
         | some (_, m) => (mfindW m 7).headD 0 == 0 && (mfindW m 9).headD 0 == 0
         | none => false)
      | none => false
    | none => false
  | none => false

end L.Arena
