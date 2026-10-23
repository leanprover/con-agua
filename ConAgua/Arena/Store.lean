module

public import ConAgua.L.Notation
public import ConAgua.Arena.Pool
public import ConAgua.Arena.SlotGrowSpec
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.SlotGrow
import ConAgua.Census.Attr

@[expose] public section

/-!
# The `lit` node store in L: records, derived hashes, an open-addressing cons table

con-ron's arena keeps every expression constructor in its own `Tbl` (`Arena/Store.lean:64`): an
array of node records, a parallel array of derived words, and a cons table
`Std.HashMap record handle`, in two tiers (persistent and scratch). This file is the L
representation of the `lit` constructor's tables, restricted to what `intern_lit` needs:

* **Records.** Word array `REC`, four words per node: kind (`0` = `natVal`, `1` = `strVal`),
  limb-pool offset, length, and the hash of the limbs (the derived word of the L table; the
  arena's own derived word, `derOfLit`, goes through Lean's opaque `mixHash` and is not
  represented). The two tiers are interleaved: node `i` of tier `t` is at
  `REC[8 i + 4 t .. 8 i + 4 t + 3]`. The node count of tier `t` is `CTL[2 + t]`.
* **Cons table.** Word array `SLOT`, the two tiers interleaved again: slot `j` of tier `t` is
  `SLOT[2 j + t]`, `n = len(SLOT) / 2` slots per tier. A slot holds `0` (free) or `i + 1`
  (node `i`). Linear probing from the home slot `mulhi(mix h, n)` with wrap-around, as
  con-ron's `HashMap2` (`ron/hashmap2.rs`): the multiply-xor finaliser is `home_index`'s, the
  range reduction is a multiply-high instead of a mask, so `n` need not be a power of two.
  No deletion, so no tombstones.
* **Scratch flag.** `CTL[1] ≠ 0` iff the scratch tier is open.

The functions: `lit_hash(o, l)` (con-ron's `nat::hash64`, FNV-1a over the limbs),
`limbs_eq(a, b, l)`, `lit_match(t, i, o, l, h)` (does node `i` of tier `t` hold the slice
`(o, l)` with hash `h`), `lit_find(t, o, l, h)` (the probe), `lit_push(t, o, l, h, j)` (append
a node, register it at slot `j`) and `intern_lit(o, l)` (`internE (.lit (.natVal n))`).

Every spec here is about L memory only, against models that compute with words exactly as the
L code does (`eqW`, `matchW`, `probeW`). What those models mean for the arena's tables is
`ConAgua/Arena/LitRefine.lean`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The `lit` records, both tiers interleaved (four words per node). -/
abbrev REC : ArrId := 2
/-- The `lit` cons-table slots, both tiers interleaved. -/
abbrev SLOT : ArrId := 3

/-- The growth schema of this table (`SlotGrow.lean`). -/
def litGS : GrowSch :=
  ⟨SLOT, REC, 4, 2, lblk (n, k, t, i, c, h) {
    h := REC.u64[i * 8 + t * 4 + 3]
  }⟩


/-! ## `lit_hash(o, l)`: FNV-1a over the limbs of a slice -/

/-- The model: the hash of the first `k` limbs of the slice at `o`. -/
def hashN (p : Array Word) (o : Nat) : Nat → Word
  | 0 => fnvBasis
  | k + 1 => (hashN p o k ^^^ (p[o + k]?.getD 0)) * fnvPrime

@[arena_grind =] theorem hashN_zero (p : Array Word) (o : Nat) : hashN p o 0 = fnvBasis := rfl

theorem hashN_succ (p : Array Word) (o k k' j : Nat) (hk : k' = k + 1) (hj : j = o + k)
    (h : j < p.size) : hashN p o k' = (hashN p o k ^^^ p[j]) * fnvPrime := by
  subst hk hj; simp [hashN, h]
grind_pattern [arena_grind] hashN_succ => hashN p o k', hashN p o k, p[j]

def hashLoop : Stmt := lblk (o, l, i, h) {
  while i < l {
    h := (h ^ POOL.u64[o + i]) * ⟪fnvPrime⟫;
    i += 1
  }
}

/-- con-ron: none — the open-addressing table's own key hash/compare (the twin's `Std.HashMap`) -/
def litHash : FunDecl := lfn (o, l) locals (i, h) {
  h := ⟪fnvBasis⟫;
  ⟪hashLoop⟫;
  return h
}

section hash
variable (p : Prog) (hp : p.lookup "lit_hash" = some litHash)

theorem hashLoop_spec (n : Nat) (s₀ : St) (hs : (s₀.mem.arr64 POOL).size < 2 ^ 64)
    (hb : (s₀.loc 0).toNat + (s₀.loc 1).toNat ≤ (s₀.mem.arr64 POOL).size)
    (hi : (s₀.loc 2).toNat ≤ (s₀.loc 1).toNat)
    (hh : s₀.loc 3 = hashN (s₀.mem.arr64 POOL) (s₀.loc 0).toNat (s₀.loc 2).toNat) :
    ⦃fun s => s = s₀⦄
    exec p n hashLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧
      s'.loc 3 = hashN (s₀.mem.arr64 POOL) (s₀.loc 0).toNat (s₀.loc 1).toNat; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := hashLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, ld64, ih] <;> finish

theorem hashLoop_step_spec (n : Nat) (s₀ : St) (hs : (s₀.mem.arr64 POOL).size < 2 ^ 64)
    (hb : (s₀.loc 0).toNat + (s₀.loc 1).toNat ≤ (s₀.mem.arr64 POOL).size)
    (hi : (s₀.loc 2).toNat ≤ (s₀.loc 1).toNat)
    (hh : s₀.loc 3 = hashN (s₀.mem.arr64 POOL) (s₀.loc 0).toNat (s₀.loc 2).toNat) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) hashLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧
      s'.loc 3 = hashN (s₀.mem.arr64 POOL) (s₀.loc 0).toNat (s₀.loc 1).toNat; ⊤⦄ :=
  Triple.step_exec (hashLoop_spec p (n + 1) s₀ hs hb hi hh)

include hp in
theorem litHash_spec (n : Nat) (s₀ : St) (o l : Word) (hs : (s₀.mem.arr64 POOL).size < 2 ^ 64)
    (hb : o.toNat + l.toNat ≤ (s₀.mem.arr64 POOL).size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "lit_hash" [o, l]
    ⦃fun r s' => s' = s₀ ∧ r.headD 0 = hashN (s₀.mem.arr64 POOL) o.toNat l.toNat; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, litHash]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLoc, hashLoop_step_spec p n] <;> finish

end hash

/-! ## `limbs_eq(a, b, l)`: are the slices `(a, l)` and `(b, l)` equal limb for limb

The model `eqW` indexes the pool with word arithmetic, exactly as the L code does, so the spec
needs no bound: a read past the pool is an L error, and on success the indices did not wrap
into the pool unless the model says so too. `eqW_iff` (`LitRefine`) turns it into a statement
about `Nat` positions. -/

def eqW (p : Array Word) (a b l i : Word) : Bool :=
  if i < l then
    if p[(a + i).toNat]?.getD 0 = p[(b + i).toNat]?.getD 0 then eqW p a b l (i + 1) else false
  else true
termination_by l.toNat - i.toNat
decreasing_by
  have : i.toNat < l.toNat := by simpa [UInt64.lt_iff_toNat_lt] using ‹i < l›
  have := l.toNat_lt
  have : (i + 1).toNat = i.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  omega

theorem eqW_end (p : Array Word) (a b l i : Word) (h : ¬ i < l) : eqW p a b l i = true := by
  rw [eqW]; simp [h]

theorem eqW_ne (p : Array Word) (a b l i : Word) (ja jb : Nat) (hi : i < l) (hja : ja = (a + i).toNat)
    (hjb : jb = (b + i).toNat) (ha : ja < p.size) (hb : jb < p.size) (hne : p[ja] ≠ p[jb]) :
    eqW p a b l i = false := by
  subst hja hjb
  rw [eqW]; simp only [hi, ↓reduceIte]; rw [getElem?_pos p _ ha, getElem?_pos p _ hb, Option.getD_some,
    Option.getD_some]
  simp only [hne, ↓reduceIte]

theorem eqW_eq (p : Array Word) (a b l i i' : Word) (ja jb : Nat) (hi : i < l) (hi' : i' = i + 1)
    (hja : ja = (a + i).toNat) (hjb : jb = (b + i).toNat) (ha : ja < p.size) (hb : jb < p.size)
    (he : p[ja] = p[jb]) : eqW p a b l i = eqW p a b l i' := by
  subst hja hjb hi'
  rw [eqW]; simp only [hi, ↓reduceIte]; rw [getElem?_pos p _ ha, getElem?_pos p _ hb, Option.getD_some,
    Option.getD_some]
  simp only [he, ↓reduceIte]

grind_pattern [arena_grind] eqW_end => eqW p a b l i
grind_pattern [arena_grind] eqW_ne => eqW p a b l i, p[ja], p[jb]
grind_pattern [arena_grind] eqW_eq => eqW p a b l i, p[ja], p[jb], eqW p a b l i'

def eqLoop : Stmt := lblk (a, b, l, i) {
  while i < l {
    if POOL.u64[a + i] != POOL.u64[b + i] { return 0 };
    i += 1
  }
}

/-- con-ron: none — the open-addressing table's own key hash/compare (the twin's `Std.HashMap`) -/
def limbsEq : FunDecl := lfn (a, b, l) locals (i) {
  ⟪eqLoop⟫;
  return 1
}

section eq
variable (p : Prog) (hp : p.lookup "limbs_eq" = some limbsEq)

theorem eqLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n eqLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [1] = [if eqW (s₀.mem.arr64 POOL) (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3)
        then 1 else 0]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := eqLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, ld64, ih] <;> finish

theorem eqLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) eqLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [1] = [if eqW (s₀.mem.arr64 POOL) (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3)
        then 1 else 0]; ⊤⦄ :=
  Triple.step_exec (eqLoop_spec p (n + 1) s₀)

include hp in
theorem limbsEq_spec (n : Nat) (s₀ : St) (a b l : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "limbs_eq" [a, b, l]
    ⦃fun r s' => s' = s₀ ∧ r = [if eqW (s₀.mem.arr64 POOL) a b l 0 then 1 else 0]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, limbsEq]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, eqLoop_step_spec p n] <;> finish

end eq

/-! ## `lit_match(t, i, o, l, h)`: does node `i` of tier `t` hold the slice `(o, l)`?

A `natVal` node (kind `0`) with hash `h`, length `l` and the same limbs. -/

/-- The model of `lit_match`. -/
def matchW (r p : Array Word) (t i o l h : Word) : Bool :=
  rdW r (i * 8 + t * 4) == 0 && rdW r (i * 8 + t * 4 + 3) == h &&
    rdW r (i * 8 + t * 4 + 2) == l && eqW p (rdW r (i * 8 + t * 4 + 1)) o l 0

/-- con-ron: none — the open-addressing table's own key hash/compare (the twin's `Std.HashMap`) -/
def litMatch : FunDecl := lfn (t, i, o, l, h) locals (k, e) {
  k := i * 8 + t * 4;
  if REC.u64[k] != 0 { return 0 };
  if REC.u64[k + 3] != h { return 0 };
  if REC.u64[k + 2] != l { return 0 };
  e := call limbs_eq(REC.u64[k + 1], o, l);
  return e
}

section match_
variable (p : Prog) (hpe : p.lookup "limbs_eq" = some limbsEq)
  (hp : p.lookup "lit_match" = some litMatch)

include hpe hp in
theorem litMatch_spec (n : Nat) (s₀ : St) (t i o l h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "lit_match" [t, i, o, l, h]
    ⦃fun r s' => s' = s₀ ∧
      r = [if matchW (s₀.mem.arr64 REC) (s₀.mem.arr64 POOL) t i o l h then 1 else 0]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, litMatch]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, limbsEq_spec p hpe n] <;>
      finish [matchW]

end match_

/-! ## `lit_find(t, o, l, h)`: the probe

Returns `(1, i, j, d)` if node `i` of tier `t` holds the slice (found at slot `j` after `d`
steps), `(0, 0, j, d)` if slot `j` is free (the run from the home slot holds no such node), and
aborts after `n` steps (a full table; unreachable while the load limit of `lit_push` holds). -/

/-- The model of the probe loop, from slot `j` after `d` steps. -/
def probeW (sl r p : Array Word) (t o l h b n j d : Word) : List Word :=
  if d < n then
    if slotV sl b (j * 2 + t) = 0 then [0, 0, j, d]
    else if matchW r p t (slotV sl b (j * 2 + t) - 1) o l h then [1, slotV sl b (j * 2 + t) - 1, j, d]
    else probeW sl r p t o l h b n ((j + 1) * (if j + 1 < n then 1 else 0)) (d + 1)
  else []
termination_by n.toNat - d.toNat
decreasing_by
  have : d.toNat < n.toNat := by simpa [UInt64.lt_iff_toNat_lt] using ‹d < n›
  have := n.toNat_lt
  have : (d + 1).toNat = d.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  omega

section probeArms
variable (sl r p : Array Word) (t o l h b n j d : Word)

theorem probeW_free (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : sl[k] ≤ b) : probeW sl r p t o l h b n j d = [0, 0, j, d] := by
  rw [probeW]; simp only [hd, ↓reduceIte, slotV_free sl b _ k hk hks hv]

theorem probeW_hit (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : ¬ sl[k] ≤ b) (hm : matchW r p t (sl[k] - b - 1) o l h = true) :
    probeW sl r p t o l h b n j d = [1, sl[k] - b - 1, j, d] := by
  obtain ⟨e, ne⟩ := slotV_used sl b _ k hk hks hv
  rw [probeW]; simp only [hd, ↓reduceIte, e, ne, hm]

theorem probeW_next (k : Nat) (j' d' : Word) (hd : d < n) (hk : k = (j * 2 + t).toNat)
    (hks : k < sl.size) (hv : ¬ sl[k] ≤ b) (hm : matchW r p t (sl[k] - b - 1) o l h = false)
    (hj' : j' = (j + 1) * (if j + 1 < n then 1 else 0)) (hd' : d' = d + 1) :
    probeW sl r p t o l h b n j d = probeW sl r p t o l h b n j' d' := by
  subst hj' hd'
  obtain ⟨e, ne⟩ := slotV_used sl b _ k hk hks hv
  rw [probeW]; simp only [hd, ↓reduceIte, e, ne, hm]; simp

end probeArms

grind_pattern [arena_grind] probeW_free => probeW sl r p t o l h b n j d, sl[k]
grind_pattern [arena_grind] probeW_hit => probeW sl r p t o l h b n j d, sl[k]
grind_pattern [arena_grind] probeW_next =>
  probeW sl r p t o l h b n j d, sl[k], probeW sl r p t o l h b n j' d'

def findLoop : Stmt := lblk (t, o, l, h, n, j, d, v, m, b) {
  while d < n {
    v := SLOT.u64[j * 2 + t];
    if v <= b { return (0, 0, j, d) };
    v := v - b;
    m := call lit_match(t, v - 1, o, l, h);
    if m != 0 { return (1, v - 1, j, d) };
    j := (j + 1) * u64(j + 1 < n);
    d += 1
  }
}

/-- con-ron: ConRon/Arena/Store.lean:90-91 ConRon.Arena.Tbl.find? -/
def litFind : FunDecl := lfn (t, o, l, h) locals (n, j, d, v, m, b) {
  n := SLOT.u64[len(SLOT.u64) - 1] + ⟪SN0⟫;
  b := CTL.u64[62] * t;
  j := mulhi((h * ⟪golden⟫) ^ ((h * ⟪golden⟫) >> 32), n);
  ⟪findLoop⟫;
  abort
}

section find
variable (p : Prog) (hpe : p.lookup "limbs_eq" = some limbsEq)
  (hpm : p.lookup "lit_match" = some litMatch) (hp : p.lookup "lit_find" = some litFind)

include hpe hpm in
theorem findLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n findLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (probeW (s₀.mem.arr64 SLOT) (s₀.mem.arr64 REC) (s₀.mem.arr64 POOL) (s₀.loc 0)
        (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 9) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6)) =
      probeW (s₀.mem.arr64 SLOT) (s₀.mem.arr64 REC) (s₀.mem.arr64 POOL) (s₀.loc 0)
        (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 9) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := findLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih,
        litMatch_spec p hpe hpm n] <;> finish

include hpe hpm in
theorem findLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) findLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (probeW (s₀.mem.arr64 SLOT) (s₀.mem.arr64 REC) (s₀.mem.arr64 POOL) (s₀.loc 0)
        (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 9) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6)) =
      probeW (s₀.mem.arr64 SLOT) (s₀.mem.arr64 REC) (s₀.mem.arr64 POOL) (s₀.loc 0)
        (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 9) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6); ⊤⦄ :=
  Triple.step_exec (findLoop_spec p hpe hpm (n + 1) s₀)

/-- The slot count of a tier. -/
def nSlots (m : Mem) : Word := rdW (m.arr64 SLOT) (m.len64 SLOT - 1) + SN0

include hpe hpm hp in
theorem litFind_spec (n : Nat) (s₀ : St) (t o l h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "lit_find" [t, o, l, h]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧
      r = probeW (s₀.mem.arr64 SLOT) (s₀.mem.arr64 REC) (s₀.mem.arr64 POOL) t o l h
        (baseW s₀.mem t) (nSlots s₀.mem) (homeW h (nSlots s₀.mem)) 0; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, litFind]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLoc, ld64, findLoop_step_spec p hpe hpm n] <;>
      finish [nSlots, homeW, baseW]

end find

/-! ## `lit_push(t, o, l, h, j)`: append a node to tier `t`, register it at slot `j`

`j` is the free slot `lit_find` returned. Aborts if the tier has `2^27` nodes (the arena's
`native` failure at `Idx.idxCap`), if the record array is full, or if the table would pass its
load limit of `3/4` (a defined "exhausted": the arena does not fail there, the L run does). -/

/-- The node count of tier `t`, `CTL[2 + t]`. -/
def cnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (2 + t)

/-- `lit_push`'s room checks: the handle index, the record array. -/
def pushOK (m : Mem) (t : Word) : Bool :=
  decide (cnt m t < (134217728 : Word)) && decide (cnt m t < m.len64 REC >>> (3 : Word))

/-- The memory after `lit_push(t, o, l, h, j)` appended node `c`. -/
def pushMem (m : Mem) (t o l h j c : Word) : Mem :=
  ((((((m.set64 REC (c * 8 + t * 4) 0).set64 REC (c * 8 + t * 4 + 1) o).set64 REC
    (c * 8 + t * 4 + 2) l).set64 REC (c * 8 + t * 4 + 3) h).set64 SLOT (j * 2 + t)
    (baseW m t + c + 1)).set64
    CTL (2 + (t &&& 1)) (c + 1))

/-- con-ron: ConRon/Arena/Store.lean:93-98 ConRon.Arena.Tbl.push -/
def litPush : FunDecl := lfn (t, o, l, h, j) locals (c, k, gn, gk, gt, gi, gc, gh, gj, gb, gd) {
  c := CTL.u64[2 + t];
  if c >= 134217728 { abort };
  if len(REC.u64) >> 3 <= c { abort };
  k := c * 8 + t * 4;
  gk := SLOT.u64[len(SLOT.u64) - 1];
  REC.u64[k] := 0;
  REC.u64[k + 1] := o;
  REC.u64[k + 2] := l;
  REC.u64[k + 3] := h;
  SLOT.u64[j * 2 + t] := CTL.u64[62] * t + c + 1;
  CTL.u64[2 + (t & 1)] := c + 1;
  if gk + ⟪SN0⟫ < (c + 1) * 2 { ⟪growBlkG litGS 7⟫ };
  return c
}

/-- The hash of node `i` of tier `t`: its word 3. -/
def litH (m : Mem) (t i : Word) : Word := rdW (m.arr64 REC) (i * 8 + t * 4 + 3)

section push
variable (p : Prog) (hp : p.lookup "lit_push" = some litPush)

/-- The growth's hash block computes `litH`. -/
theorem litH_ok : HashOK p litGS 7 litH := by
  intro k s₀
  simp only [litGS, shiftS, shiftE, L.Notation.blk]
  sym only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalArgs, setLoc, ld64] <;> finish [litH, LocEq, St.setLoc]

include hp in
theorem litPush_spec (n : Nat) (s₀ : St) (t o l h j : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "lit_push" [t, o, l, h, j]
    ⦃fun r s' => LocEq s' s₀ ∧ pushOK s₀.mem t = true ∧ r = [cnt s₀.mem t] ∧
      growIf SLOT 2 litH s₀.mem (pushMem s₀.mem t o l h j (cnt s₀.mem t))
        (cnt s₀.mem t) = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, litPush]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64, st64,
        growBlkG_spec p litGS SLOT 2 rfl rfl 7 litH (litH_ok p) n] <;>
      finish [pushMem, cnt, pushOK, baseW, growIf_grow', growIf_keep']

end push

/-! ## `intern_lit(o, l)`: hash-cons the `natVal` literal whose limbs are the slice `(o, l)`

con-ron's `EStore::intern_lit` (`arena/store.rs:4260`) and the arena's `internE (.lit _)`: probe
the persistent tier; if the scratch tier is open, probe it; append to the tier the store is in.
The handle is the arena's word: tag `8` (`ETag.lit`) in bits 31…28, the tier in bit 27, the
index below. -/

/-- The handle word of node `0` of the persistent / scratch `lit` tier. -/
def litP : Word := 0x80000000
def litS : Word := 0x88000000

/-- The model of `intern_lit`: the handle and the memory after, or `none` where the L code
aborts. `rs₀`, `rs₁`: the two probes (`[]`: the probe aborted). -/
def internW (m : Mem) (o l : Word) : Option (Word × Mem) :=
  let h := hashN (m.arr64 POOL) o.toNat l.toNat
  let rs₀ := probeW (m.arr64 SLOT) (m.arr64 REC) (m.arr64 POOL) 0 o l h (baseW m 0) (nSlots m)
    (homeW h (nSlots m)) 0
  let rs₁ := probeW (m.arr64 SLOT) (m.arr64 REC) (m.arr64 POOL) 1 o l h (baseW m 1) (nSlots m)
    (homeW h (nSlots m)) 0
  if rs₀ = [] then none
  else if rs₀.headD 0 ≠ 0 then some (litP + rs₀.tail.headD 0, m)
  else if rdW (m.arr64 CTL) 1 ≠ 0 then
    if rs₁ = [] then none
    else if rs₁.headD 0 ≠ 0 then some (litS + rs₁.tail.headD 0, m)
    else if pushOK m 1 then
      match growIf SLOT 2 litH m (pushMem m 1 o l h (rs₁.tail.tail.headD 0) (cnt m 1)) (cnt m 1) with
      | some m' => some (litS + cnt m 1, m')
      | none => none
    else none
  else if pushOK m 0 then
    match growIf SLOT 2 litH m (pushMem m 0 o l h (rs₀.tail.tail.headD 0) (cnt m 0)) (cnt m 0) with
    | some m' => some (litP + cnt m 0, m')
    | none => none
  else none

/-- con-ron: ConRon/Arena/Monad.lean:246-264 ConRon.Arena.internE
con-ron: ConRon/Arena/Monad.lean:218-244 ConRon.Arena.internNodeE -/
@[l_impl ConRon.Arena.internE ConRon.Arena.internNodeE]
def internLit : FunDecl := lfn (o, l) locals (h, f, i, j, d, sc) {
  h := call lit_hash(o, l);
  (f, i, j, d) := call lit_find(0, o, l, h);
  if f != 0 { return ⟪litP⟫ + i };
  sc := CTL.u64[1];
  if sc != 0 {
    (f, i, j, d) := call lit_find(1, o, l, h);
    if f != 0 { return ⟪litS⟫ + i };
    i := call lit_push(1, o, l, h, j);
    return ⟪litS⟫ + i
  };
  i := call lit_push(0, o, l, h, j);
  return ⟪litP⟫ + i
}

/-- The store functions, as one `#eval`-able program. -/
def litProg : Prog :=
  [("lit_hash", litHash), ("limbs_eq", limbsEq), ("lit_match", litMatch), ("lit_find", litFind),
   ("lit_push", litPush), ("intern_lit", internLit)]

/-- A memory with the limbs `5`, `7`, `5`, `1 2` in the pool (top 5), 8 nodes and 16 slots per
tier, the scratch tier closed or open. -/
def litMem (scratch : Word) : Mem :=
  { words := #[#[5, 7, 5, 1, 2, 0, 0, 0], #[5, scratch] ++ Array.replicate 62 0, Array.replicate 64 0,
      Array.replicate 32 0] }

/-- Intern each slice in turn; the handles. -/
def internAll (m : Mem) : List (Word × Word) → Option (List Word)
  | [] => some []
  | (o, l) :: xs => match run litProg 100 "intern_lit" [o, l] m with
    | .ok (r, m') => (internAll m' xs).map (r.headD 0 :: ·)
    | .error _ => none

/- `5`, `7`, `5` (another copy), `1 2`, `7`: the persistent handles 0, 1, 0, 2, 1. -/
#guard internAll (litMem 0) [(0, 1), (1, 1), (2, 1), (3, 2), (1, 1)] ==
  some [0x80000000, 0x80000001, 0x80000000, 0x80000002, 0x80000001]

/- With the scratch tier open the nodes go there (the persistent tier is empty). -/
#guard internAll (litMem 1) [(0, 1), (1, 1), (2, 1)] == some [0x88000000, 0x88000001, 0x88000000]

/- Growth: 8 slots per tier at the start; the fifth node doubles them, which a 32-word slot array
cannot hold with its last word (abort); a 128-word one holds two doublings (then all 13 nodes are
found again). -/
#guard (internAll { words := #[(Array.range 13).map (UInt64.ofNat · + 1), #[13] ++ Array.replicate 63 0,
    Array.replicate 256 0, Array.replicate 32 0] } ((List.range 5).map fun i => (UInt64.ofNat i, 1))).isNone
#guard (internAll { words := #[(Array.range 13).map (UInt64.ofNat · + 1), #[13] ++ Array.replicate 63 0,
    Array.replicate 256 0, Array.replicate 32 0] } ((List.range 4).map fun i => (UInt64.ofNat i, 1))).isSome
#guard internAll { words := #[(Array.range 13).map (UInt64.ofNat · + 1), #[13] ++ Array.replicate 63 0,
    Array.replicate 256 0, Array.replicate 128 0] }
    ((List.range 13 ++ List.range 13).map fun i => (UInt64.ofNat i, 1)) ==
  some ((List.range 13 ++ List.range 13).map fun i => 0x80000000 + UInt64.ofNat i)

section intern
variable (p : Prog) (hph : p.lookup "lit_hash" = some litHash)
  (hpe : p.lookup "limbs_eq" = some limbsEq) (hpm : p.lookup "lit_match" = some litMatch)
  (hpf : p.lookup "lit_find" = some litFind) (hpp : p.lookup "lit_push" = some litPush)
  (hp : p.lookup "intern_lit" = some internLit)

include hph hpe hpm hpf hpp hp in
theorem internLit_spec (n : Nat) (s₀ : St) (o l : Word) (hs : (s₀.mem.arr64 POOL).size < 2 ^ 64)
    (hb : o.toNat + l.toNat ≤ (s₀.mem.arr64 POOL).size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_lit" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ internW s₀.mem o l = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, internLit]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, litHash_spec p hph n,
        litFind_spec p hpe hpm hpf n, litPush_spec p hpp n] <;>
      finish [internW]

end intern

/-! ## The `strVal` arm: `lit_match_str`, `lit_find_str`, `lit_push_str`, `intern_lit_str`

con-ron's `Tbl LitNode EIdx UInt64` is one combined table per tier for *both* literal kinds
(`Arena/Store.lean:302`): a `natVal` and a `strVal` share the same node array, cons table and
counts. So this arm reuses `REC`, `SLOT`, `CTL[2 + t]` as the `natVal` arm does, and reuses
`lit_hash`/`limbs_eq`/`cnt`/`pushOK`/`nSlots`/`homeW`/`baseW` unchanged: the hash is the plain
slice hash, with the kind mixed in nowhere, since a mismatched kind is rejected by the match
check (like `nstr`'s mismatched prefix), not by a separate bucket. What differs from the
`natVal` arm is just the record's kind word, checked and written as `1` instead of `0`. -/

/-- The model of `lit_match_str`: node `i` of tier `t` has kind `1`, hash `h`, length `l` and the
words of the slice `(o, l)`. -/
def matchWStr (r p : Array Word) (t i o l h : Word) : Bool :=
  rdW r (i * 8 + t * 4) == 1 && rdW r (i * 8 + t * 4 + 3) == h &&
    rdW r (i * 8 + t * 4 + 2) == l && eqW p (rdW r (i * 8 + t * 4 + 1)) o l 0

/-- con-ron: none — the open-addressing table's own key hash/compare (the twin's `Std.HashMap`) -/
def litMatchStr : FunDecl := lfn (t, i, o, l, h) locals (k, e) {
  k := i * 8 + t * 4;
  if REC.u64[k] != 1 { return 0 };
  if REC.u64[k + 3] != h { return 0 };
  if REC.u64[k + 2] != l { return 0 };
  e := call limbs_eq(REC.u64[k + 1], o, l);
  return e
}

section matchStr
variable (p : Prog) (hpe : p.lookup "limbs_eq" = some limbsEq)
  (hp : p.lookup "lit_match_str" = some litMatchStr)

include hpe hp in
theorem litMatchStr_spec (n : Nat) (s₀ : St) (t i o l h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "lit_match_str" [t, i, o, l, h]
    ⦃fun r s' => s' = s₀ ∧
      r = [if matchWStr (s₀.mem.arr64 REC) (s₀.mem.arr64 POOL) t i o l h then 1 else 0]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, litMatchStr]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, limbsEq_spec p hpe n] <;>
      finish [matchWStr]

end matchStr

/-- The model of the `strVal` probe loop, from slot `j` after `d` steps. -/
def probeWStr (sl r p : Array Word) (t o l h b n j d : Word) : List Word :=
  if d < n then
    if slotV sl b (j * 2 + t) = 0 then [0, 0, j, d]
    else if matchWStr r p t (slotV sl b (j * 2 + t) - 1) o l h then
      [1, slotV sl b (j * 2 + t) - 1, j, d]
    else probeWStr sl r p t o l h b n ((j + 1) * (if j + 1 < n then 1 else 0)) (d + 1)
  else []
termination_by n.toNat - d.toNat
decreasing_by
  have : d.toNat < n.toNat := by simpa [UInt64.lt_iff_toNat_lt] using ‹d < n›
  have := n.toNat_lt
  have : (d + 1).toNat = d.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  omega

section probeArmsStr
variable (sl r p : Array Word) (t o l h b n j d : Word)

theorem probeWStr_free (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : sl[k] ≤ b) : probeWStr sl r p t o l h b n j d = [0, 0, j, d] := by
  rw [probeWStr]; simp only [hd, ↓reduceIte, slotV_free sl b _ k hk hks hv]

theorem probeWStr_hit (k : Nat) (hd : d < n) (hk : k = (j * 2 + t).toNat) (hks : k < sl.size)
    (hv : ¬ sl[k] ≤ b) (hm : matchWStr r p t (sl[k] - b - 1) o l h = true) :
    probeWStr sl r p t o l h b n j d = [1, sl[k] - b - 1, j, d] := by
  obtain ⟨e, ne⟩ := slotV_used sl b _ k hk hks hv
  rw [probeWStr]; simp only [hd, ↓reduceIte, e, ne, hm]

theorem probeWStr_next (k : Nat) (j' d' : Word) (hd : d < n) (hk : k = (j * 2 + t).toNat)
    (hks : k < sl.size) (hv : ¬ sl[k] ≤ b) (hm : matchWStr r p t (sl[k] - b - 1) o l h = false)
    (hj' : j' = (j + 1) * (if j + 1 < n then 1 else 0)) (hd' : d' = d + 1) :
    probeWStr sl r p t o l h b n j d = probeWStr sl r p t o l h b n j' d' := by
  subst hj' hd'
  obtain ⟨e, ne⟩ := slotV_used sl b _ k hk hks hv
  rw [probeWStr]; simp only [hd, ↓reduceIte, e, ne, hm]; simp

end probeArmsStr

grind_pattern [arena_grind] probeWStr_free => probeWStr sl r p t o l h b n j d, sl[k]
grind_pattern [arena_grind] probeWStr_hit => probeWStr sl r p t o l h b n j d, sl[k]
grind_pattern [arena_grind] probeWStr_next =>
  probeWStr sl r p t o l h b n j d, sl[k], probeWStr sl r p t o l h b n j' d'

def findLoopStr : Stmt := lblk (t, o, l, h, n, j, d, v, m, b) {
  while d < n {
    v := SLOT.u64[j * 2 + t];
    if v <= b { return (0, 0, j, d) };
    v := v - b;
    m := call lit_match_str(t, v - 1, o, l, h);
    if m != 0 { return (1, v - 1, j, d) };
    j := (j + 1) * u64(j + 1 < n);
    d += 1
  }
}

/-- con-ron: ConRon/Arena/Store.lean:90-91 ConRon.Arena.Tbl.find? -/
def litFindStr : FunDecl := lfn (t, o, l, h) locals (n, j, d, v, m, b) {
  n := SLOT.u64[len(SLOT.u64) - 1] + ⟪SN0⟫;
  b := CTL.u64[62] * t;
  j := mulhi((h * ⟪golden⟫) ^ ((h * ⟪golden⟫) >> 32), n);
  ⟪findLoopStr⟫;
  abort
}

section findStr
variable (p : Prog) (hpe : p.lookup "limbs_eq" = some limbsEq)
  (hpm : p.lookup "lit_match_str" = some litMatchStr) (hp : p.lookup "lit_find_str" = some litFindStr)

include hpe hpm in
theorem findLoopStr_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n findLoopStr
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (probeWStr (s₀.mem.arr64 SLOT) (s₀.mem.arr64 REC) (s₀.mem.arr64 POOL) (s₀.loc 0)
        (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 9) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6)) =
      probeWStr (s₀.mem.arr64 SLOT) (s₀.mem.arr64 REC) (s₀.mem.arr64 POOL) (s₀.loc 0)
        (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 9) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := findLoopStr) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih,
        litMatchStr_spec p hpe hpm n] <;> finish

include hpe hpm in
theorem findLoopStr_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) findLoopStr
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧ r.retOr [0] ≠ [] ∧
      r.retOr (probeWStr (s₀.mem.arr64 SLOT) (s₀.mem.arr64 REC) (s₀.mem.arr64 POOL) (s₀.loc 0)
        (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 9) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6)) =
      probeWStr (s₀.mem.arr64 SLOT) (s₀.mem.arr64 REC) (s₀.mem.arr64 POOL) (s₀.loc 0)
        (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 9) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6); ⊤⦄ :=
  Triple.step_exec (findLoopStr_spec p hpe hpm (n + 1) s₀)

include hpe hpm hp in
theorem litFindStr_spec (n : Nat) (s₀ : St) (t o l h : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "lit_find_str" [t, o, l, h]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧
      r = probeWStr (s₀.mem.arr64 SLOT) (s₀.mem.arr64 REC) (s₀.mem.arr64 POOL) t o l h
        (baseW s₀.mem t) (nSlots s₀.mem) (homeW h (nSlots s₀.mem)) 0; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, litFindStr]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLoc, ld64, findLoopStr_step_spec p hpe hpm n] <;>
      finish [nSlots, homeW, baseW]

end findStr

/-- The memory after `lit_push_str(t, o, l, h, j)` appended node `c`: the same writes as
`lit_push`'s, kind `1` instead of `0`. -/
def pushMemStr (m : Mem) (t o l h j c : Word) : Mem :=
  ((((((m.set64 REC (c * 8 + t * 4) 1).set64 REC (c * 8 + t * 4 + 1) o).set64 REC
    (c * 8 + t * 4 + 2) l).set64 REC (c * 8 + t * 4 + 3) h).set64 SLOT (j * 2 + t)
    (baseW m t + c + 1)).set64
    CTL (2 + (t &&& 1)) (c + 1))

/-- con-ron: ConRon/Arena/Store.lean:93-98 ConRon.Arena.Tbl.push -/
def litPushStr : FunDecl := lfn (t, o, l, h, j) locals (c, k, gn, gk, gt, gi, gc, gh, gj, gb, gd) {
  c := CTL.u64[2 + t];
  if c >= 134217728 { abort };
  if len(REC.u64) >> 3 <= c { abort };
  k := c * 8 + t * 4;
  gk := SLOT.u64[len(SLOT.u64) - 1];
  REC.u64[k] := 1;
  REC.u64[k + 1] := o;
  REC.u64[k + 2] := l;
  REC.u64[k + 3] := h;
  SLOT.u64[j * 2 + t] := CTL.u64[62] * t + c + 1;
  CTL.u64[2 + (t & 1)] := c + 1;
  if gk + ⟪SN0⟫ < (c + 1) * 2 { ⟪growBlkG litGS 7⟫ };
  return c
}

section pushStr
variable (p : Prog) (hp : p.lookup "lit_push_str" = some litPushStr)

include hp in
theorem litPushStr_spec (n : Nat) (s₀ : St) (t o l h j : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "lit_push_str" [t, o, l, h, j]
    ⦃fun r s' => LocEq s' s₀ ∧ pushOK s₀.mem t = true ∧ r = [cnt s₀.mem t] ∧
      growIf SLOT 2 litH s₀.mem (pushMemStr s₀.mem t o l h j (cnt s₀.mem t))
        (cnt s₀.mem t) = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, litPushStr]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64, st64,
        growBlkG_spec p litGS SLOT 2 rfl rfl 7 litH (litH_ok p) n] <;>
      finish [pushMemStr, cnt, pushOK, baseW, growIf_grow', growIf_keep']

end pushStr

/-- The model of `intern_lit_str`: the handle and the memory after, or `none` where the L code
aborts. Shares the `natVal` arm's handle words (`litP`, `litS`): the two literal kinds cons into
the same table. -/
def internWStr (m : Mem) (o l : Word) : Option (Word × Mem) :=
  let h := hashN (m.arr64 POOL) o.toNat l.toNat
  let rs₀ := probeWStr (m.arr64 SLOT) (m.arr64 REC) (m.arr64 POOL) 0 o l h (baseW m 0) (nSlots m)
    (homeW h (nSlots m)) 0
  let rs₁ := probeWStr (m.arr64 SLOT) (m.arr64 REC) (m.arr64 POOL) 1 o l h (baseW m 1) (nSlots m)
    (homeW h (nSlots m)) 0
  if rs₀ = [] then none
  else if rs₀.headD 0 ≠ 0 then some (litP + rs₀.tail.headD 0, m)
  else if rdW (m.arr64 CTL) 1 ≠ 0 then
    if rs₁ = [] then none
    else if rs₁.headD 0 ≠ 0 then some (litS + rs₁.tail.headD 0, m)
    else if pushOK m 1 then
      match growIf SLOT 2 litH m (pushMemStr m 1 o l h (rs₁.tail.tail.headD 0) (cnt m 1)) (cnt m 1) with
      | some m' => some (litS + cnt m 1, m')
      | none => none
    else none
  else if pushOK m 0 then
    match growIf SLOT 2 litH m (pushMemStr m 0 o l h (rs₀.tail.tail.headD 0) (cnt m 0)) (cnt m 0) with
    | some m' => some (litP + cnt m 0, m')
    | none => none
  else none

/-- con-ron: ConRon/Arena/Monad.lean:246-264 ConRon.Arena.internE
con-ron: ConRon/Arena/Monad.lean:218-244 ConRon.Arena.internNodeE -/
@[l_impl ConRon.Arena.internE ConRon.Arena.internNodeE]
def internLitStr : FunDecl := lfn (o, l) locals (h, f, i, j, d, sc) {
  h := call lit_hash(o, l);
  (f, i, j, d) := call lit_find_str(0, o, l, h);
  if f != 0 { return ⟪litP⟫ + i };
  sc := CTL.u64[1];
  if sc != 0 {
    (f, i, j, d) := call lit_find_str(1, o, l, h);
    if f != 0 { return ⟪litS⟫ + i };
    i := call lit_push_str(1, o, l, h, j);
    return ⟪litS⟫ + i
  };
  i := call lit_push_str(0, o, l, h, j);
  return ⟪litP⟫ + i
}

/-- The `strVal` store functions, as one `#eval`-able program. -/
def litProgStr : Prog :=
  [("lit_hash", litHash), ("limbs_eq", limbsEq), ("lit_match_str", litMatchStr),
   ("lit_find_str", litFindStr), ("lit_push_str", litPushStr), ("intern_lit_str", internLitStr)]

section internStr
variable (p : Prog) (hph : p.lookup "lit_hash" = some litHash)
  (hpe : p.lookup "limbs_eq" = some limbsEq) (hpm : p.lookup "lit_match_str" = some litMatchStr)
  (hpf : p.lookup "lit_find_str" = some litFindStr) (hpp : p.lookup "lit_push_str" = some litPushStr)
  (hp : p.lookup "intern_lit_str" = some internLitStr)

include hph hpe hpm hpf hpp hp in
theorem internLitStr_spec (n : Nat) (s₀ : St) (o l : Word) (hs : (s₀.mem.arr64 POOL).size < 2 ^ 64)
    (hb : o.toNat + l.toNat ≤ (s₀.mem.arr64 POOL).size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_lit_str" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ internWStr s₀.mem o l = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, internLitStr]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, litHash_spec p hph n,
        litFindStr_spec p hpe hpm hpf n, litPushStr_spec p hpp n] <;>
      finish [internWStr]

end internStr

end L.Arena
