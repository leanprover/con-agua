module

public import ConAgua.L.Notation
public import ConAgua.Arena.Pool
public import ConAgua.Arena.SlotGrowSpec
public import ConAgua.Arena.ConsLibSpec
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.SlotGrow
meta import ConAgua.Arena.ConsLib
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

/-! ## The `lit` table as a cons schema (`ConsLib.lean`)

Both literal kinds cons into one table (`REC`, `SLOT`, `CTL[2 + t]`): two schemas on the same
arrays, `litCS` (`natVal`, kind word `0`, `lit_match`) and `litStrCS` (`strVal`, kind `1`,
`lit_match_str`). The key is the slice `(o, l)`; the record stores the kind, the slice and its
hash; the match is a call; the key's hash is `lit_hash`'s (it reads the pool: `litKeyOK`). -/

/-- The handle word of node `0` of the persistent / scratch `lit` tier. -/
def litP : Word := 0x80000000
def litS : Word := 0x88000000

/-- The hash of node `i` of tier `t`: its word 3. -/
def litH (m : Mem) (t i : Word) : Word := rdW (m.arr64 REC) (i * 8 + t * 4 + 3)

/-- The pool slice of a key is in bounds (what `lit_hash`'s spec needs). -/
def litKeyOK (m : Mem) (ks : List Word) : Prop :=
  (m.arr64 POOL).size < 2 ^ 64 ∧ (ks.getD 0 0).toNat + (ks.getD 1 0).toNat ≤ (m.arr64 POOL).size

/-- The schema of one literal kind: kind word `kd`, match function `mf` (model `mt`), function
names. -/
def litCSk (kd : Word) (mf fname pname : String) (mt : Array Word → Array Word → Word → Word →
    Word → Word → Word → Bool) : ConsSch where
  ra := REC
  sa := SLOT
  w := 4
  st := 8
  ca := 2
  P := litP
  S := litS
  tag := 8
  fname := fname
  pname := pname
  nk := 2
  mloc := 1
  mpre := some (.call [9] mf [.var 0, .bin .sub (.var 7) (.const 1), .var 1, .var 2, .var 3])
  mc := .cmp .ne (.var 9) (.const 0)
  np := 3
  room := condOf (lblk (t, o, l, h, j, c) { if len(REC.u64) >> 3 <= c { skip } })
  newRecM := [.const kd, .var 1, .var 2, .var 3]
  ghash := litGS.hash
  ihash := .call [2] "lit_hash" [.var 0, .var 1]
  skipW := none
  mtM m ks t i := mt (m.arr64 REC) (m.arr64 POOL) t i (ks.getD 0 0) (ks.getD 1 0) (ks.getD 2 0)
  qhM m ks := hashN (m.arr64 POOL) (ks.getD 0 0).toNat (ks.getD 1 0).toNat
  hsM := litH
  vsM as := kd :: as
  roomM m _ c := decide (m.len64 REC >>> (3 : Word) ≤ c)
  keyOK := litKeyOK

def litCS : ConsSch := litCSk 0 "lit_match" "lit_find" "lit_push" matchW

/-! ## `lit_find(t, o, l, h)`, `lit_push(t, o, l, h, j)`, `intern_lit(o, l)`

`lit_find` returns `(1, i, j, d)` if node `i` of tier `t` holds the slice (found at slot `j`
after `d` steps), `(0, 0, j, d)` if slot `j` is free; `lit_push` appends a node at the free slot
`lit_find` returned (aborting at `2^27` nodes or a full record array) and grows the table;
`intern_lit` is con-ron's `EStore::intern_lit` (`arena/store.rs:4260`), the arena's
`internE (.lit _)`. The handle is the arena's word: tag `8` (`ETag.lit`) in bits 31…28, the
tier in bit 27, the index below. -/

/-- con-ron: ConRon/Arena/Store.lean:90-91 ConRon.Arena.Tbl.find? -/
def litFind : FunDecl := consFindG litCS

/-- The node count of tier `t`, `CTL[2 + t]`. -/
def cnt (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) (2 + t)

/-- `lit_push`'s room checks: the handle index, the record array. -/
def pushOK (m : Mem) (t : Word) : Bool :=
  decide (cnt m t < (134217728 : Word)) && decide (cnt m t < m.len64 REC >>> (3 : Word))

/-- con-ron: ConRon/Arena/Store.lean:93-98 ConRon.Arena.Tbl.push -/
def litPush : FunDecl := consPushG litCS

/-- The model of `intern_lit`: the handle and the memory after, or `none` where the L code
aborts. `rs₀`, `rs₁`: the two probes (`[]`: the probe aborted). -/
def internW (m : Mem) (o l : Word) : Option (Word × Mem) := consInternM litCS m [o, l]

/-- con-ron: ConRon/Arena/Monad.lean:246-264 ConRon.Arena.internE
con-ron: ConRon/Arena/Monad.lean:218-244 ConRon.Arena.internNodeE -/
@[l_impl ConRon.Arena.internE ConRon.Arena.internNodeE]
def internLit : FunDecl := consInternG litCS

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

def litStrCS : ConsSch := litCSk 1 "lit_match_str" "lit_find_str" "lit_push_str" matchWStr

/-- con-ron: ConRon/Arena/Store.lean:90-91 ConRon.Arena.Tbl.find? -/
def litFindStr : FunDecl := consFindG litStrCS

/-- con-ron: ConRon/Arena/Store.lean:93-98 ConRon.Arena.Tbl.push -/
def litPushStr : FunDecl := consPushG litStrCS

/-- The model of `intern_lit_str`: the handle and the memory after, or `none` where the L code
aborts. Shares the `natVal` arm's handle words (`litP`, `litS`): the two literal kinds cons into
the same table. -/
def internWStr (m : Mem) (o l : Word) : Option (Word × Mem) := consInternM litStrCS m [o, l]

/-- con-ron: ConRon/Arena/Monad.lean:246-264 ConRon.Arena.internE
con-ron: ConRon/Arena/Monad.lean:218-244 ConRon.Arena.internNodeE -/
@[l_impl ConRon.Arena.internE ConRon.Arena.internNodeE]
def internLitStr : FunDecl := consInternG litStrCS

/-- The `strVal` store functions, as one `#eval`-able program. -/
def litProgStr : Prog :=
  [("lit_hash", litHash), ("limbs_eq", limbsEq), ("lit_match_str", litMatchStr),
   ("lit_find_str", litFindStr), ("lit_push_str", litPushStr), ("intern_lit_str", internLitStr)]

/-! ## The specs: the library's, from the table's obligations -/

theorem ite_bneC (b : Bool) : ((if b = true then (1 : Word) else 0) != 0) = b := by
  cases b <;> rfl

theorem dec_le_not_lt (x y : Word) : decide (x ≤ y) = !decide (y < x) := by
  by_cases h : y < x
  · have : ¬ x ≤ y := fun h' => absurd h (UInt64.not_lt.mpr h')
    simp [h, this]
  · have : x ≤ y := UInt64.not_lt.mp h
    simp [h, this]

theorem dec_lt_not_le' (x y : Word) : decide (x < y) = !decide (y ≤ x) := by
  by_cases h : y ≤ x
  · have : ¬ x < y := fun h' => absurd h (UInt64.not_le.mpr h')
    simp [h, this]
  · have : x < y := UInt64.not_le.mp h
    simp [h, this]


section specs
variable (p : Prog)

/-- The growth's hash block computes `litH`. -/
theorem litH_ok : HashOK p litGS 7 litH := by
  intro k s₀
  simp only [litGS, shiftS, shiftE, L.Notation.blk]
  sym only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalArgs, setLoc, ld64] <;> finish [litH, LocEq, St.setLoc]

theorem litCSk_room (kd : Word) (mf fname pname : String)
    (mt : Array Word → Array Word → Word → Word → Word → Word → Word → Bool) :
    RoomOK (litCSk kd mf fname pname mt) := fun s => by
  simp only [litCSk, condOf, Cond.pval, Expr.pval, L.Notation.blk, Cmp.eval, BinOp.eval]; rfl

theorem litCSk_recs (kd : Word) (mf fname pname : String)
    (mt : Array Word → Array Word → Word → Word → Word → Word → Word → Bool) :
    CRecOK (litCSk kd mf fname pname mt) := ⟨by
      intro e he s s' h
      simp only [litCSk, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl <;> simp [Expr.pval, h],
    fun s => by simp [litCSk, argsOf, Expr.pval, List.range_succ]⟩

theorem litCSk_ihash (kd : Word) (mf fname pname : String)
    (mt : Array Word → Array Word → Word → Word → Word → Word → Word → Bool)
    (hph : p.lookup "lit_hash" = some litHash) : IHashOK p (litCSk kd mf fname pname mt) := by
  intro n s₀
  apply triple_pre_and
  rintro ⟨hs, hb⟩
  simp only [litCSk, argsOf, List.range_succ, List.range_zero, List.map, List.nil_append,
    List.cons_append, List.getD_cons_zero, List.getD_cons_succ] at hs hb ⊢
  vcgen [step, evalArgs, evalE, setLocs,
    litHash_spec p hph n s₀ (s₀.loc (0 + 0)) (s₀.loc (1 + 0)) hs hb]
  all_goals simp_all [St.setLocs_cons, St.setLocs_nil, Nat.zero_add]

theorem litOK (hph : p.lookup "lit_hash" = some litHash) (hpe : p.lookup "limbs_eq" = some limbsEq)
    (hpm : p.lookup "lit_match" = some litMatch) : ConsOK p litCS where
  match_ := by
    intro n s₀
    simp only [litCS, litCSk]
    vcgen [step, evalArgs, evalE, setLocs, litMatch_spec p hpe hpm n]
    all_goals simp_all [St.setLocs_cons, St.setLocs_nil, Keep1, Cond.pval, Expr.pval, Cmp.eval,
      BinOp.eval, argsOf, List.range_succ, St.setLoc_loc, St.setLoc_mem]
    all_goals first
      | (intro z hz; simp [St.setLoc_loc, hz])
      | exact ite_bneC _
  ghash := litH_ok p
  ihash := litCSk_ihash p _ _ _ _ _ hph
  pre := rfl
  colA := by simp [litCS, litCSk]
  recs := litCSk_recs _ _ _ _ _
  room := litCSk_room _ _ _ _ _
  skips := by intro e he; simp [litCS, litCSk] at he
  push_np := by decide
  arrs := by decide

theorem litStrOK (hph : p.lookup "lit_hash" = some litHash)
    (hpe : p.lookup "limbs_eq" = some limbsEq)
    (hpm : p.lookup "lit_match_str" = some litMatchStr) : ConsOK p litStrCS where
  match_ := by
    intro n s₀
    simp only [litStrCS, litCSk]
    vcgen [step, evalArgs, evalE, setLocs, litMatchStr_spec p hpe hpm n]
    all_goals simp_all [St.setLocs_cons, St.setLocs_nil, Keep1, Cond.pval, Expr.pval, Cmp.eval,
      BinOp.eval, argsOf, List.range_succ, St.setLoc_loc, St.setLoc_mem]
    all_goals first
      | (intro z hz; simp [St.setLoc_loc, hz])
      | exact ite_bneC _
  ghash := litH_ok p
  ihash := litCSk_ihash p _ _ _ _ _ hph
  pre := rfl
  colA := by simp [litStrCS, litCSk]
  recs := litCSk_recs _ _ _ _ _
  room := litCSk_room _ _ _ _ _
  skips := by intro e he; simp [litStrCS, litCSk] at he
  push_np := by decide
  arrs := by decide

theorem pushOK_eqC (m : Mem) (t : Word) : pushOK m t = pushOKC litCS m t := by
  rw [pushOK, pushOKC, dec_lt_not_le' (cnt m t) (m.len64 REC >>> 3)]; rfl

section kinds
variable (hph : p.lookup "lit_hash" = some litHash) (hpe : p.lookup "limbs_eq" = some limbsEq)

include hph hpe in
include hph hpe in
include hph hpe in
theorem internLit_spec (hpm : p.lookup "lit_match" = some litMatch)
    (hpf : p.lookup "lit_find" = some litFind) (hpp : p.lookup "lit_push" = some litPush)
    (hp : p.lookup "intern_lit" = some internLit) (n : Nat) (s₀ : St) (o l : Word)
    (hs : (s₀.mem.arr64 POOL).size < 2 ^ 64) (hb : o.toNat + l.toNat ≤ (s₀.mem.arr64 POOL).size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_lit" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ internW s₀.mem o l = some (r.headD 0, s'.mem); ⊤⦄ :=
  consInternG_spec p litCS (litOK p hph hpe hpm) hpf hpp "intern_lit" hp n s₀ [o, l] rfl ⟨hs, hb⟩

include hph hpe in
theorem internLitStr_spec (hpm : p.lookup "lit_match_str" = some litMatchStr)
    (hpf : p.lookup "lit_find_str" = some litFindStr) (hpp : p.lookup "lit_push_str" = some litPushStr)
    (hp : p.lookup "intern_lit_str" = some internLitStr) (n : Nat) (s₀ : St) (o l : Word)
    (hs : (s₀.mem.arr64 POOL).size < 2 ^ 64) (hb : o.toNat + l.toNat ≤ (s₀.mem.arr64 POOL).size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_lit_str" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ internWStr s₀.mem o l = some (r.headD 0, s'.mem); ⊤⦄ :=
  consInternG_spec p litStrCS (litStrOK p hph hpe hpm) hpf hpp "intern_lit_str" hp n s₀ [o, l] rfl
    ⟨hs, hb⟩

end kinds

end specs

end L.Arena
