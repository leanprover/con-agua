module

public import ConAgua.Arena.SlotGrow
public import ConAgua.Arena.Pool
public import ConAgua.Arena.Reasons
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.SlotGrow
import ConAgua.Census.Attr

@[expose] public section

/-!
# The cons-table library: one L code for every intern (hash-cons) table (lane conslib)

con-ron's arena keeps each node constructor in a `Tbl α ι δ` per tier: an array of records and a
cons `Std.HashMap` (con-ron's Rust: `HashMap2`, open addressing). Its L twin is the same for every
constructor up to a **cons schema** `ConsSch`: the record array (`w` words per node, one tiered
array per tier as con-ron's: node `i` of tier `t` at `ra⟨t⟩[i * w ..]`), the slot array (one
tiered array per tier, slot `j` a value word, `0` free or `B t + i + 1` node `i`, and a key word; linear probing from
`homeW`; grown by `kgrowB`; the layout below), the node counts at `CTL[ca + t]`, the handle bases, and the table's own pieces as L
fragments: the match of a node against the key, the room test of the push, the record words, the
key hash and the scratch skip of `intern_X`.

The L code is **generic in the schema**: `consFindG C`, `consPushG C`, `consInternG C` are Lean
functions producing the table's `X_find`, `X_push`, `intern_X` (as `MemoLib`'s templates: L names
its arrays statically, so the code cannot take the table as an argument). The table's functions
are instances (`appFind := consFindG appCS`, …) and keep their names and program entries. Their
specs are proved once, for a variable schema, from one obligation per fragment
(`ConsLibSpec.lean`).

Variables. `X_find(t, k₁ … k_nk, h)`: the template's own variables `n j d v b` follow the keys
(`lvF`), then the match's own (`mloc` of them), then `q r x` (`fvF`). `X_push(t, k₁ … k_np, j)`:
`c k` follow, then the column's prelude's (`xloc`), then the growth block's (from `gO`). `intern_X(k₁ … k_nk)`: `h sk fd i j d` follow the keys. A fragment is written
with these numbers (concretely, for its table).
-/

set_option experimental.vcgen true

namespace L.Arena

/-! ## Renaming variables -/

/-- Expression `e` with every variable `x` renamed to `f x`. -/
def mapE (f : Var → Var) : Expr → Expr
  | .var x => .var (f x)
  | .bin op a b => .bin op (mapE f a) (mapE f b)
  | .ld8 a i => .ld8 a (mapE f i)
  | .ld64 a i => .ld64 a (mapE f i)
  | .cmpw c a b => .cmpw c (mapE f a) (mapE f b)
  | .ldc d i => .ldc d (mapE f i)
  | .ld64t a t i => .ld64t a (mapE f t) (mapE f i)
  | .len64t a t => .len64t a (mapE f t)
  | .ld8x8 b i => .ld8x8 b (mapE f i)
  | e => e

/-- A block operand with its tier expression renamed. -/
def mapW (f : Var → Var) : WArr → WArr
  | .plain a => .plain a
  | .tier a t => .tier a (mapE f t)

/-- Renaming commutes with the store-record accessors (`L/TRec.lean`). -/
theorem mapE_tierX (f : Var → Var) (t : Expr) : mapE f (TRec.tierX t) = TRec.tierX (mapE f t) := by
  unfold TRec.tierX
  split
  · simp [mapE]
  · rename_i hne
    split
    · rename_i h heq
      exfalso
      cases t <;> simp only [mapE, reduceCtorEq] at heq
      rename_i op a b
      obtain ⟨rfl, ha, hb⟩ := Expr.bin.inj heq
      cases a <;> simp only [mapE, reduceCtorEq] at ha
      rename_i op' x c
      obtain ⟨rfl, -, hc⟩ := Expr.bin.inj ha
      cases c <;> simp only [mapE, reduceCtorEq, Expr.const.injEq] at hc
      cases b <;> simp only [mapE, reduceCtorEq, Expr.const.injEq] at hb
      subst hc hb
      exact hne x rfl
    · rfl

theorem mapE_exE (f : Var → Var) (R : TRec) (g : Word) (e : Expr) :
    mapE f (R.exE g e) = R.exE g (mapE f e) := by
  unfold TRec.exE
  by_cases h1 : R.hi = 0 <;> by_cases h2 : g = 0 <;> by_cases h3 : g = R.hi <;>
    simp [h1, h2, h3, mapE]

theorem mapE_tld (f : Var → Var) (R : TRec) (t i : Expr) (g : Word) :
    mapE f (R.ld t i g) = R.ld (mapE f t) (mapE f i) g := by
  simp only [TRec.ld, mapE_exE, mapE, mapE_tierX, TRec.adE]; split <;> split <;> simp [mapE]

theorem mapE_cntE (f : Var → Var) (R : TRec) (t : Expr) :
    mapE f (R.cntE t) = R.cntE (mapE f t) := by simp [TRec.cntE, mapE]

theorem mapE_tierE (f : Var → Var) (h : Expr) : mapE f (tierE h) = tierE (mapE f h) := by
  simp [tierE, mapE]

theorem mapE_idxE (f : Var → Var) (h : Expr) : mapE f (idxE h) = idxE (mapE f h) := by
  simp [idxE, mapE]

/-- Condition `c` with every variable renamed by `f`. -/
def mapC (f : Var → Var) : Cond → Cond
  | .cmp c a b => .cmp c (mapE f a) (mapE f b)
  | .and p q => .and (mapC f p) (mapC f q)
  | .or p q => .or (mapC f p) (mapC f q)
  | .not p => .not (mapC f p)

/-- Statement `s` with every variable renamed by `f`. -/
def mapS (f : Var → Var) : Stmt → Stmt
  | .set x e => .set (f x) (mapE f e)
  | .st8 a i e => .st8 a (mapE f i) (mapE f e)
  | .st64 a i e => .st64 a (mapE f i) (mapE f e)
  | .seq s t => .seq (mapS f s) (mapS f t)
  | .ite c s t => .ite (mapC f c) (mapS f s) (mapS f t)
  | .while c s => .while (mapC f c) (mapS f s)
  | .ret es => .ret (es.map (mapE f))
  | .call xs g args => .call (xs.map f) g (args.map (mapE f))
  | .gset g e => .gset g (mapE f e)
  | .st64t a t i e => .st64t a (mapE f t) (mapE f i) (mapE f e)
  | .copy64 d di s si n => .copy64 (mapW f d) (mapE f di) (mapW f s) (mapE f si) (mapE f n)
  | .copy8w d di s si n => .copy8w (mapW f d) (mapE f di) s (mapE f si) (mapE f n)
  | .scan8 x s i e c => .scan8 (f x) s (mapE f i) (mapE f e) c
  | .abort e => .abort (mapE f e)
  | s => s

/-- The template's variable `x` in a function whose first parameter is the tier and whose next
`nk` are the key: variable `0` stays, the others move past the key. -/
def lvF (nk : Nat) (x : Var) : Var := if x = 0 then 0 else x + nk

/-- `s₁; s₂; …; t`, nested to the right as `lfn` writes a block. -/
def seqs : List Stmt → Stmt → Stmt
  | [], t => t
  | s :: ss, t => .seq s (seqs ss t)

/-- `s; t`, or `t` when there is no `s`. -/
def seqO : Option Stmt → Stmt → Stmt
  | none, t => t
  | some s, t => .seq s t

/-- The condition of an `if` (to write a fragment's condition with `lblk`). -/
def condOf : Stmt → Cond
  | .ite c _ _ => c
  | _ => .cmp .eq (.const 0) (.const 0)

/-- The right-hand side of an assignment (to write a fragment's expression with `lblk`). -/
def rhsOf : Stmt → Expr
  | .set _ e => e
  | _ => .const 0

/-! ## The schema -/

/-- A cons table. Arrays and words: record array `ra`, slot array `sa`, `w` words per record (in
tier `t`'s array `ra⟨t⟩`), node counts at `CTL[ca + t]`, handle words `P + i` (persistent tier) and
`S + i` (scratch tier). Functions: `fname`, `pname` (the find and the push `intern_X` calls).
Fragments (in the variables of the module doc):
* `nk` key words; the find's match: `mpre` (a prelude, e.g. `m := call X_match(…)`, with `mloc`
  locals of its own after `b`) and the condition `mc` on node `v - 1`;
* `np` record inputs of the push (the key, and for some tables the hash), the room test `room`
  (the push aborts if it holds), the record words `rec`;
* `ihash`: `h :=` the key's hash, in `intern_X`; `skip`: the scratch-skip word (`some`: the
  persistent probe is skipped when the scratch tier is open and the word is not `0`). -/
structure ConsSch where
  ra : ArrId
  sa : ArrId
  w : Word
  ca : Word
  P : Word
  S : Word
  /-- The handle tag (`P = tag · 2^28`, `S = P + 2^27`). -/
  tag : UInt32
  fname : String
  pname : String
  nk : Nat
  mloc : Nat := 0
  mpre : Option Stmt := none
  mc : Cond
  np : Nat
  room : Cond
  recW : List Expr
  ihash : Stmt
  skipW : Option Expr
  /-- Models (`ConsLibSpec.lean` states each fragment's obligation against them): the match of
  node `i` of tier `t` against the key, the key's hash, a node's hash (the growth's), the record
  words from the push's inputs, the room test from the count, the skip word from the key. -/
  mtM : Mem → List Word → Word → Word → Bool
  qhM : Mem → List Word → Word
  hsM : Mem → Word → Word → Word
  vsM : List Word → List Word
  roomM : Mem → Word → Word → Bool
  skM : List Word → Word := fun _ => 0
  /-- A derived column written by the push (`col[2 c + t] := x`), its value `x` (variable
  `4 + np`) computed by the prelude `pre` with `xloc` locals of its own, and its model `colM`
  (from the push's inputs). -/
  xloc : Nat := 0
  pre : Option Stmt := none
  col : Option ArrId := none
  colM : Mem → List Word → Word := fun _ _ => 0
  /-- What the find's match and `ihash` may assume of the key (e.g. a pool slice in bounds). -/
  keyOK : Mem → List Word → Prop := fun _ _ => True
  /-- The slot's key word is the key itself (`nk ≤ 2`, a two-word key's words below `2^32`,
  which `intern_X` checks): a probe compares it and reads no record. -/
  exact : Bool := false
  /-- A packed record (lane memlay): the two key words share record word `0` (the first in bits
  0–31, the second in bits 32–63). -/
  kpk : Bool := false

/-! ## The slot layout (KSTP)

Each tier has its own slot array `sa⟨t⟩` (lane tierswitch; con-ron's per-tier tables). Its words
`0` and `1` hold `n - SN0` (`n` the slot count, a multiple of 8) and `o`, the table's offset (`0`:
nothing writes it); the table starts at word `r = 2 + o`. Slot `j` is the two words `r + 2 j` (the
value: `0` free, `B t + i + 1` node `i`) and `r + 2 j + 1` (the key word). The table grows at load
3/4 (con-ron's `HashMap2`) and **in place** (lane memlay): it doubles where it is (`kgrowB`), so no
old copy of it stays resident, and the growth aborts if the array cannot hold the doubled table.
A fresh array (all zero) is a table of `SN0` slots at offset `0`: a small run touches only the
array's first words.

The key word (`kwE`): for an `exact` table the key itself (no key word: `0`; one: the word; two:
`k₁ | k₂ << 32`, both below `2^32`), so a probe that meets it has found the node and reads no
record; otherwise the key's hash, a fingerprint: only a slot with the same hash runs the match. -/

/-- The key word of a find (`t`, key `1 ‥ nk`, hash `1 + nk`). -/
def kwE (C : ConsSch) : Expr :=
  if C.exact then
    match C.nk with
    | 0 => .const 0
    | 1 => .var 1
    | _ => .bin .or (.var 1) (.bin .shl (.var 2) (.const 32))
  else .var (1 + C.nk)

/-! ## `X_find(t, k₁ … k_nk, h)`: the probe -/

/-- The template's find variables `t h n j d v b` (`lvF`), then, past the match's own locals,
`q r x` (the key word, the region's first word, the probed slot's first word). -/
def fvF (C : ConsSch) (x : Var) : Var :=
  if x = 0 then 0 else if x < 7 then x + C.nk else x + C.nk + C.mloc

def kfHead (sa : ArrId) : Stmt := lblk (t, h, n, j, d, v, b, q, r, x) {
  n := sa⟨t⟩[0] + ⟪SN0⟫;
  x := sa⟨t⟩[1];
  r := x + 2;
  b := CTL.u64[62] * t;
  j := mulhi((h * ⟪golden⟫) ^ ((h * ⟪golden⟫) >> 32), n)
}
def kfLoad (sa : ArrId) : Stmt := lblk (t, h, n, j, d, v, b, q, r, x) {
  x := r + j * 2;
  v := sa⟨t⟩[x];
  if v <= b { return (0, 0, j, d) };
  v := v - b
}
def kfKey (sa : ArrId) : Cond :=
  condOf (lblk (t, h, n, j, d, v, b, q, r, x) { if sa⟨t⟩[x + 1] == q { skip } })
def cfHit : Stmt := lblk (t, h, n, j, d, v, b) { return (1, v - 1, j, d) }
def cfAdv : Stmt := lblk (t, h, n, j, d, v, b) {
  j := (j + 1) * u64(j + 1 < n);
  d += 1
}

/-- The match of a slot whose key word is the key's: the hit (exact), or the instance's match. -/
def kfMatch (C : ConsSch) : Stmt :=
  if C.exact then mapS (lvF C.nk) cfHit
  else seqO C.mpre (.ite C.mc (mapS (lvF C.nk) cfHit) .skip)

/-- The probe loop. -/
def cfLoop (C : ConsSch) : Stmt :=
  .while (.cmp .ult (.var (4 + C.nk)) (.var (2 + C.nk)))
    (.seq (mapS (fvF C) (kfLoad C.sa))
      (.seq (.ite (mapC (fvF C) (kfKey C.sa)) (kfMatch C) .skip) (mapS (lvF C.nk) cfAdv)))

/-- con-ron: ConRon/Arena/Store.lean:90-91 ConRon.Arena.Tbl.find? -/
def consFindG (C : ConsSch) : FunDecl :=
  { nparams := 2 + C.nk, nlocals := 10 + C.nk + C.mloc,
    body := .seq (mapS (fvF C) (kfHead C.sa))
      (.seq (.set (7 + C.nk + C.mloc) (kwE C)) (.seq (cfLoop C) (.abort (.const 0)))) }

/-! ## `X_push(t, k₁ … k_np, j)`: append a node to tier `t`, register it at slot `j` -/

/-- The first variable of the push's growth block. -/
def gO (C : ConsSch) : Nat := 4 + C.xloc + C.np

/-- The template's push variables `t j c k`. -/
def cpHead (C : ConsSch) : List Stmt :=
  [lblk (t, j, c, k) { c := CTL.u64[⟪C.ca⟫ + t] },
   lblk (t, j, c, k) { if c >= 134217728 { abort } }]
def cpMid (C : ConsSch) : List Stmt :=
  [mapS (lvF C.np) (if C.w = 1 then lblk (t, j, c, k) { k := c } else lblk (t, j, c, k) { k := c * ⟪C.w⟫ }),
   .set (gO C + 1) (.ld64t C.sa (.var 0) (.const 0))]

/-- The record words: word `f` of the new record is `e` (`k` = `np + 3`). -/
def cpWr (C : ConsSch) : Nat → List Expr → Stmt → Stmt
  | _, [], t => t
  | f, e :: es, t =>
    .seq (.st64t C.ra (.var 0) (if f = 0 then .var (3 + C.np) else .bin .add (.var (3 + C.np)) (.const (UInt64.ofNat f))) e)
      (cpWr C (f + 1) es t)

/-- The key's hash recomputed by `ihash` in a block of `nk + 1` variables from `o` (the key words
`o ‥ o + nk - 1`, the hash at `o + nk`). -/
def ihashAt (C : ConsSch) (o : Nat) : Stmt := shiftS o C.ihash

/-- `q :=` the key word, in the push (`q` at `gO + 2`; the key is the push's inputs `1 ‥ nk`,
the hash input `1 + nk` if the record stores it, else recomputed from the key). -/
def cpKey (C : ConsSch) : Stmt :=
  if C.exact then .set (gO C + 2) (kwE C)
  else if C.nk < C.np then .set (gO C + 2) (.var (1 + C.nk))
  else seqs ((List.range C.nk).map fun i => .set (gO C + 14 + i) (.var (1 + i)))
    (.seq (ihashAt C (gO C + 14)) (.set (gO C + 2) (.var (gO C + 14 + C.nk))))

/-- The slot write: value and key word at slot `j` of tier `t`'s table (`r` at `gO + 3`; the slot
count's word `g` at `gO + 1`). -/
def cpSlot (C : ConsSch) : Stmt :=
  mapS (fun x => if x < 4 then (lvF C.np x) else gO C + (x - 3))
    (lblk (t, j, c, k, g, q, r) {
      r := C.sa⟨t⟩[1] + 2;
      C.sa⟨t⟩[r + j * 2] := CTL.u64[62] * t + c + 1;
      C.sa⟨t⟩[r + j * 2 + 1] := q })

def cpCnt (C : ConsSch) : Stmt :=
  mapS (lvF C.np) (lblk (t, j, c, k) { CTL.u64[⟪C.ca⟫ + (t & 1)] := c + 1 })

/-! ### The growth (in place, the pushing tier only) -/

/-- The growth's hash of the key word `q`: `q` itself (fingerprint), or `ihash` of the key
unpacked from it (exact). Template variables as `kgrowB`; the `ihash` block at `15`. -/
def khashB (C : ConsSch) : Stmt :=
  if C.exact then
    seqs ((match C.nk with
      | 0 => []
      | 1 => [.set 15 (.var 10)]
      | _ => [.set 15 (.bin .and (.var 10) (.const 4294967295)),
              .set 16 (.bin .shr (.var 10) (.const 32))]))
      (.seq (ihashAt C 15) (.set 11 (.var (15 + C.nk))))
  else .set 11 (.var 10)

/-- The zero loop of slot array `sa`: `e` steps of eight zero words from `x` of tier `t`.
Template variables `t n2 n H Q ob nb x e v q h j d bt` (`kgrowB`; also `scratch_reset`'s wrap,
`Scratch.lean`). -/
def kzeroLs (sa : ArrId) : Stmt := lblk (t, n2, n, H, Q, ob, nb, x, e, v, q, h, j, d, bt) {
  while e != 0 {
    sa⟨t⟩[x] := 0; sa⟨t⟩[x + 1] := 0; sa⟨t⟩[x + 2] := 0; sa⟨t⟩[x + 3] := 0;
    sa⟨t⟩[x + 4] := 0; sa⟨t⟩[x + 5] := 0; sa⟨t⟩[x + 6] := 0; sa⟨t⟩[x + 7] := 0;
    x += 8;
    e -= 1
  }
}

/-- The zero loop of the growth (`kzeroLs` of the table's slot array). -/
def kzeroL (C : ConsSch) : Stmt := kzeroLs C.sa

/-- The growth's head: the slot count `n`, the doubled `n2`, the table's first word `ob` (`nb`
the offset), the room `Q`. -/
def kgrowH1 (C : ConsSch) : Stmt := lblk (t, n2, n, H, Q, ob, nb, x, e, v, q, h, j, d, bt) {
  n := C.sa⟨t⟩[0] + ⟪SN0⟫;
  n2 := n * 2;
  nb := C.sa⟨t⟩[1];
  ob := nb + 2;
  Q := len(C.sa⟨t⟩) - 2
}

/-- The room check (the doubled table in place) and the new count word. -/
def kgrowH2 (C : ConsSch) : Stmt := lblk (t, n2, n, H, Q, ob, nb, x, e, v, q, h, j, d, bt) {
  if Q < nb + n2 * 2 { abort };
  C.sa⟨t⟩[0] := n2 - ⟪SN0⟫
}

/-- The zero loop's start (the new upper half, `2 n` words after the old table) and count. -/
def kgrowH3 : Stmt := lblk (t, n2, n, H, Q, ob, nb, x, e, v, q, h, j, d, bt) {
  x := ob + n * 2;
  e := n >> 2
}

/-- The mark loop's start and count, and the slot base `bt`. -/
def kgrowH4 : Stmt := lblk (t, n2, n, H, Q, ob, nb, x, e, v, q, h, j, d, bt) {
  bt := CTL.u64[62] * t;
  x := ob;
  e := n
}

/-- The mark loop: each live slot of the old half (`e` slots from word `x`) gets the mark. -/
def kmarkL (C : ConsSch) : Stmt := lblk (t, n2, n, H, Q, ob, nb, x, e, v, q, h, j, d, bt) {
  while e != 0 {
    v := C.sa⟨t⟩[x];
    if bt < v { C.sa⟨t⟩[x] := v + ⟪MARK⟫ };
    x += 2;
    e -= 1
  }
}

/-- The re-insertion's start: slot `H = 0`, and the budget `e = n` of re-insertions (each one
unmarks a slot, and only the `n` old slots carry marks). -/
def kgrowH5 : Stmt := lblk (t, n2, n, H, Q, ob, nb, x, e, v, q, h, j, d, bt) {
  H := 0;
  e := n
}

/-- Take the marked entry in slot `H` (value `v`): spend one of the budget, unmark it, hash its
key word `q`, and start the probe at the home of the hash in the doubled table. -/
def kpickB (C : ConsSch) : Stmt := lblk (t, n2, n, H, Q, ob, nb, x, e, v, q, h, j, d, bt) {
  if e == 0 { abort };
  e -= 1;
  v := v - ⟪MARK⟫;
  q := C.sa⟨t⟩[ob + H * 2 + 1];
  ⟪khashB C⟫;
  j := mulhi((h * ⟪golden⟫) ^ ((h * ⟪golden⟫) >> 32), n2);
  d := 0
}

/-- The probe: past the live unmarked slots, to slot `H` itself, a free slot or a marked one
(aborting after `n2` steps). -/
def kprobeL (C : ConsSch) : Stmt := lblk (t, n2, n, H, Q, ob, nb, x, e, v, q, h, j, d, bt) {
  while j != H && bt < C.sa⟨t⟩[ob + j * 2] && C.sa⟨t⟩[ob + j * 2] < ⟪MARK⟫ {
    if d >= n2 { abort };
    j := (j + 1) * u64(j + 1 < n2);
    d += 1
  }
}

/-- Place the entry at slot `j`: at `H` itself it stays; at a free slot it moves there and `H`
becomes free; at a marked slot the two swap, and the displaced marked entry is next (`v`). -/
def kplaceB (C : ConsSch) : Stmt := lblk (t, n2, n, H, Q, ob, nb, x, e, v, q, h, j, d, bt) {
  if j == H {
    C.sa⟨t⟩[ob + H * 2] := v;
    v := 0
  } else {
    nb := C.sa⟨t⟩[ob + j * 2];
    x := C.sa⟨t⟩[ob + j * 2 + 1];
    C.sa⟨t⟩[ob + j * 2] := v;
    C.sa⟨t⟩[ob + j * 2 + 1] := q;
    if ⟪MARK⟫ <= nb {
      C.sa⟨t⟩[ob + H * 2] := nb;
      C.sa⟨t⟩[ob + H * 2 + 1] := x;
      v := nb
    } else {
      C.sa⟨t⟩[ob + H * 2] := 0;
      v := 0
    }
  }
}

/-- The re-insertions of the entry in slot `H` and of the marked entries it displaces. -/
def kinnerL (C : ConsSch) : Stmt := lblk (t, n2, n, H, Q, ob, nb, x, e, v, q, h, j, d, bt) {
  while ⟪MARK⟫ <= v {
    ⟪kpickB C⟫;
    ⟪kprobeL C⟫;
    ⟪kplaceB C⟫
  }
}

/-- The re-insertion loop over the old half's slots `H = 0 ‥ n - 1`. -/
def krehashL (C : ConsSch) : Stmt := lblk (t, n2, n, H, Q, ob, nb, x, e, v, q, h, j, d, bt) {
  while H < n {
    v := C.sa⟨t⟩[ob + H * 2];
    ⟪kinnerL C⟫;
    H += 1
  }
}

/-- The growth's head. -/
def kgrowH (C : ConsSch) : Stmt := lblk (t, n2, n, H, Q, ob, nb, x, e, v, q, h, j, d, bt) {
  ⟪kgrowH1 C⟫;
  ⟪kgrowH2 C⟫;
  ⟪kgrowH3⟫
}

/-- **The growth of tier `t`, in place** (con-ron's `HashMap2::try_resize` doubles into a new
table and frees the old one; here the table doubles where it is, so no old copy stays resident):
the slot count doubles, the new upper half is zeroed, every live slot of the old half is marked,
then each marked entry is re-inserted from its home in the doubled table (linear probing past
the live unmarked slots; a marked slot met on the way is swapped and re-inserted next: absl's
in-place rehash). Aborts if the array cannot hold the doubled table. Template variables
`t n2 n H Q ob nb x e v q h j d bt` (`t` the push's tier, the others from `gO`). -/
def kgrowB (C : ConsSch) : Stmt := lblk (t, n2, n, H, Q, ob, nb, x, e, v, q, h, j, d, bt) {
  ⟪kgrowH C⟫;
  ⟪kzeroL C⟫;
  ⟪kgrowH4⟫;
  ⟪kmarkL C⟫;
  ⟪kgrowH5⟫;
  ⟪krehashL C⟫
}

/-- The renaming of the growth's template variables into the push's: `t` stays, the others
from `gO` on. -/
def gmap (C : ConsSch) (x : Var) : Var := if x = 0 then 0 else gO C + (x - 1)

/-- The growth block, its variables from `gO` on (`t` stays the push's tier). -/
def kgrowBlk (C : ConsSch) : Stmt := mapS (gmap C) (kgrowB C)

/-- The growth test: the tier grows when its node count `c + 1` passes 3/4 of its slot count
`g + SN0` (`(g + SN0) * 3 < (c + 1) * 4`; con-ron's `HashMap2` load factor `LOAD_NUM/LOAD_DEN`). -/
def cpGrowIf (C : ConsSch) : Stmt :=
  .ite (.cmp .ult (.bin .mul (.bin .add (.var (gO C + 1)) (.const SN0)) (.const 3))
      (.bin .mul (.bin .add (.var (2 + C.np)) (.const 1)) (.const 4)))
    (kgrowBlk C) .skip

/-- The derived column's write, `col⟨t⟩[c] := x`. -/
def cpColW (C : ConsSch) : Option Stmt :=
  C.col.map fun A => .st64t A (.var 0) (.var (2 + C.np)) (.var (4 + C.np))

/-- The push's tail: the key word, the slot, the count, the column, the growth, the return. -/
def cpRest (C : ConsSch) : Stmt :=
  seqs [cpKey C, cpSlot C, cpCnt C]
    (seqO (cpColW C) (.seq (cpGrowIf C) (.ret [.var (2 + C.np)])))

/-- con-ron: ConRon/Arena/Store.lean:93-98 ConRon.Arena.Tbl.push -/
def consPushG (C : ConsSch) : FunDecl :=
  { nparams := 2 + C.np, nlocals := gO C + 15 + C.nk,
    body := seqO C.pre (seqs ((cpHead C).map (mapS (lvF C.np)))
      (.seq (.ite C.room (.abort (.const R_CAP_STORE)) .skip)
        (seqs (cpMid C) (cpWr C 0 C.recW (cpRest C))))) }

/-! ## `intern_X(k₁ … k_nk)`: hash-cons the node with key `k`

con-ron's `EStore::intern` (the arena's `internE`/`internNodeE`): the persistent probe unless the
scratch tier is open and the skip word is not `0`, the scratch probe if the scratch tier is open,
the append to the tier the store is in. -/

/-- The key's variables, then `extra`. -/
def keyArgs (nk : Nat) (extra : List Expr) : List Expr := (List.range nk).map .var ++ extra

/-- `(fd, i, j, d) := call X_find(t, k…, h)`. -/
def ciFind (C : ConsSch) (t : Word) : Stmt :=
  .call [2 + C.nk, 3 + C.nk, 4 + C.nk, 5 + C.nk] C.fname (.const t :: keyArgs C.nk [.var C.nk])

/-- The hash as a push input, if the record stores it. -/
def hOpt (C : ConsSch) : List Expr := if C.nk < C.np then [.var C.nk] else []

/-- `i := call X_push(t, k…, j)` (the push's record inputs: the key, then `h` if `np > nk`). -/
def ciPush (C : ConsSch) (t : Word) : Stmt :=
  .call [3 + C.nk] C.pname
    (.const t :: keyArgs C.nk (hOpt C ++ [.var (4 + C.nk)]))

/-- `if fd != 0 { return B + i }`. -/
def ciHit (C : ConsSch) (B : Word) : Stmt :=
  .ite (.cmp .ne (.var (2 + C.nk)) (.const 0)) (.ret [.bin .add (.const B) (.var (3 + C.nk))]) .skip

/-- `CTL.u64[1] != 0`: the scratch tier is open. -/
def ciOpen : Cond := .cmp .ne (.ld64 CTL (.const 1)) (.const 0)

/-- The scratch branch: probe tier 1, else append to it. -/
def ciScr (C : ConsSch) : Stmt :=
  .ite ciOpen
    (seqs [ciFind C 1, ciHit C C.S, ciPush C 1] (.ret [.bin .add (.const C.S) (.var (3 + C.nk))]))
    .skip

/-- The persistent branch's end: append to tier 0. -/
def ciEnd (C : ConsSch) : Stmt :=
  .seq (ciPush C 0) (.ret [.bin .add (.const C.P) (.var (3 + C.nk))])

/-- An exact two-word key: abort unless both words are below `2^32` (the key word packs them). -/
def ciChk (C : ConsSch) : List Stmt :=
  if C.exact ∧ C.nk = 2 then
    [.ite (.cmp .ne (.bin .shr (.bin .or (.var 0) (.var 1)) (.const 32)) (.const 0)) (.abort (.const R_CAP_KEY)) .skip]
  else []

/-- con-ron: ConRon/Arena/Monad.lean:246-264 ConRon.Arena.internE
con-ron: ConRon/Arena/Monad.lean:218-244 ConRon.Arena.internNodeE -/
def consInternG (C : ConsSch) : FunDecl :=
  match C.skipW with
  | some sk =>
    { nparams := C.nk, nlocals := 6 + C.nk,
      body := seqs (C.ihash :: ciChk C ++ [.set (1 + C.nk) (.const 0), .ite ciOpen (.set (1 + C.nk) sk) .skip,
        .ite (.cmp .eq (.var (1 + C.nk)) (.const 0)) (.seq (ciFind C 0) (ciHit C C.P)) .skip,
        ciScr C]) (ciEnd C) }
  | none =>
    { nparams := C.nk, nlocals := 6 + C.nk,
      body := seqs (C.ihash :: ciChk C ++ [ciFind C 0, ciHit C C.P, ciScr C]) (ciEnd C) }

end L.Arena
