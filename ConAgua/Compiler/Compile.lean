module

public import ConAgua.L.DefAssign
public import ConAgua.Compiler.Bce

@[expose] public section

/-!
# The compiler from L: descriptor table and target-independent helpers

See DESIGN.md, "The compiler". One pass: an expression is evaluated straight into its target
register by `gen`, with scratch registers; where `gen` does not apply, into `rax` with
intermediate values in fixed per-frame temporary slots (`compileE`).

**Machine state during L code.**
* `r15` = `T`, the address of the run's descriptor table (`Tab`); pinned.
* `r14` = the fuel counter; decremented at every loop back-edge and every call.
* `rsp` = the current frame; constant while a body runs. Local `x` is the word at `rsp + 8x`,
  temporary `t` is at `rsp + 8(nlocals + t)`. The frame has `frameWords` words.
* `rbp` = the trampoline's saved stack pointer; never written by L code.
* `rbx`, `r12`, `r13`: free; the trampoline saves and restores them for its caller.
* `rax` = expression result, `rcx`/`rdx` = scratch, `rsi` = argument pointer at a call.

**Exits.** `ca_error`, `ca_abort` and `ca_exhausted` are global; they restore the caller's `rsp`
from `rbp` and return to the harness with `rdx` = 2, 2 resp. 1. `ca_abort` is an error whose code
(`Err.code`) is in `rbx` (`abort e`, `if c abort k`: `if c abort k` sets `rbx` before the test
and keeps its one conditional jump; the test itself keeps `rbx`), `ca_error` one with code `0` (a
bounds check, a bare `abort`); both return the code in `rax`. `abort e` may overwrite any
register, a leaf's locals in `rbx` included (nothing after an abort reads a local), but `if c abort
k` writes `rbx` also when it does not abort: it does so only where no local lives in `rbx`
(`Ctx.rbxFree`, `sim_ifAbortK`); in a leaf that keeps a local there it is the general `if`. A
normal return has `rdx` = 0 and the result in `rax`.
-/

namespace L.Compiler

/-! ## The layout map

L's arrays are names, in one name space: a byte array `a` (an `ArrId`) or a word array (a
`TieredArray`), never both under one number; a byte array has the key of `↑a`. The compiler alone
maps each name a program may use to a **descriptor position**, one position space for both kinds
with an element kind per position: positions `[0, nb)` hold byte arrays, `[nb, nb + nw)` word
arrays, and a tiered array's tier 1 is right after its tier 0 (a tiered access is one indexed
load). The map is a search tree keyed by `TieredArray.code` (`Tab.lmap`), stored with its inverse
(`Tab.arrAt`, the array at each position); the table carries the proof that the two agree
(`Tab.layOk`, a `Bool` check of the literal). The simulation relation (`MemRel`) relates L's
arrays to the machine's regions through this map, and nothing above the compiler sees a position:
the definitions are irreducible past their lemmas (`Tab.pos64_lt`, `Tab.pos64_ne`,
`Tab.pos64_tierA`, …). -/

/-- Binary search tree: a number (a name code, an array code) ↦ a number. -/
inductive NTree where
  | leaf
  | node (l : NTree) (k v : Nat) (r : NTree)
  deriving Repr, Inhabited, DecidableEq

def NTree.find (k : Nat) : NTree → Option Nat
  | .leaf => none
  | .node l k' v r => if k < k' then find k l else if k = k' then some v else find k r

/-- Insert `k ↦ v`; `none` if `k` is there already. -/
def NTree.insert (k v : Nat) : NTree → Option NTree
  | .leaf => some (.node .leaf k v .leaf)
  | .node l k' v' r =>
    if k < k' then (insert k v l).map (.node · k' v' r)
    else if k = k' then none
    else (insert k v r).map (.node l k' v' ·)

/-- Every entry of the tree satisfies `f`. -/
def NTree.all (f : Nat → Nat → Bool) : NTree → Bool
  | .leaf => true
  | .node l k v r => NTree.all f l && f k v && NTree.all f r

/-- What `find` finds is an entry. -/
theorem NTree.all_find {f : Nat → Nat → Bool} : ∀ {t : NTree} {k v : Nat}, t.all f = true →
    t.find k = some v → f k v = true
  | .leaf, _, _, _, h => by simp [NTree.find] at h
  | .node l k' v' r, k, v, ha, h => by
    simp only [NTree.all, Bool.and_eq_true] at ha
    simp only [NTree.find] at h
    split at h
    · exact NTree.all_find ha.1.1 h
    · split at h
      · rename_i e; cases h; rw [e]; exact ha.1.2
      · exact NTree.all_find ha.2 h

/-- The balanced tree of the entries `a[lo, hi)`, sorted by key. -/
def NTree.ofSorted (a : Array (Nat × Nat)) (lo hi : Nat) : NTree :=
  if lo < hi then
    let m := (lo + hi) / 2
    .node (ofSorted a lo m) a[m]!.1 a[m]!.2 (ofSorted a (m + 1) hi)
  else .leaf
termination_by hi - lo

/-- The array at position `i` of the position list `l` (tier 0 of array `0` past its end). -/
def arrAtD (l : List TieredArray) (i : Nat) : TieredArray := l.getD i ⟨0, false⟩

/-- **The layout check**: `l` lists the array at each of the `nb + nw` positions, `m` maps each of
them to its position and nothing else (an entry `k ↦ v` has `v` in range and `l[v]` of code `k`),
the byte positions `[0, nb)` hold tier-0 names, and a tier 1 sits at a word position right after
its tier 0. -/
def layOkB (nb nw : Nat) (l : List TieredArray) (m : NTree) : Bool :=
  l.length == nb + nw &&
  m.all (fun k v => decide (v < nb + nw) && (l[v]?.map TieredArray.code == some k)) &&
  (List.range (nb + nw)).all (fun i => m.find (arrAtD l i).code == some i) &&
  (List.range nb).all (fun i => !(arrAtD l i).hi) &&
  (List.range (nb + nw)).all (fun i => !(arrAtD l i).hi ||
    (decide (nb < i) && arrAtD l (i - 1) == TieredArray.t0 (arrAtD l i).arr))

/-- The number of result registers. -/
def maxRes : Nat := 6

/-- The layout of the descriptor table at `T`:
* `[T]` the initial stack pointer (top of the stack region), `[T + 8]` its lower limit;
* `[T + 16 + 8p]` the base of the array at descriptor position `p < nb + nw` (`Tab.dbase`), then
  `[T + 16 + 8 (nb + nw) + 8p]` its length (`Tab.dlen`), in bytes for a byte position (`p < nb`),
  in words for a word position, then `[T + 16 + 16 (nb + nw) + 8p]` a word position's length in
  32-bit elements (`Tab.dlen32`, twice its length in words: the bound of a 32-bit access);
* then the constant data `rom` (the byte strings of the program's `ldc` reads), padded to whole
  words;
* then the result area: results `maxRes, maxRes + 1, …, nres - 1` of a call, one word each (empty
  if `nres ≤ maxRes`);
* then the global variables `0, …, ng - 1`, one word each;
* then the arguments of the entry function, one word each.

(`nres` is not part of the table in memory: it says how many results the code passes.) -/
structure Tab where
  /-- The byte positions `[0, nb)`. -/
  nb : Nat
  /-- The word positions `[nb, nb + nw)`. -/
  nw : Nat
  /-- The array at each position (`Tab.wAt`; a byte array `a` as `↑a`). -/
  arrAt : List TieredArray
  /-- The layout map: `s.code ↦` the position of `s` (`Tab.pos64`, `Tab.pos8`). -/
  lmap : NTree
  /-- The map and the position list agree (`layOkB`). -/
  layOk : layOkB nb nw arrAt lmap = true
  rom : List UInt8 := []
  /-- The number of results in use: the most results any `return` gives or any call reads. The
  first `maxRes` go in registers (`resReg 0`, …), the rest in the table's result area. -/
  nres : Nat := 1
  /-- The number of global variables: global `g` (with `g.id < ng`) is the word at `globOff g`. -/
  ng : Nat := 0
  /-- Minimum lengths (`L.ArrDecl.min`): `(s.code, k)` says that word array `s` has at
  least `k` words in every layout the code runs in (`Layout.Ok.min64`; the entry stubs establish
  it), so a constant index below `k` needs no bounds check (`Tab.min64`). -/
  mins : List (Nat × Nat) := []
  /-- The table-relative array (`L.ArrDecl.atTable`): `(a, c)` says that tier 0 of word array `a`
  starts at `T + c`, past the table and the trampoline's save area, in every layout the code runs in
  (`Layout.Ok.tbl64`; the entry stubs place it there), so the code addresses it from `r15` without
  loading its base. -/
  tbl : Option (ArrId × Nat) := none
  /-- `rom.length`, stored: the offsets past the constant data (`resOff`, `globOff`, `args`) are
  then arithmetic on the table's fields, and the kernel does not count the bytes of a large ROM
  each time it evaluates the code generator (DESIGN.md, "Kernel-checked compiler output"). -/
  romLen : Nat := rom.length
  romLen_eq : romLen = rom.length := by rfl
  deriving Repr, DecidableEq

def Tab.stackTop : Int := 0
def Tab.stackLimit : Int := 8

/-- The array at position `p`. -/
def Tab.wAt (t : Tab) (p : Nat) : TieredArray := arrAtD t.arrAt p

/-- The element width of position `p`: a byte position `1`, a word position `8`. -/
def Tab.wd (t : Tab) (p : Nat) : Nat := if p < t.nb then 1 else 8

/-- The byte arrays a program may name (a byte position), and their positions. -/
def Tab.dom8 (t : Tab) (a : ArrId) : Bool :=
  match t.lmap.find (TieredArray.t0 a).code with
  | some p => decide (p < t.nb)
  | none => false
def Tab.pos8 (t : Tab) (a : ArrId) : Nat := (t.lmap.find (TieredArray.t0 a).code).getD 0

/-- The word arrays a program may name (a word position), and their positions. -/
def Tab.dom64 (t : Tab) (s : TieredArray) : Bool :=
  match t.lmap.find s.code with
  | some p => decide (t.nb ≤ p)
  | none => false
def Tab.pos64 (t : Tab) (s : TieredArray) : Nat := (t.lmap.find s.code).getD 0

section
variable (t : Tab)

theorem Tab.layOk_spec : t.arrAt.length = t.nb + t.nw ∧
    t.lmap.all (fun k v => decide (v < t.nb + t.nw) && (t.arrAt[v]?.map TieredArray.code == some k)) = true ∧
    (List.range (t.nb + t.nw)).all (fun i => t.lmap.find (arrAtD t.arrAt i).code == some i) = true ∧
    (List.range t.nb).all (fun i => !(arrAtD t.arrAt i).hi) = true ∧
    (List.range (t.nb + t.nw)).all (fun i => !(arrAtD t.arrAt i).hi ||
      (decide (t.nb < i) && arrAtD t.arrAt (i - 1) == TieredArray.t0 (arrAtD t.arrAt i).arr)) = true := by
  have h := t.layOk
  simp only [layOkB, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- An entry of the map: a position, holding the array of that code. -/
theorem Tab.find_some {k v : Nat} (h : t.lmap.find k = some v) : v < t.nb + t.nw ∧ (t.wAt v).code = k := by
  have := NTree.all_find t.layOk_spec.2.1 h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
  refine ⟨this.1, ?_⟩
  obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.mp this.2
  simp only [Tab.wAt, arrAtD, List.getD_eq_getElem?_getD, hx, Option.getD_some, e]

/-- The array at a position is found there. -/
theorem Tab.find_wAt {p : Nat} (hp : p < t.nb + t.nw) : t.lmap.find (t.wAt p).code = some p := by
  have := t.layOk_spec.2.2.1
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at this
  exact this p hp

theorem Tab.wAt_byte {p : Nat} (hp : p < t.nb) : (t.wAt p).hi = false := by
  have := t.layOk_spec.2.2.2.1
  simp only [List.all_eq_true, List.mem_range, Bool.not_eq_true'] at this
  exact this p hp

theorem Tab.wAt_tier {p : Nat} (hp : p < t.nb + t.nw) (h : (t.wAt p).hi = true) :
    t.nb < p ∧ t.wAt (p - 1) = TieredArray.t0 (t.wAt p).arr := by
  have := t.layOk_spec.2.2.2.2
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at this
  rcases this p hp with h' | h'
  · simp only [Tab.wAt] at h; rw [h] at h'; cases h'
  · exact h'

theorem Tab.find_code {s : TieredArray} {p : Nat} (h : t.lmap.find s.code = some p) : t.wAt p = s :=
  TieredArray.code_inj.mp (t.find_some h).2

theorem Tab.dom64_find {s : TieredArray} (h : t.dom64 s = true) :
    ∃ p, t.lmap.find s.code = some p ∧ t.nb ≤ p := by
  unfold Tab.dom64 at h
  split at h
  · rename_i p e; exact ⟨p, e, by simpa using h⟩
  · cases h

theorem Tab.dom8_find {a : ArrId} (h : t.dom8 a = true) :
    ∃ p, t.lmap.find (TieredArray.t0 a).code = some p ∧ p < t.nb := by
  unfold Tab.dom8 at h
  split at h
  · rename_i p e; exact ⟨p, e, by simpa using h⟩
  · cases h

theorem Tab.pos64_eq {s : TieredArray} {p : Nat} (h : t.lmap.find s.code = some p) : t.pos64 s = p := by
  simp [Tab.pos64, h]

theorem Tab.pos8_eq {a : ArrId} {p : Nat} (h : t.lmap.find (TieredArray.t0 a).code = some p) : t.pos8 a = p := by
  simp [Tab.pos8, h]

theorem Tab.dom64_of_find {s : TieredArray} {p : Nat} (h : t.lmap.find s.code = some p) (hp : t.nb ≤ p) :
    t.dom64 s = true := by
  unfold Tab.dom64; rw [h]; simpa using hp

/-- A word array's position is a word position. -/
theorem Tab.pos64_lt {s : TieredArray} (h : t.dom64 s = true) : t.nb ≤ t.pos64 s ∧ t.pos64 s < t.nb + t.nw := by
  obtain ⟨p, e, hp⟩ := t.dom64_find h
  rw [t.pos64_eq e]; exact ⟨hp, (t.find_some e).1⟩

/-- A byte array's position is a byte position. -/
theorem Tab.pos8_lt {a : ArrId} (h : t.dom8 a = true) : t.pos8 a < t.nb := by
  obtain ⟨p, e, hp⟩ := t.dom8_find h
  rw [t.pos8_eq e]; exact hp

/-- Word array `s` sits at its position. -/
theorem Tab.wAt_pos64 {s : TieredArray} (h : t.dom64 s = true) : t.wAt (t.pos64 s) = s := by
  obtain ⟨p, e, _⟩ := t.dom64_find h
  rw [t.pos64_eq e]; exact t.find_code e

theorem Tab.wAt_pos8 {a : ArrId} (h : t.dom8 a = true) : t.wAt (t.pos8 a) = TieredArray.t0 a := by
  obtain ⟨p, e, _⟩ := t.dom8_find h
  rw [t.pos8_eq e]; exact t.find_code e

/-- The array at a word position is a word array there. -/
theorem Tab.dom64_wAt {p : Nat} (h1 : t.nb ≤ p) (h2 : p < t.nb + t.nw) :
    t.dom64 (t.wAt p) = true ∧ t.pos64 (t.wAt p) = p := by
  have e := t.find_wAt h2
  refine ⟨?_, t.pos64_eq e⟩
  unfold Tab.dom64; rw [e]; simpa using h1

/-- The array at a byte position is a byte array there. -/
theorem Tab.dom8_wAt {p : Nat} (h : p < t.nb) :
    TieredArray.t0 (t.wAt p).arr = t.wAt p ∧ t.dom8 (t.wAt p).arr = true ∧ t.pos8 (t.wAt p).arr = p := by
  have e := t.find_wAt (p := p) (by omega)
  have hb := t.wAt_byte h
  have e0 : TieredArray.t0 (t.wAt p).arr = t.wAt p := by
    rcases hw : t.wAt p with ⟨x, hi⟩; rw [hw] at hb; cases hb; rfl
  rw [← e0] at e
  refine ⟨e0, ?_, t.pos8_eq e⟩
  unfold Tab.dom8; rw [e]; simpa using h

/-- Distinct positions hold distinct arrays. -/
theorem Tab.wAt_inj {p q : Nat} (hp : p < t.nb + t.nw) (hq : q < t.nb + t.nw) (h : t.wAt p = t.wAt q) :
    p = q := by
  have e1 := t.find_wAt hp; have e2 := t.find_wAt hq
  rw [h] at e1; rw [e1] at e2; cases e2; rfl

theorem Tab.pos64_inj {s s' : TieredArray} (h : t.dom64 s = true) (h' : t.dom64 s' = true)
    (e : t.pos64 s = t.pos64 s') : s = s' := by
  rw [← t.wAt_pos64 h, ← t.wAt_pos64 h', e]

theorem Tab.pos64_ne {s s' : TieredArray} (h : t.dom64 s = true) (h' : t.dom64 s' = true)
    (e : s ≠ s') : t.pos64 s ≠ t.pos64 s' := fun e' => e (t.pos64_inj h h' e')

theorem Tab.pos8_ne {a a' : ArrId} (h : t.dom8 a = true) (h' : t.dom8 a' = true)
    (e : a ≠ a') : t.pos8 a ≠ t.pos8 a' := fun e' => e (by
  have := t.wAt_pos8 h; rw [e', t.wAt_pos8 h'] at this; exact (TieredArray.t0_inj.mp this).symm)

/-- A byte array and a word array are at distinct positions (their kinds differ). -/
theorem Tab.pos8_ne_pos64 {a : ArrId} {s : TieredArray} (h : t.dom8 a = true) (h' : t.dom64 s = true) :
    t.pos8 a ≠ t.pos64 s := by
  have := t.pos8_lt h; have := t.pos64_lt h'; omega

theorem Tab.adj64 (a : ArrId) (h : t.dom64 (tier1 a) = true) :
    t.dom64 (TieredArray.t0 a) = true ∧ t.pos64 (tier1 a) = t.pos64 (TieredArray.t0 a) + 1 := by
  have hp := t.pos64_lt h
  have hw := t.wAt_pos64 h
  obtain ⟨h1, h2⟩ := t.wAt_tier hp.2 (by rw [hw])
  rw [hw] at h2
  have hd := t.dom64_wAt (p := t.pos64 (tier1 a) - 1) (by omega) (by omega)
  rw [h2] at hd
  exact ⟨hd.1, by rw [hd.2]; omega⟩

theorem Tab.pos64_tierA {a : ArrId} (h : t.dom64 (tier1 a) = true) (u : Word) :
    t.pos64 (tierA a u) = t.pos64 (TieredArray.t0 a) + (u &&& 1).toNat := by
  have : u &&& 1 = 0 ∨ u &&& 1 = 1 := by
    have : (u &&& 1).toNat ≤ 1 := by rw [UInt64.toNat_and]; exact Nat.and_le_right
    rcases (by omega : (u &&& 1).toNat = 0 ∨ (u &&& 1).toNat = 1) with h | h
    · exact .inl (UInt64.toNat_inj.mp h)
    · exact .inr (UInt64.toNat_inj.mp h)
  rcases this with e | e
  · simp [tierA, e]
  · simp [tierA, e, (t.adj64 a h).2]

theorem Tab.dom64_tierA {a : ArrId} (h : t.dom64 (tier1 a) = true) (u : Word) :
    t.dom64 (tierA a u) = true := by
  rcases tierA_eq_or a u with e | e <;> rw [e]
  · exact (t.adj64 a h).1
  · exact h

theorem Tab.dom64_t0 {a : ArrId} (h : t.dom64 (tier1 a) = true) :
    t.dom64 (TieredArray.t0 a) = true := (t.adj64 a h).1

theorem Tab.wd_pos8 {a : ArrId} (h : t.dom8 a = true) : t.wd (t.pos8 a) = 1 := by
  simp [Tab.wd, t.pos8_lt h]

theorem Tab.wd_pos64 {s : TieredArray} (h : t.dom64 s = true) : t.wd (t.pos64 s) = 8 := by
  have := t.pos64_lt h; simp only [Tab.wd]; split <;> omega

end

/- The proofs above the layout use only the lemmas above (`pos64_lt`, `pos64_ne`, `pos64_tierA`,
…): unfolding the layout map in a goal makes `whnf` search the tree. The kernel (code generation,
`decide +kernel`) still evaluates them. -/
attribute [irreducible] Tab.pos64 Tab.dom64 Tab.pos8 Tab.dom8

/-- The descriptor words of position `p`: its base and its length. -/
def Tab.dbase (_ : Tab) (p : Nat) : Int := 16 + 8 * p
def Tab.dlen (t : Tab) (p : Nat) : Int := 16 + 8 * (t.nb + t.nw) + 8 * p
/-- The third descriptor word of position `p`: a word position's length in 32-bit elements
(twice its length in words), the bound of a 32-bit access (`ld32Code`, `st32Code`). -/
def Tab.dlen32 (t : Tab) (p : Nat) : Int := 16 + 16 * (t.nb + t.nw) + 8 * p

/-- The descriptor words of byte array `a` and of word array `s`, through the layout map. -/
def Tab.base8 (t : Tab) (a : ArrId) : Int := t.dbase (t.pos8 a)
def Tab.len8 (t : Tab) (a : ArrId) : Int := t.dlen (t.pos8 a)
def Tab.base64 (t : Tab) (s : TieredArray) : Int := t.dbase (t.pos64 s)
def Tab.len64 (t : Tab) (s : TieredArray) : Int := t.dlen (t.pos64 s)
def Tab.len32 (t : Tab) (s : TieredArray) : Int := t.dlen32 (t.pos64 s)

/-- The positions of the byte arrays `bs` and the word arrays `ws` (each with its tiered flag), in
order: the byte arrays, then each word array, tier 1 of a tiered one right after its tier 0. -/
def layoutOf (bs : List ArrId) (ws : List (ArrId × Bool)) : List TieredArray :=
  bs.map TieredArray.t0 ++ ws.flatMap fun (a, ti) => if ti then [TieredArray.t0 a, tier1 a] else [TieredArray.t0 a]

/-- The layout map of the position list `l` (a balanced tree). -/
def lmapOf (l : List TieredArray) : NTree :=
  let es := ((l.zipIdx.map fun (s, i) => (s.code, i)).toArray.qsort (fun x y => x.1 < y.1))
  NTree.ofSorted es 0 es.size

/-- The table with the byte arrays `bs` and the word arrays `ws` in this order (`layoutOf`), and
the given constant data, result count and global count; if two of the names coincide (the layout
check fails), the table with no arrays. -/
def Tab.ofArrs (bs : List ArrId) (ws : List (ArrId × Bool)) (rom : List UInt8) (nres ng : Nat) : Tab :=
  let l := layoutOf bs ws
  let m := lmapOf l
  if h : layOkB bs.length (l.length - bs.length) l m = true then
    { nb := bs.length, nw := l.length - bs.length, arrAt := l, lmap := m, layOk := h, rom, nres, ng }
  else
    { nb := 0, nw := 0, arrAt := [], lmap := .leaf, layOk := by decide, rom, nres, ng }

/-- The minimum length of word array `s` (`Tab.mins`), `0` if it has none. -/
def Tab.min64 (t : Tab) (s : TieredArray) : Nat := (t.mins.lookup s.code).getD 0

/-- The offset from the table of word array `s`, if it is the table-relative one (`Tab.tbl`). -/
def Tab.tbl64 (t : Tab) (s : TieredArray) : Option Nat :=
  match t.tbl with
  | some (a, c) => if !s.hi && s.arr == a then some c else none
  | none => none

/-- The minimum length both tiers of the tiered array `a` have (a tiered access, either tier). -/
def Tab.min64t (t : Tab) (a : ArrId) : Nat := min (t.min64 (TieredArray.t0 a)) (t.min64 (tier1 a))

theorem Tab.min64t_le (t : Tab) (a : ArrId) (u : Word) : t.min64t a ≤ t.min64 (tierA a u) := by
  unfold Tab.min64t
  rcases tierA_eq_or a u with e | e <;> rw [e] <;> omega

theorem lookup_getD_lt : ∀ (l : List (Nat × Nat)) (a c : Nat), 0 < c →
    l.all (fun x => decide (x.2 < c)) = true → (l.lookup a).getD 0 < c
  | [], _, _, hc, _ => by simpa using hc
  | (b, k) :: l, a, c, hc, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [List.lookup_cons]
    split
    · simpa using h.1
    · exact lookup_getD_lt l a c hc h.2

/-- Every minimum length is below `c`. -/
theorem Tab.min64_lt {t : Tab} {c : Nat} (hc : 0 < c) (h : t.mins.all (fun x => decide (x.2 < c)) = true)
    (s : TieredArray) : t.min64 s < c :=
  lookup_getD_lt t.mins s.code c hc h

/-- The words the constant data takes. -/
def Tab.romWords (t : Tab) : Nat := (t.romLen + 7) / 8

theorem Tab.rom_length_le (t : Tab) : t.rom.length ≤ 8 * t.romWords := by
  simp only [Tab.romWords, t.romLen_eq]; omega
def Tab.romBase (t : Tab) : Int := 16 + 24 * (t.nb + t.nw)
/-- The results past the registers. -/
def Tab.nxres (t : Tab) : Nat := t.nres - maxRes
/-- The result area: result `i ≥ maxRes` is the word at `resOff i`. -/
def Tab.resBase (t : Tab) : Int := 16 + 24 * (t.nb + t.nw) + 8 * t.romWords
def Tab.resOff (t : Tab) (i : Nat) : Int := t.resBase + 8 * ((i - maxRes : Nat) : Int)
/-- Where the table-relative array starts (`Tab.tbl`): past the table's descriptors, constant
data, result area and globals (an entry without arguments) and the trampoline's 32-byte save area,
rounded up to 64 bytes. -/
def Tab.tblBase (t : Tab) : Nat :=
  64 * ((16 + 24 * (t.nb + t.nw) + 8 * t.romWords + 8 * t.nxres + 8 * t.ng + 32 + 63) / 64)

/-- The global variables: global `g` is the word at `globOff g`. -/
def Tab.globBase (t : Tab) : Int := 16 + 24 * (t.nb + t.nw) + 8 * t.romWords + 8 * t.nxres
def Tab.globOff (t : Tab) (g : GVar) : Int := t.globBase + 8 * (g.id : Int)
def Tab.args (t : Tab) : Int := 16 + 24 * (t.nb + t.nw) + 8 * t.romWords + 8 * t.nxres + 8 * t.ng

/-- The first position of `d` in `rom` (`0` if there is none; `WF` checks that it is one). -/
def romIdx (d : List UInt8) : List UInt8 → Nat
  | [] => 0
  | b :: rom => if d.isPrefixOf (b :: rom) then 0 else romIdx d rom + 1

/-- The constant bytes of a byte source. -/
def BSrc.roms : BSrc → List (List UInt8)
  | .arr _ => []
  | .rom d => [d]

/-- The constant byte strings of an expression, a condition, a statement, a program. -/
def Expr.roms : Expr → List (List UInt8)
  | .bin _ a b | .cmpw _ a b => Expr.roms a ++ Expr.roms b
  | .ld8 _ i | .ld64 _ i => Expr.roms i
  | .ldc d i => d :: Expr.roms i
  | .ld64t _ t i => Expr.roms t ++ Expr.roms i
  | .len64t _ t => Expr.roms t
  | .ld8x8 s i => BSrc.roms s ++ Expr.roms i
  | .ld32t _ t i => Expr.roms t ++ Expr.roms i
  | .ld32h _ t i _ => Expr.roms t ++ Expr.roms i
  | _ => []

def WArr.roms : WArr → List (List UInt8)
  | .plain _ => []
  | .tier _ t => Expr.roms t

def Cond.roms : Cond → List (List UInt8)
  | .cmp _ a b => Expr.roms a ++ Expr.roms b
  | .and p q | .or p q => Cond.roms p ++ Cond.roms q
  | .not p => Cond.roms p

def Stmt.roms : Stmt → List (List UInt8)
  | .skip | .brk => []
  | .set _ e | .abort e => Expr.roms e
  | .st8 _ i e | .st64 _ i e => Expr.roms i ++ Expr.roms e
  | .seq s t => Stmt.roms s ++ Stmt.roms t
  | .ite c s t => Cond.roms c ++ Stmt.roms s ++ Stmt.roms t
  | .while c s => Cond.roms c ++ Stmt.roms s
  | .ret es => es.flatMap Expr.roms
  | .call _ _ args => args.flatMap Expr.roms
  | .gset _ e => Expr.roms e
  | .st64t _ t i e => Expr.roms t ++ Expr.roms i ++ Expr.roms e
  | .copy64 d di s si n => WArr.roms d ++ Expr.roms di ++ WArr.roms s ++ Expr.roms si ++ Expr.roms n
  | .copy8w d di s si n => WArr.roms d ++ Expr.roms di ++ BSrc.roms s ++ Expr.roms si ++ Expr.roms n
  | .scan8 _ s i e c => BSrc.roms s ++ Expr.roms i ++ Expr.roms e ++ [c]
  | .st32t _ t i e => Expr.roms t ++ Expr.roms i ++ Expr.roms e

/-- Insert `d` before the first longer string (structural, so the kernel evaluates it). -/
def romInsert (d : List UInt8) : List (List UInt8) → List (List UInt8)
  | [] => [d]
  | e :: es => if d.length ≤ e.length then d :: e :: es else e :: romInsert d es

/-- Byte strings by length, shortest first (a stable insertion sort). -/
def romSort : List (List UInt8) → List (List UInt8)
  | [] => []
  | d :: ds => romInsert d (romSort ds)

/-- The constant data of a program: its byte strings, each once, shortest first (so that finding
a short string, `romIdx`, does not scan a long one: this keeps the static check of a program
with a large ROM cheap, `WFSplit.lean`). -/
def Prog.rom (p : Prog) : List UInt8 :=
  (romSort ((p.flatMap fun (_, fd) => Stmt.roms fd.body).foldl
    (fun acc d => if acc.contains d then acc else acc ++ [d]) [])).flatten

/-- The most results a statement returns or reads from a call. -/
def Stmt.nres : Stmt → Nat
  | .seq s t | .ite _ s t => max (Stmt.nres s) (Stmt.nres t)
  | .while _ s => Stmt.nres s
  | .ret es => es.length
  | .call xs _ _ => xs.length
  | _ => 0

/-! ## Names as numbers, and a search tree keyed by them

The kernel compares `String`s slowly (UTF-8 byte lists), `Nat` literals fast (GMP): code that the
kernel evaluates looks names up by `nameCode` in an `NTree` (`WFFast.lean`; the per-callee result
counts below). -/

/-- Bijective base-257 numeration of a byte list (digits `1..256`, least significant first). -/
def bytesCode : List UInt8 → Nat
  | [] => 0
  | b :: l => (b.toNat + 1) + 257 * bytesCode l

/-- A function name as a number. -/
def nameCode (s : String) : Nat := bytesCode s.toByteArray.data.toList


/-- The most results a statement returns: a function sets only these (`Ctx.nr`); a caller that
reads more zeroes the rest itself. -/
def Stmt.nret : Stmt → Nat
  | .seq s t | .ite _ s t => max (Stmt.nret s) (Stmt.nret t)
  | .while _ s => Stmt.nret s
  | .ret es => es.length
  | _ => 0

/-- The result counts of a program's functions (`Stmt.nret` of the body) by `nameCode`; `none`
if a name occurs twice (built right to left, as `WFFast.lean`'s `progTree`). -/
def Prog.nrTree : Prog → Option NTree
  | [] => some .leaf
  | (f, fd) :: p => (Prog.nrTree p).bind (·.insert (nameCode f) (Stmt.nret fd.body))

/-- `Prog.nrTree`, or the empty tree (then every call site reads all `nres` results; `Prog.wf`
rules this case out). -/
def Prog.nrt (p : Prog) : NTree := (Prog.nrTree p).getD .leaf

/-- The results callee `f` sets: its entry in `t`, else all `tab.nres`. -/
def nrOf (t : NTree) (tab : Tab) (f : FnName) : Nat := (t.find (nameCode f)).getD tab.nres

/-- The frame (in words) of callee `f` if it is a leaf with no stack check of its own: its entry
in the table `sk` (`Prog.skt`), else 0. A caller's stack check leaves room for it. -/
def skOf (sk : NTree) (f : FnName) : Nat := (sk.find (nameCode f)).getD 0

/-- The largest `skOf sk g` over the functions `g` a statement calls (also by tail call). -/
def Stmt.need (sk : NTree) : Stmt → Nat
  | .seq s t | .ite _ s t => max (Stmt.need sk s) (Stmt.need sk t)
  | .while _ s => Stmt.need sk s
  | .call _ g _ => skOf sk g
  | _ => 0

/-- One more than the largest global variable an expression, a condition, a statement names. -/
def Expr.nglob : Expr → Nat
  | .bin _ a b | .cmpw _ a b => max (Expr.nglob a) (Expr.nglob b)
  | .ld8 _ i | .ld64 _ i | .ldc _ i => Expr.nglob i
  | .glob g => g.id + 1
  | .ld64t _ t i => max (Expr.nglob t) (Expr.nglob i)
  | .len64t _ t => Expr.nglob t
  | .ld8x8 _ i => Expr.nglob i
  | .ld32t _ t i => max (Expr.nglob t) (Expr.nglob i)
  | .ld32h _ t i _ => max (Expr.nglob t) (Expr.nglob i)
  | _ => 0

def WArr.nglob : WArr → Nat
  | .plain _ => 0
  | .tier _ t => Expr.nglob t

def Cond.nglob : Cond → Nat
  | .cmp _ a b => max (Expr.nglob a) (Expr.nglob b)
  | .and p q | .or p q => max (Cond.nglob p) (Cond.nglob q)
  | .not p => Cond.nglob p

def Stmt.nglob : Stmt → Nat
  | .skip | .brk => 0
  | .set _ e | .abort e => Expr.nglob e
  | .st8 _ i e | .st64 _ i e => max (Expr.nglob i) (Expr.nglob e)
  | .seq s t => max (Stmt.nglob s) (Stmt.nglob t)
  | .ite c s t => max (Cond.nglob c) (max (Stmt.nglob s) (Stmt.nglob t))
  | .while c s => max (Cond.nglob c) (Stmt.nglob s)
  | .ret es | .call _ _ es => es.foldl (fun acc e => max acc (Expr.nglob e)) 0
  | .gset g e => max (g.id + 1) (Expr.nglob e)
  | .st64t _ t i e => max (Expr.nglob t) (max (Expr.nglob i) (Expr.nglob e))
  | .copy64 d di s si n => max (WArr.nglob d) (max (Expr.nglob di) (max (WArr.nglob s)
      (max (Expr.nglob si) (Expr.nglob n))))
  | .copy8w d di _ si n => max (WArr.nglob d) (max (Expr.nglob di) (max (Expr.nglob si) (Expr.nglob n)))
  | .scan8 _ _ i e _ => max (Expr.nglob i) (Expr.nglob e)
  | .st32t _ t i e => max (Expr.nglob t) (max (Expr.nglob i) (Expr.nglob e))

/-! ## The arrays a program names -/

/-- The arrays a byte source, an expression, …, a statement names: `(a, 0)` the byte array `a`,
`(a, 1)` the word array `a` (a plain access), `(a, 2)` the tiered array `a`. -/
def BSrc.arrU : BSrc → List (Nat × Nat)
  | .arr a => [(a, 0)]
  | .rom _ => []

def Expr.arrU : Expr → List (Nat × Nat)
  | .bin _ a b | .cmpw _ a b => Expr.arrU a ++ Expr.arrU b
  | .ld8 a i => (a, 0) :: Expr.arrU i
  | .ld64 a i => (a, 1) :: Expr.arrU i
  | .len8 a => [(a, 0)]
  | .len64 a => [(a, 1)]
  | .ldc _ i => Expr.arrU i
  | .ld64t a t i => (a, 2) :: (Expr.arrU t ++ Expr.arrU i)
  | .len64t a t => (a, 2) :: Expr.arrU t
  | .ld8x8 s i => BSrc.arrU s ++ Expr.arrU i
  | .ld32t a t i => (a, 2) :: (Expr.arrU t ++ Expr.arrU i)
  | .ld32h a t i _ => (a, 2) :: (Expr.arrU t ++ Expr.arrU i)
  | _ => []

def WArr.arrU : WArr → List (Nat × Nat)
  | .plain a => [(a, 1)]
  | .tier a t => (a, 2) :: Expr.arrU t

def Cond.arrU : Cond → List (Nat × Nat)
  | .cmp _ a b => Expr.arrU a ++ Expr.arrU b
  | .and p q | .or p q => Cond.arrU p ++ Cond.arrU q
  | .not p => Cond.arrU p

def Stmt.arrU : Stmt → List (Nat × Nat)
  | .skip | .brk => []
  | .set _ e | .abort e | .gset _ e => Expr.arrU e
  | .st8 a i e => (a, 0) :: (Expr.arrU i ++ Expr.arrU e)
  | .st64 a i e => (a, 1) :: (Expr.arrU i ++ Expr.arrU e)
  | .seq s t => Stmt.arrU s ++ Stmt.arrU t
  | .ite c s t => Cond.arrU c ++ Stmt.arrU s ++ Stmt.arrU t
  | .while c s => Cond.arrU c ++ Stmt.arrU s
  | .ret es | .call _ _ es => es.flatMap Expr.arrU
  | .st64t a t i e => (a, 2) :: (Expr.arrU t ++ Expr.arrU i ++ Expr.arrU e)
  | .copy64 d di s si n => WArr.arrU d ++ Expr.arrU di ++ WArr.arrU s ++ Expr.arrU si ++ Expr.arrU n
  | .copy8w d di s si n => WArr.arrU d ++ Expr.arrU di ++ BSrc.arrU s ++ Expr.arrU si ++ Expr.arrU n
  | .scan8 _ s i e _ => BSrc.arrU s ++ Expr.arrU i ++ Expr.arrU e
  | .st32t a t i e => (a, 2) :: (Expr.arrU t ++ Expr.arrU i ++ Expr.arrU e)

def Prog.arrU (p : Prog) : List (Nat × Nat) := p.flatMap fun (_, fd) => Stmt.arrU fd.body

/-- The numbers of `l`, sorted, each once. -/
def sortDedup (l : List Nat) : List Nat :=
  let s := l.mergeSort
  (s.zip ((none :: s.map some).take s.length)).filterMap fun (x, y) => if y == some x then none else some x

/-- The byte arrays a program names, by number. -/
def Prog.byteArrs (p : Prog) : List ArrId := sortDedup (((Prog.arrU p).filter (·.2 == 0)).map (·.1))

/-- The word arrays a program names, by number, each with whether it is tiered. -/
def Prog.wordArrs (p : Prog) : List (ArrId × Bool) :=
  let us := Prog.arrU p
  let ts := sortDedup ((us.filter (·.2 == 2)).map (·.1))
  (sortDedup ((us.filter (·.2 != 0)).map (·.1))).map fun a => (a, ts.contains a)

/-- **The table of a program**: its byte arrays, then its word arrays (by number; tier 1 of a tiered
one right after its tier 0, `Tab.ofArrs`), its constant data, its result and global counts. -/
def Prog.tab (p : Prog) : Tab :=
  Tab.ofArrs (Prog.byteArrs p) (Prog.wordArrs p) (Prog.rom p) ((p.map fun (_, fd) => Stmt.nres fd.body).foldl max 1)
    ((p.map fun (_, fd) => Stmt.nglob fd.body).foldl max 0)


/-- A right operand that needs no temporary: a variable, a global, an array length or a constant. -/
def Expr.isSimple : Expr → Bool
  | .var _ | .glob _ | .len8 _ | .len64 _ | .const _ => true
  | _ => false

def tempsE : Expr → Nat
  | .bin _ a b | .cmpw _ a b => if Expr.isSimple b then tempsE a else max (tempsE a) (1 + tempsE b)
  | .ld8 _ i | .ld64 _ i | .ldc _ i => tempsE i
  | .ld64t _ t i => if Expr.isSimple t then tempsE i else max (tempsE t) (1 + tempsE i)
  | .len64t _ t => tempsE t
  | .ld8x8 _ i => tempsE i
  | .ld32t _ t i => if Expr.isSimple t then tempsE i else max (tempsE t) (1 + tempsE i)
  | .ld32h _ t i _ => if Expr.isSimple t then tempsE i else max (tempsE t) (1 + tempsE i)
  | _ => 0

def tempsC : Cond → Nat
  | .cmp _ a b => if Expr.isSimple b then tempsE a else max (tempsE a) (1 + tempsE b)
  | .and p q | .or p q => max (tempsC p) (tempsC q)
  | .not p => tempsC p

def tempsArgs : Nat → List Expr → Nat
  | _, [] => 0
  | i, e :: es => max (max (i + 1) (i + tempsE e)) (tempsArgs (i + 1) es)

/-- The temporaries of `compileE` on each of `es`, from `0`. -/
def tempsEs : List Expr → Nat
  | [] => 0
  | e :: es => max (tempsE e) (tempsEs es)

/-- A bound on the temporaries of a statement (`tempsS`, which also knows which `return`s are
compiled without temporaries). -/
def tempsSB : Stmt → Nat
  | .skip | .brk => 0
  | .set _ e | .abort e => tempsE e
  | .ret es => max 1 (tempsArgs 0 es)
  | .st8 _ i e | .st64 _ i e => if Expr.isSimple e then tempsE i else max (tempsE i) (1 + tempsE e)
  | .seq s t => max (tempsSB s) (tempsSB t)
  | .ite c s t => max (tempsC c) (max (tempsSB s) (tempsSB t))
  | .while c s => max (tempsC c) (tempsSB s)
  | .call _ _ args => tempsArgs 0 args
  | .gset _ e => tempsE e
  | .st64t _ _ i e => if Expr.isSimple e then tempsE i else max (tempsE i) (1 + tempsE e)
  | .copy64 .. | .copy8w .. => 1
  | .scan8 .. => 0
  | .st32t _ _ i e => if Expr.isSimple e then tempsE i else max (tempsE i) (1 + tempsE e)

/-- A bound on the number of words in the frame of `fd` (`Prog.wf` checks that it is small). -/
def frameWords (fd : FunDecl) : Nat := fd.nlocals + tempsSB fd.body

/-- A constant that fits a sign-extended 32-bit immediate. -/
def fitsImm32 (w : Word) : Bool := -2147483648 ≤ w.toInt64.toInt && w.toInt64.toInt < 2147483648

/-- A constant tier expression's value (lane p32use): a 32-bit access with a constant tier reads
that tier's descriptor words at fixed offsets, and may name an untiered array with tier `0`. -/
def _root_.L.Expr.constTier? : Expr → Option Word
  | .const c => some c
  | _ => none

/-- The array of a 32-bit access `a⟨t⟩.u32[i]` exists: tier `c` of `a` for a constant tier `c`,
else both tiers (`a` tiered). -/
def Tab.tier32Ok (tab : Tab) (a : ArrId) (t : Expr) : Bool :=
  match t.constTier? with
  | some c => tab.dom64 (tierA a c)
  | none => tab.dom64 (tier1 a)

/-- An operand of a block that needs no code: a local, a global, an array length or an imm32
constant (`Stmt.wf` asks for this). -/
def Expr.isOpnd : Expr → Bool
  | .var _ | .glob _ | .len8 _ | .len64 _ => true
  | .const w => fitsImm32 w
  | _ => false

/-- Does the statement call? -/
def Stmt.calls : Stmt → Bool
  | .seq s t | .ite _ s t => Stmt.calls s || Stmt.calls t
  | .while _ s => Stmt.calls s
  | .call .. => true
  | _ => false

end L.Compiler
