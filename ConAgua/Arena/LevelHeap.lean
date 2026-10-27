module

meta import ConAgua.L.Semantics
import ConAgua.Census.Attr
public import ConAgua.Arena.StoreFields
public import ConAgua.L.Notation
import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.LevelGrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
public import ConAgua.Layout

@[expose] public section

/-!
# The level scratch heap: one view over store handles and heap nodes

con-ron runs the level algorithms (`Level.simplify`, `leqCore`, `isEquiv`, `subst`, …) on
transient `ConLeche.Level` trees read back out of the store (`readLevelM`). L has no trees, so it
has a **scratch heap**: a word array `LH` (array 192) of three-word nodes `[tag, a, b]` (the
level store's tags: `0` zero, `1` succ `a`, `2` max `a b`, `3` imax `a b`, `4` param `a`, `a` a
name handle word), bump-allocated below the top `CTL[192]`.

A **level pointer** is a word: below `2^32` it is a store handle (tag in bits 31…28, tier bit 27,
index below), at or above `2^32` it is heap node `p - 2^32`. The readback is free: an algorithm
runs on the store handles directly and allocates heap nodes only for what it builds, so a
store DAG is never copied and `readLC` needs no L table. Children of a heap node are pointers of
either kind.

* `lv_node(p)`: the view `(tag, a, b)` of either kind (a store handle by the store's checks, a heap
  node below the top); `abort` on a dangling pointer.
* `lh_mk(g, a, b)`: allocate a heap node.
* `lv_eq(p, q)`: structural equality (`Level.beq`, i.e. `decide (l = r)`), `1`/`0`, with a
  pointer-equality shortcut.

The relation to `Level` values (`LvR`, a decoder as an inductive relation) is in
`LevelHeapRel.lean`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## `lv_node(p)`: the view of a level pointer -/

/-- **The model of `lv_node`**: `[tag, a, b]`, or `[]` where the L code aborts. -/
def lvNodeW (m : Mem) (p : Word) : List Word :=
  if p >>> 32 ≠ 0 then
    if rdW (m.arr64 CTL) 192 < p - 4294967296 + 3 then []
    else [rdW (m.arr64 LH) (p - 4294967296), rdW (m.arr64 LH) (p - 4294967296 + 1),
      rdW (m.arr64 LH) (p - 4294967296 + 2)]
  else if tierW p ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then []
  else if p >>> 28 = 0 then
    if tcnt m ZERO (tierW p) ≤ idxW p then [] else [0, 0, 0]
  else if p >>> 28 = 1 then
    if tcnt m SUCC (tierW p) ≤ idxW p then []
    else [1, tfld m SUCC (tierW p) (idxW p) 0, 0]
  else if p >>> 28 = 2 then
    if tcnt m MAX (tierW p) ≤ idxW p then []
    else [2, tfld m MAX (tierW p) (idxW p) 0,
      tfld m MAX (tierW p) (idxW p) 1]
  else if p >>> 28 = 3 then
    if tcnt m IMAX (tierW p) ≤ idxW p then []
    else [3, tfld m IMAX (tierW p) (idxW p) 0,
      tfld m IMAX (tierW p) (idxW p) 1]
  else if p >>> 28 = 4 then
    if tcnt m PARAM (tierW p) ≤ idxW p then []
    else [4, tfld m PARAM (tierW p) (idxW p) 0, 0]
  else []

/-- con-ron: none — the level scratch heap (the twin reads `ConLeche.Level` trees back, `readLevelM`) -/
def lvNode : FunDecl := lfn (p) locals (o, g, t, i) {
  if p >> 32 != 0 {
    o := p - 4294967296;
    if CTL.u64[192] < o + 3 { abort };
    return (LH.u64[o], LH.u64[o + 1], LH.u64[o + 2])
  };
  g := p >> 28;
  t := ⟦p⟧.tier;
  i := ⟦p⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if g == 0 { if ZERO⟨t⟩.count <= i { abort }; return (0, 0, 0) };
  if g == 1 { if SUCC⟨t⟩.count <= i { abort }; return (1, SUCC⟨t, i⟩.u, 0) };
  if g == 2 {
    if MAX⟨t⟩.count <= i { abort };
    return (2, MAX⟨t, i⟩.u, MAX⟨t, i⟩.v)
  };
  if g == 3 {
    if IMAX⟨t⟩.count <= i { abort };
    return (3, IMAX⟨t, i⟩.u, IMAX⟨t, i⟩.v)
  };
  if g == 4 { if PARAM⟨t⟩.count <= i { abort }; return (4, PARAM⟨t, i⟩.n, 0) };
  abort
}

theorem lvNode_spec (p : Prog) (hp : p.lookup "lv_node" = some lvNode) (n : Nat) (s₀ : St)
    (q : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "lv_node" [q]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧ r = lvNodeW s₀.mem q; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, lvNode]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, level_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld,
        evalE_cnt, tcntM, evalE_tierE, evalE_idxE] <;>
      finish [lvNodeW, tierW, idxW]

/-! ## `lh_mk(g, a, b)`: allocate a heap node -/

/-- The heap top, `CTL[192]`. -/
def htop (m : Mem) : Word := rdW (m.arr64 CTL) 192

/-- The memory after writing node `[g, a, b]` at the top `o`. -/
def lhMem (m : Mem) (o g a b : Word) : Mem :=
  (((m.set64 LH o g).set64 LH (o + 1) a).set64 LH (o + 2) b).set64 CTL 192 (o + 3)

/-- **The model of `lh_mk`**: the new pointer and the memory after. -/
def lhMkW (m : Mem) (g a b : Word) : Option (Word × Mem) :=
  if htop m >>> 40 ≠ 0 ∨ m.len64 LH ≤ htop m + 2 ∨ (m.arr64 CTL).size ≤ 192 then none
  else some (htop m + 4294967296, lhMem m (htop m) g a b)

/-- con-ron: none — the level scratch heap (the twin reads `ConLeche.Level` trees back, `readLevelM`) -/
def lhMk : FunDecl := lfn (g, a, b) locals (o) {
  o := CTL.u64[192];
  if o >> 40 != 0 || len(LH.u64) <= o + 2 { abort };
  LH.u64[o] := g;
  LH.u64[o + 1] := a;
  LH.u64[o + 2] := b;
  CTL.u64[192] := o + 3;
  return o + 4294967296
}

theorem lhMk_spec (p : Prog) (hp : p.lookup "lh_mk" = some lhMk) (n : Nat) (s₀ : St)
    (g a b : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "lh_mk" [g, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ lhMkW s₀.mem g a b = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, lhMk]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, level_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64] <;>
      finish [lhMkW, lhMem, htop]

/-! ## `lv_eq(p, q)`: structural equality -/

/-- The fields of the view. -/
def lvG (m : Mem) (p : Word) : Word := (lvNodeW m p).headD 0
def lvA (m : Mem) (p : Word) : Word := (lvNodeW m p).tail.headD 0
def lvB (m : Mem) (p : Word) : Word := (lvNodeW m p).tail.tail.headD 0

theorem lvG_eq (m : Mem) (p : Word) : lvG m p = (lvNodeW m p).headD 0 := rfl
theorem lvA_eq (m : Mem) (p : Word) : lvA m p = (lvNodeW m p).tail.headD 0 := rfl
theorem lvB_eq (m : Mem) (p : Word) : lvB m p = (lvNodeW m p).tail.tail.headD 0 := rfl
attribute [level_grind =] lvG_eq lvA_eq lvB_eq

mutual
/-- **The model of `lv_eq`** at L fuel `n`: `1` if the two levels are equal, else `0`. -/
def lvEqW : Nat → Mem → Word → Word → Option Word
  | 0, _, _, _ => none
  | n + 1, m, p, q =>
    if p = q then some 1
    else if lvG m p ≠ lvG m q then some 0
    else if lvG m p = 4 then some (if lvA m p = lvA m q then 1 else 0)
    else eqK n m (lvB m p) (lvB m q) (lvEqW n m (lvA m p) (lvA m q))

/-- After the first children. -/
def eqK (n : Nat) (m : Mem) (b d : Word) : Option Word → Option Word
  | none => none
  | some x => if x = 0 then some 0 else lvEqW n m b d
end

section eqArms
variable (n : Nat) (m : Mem) (p q b d x : Word)

theorem lvEqW_refl : lvEqW (n + 1) m p p = some 1 := by simp [lvEqW]
theorem lvEqW_tag (hpq : p ≠ q) (hg : lvG m p ≠ lvG m q) : lvEqW (n + 1) m p q = some 0 := by
  simp [lvEqW, hpq, hg]
theorem lvEqW_param (hpq : p ≠ q) (hg : lvG m p = lvG m q) (h4 : lvG m p = 4) :
    lvEqW (n + 1) m p q = some (if lvA m p = lvA m q then 1 else 0) := by
  have h4' : lvG m q = 4 := hg ▸ h4
  simp only [lvEqW, hpq, ↓reduceIte, hg, h4', ne_eq, not_true_eq_false]
theorem lvEqW_rec (hpq : p ≠ q) (hg : lvG m p = lvG m q) (h4 : lvG m p ≠ 4) :
    lvEqW (n + 1) m p q = eqK n m (lvB m p) (lvB m q) (lvEqW n m (lvA m p) (lvA m q)) := by
  have h4' : lvG m q ≠ 4 := hg ▸ h4
  simp only [lvEqW, hpq, ↓reduceIte, hg, h4', ne_eq, not_true_eq_false]
theorem eqK_zero : eqK n m b d (some 0) = some 0 := by simp [eqK]
theorem eqK_ne (hx : x ≠ 0) : eqK n m b d (some x) = lvEqW n m b d := by simp [eqK, hx]

end eqArms

grind_pattern [level_grind] lvEqW_refl => lvEqW (n + 1) m p p
grind_pattern [level_grind] lvEqW_tag => lvEqW (n + 1) m p q
grind_pattern [level_grind] lvEqW_param => lvEqW (n + 1) m p q
grind_pattern [level_grind] lvEqW_rec => lvEqW (n + 1) m p q
grind_pattern [level_grind] eqK_zero => eqK n m b d (some 0)
grind_pattern [level_grind] eqK_ne => eqK n m b d (some x)

/-- con-leche: ConLeche/Kernel/Expr.lean:75-78 ConLeche.Level.beq -/
@[l_impl ConLeche.Level.beq]
def lvEq : FunDecl := lfn (p, q) locals (g, a, b, h, c, d, x) {
  if p == q { return 1 };
  (g, a, b) := call lv_node(p);
  (h, c, d) := call lv_node(q);
  if g != h { return 0 };
  if g == 4 { return u64(a == c) };
  x := call lv_eq(a, c);
  if x == 0 { return 0 };
  x := call lv_eq(b, d);
  return x
}

section eq
variable (p : Prog) (hpn : p.lookup "lv_node" = some lvNode) (hp : p.lookup "lv_eq" = some lvEq)

include hpn hp in
theorem lvEq_spec (n : Nat) : ∀ (s₀ : St) (a b : Word),
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "lv_eq" [a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ lvEqW n s₀.mem a b = some (r.headD 0); ⊤⦄ := by
  induction n with
  | zero => intro s₀ a b; rw [invoke_eq _ hp]; simp only [callFn, lvEq]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ a b
    rw [invoke_eq _ hp]
    simp only [callFn, lvEq]
    sym only [lang_grind, arena_grind, level_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, lvNode_spec p hpn n, ih] <;>
      finish (gen := 20)

end eq

end L.Arena
