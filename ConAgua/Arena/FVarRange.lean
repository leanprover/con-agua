module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
public import ConAgua.Arena.MemoLib
public import ConAgua.Arena.StoreFields
import ConAgua.L.ModelGen
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.MemoLib

@[expose] public section

/-!
# `fvarRange`: the memoized exact free-variable range

con-ron's `fvar_range_go`/`fvar_range_memo` (`arena/expr_ops.rs:2075,2146`, Lean twin
`fvarRangeGo`/`fvarRangeMemo`, `Arena/ExprOps.lean:1483-1563`): `1 +` the largest free-variable
index under a handle (`0` if there is none), memoized per node in `fvarBC`
(`MemoLib.lean`'s `frSch`, array 48). `Walk.lean`'s `bvarBoundGo`/`Memo` shape exactly, with three
differences: the `bvar` arm returns `0` (not `i + 1`: a bound variable is not free), the `fvar` arm
returns `idx + 1` (not `0`), and the binder/`letE` arms do **not** truncate the last child (the
cursor does not move: a binder's own `fvar` annotations are read by `wscopedB`'s refinement, not
descended into, so the whole subterm's fvar range is the plain `max` of its children, unlike
`bvarBound`'s `satPred` on the body). `abstract1`'s cutoff reads it the way
`instantiate1Lift`/`liftLooseBVars` read `der_b`: `fvarB ≤ d` skips the walk (con-ron's `expr_ops.rs`).

`fr_go(h, c)`: `abort` at `c = 0` (the twin's `fuel` exhausted: it throws), else probe the memo
(`fm_find`, `memoFindG frSch`); on a hit return the value. Otherwise `fr_node(h, c - 1)` decodes
the handle and dispatches on the tag, every child at the same `c - 1` (the twin's depth counter,
`fvarRangeGo (fuel + 1)` runs its arms at `fuel`):

* `bvar i` (tag 0): `0`;
* `fvar idx _` (tag 1): `idx + 1` (an `abort` where it wraps);
* `sort`, `const`, `lit` (tags 2, 3, 8): `0`;
* `app f a` (tag 4): `max (fr_go f) (fr_go a)`;
* `lam ty body`, `forallE ty body` (tags 5, 6): `max (fr_go ty) (fr_go body)`;
* `letE ty val body` (tag 7): `max (max (fr_go ty) (fr_go val)) (fr_go body)`;
* `proj n i e` (tag 9): `fr_go e`;
* any other tag: `abort` (the arena's `view` fails there too).

then record the result (probe again, `fm_put`). `fr_memo(h, c)` is `fm_clear(); r := fr_go(h, c); fm_clear()`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- con-ron: ConRon/Arena/ExprOps.lean:1514-1536 ConRon.Arena.fvarRangeGo -/
@[no_expose, l_impl ConRon.Arena.fvarRangeGo]
def frGo : FunDecl := lfn (h, c) locals (fd, j, d, r, u) {
  if c == 0 { abort };
  (fd, j, d) := call fm_find(h, 0);
  if fd != 0 { return FRMEMO.u64[j * 4 + 3] };
  r := call fr_node(h, c - 1);
  (fd, j, d) := call fm_find(h, 0);
  u := call fm_put(h, 0, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1514-1536 ConRon.Arena.fvarRangeGo -/
@[no_expose, l_impl ConRon.Arena.fvarRangeGo]
def frNode : FunDecl := lfn (h, c) locals (g, t, i, f, a, b, x, y, z) {
  g := ⟦h⟧.tag;
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if g == 0 { if BVAR⟨t⟩.count <= i { abort }; return 0 };
  if g == 1 {
    if FVAR⟨t⟩.count <= i { abort };
    x := FVAR⟨t, i⟩.i + 1;
    if x == 0 { abort };
    return x
  };
  if g == 4 {
    i := ⟦h⟧.aidx;
    if APP⟨t⟩.count <= i { abort };
    f := APP⟨t, i⟩.f;
    a := APP⟨t, i⟩.a;
    x := call fr_go(f, c);
    y := call fr_go(a, c);
    return x + (y - x) * u64(x < y)
  };
  if g == 5 {
    if LAM⟨t⟩.count <= i { abort };
    f := LAM⟨t, i⟩.ty;
    a := LAM⟨t, i⟩.b;
    x := call fr_go(f, c);
    y := call fr_go(a, c);
    return x + (y - x) * u64(x < y)
  };
  if g == 6 {
    if FORALL⟨t⟩.count <= i { abort };
    f := FORALL⟨t, i⟩.ty;
    a := FORALL⟨t, i⟩.b;
    x := call fr_go(f, c);
    y := call fr_go(a, c);
    return x + (y - x) * u64(x < y)
  };
  if g == 9 {
    if PROJ⟨t⟩.count <= i { abort };
    f := PROJ⟨t, i⟩.e;
    x := call fr_go(f, c);
    return x
  };
  if g == 7 {
    if LET⟨t⟩.count <= i { abort };
    f := LET⟨t, i⟩.ty;
    a := LET⟨t, i⟩.v;
    b := LET⟨t, i⟩.b;
    x := call fr_go(f, c);
    y := call fr_go(a, c);
    z := call fr_go(b, c);
    x := x + (y - x) * u64(x < y);
    return x + (z - x) * u64(x < z)
  };
  if g == 2 { if SORT⟨t⟩.count <= i { abort }; return 0 };
  if g == 3 { if CONST⟨t⟩.count <= i { abort }; return 0 };
  if g == 8 { if LIT⟨t⟩.count <= i { abort }; return 0 };
  abort
}

/-- **`fr_go` and `fr_node` are their models** `frW`, `frNodeW`, at every fuel. -/
l_model frGo_spec (p : Prog) (hpf : p.lookup "fm_find" = some (memoFindG frSch))
  (hps : p.lookup "fm_put" = some (memoPutG frSch)) (hp : p.lookup "fr_go" = some frGo)
  (hpn : p.lookup "fr_node" = some frNode)
  fns [hp ↦ frW, hpn ↦ frNodeW]
  specs [memoFindG_spec frSch p _ hpf n, memoPutG_spec frSch p _ hps n]
  grind [arena_grind] fold [tierW, idxW]
  extra [evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  finish [tierW, idxW] gen 20 heartbeats 1000000

/-! ## `fr_memo(h, c)`: the entry, between two clears -/

/-- After the walk: clear the memo again. -/
def frClrK : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m₁) => if rdW (m₁.arr64 CTL) 46 + 2 = 0 then none else some (r, mclearG frSch m₁)

/-- **The model of `fr_memo`.** -/
def frMemoW (n : Nat) (m : Mem) (h c : Word) : Option (Word × Mem) :=
  if rdW (m.arr64 CTL) 46 + 2 = 0 then none else frClrK (frW n (mclearG frSch m) h c)

theorem frMemoW_eq (n : Nat) (m : Mem) (h c : Word) (h0 : rdW (m.arr64 CTL) 46 + 2 ≠ 0) :
    frMemoW n m h c = frClrK (frW n (mclearG frSch m) h c) := by simp [frMemoW, h0]

theorem frClrK_some (r : Word) (m₁ : Mem) (h0 : rdW (m₁.arr64 CTL) 46 + 2 ≠ 0) :
    frClrK (some (r, m₁)) = some (r, mclearG frSch m₁) := by simp [frClrK, h0]

grind_pattern [arena_grind] frMemoW_eq => frMemoW n m h c
grind_pattern [arena_grind] frClrK_some => frClrK (some (r, m₁))

/-- con-ron: ConRon/Arena/ExprOps.lean:1588-1594 ConRon.Arena.fvarRangeMemo -/
@[no_expose, l_impl ConRon.Arena.fvarRangeMemo]
def frMemo : FunDecl := lfn (h, c) locals (r, u) {
  u := call fm_clear();
  r := call fr_go(h, c);
  u := call fm_clear();
  return r
}

theorem frMemo_spec (p : Prog) (hpf : p.lookup "fm_find" = some (memoFindG frSch))
    (hps : p.lookup "fm_put" = some (memoPutG frSch)) (hp : p.lookup "fr_go" = some frGo)
    (hpn : p.lookup "fr_node" = some frNode) (hpc : p.lookup "fm_clear" = some (memoClearG frSch))
    (hpm : p.lookup "fr_memo" = some frMemo) (n : Nat) (s₀ : St) (h c : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "fr_memo" [h, c]
    ⦃fun r s' => LocEq s' s₀ ∧ frMemoW n s₀.mem h c = some (r.headD 0, s'.mem); ⊤⦄ := by
  have ih := (frGo_spec p hpf hps hp hpn n).1
  rw [invoke_eq _ hpm]
  simp only [callFn, frMemo]
  sym only [lang_grind, arena_grind] =>
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, memoClearG_spec frSch p _ hpc n, ih] <;>
    finish

/-- The walk and the memo, as one program. -/
def fvarRangeProg : Prog :=
  [("fm_find", memoFindG frSch), ("fm_put", memoPutG frSch), ("fm_clear", memoClearG frSch),
    ("fr_go", frGo), ("fr_node", frNode), ("fr_memo", frMemo)]

end L.Arena
