module

public import ConAgua.L.Semantics
public meta import Lean

public section

/-!
# L: reads of locals through chains of writes, in one step

`vcgen` leaves the state after a run of statements as a chain of writes,
`((s.setLoc 3 a).setLocs [4, 5] r).setLoc 3 b`, and every read `(…).loc 4` or `(…).mem` in the
verification conditions has to get through it. With the equations `St.setLoc_loc`,
`St.setLoc_mem`, `St.setLocs_cons`, … (`Logic.lean`) that is one rewrite, one literal comparison
and one `if` per write in the chain, for every read, in every hypothesis, again in each round of
`simp_all` and for each instance in `grind`.

The two simprocs here resolve such a read in one step, by walking the chain in `MetaM`:

* `L.reduceLoc`: `St.loc s y` for a literal `y`. A `setLoc x v` with literal `x = y` gives `v`; a
  `setLocs xs vs` with a literal list `xs` gives the entry of `vs` at `y`'s last position in `xs`
  (`vs`'s element if `vs` is a literal list, else `(vs.tail…).headD 0`); a write to another local
  and a `setG` are skipped; a literal state `St.mk m l` gives `l y` (an element of a literal
  `Locals.init` list, or `0` past its end). The walk stops at the first write to a local that is
  not a literal, and at any other state.
* `L.reduceLocMem`: `St.mem s` skips the `setLoc`/`setLocs` layers of `s` (a literal state gives
  its memory).

Both are `dsimproc`s (the result is definitionally equal: no proof term, the kernel unfolds the
chain once) and run before the subterms are simplified (`↓`), so a read is resolved before the
chain's values are visited. They are registered for `seval`, the simproc set of `grind`'s
normalizer, so `grind`, `finish` and `sym … => vcgen … <;> finish` resolve every read when they
internalize it, instead of instantiating `St.setLoc_loc` once per layer. `simp`, `simp_all` and
`simp only` use them when they are listed (`simp only [L.reduceLoc, L.reduceLocMem, …]`); they
are not in the default `simp` set, where every `simp [St.setLoc_loc, …]` list would turn into
unused arguments.

Both walks stop at a write to a local that is not a literal (`setLoc x v` for a variable `x`, a
`setLocs` whose list is not a literal list of literals). The verification conditions only have
literal locals, and the left sides of the general equations (`St.setLoc_mem`, `St.setLocs_mem`, as
`grind` patterns) stay as they are.
-/

namespace L.LocNF

open Lean Meta

/-- `xs[i]` of a literal list, `0 : Word` past its end. -/
meta def entryOr0 (vs : Array Lean.Expr) (i : Nat) : Lean.Expr :=
  vs[i]?.getD (toExpr (0 : Word))

/-- `(vs.tail^i).headD 0`: entry `i` of a list of words `vs`, `0` past its end. -/
meta def entryOf (vs : Lean.Expr) (i : Nat) : MetaM Lean.Expr := do
  if let some l ← getListLit? vs then return entryOr0 l i
  let mut l := vs
  for _ in [0:i] do l := mkApp2 (mkConst ``List.tail [.zero]) (mkConst ``Word) l
  return mkApp3 (mkConst ``List.headD [.zero]) (mkConst ``Word) l (toExpr (0 : Word))

/-- `Locals.init vs y` for a literal list `vs`: its entry, `0` past the end. -/
meta def initRead (l : Lean.Expr) (y : Nat) : MetaM (Option Lean.Expr) := do
  let_expr Locals.init vs := l | return none
  let some vs ← getListLit? vs | return none
  return some (entryOr0 vs y)

/-- The value of local `y` in state `s`, read through the writes at the top of `s`: `none` if
there is no write to skip and nothing to resolve. -/
meta partial def locRead (s : Lean.Expr) (y : Nat) : MetaM (Option Lean.Expr) := do
  let below (s' : Lean.Expr) : MetaM (Option Lean.Expr) := do
    return some ((← locRead s' y).getD (mkApp2 (mkConst ``St.loc) s' (mkNatLit y)))
  match_expr s with
  | St.setLoc s' x v =>
    let some xv ← getNatValue? x | return none
    if xv == y then return some v else below s'
  | St.setLocs s' xs vs =>
    let some xs ← getListLit? xs | return none
    let mut last : Option Nat := none
    for i in [0:xs.size] do
      let some xv ← getNatValue? xs[i]! | return none
      if xv == y then last := some i
    match last with
    | some i => return some (← entryOf vs i)
    | none => below s'
  | St.setG s' _ _ => below s'
  | St.mk _ l => return some ((← initRead l y).getD (mkApp l (mkNatLit y)))
  | _ => return none

/-- Whether `xs` is a literal list of literal locals. -/
meta def litVars (xs : Lean.Expr) : MetaM Bool := do
  let some xs ← getListLit? xs | return false
  xs.allM fun x => return (← getNatValue? x).isSome

/-- The state below the writes to literal locals at the top of `s`. -/
meta partial def memBase (s : Lean.Expr) : MetaM Lean.Expr := do
  match_expr s with
  | St.setLoc s' x _ => if (← getNatValue? x).isSome then memBase s' else return s
  | St.setLocs s' xs _ => if ← litVars xs then memBase s' else return s
  | _ => return s

end L.LocNF

open Lean Meta in
/-- A read of a local through a chain of writes, in one step (see the module doc). -/
dsimproc ↓ [seval] L.reduceLoc (L.St.loc _ _) := fun e => do
  let_expr L.St.loc s y ← e | return .continue
  let some yv ← getNatValue? y | return .continue
  match ← L.LocNF.locRead s yv with
  | some r => return .visit r
  | none => return .continue

open Lean Meta in
/-- A read of a local of a literal frame, `Locals.init [a, b, …] k`. -/
dsimproc ↓ [seval] L.reduceLocalsInit (L.Locals.init _ _) := fun e => do
  let_expr L.Locals.init vs y ← e | return .continue
  let some yv ← getNatValue? y | return .continue
  match ← L.LocNF.initRead (mkApp (mkConst ``L.Locals.init) vs) yv with
  | some r => return .visit r
  | none => return .continue

open Lean Meta in
/-- The memory of a state behind writes to locals, in one step. -/
dsimproc ↓ [seval] L.reduceLocMem (L.St.mem _) := fun e => do
  let_expr L.St.mem s ← e | return .continue
  let b ← L.LocNF.memBase s
  if b == s then return .continue
  match_expr b with
  | L.St.mk m _ => return .visit m
  | _ => return .visit (mkApp (mkConst ``L.St.mem) b)

/-! Checks. -/

example (s : L.St) (a b c : L.Word) (r : List L.Word) :
    (((s.setLoc 1 a).setLocs [2, 4] r).setLoc 1 c).loc 4 = r.tail.headD 0 ∧
    (((s.setLoc 1 a).setLocs [2, 4] [b, c]).setLoc 1 c).loc 4 = c ∧
    (((s.setLoc 1 a).setLoc 2 b).setLoc 1 c).loc 1 = c ∧
    (((s.setLoc 1 a).setLoc 2 b).setLoc 1 c).loc 3 = s.loc 3 ∧
    ((L.St.mk s.mem (L.Locals.init [a, b])).setLoc 0 c).loc 1 = b ∧
    ((L.St.mk s.mem (L.Locals.init [a, b])).setLoc 0 c).loc 5 = 0 ∧
    (((s.setLoc 1 a).setLocs [2, 4] r).setLoc 1 c).mem = s.mem := by
  simp only [L.reduceLoc, L.reduceLocMem, and_self]

example (s : L.St) (a c : L.Word) (P : L.Word → Prop)
    (h : P (((s.setLoc 1 a).setLoc 2 c).setLoc 1 c |>.loc 5)) : P (s.loc 5) := by
  grind
