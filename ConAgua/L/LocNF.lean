module

public import ConAgua.L.Semantics
public meta import Lean
import Lean.Expr

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

Each step of the walk is one of the lemmas below, instantiated by hand, and the proof is their
chain of `Eq.trans`; the literal comparisons are `Nat.beq` facts proved by `rfl`. (A `dsimproc`,
whose result the kernel has to see as definitionally equal on its own, sends the kernel unfolding
the values instead of the chain: deep recursion in `FVarRange`, `Walk`, `RomExpr`.) The simprocs
run before the subterms are simplified (`↓`), so a read is resolved before the chain's values are
visited. They are registered for `seval`, the simproc set of `grind`'s
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

/-! ## The steps of the walk -/

theorem loc_setLoc_eq (s : St) (x y : Var) (v : Word) (h : Nat.beq y x = true) :
    (s.setLoc x v).loc y = v := by
  simp [St.setLoc, Nat.eq_of_beq_eq_true h]

theorem loc_setLoc_ne (s : St) (x y : Var) (v : Word) (h : Nat.beq y x = false) :
    (s.setLoc x v).loc y = s.loc y := by
  simp [St.setLoc, Nat.ne_of_beq_eq_false h]

theorem loc_setLocs_nil (s : St) (vs : List Word) (y : Var) : (s.setLocs [] vs).loc y = s.loc y :=
  rfl

theorem loc_setLocs_cons_cons (s : St) (x : Var) (xs : List Var) (v : Word) (vs : List Word)
    (y : Var) : (s.setLocs (x :: xs) (v :: vs)).loc y = ((s.setLoc x v).setLocs xs vs).loc y :=
  rfl

theorem loc_setLocs_cons_nil (s : St) (x : Var) (xs : List Var) (y : Var) :
    (s.setLocs (x :: xs) []).loc y = ((s.setLoc x 0).setLocs xs []).loc y :=
  rfl

theorem loc_setLocs_cons (s : St) (x : Var) (xs : List Var) (vs : List Word) (y : Var) :
    (s.setLocs (x :: xs) vs).loc y = ((s.setLoc x (vs.headD 0)).setLocs xs vs.tail).loc y :=
  rfl

theorem _root_.L.St.setG_loc (s : St) (g : GVar) (v : Word) (y : Var) : (s.setG g v).loc y = s.loc y := rfl

theorem loc_mk (m : Mem) (l : Locals) (y : Var) : (St.mk m l).loc y = l y := rfl

theorem _root_.L.Locals.init_nil (y : Var) : Locals.init [] y = 0 := by simp [Locals.init]

theorem init_cons_zero (v : Word) (vs : List Word) (y : Var) (h : y = 0) :
    Locals.init (v :: vs) y = v := by
  subst h; rfl

theorem init_cons_succ (v : Word) (vs : List Word) (y z : Var) (h : y = z + 1) :
    Locals.init (v :: vs) y = Locals.init vs z := by
  subst h; rfl

theorem _root_.L.St.setLoc_mem (s : St) (x : Var) (v : Word) : (s.setLoc x v).mem = s.mem := rfl

theorem _root_.L.St.setLocs_mem (s : St) (xs : List Var) (vs : List Word) : (s.setLocs xs vs).mem = s.mem := by
  induction xs generalizing s vs with
  | nil => rfl
  | cons x xs ih => exact (ih _ _).trans (L.St.setLoc_mem _ _ _)

theorem mem_mk (m : Mem) (l : Locals) : (St.mk m l).mem = m := rfl

/-! ## The walks -/

open Lean Meta

/-- `p₁ : a = b` then `p₂ : b = c` (either may be missing: `b` and `c` are then the same). -/
meta def trans? (p₁ : Lean.Expr) (p₂? : Option Lean.Expr) : MetaM Lean.Expr := do
  match p₂? with
  | some p₂ => mkEqTrans p₁ p₂
  | none => return p₁

/-- Whether `xs` is a literal list of literal locals. -/
meta def litVars (xs : Lean.Expr) : MetaM Bool := do
  let some xs ← getListLit? xs | return false
  xs.allM fun x => return (← getNatValue? x).isSome

/-- `Locals.init vs y` for a literal `y` and a literal list `vs`: the entry and a proof. -/
meta partial def initRead (vs yE : Lean.Expr) (y : Nat) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  match_expr vs with
  | List.nil _ => return some (toExpr (0 : Word), mkApp (mkConst ``L.Locals.init_nil) yE)
  | List.cons _ v vs' =>
    if y == 0 then
      return some (v, mkApp4 (mkConst ``init_cons_zero) v vs' yE (← mkEqRefl yE))
    else
      let zE := mkNatLit (y - 1)
      let p := mkApp5 (mkConst ``init_cons_succ) v vs' yE zE (← mkEqRefl yE)
      match ← initRead vs' zE (y - 1) with
      | some (r, q) => return some (r, ← mkEqTrans p q)
      | none => return some (mkApp2 (mkConst ``Locals.init) vs' zE, p)
  | _ => return none

/-- The value of local `y` (the literal `yE`) in state `s`, read through the writes at the top of
`s`, with a proof of `s.loc yE = value`; `none` if there is no write to step through. -/
meta partial def locRead (s yE : Lean.Expr) (y : Nat) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  -- one step `p : s.loc yE = s'.loc yE`, then on through `s'`
  let next (p s' : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
    match ← locRead s' yE y with
    | some (r, q) => return some (r, ← mkEqTrans p q)
    | none => return some (mkApp2 (mkConst ``St.loc) s' yE, p)
  match_expr s with
  | St.setLoc s' x v =>
    let some xv ← getNatValue? x | return none
    if xv == y then
      return some (v, mkApp5 (mkConst ``loc_setLoc_eq) s' x yE v (mkApp2 (mkConst ``Eq.refl [1])
        (mkConst ``Bool) (mkConst ``Bool.true)))
    else
      next (mkApp5 (mkConst ``loc_setLoc_ne) s' x yE v (mkApp2 (mkConst ``Eq.refl [1])
        (mkConst ``Bool) (mkConst ``Bool.false))) s'
  | St.setLocs s' xs vs =>
    unless ← litVars xs do return none
    match_expr xs with
    | List.nil _ => next (mkApp3 (mkConst ``loc_setLocs_nil) s' vs yE) s'
    | List.cons _ x xs' =>
      match_expr vs with
      | List.cons _ v vs' =>
        next (mkApp6 (mkConst ``loc_setLocs_cons_cons) s' x xs' v vs' yE)
          (mkApp3 (mkConst ``St.setLocs) (mkApp3 (mkConst ``St.setLoc) s' x v) xs' vs')
      | List.nil _ =>
        next (mkApp4 (mkConst ``loc_setLocs_cons_nil) s' x xs' yE)
          (mkApp3 (mkConst ``St.setLocs) (mkApp3 (mkConst ``St.setLoc) s' x (toExpr (0 : Word))) xs' vs)
      | _ =>
        let hd := mkApp3 (mkConst ``List.headD [.zero]) (mkConst ``Word) vs (toExpr (0 : Word))
        let tl := mkApp2 (mkConst ``List.tail [.zero]) (mkConst ``Word) vs
        next (mkApp5 (mkConst ``loc_setLocs_cons) s' x xs' vs yE)
          (mkApp3 (mkConst ``St.setLocs) (mkApp3 (mkConst ``St.setLoc) s' x hd) xs' tl)
    | _ => return none
  | St.setG s' g v => next (mkApp4 (mkConst ``L.St.setG_loc) s' g v yE) s'
  | St.mk m l =>
    let p := mkApp3 (mkConst ``loc_mk) m l yE
    match_expr l with
    | Locals.init vs =>
      if (← getListLit? vs).isNone then return some (mkApp l yE, p)
      match ← initRead vs yE y with
      | some (r, q) => return some (r, ← mkEqTrans p q)
      | none => return some (mkApp l yE, p)
    | _ => return some ((mkApp l yE).headBeta, p)
  | _ => return none

/-- `s.mem` through the writes to literal locals at the top of `s`: the state below them, with a
proof of `s.mem = base.mem` (`none`: no such write). -/
meta partial def memRead (s : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let next (p s' : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
    match ← memRead s' with
    | some (r, q) => return some (r, ← mkEqTrans p q)
    | none => return some (mkApp (mkConst ``St.mem) s', p)
  match_expr s with
  | St.setLoc s' x v =>
    if (← getNatValue? x).isSome then next (mkApp3 (mkConst ``L.St.setLoc_mem) s' x v) s' else return none
  | St.setLocs s' xs vs =>
    if ← litVars xs then next (mkApp3 (mkConst ``L.St.setLocs_mem) s' xs vs) s' else return none
  | St.mk m l => return some (m, mkApp2 (mkConst ``mem_mk) m l)
  | _ => return none

end L.LocNF

namespace L.LocNF
open Lean Meta Simp

/-- `s.loc y` for a literal `y`, through the writes at the top of `s`. -/
meta def locProc : Simproc := fun e => do
  let_expr St.loc s y ← e | return .continue
  let some yv ← getNatValue? y | return .continue
  match ← locRead s y yv with
  | some (r, p) => return .visit { expr := r, proof? := some p }
  | none => return .continue

/-- `Locals.init vs y` for a literal `y` and a literal list `vs`. A literal list only: the general
equations (`Locals.init_cons_zero`, a `grind` pattern) keep their left sides. -/
meta def initProc : Simproc := fun e => do
  let_expr Locals.init vs y ← e | return .continue
  let some yv ← getNatValue? y | return .continue
  if (← getListLit? vs).isNone then return .continue
  match ← initRead vs y yv with
  | some (r, p) => return .visit { expr := r, proof? := some p }
  | none => return .continue

/-- `s.mem` through the writes to literal locals at the top of `s`. -/
meta def memProc : Simproc := fun e => do
  let_expr St.mem s ← e | return .continue
  match ← memRead s with
  | some (r, p) => return .visit { expr := r, proof? := some p }
  | none => return .continue

end L.LocNF

/-! Each runs before the subterms are simplified (a read is resolved before the chain's values are
visited) and again after (a read that appears only once a subterm is simplified, such as
`(x, s).snd.loc 5`). -/

/-- A read of a local through a chain of writes, in one step (see the module doc). -/
simproc ↓ [seval] L.reduceLoc (L.St.loc _ _) := L.LocNF.locProc
/-- `L.reduceLoc`, after the subterms. -/
simproc [seval] L.reduceLocPost (L.St.loc _ _) := L.LocNF.locProc

/-- A read of a local of a literal frame, `Locals.init [a, b, …] k`. -/
simproc ↓ [seval] L.reduceLocalsInit (L.Locals.init _ _) := L.LocNF.initProc
/-- `L.reduceLocalsInit`, after the subterms. -/
simproc [seval] L.reduceLocalsInitPost (L.Locals.init _ _) := L.LocNF.initProc

/-- The memory of a state behind writes to locals, in one step. -/
simproc ↓ [seval] L.reduceLocMem (L.St.mem _) := L.LocNF.memProc
/-- `L.reduceLocMem`, after the subterms. -/
simproc [seval] L.reduceLocMemPost (L.St.mem _) := L.LocNF.memProc

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
