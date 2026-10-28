module

public import ConAgua.L.Logic
public meta import Lean

public section

/-!
# `vc_flat`: verification conditions without intermediate states

`vcgen` leaves a verification condition with one state per statement of the path: equations
`s₂ = s₁.setLoc x v`, a callee's post `LocEq s₃ s₂ ∧ F = some (r, s₃.mem)`, and reads `s₃.loc y`
of those states in the path conditions. `simp_all` then rewrites through the states in every
hypothesis, in every round.

`vc_flat` removes the states from the context, in the order of the context:

* a conjunction is split;
* an equation `s = e` (or `e = s`) between states, `s` a variable not in `e`, is substituted;
* `LocEq s t`, `s` a variable not in `t`, replaces `s` by `⟨m, t.loc⟩` for a fresh memory `m`
  (`cases s`, then the locals substituted): the state after a call is its memory over the
  caller's locals.

What is left are the memories, the callees' results, their equations and the path conditions;
reads of locals of `⟨m, t.loc⟩` are reads of `t`. Run it after the reads were resolved on the
shared terms (`simp only [L.reduceLoc, L.reduceLocMem] at *`): substituting first unshares the
nested states that `vcgen` built (the reads then cost several times more). Used by `l_model`'s
`flat` recipe (`ModelGen.lean`).
-/

namespace L.VcFlat

open Lean Meta

/-- One step of `vc_flat` on the first hypothesis at or after position `start` it applies to;
the new goal and the position to continue from. -/
meta def step (g : MVarId) (start : Nat) : MetaM (Option (MVarId × Nat)) := g.withContext do
  let decls := (← getLCtx).decls.toList.filterMap id
  -- the hypotheses before the eliminated variable stay where they are
  let idx (x : Lean.Expr) : Nat := (decls.findIdx? (·.fvarId == x.fvarId!)).getD 0
  for i in [start:decls.length] do
    let d := decls[i]!
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``And 2 then
      let #[sub] ← g.cases d.fvarId | throwError "vc_flat: cases on a conjunction"
      return some (sub.mvarId, i)
    if let some (α, lhs, rhs) := ty.eq? then
      if α.isConstOf ``L.St then
        if lhs.isFVar && !(rhs.containsFVar lhs.fvarId!) then
          return some ((← substCore g d.fvarId (symm := false) (tryToSkip := true)).2, idx lhs)
        if rhs.isFVar && !(lhs.containsFVar rhs.fvarId!) then
          return some ((← substCore g d.fvarId (symm := true) (tryToSkip := true)).2, idx rhs)
    if ty.isAppOfArity ``L.LocEq 2 then
      let a := ty.appFn!.appArg!
      let b := ty.appArg!
      if a.isFVar && !(b.containsFVar a.fvarId!) then
        let #[sub] ← g.cases a.fvarId! | throwError "vc_flat: cases on a state"
        let some (.fvar h) := sub.subst.find? d.fvarId | throwError "vc_flat: lost the hypothesis"
        let l := sub.fields[1]!
        let b' := sub.subst.apply b
        let g' := sub.mvarId
        let g' ← g'.withContext do
          g'.replaceLocalDeclDefEq h (← mkEq l (mkApp (mkConst ``L.St.loc) b'))
        return some ((← substCore g' h (symm := false) (tryToSkip := true)).2, idx a)
  return none

/-- `vc_flat` on one goal. -/
meta def run (g : MVarId) : MetaM MVarId := do
  let mut g := g
  let mut pos := 0
  -- each step removes a hypothesis or splits one; the bound only guards against a loop
  for _ in [0:100000] do
    match ← step g pos with
    | some (g', p) => g := g'; pos := p
    | none => return g
  return g

/-- Remove the intermediate states from a verification condition (see the module docstring). -/
syntax (name := vcFlat) "vc_flat" : tactic

open Elab Tactic in
@[tactic vcFlat] meta def evalVcFlat : Tactic := fun _ =>
  liftMetaTactic fun g => return [← run g]

end L.VcFlat
