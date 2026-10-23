import ConAgua.Checker.PreludeSimProg

/-!
# Program bundles at `checkerProg` by indexed lookups (lane `loopt3`)

`rfl` on `checkerProg.lookup "f" = some fd` compares `f` with every name before it as `String`s
in the kernel (~0.5 s each). Here a lookup is `lookup_of_mem checkerProg_nodup` (the names are
distinct, `checkerProg_wf`) of the membership `checkerProg[i]? = some ("f", fd)` at the position
`i` (found by compiled code at elaboration time; the kernel walks `i` cons cells and compares no
`String`): ~50 ms each.

* `chk_lk` closes a goal `checkerProg.lookup "f" = some fd`.
* `prog_bundle [h₁, …]` closes a program bundle at `checkerProg`: a lookup by `chk_lk`, a goal
  whose type is one of the `hᵢ`'s by it, a structure field by field (its parents too), a
  `ProgHas checkerProg l` cons by cons (`l` unfolded to `[…]`, `++`, `[]`), a definition by
  unfolding it. It fails on the first goal it cannot close, naming it.
-/

namespace L.Checker

open L

theorem lk_of_idx {i : Nat} {f : FnName} {fd : FunDecl} (h : checkerProg[i]? = some (f, fd)) :
    checkerProg.lookup f = some fd :=
  lookup_of_mem checkerProg_nodup (List.mem_of_getElem? h)

/-- **`p` agrees with `fs` on `fs`'s names** (`ProgHas.agree` without the decided side condition). -/
theorem ProgHas.agreeNames {p fs : Prog} (h : ProgHas p fs) :
    ∀ f ∈ fs.map (·.1), p.lookup f = fs.lookup f := by
  intro f hf
  obtain ⟨⟨g, gd⟩, hm, rfl⟩ := List.mem_map.mp hf
  cases e : fs.lookup g with
  | none => rw [List.lookup_eq_none_iff] at e; exact absurd (e _ hm) (by simp)
  | some fd => exact h _ _ e

open Lean Meta Elab Tactic

/-- The positions of `checkerProg`'s names, by compiled code. -/
unsafe def chkIdx : MetaM (Std.HashMap String Nat) := do
  let e ← mkAppM ``List.map #[mkConst ``Prod.fst [0, 0] |>.app (mkConst ``String)
    |>.app (mkConst ``FunDecl), mkConst ``checkerProg]
  let ns ← evalExpr (List String) (mkApp (mkConst ``List [0]) (mkConst ``String)) e
  let mut m : Std.HashMap String Nat := {}
  for (n, i) in ns.zipIdx do
    unless m.contains n do m := m.insert n i
  return m

/-- A goal `checkerProg.lookup "f" = some fd`, as `(f, fd)`. -/
def lookupGoal? (ty : Lean.Expr) : Option (String × Lean.Expr × Lean.Expr) := do
  let some (_, lhs, rhs) := ty.eq? | none
  guard (lhs.isAppOfArity ``List.lookup 5)
  guard (lhs.appArg!.isConstOf ``checkerProg)
  let fE := lhs.appFn!.appArg!
  let .lit (.strVal f) := fE | none
  guard (rhs.isAppOfArity ``Option.some 2)
  return (f, fE, rhs.appArg!)

/-- Close a lookup goal by its position. -/
def chkLookup (idx : Std.HashMap String Nat) (g : MVarId) (f : String) (fE fd : Lean.Expr) :
    MetaM Unit := do
  let some n := idx[f]? | throwError "chk_lk: {f} is not a function of checkerProg"
  let elemTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkConst ``FunDecl)
  let pair := mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String) (mkConst ``FunDecl) fE fd
  let some_ := mkApp2 (mkConst ``Option.some [0]) elemTy pair
  let h := mkApp2 (mkConst ``Eq.refl [1]) (mkApp (mkConst ``Option [0]) elemTy) some_
  g.assign (mkApp4 (mkConst ``lk_of_idx) (mkNatLit n) fE fd h)

elab "chk_lk" : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let some (f, fE, fd) := lookupGoal? ty | throwError "chk_lk: not a checkerProg lookup: {ty}"
  chkLookup (← unsafe chkIdx) g f fE fd
  replaceMainGoal []

/-- Close a bundle goal (see the module doc). -/
partial def bundle (idx : Std.HashMap String Nat) (hs : Array Lean.Expr)
    (memo : IO.Ref (Std.HashMap Lean.Expr Lean.Expr)) (g : MVarId) : MetaM Unit := do
  let ty ← instantiateMVars (← g.getType)
  let ty := ty.headBeta
  if let some pf := (← memo.get)[ty]? then g.assign pf; return
  bundleGo idx hs memo g ty
  memo.modify (·.insert ty (.mvar g))
where
  bundleGo idx hs memo (g : MVarId) (ty : Lean.Expr) : MetaM Unit := do
  for h in hs do
    if (← instantiateMVars (← inferType h)) == ty then g.assign h; return
  if let some (f, fE, fd) := lookupGoal? ty then return ← chkLookup idx g f fE fd
  for h in hs do
    if ← withReducible (withNewMCtxDepth (isDefEq (← inferType h) ty)) then g.assign h; return
  let env ← getEnv
  match ty.getAppFn with
  | .const c _ =>
    if isStructure env c then
      let gs ← g.constructor
      for g' in gs do bundle idx hs memo g'
      return
    if c == ``ProgHas && ty.getAppNumArgs == 2 then
      let l ← whnfD (ty.appArg!)
      if l.isAppOfArity ``List.nil 1 then
        g.assign (mkApp (mkConst ``ProgHas.nil) (ty.appFn!.appArg!)); return
      if l.isAppOfArity ``List.cons 3 then
        let x ← whnfD l.appFn!.appArg!
        let l' := mkApp3 (mkConst ``List.cons [0]) l.appFn!.appFn!.appArg! x l.appArg!
        let g' ← g.replaceTargetDefEq (mkApp2 (mkConst ``ProgHas) ty.appFn!.appArg! l')
        for g'' in ← g'.apply (mkConst ``ProgHas.cons) do bundle idx hs memo g''
        return
      throwError "prog_bundle: the list does not unfold: {l}"
    match ← unfoldDefinition? ty with
    | some ty' => bundle idx hs memo (← g.replaceTargetDefEq ty')
    | none => throwError "prog_bundle: cannot close {ty}"
  | _ => throwError "prog_bundle: cannot close {ty}"

elab "prog_bundle" " [" hs:term,* "]" : tactic => withMainContext do
  let g ← getMainGoal
  let hs ← hs.getElems.mapM fun h => Term.elabTerm h none
  bundle (← unsafe chkIdx) hs (← IO.mkRef {}) g
  replaceMainGoal []

end L.Checker
