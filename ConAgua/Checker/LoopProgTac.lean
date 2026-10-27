import ConAgua.Checker.PreludeSimProg
import ConAgua.Checker.RomProg0

/-!
# Program bundles at `checkerProg` by indexed lookups (lane `loopt3`)

`rfl` on `checkerProg.lookup "f" = some fd` compares `f` with every name before it as `String`s
in the kernel (~0.5 s each). Here a lookup is `lookup_of_mem checkerProg_nodup` (the names are
distinct, `checkerProg_wf`) of the membership of `("f", fd)` in `checkerProg` at a position found
by compiled code at elaboration time; the kernel compares no `String`. The position is a chunk
`j` of `checkerChunks` (`checkerProg` cut into lists of `chkChunk` functions,
`checkerProg_chunks`) and an index `i` in it (`lk_of_chunk`): the kernel walks `j + i` cons cells,
at most ~90, where `checkerProg[n]?` walked up to 1838 (~17 µs each).

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

/-! ## `checkerProg` in chunks -/

/-- The functions per chunk of `checkerChunks`. -/
def chkChunk : Nat := 32

open Lean Meta Elab Command in
/-- Declares `checkerProg.chunk<j>` (the functions `chkChunk * j, …` of `checkerProg`, the same
terms), `checkerChunks` (their list) and `checkerProg_chunks : checkerProg = checkerChunks.flatten`
(one kernel check). -/
elab "chunk_checker_prog" : command => liftTermElabM <|
    withTheReader Core.Context (fun c => { c with maxRecDepth := max c.maxRecDepth 100000 }) do
  let elemTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkConst ``FunDecl)
  let progTy := mkConst ``Prog
  let elems ← L.Compiler.listElems (mkConst ``checkerProg)
  let mut cs : Array Lean.Expr := #[]
  let mut i := 0
  while i < elems.size do
    let n := ``checkerProg ++ Name.mkSimple s!"chunk{cs.size}"
    let lit ← mkListLit elemTy (elems.extract i (i + chkChunk)).toList
    addDecl (.defnDecl (mkDefinitionValEx n [] progTy lit (.regular 0) .safe []))
    -- no code: a view of `checkerProg` for the kernel (the program dump skips it)
    modifyEnv (addNoncomputable · n)
    cs := cs.push (mkConst n)
    i := i + chkChunk
  let csLit ← mkListLit progTy cs.toList
  addDecl (.defnDecl (mkDefinitionValEx `L.Checker.checkerChunks [] (mkApp (mkConst ``List [0]) progTy) csLit
    (.regular 0) .safe []))
  modifyEnv (addNoncomputable · `L.Checker.checkerChunks)
  let rhs := mkApp2 (mkConst ``List.flatten [0]) elemTy (mkConst `L.Checker.checkerChunks)
  addDecl (L.Compiler.thm `L.Checker.checkerProg_chunks (mkApp3 (mkConst ``Eq [1]) progTy (mkConst ``checkerProg) rhs)
    (mkApp2 (mkConst ``Eq.refl [1]) progTy (mkConst ``checkerProg)) [])

chunk_checker_prog

theorem lk_of_chunk {j i : Nat} {c : Prog} {f : FnName} {fd : FunDecl}
    (hc : (checkerChunks : List Prog)[j]? = some c) (h : c[i]? = some (f, fd)) :
    checkerProg.lookup f = some fd := by
  refine lookup_of_mem checkerProg_nodup ?_
  rw [checkerProg_chunks]
  exact List.mem_flatten.mpr ⟨c, List.mem_of_getElem? hc, List.mem_of_getElem? h⟩

/-- **`p` agrees with `fs` on `fs`'s names** (`ProgHas.agree` without the decided side condition). -/
theorem ProgHas.agreeNames {p fs : Prog} (h : ProgHas p fs) :
    ∀ f ∈ fs.map (·.1), p.lookup f = fs.lookup f := by
  intro f hf
  obtain ⟨⟨g, gd⟩, hm, rfl⟩ := List.mem_map.mp hf
  cases e : fs.lookup g with
  | none => rw [List.lookup_eq_none_iff] at e; exact absurd (e _ hm) (by simp)
  | some fd => exact h _ _ e

/-- Names and whether the function reads no pin data. -/
def chkNames (p : Prog) : List (String × Bool) := p.map fun x => (x.1, x.2.body.noPB)

open Lean Meta Elab Tactic

/-- `checkerProg`'s names: their positions and whether the function reads no pin data, by
compiled code. -/
structure ChkIdx where
  pos : Std.HashMap String Nat
  noPB : Std.HashMap String Bool

/-- The index of `checkerProg`'s names. -/
unsafe def chkIdx : MetaM ChkIdx := do
  let e := mkApp (mkConst ``chkNames) (mkConst ``checkerProg)
  let ns ← evalExpr (List (String × Bool)) (← inferType e) e
  let mut m : Std.HashMap String Nat := {}
  let mut b : Std.HashMap String Bool := {}
  for ((n, x), i) in ns.zipIdx do
    unless m.contains n do m := m.insert n i; b := b.insert n x
  return ⟨m, b⟩

/-- A goal `P.lookup "f" = some fd` for `P` `checkerProg` or `Prog.subPB bs checkerProg`, as
`(f, fd, bs?)`. -/
def lookupGoal? (ty : Lean.Expr) : Option (String × Lean.Expr × Lean.Expr × Option Lean.Expr) := do
  let some (_, lhs, rhs) := ty.eq? | none
  guard (lhs.isAppOfArity ``List.lookup 5)
  let P := lhs.appArg!
  let bs? ← if P.isConstOf ``checkerProg then pure none
    else if P.isAppOfArity ``Prog.subPB 2 && P.appArg!.isConstOf ``checkerProg then
      pure (some P.appFn!.appArg!)
    else none
  let fE := lhs.appFn!.appArg!
  let .lit (.strVal f) := fE | none
  guard (rhs.isAppOfArity ``Option.some 2)
  return (f, fE, rhs.appArg!, bs?)

/-- `checkerProg`'s element at position `n`, by `whnf` of its chunk. -/
def chkElem (n : Nat) : MetaM Lean.Expr := do
  let c := mkConst (``checkerProg ++ Name.mkSimple s!"chunk{n / chkChunk}")
  let mut l ← whnfD c
  for _ in [0:n % chkChunk] do l ← whnfD l.appArg!
  unless l.isAppOfArity ``List.cons 3 do throwError "chk_lk: no element {n}"
  return l.appFn!.appArg!

/-- Close a lookup goal by its position: in `checkerProg` (`lk_of_idx`); in the substituted
program, a function that reads no pin data by `lkN` (its `noPB` decided), a reader by `lkR` (its
substituted body by `rfl`). -/
def chkLookup (idx : ChkIdx) (g : MVarId) (f : String) (fE fd : Lean.Expr)
    (bs? : Option Lean.Expr) : MetaM Unit := do
  let some n := idx.pos[f]? | throwError "chk_lk: {f} is not a function of checkerProg"
  let elemTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkConst ``FunDecl)
  let progTy := mkConst ``Prog
  let c := mkConst (``checkerProg ++ Name.mkSimple s!"chunk{n / chkChunk}")
  let hc := mkApp2 (mkConst ``Eq.refl [1]) (mkApp (mkConst ``Option [0]) progTy)
    (mkApp2 (mkConst ``Option.some [0]) progTy c)
  let hIdx (fd : Lean.Expr) :=
    let some_ := mkApp2 (mkConst ``Option.some [0]) elemTy
      (mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String) (mkConst ``FunDecl) fE fd)
    mkAppN (mkConst ``lk_of_chunk) #[mkNatLit (n / chkChunk), mkNatLit (n % chkChunk), c, fE, fd,
      hc, mkApp2 (mkConst ``Eq.refl [1]) (mkApp (mkConst ``Option [0]) elemTy) some_]
  match bs? with
  | none => g.assign (hIdx fd)
  | some bs =>
    if idx.noPB[f]?.getD false then
      g.assign (mkAppN (mkConst ``lkN) #[bs, fE, fd, hIdx fd,
        mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)])
    else
      let fc := (← chkElem n).appArg!
      g.assign (mkAppN (mkConst ``lkR) #[bs, fE, fc, fd, hIdx fc,
        mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``FunDecl) fd])

elab "chk_lk" : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let some (f, fE, fd, bs?) := lookupGoal? ty | throwError "chk_lk: not a checkerProg lookup: {ty}"
  chkLookup (← unsafe chkIdx) g f fE fd bs?
  replaceMainGoal []

/-- Close a bundle goal (see the module doc). -/
partial def bundle (idx : ChkIdx) (hs : Array Lean.Expr)
    (memo : IO.Ref (Std.HashMap Lean.Expr Lean.Expr)) (g : MVarId) : MetaM Unit := do
  let ty ← instantiateMVars (← g.getType)
  let ty := ty.cleanupAnnotations.headBeta
  if let some pf := (← memo.get)[ty]? then g.assign pf; return
  bundleGo idx hs memo g ty
  memo.modify (·.insert ty (.mvar g))
where
  bundleGo idx hs memo (g : MVarId) (ty : Lean.Expr) : MetaM Unit := do
  for h in hs do
    if (← instantiateMVars (← inferType h)) == ty then g.assign h; return
  if let some (f, fE, fd, bs?) := lookupGoal? ty then return ← chkLookup idx g f fE fd bs?
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
