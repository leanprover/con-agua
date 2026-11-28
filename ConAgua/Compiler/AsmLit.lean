module

public import Lean
public meta import Lean

@[expose] public section

namespace L.Compiler

open Lean Meta

meta partial def listElemsW (e : Lean.Expr) (acc : Array Lean.Expr := #[]) : MetaM (Array Lean.Expr) := do
  let e ← whnfD e
  if e.isAppOfArity ``List.cons 3 then listElemsW e.appArg! (acc.push e.appFn!.appArg!)
  else if e.isAppOfArity ``List.nil 1 then return acc
  else throwError "listElemsW: the program does not reduce to a list literal: {e}"

meta def progElem (i : Nat) (x : Lean.Expr) : MetaM (String × Lean.Expr × Lean.Expr) := do
  let x ← whnfD x
  unless x.isAppOfArity ``Prod.mk 4 do throwError "progElem: element {i} is not a pair: {x}"
  let fE := x.appFn!.appArg!
  let .lit (.strVal f) ← whnfD fE | throwError "progElem: the name of element {i} is not a literal: {fE}"
  return (f, fE, x.appArg!)

end L.Compiler
