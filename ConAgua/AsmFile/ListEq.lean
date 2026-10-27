import ConAgua.AsmFile.Term
import Lean.Elab.Command
import Std.Do.Triple.SpecLemmas

/-!
# `a = lit` for a long program literal, in kernel-sized pieces (not trusted)

`list_eq name : lit = a` proves that the constant `lit` equals the program `a` (any term that
evaluates to a list), where `lit`, whose value is a balanced `++` tree of list literals (`programExpr`,
`ConAgua/AsmFile/Term.lean`). One `Eq.refl` overflows the kernel's stack on a long list (the
kernel compares lists element by element, recursively); this splits along the literal's tree,
`a = take k a ++ drop k a`, down to pieces of at most `leaf` directives, each by `Eq.refl` (lane
asmfile's code, docs/design/asmfile.md).
-/

namespace L.Compiler

open Lean Elab Command Meta

/-- The number of directives of a literal tree. -/
partial def litLen (e : Lean.Expr) : Nat :=
  if e.isAppOfArity ``HAppend.hAppend 6 then litLen e.appFn!.appArg! + litLen e.appArg!
  else if e.isAppOfArity ``List.cons 3 then 1 + litLen e.appArg!
  else 0

/-- A proof of `t = lit`, split along `lit`'s `++` tree into pieces of at most `leaf` elements;
the pieces of the top `sep` levels are separate theorems `base.i` (so that the kernel's caches do
not pile up across the whole list). -/
partial def listEqProof (base : Name) (leaf sep : Nat) (t lit : Lean.Expr) : StateT Nat CoreM Lean.Expr := do
  let appC := mkApp4 (mkConst ``HAppend.hAppend [0, 0, 0]) progTy progTy progTy
    (mkApp2 (mkConst ``instHAppendOfAppend [0]) progTy (mkApp (mkConst ``List.instAppend [0]) dirTy))
  let refl := mkApp2 (mkConst ``Eq.refl [1]) progTy t
  if lit.isAppOfArity ``HAppend.hAppend 6 && litLen lit > leaf then
    let a := lit.appFn!.appArg!
    let b := lit.appArg!
    let k := mkRawNatLit (litLen a)
    let tk := mkApp3 (mkConst ``List.take [0]) dirTy k t
    let td := mkApp3 (mkConst ``List.drop [0]) dirTy k t
    let split := mkApp2 appC tk td
    let hs := mkApp4 (mkConst ``Eq.symm [1]) progTy split t
      (mkApp3 (mkConst ``List.take_append_drop [0]) dirTy k t)
    let piece (x y : Lean.Expr) : StateT Nat CoreM Lean.Expr := do
      let p ← listEqProof base leaf (sep - 1) x y
      if sep = 0 then return p
      let i ← modifyGet fun i => (i, i + 1)
      let n := base.appendIndexAfter i
      addDecl (.thmDecl { name := n, levelParams := [], type := mkApp3 (mkConst ``Eq [1]) progTy x y, value := p })
      return mkConst n
    let ha ← piece tk a
    let hb ← piece td b
    let hc := mkApp8 (mkConst ``congr [1, 1]) progTy progTy (mkApp appC tk) (mkApp appC a) td b
      (mkApp6 (mkConst ``congrArg [1, 1]) progTy (mkForall `x .default progTy progTy) tk a appC ha) hb
    return mkApp6 (mkConst ``Eq.trans [1]) progTy t split lit hs hc
  else return refl

syntax (name := listEqCmd) (docComment)? "list_eq " ident " : " ident " = " term : command

@[command_elab listEqCmd] def elabListEq : CommandElab := fun stx => do
  let `($[$doc?:docComment]? list_eq $n:ident : $litS:ident = $a:term) := stx | throwUnsupportedSyntax
  let name := (← getCurrNamespace) ++ n.getId
  liftTermElabM do
    let litN ← realizeGlobalConstNoOverload litS
    let some litV := (← getConstInfo litN).value? | throwError "list_eq: {litN} has no value"
    let a ← Term.elabTermEnsuringType a progTy
    let a ← instantiateMVars a
    let ty := mkApp3 (mkConst ``Eq [1]) progTy (mkConst litN) a
    -- `a = litV` by pieces (`litV = lit` by delta), then symmetry
    let (p, _) ← (StateT.run (listEqProof (name ++ `piece) 8192 1 a litV) (0 : Nat) : CoreM _)
    let pf := mkApp4 (mkConst ``Eq.symm [1]) progTy a (mkConst litN) p
    addDecl (.thmDecl { name, levelParams := [], type := ty, value := pf })
    addDocString' name .missing doc?

end L.Compiler
