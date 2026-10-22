import Lean
import ConAgua.Compiler.Compile

/-!
# The compiler's output as a kernel-checked literal

`asm_lit name : tab p entry` declares `name : Program`, a literal (constructor applications), and
`name_eq : compileProg tab p entry = name`, checked by the kernel. DESIGN.md, "Kernel-checked
compiler output".

* **The literal.** Each function's code is computed by compiled code (`compileFn`, evaluated
  here) and turned back into a term (`toExpr`, Kraken's derived instances), with every label
  string replaced by the term that names it: `lbl f n m` (a local label: the function's name,
  the node's position as a `Nat` literal, the marker), `fnL g` (a function's entry), `errorL`,
  `exhaustedL`, `finishL`, `enterL`. The kernel never computes a string. How the literal was
  found does not matter: the kernel checks it.
* **Per function** `name.f<i> : Program` (the code of the `i`-th function, a balanced `++` of
  list literals of at most 64 directives, so that the term stays shallow) and
  `name.f<i>_eq : compileFn tab f fd = name.f<i>`, by `Eq.refl`: the kernel evaluates
  `compileFn` on that one function and compares. The trampoline: `name.tramp`, `name.tramp_eq`.
* **The whole program**: `name := name.tramp ++ (name.f0 ++ (name.f1 ++ … ++ []))`, and
  `name_eq` from the per-function equations by `List.flatMap_cons` and congruence, without
  evaluation.

The table must be cheap to unfold (a literal: `tab_lit%`); the program must reduce to a list
literal by `whnf`.
-/

namespace L.Compiler

open Lean Elab Command Meta
open Lean.Elab.Term (elabTermEnsuringType synthesizeSyntheticMVarsNoPostponing)

unsafe def evalProgramU (e : Lean.Expr) : MetaM Program :=
  evalExpr Program (mkApp (mkConst ``List [0]) (mkConst ``Directive)) e
@[implemented_by evalProgramU] opaque evalProgram (e : Lean.Expr) : MetaM Program

/-- The term for a label of function `f`'s code. -/
def labelExpr (f : String) (s : String) : Lean.Expr := Id.run do
  if s == errorL then return mkConst ``errorL
  if s == exhaustedL then return mkConst ``exhaustedL
  if s == finishL then return mkConst ``finishL
  if s == enterL then return mkConst ``enterL
  if s.startsWith "ca_f_" then return mkApp (mkConst ``fnL) (mkStrLit (s.drop 5).toString)
  let pre := ".Lca_" ++ f ++ "_"
  if s.startsWith pre then
    let rest := (s.drop pre.length).toString
    let ds := (rest.takeWhile Char.isDigit).toString
    let m := (rest.drop ds.length).toString
    if ds != "" && m != "" && m.all Char.isUpper then
      return mkApp3 (mkConst ``lbl) (mkStrLit f) (mkRawNatLit ds.toNat!) (mkStrLit m)
  return mkStrLit s

/-- A directive as a term, its labels as `labelExpr`. -/
def directiveExpr (f : String) (d : Directive) : Lean.Expr :=
  (toExpr d).replace fun
    | .lit (.strVal s) => some (labelExpr f s)
    | _ => none

def dirTy : Lean.Expr := mkConst ``Directive
def progTy : Lean.Expr := mkApp (mkConst ``List [0]) dirTy

def appendE (a b : Lean.Expr) : Lean.Expr :=
  mkApp6 (mkConst ``HAppend.hAppend [0, 0, 0]) progTy progTy progTy
    (mkApp2 (mkConst ``instHAppendOfAppend [0]) progTy (mkApp (mkConst ``List.instAppend [0]) dirTy)) a b

/-- A list literal as a balanced tree of `++` over chunks of at most 64 elements (a long list
literal is a term of linear depth). -/
partial def programExpr (xs : Array Lean.Expr) : Lean.Expr :=
  if xs.size ≤ 64 then
    xs.foldr (fun d acc => mkApp3 (mkConst ``List.cons [0]) dirTy d acc) (mkApp (mkConst ``List.nil [0]) dirTy)
  else
    let h := (xs.size / 64 + 1) / 2 * 64
    appendE (programExpr (xs.extract 0 h)) (programExpr (xs.extract h xs.size))

/-- The elements of a list expression, by `whnf`. -/
partial def listElemsW (e : Lean.Expr) (acc : Array Lean.Expr := #[]) : MetaM (Array Lean.Expr) := do
  let e ← whnfD e
  if e.isAppOfArity ``List.cons 3 then listElemsW e.appArg! (acc.push e.appFn!.appArg!)
  else if e.isAppOfArity ``List.nil 1 then return acc
  else throwError "asm_lit: the program does not reduce to a list literal: {e}"

/-- Declare `n : Program := lit` (compiled, so that the printer can run it) and
`n_eq : lhs = n` by `Eq.refl` (the kernel evaluates `lhs`). -/
def declLit (n : Name) (lhs : Lean.Expr) (f : String) : MetaM Unit := do
  let v ← evalProgram lhs
  let lit := programExpr (v.toArray.map (directiveExpr f))
  addAndCompile (.defnDecl (mkDefinitionValEx n [] progTy lit .abbrev .safe []))
  addDecl (.thmDecl { name := n.appendAfter "_eq", levelParams := [], type := mkApp3 (mkConst ``Eq [1]) progTy lhs (mkConst n)
                      value := mkApp2 (mkConst ``Eq.refl [1]) progTy lhs })

/-- `asm_lit name : tab p entry` -/
syntax (name := asmLit) (docComment)? "asm_lit " ident " : " term:max term:max term:max : command

@[command_elab asmLit] def elabAsmLit : CommandElab := fun stx => do
  let `($[$doc?:docComment]? asm_lit $n:ident : $tabS $progS $entryS) := stx | throwUnsupportedSyntax
  let name := (← getCurrNamespace) ++ n.getId
  liftTermElabM <| withTheReader Core.Context (fun c => { c with maxRecDepth := max c.maxRecDepth 100000, maxHeartbeats := 0 }) do
    let tabE ← elabTermEnsuringType tabS (mkConst ``Tab)
    let pE ← elabTermEnsuringType progS (mkConst ``Prog)
    let entryE ← elabTermEnsuringType entryS (mkConst ``String)
    synthesizeSyntheticMVarsNoPostponing
    let tabE ← instantiateMVars tabE
    let pE ← instantiateMVars pE
    let entryE ← instantiateMVars entryE
    -- `compileProg tab p entry`, unfolded once: `trampoline tab entry ++ List.flatMap g p`
    let some (.defnInfo ci) := (← getEnv).find? ``compileProg | throwError "compileProg"
    let body := ci.value.beta #[tabE, pE, entryE]
    unless body.isAppOfArity ``HAppend.hAppend 6 do throwError "asm_lit: unexpected shape of compileProg: {body}"
    let flatE := body.appArg!
    unless flatE.isAppOfArity ``List.flatMap 4 do throwError "asm_lit: unexpected shape of compileProg: {flatE}"
    let g := flatE.appFn!.appArg!
    let elemTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkConst ``FunDecl)
    -- the trampoline
    let trampN := name ++ `tramp
    declLit trampN (mkApp2 (mkConst ``trampoline) tabE entryE) ""
    -- the functions
    let elems ← listElemsW pE
    let mut fnNames : Array Name := #[]
    for h : i in [0:elems.size] do
      let x ← whnfD elems[i]
      unless x.isAppOfArity ``Prod.mk 4 do throwError "asm_lit: element {i} is not a pair: {x}"
      let fE := x.appFn!.appArg!
      let .lit (.strVal f) ← whnfD fE | throwError "asm_lit: the name of element {i} is not a literal: {fE}"
      let fN := name ++ Name.mkSimple s!"f{i}"
      declLit fN (mkApp3 (mkConst ``compileFn) tabE fE x.appArg!) f
      fnNames := fnNames.push fN
    -- `name := tramp ++ (f0 ++ (f1 ++ … ++ []))`, and `flatMap g p = f0 ++ (f1 ++ … ++ [])`
    let nil := mkApp (mkConst ``List.nil [0]) dirTy
    let mut rhs := nil
    let mut tl := mkApp (mkConst ``List.nil [0]) elemTy
    let mut pf := mkApp2 (mkConst ``Eq.refl [1]) progTy nil
    for i in (List.range elems.size).reverse do
      let fi := mkConst fnNames[i]!
      let xi := elems[i]!
      let hi := mkConst (fnNames[i]!.appendAfter "_eq")
      let flatTl := mkApp4 (mkConst ``List.flatMap [0, 0]) elemTy dirTy g tl
      -- `g xi ++ flatMap g tl = fi ++ rhs`
      let appC := mkApp4 (mkConst ``HAppend.hAppend [0, 0, 0]) progTy progTy progTy
        (mkApp2 (mkConst ``instHAppendOfAppend [0]) progTy (mkApp (mkConst ``List.instAppend [0]) dirTy))
      let progTo := mkForall `_ .default progTy progTy
      -- congrArg (f := appC) (a₁ := g xi) (a₂ := fi) hi : appC (g xi) = appC fi
      let h1 := mkApp6 (mkConst ``congrArg [1, 1]) progTy progTo (mkApp g xi) fi appC hi
      -- congr h1 pf : appC (g xi) (flatMap g tl) = appC fi rhs
      let h2 := mkApp8 (mkConst ``congr [1, 1]) progTy progTy (mkApp appC (mkApp g xi)) (mkApp appC fi)
        flatTl rhs h1 pf
      let consTl := mkApp3 (mkConst ``List.cons [0]) elemTy xi tl
      -- flatMap_cons : flatMap g (xi :: tl) = g xi ++ flatMap g tl
      let h0 := mkApp5 (mkConst ``List.flatMap_cons [0, 0]) elemTy dirTy xi tl g
      pf := mkApp6 (mkConst ``Eq.trans [1]) progTy (mkApp4 (mkConst ``List.flatMap [0, 0]) elemTy dirTy g consTl)
        (appE appC (mkApp g xi) flatTl) (appE appC fi rhs) h0 h2
      rhs := appE appC fi rhs
      tl := consTl
    let whole := appendE (mkConst trampN) rhs
    addAndCompile (.defnDecl (mkDefinitionValEx name [] progTy whole .abbrev .safe []))
    addDocString' name .missing doc?
    -- `compileProg tab p entry = name`: `p` unfolds to the literal `tl`
    let eqTy := mkApp3 (mkConst ``Eq [1]) progTy (mkApp3 (mkConst ``compileProg) tabE pE entryE) (mkConst name)
    let appC := mkApp4 (mkConst ``HAppend.hAppend [0, 0, 0]) progTy progTy progTy
      (mkApp2 (mkConst ``instHAppendOfAppend [0]) progTy (mkApp (mkConst ``List.instAppend [0]) dirTy))
    let progTo := mkForall `_ .default progTy progTy
    let tr := mkApp2 (mkConst ``trampoline) tabE entryE
    let h1 := mkApp6 (mkConst ``congrArg [1, 1]) progTy progTo tr (mkConst trampN) appC (mkConst (trampN.appendAfter "_eq"))
    let flatP := mkApp4 (mkConst ``List.flatMap [0, 0]) elemTy dirTy g tl
    let top := mkApp8 (mkConst ``congr [1, 1]) progTy progTy (mkApp appC tr) (mkApp appC (mkConst trampN)) flatP rhs h1 pf
    addDecl (.thmDecl { name := name.appendAfter "_eq", levelParams := [], type := eqTy, value := top })
where
  appE (appC a b : Lean.Expr) : Lean.Expr := mkApp2 appC a b

end L.Compiler
