module

public import Lean
public import ConAgua.Compiler.AsmLit
public import ConAguaX86.Compiler.CompileX64
public import ConAguaX86.AsmFile.Term
public meta import Lean
public meta import ConAgua.Compiler.AsmLit
public meta import ConAguaX86.Compiler.CompileX64
public meta import ConAguaX86.AsmFile.Term

@[expose] public section

/-!
# The compiler's output as a kernel-checked literal

`asm_lit name : tab nrt skt p entry` declares `name : Program`, a literal (constructor applications),
and `name_eq : compileProg tab p entry = name`, checked by the kernel; with a trailing `asm X` (a
table of hand-written bodies, `AsmTab`), `name_eq : compileProgX X tab p entry = name`. DESIGN.md, "Kernel-checked
compiler output". `nrt` is a constant holding `Prog.nrt p` as a literal, with `nrt_eq : Prog.nrt p =
nrt` (`nrt_lit`, `WFSplit.lean`): the result counts of the functions, which every call site looks up.
Likewise `skt` holds `Prog.skt p entry`, with `skt_eq` (`skt_lit`): the frames of the leaves without
a stack check, which every function's stack check looks up.

* **The literal.** Each function's code is computed by compiled code (`compileFn`, evaluated
  here) and turned back into a term (`toExpr`, Kraken's derived instances), with every label
  string replaced by the term that names it: `lbl f n m` (a local label: the function's name,
  the node's position as a `Nat` literal, the marker), `fnL g` (a function's entry), `errorL`,
  `exhaustedL`, `finishL`, `enterL`. The kernel never computes a string. How the literal was
  found does not matter: the kernel checks it.
* **Per function** `name.f<i> : Program` (the code of the `i`-th function, a balanced `++` of
  list literals of at most 64 directives, so that the term stays shallow) and
  `name.f<i>_eq : fnCode X tab nrt skt f fd = name.f<i>`, by `Eq.refl`: the kernel evaluates
  `fnCode` (the compiler, or the lookup in `X`) on that function and compares. The equations of `asmLitBatch` consecutive
  functions are one kernel check (`name.f<j>_batch`, their conjunction; each `_eq` a projection
  of it), so that what they share is evaluated once: a long `ldc` string's `romIdx` (the 110
  prelude copies read a 15 700-byte string: ~5 s per check). The trampoline: `name.tramp`, `name.tramp_eq`.
* **The whole program**: `name := name.tramp ++ (name.f0 ++ (name.f1 ++ … ++ []))`, and
  `name_eq` from the per-function equations by `List.flatMap_cons` and congruence, without
  evaluation, and `nrt_eq`, `skt_eq`.

The table must be cheap to unfold (a literal: `tab_lit%`); the program must reduce to a list
literal by `whnf`.
-/

namespace L.Compiler

open Lean Elab Command Meta
open Lean.Elab.Term (elabTermEnsuringType synthesizeSyntheticMVarsNoPostponing)

meta unsafe def evalProgramU (e : Lean.Expr) : MetaM Program :=
  evalExpr Program (mkApp (mkConst ``List [0]) (mkConst ``Directive)) e
@[implemented_by evalProgramU] meta opaque evalProgram (e : Lean.Expr) : MetaM Program

/-- The code of every function of `p`. -/
def progCode (X : AsmTab) (tab : Tab) (t sk : NTree) (p : Prog) : List Program := p.map fun x => fnCode X tab t sk x.1 x.2

meta unsafe def evalProgramsU (e : Lean.Expr) : MetaM (List Program) :=
  evalExpr (List Program) (mkApp (mkConst ``List [0]) (mkApp (mkConst ``List [0]) (mkConst ``Directive))) e
@[implemented_by evalProgramsU] meta opaque evalPrograms (e : Lean.Expr) : MetaM (List Program)

/-- Declare `n : Program := lit` (not compiled: nothing runs it); the equation `lhs = n` is left to
the caller. -/
meta def declLitDef (n : Name) (f : String) (v : Program) : MetaM Unit := do
  let lit := programExpr (v.toArray.map (directiveExpr f))
  withExporting <| addDecl (.defnDecl (mkDefinitionValEx n [] progTy lit .abbrev .safe []))

/-- Declare `n : Program := lit` and `n_eq : lhs = n` by `Eq.refl` (the kernel evaluates `lhs`). -/
meta def declLit (n : Name) (lhs : Lean.Expr) (f : String) (v : Program) : MetaM Unit := do
  declLitDef n f v
  addDecl (.thmDecl { name := n.appendAfter "_eq", levelParams := [], type := mkApp3 (mkConst ``Eq [1]) progTy lhs (mkConst n)
                      value := mkApp2 (mkConst ``Eq.refl [1]) progTy lhs })

meta register_option asmLitBatch : Nat := {
  defValue := 16
  descr := "asm_lit: functions per kernel check (one conjunction; the kernel evaluates what the \
    functions share, such as a long `ldc` string's `romIdx`, once per check)"
}

/-- Declare the equations `lhsᵢ = nᵢ` (`nᵢ_eq`) of a batch by one kernel check: `name` proves
their conjunction by `Eq.refl`s, and each `nᵢ_eq` is a projection of it (no evaluation). -/
meta def declEqBatch (name : Name) (eqs : Array (Name × Lean.Expr)) : MetaM Unit := do
  if eqs.isEmpty then return
  let tys := eqs.map fun (n, lhs) => mkApp3 (mkConst ``Eq [1]) progTy lhs (mkConst n)
  let pfs := eqs.map fun (_, lhs) => mkApp2 (mkConst ``Eq.refl [1]) progTy lhs
  -- `T₀ ∧ (T₁ ∧ … ∧ Tₖ)` and its proof
  let k := eqs.size - 1
  let mut conj := tys[k]!
  let mut pf := pfs[k]!
  let mut tails : Array Lean.Expr := #[conj]  -- tails[j] = Tₖ₋ⱼ ∧ … ∧ Tₖ
  for j in (List.range k).reverse do
    pf := mkApp4 (mkConst ``And.intro) tys[j]! conj pfs[j]! pf
    conj := mkApp2 (mkConst ``And) tys[j]! conj
    tails := tails.push conj
  addDecl (.thmDecl { name, levelParams := [], type := conj, value := pf })
  -- `tail j` = `Tⱼ ∧ … ∧ Tₖ`
  let tail (j : Nat) : Lean.Expr := tails[k - j]!
  let mut h := mkConst name  -- : tail 0
  for j in List.range (k + 1) do
    let pj := if j == k then h else mkApp3 (mkConst ``And.left) tys[j]! (tail (j + 1)) h
    addDecl (.thmDecl { name := eqs[j]!.1.appendAfter "_eq", levelParams := [], type := tys[j]!, value := pj })
    if j < k then h := mkApp3 (mkConst ``And.right) tys[j]! (tail (j + 1)) h

/-- Declare `name.f<i>` and `name.f<i>_eq` for the functions `lo ≤ i < hi` of `p` (`elems`), except
those already declared (by `asm_lit_fns` in an imported module). -/
meta def declFns (name : Name) (XE tabE nrtE sktE pE : Lean.Expr) (elems : Array Lean.Expr) (lo hi : Nat) :
    MetaM (Array Name) := do
  let hi := min hi elems.size
  let env ← getEnv
  let todo := (List.range (hi - lo)).map (· + lo) |>.filter fun i =>
    !env.contains (name ++ Name.mkSimple s!"f{i}")
  let mut codes : Array Program := #[]
  if let some i0 := todo.head? then
    -- the code of functions `i0 … hi - 1`, by compiled code in one evaluation
    let slice := mkApp3 (mkConst ``List.take [0]) (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkConst ``FunDecl))
      (mkRawNatLit (hi - i0)) (mkApp3 (mkConst ``List.drop [0]) (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String)
        (mkConst ``FunDecl)) (mkRawNatLit i0) pE)
    codes := (← evalPrograms (mkApp5 (mkConst ``progCode) XE tabE nrtE sktE slice)).toArray
    let b := max 1 (asmLitBatch.get (← getOptions))
    let mut batch : Array (Name × Lean.Expr) := #[]
    for i in todo do
      let (f, fE, fdE) ← progElem i elems[i]!
      let n := name ++ Name.mkSimple s!"f{i}"
      declLitDef n f codes[i - i0]!
      batch := batch.push (n, mkApp6 (mkConst ``fnCode) XE tabE nrtE sktE fE fdE)
      if batch.size ≥ b then
        declEqBatch (n.appendAfter "_batch") batch
        batch := #[]
    if let some (n, _) := batch.back? then declEqBatch (n.appendAfter "_batch") batch
  return (List.range (hi - lo)).toArray.map fun i => name ++ Name.mkSimple s!"f{i + lo}"

/-- The table of hand-written bodies of an `asm X` clause, or `[]`. -/
meta def elabAsmTab (xS? : Option Term) : TermElabM Lean.Expr := do
  match xS? with
  | some xS => elabTermEnsuringType xS (mkConst ``AsmTab)
  | none => return mkApp (mkConst ``List.nil [0]) (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) progTy)

/-- `asm_lit_fns name : tab nrt skt p lo hi`: the per-function literals and equations of `asm_lit name`
for the functions `lo ≤ i < hi` only, so that a large program's checks can be spread over several
modules (built in parallel); `asm_lit` then skips them. -/
syntax (name := asmLitFns) "asm_lit_fns " ident " : " term:max term:max term:max term:max num num (" asm " term:max)? : command

@[command_elab asmLitFns] meta def elabAsmLitFns : CommandElab := fun stx => do
  let `(asm_lit_fns $n:ident : $tabS $nrtS $sktS $progS $lo $hi $[asm $xS?]?) := stx | throwUnsupportedSyntax
  let name := (← getCurrNamespace) ++ n.getId
  liftTermElabM <| withTheReader Core.Context (fun c => { c with maxRecDepth := max c.maxRecDepth 100000, maxHeartbeats := 0 }) do
    let tabE ← elabTermEnsuringType tabS (mkConst ``Tab)
    let nrtE ← elabTermEnsuringType nrtS (mkConst ``NTree)
    let sktE ← elabTermEnsuringType sktS (mkConst ``NTree)
    let pE ← elabTermEnsuringType progS (mkConst ``Prog)
    let XE ← elabAsmTab xS?
    synthesizeSyntheticMVarsNoPostponing
    let tabE ← instantiateMVars tabE
    let nrtE ← instantiateMVars nrtE
    let sktE ← instantiateMVars sktE
    let pE ← instantiateMVars pE
    let XE ← instantiateMVars XE
    discard <| declFns name XE tabE nrtE sktE pE (← listElemsW pE) lo.getNat hi.getNat

/-- `asm_lit name : tab nrt skt p entry` (`nrt` a constant, with `nrt_eq : Prog.nrt p = nrt`; `skt` a
constant, with `skt_eq : Prog.skt p entry = skt`) -/
syntax (name := asmLit) (docComment)? "asm_lit " ident " : " term:max ident ident term:max term:max (" asm " term:max)? : command

@[command_elab asmLit] meta def elabAsmLit : CommandElab := fun stx => do
  let `($[$doc?:docComment]? asm_lit $n:ident : $tabS $nrtS:ident $sktS:ident $progS $entryS $[asm $xS?]?) := stx | throwUnsupportedSyntax
  let name := (← getCurrNamespace) ++ n.getId
  liftTermElabM <| withTheReader Core.Context (fun c => { c with maxRecDepth := max c.maxRecDepth 100000, maxHeartbeats := 0 }) do
    let tabE ← elabTermEnsuringType tabS (mkConst ``Tab)
    let nrtN ← realizeGlobalConstNoOverload nrtS
    let nrtE := mkConst nrtN
    let nrtEqE := mkConst (nrtN.appendAfter "_eq")
    let sktN ← realizeGlobalConstNoOverload sktS
    let sktE := mkConst sktN
    let sktEqE := mkConst (sktN.appendAfter "_eq")
    let pE ← elabTermEnsuringType progS (mkConst ``Prog)
    let entryE ← elabTermEnsuringType entryS (mkConst ``String)
    let XE ← elabAsmTab xS?
    synthesizeSyntheticMVarsNoPostponing
    let tabE ← instantiateMVars tabE
    let pE ← instantiateMVars pE
    let entryE ← instantiateMVars entryE
    let XE ← instantiateMVars XE
    -- `compileFns X tab nrt skt p`, unfolded once: `List.flatMap g p`
    let some (.defnInfo ci) := (← getEnv).find? ``compileFns | throwError "compileFns"
    let flatE := ci.value.beta #[XE, tabE, nrtE, sktE, pE]
    unless flatE.isAppOfArity ``List.flatMap 4 do throwError "asm_lit: unexpected shape of compileFns: {flatE}"
    let g := flatE.appFn!.appArg!
    let elemTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkConst ``FunDecl)
    -- the trampoline
    let trampN := name ++ `tramp
    let trE := mkApp4 (mkConst ``trampoline) tabE entryE (mkApp3 (mkConst ``nrOf) nrtE tabE entryE)
      (mkApp2 (mkConst ``entryNp) pE entryE)
    declLit trampN trE "" (← evalProgram trE)
    -- the functions (those not declared yet by `asm_lit_fns`)
    let elems ← listElemsW pE
    let fnNames ← declFns name XE tabE nrtE sktE pE elems 0 elems.size
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
    withExporting <| addDecl (.defnDecl (mkDefinitionValEx name [] progTy whole .abbrev .safe []))
    addDocString' name .missing doc?
    -- `compileProgT X tab nrt skt p entry = name`: `p` unfolds to the literal `tl`
    let appC := mkApp4 (mkConst ``HAppend.hAppend [0, 0, 0]) progTy progTy progTy
      (mkApp2 (mkConst ``instHAppendOfAppend [0]) progTy (mkApp (mkConst ``List.instAppend [0]) dirTy))
    let progTo := mkForall `_ .default progTy progTy
    let h1 := mkApp6 (mkConst ``congrArg [1, 1]) progTy progTo trE (mkConst trampN) appC (mkConst (trampN.appendAfter "_eq"))
    let flatP := mkApp4 (mkConst ``List.flatMap [0, 0]) elemTy dirTy g tl
    let top := mkApp8 (mkConst ``congr [1, 1]) progTy progTy (mkApp appC trE) (mkApp appC (mkConst trampN)) flatP rhs h1 pf
    let progTE := mkApp6 (mkConst ``compileProgT) XE tabE nrtE sktE pE entryE
    let topN := name ++ `progT_eq
    addDecl (.thmDecl { name := topN, levelParams := [], type := mkApp3 (mkConst ``Eq [1]) progTy progTE (mkConst name),
                        value := top })
    -- `compileProgX X tab p entry = compileProgT X tab (Prog.nrt p) (Prog.skt p entry) p entry
    --   = compileProgT X tab nrt skt p entry` (without `asm X`: `compileProg tab p entry`, the same
    -- by unfolding)
    let treeTy := mkConst ``NTree
    let progOf ← withLocalDeclD `t treeTy fun t => withLocalDeclD `s treeTy fun s =>
      mkLambdaFVars #[t, s] (mkApp6 (mkConst ``compileProgT) XE tabE t s pE entryE)
    let nrtP := mkApp (mkConst ``Prog.nrt) pE
    let sktP := mkApp2 (mkConst ``Prog.skt) pE entryE
    let treeTo := mkForall `_ .default treeTy progTy
    -- `progOf (Prog.nrt p) = progOf nrt`, then applied to `Prog.skt p entry = skt`
    let hN1 := mkApp6 (mkConst ``congrArg [1, 1]) treeTy treeTo nrtP nrtE progOf nrtEqE
    let hN := mkApp8 (mkConst ``congr [1, 1]) treeTy progTy (mkApp progOf nrtP) (mkApp progOf nrtE) sktP sktE
      hN1 sktEqE
    let lhs := if xS?.isSome then mkApp4 (mkConst ``compileProgX) XE tabE pE entryE
      else mkApp3 (mkConst ``compileProg) tabE pE entryE
    let eqTy := mkApp3 (mkConst ``Eq [1]) progTy lhs (mkConst name)
    let whole := mkApp6 (mkConst ``Eq.trans [1]) progTy lhs progTE
      (mkConst name) hN (mkConst topN)
    addDecl (.thmDecl { name := name.appendAfter "_eq", levelParams := [], type := eqTy, value := whole })
where
  appE (appC a b : Lean.Expr) : Lean.Expr := mkApp2 appC a b

end L.Compiler
