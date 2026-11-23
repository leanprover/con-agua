module

public import ConAgua.AsmFile.Term
public import ConAgua.Compiler.Compile
public import Lean.Elab.Command
public import Std.Do.Triple.SpecLemmas
public meta import ConAgua.AsmFile.Term
public meta import ConAgua.Compiler.Compile
public meta import Lean.Elab.Command
public meta import Std.Do.Triple.SpecLemmas

@[expose] public section

/-!
# The file's code is the compiler's output (kernel-checked; not trusted)

`asm_file_eq name : file = stub ++ code via code_eq`, where `file` is a constant whose value is
`include_asm`'s term `S ++ R` (`S` the file's first segment: the code before the trampoline),
`code` a constant built by `asm_lit` (e.g. `checkerAsm`) and `code_eq : rhs = code` (e.g.
`checkerAsm_eq : compileProg … = checkerAsm`), declares

* `stub : Program := S`, the file's code before the trampoline, as a literal (unless `asm_stub stub :
  file` declared it already, in an imported module);
* `name.lit : file = stub ++ code`, by `Eq.refl`: the file's remaining segments and `code` are the
  same terms (`include_asm` and `asm_lit` build them with the same functions,
  `ConAgua/AsmFile/Term.lean`), so the kernel compares them structurally, without evaluating;
* `name : file = stub ++ rhs`, from `name.lit` and `code_eq`.

Before handing the terms to the kernel, the segments are compared here, so that a file that is not
the compiler's output (stale, or printed wrongly) fails with the first differing function named,
not with a long kernel computation.

What the stub is (lane `abi`'s `abiStub checkerTab`) is checked separately, in pieces
(`checkerStub_eq`, `ConAgua/Checker/AsmStubEq.lean`, by `list_eq`). docs/design/asmfile.md.
-/

namespace L.Compiler

open Lean Elab Command Meta

/-- The operands of `a ++ b` at `Program`, if `e` is one. -/
meta def appendArgs? (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr) :=
  if e.isAppOfArity ``HAppend.hAppend 6 then some (e.appFn!.appArg!, e.appArg!) else none

/-- The segments of a right-nested `s₀ ++ (s₁ ++ … ++ [])`, each constant unfolded once, so that
`asm_lit`'s `code.f<i>` and the file's literals compare as terms. -/
meta partial def segmentsOf (e : Lean.Expr) (acc : Array Lean.Expr := #[]) : MetaM (Array Lean.Expr) := do
  let unfold (e : Lean.Expr) : MetaM Lean.Expr := do
    if e.isConst then return (← getConstInfo e.constName!).value?.getD e else return e
  match appendArgs? e with
  | some (a, b) => segmentsOf b (acc.push (← unfold a))
  | none =>
    if e.isAppOfArity ``List.nil 1 then return acc
    else if e.isConst then segmentsOf (← unfold e) acc
    else throwError "asm_file_eq: not a list of segments: {e}"

/-- The function a segment belongs to (its entry label `fnL g`), for messages. -/
meta def segName (e : Lean.Expr) : String :=
  match e.find? fun x => x.isAppOfArity ``fnL 1 with
  | some x => match x.appArg! with | .lit (.strVal g) => g | _ => "?"
  | none => "the trampoline"

/-- `asm_stub stub : file` declares `stub : Program`, the code of `file` (`include_asm`'s `S ++ R`)
before the trampoline (`S`), as `asm_file_eq` does, in a module of its own: what is checked about
the stub (`checkerStub_eq`) then does not wait for the compiled code (`checkerAsm`). -/
syntax (name := asmStub) (docComment)? "asm_stub " ident " : " ident : command

@[command_elab asmStub] meta def elabAsmStub : CommandElab := fun stx => do
  let `($[$doc?:docComment]? asm_stub $stubS:ident : $fileS:ident) := stx | throwUnsupportedSyntax
  let stubN := (← getCurrNamespace) ++ stubS.getId
  liftTermElabM do
    let fileN ← realizeGlobalConstNoOverload fileS
    let some fileV := (← getConstInfo fileN).value? | throwError "asm_stub: {fileN} has no value"
    let some (sLit, _) := appendArgs? fileV | throwError "asm_stub: {fileN} is not `stub ++ code`"
    withExporting <| addDecl (.defnDecl (mkDefinitionValEx stubN [] progTy sLit .abbrev .safe []))
    addDocString' stubN .missing doc?

/-- The elements of a list literal tree (`programExpr`: `++` of `cons` chains ending in `[]`). -/
meta partial def litElems (e : Lean.Expr) (acc : Array Lean.Expr := #[]) : MetaM (Array Lean.Expr) := do
  if let some (a, b) := appendArgs? e then return ← litElems b (← litElems a acc)
  if e.isAppOfArity ``List.cons 3 then return ← litElems e.appArg! (acc.push e.appFn!.appArg!)
  if e.isAppOfArity ``List.nil 1 then return acc
  if e.isConst then
    if let some v := (← getConstInfo e.constName!).value? then return ← litElems v acc
  throwError "asm_tail: not a list literal: {e}"

/-- The last segment of `file`'s code after the stub (`include_asm`'s term), as elements. -/
meta def lastSegElems (fileN : Name) : MetaM (Array Lean.Expr) := do
  let some fileV := (← getConstInfo fileN).value? | throwError "asm_tail: {fileN} has no value"
  let some (_, rest) := appendArgs? fileV | throwError "asm_tail: {fileN} is not `stub ++ code`"
  let fs ← segmentsOf rest
  let some l := fs.back? | throwError "asm_tail: {fileN} has no code after the stub"
  litElems l

/-- `asm_tail tail : file from "lab"` declares `tail : Program`, the code of `file` from the label
`lab` on, which must be in the file's last segment (code emitted after the compiled functions,
which `include_asm` does not cut off: the compared run's driver, `ConAgua/Compiler/AbiCmp.lean`).
In a module of its own, as `asm_stub`, so that what is checked about the tail does not wait for
the compiled code. `asm_file_eq … ++ code ++ tail` then splits the last segment there. -/
syntax (name := asmTail) (docComment)? "asm_tail " ident " : " ident " from " str : command

@[command_elab asmTail] meta def elabAsmTail : CommandElab := fun stx => do
  let `($[$doc?:docComment]? asm_tail $tS:ident : $fileS:ident from $lab:str) := stx | throwUnsupportedSyntax
  let tN := (← getCurrNamespace) ++ tS.getId
  liftTermElabM do
    let fileN ← realizeGlobalConstNoOverload fileS
    let es ← lastSegElems fileN
    let target := directiveExpr "" (.label lab.getString)
    let some i := es.findIdx? (· == target) | throwError "asm_tail: no label {lab.getString} in the last segment"
    withExporting <| addDecl (.defnDecl (mkDefinitionValEx tN [] progTy (programExpr (es.extract i es.size))
      .abbrev .safe []))
    addDocString' tN .missing doc?

/-- The spine `s₀ ++ (s₁ ++ … ++ [])` of a code term: its heads as written (constants not
unfolded) and unfolded (for comparing with the file), unfolding constants in tail position. -/
meta partial def spineOf (e : Lean.Expr) (acc : Array (Lean.Expr × Lean.Expr) := #[]) :
    MetaM (Array (Lean.Expr × Lean.Expr)) := do
  let unfold (e : Lean.Expr) : MetaM Lean.Expr := do
    if e.isConst then return (← getConstInfo e.constName!).value?.getD e else return e
  match appendArgs? e with
  | some (a, b) => spineOf b (acc.push (a, ← unfold a))
  | none =>
    if e.isAppOfArity ``List.nil 1 then return acc
    else if e.isConst then spineOf (← unfold e) acc
    else throwError "asm_file_eq: not a list of segments: {e}"

syntax (name := asmFileEq) (docComment)? "asm_file_eq " ident " : " ident " = " ident " ++ " ident
  (" ++ " ident)? " via " ident : command

/-- `asm_file_eq name : file = stub ++ code ++ tail via code_eq`: as without `tail`, but the file's last
segment is `code`'s last segment followed by `tail` (declared by `asm_tail`). Declares
`name.lit : file = stub ++ (code ++ tail)` and `name : file = stub ++ (rhs ++ tail)`. The proof
reassociates along the spine (`List.append_assoc`, one step per segment, so the kernel never
evaluates the long list); only the last segment is compared by evaluation (`Eq.refl`). -/
meta def elabAsmFileEqTail (doc? : Option (TSyntax ``Lean.Parser.Command.docComment)) (n fileS stubS codeS tailS codeEqS : Ident) :
    CommandElabM Unit := do
  let ns ← getCurrNamespace
  let name := ns ++ n.getId
  let stubN := ns ++ stubS.getId
  liftTermElabM do
    let fileN ← realizeGlobalConstNoOverload fileS
    let codeN ← realizeGlobalConstNoOverload codeS
    let tailN ← realizeGlobalConstNoOverload tailS
    let codeEqN ← realizeGlobalConstNoOverload codeEqS
    let some fileV := (← getConstInfo fileN).value? | throwError "asm_file_eq: {fileN} has no value"
    let some (sLit, rest) := appendArgs? fileV | throwError "asm_file_eq: {fileN} is not `stub ++ code`"
    let fsp ← spineOf rest
    let csp ← spineOf (mkConst codeN)
    let n := csp.size
    unless fsp.size == n && n > 0 do
      throwError "asm_file_eq: the file has {fsp.size} segments after the stub, {codeN} {n}; regenerate it"
    for i in [0:n - 1] do
      unless fsp[i]!.2 == csp[i]!.2 do
        throwError "asm_file_eq: the file differs from {codeN} in segment {i} ({segName csp[i]!.2}); \
          regenerate it"
    -- the last segment: the code's, then the tail
    let fl ← litElems fsp[n - 1]!.2
    let cl ← litElems csp[n - 1]!.2
    let tl ← litElems (mkConst tailN)
    unless fl == cl ++ tl do
      throwError "asm_file_eq: the file's last segment is not {codeN}'s last segment followed by {tailN}; \
        regenerate it (or rebuild the `asm_tail` module)"
    match (← getEnv).find? stubN with
    | some ci =>
      unless ci.value? == some sLit do
        throwError "asm_file_eq: {stubN} is not the stub of {fileN} (rebuild its `asm_stub` module)"
    | none => withExporting <| addDecl (.defnDecl (mkDefinitionValEx stubN [] progTy sLit .abbrev .safe []))
    let eqTy (a b : Lean.Expr) := mkApp3 (mkConst ``Eq [1]) progTy a b
    let appC := mkApp4 (mkConst ``HAppend.hAppend [0, 0, 0]) progTy progTy progTy
      (mkApp2 (mkConst ``instHAppendOfAppend [0]) progTy (mkApp (mkConst ``List.instAppend [0]) dirTy))
    let app (a b : Lean.Expr) := mkApp2 appC a b
    let trans (a b c h1 h2 : Lean.Expr) := mkApp6 (mkConst ``Eq.trans [1]) progTy a b c h1 h2
    let cgr (f a b h : Lean.Expr) := mkApp6 (mkConst ``congrArg [1, 1]) progTy progTy a b f h
    let t := mkConst tailN
    -- the code's suffixes `X i = c i ++ X (i + 1)`, `X n = []`, rebuilt from the heads
    let mut X : Array Lean.Expr := #[nilE]
    for i in [0:n] do
      X := X.push (app csp[n - 1 - i]!.1 X.back!)
    let Xs (i : Nat) := X[n - i]!
    -- the last segment: `(c ++ []) ++ t = f ++ []`
    let c := csp[n - 1]!.1
    let f := fsp[n - 1]!.1
    let h0 := mkApp2 (mkConst ``Eq.refl [1]) progTy (app c t)          -- `c ++ t = f`, by evaluation
    let hlast := trans (app (app c nilE) t) (app c t) (app f nilE)
      (cgr (mkLambda `x .default progTy (app (.bvar 0) t)) (app c nilE) c
        (mkApp2 (mkConst ``List.append_nil [0]) dirTy c))
      (trans (app c t) f (app f nilE) h0
        (mkApp4 (mkConst ``Eq.symm [1]) progTy (app f nilE) f (mkApp2 (mkConst ``List.append_nil [0]) dirTy f)))
    -- `P i : X i ++ t = R i`, `R i = c i ++ R (i + 1)`, `R (n - 1) = f ++ []`
    let mut P := hlast
    let mut R := app f nilE
    for k in [0:n - 1] do
      let i := n - 2 - k
      let ci := csp[i]!.1
      let step := trans (app (app ci (Xs (i + 1))) t) (app ci (app (Xs (i + 1)) t)) (app ci R)
        (mkApp4 (mkConst ``List.append_assoc [0]) dirTy ci (Xs (i + 1)) t)
        (cgr (mkApp appC ci) (app (Xs (i + 1)) t) R P)
      P := step
      R := app ci R
    -- `name.lit : file = stub ++ (code ++ tail)`, from `P 0 : code ++ tail = rest` (by delta)
    let litN := name ++ `lit
    let hrest := mkApp4 (mkConst ``Eq.symm [1]) progTy (app (mkConst codeN) t) rest P
    addDecl (.thmDecl { name := litN, levelParams := [],
                        type := eqTy (mkConst fileN) (app (mkConst stubN) (app (mkConst codeN) t)),
                        value := cgr (mkApp appC (mkConst stubN)) rest (app (mkConst codeN) t) hrest })
    let ty ← match (← getEnv).find? codeEqN with
      | some (.thmInfo ci) | some (.axiomInfo ci) => pure ci.type
      | _ => throwError "asm_file_eq: {codeEqN} is not a theorem"
    let some (_, rhs, _) := ty.eq? | throwError "asm_file_eq: {codeEqN} is not an equation"
    -- `stub ++ (code ++ t) = stub ++ (rhs ++ t)`
    let h := cgr (mkLambda `x .default progTy (app (mkConst stubN) (app (.bvar 0) t))) (mkConst codeN) rhs
      (mkApp4 (mkConst ``Eq.symm [1]) progTy rhs (mkConst codeN) (mkConst codeEqN))
    addDecl (.thmDecl { name, levelParams := [], type := eqTy (mkConst fileN) (app (mkConst stubN) (app rhs t)),
                        value := trans (mkConst fileN) (app (mkConst stubN) (app (mkConst codeN) t))
                          (app (mkConst stubN) (app rhs t)) (mkConst litN) h })
    addDocString' name .missing doc?

@[command_elab asmFileEq] meta def elabAsmFileEq : CommandElab := fun stx => do
  let `($[$doc?:docComment]? asm_file_eq $n:ident : $fileS:ident = $stubS:ident ++ $codeS:ident $[++ $tailS?]? via $codeEqS:ident) := stx
    | throwUnsupportedSyntax
  if let some tailS := tailS? then return ← elabAsmFileEqTail doc? n fileS stubS codeS tailS codeEqS
  let ns ← getCurrNamespace
  let name := ns ++ n.getId
  let stubN := ns ++ stubS.getId
  liftTermElabM do
    let fileN ← realizeGlobalConstNoOverload fileS
    let codeN ← realizeGlobalConstNoOverload codeS
    let codeEqN ← realizeGlobalConstNoOverload codeEqS
    let some fileV := (← getConstInfo fileN).value? | throwError "asm_file_eq: {fileN} has no value"
    let some (sLit, rest) := appendArgs? fileV | throwError "asm_file_eq: {fileN} is not `stub ++ code`"
    -- the file's segments after the stub against `code`'s
    let fs ← segmentsOf rest
    let cs ← segmentsOf (mkConst codeN)
    for i in [0:min fs.size cs.size] do
      unless fs[i]! == cs[i]! do
        throwError "asm_file_eq: the file differs from {codeN} in segment {i} ({segName cs[i]!}); \
          regenerate it"
    unless fs.size == cs.size do
      throwError "asm_file_eq: the file has {fs.size} segments after the stub, {codeN} {cs.size}; \
        regenerate it"
    -- the stub, unless `asm_stub` declared it (then it must be the file's)
    match (← getEnv).find? stubN with
    | some ci =>
      unless ci.value? == some sLit do
        throwError "asm_file_eq: {stubN} is not the stub of {fileN} (rebuild its `asm_stub` module)"
    | none => withExporting <| addDecl (.defnDecl (mkDefinitionValEx stubN [] progTy sLit .abbrev .safe []))
    let eqTy (a b : Lean.Expr) := mkApp3 (mkConst ``Eq [1]) progTy a b
    let appC := mkApp4 (mkConst ``HAppend.hAppend [0, 0, 0]) progTy progTy progTy
      (mkApp2 (mkConst ``instHAppendOfAppend [0]) progTy (mkApp (mkConst ``List.instAppend [0]) dirTy))
    -- `name.lit : file = stub ++ code`
    let litN := name ++ `lit
    addDecl (.thmDecl { name := litN, levelParams := [],
                        type := eqTy (mkConst fileN) (mkApp2 appC (mkConst stubN) (mkConst codeN)),
                        value := mkApp2 (mkConst ``Eq.refl [1]) progTy (mkConst fileN) })
    -- `name : file = stub ++ rhs`, from `code_eq : rhs = code`
    -- an imported theorem of a module is seen as an axiom (its statement without its proof)
    let ty ← match (← getEnv).find? codeEqN with
      | some (.thmInfo ci) | some (.axiomInfo ci) => pure ci.type
      | _ => throwError "asm_file_eq: {codeEqN} is not a theorem"
    let some (_, rhs, _) := ty.eq? | throwError "asm_file_eq: {codeEqN} is not an equation"
    -- `stub ++ code = stub ++ rhs`
    let h := mkApp6 (mkConst ``congrArg [1, 1]) progTy progTy (mkConst codeN) rhs (mkApp appC (mkConst stubN))
      (mkApp4 (mkConst ``Eq.symm [1]) progTy rhs (mkConst codeN) (mkConst codeEqN))
    addDecl (.thmDecl { name, levelParams := [], type := eqTy (mkConst fileN) (mkApp2 appC (mkConst stubN) rhs),
                        value := mkApp6 (mkConst ``Eq.trans [1]) progTy (mkConst fileN)
                          (mkApp2 appC (mkConst stubN) (mkConst codeN)) (mkApp2 appC (mkConst stubN) rhs)
                          (mkConst litN) h })
    addDocString' name .missing doc?

end L.Compiler
