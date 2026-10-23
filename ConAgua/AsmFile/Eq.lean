import ConAgua.AsmFile.Term
import ConAgua.Compiler.Compile

/-!
# The file's code is the compiler's output (kernel-checked; not trusted)

`asm_file_eq name : file = stub ++ code via code_eq` proves `name : file = stub ++ rhs`, where
`file` is a constant whose value is `include_asm`'s term `S ++ R`, `code` a constant (`asm_lit`'s
literal, e.g. `checkerAsm`), `code_eq : rhs = code` (e.g. `checkerAsm_eq : compileProg … = checkerAsm`)
and `stub` any term (e.g. `abiStub checkerTab`). Steps, each checked by the kernel:

* `name.stub := S` (the file's first segment, as a constant) and `name.stub_eq : stub = name.stub`
  by `Eq.refl` (the kernel evaluates `stub`);
* `name.code_eq : file = name.stub ++ code` by `Eq.refl`: the file's remaining segments and `code`
  are the same terms (`include_asm` and `asm_lit` build them with the same functions,
  `ConAgua/AsmFile/Term.lean`), so the kernel compares them structurally, without evaluating;
* `name` from these and `code_eq`.

Before handing the terms to the kernel, the segments are compared here, so that a file that is not
the compiler's output (a stale file, a printer bug) fails with the first differing segment named,
not with a long kernel computation.
-/

namespace L.Compiler

open Lean Elab Command Meta
open Lean.Elab.Term (elabTermEnsuringType synthesizeSyntheticMVarsNoPostponing)

/-- The operands of `a ++ b` at `Program`, if `e` is one. -/
def appendArgs? (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr) :=
  if e.isAppOfArity ``HAppend.hAppend 6 then some (e.appFn!.appArg!, e.appArg!) else none

/-- The segments of a right-nested `s₀ ++ (s₁ ++ … ++ [])`, each with its constants unfolded once
(`delta`), so that `asm_lit`'s `code.f<i>` and the file's literal compare as terms. -/
partial def segmentsOf (e : Lean.Expr) (acc : Array Lean.Expr := #[]) : MetaM (Array Lean.Expr) := do
  match appendArgs? e with
  | some (a, b) =>
    let a ← if a.isConst then pure ((← getConstInfo a.constName!).value?.getD a) else pure a
    segmentsOf b (acc.push a)
  | none =>
    if e.isAppOfArity ``List.nil 1 then return acc
    else if e.isConst then segmentsOf ((← getConstInfo e.constName!).value?.getD e) acc
    else throwError "asm_file_eq: not a list of segments: {e}"

/-- The function name of a segment (its first label, `fnL g`), for messages. -/
def segName (e : Lean.Expr) : String :=
  match e.find? fun x => x.isAppOfArity ``fnL 1 with
  | some x => match x.appArg! with | .lit (.strVal g) => g | _ => "?"
  | none => "(trampoline)"

syntax (name := asmFileEq) "asm_file_eq " ident " : " ident " = " term:max " ++ " ident
  " via " ident : command

@[command_elab asmFileEq] def elabAsmFileEq : CommandElab := fun stx => do
  let `(asm_file_eq $n:ident : $fileS:ident = $stubS ++ $codeS:ident via $codeEqS:ident) := stx
    | throwUnsupportedSyntax
  let name := (← getCurrNamespace) ++ n.getId
  liftTermElabM <| withTheReader Core.Context
      (fun c => { c with maxRecDepth := max c.maxRecDepth 100000, maxHeartbeats := 0 }) do
    let fileN ← realizeGlobalConstNoOverload fileS
    let codeN ← realizeGlobalConstNoOverload codeS
    let codeEqN ← realizeGlobalConstNoOverload codeEqS
    let stubE ← elabTermEnsuringType stubS progTy
    synthesizeSyntheticMVarsNoPostponing
    let stubE ← instantiateMVars stubE
    let some fileV := (← getConstInfo fileN).value? | throwError "asm_file_eq: {fileN} has no value"
    let some (sLit, rest) := appendArgs? fileV | throwError "asm_file_eq: {fileN} is not `stub ++ code`"
    -- compare the file's segments after the stub with `code`'s
    let fs ← segmentsOf rest
    let cs ← segmentsOf (mkConst codeN)
    for i in [0:min fs.size cs.size] do
      unless fs[i]! == cs[i]! do
        throwError "asm_file_eq: the file differs from {codeN} in segment {i} ({segName cs[i]!})"
    unless fs.size == cs.size do
      throwError "asm_file_eq: the file has {fs.size} segments after the stub, {codeN} {cs.size}"
    -- `name.stub := S`, `name.stub_eq : stub = name.stub`
    let stubN := name ++ `stub
    addDecl (.defnDecl (mkDefinitionValEx stubN [] progTy sLit .abbrev .safe []))
    let eqTy (a b : Lean.Expr) := mkApp3 (mkConst ``Eq [1]) progTy a b
    let stubEqN := name ++ `stub_eq
    addDecl (.thmDecl { name := stubEqN, levelParams := [], type := eqTy stubE (mkConst stubN),
                        value := mkApp2 (mkConst ``Eq.refl [1]) progTy stubE })
    -- `name.code_eq : file = name.stub ++ code`
    let codeEqN' := name ++ `code_eq
    addDecl (.thmDecl { name := codeEqN', levelParams := [],
                        type := eqTy (mkConst fileN) (appendE (mkConst stubN) (mkConst codeN)),
                        value := mkApp2 (mkConst ``Eq.refl [1]) progTy (mkConst fileN) })
    -- `name : file = stub ++ rhs`, from `code_eq : rhs = code`
    let some (.thmInfo ci) := (← getEnv).find? codeEqN | throwError "asm_file_eq: {codeEqN} is not a theorem"
    let some (_, rhs, _) := ci.type.eq? | throwError "asm_file_eq: {codeEqN} is not an equation"
    let goal := eqTy (mkConst fileN) (appendE stubE rhs)
    let pf ← mkEqTrans (mkConst codeEqN')
      (← mkCongr (← mkCongrArg (mkApp (mkConst ``HAppend.hAppend [0, 0, 0]) progTy |>.app progTy |>.app progTy
          |>.app (mkApp2 (mkConst ``instHAppendOfAppend [0]) progTy (mkApp (mkConst ``List.instAppend [0]) dirTy)))
          (← mkEqSymm (mkConst stubEqN)))
        (← mkEqSymm (mkConst codeEqN)))
    addDecl (.thmDecl { name, levelParams := [], type := goal, value := pf })

end L.Compiler
