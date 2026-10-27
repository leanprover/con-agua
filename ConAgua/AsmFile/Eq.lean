import ConAgua.AsmFile.Term
import Lean.Elab.Command
import Std.Do.Triple.SpecLemmas

/-!
# The file's code is the compiler's output (kernel-checked; not trusted)

`asm_file_eq name : file = stub ++ code via code_eq`, where `file` is a constant whose value is
`include_asm`'s term `S ++ R` (`S` the file's first segment: the code before the trampoline),
`code` a constant built by `asm_lit` (e.g. `checkerAsm`) and `code_eq : rhs = code` (e.g.
`checkerAsm_eq : compileProg … = checkerAsm`), declares

* `stub : Program := S`, the file's code before the trampoline, as a literal;
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
def appendArgs? (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr) :=
  if e.isAppOfArity ``HAppend.hAppend 6 then some (e.appFn!.appArg!, e.appArg!) else none

/-- The segments of a right-nested `s₀ ++ (s₁ ++ … ++ [])`, each constant unfolded once, so that
`asm_lit`'s `code.f<i>` and the file's literals compare as terms. -/
partial def segmentsOf (e : Lean.Expr) (acc : Array Lean.Expr := #[]) : MetaM (Array Lean.Expr) := do
  let unfold (e : Lean.Expr) : MetaM Lean.Expr := do
    if e.isConst then return (← getConstInfo e.constName!).value?.getD e else return e
  match appendArgs? e with
  | some (a, b) => segmentsOf b (acc.push (← unfold a))
  | none =>
    if e.isAppOfArity ``List.nil 1 then return acc
    else if e.isConst then segmentsOf (← unfold e) acc
    else throwError "asm_file_eq: not a list of segments: {e}"

/-- The function a segment belongs to (its entry label `fnL g`), for messages. -/
def segName (e : Lean.Expr) : String :=
  match e.find? fun x => x.isAppOfArity ``fnL 1 with
  | some x => match x.appArg! with | .lit (.strVal g) => g | _ => "?"
  | none => "the trampoline"

syntax (name := asmFileEq) (docComment)? "asm_file_eq " ident " : " ident " = " ident " ++ " ident
  " via " ident : command

@[command_elab asmFileEq] def elabAsmFileEq : CommandElab := fun stx => do
  let `($[$doc?:docComment]? asm_file_eq $n:ident : $fileS:ident = $stubS:ident ++ $codeS:ident via $codeEqS:ident) := stx
    | throwUnsupportedSyntax
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
    addDecl (.defnDecl (mkDefinitionValEx stubN [] progTy sLit .abbrev .safe []))
    let eqTy (a b : Lean.Expr) := mkApp3 (mkConst ``Eq [1]) progTy a b
    let appC := mkApp4 (mkConst ``HAppend.hAppend [0, 0, 0]) progTy progTy progTy
      (mkApp2 (mkConst ``instHAppendOfAppend [0]) progTy (mkApp (mkConst ``List.instAppend [0]) dirTy))
    -- `name.lit : file = stub ++ code`
    let litN := name ++ `lit
    addDecl (.thmDecl { name := litN, levelParams := [],
                        type := eqTy (mkConst fileN) (mkApp2 appC (mkConst stubN) (mkConst codeN)),
                        value := mkApp2 (mkConst ``Eq.refl [1]) progTy (mkConst fileN) })
    -- `name : file = stub ++ rhs`, from `code_eq : rhs = code`
    let some (.thmInfo ci) := (← getEnv).find? codeEqN | throwError "asm_file_eq: {codeEqN} is not a theorem"
    let some (_, rhs, _) := ci.type.eq? | throwError "asm_file_eq: {codeEqN} is not an equation"
    -- `stub ++ code = stub ++ rhs`
    let h := mkApp6 (mkConst ``congrArg [1, 1]) progTy progTy (mkConst codeN) rhs (mkApp appC (mkConst stubN))
      (mkApp4 (mkConst ``Eq.symm [1]) progTy rhs (mkConst codeN) (mkConst codeEqN))
    addDecl (.thmDecl { name, levelParams := [], type := eqTy (mkConst fileN) (mkApp2 appC (mkConst stubN) rhs),
                        value := mkApp6 (mkConst ``Eq.trans [1]) progTy (mkConst fileN)
                          (mkApp2 appC (mkConst stubN) (mkConst codeN)) (mkApp2 appC (mkConst stubN) rhs)
                          (mkConst litN) h })
    addDocString' name .missing doc?

end L.Compiler
