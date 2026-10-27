import ConAgua.AsmFile.Parse
import ConAgua.AsmFile.Term
import Kraken.X64.PrintATT
import Lean.Elab.Term.TermElabM
import Std.Do.Triple.SpecLemmas

/-!
# `include_asm "path"`: an assembler file as a `Program` (TRUSTED)

`include_asm "path"` is a term of type `Program`: the `.text` section of the assembler file at
`path` (relative to the directory of the current Lean file, as `include_str`), read by
`parseAsmFile` (`ConAgua/AsmFile/Parse.lean`) when the term is elaborated, and turned into a term by
`programTerm` (`ConAgua/AsmFile/Term.lean`). A file it cannot parse is an error.

The term is cut into segments for the kernel's sake, without changing its value: a new segment
starts at the label `ca_enter` (the trampoline) and at each function entry `ca_f_g`; the labels of
segment `ca_f_g` are written as `lbl "g" n m` where that is their value. So the term is
`stub ++ (trampoline ++ (f₀ ++ (… ++ (fₖ ++ []))))`, the shape `asm_lit`'s `checkerAsm` has.

The trusted base is this parser (`parseAsmFile`): the term comes from it alone. Two independent
cross-checks, not needed for soundness: Kraken's own parser must read the file's code the same way
(`ConAgua/AsmFile/CrossCheck.lean`, run by `scripts/asm_file.py`: ~13 s, too slow to
run here), and the assembler must encode what the file says (`scripts/check-asm.sh`). And here,
the code is printed again with Kraken's printer (`toATT`) and compared with the file's `.text`
lines: parse ∘ print is the identity on the file, so the parser reads every instruction the way
the printer (which wrote the file) meant it.

Lake does not see the file through the import graph: the module that uses `include_asm` must be in
a library whose `needs` list the file as an `input_file` (`lakefile.toml`, library `ConAguaAsm`), so
that the file's content is part of the module's input hash (rebuilds, and the shared artifact cache).
-/

namespace L.Compiler

open Lean Elab Term Meta ConAgua.AsmFile

/-- Cut `p` before `ca_enter:` and before every `ca_f_g:`; each piece with the function name its
labels use (`g`, or `""` before the first function). -/
def segments (p : Program) : List (String × Program) := Id.run do
  let mut out : Array (String × Program) := #[]
  let mut cur : Array Directive := #[]
  let mut f := ""
  for d in p do
    let start? : Option String := match d with
      | .label l => if l == enterL then some "" else if l.startsWith "ca_f_" then some (l.drop 5).toString else none
      | _ => none
    if let some g := start? then
      if !cur.isEmpty then out := out.push (f, cur.toList)
      cur := #[]
      f := g
    cur := cur.push d
  if !cur.isEmpty then out := out.push (f, cur.toList)
  return out.toList

/-- The term for `p`: its segments joined (see the module doc). -/
def programTerm (p : Program) : Lean.Expr :=
  joinE ((segments p).map fun (f, v) => codeExpr f v)

syntax (name := includeAsm) "include_asm " str : term

@[term_elab includeAsm] def elabIncludeAsm : TermElab := fun stx _ => do
  let `(include_asm $path:str) := stx | throwUnsupportedSyntax
  let some dir := (System.FilePath.mk (← getFileName)).parent
    | throwError "include_asm: no directory for {← getFileName}"
  let file := dir / path.getString
  let text ← IO.FS.readFile file
  match parseAsmFile text with
  | .error e => throwErrorAt path "include_asm: {file}: {e}"
  | .ok f =>
    let textLines := (text.splitOn "\n").takeWhile (!·.startsWith ".section ") |>.filter fun l =>
      !l.isEmpty && l != ".text" && !l.startsWith ".globl "
    unless Kraken.X64.toATT f.text == "\n".intercalate textLines do
      throwErrorAt path "include_asm: {file}: printing the parsed code does not give the file back"
    return programTerm f.text

end L.Compiler
