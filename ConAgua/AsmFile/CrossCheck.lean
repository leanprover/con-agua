import ConAgua.AsmFile.Parse
import ConAgua.Compiler.Compile
import Kraken.X64.Parser.Basic

/-! `lake env lean --run ConAgua/AsmFile/CrossCheck.lean FILE.s`: reads the file's code with both
parsers, the trusted one (`parseAsmFile`, `ConAgua/AsmFile/Parse.lean`, which the final theorems'
term comes from) and Kraken's own (`Kraken.X64.Parser.parse`, independent code), and fails
(exit 1), naming the first differing directive, its line and function, if they disagree. A
cross-check, not part of the trusted base; `scripts/asm_file.py` runs it (and so `land.sh`). It is
not in `include_asm`: Kraken's parser takes about 17 s on the checker's 5.3 MB there, twice the
module's elaboration time (docs/design/asmfile.md). -/

open L.Compiler ConAgua.AsmFile

/-- The function directive `i` of `p` belongs to, for messages. -/
def segmentOf (p : Program) (i : Nat) : String := Id.run do
  let mut f := "the stub"
  for d in p.take (i + 1) do
    if let .label l := d then
      if l == enterL then f := "the trampoline"
      else if l.startsWith "ca_f_" then f := l
  return f

def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: CrossCheck.lean FILE.s"; return 2
  let text ← IO.FS.readFile path
  let f ← match parseAsmFile text with
    | .ok f => pure f
    | .error e => IO.eprintln s!"{path}: the trusted parser rejects it: {e}"; return 1
  -- the `.text` lines, one per directive (the trusted parser rejects `.text` after another section)
  let lines := (text.splitOn "\n").takeWhile (!·.startsWith ".section ") |>.filter fun l =>
    !l.isEmpty && l != ".text" && !l.startsWith ".globl "
  match Kraken.X64.Parser.parse ("\n".intercalate lines) with
  | .error e => IO.eprintln s!"{path}: Kraken's parser rejects the code: {e}"; return 1
  | .ok k =>
    if k == f.text then
      IO.println s!"{path}: both parsers agree ({k.length} directives)"
      return 0
    let i := ((k.zip f.text).findIdx fun (a, b) => a != b)
    IO.eprintln s!"{path}: the parsers disagree from directive {i} on ({k.length} vs {f.text.length} \
      directives): '{lines.getD i "<end>"}', in {segmentOf f.text i}"
    return 1
