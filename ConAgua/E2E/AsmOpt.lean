import ConAgua.E2E.Ser
import ConAgua.Compiler.Run
import ConAgua.Compiler.Abi
import ConAgua.Compiler.WF

/-!
# `compopt-asm PROG ENTRY OUT.s` (lane `compopt`)

`e2e-l asm` without the rest of `e2e-l`: it imports only the compiler, `Prog.wf` and the program
file reader, not the compiler's correctness proof (`Final.Statement` imports `Compiler.Main`), so a
prototype compiler builds while its proof is broken. Same output as `e2e-l asm`.
-/

namespace L.E2E.AsmOpt

open L L.Compiler

def stubBodyAsm (diag code : Nat) : Stmt :=
  .seq (.st64 diag (.const 0) (.const code.toUInt64)) (.abort (.const 0))

def asmMain (prog entry out : String) : IO UInt32 := do
  let pf ← match parseProgFile (← IO.FS.readFile prog) with
    | .ok pf => pure pf
    | .error e => throw (IO.userError s!"{prog}: {e}")
  let p0 : Prog := pf.fns.toList
  let nw := (Prog.arrs p0).2
  let nb := max 1 (Prog.arrs p0).1
  let diag := nw
  let p : Prog := p0 ++ pf.stubs.toList.map fun (n, np, code) => (n, { nparams := np, nlocals := np, body := stubBodyAsm diag code })
  let tab := Prog.tab p nb (nw + 1)
  unless Prog.wf tab p do
    IO.eprintln "Prog.wf fails"
    return 1
  let txt := asmTextAbi tab (compileProg tab p entry) ++
    s!".section .rodata\n.globl ca_nw\n.globl ca_nb\n.globl ca_diag\nca_nw: .quad {nw + 1}\nca_nb: .quad {nb}\nca_diag: .quad {diag}\n"
  IO.FS.writeFile out txt
  IO.println s!"nw {nw + 1} nb {nb} diag {diag} fns {p.length}"
  return 0

end L.E2E.AsmOpt

def main (args : List String) : IO UInt32 := do
  match args with
  | [prog, entry, out] => L.E2E.AsmOpt.asmMain prog entry out
  | _ => IO.eprintln "usage: compopt-asm PROG ENTRY OUT.s"; return 2
