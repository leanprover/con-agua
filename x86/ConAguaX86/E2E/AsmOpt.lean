module

public import ConAgua.E2E.Ser
public import ConAguaX86.Compiler.Run
public import ConAguaX86.Compiler.Abi
public import ConAgua.Compiler.WF
public import ConAgua.Layout

@[expose] public section

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
  -- `DIAG`: a word array numbered past every array of the program and the input and pin data
  let diag := (Prog.arrU p0).foldl (fun m u => max m (u.1 + 1)) (max IN Rom.PB + 1)
  let p : Prog := p0 ++ pf.stubs.toList.map fun (n, np, code) => (n, { nparams := np, nlocals := np, body := stubBodyAsm diag code })
  -- the input and the pin data at positions `0` and `1`, where the stub puts the buffers
  let t := Prog.tab p
  let tab := Tab.ofArrs ([IN, Rom.PB] ++ (Prog.byteArrs p).filter (fun a => a != IN && a != Rom.PB))
    (Prog.wordArrs p) t.rom t.nres t.ng
  unless Prog.wf tab p do
    IO.eprintln "Prog.wf fails"
    return 1
  let txt := asmTextAbi tab (compileProg tab p entry) ++
    tabSymbols tab ++ s!".globl ca_diag\nca_diag: .quad {diag}\n"
  IO.FS.writeFile out txt
  IO.println s!"nw {tab.nw} nb {tab.nb} diag {diag} fns {p.length}"
  return 0

end L.E2E.AsmOpt

def main (args : List String) : IO UInt32 := do
  match args with
  | [prog, entry, out] => L.E2E.AsmOpt.asmMain prog entry out
  | _ => IO.eprintln "usage: compopt-asm PROG ENTRY OUT.s"; return 2
