import ConAgua.E2E.Ser
import ConAgua.E2E.Trace
import ConAgua.Compiler.Run
import ConAgua.Compiler.Abi
import ConAgua.Compiler.WF
import ConAgua.Final.Statement

/-!
# `e2e-l`: compile or interpret an assembled program file (lane `e2e`)

* `e2e-l asm PROG ENTRY OUT.s` — the stubs become `DIAG.u64[0] := code; abort` (`DIAG` is one word
  array past every array the program names), checks `Prog.wf`, and writes `asmText` plus the
  symbols `ca_nw` (word arrays) and `ca_diag` (the `DIAG` array) for `main.c`, and
  declining parallel-mode entries (`parDeclineText`). Prints `nw N nb B diag D fns F`. (The
  checker's own `check` is not compiled here: `scripts/e2e.py` runs `checker.s`'s generator,
  `ConAgua/Checker/AsmEmit.lean`, so the e2e runs test the shipped code.)
* `e2e-l run PROG ENTRY FILE [WORDS] [FUEL]` — `L.run` (the reference semantics) on
  `loadMem FILE PINS [WORDS] (replicate nw WORDS)` (`PINS`: the file `$CA_PINS`, else empty); the stubs become a call of the undefined function
  `__missing_<name>`, so the error names the function. Prints `ok R`, `abort`, `oob`,
  `missing NAME` or `exhausted`.
-/

namespace L.E2E

open L L.Compiler

def stubBodyAsm (diag code : Nat) : Stmt :=
  .seq (.st64 diag (.const 0) (.const code.toUInt64)) (.abort (.const 0))

def stubBodyRun (name : String) : Stmt := .call [] ("__missing_" ++ name) []

def loadPF (path : String) : IO ProgFile := do
  match parseProgFile (← IO.FS.readFile path) with
  | .ok pf => pure pf
  | .error e => throw (IO.userError s!"{path}: {e}")

/-- The pin-data buffer (byte array `1`, DESIGN.md lane `romload`): the file `$CA_PINS`, if set. -/
def pinBytes : IO ByteArray := do
  match ← IO.getEnv "CA_PINS" with
  | some f => IO.FS.readBinFile f
  | none => pure .empty

/-- `main.c` also links the parallel mode's entries and symbols (`asmTextAbiPar`, the
checker's `checker.s`); a test program has no parallel mode, so here they decline (`rdx = 1`,
never accept). -/
def parDeclineText : String :=
  ".text\n.globl ca_start_a\n.globl ca_check_b\n" ++
  "ca_start_a:\nca_check_b:\nmovq $0, %rax\nmovq $1, %rdx\nret\n" ++
  ".section .rodata\n.globl ca_out_off\n.globl ca_worker_size\nca_out_off: .quad 0\nca_worker_size: .quad 0\n"

def asmMain (prog entry out : String) : IO UInt32 := do
  let pf ← loadPF prog
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
    s!".section .rodata\n.globl ca_nw\n.globl ca_nb\n.globl ca_diag\nca_nw: .quad {nw + 1}\nca_nb: .quad {nb}\nca_diag: .quad {diag}\n" ++
    parDeclineText
  IO.FS.writeFile out txt
  IO.println s!"nw {nw + 1} nb {nb} diag {diag} fns {p.length}"
  return 0

def runMain (prog entry file : String) (words fuel : Nat) : IO UInt32 := do
  let pf ← loadPF prog
  let p0 : Prog := pf.fns.toList
  let nw := (Prog.arrs p0).2
  let p : Prog := p0 ++ pf.stubs.toList.map fun (n, np, _) => (n, { nparams := np, nlocals := np, body := stubBodyRun n })
  let b ← IO.FS.readBinFile file
  let pb ← pinBytes
  let m := ConAgua.Final.loadMem b pb [words] (List.replicate (nw + 1) words)
  match L.run p fuel entry [] m with
  | .ok (rs, _) => IO.println s!"ok {rs.headD 0}"
  | .error (.abort _) => IO.println "abort"
  | .error .oob => IO.println "oob"
  | .error .outOfFuel => IO.println "exhausted"
  | .error (.noFun f) =>
    if f.startsWith "__missing_" then IO.println s!"missing {f.drop "__missing_".length}"
    else IO.println s!"nofun {f}"
  return 0

/-- The tracing interpreter (`Trace.lean`): where the run stops. -/
def traceMain (prog entry file : String) (words : Nat) : IO UInt32 := do
  let pf ← loadPF prog
  let p0 : Prog := pf.fns.toList
  let nw := (Prog.arrs p0).2
  let p : Prog := p0 ++ pf.stubs.toList.map fun (n, np, _) => (n, { nparams := np, nlocals := np, body := stubBodyRun n })
  let b ← IO.FS.readBinFile file
  let pb ← pinBytes
  let m := ConAgua.Final.loadMem b pb [words] (List.replicate (nw + 1) words)
  let (msg, stack, calls) := Trace.run p entry m
  IO.println msg
  IO.println s!"stack {" > ".intercalate stack.toList}"
  let top := (calls.toArray.qsort (fun a b => a.2 > b.2)).toList.take 15
  IO.println s!"calls {top}"
  return 0

end L.E2E

def main (args : List String) : IO UInt32 := do
  match args with
  | ["asm", prog, entry, out] => L.E2E.asmMain prog entry out
  | "run" :: prog :: entry :: file :: rest =>
    let words := (rest[0]?.bind String.toNat?).getD 65536
    let fuel := (rest[1]?.bind String.toNat?).getD (2 ^ 40)
    L.E2E.runMain prog entry file words fuel
  | "trace" :: prog :: entry :: file :: rest =>
    L.E2E.traceMain prog entry file ((rest[0]?.bind String.toNat?).getD 65536)
  | _ =>
    IO.eprintln "usage: e2e-l asm PROG ENTRY OUT.s | e2e-l run PROG ENTRY FILE [WORDS] [FUEL]"
    return 2
