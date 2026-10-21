import ConAgua.Compiler.Run
import ConAgua.Compiler.WF
import ConAgua.Arena.WalkBench

/-! `lake env lean --run ConAgua/Arena/WalkEmit.lean OUT.s` writes the compiled `benchProg`
(entry `bb_bench`, no byte arrays, 25 word arrays) for `harness/walk.c`.

Kraken's AT&T printer writes the compiler's `imul rax, rcx` (`.imul (some rax) rax rcx`) as
`imulq %rcx, %rax, %rax`, which binutils 2.46 assembles as the APX three-operand form (EVEX), an
illegal instruction on this machine. The scanner never multiplies, so this is the first program
to meet it. `fixImul` rewrites it to the two-operand `imulq %rcx, %rax` (the same operation);
see `DESIGN.md`, lane `walk`. -/

open L L.Compiler L.Arena

#guard Prog.wf (Prog.tab benchProg 0 25) benchProg
#guard Prog.wf (Prog.tab walkProg 0 25) walkProg

/-- The two-operand spelling of the compiler's one `imul`. -/
def fixImul (s : String) : String := s.replace "imulq %rcx, %rax, %rax" "imulq %rcx, %rax"

def main (args : List String) : IO Unit := do
  let out := args.headD "walk.s"
  IO.FS.writeFile out (fixImul (asmText (Prog.tab benchProg 0 25) benchProg "bb_bench"))
