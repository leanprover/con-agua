import ConLeche.Frontend.Scan.Fast

/-! `lake exe valbench FILE`: con-leche's compiled `scanLineFwd` over a whole lean4export file,
with the driver of the Stage B validator (`L.Scan.Line.validN`): prints `ok 0` if every line
scans, `ok N` if line `N` is the first that does not — the same output as the compiled validator
under `ConAgua/Compiler/harness/run.c`. The baseline for DESIGN.md's measurements. -/

open ConLeche.Frontend

partial def drive (b : ByteArray) (i : USize) (ln : Nat) : Nat :=
  if i < b.usize then
    match scanLineFwd b i with
    | .err _ => ln + 1
    | .ok _ j => if j == 0 then 0 else if j ≤ i then ln + 1 else drive b j (ln + 1)
  else 0

def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: valbench FILE"; return 2
  let b ← IO.FS.readBinFile path
  IO.println s!"ok {drive b 0 0}"
  return 0
