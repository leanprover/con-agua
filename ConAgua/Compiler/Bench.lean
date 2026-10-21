import ConLeche.Frontend.Scan.Fast

/-! `lake exe skipbench FILE`: con-leche's compiled `skipBraced` on every line of a lean4export
file that starts with `{`, as `harness/run.c --lines` does with the compiled L code (the baseline
for DESIGN.md's measurements). `skipbench FILE noop` runs the same loop without the calls (the
harness overhead). -/

def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: skipbench FILE [noop]"; return 2
  let noop := args.length > 1
  let b ← IO.FS.readBinFile path
  let mut i := 0
  let mut n : Nat := 0
  let mut sum : Nat := 0
  let mut bad : Nat := 0
  while i < b.size do
    let mut eol := i
    while eol < b.size && b[eol]! != 10 do eol := eol + 1
    if b[i]! == 123 then
      let r := if noop then eol.toUSize else ConLeche.Frontend.skipBraced b (i + 1).toUSize 0
      if r.toNat != eol then bad := bad + 1
      sum := sum + r.toNat
      n := n + 1
    i := eol + 1
  IO.println s!"lines {n} checksum {sum} mismatches {bad}"
  return (if bad == 0 then 0 else 1)
