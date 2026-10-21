import ConRon.Arena.ExprOps

/-! `lake exe walkbench N K [build]`: con-ron's compiled arena (`bvarBoundMemo`) on the term
`WalkBench.lean`'s `bb_bench(N, K)` builds, the baseline for the compiled L walk
(`harness/walk.c`, DESIGN.md lane `walk`). With `build`, only the term is built. -/

open ConRon.Arena

def build (n k : Nat) : AM EIdx := do
  let b ← internE (.bvar k)
  let mut x := b
  for _ in [0:n] do
    x ← internE (.app x b)
  pure x

def main (args : List String) : IO UInt32 := do
  let n := (args.getD 0 "1000").toNat!
  let k := (args.getD 1 "7").toNat!
  let onlyBuild := args.length > 2
  let act : AM Nat := do
    let x ← build n k
    if onlyBuild then pure x.word.toNat else bvarBoundMemo (n + 10) x
  match act.run (AState.init EStore.empty) with
  | .ok (r, _) => IO.println s!"ok {r}"; return 0
  | .error _ => IO.println "error"; return 1
