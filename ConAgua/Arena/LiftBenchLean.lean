import ConRon.Arena.ExprOps

/-! `lake exe liftbenchlean N K SHIFT CUTOFF [build]`: con-ron's compiled arena
(`liftLooseBVarsFast`) on the term `LiftBenchComp.lean`'s `lift_bench(N, K, …)` builds, the
baseline for the compiled L lift (`harness/lift.c`, DESIGN.md lane `exprops2`).
`WalkBenchLean.lean`'s shape exactly. -/

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
  let shift := (args.getD 2 "2").toNat!
  let cutoff := (args.getD 3 "0").toNat!
  let onlyBuild := args.length > 4
  let act : AM Nat := do
    let x ← build n k
    if onlyBuild then pure x.word.toNat
    else do
      let r ← liftLooseBVarsFast (n + 10) shift cutoff x
      pure r.word.toNat
  match act.run (AState.init EStore.empty) with
  | .ok (r, _) => IO.println s!"ok {r}"; return 0
  | .error _ => IO.println "error"; return 1
