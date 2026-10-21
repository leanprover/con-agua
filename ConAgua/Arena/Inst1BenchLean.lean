import ConRon.Arena.ExprOps

/-! `lake exe instbenchlean N K VAL D [build]`: con-ron's compiled arena (`instantiate1Fast`) on
the term `Inst1BenchComp.lean`'s `inst1_bench(N, K, …)` builds, the baseline for the compiled L
instantiate1 (`harness/inst1.c`, DESIGN.md lane `exprops2`). `LiftBenchLean.lean`'s shape
exactly. -/

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
  let val := (args.getD 2 "0").toNat!
  let d := (args.getD 3 "0").toNat!
  let onlyBuild := args.length > 4
  let act : AM Nat := do
    let x ← build n k
    if onlyBuild then pure x.word.toNat
    else do
      let v ← internE (.bvar val)
      let r ← instantiate1Fast (n + 10) x v d
      pure r.word.toNat
  match act.run (AState.init EStore.empty) with
  | .ok (r, _) => IO.println s!"ok {r}"; return 0
  | .error _ => IO.println "error"; return 1
