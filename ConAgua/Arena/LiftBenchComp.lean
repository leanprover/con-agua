module

public import ConAgua.Arena.LiftSpec
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.LiftSpec

@[expose] public section

/-!
# A compiled benchmark driver for `lift_entry`

`lift_bench(n, k, shift, cutoff)` builds the left-nested term `app (… (app (bvar k) (bvar k)) …)
(bvar k)` with `n` applications, through `mk_app` (not `intern_app`: the walk needs the derived
range, `ExprMk.lean`), and returns its handle (`k ≥ 2^63`: the build only) or
`lift_entry(x, shift, cutoff)` of it. `WalkBench.lean`'s `bb_bench` exactly, with `mk_app` in place
of `intern_app` and the two extra arguments. `LiftEmit.lean` compiles `liftBenchProg` for
`harness/lift.c`.
-/

namespace L.Arena

/-- con-ron: none — a benchmark driver -/
def liftBench : FunDecl := lfn (n, k, shift, cutoff) locals (b, x, i, r) {
  b := call intern_bvar(k & 9223372036854775807);
  x := b;
  i := 0;
  while i < n {
    x := call mk_app(x, b);
    i += 1
  };
  if k >> 63 != 0 { return x };
  r := call lift_entry(x, shift, cutoff, 4000000000);
  return r
}

/-- The lift walk, `mk_app`, the stores it calls, and the driver. -/
def liftBenchProg : Prog := liftProg ++ [("lift_bench", liftBench)]

/-- A memory with room for `c` nodes per table (the full layout through the derived-range
arrays, `42`‥`46`, and the lift memo, `41`): every content array `8 c` words, `CTL` of `64`. -/
def liftBenchMem (c : Nat) : Mem :=
  { words := withTiers <| ((List.range 47).map
      (fun i => Array.replicate (if i = 0 then 0 else if i = 1 then 64 else 8 * c) 0)).toArray }

/-- Run `f` from the memory `m`; the first result. -/
def liftBenchRun (fuel : Nat) (f : FnName) (args : List Word) (m : Mem) : Option (Word × Mem) :=
  match run liftBenchProg fuel f args m with
  | .ok (r, m') => some (r.headD 0, m')
  | .error _ => none

/- `bvar 3` nested in 5 applications, lifted by `2` at cutoff `0`: the spine's bound is `4`, above
the cutoff, so every node is rewritten; the result is some new handle (hash-consing makes the
exact value uninteresting here, `LiftBench.lean` already checks the denotation). -/
#guard (liftBenchRun 1000 "lift_bench" [5, 3, 2, 0] (liftBenchMem 32)).isSome

/- Not enough fuel: no answer. -/
#guard (liftBenchRun 40 "lift_bench" [50, 3, 2, 0] (liftBenchMem 512)).isNone
#guard (liftBenchRun 300 "lift_bench" [50, 3, 2, 0] (liftBenchMem 512)).isSome

end L.Arena
