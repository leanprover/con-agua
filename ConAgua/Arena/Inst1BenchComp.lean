module

public import ConAgua.Arena.Inst1Spec
public import ConAgua.Arena.LiftBenchComp
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Inst1Spec
meta import ConAgua.Arena.LiftBenchComp

@[expose] public section

/-!
# A compiled benchmark driver for `inst_entry`

`inst_bench(n, k, val, d)` builds the left-nested term `app (… (app (bvar k) (bvar k)) …) (bvar
k)` with `n` applications through `mk_app`, interns `bvar val` as the substitute, and returns the
spine's handle (`k ≥ 2^63`: the build only) or `inst_entry(x, val', d)` of it. `LiftBenchComp.lean`'s
`liftBench` exactly, with `inst_entry` (`val`, `d`) in place of `lift_entry` (`shift`, `cutoff`).
`Inst1Emit.lean` compiles `inst1BenchProg` for `harness/inst1.c`.
-/

namespace L.Arena

/-- con-ron: none — a benchmark driver -/
def inst1Bench : FunDecl := lfn (n, k, val, d) locals (b, x, i, v, r) {
  b := call intern_bvar(k & 9223372036854775807);
  x := b;
  i := 0;
  while i < n {
    x := call mk_app(x, b);
    i += 1
  };
  if k >> 63 != 0 { return x };
  v := call intern_bvar(val);
  r := call inst_entry(x, v, d);
  return r
}

/-- The instantiate1 walk, `mk_app`, the stores it calls, and the driver. -/
def inst1BenchProg : Prog := instProg ++ [("inst1_bench", inst1Bench)]

/-- `liftBenchMem`'s sizing, one array wider: `IMEMO` (`47`) as well as `LMEMO` (`41`). -/
def inst1BenchMem (c : Nat) : Mem :=
  { words := withTiers <| ((List.range 48).map
      (fun i => Array.replicate (if i = 0 then 0 else if i = 1 then 64 else 8 * c) 0)).toArray }

/-- Run `f` from the memory `m`; the first result. -/
def inst1BenchRun (fuel : Nat) (f : FnName) (args : List Word) (m : Mem) : Option (Word × Mem) :=
  match run inst1BenchProg fuel f args m with
  | .ok (r, m') => some (r.headD 0, m')
  | .error _ => none

/- `bvar 3` nested in 5 applications, instantiated with `bvar 0` at depth `0`: some new handle. -/
#guard (inst1BenchRun 1000 "inst1_bench" [5, 3, 0, 0] (inst1BenchMem 32)).isSome

/- Not enough fuel: no answer. -/
#guard (inst1BenchRun 40 "inst1_bench" [50, 3, 0, 0] (inst1BenchMem 512)).isNone
#guard (inst1BenchRun 300 "inst1_bench" [50, 3, 0, 0] (inst1BenchMem 512)).isSome

end L.Arena
