module

public import ConAgua.Arena.Walk
public import ConAgua.Arena.SortStore
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Walk
meta import ConAgua.Arena.SortStore

@[expose] public section

/-!
# Tests and a benchmark driver for the walk

`bb_bench(n, k)` builds the left-nested term `app (… (app (bvar k) (bvar k)) …) (bvar k)` with `n`
applications by interning (`intern_bvar`, `intern_app`) and returns its handle (`k ≥ 2^63`: the
build only) or `bb_memo` of it (`k + 1`). The walk recurses `n` deep through the `f` children.
`#guard`s run the walk on small terms in the L interpreter; `WalkEmit.lean` compiles `benchProg`
for `harness/walk.c`, which runs it natively.
-/

namespace L.Arena

def bbBench : FunDecl := lfn (n, k) locals (b, x, i, r) {
  b := call intern_bvar(k & 9223372036854775807);
  x := b;
  i := 0;
  while i < n {
    x := call intern_app(x, b);
    i += 1
  };
  if k >> 63 != 0 { return x };
  r := call bb_memo(x);
  return r
}

/-- The walk, the stores it reads, and the driver. -/
def benchProg : Prog :=
  walkProg ++ appProg ++ bvarProg ++ sortProg ++ letProg ++ [("bb_bench", bbBench)]

/-- A memory with room for `c` nodes per table: 25 word arrays, all zero. -/
def walkMem (c : Nat) : Mem :=
  { words := #[#[], Array.replicate 26 0, #[], #[], Array.replicate (4 * c) 0,
      Array.replicate (4 * c) 0] ++ Array.replicate 10 #[] ++
      #[Array.replicate (2 * c) 0, Array.replicate (4 * c) 0] ++ Array.replicate 2 #[] ++
      #[Array.replicate (6 * c) 0, Array.replicate (4 * c) 0, Array.replicate (2 * c) 0,
        Array.replicate (4 * c) 0, Array.replicate (8 * c) 0] }

/-- Run `f` from the memory `m`; the first result. -/
def walkRun (fuel : Nat) (f : FnName) (args : List Word) (m : Mem) : Option (Word × Mem) :=
  match run benchProg fuel f args m with
  | .ok (r, m') => some (r.headD 0, m')
  | .error _ => none

/- `bvar 3` nested in 5 applications: bound 4. -/
#guard (walkRun 1000 "bb_bench" [5, 3] (walkMem 16)).map (·.1) == some 4

/- `letE (bvar 0) (sort u) (app (bvar 2) (bvar 0))`: `max (max 1 0) (3 - 1) = 2`. -/
#guard
  match walkRun 100 "intern_bvar" [0] (walkMem 16) with
  | some (b0, m) => match walkRun 100 "intern_bvar" [2] m with
    | some (b2, m) => match walkRun 100 "intern_sort" [0x10000000] m with
      | some (s, m) => match walkRun 100 "intern_app" [b2, b0] m with
        | some (ap, m) => match walkRun 100 "intern_letE" [b0, s, ap] m with
          | some (le, m) => (walkRun 100 "bb_memo" [le] m).map (·.1) == some 2
          | none => false
        | none => false
      | none => false
    | none => false
  | none => false

/- Not enough fuel for 50 nested applications: no answer. -/
#guard (walkRun 40 "bb_bench" [50, 3] (walkMem 64)).isNone
#guard (walkRun 200 "bb_bench" [50, 3] (walkMem 64)).map (·.1) == some 4

end L.Arena
