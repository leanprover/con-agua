module

public import ConAgua.Arena.Walk
public import ConAgua.Arena.SortStore
public import ConAgua.Arena.AppStore
public import ConAgua.Arena.BVarStore
public import ConAgua.Arena.FVarStore
public import ConAgua.Arena.ForallStore
public import ConAgua.Arena.LamStore
public import ConAgua.Arena.LetStore
public import ConAgua.Arena.ProjStore

@[expose] public section

/-!
# Tests and a benchmark driver for the walk

`bb_bench(n, k)` builds the left-nested term `app (… (app (bvar k) (bvar k)) …) (bvar k)` with `n`
applications by interning (`intern_bvar`, `intern_app`) and returns its handle (`k ≥ 2^63`: the
build only) or `bb_memo` of it (`k + 1`), at the depth counter `n + 10` (`WalkBenchLean.lean`'s twin fuel). The walk recurses `n` deep through the `f` children.
`#guard`s run the walk on small terms in the L interpreter; `WalkEmit.lean` compiles `benchProg`
for `harness/walk.c`, which runs it natively.
-/

namespace L.Arena

/-- con-ron: none — a benchmark driver -/
def bbBench : FunDecl := lfn (n, k) locals (b, x, i, r) {
  b := call intern_bvar(k & 9223372036854775807);
  x := b;
  i := 0;
  while i < n {
    x := call intern_app(x, b);
    i += 1
  };
  if k >> 63 != 0 { return x };
  r := call bb_memo(x, n + 10);
  return r
}

/-- The walk, the stores it reads, and the driver. -/
def benchProg : Prog :=
  walkProg ++ appProg ++ bvarProg ++ sortProg ++ letProg ++ fvarProg ++ lamProg ++ forallProg ++
    projProg ++ [("bb_bench", bbBench)]

/-- A memory with room for `c` nodes per table the walk reads: the 62 word arrays of the arena
layout (`ArenaRel.lean`) and the level-parameter columns 55‥61, all zero; the tables the walk does not read are empty. -/
def walkMem (c : Nat) : Mem :=
  { words := withTiers <| #[#[], Array.replicate 64 0, #[], #[], Array.replicate (4 * c) 0,
      Array.replicate (4 * c) 0] ++ Array.replicate 10 #[] ++
      #[Array.replicate (2 * c) 0, Array.replicate (4 * c) 0] ++ Array.replicate 2 #[] ++
      #[Array.replicate (6 * c) 0, Array.replicate (4 * c) 0, Array.replicate (2 * c) 0,
        Array.replicate (4 * c) 0, Array.replicate (8 * c) 0] ++
      #[Array.replicate (4 * c) 0, Array.replicate (4 * c) 0, Array.replicate (4 * c) 0,
        Array.replicate (4 * c) 0, Array.replicate (4 * c) 0, Array.replicate (4 * c) 0,
        Array.replicate (6 * c) 0, Array.replicate (4 * c) 0] ++ Array.replicate 22 #[] ++
      Array.replicate 7 (Array.replicate (2 * c) 0) }

/-- Run `f` from the memory `m`; the first result. -/
def walkRun (fuel : Nat) (f : FnName) (args : List Word) (m : Mem) : Option (Word × Mem) :=
  match run benchProg fuel f args m with
  | .ok (r, m') => some (r.headD 0, m')
  | .error _ => none

/- `bvar 3` nested in 5 applications: bound 4. -/
#guard (walkRun 1000 "bb_bench" [5, 3] (walkMem 64)).map (·.1) == some 4

/- `letE (bvar 0) (sort u) (app (bvar 2) (bvar 0))`: `max (max 1 0) (3 - 1) = 2`. -/
#guard
  match walkRun 100 "intern_bvar" [0] (walkMem 64) with
  | some (b0, m) => match walkRun 100 "intern_bvar" [2] m with
    | some (b2, m) => match walkRun 100 "intern_sort" [0x10000000] m with
      | some (s, m) => match walkRun 100 "intern_app" [b2, b0] m with
        | some (ap, m) => match walkRun 100 "intern_letE" [b0, s, ap] m with
          | some (le, m) => (walkRun 100 "bb_memo" [le, 100] m).map (·.1) == some 2
          | none => false
        | none => false
      | none => false
    | none => false
  | none => false

/- `lam (fvar 0 (sort u)) (forallE (bvar 1) (proj c 0 (bvar 3)))`: the `forallE`'s bound is
`max 2 (4 - 1) = 3`, the `lam`'s `max 0 (3 - 1) = 2`. -/
#guard
  match walkRun 100 "intern_sort" [0x10000000] (walkMem 64) with
  | some (s, m) => match walkRun 100 "intern_fvar" [0, s] m with
    | some (fv, m) => match walkRun 100 "intern_bvar" [1] m with
      | some (b1, m) => match walkRun 100 "intern_bvar" [3] m with
        | some (b3, m) => match walkRun 100 "intern_proj" [0x10000000, 0, b3] m with
          | some (pj, m) => match walkRun 100 "intern_forall" [b1, pj] m with
            | some (fa, m) => match walkRun 100 "intern_lam" [fv, fa] m with
              | some (la, m) => (walkRun 100 "bb_memo" [la, 100] m).map (·.1) == some 2
              | none => false
            | none => false
          | none => false
        | none => false
      | none => false
    | none => false
  | none => false

/- The depth counter: `bvar 0` needs one level; at `0` the walk aborts (the twin throws). -/
#guard
  match walkRun 100 "intern_bvar" [0] (walkMem 64) with
  | some (b0, m) => (walkRun 100 "bb_memo" [b0, 0] m).isNone &&
      (walkRun 100 "bb_memo" [b0, 1] m).map (·.1) == some 1
  | none => false

/- Not enough fuel for 50 nested applications: no answer. -/
#guard (walkRun 40 "bb_bench" [50, 3] (walkMem 512)).isNone
#guard (walkRun 200 "bb_bench" [50, 3] (walkMem 512)).map (·.1) == some 4

end L.Arena
