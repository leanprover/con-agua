module

public import ConAgua.Arena.LiftSpec
public import ConAgua.Arena.SortStore
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.LiftSpec
meta import ConAgua.Arena.SortStore

@[expose] public section

/-!
# Tests for `liftLooseBVars` in the L interpreter

Terms are built through `mk_*` (so their derived ranges are in L), lifted with `lift_entry`, and
compared with the expected term built afterwards: hash-consing makes equal terms equal handles.
-/

namespace L.Arena

/-- The walk, the stores, `mk_*` and `intern_sort`. -/
def liftTestProg : Prog := liftProg ++ sortProg

/-- A memory with room for `c` nodes per table: 64 word arrays of `8 c` zeros, `CTL` of 64. -/
def liftMem (c : Nat) : Mem :=
  { words := (Array.replicate 64 (Array.replicate (8 * c) 0)).set! 1 (Array.replicate 64 0) }

/-- Run `f`; the first result and the memory. -/
def liftRun (f : FnName) (args : List Word) (m : Mem) : Option (Word × Mem) :=
  match run liftTestProg 1000 f args m with
  | .ok (r, m') => some (r.headD 0, m')
  | .error _ => none

/-- `lift t k c` against the expected term `e`, both built by `build`. -/
def liftCheck (build : Mem → Option (Word × Mem)) (k c : Word)
    (expect : Mem → Option (Word × Mem)) : Bool :=
  match build (liftMem 16) with
  | none => false
  | some (t, m) => match liftRun "lift_entry" [t, k, c, 4000000000] m with
    | none => false
    | some (r, m) => match expect m with
      | none => false
      | some (e, _) => r == e

/-- `bvar i`. -/
def bv (i : Word) (m : Mem) : Option (Word × Mem) := liftRun "intern_bvar" [i] m

/-- Two-child constructors through `mk_*`. -/
def mk2 (f : FnName) (x y : Mem → Option (Word × Mem)) (m : Mem) : Option (Word × Mem) := do
  let (a, m) ← x m
  let (b, m) ← y m
  liftRun f [a, b] m

/- `lam (bvar 0) (app (bvar 1) (bvar 0))` lifted by 2 at 0: `lam (bvar 2) (app (bvar 3) (bvar 0))`. -/
#guard liftCheck (mk2 "mk_lam" (bv 0) (mk2 "mk_app" (bv 1) (bv 0))) 2 0
  (mk2 "mk_lam" (bv 2) (mk2 "mk_app" (bv 3) (bv 0)))

/- A closed term is returned unchanged (the cutoff): `lam (bvar 0) (bvar 0)` is not closed, its
type is; `forallE (sort u) (bvar 0)` is. -/
#guard liftCheck (mk2 "mk_forall" (fun m => liftRun "intern_sort" [0x10000000] m) (bv 0)) 5 0
  (mk2 "mk_forall" (fun m => liftRun "intern_sort" [0x10000000] m) (bv 0))

/- `letE (bvar 1) (bvar 0) (app (bvar 2) (bvar 0))` lifted by 1 at 1:
`letE (bvar 2) (bvar 0) (app (bvar 3) (bvar 0))`. -/
#guard liftCheck
  (fun m => do
    let (t, m) ← bv 1 m
    let (v, m) ← bv 0 m
    let (b, m) ← mk2 "mk_app" (bv 2) (bv 0) m
    liftRun "mk_let" [t, v, b] m) 1 1
  (fun m => do
    let (t, m) ← bv 2 m
    let (v, m) ← bv 0 m
    let (b, m) ← mk2 "mk_app" (bv 3) (bv 0) m
    liftRun "mk_let" [t, v, b] m)

/- `proj s 0 (bvar 4)` lifted by 3 at 2: `proj s 0 (bvar 7)`. -/
#guard liftCheck
  (fun m => do let (e, m) ← bv 4 m; liftRun "mk_proj" [0x10000000, 0, e] m) 3 2
  (fun m => do let (e, m) ← bv 7 m; liftRun "mk_proj" [0x10000000, 0, e] m)

end L.Arena
