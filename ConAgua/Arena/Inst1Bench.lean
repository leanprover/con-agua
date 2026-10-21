module

public import ConAgua.Arena.Inst1Spec
public import ConAgua.Arena.LiftBench
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Inst1Spec
meta import ConAgua.Arena.LiftBench

@[expose] public section

/-!
# Tests for `instantiate1` in the L interpreter

As `LiftBench.lean`: build through `mk_*`, instantiate with `inst_entry`, compare with the expected
term's handle.
-/

namespace L.Arena

/-- The walks, the stores, `mk_*` and `intern_sort`. -/
def instTestProg : Prog := instProg ++ sortProg

def instRun (f : FnName) (args : List Word) (m : Mem) : Option (Word × Mem) :=
  match run instTestProg 1000 f args m with
  | .ok (r, m') => some (r.headD 0, m')
  | .error _ => none

/-- `instantiate1 t v d` against the expected term `e`; `v` is built after `t`. -/
def instCheck (build : Mem → Option (Word × Mem)) (val : Mem → Option (Word × Mem)) (d : Word)
    (expect : Mem → Option (Word × Mem)) : Bool :=
  match build (liftMem 16) with
  | none => false
  | some (t, m) => match val m with
    | none => false
    | some (v, m) => match instRun "inst_entry" [t, v, d] m with
      | none => false
      | some (r, m) => match expect m with
        | none => false
        | some (e, _) => r == e

def ibv (i : Word) (m : Mem) : Option (Word × Mem) := instRun "intern_bvar" [i] m
def imk2 (f : FnName) (x y : Mem → Option (Word × Mem)) (m : Mem) : Option (Word × Mem) := do
  let (a, m) ← x m
  let (b, m) ← y m
  instRun f [a, b] m
def isort (m : Mem) : Option (Word × Mem) := instRun "intern_sort" [0x10000000] m

/- `app (bvar 0) (bvar 2)` with `bvar 0 := sort u`: `app (sort u) (bvar 1)`. -/
#guard instCheck (imk2 "mk_app" (ibv 0) (ibv 2)) isort 0 (imk2 "mk_app" isort (ibv 1))

/- Under a binder: `lam (bvar 0) (app (bvar 1) (bvar 0))`, `bvar 0 := sort u` at depth 0:
`lam (sort u) (app (sort u) (bvar 0))`. -/
#guard instCheck (imk2 "mk_lam" (ibv 0) (imk2 "mk_app" (ibv 1) (ibv 0))) isort 0
  (imk2 "mk_lam" isort (imk2 "mk_app" isort (ibv 0)))

/- A closed term is returned unchanged (the cut-off). -/
#guard instCheck (imk2 "mk_forall" isort (ibv 0)) (ibv 5) 0 (imk2 "mk_forall" isort (ibv 0))

/- `proj s 0 (bvar 3)` at depth 1 with `bvar 1 := bvar 7`: `bvar 3` is above, lowered to
`bvar 2`. -/
#guard instCheck (fun m => do let (e, m) ← ibv 3 m; instRun "mk_proj" [0x10000000, 0, e] m)
  (ibv 7) 1 (fun m => do let (e, m) ← ibv 2 m; instRun "mk_proj" [0x10000000, 0, e] m)

end L.Arena
