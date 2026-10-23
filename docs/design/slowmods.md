# Lane `slowmods`: the slowest modules

Goal: no module above ~60 s or ~6 GB of elaboration. Measurements: each module elaborated alone
(`lake env lean -Dprofiler=true -Dprofiler.threshold=1000 F.lean`, imports from the shared cache),
wall seconds and peak RSS of the process tree, niced, 3-4 at a time on the shared machine (load ~50-70):
compare before/after of the same module, not single digits.

## Landings

| module | before | after | how |
|---|---:|---:|---|
| `ConAgua.Checker.ProjFnShapeRef` | ~290 s (lane's figure) | 2 s, 2.5 GB | `pfs_spec` from `L.Ind.isProjFnShape_specW` (`IndRealIpf.lean`, the same L function's spec by `vcgen` with `L.evalC_spec`) plus `pfsW = ipfW`; its own `vcgen` over `evalC` had ~790 paths |
| `ConAgua.Arena.DeclCanonExpr` | 442 s, 2.8 GB | 26 s, 2.6 GB | `canonExprEq_spec`: plain `vcgen`, then `simp only` the locals (`setLoc`/`setLocs`/`init9_k`, `Cmp.eval`) at every goal, then `grind`, instead of `sym … => vcgen … <;> finish` |

## Findings

- `ProjFnShapeRef`: the same function `is_proj_fn_shape` had two specs, one in `IndRealIpf.lean`
  (`evalC_spec`, PLAN "long `&&`/`||` chain") and one here (plain `evalC`, every `&&`/`||` exit a
  path). Before writing a spec, grep for one of the same L function. Re-proving the old proof with
  `evalC_spec` alone was 130 s (three `grind`s of ~47 s); reusing the existing spec, 2 s.

- **The recipe "normalize the locals, then grind"** (`DeclCanonExpr`). After `sym only […] => vcgen
  … <;> finish`, each goal still carries the state as unsimplified chains (`({…}.setLocs [9, 10, 11,
  12] (eViewW …)).snd.loc 9`, `Cmp.ne.eval …`); `finish` works through them in the e-graph, and the
  cost grows with the arm's position in an `if t == k { … }; …` dispatch (1 s for the first arm,
  58 s for the last; 18 arms, 440 s). A plain `vcgen` followed by `all_goals (try simp only
  [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, List.headD_cons, …, Locals.init
  lemmas, Cmp.eval, BinOp.eval, Nat.reduceEqDiff, reduceIte, …] at *)` and `all_goals grind
  [lang_grind, arena_grind, …]` closes the same goals in under 1 s each. Guarded per-arm equations
  for the model's `if` chain (PLAN) made no difference here: the cost was on the L side.
