# Lane `slowmods`: the slowest modules

Goal: no module above ~60 s or ~6 GB of elaboration. Measurements: each module elaborated alone
(`lake env lean -Dprofiler=true -Dprofiler.threshold=1000 F.lean`, imports from the shared cache),
wall seconds and peak RSS of the process tree, niced, 3-4 at a time on the shared machine (load ~50-70):
compare before/after of the same module, not single digits.

## Landings

| module | before | after | how |
|---|---:|---:|---|
| `ConAgua.Checker.ProjFnShapeRef` | ~290 s (lane's figure) | 2 s, 2.5 GB | `pfs_spec` from `L.Ind.isProjFnShape_specW` (`IndRealIpf.lean`, the same L function's spec by `vcgen` with `L.evalC_spec`) plus `pfsW = ipfW`; its own `vcgen` over `evalC` had ~790 paths |

## Findings

- `ProjFnShapeRef`: the same function `is_proj_fn_shape` had two specs, one in `IndRealIpf.lean`
  (`evalC_spec`, PLAN "long `&&`/`||` chain") and one here (plain `evalC`, every `&&`/`||` exit a
  path). Before writing a spec, grep for one of the same L function. Re-proving the old proof with
  `evalC_spec` alone was 130 s (three `grind`s of ~47 s); reusing the existing spec, 2 s.
