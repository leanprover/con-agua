# Lane localsnf: a normal form for reads of locals

Goal (rank 1 of `lrecords.md` §2): proofs stop paying for long `setLoc` chains. `vcgen` leaves
the state after a run of statements as a chain of writes, `((s.setLoc 3 a).setLocs [4, 5]
r).setLoc 3 b`, and every read of a local or of the memory in a verification condition has to get
through it.

## 1. Baseline (master 386bf921)

**Method.** Ten slow spec modules, chosen from the `buildtime` after-cold log (module time) and
the `lrecords` profile (`loc` vocabulary), covering the three proof recipes in use: `sym … =>
vcgen … <;> finish`, plain `vcgen` + `simp only [St.setLoc_loc, …]` + `grind`, and `l_model`
(`simp_all` steps, with and without the `locals` pre-pass). None of them is in the absarrays
switch's file list. Each module is elaborated alone on a built tree, `lake env lean
-Dprofiler=true -Dprofiler.threshold=200 F.lean` (plain `profiler`, no `trace.profiler`); the
times are CPU seconds (user) from the shell's `time` and the profiler's cumulative categories
(`grind` is the sum of all `grind*` categories). Machine shared, load 6–14. Scripts:
`_tmp/localsnf/{prof.sh,runvar.sh,mkvar.py,summ.py}`, profiles under `_tmp/localsnf/prof/`.

| module | recipe | CPU s | simp | grind | kernel |
|---|---|---:|---:|---:|---:|
| `Verdict.IndBGrpM` | `l_model … locals` | 74.0 | 61.1 | 5.3 | 0.3 |
| `Arena.IndInstallSpec.GenRecCheckPrep` | `sym … finish` | 67.0 | 0.1 | 65.3 | 0.5 |
| `Arena.DeclApdSpec` | `sym … finish` | 39.4 | 0.6 | 33.1 | 0.5 |
| `Verdict.DefEqTailE` | `l_model` | 33.3 | 21.2 | 3.1 | 1.1 |
| `Arena.LevelLeqSpec` | `sym … finish` | 28.8 | 0.0 | 27.0 | 0.3 |
| `Arena.RecGenSpec.OcW` | `sym … finish` | 27.5 | 0.4 | 24.4 | 0.4 |
| `Arena.RecGenSpec.Tmc` | `sym … finish` | 25.1 | 0.0 | 24.1 | 0.1 |
| `Arena.DeclCanonExpr` | `vcgen` + `simp only` + `grind` | 18.0 | 6.2 | 5.8 | 0.6 |
| `Verdict.IndBTmm` | `l_model` | 16.9 | 13.0 | 1.4 | 0.3 |
| `Arena.IndInstallSpec.Pos3Init` | `l_model` (`sym` steps) | 13.5 | 0.0 | 12.6 | 0.1 |
| **total** | | **343.5** | 102.6 | 202.1 | 4.2 |

Where the locals cost sits: in `grind` (`sym … finish`), `St.setLoc_loc` is a `lang_grind`
equation, so each read `(chain).loc k` is instantiated once per layer of the chain, each instance
an `if k = x` that `grind` decides by its literal arithmetic; a goal has tens of reads of chains of
up to ~30 layers, in each of up to ~150 goals. In `simp`/`simp_all`, the same equation rewrites
each layer (one rewrite, one `Nat` literal comparison, one `ite` reduction per layer and per
read), again in every round of `simp_all`, and the proof term carries every step.
