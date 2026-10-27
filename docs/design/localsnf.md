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

## 2. Design

Three candidates were on the table: a simproc that resolves reads through the chain, a different
representation of the locals (in the frame or in `vcgen`'s output), and fixed `simp only` lemma
sets. The representation change touches `L/Semantics.lean` and with it the compiler proofs and
every spec; the lemma sets exist already (299 hand-written copies) and are what costs the time. The
simproc needs no change to any statement and reaches `grind` as well as `simp`, so it came first,
and the prototype (§3.1) left no reason to try the others.

**`ConAgua/L/LocNF.lean`** has three simprocs, imported by `L/Logic.lean`, so every L proof has
them:

* `L.reduceLoc`: `St.loc s y` for a literal `y`. It walks the writes at the top of `s`: a
  `setLoc x v` with a literal `x` gives `v` if `x = y` and is skipped otherwise; a `setLocs xs vs`
  with a literal list of literal locals is stepped through one entry at a time (taking the entries
  of `vs` when it is a literal list); a `setG` is skipped; a literal frame `St.mk m l` gives `l y`,
  and an entry of a literal `Locals.init` list (or `0` past its end).
* `L.reduceLocalsInit`: `Locals.init vs y` for a literal list `vs` and a literal `y`.
* `L.reduceLocMem`: `St.mem s` through the writes to literal locals at the top of `s`.

Each step is a small lemma (`loc_setLoc_eq`, `loc_setLoc_ne`, `loc_setLocs_cons_cons`, …,
`mem_setLocs`) instantiated by hand, the literal comparisons are `Nat.beq` facts by `rfl`, and the
proof is the chain of `Eq.trans`. The simprocs are registered for **`seval`**, the simproc set
that `grind`'s normalizer runs on every term it internalizes, so `grind`, `finish` and `sym … =>
vcgen … <;> finish` resolve each read once, when it enters the e-graph, instead of instantiating
`St.setLoc_loc` once per layer and deciding an `if` per instance. Each is registered twice, before
the subterms (`↓`) and after them (a read that appears only once a subterm is simplified, such as
`(x, s).snd.loc 5`). `simp`, `simp_all` and `simp only` use them when listed.

Decisions, each forced by a failure of the simpler version:

* **Not in the default `simp` set.** With `[simp]`, every `simp [St.setLoc_loc, …]` list
  (299 in 115 files) turns into unused-argument warnings, which fail CI, and `Arena.Store`'s
  `simp_all` hits the recursion limit. As `seval` only, no `simp` call changes.
* **Proofs, not definitional steps.** As `dsimproc`s (result definitionally equal, no proof) the
  kernel has to check `chain.loc 7 ≡ v` on its own, and it unfolds the value side first: "deep
  recursion" in `FVarRange`, `Walk`, `WalkScope`, `Inst1`, `InstListSpec`, `RomExpr`.
* **Literal locals only.** A walk through `setLoc x v` with a variable `x` would rewrite the left
  sides of the general equations themselves when they are registered as `grind` patterns
  (`St.setLoc_mem`, `Scan.St.setLocs_mem`, `Locals.init_cons_zero`: "invalid pattern"). The
  verification conditions only have literal locals.

## 3. Measurements

### 3.1 Prototype

The simprocs pasted into copies of the ten modules (`_tmp/localsnf/mkvar.py`; also added to the
hand-written `simp only [St.setLoc_loc, …]` lists): 307 → 184 CPU s over the nine modules that
elaborated (`LevelLeqSpec` is a `module` file and the pasted code was not `meta`). Every proof
went through unchanged. The gain was almost all in `grind`.

### 3.2 The ten modules, alone, interleaved

Master e2f3ea22 (A) and this branch (B), each module elaborated alone, A then B, CPU seconds
(`_tmp/localsnf/inter.sh`, load about 20):

| module | A | B |
|---|---:|---:|
| `Verdict.IndBGrpM` | 81.5 | 81.2 |
| `Arena.IndInstallSpec.GenRecCheckPrep` | 88.3 | 19.7 |
| `Arena.RecGenSpec.Tmc` | 52.0 | 4.1 |
| `Arena.DeclApdSpec` | 47.9 | 9.7 |
| `Verdict.DefEqTailE` | 42.6 | 41.8 |
| `Arena.LevelLeqSpec` | 34.5 | 6.5 |
| `Arena.IndInstallSpec.Pos3Init` | 34.2 | 4.4 |
| `Arena.RecGenSpec.OcW` | 31.5 | 9.9 |
| `Arena.DeclCanonExpr` | 30.8 | 27.8 |
| `Verdict.IndBTmm` | 25.0 | 22.6 |
| **total** | **468** | **228** (−51 %) |

The four modules that did not move (`IndBGrpM`, `DefEqTailE`, `IndBTmm`, `DeclCanonExpr`) spend
their time in `simp`/`simp_all` (`l_model`'s recipe, a hand `simp only`), which does not use the
simprocs unless they are listed (§4).

### 3.3 The whole build

Two cold builds one after the other (`LAKE_COLD=1`, empty `.lake/build`, 16 jobs, load 20–45;
logs `_tmp/localsnf/cold-{base,nf}.log`):

| | master e2f3ea22 | this branch |
|---|---:|---:|
| wall | 561 s | 447 s |
| CPU (user) | 11 103 s | 8 477 s |
| sum of `ConAgua` module times | 6 963 s | 5 219 s (−25 %) |

The largest drops: `Arena.DeclApdSpec` 80 → 11 s, `Arena.IndInstallSpec.GenRecCheckPrep` 74 →
9 s, `Front.FieldsExpr` 53 → 6 s, `Checker.Hoist` 59 → 19 s, `Arena.LevelLeqSpec` 45 → 6 s,
`Arena.RecGenSpec.OcW` 45 → 8 s, `Arena.RecGenSpec.Tmc` 37 → 3 s, `Arena.NatDiv` 58 → 31 s,
`Verdict.InferBindE` 54 → 29 s. The modules that got slower are kernel and program checks the
change cannot reach (`Checker.NoVerdictTree`, `IndArmTrees*`, `AsmPart*`): load noise of a
single pair of runs. No new warning (the same 21, all in Kraken and `vendor/`).

### 3.4 Fallout

Ten proof files changed (plus import lines):

* `DeclCanonLvl`, `DeclCanonRules`, `DeclCanonExpr`: the hand-written `init9_*`/`init11_*`
  lemmas (`Locals.init [a0, …, a10] k = ak`), passed to `finish`, had no pattern any more (the
  normalizer reduces their left sides). They are deleted; `DeclCanonExpr`'s `simp only` names
  `L.reduceLocalsInit` instead.
* `PromoteCI` (`erec_wr4`, `erec_wr5`, `proj_wr`), `IndInstallSpec.IcaW` (`er_put5`): runs of
  four to six stores need more than `finish`'s default five E-matching rounds (`ematch := 8`,
  commented as a depth).
* `WhnfCoreAppLoop` (`whnfAppRestW_spec`): one more case split than the default nine
  (`splits := 12`).
* `RecGenSpec.ClassMinorSlot`: the model's base arm as a `have` (the model's term occurs only
  under the post's `∃`).
* `NatArms` (`natPowLit_refines`): two small lemmas for `finish`, `pv_of_lt_one` and
  `pow_of_eq_zero` (the exponent's slice is empty).

* `RecGenSpec.CfhW`, `RecCheckSpec.TaCW`: their `finish` lists lose `loc_init4`…`loc_init9`
  (`RecSim.lean`'s hand lemmas for reads of the frame's arguments; the reads resolve before
  E-matching sees them).
* Imports: 26 modules imported `Scan.Common` only for its `lang_grind` equation `St.setLocs_mem`,
  and `CfhW`/`TaCW` imported `RecSim` only for `loc_init*`. `grind` no longer uses them, the import
  gate (`shake`) proposes the removals, and they are removed (`RcLook` now imports `RecSim`
  itself). `Logic`'s import of `LocNF` is allowlisted: an attribute's use is not recorded.

Each of the changed modules is faster than before.

## 4. Next: the `simp` side

`l_model`'s steps and the hand-written `simp only [St.setLoc_loc, …]` sets do not use the
simprocs unless they name them. Pilot (worktree only, not landed): the five simprocs added to
`l_model`'s `simpBase` list (`ModelGen.lean`); measurement below.
