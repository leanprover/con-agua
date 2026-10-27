# Lane buildtime: a shorter cold build

Goal: a shorter cold build (wall time and critical path) and faster slow modules, by fixing the
causes in the proofs and the generators (never by raising timeouts or heartbeats). Theorem
statements of `ConAgua/Final/`, L program text, `checker.s`, `pins.bin` and `main.c` stay
unchanged.

## Measuring

Cold build: `LAKE_COLD=1 scripts/lake build` from an empty `.lake/build` in a fresh worktree, all
cores, quiet machine (load below 10 at the start); wall and CPU from the build's resource usage.
Critical path and slack from Lake's `Built X (t)` lines and the import graph (restructure's
`cp.py`; a module starts when its last import is done, unlimited cores). Per-module profile:
the module elaborated alone on a built tree, `lake env lean -Dprofiler=true
-Dtrace.profiler=true -Dtrace.profiler.threshold=300 F.lean`.

Baseline, master 8a4d29c7 (2026-10-27): **wall 578 s, CPU 13 640 s, critical path 568 s**
(2104 modules, 8928 module-seconds).

The critical path is flat: 387 modules lie on a path longer than 520 s, 637 on one longer than
480 s. Making one module free gains at most its slack to the next path (about 10 s for most
modules on the path; the last module, `Verdict.IndArmTopE`, 31 s). So the gains come from causes
that many modules share.

## Causes found

### The inductive arm's top (`Checker.IndArm*`, `Verdict.IndArmTopE`; batch 1)

The last modules of the critical path, `Checker.IndArmClosed` (108 s) → `Checker.IndArm` (31 s) →
`Verdict.IndArmTopE` (31 s), were almost all kernel time:

* **Lookups in `prog_bundle`/`chk_lk`.** A lookup `checkerProg.lookup "f" = some fd` was proved
  from `checkerProg[n]? = some ("f", fd)`: the kernel walked up to 1838 cons cells (~17 µs each,
  ~18 ms per lookup), and the bundles of the two modules made ~1160 lookups each (~11 s for
  `KnotStageProg`, ~11 s for `CidProg`), both bundles proved twice (once in each module). Now
  `chunk_checker_prog` cuts `checkerProg` into chunks of 32 functions (`checkerProg.chunk<j>`,
  `checkerProg_chunks : checkerProg = checkerChunks.flatten`, one kernel check), and a lookup is
  `lk_of_chunk` (at most ~90 cells). Every `prog_bundle` user gains (`Verdict.KnotAllE` 21 → 4 s,
  `Checker.LoopProg` 35 → 19 s).
* **`by decide +kernel` memberships** (`∀ f ∈ passCallees, f ∈ armPosFns`, ~1000 names): `String`
  comparisons, ~19 s per module, in both modules. Now proved from the `names_tree`s
  (`subset_of_tree`/`mem_of_tree`), no `String` comparisons.
* The program facts of the arm are one structure `IndArmProgs` proved once
  (`indArmProgs_checker`, one `prog_bundle`, shared lookups proved once) and the `AbsKeep` facts
  `indArmKeep_checker`; `Verdict.IndArmTopE` reuses them.
* **`IndArmClosed`** (9 arms × ~58 `prog_all` chunks over the whole program, ~100 s of kernel
  checks, serial: `addDecl` inside one command runs each kernel check after the previous one,
  `Lean/AddDecl.lean`, `BaseIO.mapTask … env.checked`; separate `theorem` commands do run in
  parallel) waited ~47 s for late `Arena` imports that its chunk checks do not need. It now
  imports only `Checker.Prog`, `IndArmFns`, `WriteSetSplit`, `IndRealAbs`; the 9 composition
  theorems `checkerProg_armX` moved to `Checker.IndArm`. Its own time is unchanged.

| module | before | after |
|---|---:|---:|
| `Verdict.IndArmTopE` | 31 s | 3 s |
| `Checker.IndArm` | 31 s | 6 s |
| `Verdict.KnotAllE` | 21 s | 4 s |
| `Checker.LoopProg` | 35 s | 19 s |
| `Checker.IndArmClosed` | 108 s, done at 466 s | same time, done at ~418 s |

(After: `Built X (t)` times on a loaded machine. Estimated critical path 568 → ~540 s.) Left:
`IndArmClosed`'s CPU (~100 s): one walk checking all nine arms per function (a per-name bitmask)
would cut it several-fold.

### `Checker.Prog`'s literals (batch 2)

`Checker.Prog` (72 s in the cold build) is imported by every whole-program proof (`ProgWf`, the
loop and arm closures, `LoopProg`, `RomProg*`, …). Its time was not the program: `checkerSkt_eq :
Prog.skt checkerProg "check" = checkerSkt` is a 45 s kernel check (peak 11 GB), `checkerNrt_eq` 9 s,
`skt_lit`'s evaluation 9.5 s and `checkerTab`'s `#guard` 9 s. Only the compiled code
(`AsmPart*`, `AsmEmit`, `AsmFinal`) and the static check (`ProgWf`) read these literals. They now
sit in three generated modules after `Prog.lean`, built in parallel: `Checker.ProgTab`
(`checkerTab` and its `#guard`s), `Checker.ProgNrt`, `Checker.ProgSkt` (`scripts/checker_prog.py`;
the merge queue regenerates them with the others, `scripts/mq.py`'s `GEN_PROG`; `shake-keep.txt`
lists them, and `AsmPart4`…`9`, whose imports the generator writes).

| module (alone) | before | after |
|---|---:|---:|
| `Checker.Prog` | 66 s | 2 s |
| `Checker.ProgTab` | – | 14 s |
| `Checker.ProgNrt` | – | 12 s |
| `Checker.ProgSkt` | – | 42 s (peak 11 GB) |

`checker.s` and `pins.bin` are unchanged (`asm_file.py --check`).

### Single slow proofs in the `Arena` families (batch 3)

Most were `grind` searches over goals whose locals were still `setLoc` chains. Three fixes, in most
places together:

1. **Loads as `rdW`.** `vcgen`'s own unfolding of `ld64` leaves each read as `a[i.toNat]'h`, a bound
   proof inside the term, so `simp` could not normalize the locals. `ld64_rd_spec`
   (`Arena/LdRd.lean`) answers `rdW` with no proof inside. (The import gate cannot see that
   `vcgen [ld64_rd_spec]` needs the module: the proof term does not keep the name; allowlisted.)
2. **Plain `vcgen` instead of `sym … => vcgen … <;> finish`** (the PLAN recipe), then
   `subst_vars` and `simp only [St.setLoc_loc, …]`; `L.evalC_spec` and `Cond.pval` for long `||`
   conditions.
3. **`simp only [LocEq] at *`, then `simp only [*, St.setLoc_loc, …] at *` before `grind`**: the
   callee posts rewrite the locals, and `grind` no longer walks `LocEq` chains (`ctlW_spec` 32 →
   4 s; `tkh_spec`, `cg_specW`, `classFeRGo_spec`, `ci_specW` 3–4×).

Special cases: `natOpDeps_specW` (32 goals each re-simplified the 16 pin reads): the body is cut
after the reads (`seqTake`/`seqDrop`, `seqTake_drop`) and the dispatch has its own spec over named
locals; `natOpResultL_refinesR` (160 goals carrying the arms structure into `grind`): `clear` it,
and `rdW_PINS_ofNat` turns pin reads into `pinW`.

| module (cold build) | before | after |
|---|---:|---:|
| `Arena.DeclNatDeps` | 30 s | 16 s |
| `Arena.RecGenSpec.Rec3TmdWDecB` | 37 s | 19 s |
| `Arena.RecClassSpec.PrefixBinders` | 38 s | 26 s |
| `Arena.RecClassSpec.MnW` | 27 s | 15 s |
| `Arena.IndPartsSpec.BlockRecNamesUnreserved` | 19 s | 4 s |
| `Arena.StubNamesRefine` | 29 s | 2 s |
| `Arena.PinsNatOp` | 25 s | 13 s |
| `Arena.RecCheckSpec.Tka` | 48 s | 12 s |
| `Arena.IndSumSpec.CtlW` | 40 s | 7 s |
| `Arena.StrLitChar` | 50 s | 5 s |
| `Arena.DeclDivModSpec.SubstConst0List` | 48 s | 4 s |
| `Rom.CIReadRefW` | 48 s | 8 s |
| `Arena.RecGenSpec.ClassFeR` | 56 s | 10 s |
| `Arena.RecClassSpec.CrW` | 51 s | 22 s |
| `Arena.IndSumSpec.McGoStep` | 41 s | 14 s |

Left: `l_model` steps in these modules (`classGenMinorTyBody_spec.step1` 7 s,
`ruleBody_spec.step1` 6 s), `natOpDeps_run`'s kernel check (6–8 s, from its `simp` over 15 nested
`if`s), `classReadRecCls_spec` (10 s), `tka_spec` (14 s).

### `IndArmClosed` in three modules

The kernel checks of one module run one after another (`addDecl` waits for the checks before it;
measured: six `decide +kernel` theorems of 21 s each take 130 s in one file, with
`Elab.async` too). `IndArmClosed`'s nine arms (~100 s of kernel checks) are now in
`IndArmClosed1`…`3`, three arms each, which Lake builds in parallel; `IndArmClosed` keeps the
array tests `tA`/`tC`.

### The start of the path: the Nat ops and Scan (batch 4)

The path began with the chain `NatAdd` → `NatCmp` → `NatSub` → `NatShl` → `NatShr` → `NatDiv`
(165 s before anything above it started), and beside it Scan (`Utf8` → `Key` → … → `RecordsSpec`
→ `Line`, ~8 s slack).

* **Nat chain**: the modules waited on each other only for a few helper lemmas. They are in two
  small modules now, `Arena.NatCmpFacts` (`cmpW`, `pv_lt_wt`, `pv_succ_lt`, `pv_len_lt`,
  `pv_append`, `pv_ge_wt`) and `Arena.NatShiftFacts` (`sh`, the `shl_*` word facts, `and63_lt`,
  `sh_zero`, `sh_pos`, `shamt`, `pv_one`); `NatCmp`, `NatSub`, `NatShl`, `NatShr` import only
  `NatAdd` and these, `NatDiv` imports `NatSub` and these. In the model the Nat side is done at
  ~80 s instead of 173 s (and has ~85 s slack, so its proofs were left as they are).
* **`Scan.Line`** (46 s): `lineLoop_spec` was one proof over 223 goals with long path conditions.
  Now one spec per arm of the key dispatch (the arms are Lean projections of `lineLoop`'s syntax
  tree; the L code is unchanged) and one for the dispatch, which Lean elaborates in parallel; a
  step model `lineStepN` (`lineN_step`), one equation per key for `lineVal`/`lineKind`.
* **`Scan.RecordsLink`** (39 s): each `link_val` `macro_rules` after a record waited for all proofs
  before it (a command that changes the environment ends the parallel elaboration of the proofs
  before it), so the file ran serially. The 22 `macro_rules` are up front now.
* **`Scan.Key`**: `grind` case-split on `Bool` copies of the path conditions; `subst_vars` first,
  then `simp only [model, *, reduceIte]`. **`Utf8`, `Values`, `Str`**: plain `vcgen` + `simp` +
  `grind` instead of `sym … finish`; `L.evalC_spec` for `Str`'s 8-way escape test.

| module | before | after |
|---|---:|---:|
| `Scan.Key` | 24 s | 5–7 s |
| `Scan.Values` | 10 s | 5 s |
| `Scan.Utf8` | 9 s | 6–7 s |
| `Scan.Str` | 15 s | 7–11 s |
| `Scan.Line` | 46 s | 9–11 s |
| `Scan.RecordsLink` | 39 s | 10–12 s |
| Nat ops | a chain, 165 s | in parallel, ~80 s |

(After: single-file times on a loaded machine.) Left: `Scan.RecordsSpec` (28 s; the same arm
split for its two 11-key loops would gain ~7 s on the path).

### `l_model`'s step proofs (batch 5)

`l_model`'s `simp [lemmas]` recipe proves each step by `vcgen … <;> (try simp_all […]) <;> grind`.
In `Verdict.IndBGrpM` (one `l_model`, 324 s) `simp_all` took 257 s over 115 goals; in
`IndBTmn` (`tmnE_spec.step1`) 70 s. Unfolding the models through their `Except` match trees was
not the cost:

1. **Induction hypotheses left in the context.** A recursive member's step theorem (and a loop's
   spec) kept `ih` and its copy `ih1` after `vcgen` had used them, and `simp_all` re-simplified
   these large `∀`-triples (they contain the model) against every hypothesis in every round:
   57 of `tmnE_spec.step1`'s 60 s. Now the generator clears them right after `vcgen` (the
   default).
2. **Locals as long `setLoc` chains.** In a long straight-line function (`gen_rec_check_prep`: 12
   calls, 14 stores, 144 goals) every local is a `setLoc`/`setLocs` chain through ~30 states in
   ~70 hypotheses per goal (183 MB printed), and `simp_all` evaluates the chains again in each
   round; a goal's cost also grows with the goals before it (4 s alone, 18 s in sequence). A new
   option `locals` puts one `simp only [the locals' lemmas] at *` before `simp_all`. It is not the
   default: on small functions it costs more than it saves (`ClassFeR` 35 → 48 s), and where
   `grind` needs the `LocEq`s folded it fails (`CkcW`, `ErToIwWStage`, `UnresolvedE`). Used by
   `IndBGrpM` and `IndBSum3`.

| module (alone, CPU) | before | after |
|---|---:|---:|
| `Verdict.IndBTmn` | 106 s | 9 s |
| `Verdict.IndBGrpM` | 335 s | 93 s |
| `Verdict.IndBSum3` | 56 s | 36 s |
| other `l_model` modules | | unchanged within ±5 % |

Left: the hand-written copies of the recipe (`inferProj_specE` in `Verdict.InferLeavesE`, 118 s:
the pre-pass gives only 158 → 140 s); `DeclValE`'s `finish` recipe (`checkValueGroup_specE.step1`,
45 s); `CkcW` and `ErToIwWStage` pass `simp [getElem_rdW']` without importing the lemma, so their
`simp_all` always fails under `try` and `grind` alone proves the steps.

## Midway measurement

Master cec860c2 (batches 1–5 and the other lanes' landings), cold build with 16 jobs on a loaded
machine (load 55 at the start; not comparable with the baseline's wall time): CPU 13 448 s,
**critical path 485 s** from the module times (568 s at 8a4d29c7). The path now starts with the
Arena libraries `ConsLibSpec` → `ExprMk` → `Lift` → `Abs1Spec` → `ArRangeSpec` and ends with
`IndPosSpec` → `RecCheckSpec.Tpd` → `Verdict.IndBK53` → `IndBAgree` → `IndBCtor` → `IndBNfs`.

### Round 2 (batch 6)

* **`Scan.RecordsSpec`** (33 s wall, 246 CPU-s): every one of the 17 record loops was its own
  `sym … finish` proof. Each loop is now `objLoop mask disp` (equal to the original by `rfl`; the
  L code is unchanged), a dispatch over arms of four kinds (`slot_nat`, `scan_nat_list`,
  `scan_bool`, a one-result scanner); each kind, the dispatch and the loop are proved once, and a
  record's spec plugs in its arms: 5 s wall, 32 CPU-s.
* **`f ∈ nvFns` by `decide +kernel`** (306 error-claim proofs, a `String` compared with up to 1537
  names, ~2.3 s each, serial within a module): now looked up in `nvTree`, a name-code tree
  checked once (`Checker.NoVerdictTree`, `nv_mem`/`nv_sub`); ~700 CPU-s over the build
  (`Verdict.PosE2` 38 → 7 s, `IndBSum3` 59 → 31 s, `IndBK53` 9.5 → 3.4 s, `IndBAgree` 14 → 8.5 s).
* **`checkerProg.lookup f = … := by rfl`** (~140 in the loop and ROM program proofs, each
  comparing `String`s, ~1 s in the elaborator and the kernel): `lk_agree` (chunked position lookup
  plus the text side's `rfl`). `Checker.LoopDeclArm1` 33 → 10 s, `LoopDeclArm` 46 → 12.5 s,
  `LoopDeclAgree` 32 → 5 s, `RomProgA` 40 → 4 s, `RomProgB` 38 → 7 s; peak RSS of `LoopDeclArm1`
  4.1 → 2.6 GB (the 16 GB kills of the first profiling run came from `trace.profiler`, not from the
  modules).
* `RecCheckSpec.Tpd` 24 → 4 s, `TruncSl` 10 → 2 s, `IndPosSpec.NestHoles` 7.8 → 3 s (plain
  `vcgen`, locals by `simp`).

Tried on `IndBGrpM`'s step (93 s with `locals`): `simp only [models, *]` instead of `simp_all`
fails; `simp_all only […]` or no `simp_all` at all (only `grind`) run past 500 s; `subst_vars`
before `simp_all` changes nothing (73 vs 76 s).

### Round 3 (batch 7): the Arena libraries at the start, the `Infer` errors

After round 1 the path started with `Arena.ConsLibSpec` → `ExprMk` → `Lift` → `Abs1Spec` →
`ArRangeSpec`.

* **Import cuts.** `Arena.LiftL` holds the lift L code, `LiftProg`, `liftProg`; `Abs1`, `Inst1`,
  `InstList` and `Checker.Prog` import it instead of `Lift`/`LiftSpec` and no longer wait for
  `Lift`'s 32 s `l_model` (`Lift`, `LiftSpec` `import all` it: `l_model` reads a definition's
  source from another module only so). `absEntry`/`aclrK` moved into `Abs1`, so `ArRangeSpec`
  and `Abs1Spec` build in parallel. `seqTake`/`seqDrop` moved to `Arena.LdRd`.
* **One theorem per arm** (`ConsLibSpec`: `consInternG_spec`, `cfLoop_spec`; `ExprMk`:
  `der_pushZ` per table): Lean elaborates separate theorems in parallel.
* **Cut a function after its decodes** (`seqTake`/`seqDrop`, the rest specified over named
  locals): `ExprMk`'s `derB_spec` (160 goals each re-simplified the decode chain),
  `Verdict.InferLeavesE`'s hand-written `inferProj_specE` (262 goals; three pieces),
  `Verdict.IndBTka`'s `tkaE_spec` (its two slice `if`s repeated all calls 4×).
* `Abs1Spec`, `ArRangeSpec`, `MemoLib`: plain `vcgen [ld64_rd_spec]` + `subst_vars` + `simp only` +
  `grind` instead of `sym … finish (gen 20)`. `Verdict.DeclValE`: its `l_model` uses `simp []
  errors locals` instead of `finish (gen 20, instances 4000)`.

| module (cold build) | before | after |
|---|---:|---:|
| `Arena.ConsLibSpec` | 51 s | 16 s |
| `Arena.ExprMk` | 24 s | 8 s |
| `Arena.Abs1Spec` | 27 s | 10 s |
| `Arena.ArRangeSpec` | 28 s | 10 s |
| `Arena.MemoLib` | 17 s | 10 s |
| `Verdict.InferLeavesE` | 101 s | 19 s |
| `Verdict.DeclValE` | 53 s | 4 s |
| `Verdict.IndBTka` | 59 s | 11 s |

Left: `Arena.Lift` (32 s, `liftGo_spec.step1` 21 s: the `simp […]` option does not parse when the
`specs` are long, `l_model` wraps the spec terms across lines; without `gen 20` the proof fails),
`Verdict.InferBindE` (32 s, the generated `inferPisE.loop1.spec`), `Front.Fields` (31 s,
`recLoop_spec`: would need `Scan.Line`'s per-arm split), `Arena.LpCol` (needs the decode cut).

## Measured before and after

Same machine, otherwise idle (the merge queue held, no other `lean` process), `LAKE_COLD=1
scripts/lake build` from an empty `.lake/build`, one job per core (`LEAN_NUM_THREADS=96`, what an
unset variable meant for the baseline), wall and CPU from the build's resource usage (logs
`_tmp/buildtime/{before,after}-cold.log`):

| | master 8a4d29c7 (before) | master 8a84fd4e (after) |
|---|---:|---:|
| wall | 578 s | **429 s** |
| CPU | 13 640 s | 13 430 s |
| sum of module times | 8 928 s | 8 425 s |
| critical path (from the module times) | 568 s | **421 s** |

(Between the two, other lanes landed too: namedarrays, sectionvars, leanthreads.) Peak session
memory during the after build: 32 GB.

Per module (cold build, before → after), the ones this lane changed:

| module | before | after |
|---|---:|---:|
| `Verdict.IndBGrpM` | 324 s | 101 s |
| `Verdict.InferLeavesE` | 118 s | 24 s |
| `Checker.IndArmClosed` | 108 s | 61 + 42 + 68 s in parallel (`IndArmClosed1`…`3`) |
| `Checker.Prog` | 72 s | 2 s (+ `ProgSkt` 78 s, `ProgTab` 20 s, `ProgNrt` 19 s in parallel, only the compiled code waits for them) |
| `Verdict.IndBTmn` | 62 s | 2 s |
| `Verdict.DeclValE` | 57 s | 6 s |
| `Arena.RecGenSpec.ClassFeR` | 56 s | 10 s |
| `Arena.RecClassSpec.CrW` | 51 s | 28 s |
| `Arena.StrLitChar` | 50 s | 7 s |
| `Arena.RecCheckSpec.Tka` | 48 s | 15 s |
| `Arena.DeclDivModSpec.SubstConst0List` | 48 s | 4 s |
| `Rom.CIReadRefW` | 48 s | 11 s |
| `Checker.LoopDeclArm1` | 48 s | 10 s |
| `Scan.Line` | 46 s | 11 s |
| `Checker.RomProgA` | 43 s | 4 s |
| `Verdict.IndBSum3` | 42 s | 24 s |
| `Arena.IndSumSpec.McGoStep` | 41 s | 18 s |
| `Checker.LoopDeclAgree` | 40 s | 5 s |
| `Arena.IndSumSpec.CtlW` | 40 s | 7 s |
| `Scan.RecordsLink` | 39 s | 13 s |
| `Verdict.IndBTka` | 38 s | 7 s |
| `Arena.RecClassSpec.PrefixBinders` | 38 s | 29 s |
| `Checker.LoopDeclArm` | 37 s | 10 s |
| `Checker.RomProgB` | 37 s | 9 s |
| `Arena.RecGenSpec.Rec3TmdWDecB` | 37 s | 18 s |
| `Checker.LoopProg` | 35 s | 16 s |
| `Verdict.PosE2` | 32 s | 7 s |
| `Arena.ConsLibSpec` | 31 s | 15 s |
| `Verdict.IndArmTopE` | 31 s | 3 s |
| `Checker.IndArm` | 31 s | 11 s |
| `Arena.DeclNatDeps` | 30 s | 22 s |
| `Arena.StubNamesRefine` | 29 s | 2 s |
| `Scan.RecordsSpec` | 28 s | 6 s |
| `Arena.RecCheckSpec.Tpd` | 27 s | 4 s |
| `Arena.RecClassSpec.MnW` | 27 s | 17 s |
| `Arena.PinsNatOp` | 25 s | 21 s |
| `Scan.Key` | 24 s | 7 s |
| `Verdict.KnotAllE` | 21 s | 9 s |
| `Arena.ExprMk` | 21 s | 10 s |
| `Arena.ArRangeSpec` | 20 s | 10 s |
| `Arena.Abs1Spec` | 19 s | 9 s |
| `Arena.IndPartsSpec.BlockRecNamesUnreserved` | 19 s | 5 s |

The Nat ops were not sped up, only made parallel (`NatShl` 54 → 64 s, `NatDiv` 32 → 40 s under
the busier start of the build); they have ~85 s slack now.

## Shared causes (the lessons)

* **Kernel checks of one module run serially** (`addDecl` waits for the checks before it; also
  for separate `theorem`s, measured). A module of many kernel checks (`prog_all` chunks) is split
  into modules that Lake builds in parallel; elaboration of separate theorems is parallel, so a
  proof over many arms is split into one theorem per arm.
* **`String` comparisons in the kernel**: `checkerProg.lookup … := by rfl`, `decide +kernel` over
  name lists (`nvFns`, callee lists). Use the chunked positions (`chk_lk`, `prog_bundle`,
  `lk_agree`) and the name-code trees (`nv_mem`, `mem_of_tree`).
* **Locals as `setLoc` chains** behind `sym … => vcgen … <;> finish`, `simp_all` and `grind`: plain
  `vcgen` with `ld64_rd_spec` (no bound proof inside a load), `subst_vars`, `simp only [LocEq] at
  *`, `simp only [*, St.setLoc_loc, …] at *`, then `grind`; for a long function, cut it after its
  decodes (`seqTake`/`seqDrop`) and specify the rest over named locals.
* **Unused hypotheses in `simp_all`'s context** (induction hypotheses after `vcgen`): clear them.
* **Imports for one definition**: a module that needs only a definition or a lemma of a slow one
  imports a small module holding it (`NatShiftFacts`, `LiftL`, `ProgTab`).

## Left

The critical path (421 s) now runs Scan → `Front.Fields` (32 s, `recLoop_spec`: the per-arm
split `Scan.Line` got) → the ROM and declaration setup → `Arena.DeclCanonSpec`/`DeclCanonLvl`/
`DeclCanonExpr` (27/25/37 s) → `Arena.Checker` → `Checker.LoopProgInd` (33 s) → `LoopProg` →
`IndArm` → `CheckARun` (22 s) → `VerdictEntry1` → the `Verdict` top. Off it: `Verdict.IndBGrpM`
(101 s; the long pole of the 4-core CI build: `simp_all` over 144 goals whose cost grows with the
goals before it; tried variants in the round-2 section), `Checker.ProgSkt` (78 s, 11 GB, one
kernel check of `Prog.skt`), `IndArmClosed1`…`3` (one walk checking all arms per function would
cut their CPU several-fold), `Arena.Lift` (`l_model`'s `simp` option does not parse long `specs`),
`Verdict.InferBindE`, `Arena.LpCol`. The second shake round (attribute, `Std` and `meta` imports,
the macro modules) was not done: with the path in proof modules it would not shorten it.
