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
