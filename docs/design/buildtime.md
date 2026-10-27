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
