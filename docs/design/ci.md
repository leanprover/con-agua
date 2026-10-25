# Lane ci: GitHub Actions CI

`.github/workflows/ci.yml`, two jobs; the file's header comment is the reference (what each job
covers and does not, environment, caches, times, what was exercised locally).

## Decisions

- **checker job without Lean.** `scripts/e2e.py` needs `e2e-ref`/`e2e-l` (Lean executables) and
  con-ron's Rust binary, so CI uses a new `scripts/diff-e2e.py` instead: the built `checker` on
  con-leche's pinned expectations (`tests/e2e-expected.txt`, `tests/arena-expected.txt`, 628
  fixtures), like con-ron's `diff-e2e.sh`. Compared on accept versus not-accept (the checker exits
  0 only on accept and does not tell reject from decline): UNSOUND / INCOMPLETE / CRASH / TIMEOUT
  all fail. Fixtures expecting 124 (non-terminating) get 10 s; a run still going then agrees.
  con-leche's tests are a sparse checkout at `vendor/UPSTREAM`'s revision (con-leche is public).
- **Compiler.** A probe step takes the first installed compiler that compiles an `#embed`; else
  `apt-get install clang-19`, else apt.llvm.org. Untested on a runner (local clang 23 has it).
- **proof job uses `scripts/lake`** (every gate script calls it anyway) with
  `LAKE_ARTIFACT_CACHE=false`, `LAKE_NICE=0`; the Actions cache holds `.lake/build` +
  `.lake/packages`, not the Lake artifact cache dir (which would grow without bound across runs).
- **Incomplete builds** are saved under `<primary key>-incomplete-<run>-<attempt>`: an immutable
  cache entry under the primary key from a cancelled/failed build would block the finished one.
- **Gates**: all of `land.sh`'s (link gate, build, core/loop/leaf/preloop closure `--check`s,
  modules_check, bump-con-ron `--check`) plus `asm_file.py --check` and `provenance.py check`.

## Measurements (2026-10-25, master 2acb1e0e + this lane, the 96-core development machine, load ~40)

- Cold `scripts/lake build` in a fresh clone (own empty `_tmp/`), `LEAN_NUM_THREADS=4`: 2124 s,
  3610 jobs, 4 Lean processes at a time. Peak RSS per process: `Checker/Prelude` 6.7 GB,
  `Checker/AsmStubEq` 6.0, `Checker/Prog` 5.3, a dozen more at 4-5 GB. Sum of RSS peaked at 17.9 GB,
  sum of PSS at 8.3 GB (measured on a rebuild of `ConAgua/Checker/*` + `ConAgua/Final/*`, 893 s,
  the memory-heavy tail): the RSS sum double-counts the mmapped `.olean`s. So 4 fits 16 GB.
- `.lake/build` 4.5 GB, 1.3 GB as zstd -3 tar.
- Gates on a built tree: asm_file.py --check 25-36 s, leaf_fns 26 s, the other closures 1-2 s,
  link gate/modules_check/provenance < 2 s, bump-con-ron --check 8 s with fresh clones.
- diff-e2e: 628/628 agree, sequential 59-64 s, `--jobs=4` 55-63 s at `--parallel 4`;
  slowest `stack_fuel_offset` (expects 134; we say `exhausted` after ~40-55 s, 6.1 GB RSS);
  `whnf_core_loop`/`whnf_delta_loop` still running after 900 s (whnf_core_loop at 4.5 GB).
