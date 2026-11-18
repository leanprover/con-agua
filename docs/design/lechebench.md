# Lane lechebench: bignum performance against con-leche (2026-11-18)

## Goal
The user asked (2026-11-18) that every bignum performance report also compare against con-leche,
the Lean checker whose `Nat` arithmetic is Lean's runtime, i.e. GMP, "to see how far we are away
from that". This lane builds con-leche at the pinned revision, adds it to `scripts/bench.py`, and
measures one comparison table on master.

The coordinator added a second item: rename the exe `e2e-ref` (con-ron's Lean model compiled by
Lean) to `con-ron-lean-twin`, or remove it if `con-ron-lean` can replace it.

## The con-leche binary
* Revision: `600d3b583b769176e911b06d20ba16330c9a179b` (the con-leche row of `vendor/UPSTREAM`),
  toolchain `leanprover/lean4:v4.35.0` (its `lean-toolchain`).
* Recipe (no network needed: the package has no dependencies):
  ```
  D=_tmp/ref/con-leche-bin/600d3b58
  mkdir -p $D/src
  git -C _tmp/ref/con-leche archive 600d3b583b769176e911b06d20ba16330c9a179b | tar -x -C $D/src
  (cd $D/src && lake build con-leche)        # elan picks v4.35.0; 2 min 19 s, 330 jobs
  cp $D/src/.lake/build/bin/con-leche $D/con-leche
  rm -rf $D/src
  ```
  The reference clone's checkout is not touched (`git archive` reads the object store only).
* `sha256 fbda4f9bfe18d9a2536ea2d9ddf332f5dd7d8eeac142836ec5aeebf2f38ac215`, 20.3 MB. GMP is
  linked statically (`nm` lists `__gmpn_mul_fft`, `__gmpn_mu_div_qr`, …); only libc is dynamic.
* How con-leche runs a fixture: `con-leche [--verified|--trusted] [--jobs=N] [--max-nat-size=N]
  [--] FILE.ndjson`; exit 0 accept, 1 reject, 2 decline, 3 error (`ConLeche/Driver/Cli.lean`).
  Its own test harness (`tests/arena.sh`) runs `con-leche --verified FILE` (default jobs), with
  extra flags only for the `nat_size_limit_*` fixtures (`--max-nat-size=16`, `E2E_FLAGS`). Its pins
  are built in (`pins/<toolchain>.json`, all toolchain variants); there is no pin option.
  `scripts/bench.py` runs `con-leche --jobs=1 -- FILE`: one check worker, as con-ron runs with
  `--jobs=1`, in the default `--verified` mode (the mode its theorem covers; it includes its
  "certification tax", extra checks only the proof needs).
* Verdicts: `scripts/diff-e2e.py --bin <con-leche> --jobs 2 --parallel 8` gives 740 agree
  (441 accepted, 299 not), 0 kind differences: the binary reproduces its own pinned
  expectations exactly. gf3 and every benchmark fixture below: accepted by all four systems.

## `scripts/bench.py`
* New system `con-leche` (`--leche PATH`; default `LECHE`, the binary above, when it exists, also
  settable with `$CA_LECHE`; `--no-leche` leaves it out). Same interleaved randomized rounds,
  same `perf stat`, verdict from the exit code (the same codes as con-ron).
* The JSON stats now also carry the wall mean and its 95 % t-interval half-width
  (`wall_mean`, `wall_ci`). The markdown table is unchanged.
* `--no-twin` (old spelling `--no-ref` still accepted) for the renamed twin system.

## `e2e-ref` → `con-ron-lean-twin` (choice (b): rename, keep)
`con-ron-lean` (upstream's `ConRon.Arena.Exe`) cannot replace it:
* `e2e-ref` has `--no-prelude`, the reference of `scripts/e2e.py`'s `check_np` entry (the pipeline
  without the prelude stages); `con-ron-lean` always runs the prelude.
* Pins: `e2e-ref --pins=N` checks at `natOpPinSets.take N`; `con-ron-lean` has all or none
  (`--no-pins`). The scripts use `N = 4` (`e2e.PIN_VARIANTS`, all variants), which is
  `con-ron-lean`'s default, so the pins alone would not need a second exe.
* Output: `e2e-ref` prints `verdict CODE MESSAGE` on stdout, which `scripts/e2e.py`'s
  `ref_verdict` parses (the message goes into the report); `con-ron-lean` prints the message on
  stderr. The exit codes are the same.
* `e2e-ref` parses the whole file as one buffer (`parseBytes`, what `front_run` refines);
  `con-ron-lean` reads 4 MiB chunks. Equal by upstream's theorem, but the one-buffer path is the
  one the L frontend is compared with.

So the exe is renamed (`lakefile.toml`, module `ConAgua.E2E.Ref` unchanged), and reports label it
`con-ron-lean-twin`: `scripts/{bench,diff-e2e,e2e}.py`, `ConAgua/E2E/*`, PLAN.md, OVERVIEW.md
§10.3, the link expectations. README.md does not mention it. The verdict cache key is now
`con-ron-lean-twin-<hash>`; the first `--refs` run refilled it. `diff-e2e.py --refs --parallel 16`
after the rename: 740 agree, 0 REFDIFF, 0 unsound, 35 s.

## Measurements
RESULTS
