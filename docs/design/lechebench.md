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
### Method
* Systems: con-agua (the shipped `./checker`, `make`), con-ron (`_tmp/ref/con-ron-integrate`,
  de06320f, `--jobs=1`, the 4 pin variants), con-leche (above, `--jobs=1`, verified), and
  `con-ron-lean-twin` (con-ron's Lean model compiled by Lean, `--pins=4`; its `Nat` is Lean's
  too, so also GMP).
* `scripts/bench.py --bin L=<checker>`: per round the fixtures in random order and per fixture
  the four systems in random order; `instructions:u` median, wall mean with a 95 % t-interval.
  Load 30–65 on 96 cores, no CPU pinning. Every system accepts every fixture below.
* Runs: the microbenchmarks, 10 rounds, on master `6a44a928c`; master then gained lithash2
  (`053543944`, a hand-written `lit_hash`), merged before the rest: Init (5 rounds) and gf3
  (10 rounds) on `053543944`, and one instructions-only round of both con-agua binaries on the
  microbenchmarks. The con-agua instruction column below is `053543944`'s (lithash2 cut gf3 by
  19.8 % and the microbenchmark fixtures by 0.1–3.4 %); the micro wall columns are from the
  `6a44a928c` run.
* Microbenchmarks (exported with lean4export at v4.35.0-rc3; not in the repository; copies with
  their `.lean` sources and `mk.sh` in the lane's scratch, `lechebench/fx/`). "Per operation" is
  `(W − S) / n`: two files of the same theorems, `n` more in `W`, as the bigmul/asmesc2 rows were
  measured. It includes building the operands (`Nat.sub (Nat.shiftLeft 1 k) i`) and the
  theorem's own check:
  * products: lane mulasm's `S/W1024` (8/64 theorems `Nat.land (Nat.mul a b) 255 = r`,
    1024 × 1024 limbs), `S/W8192` (2/8), `S/W13x9519` (16/128);
  * division: asmesc2's `D2k1k` / `D2k1kW` (4/16 `Nat.div` of 2048 by 1024 limbs);
  * literals (`scripts/biglit_fixtures.py`): `BigLit1e5`, `BigLit1e6` (one literal of 10^5 /
    10^6 digits) minus `BigLit1` (one digit);
  * bitwise: asmesc2's `B1k` (180 theorems `Nat.beq (op a b) (op a b) = true`, op ∈ land, lor,
    xor, 1000-limb operands) and its first 45 theorems;
  * compares: asmesc2's `C1k` (200 theorems `Nat.ble a a = true`, `a` 1000 limbs) and its first
    50 theorems.

### Results

| measure | con-agua instr | con-ron instr | con-leche instr | twin instr | con-agua / con-leche instr | con-agua wall | con-ron wall | con-leche wall | twin wall | con-agua / con-leche wall |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| gf3, whole file | 26.10 G | 50.96 G | 17.87 G | 42.77 G | **1.46** | 1.826 s ± 0.053 | 5.398 s ± 0.073 | 2.393 s ± 0.143 | 6.571 s ± 0.174 | **0.76** |
| Init (init435), whole file | 202.59 G | 165.77 G | 248.54 G | 760.61 G | **0.82** | 20.56 s ± 3.97 | 16.96 s ± 1.47 | 25.62 s ± 1.54 | 96.5 s ± 8.0 | **0.80** |
| per product 1024 × 1024 limbs | 6.22 M | 7.65 M | 2.19 M | 3.57 M | **2.84** | 0.52 ms ± 0.43 | 0.72 ms ± 0.83 | 0.01 ms ± 0.34 | 0.44 ms ± 0.41 | (noise) |
| per product 8192 × 8192 | 157.5 M | 194.4 M | 21.2 M | 19.7 M | **7.42** | 6.9 ms ± 2.1 | 9.0 ms ± 2.2 | 0.8 ms ± 4.0 | (noise) | ≈ 8 |
| per product 13 × 9519 (gf3's shape) | 2.33 M | 4.36 M | 1.92 M | 3.23 M | **1.21** | 0.24 ms ± 0.12 | 0.47 ms ± 0.11 | 0.28 ms ± 0.08 | 0.67 ms ± 0.46 | 0.84 |
| per division 2048 ÷ 1024 limbs | 13.05 M | 221.0 M | 4.91 M | 3.73 M | **2.65** | 1.4 ms ± 1.7 | 18.9 ms ± 6.4 | 0.25 ms ± 0.89 | 4.4 ms ± 8.8 | (noise) |
| per literal of 10^5 digits | 86.4 M | 108.1 M | 6.82 G | 6.82 G | **0.013** | 1.8 ms ± 11.4 | 1.2 ms ± 32.2 | 415 ms ± 38 | 411 ms ± 46 | ≈ 0 |
| per literal of 10^6 digits | 3.38 G | 4.19 G | 640.8 G | 640.8 G | **0.005** | 0.204 s ± 0.064 | 0.231 s ± 0.058 | 42.98 s ± 2.81 | 41.62 s ± 1.05 | 0.005 |
| per bitwise theorem, 1000 limbs | 698 k | 715 k | 720 k | 2.30 M | **0.97** | 0.12 ms ± 0.34 | (noise) | 0.13 ms ± 0.31 | 0.70 ms ± 1.23 | (noise) |
| per compare theorem, 1000 limbs | 454 k | 523 k | 592 k | 1.65 M | **0.77** | 0.08 ms ± 0.06 | 0.17 ms ± 0.18 | 0.24 ms ± 0.28 | 0.26 ms ± 0.24 | (noise) |

Whole-fixture totals of the `S` files (the fixed cost of a ~0.76 MB export with the `Nat`
definitions): con-agua 1.42–1.44 G instructions (0.12 s), con-ron 1.16–1.99 G, con-leche
0.52–0.55 G (0.08 s), the twin 4.3–4.4 G. Peak RSS on gf3 is 3.2–3.7 GB for all four (the
fixture's numbers); on Init con-agua 626 MB, con-ron 409 MB, con-leche 308 MB, twin 1.4 GB.

### Where the comparison is not like for like
* **Fixed cost.** con-leche's start-up and prelude cost about a third of con-agua's
  instructions. Whole-file numbers include it; the per-operation rows cancel it.
* **Literals.** con-leche (and the twin) read a decimal literal one digit at a time,
  `acc * 10 + d` on a GMP number (`readNat`, `ConLeche/Frontend/Scan/Fast.lean` line 108):
  quadratic in the digits, so 10^6 digits take 43 s. con-agua and con-ron convert by divide and
  conquer. These rows measure the reader, not GMP's arithmetic.
* **Operand construction** is in every per-operation row (two `Nat.sub` of 1000+-limb numbers
  per theorem, more for the bitwise and compare files). For the O(n) operations (bitwise,
  compare) it is of the same order as the operation itself, so those rows say "the whole
  theorem is at par", not "the loop is at par".
* **Caching.** All four memoize reductions; a theorem's repeated subterms (the bitwise files
  compute each `op a b` twice) are evaluated once by each. No system skips work the others do,
  as far as the instruction counts show (con-agua, con-ron and con-leche are within
  ±25 % of each other).
* **Verified mode.** con-leche runs `--verified` (its default and its theorem's mode), which
  adds its certification checks; `--trusted` would be a little faster. con-agua has no such
  mode.
* **Wall vs instructions.** con-leche runs more instructions per second than con-agua on gf3
  (17.9 G in 2.39 s vs 26.1 G in 1.83 s), so con-agua is 0.76× its wall at 1.46× its
  instructions. Per-operation wall differences below about a millisecond are within the
  noise of the whole-fixture runs (marked "noise"); the instruction columns are the measure
  there.

### Reading
* Large products: GMP (con-leche, the twin) is 2.8× (1024²) to 7.4× (8192²) fewer instructions:
  con-agua's Karatsuba against GMP's Toom/FFT multipliers and assembly inner loops. Division
  2048 ÷ 1024: 2.65×.
* gf3's shape (13 × 9519) is within 1.2× of con-leche; the O(n) operations (bitwise, compare)
  are at par or ahead.
* Whole files: gf3 1.46× con-leche's instructions but 0.76× its wall; Init 0.82× instructions,
  0.80× wall.
* Literal reading is 80–190× ahead of con-leche (its reader is quadratic).
