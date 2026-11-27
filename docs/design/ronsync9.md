# Lane ronsync9: the con-ron sync 8021ddac → 62cd8aba

Lane of 2026-11-27 (Opus), con-ron `8021ddac → 62cd8aba` (Tasks #174–#187, 23 commits), con-leche
`bc667610 → 4d398342` (Tasks #633–#638, 45 commits). The closest model was `ronsync8.md`.

## 0. Stage 0: footprint and stage plan

`_tmp/bump-62cd8aba/report.{txt,md,json}` (the coordinator's step 1).

**Upstream.** con-ron: 10 definitions and 1 theorem changed, nothing new or removed. con-leche: 2
definitions changed, 2 new (`mix32`, `mixHash32`), 1 type (`ConLeche.Expr`, its `data` field).
`pins/` did not move, so `pins.bin` and the ROM's pin records stay the same. One test expectation
file moved (`tests/e2e-expected.txt`: `tower_quot`, `basis_quot_lift_type_bad` 2 → 1). Every
patch applies cleanly.

**Toolchain.** Upstream is still on v4.36.0, the same as at ronsync8. Our nightly-2026-10-20 and
patch con-ron/0002 still work. No toolchain bump.

**L items to re-check**: 1 (`checkQuotRecordL`). 42 declarations of ours in 12 files mention a
changed twin function, and 309 mention only the changed type.

**Kind of sync**: very small. No statement renames. The one twin change that executes (#636) is
a change of class of two messages, so the L code stays the same. Ladder estimate: 0.

## 1. What was mirrored (by upstream item)

| upstream | L |
|---|---|
| con-leche #634/#638 (con-ron #187) node hashes combine children with `mix32` (`mixHash32`, lean4#16107) | **no L change: hash bits opaque** (`Arena/ExprMk.lean` header). L's derived words keep only the bvar range, the fvar range and the level-parameter bit. In con-ron (Lean and Rust at 62cd8aba) `derivedE`/`derived_e` are read only through `bvarOfData`/`fvarOfData`/`lpOfData`. `hashOfData` is read only to compute a parent's hash. No cons table or memo uses it as a key: the cons tables hash the child-handle records, and so does L's `ConsLib`. The only effect on us: the seeds of `derOfBindAt` moved (`lam` 19 → 29, `forallE` 23 → 31), so `internE_lam_run`/`internE_forall_run` (internal refinement statements, `LamRefine.lean`, `ForallRefine.lean`) name the new seeds. `DerRel`/`LpColRel` (range bits only, `bvarOfData_pack`) built unchanged. Levels: `level.rs` changed only in comments. Literals: unchanged (`lit_hash`, con-leche/0004's `natBigHash` stays). No `mix32` leaf L function: it would be dead code. |
| con-leche #636 (con-ron #187) a `quot` record off its pin, or before the slots it needs, is `.invalid`; `Quot.sound` off its pin stays `.notImplemented` | `scripts/reasons.tsv`: `R_QUOTIENT_DECLARATION_MISMATCH` and `R_QUOTIENT_DECLARATION_BEFORE` go from `decline` to `reject` (codes 82 → 81, 646 → 645). `R_QUOTIENT_SOUNDNESS_AXIOM` stays `decline`. `check_quot_record`'s code is unchanged: it already split `k == 4` (sound) from the other slots. `cqr_ref`: see §3. No deviation row covered this. |
| con-leche #633, reverted by #637 | Nothing reached us. #633's commits all come after bc667610, and the net con-leche diff bc667610 → 4d398342 has no projection change (`Kernel/Checker.lean`'s diff is only #636). |
| con-ron #187 the concise `--help` (`helpText`, `synopsis`) | Not ported. `main.c` stays minimal (driver simplicity). `TwinAccepts` does not reach these, so `not-needed.md` needs no row. |
| con-leche: "slowest checks" only from 10 s (`Driver/Stats.lean`, `Run.lean`, `Schedule/*`) | twin-side only (statistics output; con-ron prints no such line) |
| con-ron `Monad.lean`, `Handle.lean`, `Denote.lean`, `Exe.lean`, `Generated/Types.lean`, `Refine/*`, `Refine2/*` | twin-side only: citation line moves, and upstream's own proofs |
| con-ron `WFProofs.lean` `EStore.internBind_cases` (seeds 29/31) | twin-side only (no proof of ours names it) |
| con-ron #174–#180 (olean-compare, pin-last, landing pipeline, Aeneas speed) | twin-side tooling |

**Bignum parity**: upstream did not touch `nat.rs`/`nat_decimal.rs` (8021ddac → 62cd8aba).

## 2. Progress log

* 14:39 start. 14:43 bump committed (`c2e1c2bf1`). The first build failed in 2 files
  (`ForallRefine`, `LamRefine`: the seeds), and both were fixed.
* 14:45–14:55 the second build: everything built except `Checker/AsmFileEq` (`checker.s` was
  stale: `check_quot_record`'s two abort codes). `asm_file.py` rewrote 2 lines of `checker.s`,
  and `pins.bin` was unchanged. The third build was green (5210 jobs) with zero `sorry`.
  `--refresh-patches` moved the offsets in con-leche/0001 and con-ron/0001.
* 14:56 con-ron 62cd8aba built in `_tmp/ref/con-ron-62cd` (a worktree of the integrate
  clone, `nix develop -c cargo build --release`).
* 14:57–15:05 `diff-e2e --refs --tests`, `e2e.py --latest ''`. 15:06–15:20 perf.

## 3. Proofs and statements

**The ladder** was not run: no theorem failed for a statement change. The only failures were
the two internal `protoRun` statements with the binder seeds, fixed by hand. Yield: n/a
(estimate 0, as stage 0 said).

**`cqr_ref`** (`QuotRecT.lean`) built unchanged against the new `checkQuotRecord`. Its abort
arms close with `ErrClaim.fail_abort _ _ (by decide)`, which reads the class from the code
(`4 r + c`). So moving the two rows to `reject` matches the twin's `.invalid` with no proof
edit, and `R_QUOTIENT_SOUNDNESS_AXIOM` (`decline`) still matches `.notImplemented`.

**Statement changes**: none in `Final/*`, `Audit/*` or the harness. Internal only:
`internE_lam_run` (`… (a.store.derOfBindAt 19 ty b)` → `… 29 …`) and `internE_forall_run`
(`23` → `31`).

**Deviations**: none added or fixed (no row covered the quotient class).

## 4. Checks

* `diff-e2e --refs --tests` at con-leche 4d398342 (con-ron 62cd8aba from `_tmp/ref/con-ron-62cd`;
  con-ron-lean-twin rebuilt at this branch; no cache): **766/766 agree** (447 accepted, 319 not),
  the kind matches everywhere ("kind differs: 0", so `tower_quot` and `basis_quot_lift_type_bad`
  reject now), UNSOUND/INCOMPLETE/CRASH/TIMEOUT/REFDIFF 0, 7 SKIPPED (`--max-nat-size`, D49).
* `e2e.py --latest '' --no-perf` (same con-ron): 827 fixtures, all agree (482 accept, 55 decline,
  288 reject, 2 time out in both). Compared with ronsync8, 2 declines became rejects (the two
  quotient fixtures in the arena set). The `check_np` link in `e2e.py` fails (`undefined
  reference to ca_start_c`; `main.c` gained that entry with the compare lanes). This is a
  tool issue from before this sync, and the `check` runs are unaffected.
* `provenance.py check --strict`: all exact at con-ron 62cd8aba, con-leche 4d398342, 0 markers
  (1 at the bump). `bump-con-ron.sh --check` ok. `reasons.py --check` ok. `asm_file.py --check`:
  `checker.s` up to date, `pins.bin` unchanged.

## 5. Performance

Against master `9e23582a7`. Both binaries come from `make` on the committed files. Fixture:
`Init` (`_tmp/fixtures/init/init435.ndjson`), load 1–4.

| | master | ronsync9 | Δ |
|---|---:|---:|---:|
| `Init`, `instructions:u`, one thread (2 runs each) | 202 632.9 M | 202 632.9 M | **0.000 %** (±10 k, noise) |
| `Init`, peak RSS, one thread | 628 MB | 628 MB | 0 |
| `Init`, peak RSS, `--jobs=16` | 764 MB | 764 MB | 0 |
| `Init` wall, one thread (12 interleaved paired rounds, exact Wilcoxon) | 14.81 s | 14.81 s | +0.21 % [−0.39, +0.80], p = 0.47 |
| `Init` wall, `--jobs=16` (same) | 2.563 s | 2.571 s | +0.10 % [−0.49, +0.70], p = 0.38 |

The two binaries differ in 8 bytes (two abort-code immediates), so the unchanged instruction
count is what we expect. **Wall caveat**: the first paired rounds ran master's binary from
`_tmp/ronsync9/master/` and ours from the worktree, and gave +0.80 % (p = 0.007, one thread) and
+3.07 % (p < 0.001, 16 threads). The same master binary against a copy of itself in another
directory gave −0.77 % (p = 0.05). The table's rows compare copies in one directory. So a binary's
location can move wall time by up to ~3 % here, and ronsync8's +0.85 % may be the same effect.

**Hash-table behaviour and the share spent hashing** (for lane `hashasm`). L computes no node
hash, so upstream's motivation (fewer 32-bit collisions on `acc + 1` chains in con-leche's
`Expr`-keyed memos) does not apply: L's cons tables and memos are keyed on handles. Where the
time goes (`perf record -e cycles:u`, `Init`, one thread, this branch): the cons-table finds
(`*_find`: the home-slot mix and the linear probe, inlined in each) take **35.6 %** of cycles
(`app_find` 14.6 %, `ilm_find` 5.0 %, `lam_find` 1.9 %, `apd_find` 1.7 %, the rest < 1.3 % each).
`lit_hash` (FNV-1a over limbs) takes 0.05 %. `scripts/asmprof.py` gives no complete `Init`
profile: its instrumented binary rejects `Init` after 18.9 G instructions ("application type
mismatch"), on master's `checker.s` too. This is a tool issue from before this sync.

## 6. What went wrong

* Nothing in the sync itself. The cost was in the measurements: the binary-location effect
  on wall time (above) took one extra pair of control runs to find, and `asmprof.py` and
  `e2e.py`'s `check_np` link are both broken on master (reported, not fixed here).
