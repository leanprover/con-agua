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
