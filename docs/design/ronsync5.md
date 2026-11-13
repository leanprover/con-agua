# Lane ronsync5: the con-ron sync c78714ac → 42a08640

Lane of 2026-11-13 (Opus), from master `d2b589483`. con-ron `c78714ac → 42a08640`, con-leche
`ca6af099 → 6810492c`. A small sync: con-leche's fourth `Nat`-operation pin variant.

## 0. Upstream

* **Task #153** (con-ron) / **#578** (con-leche): lean4 master's wf-recursion changes respell
  `Nat.bitwise` (and `Nat.land`/`lor`/`xor`), so no committed pin variant matched master's `Init`.
  con-leche adds a fourth variant, `pins/leanprover-lean4-pr-releases-pr-release-16441.json`
  (42 314 lines), and orders `#load_natop_pins` **newest toolchain first**: pr-release-16441,
  nightly-2026-09-10, v4.34.0-rc2, v4.33.0 (before: nightly-2026-09-10, v4.33.0, v4.34.0-rc2).
  con-ron's own change is citations only (line ranges moved) plus its decoder tests, which expect
  four variants.
* **Also in #578:** the four pointer-first equalities (`Name`, `Level`, `Literal`, `Expr`) now
  call `withPtrEqDecEq` through one definition, `ConLeche.ptrDecEq` (`Kernel/PtrDecEq.lean`).
* **Task #154** (the `.olean` reader's ranged read): Rust-side, olean-only, out of scope (D44).

**History.** Upstream rewrote its history: our vendored `c78714ac` is not an ancestor of
`42a08640`, but its tree is the same as `92b2a7e2`'s (`git diff c78714ac 92b2a7e2` is empty). The
real change is `92b2a7e2..42a08640` (8 commits; the report's "46 commits" counts
`c78714ac..42a08640`). `bump-con-ron.sh` and `provenance.py update --old c78714ac` compare trees,
not ancestry, so neither needed a change.

## 1. Report and bump

`bump-con-ron.sh --report 42a08640`: 2 L items to re-check (both "gone"), 10 citations
comment-only, 6 changed or new con-leche definitions that nothing cites (the `ptrDecEq` refactor).
Patch `con-leche/0001-withptreq-shim` conflicted in `Kernel/Expr.lean` and `Kernel/Name.lean`.

* **The shim patch.** Upstream's new `ptrDecEq` is now the only caller of `withPtrEqDecEq`, so
  the patch changes that one call (our toolchain's convention, `withPtrEqDecEq ConLeche.withPtrEq
  (fun _ _ _ _ => rfl) a b k`) instead of five call sites. `Kernel/Name.lean` is pristine again;
  `Kernel/Expr.lean` keeps only the import and `beqMemo`'s `ConLeche.withPtrEq`.
  `vendor/README.md` says so.
* **The two "gone" items** were not gone: `TwinPins.lean` cites the theorem
  `ConRon.Bridge.internAllPins_run`, and `provenance.py` indexed only `ConRon/Arena`. It now also
  indexes `ConRon/Bridge` (`check`, `locate`, `report` agree; the markers were deleted).
* **Markers:** 2 inserted, 0 left. `provenance.py check --strict`: all exact.

## 2. L code and proofs

Nothing assumes the number or the order of the variants. The pin data is an input
(`pins.bin`, DESIGN.md "The pin data as an input"): the final theorem holds at whatever pin list
the buffer decodes to, and the L readers (`pb_check`, `intern_all_pins`, the ROM pin sets) take
the variant count from the buffer. No L function, model or proof changed.

* `pins.bin` is now `romgen pins.bin 4` (`asm_file.py`'s and `e2e.py`'s `PIN_VARIANTS`):
  1 925 014 bytes (was 1 434 062 with three variants). `checker.s` is unchanged.
* Comments that called the first variant "the repository toolchain's" now say "newest first"
  (`Rom/Gen.lean`, `Rom/PinStream.lean`); `main.c`, PLAN.md, OVERVIEW.md, D5 say four variants.
* `romtest` (not a gate) had an unbound `erec_put` since ronsync3; it is bound now. The tool
  itself is killed (SIGKILL) after about 5 minutes even with one variant, also before this lane's
  changes; not pursued.

## 3. Statement changes of the final theorems

None.

## 4. Checks

* `gates.sh`: 15 OK. `bump-con-ron.sh --check` ok.
* `diff-e2e --tests` at con-leche 6810492c with `--refs` (con-ron 42a08640 built in a worktree
  of `_tmp/ref/con-ron`, e2e-ref): 726/726 agree; UNSOUND/INCOMPLETE/CRASH/TIMEOUT/REFDIFF 0.
* `e2e.py --latest ''` with that con-ron: 780 fixtures, all three agree on 778, the other 2 time
  out in all three (as in ronsync4). The references ran at four variants (`e2e-ref --pins=4`).
* Census: 100 % (the 2 "bad links" of `topLitS` were there before).

## 5. Performance

`Init` (`_tmp/fixtures/init/init435.ndjson`), both binaries `make` from the committed files;
`checker.s` is the same, only `pins.bin` differs. One thread on CPU 44, `--jobs=16` on CPUs 24–39.

| | master | ronsync5 | Δ |
|---|---:|---:|---:|
| `instructions:u`, one thread (2 runs each, ±0.0001 %) | 217 205.6 M | 217 233.7 M | +0.013 % |
| peak RSS, one thread | 634–636 MB | 636 MB | +0.3 % |
| peak RSS, `--jobs=16` | 782 MB | 783 MB | +0.1 % |

The extra instructions are the fourth variant's interning at startup and the first (newest)
variant being tried and declined before the v4.35.0 one matches. Wall time was not measured: the
load was 25–27 (the rule is < 12).
