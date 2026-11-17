# Lane ronsync7: the con-ron sync 8b088905 → de06320f

Lane of 2026-11-17 (Opus), from master `22f938604`. con-ron `8b088905 → de06320f` (14 commits),
con-leche unchanged at `600d3b58`. Upstream tasks #158 (the bignum's algorithms: Karatsuba,
Knuth D, in-place loops), #159 (subquadratic decimal literals), #160 (every upstream task lands
as a `--no-ff` merge; upstream tooling only).

## Footprint

`scripts/bump-con-ron.sh --report origin/master` (`_tmp/bump-de06320f/report.{txt,md,json}`):

* Vendored files: 6 con-ron proof files (`Generated/Funs.lean`, `Generated/Types.lean`,
  `Refine/Nat.lean`, `Refine2/Frontend/ExportC.lean`, `Refine2/Frontend/Scan/{Spec,Str}.lean`),
  +1 764 −949 lines. con-leche, its `pins/` and its test expectations did not move.
* The Rust side changed in `ron/nat.rs` and `frontend/nat_decimal.rs` only.
* Patches: all six apply unchanged.
* Provenance: **0** L items to re-check, 0 declarations of ours mention a changed twin
  declaration, 0 uncited changed twin definitions. L's limb arithmetic (`Arena/Nat*.lean`) is
  `con-ron: none` (the twin computes on `Nat`), and no L code cites `nat_decimal.rs`.

**Kind of sync**: vendor-only. Both functional tasks are performance rewrites whose public
statements upstream kept unchanged (`*_refines` of `mul`, `div_mod`, `from_decimal`), so there is
nothing to port, restate or re-prove. No rules file, no ladder.

## The bump

`scripts/bump-con-ron.sh origin/master`: re-vendor, patches applied, `provenance.py update` (no
markers), build green (4 572 jobs; only deprecation warnings inside `vendor/`), census 100 %,
zero `sorry` sources (the 2 bad links of `topLitS` were there before).

## Gates

* `scripts/gates.sh`: 15 OK (links needed `scripts/overview-links.sh --update`: OVERVIEW.md cites
  `vendor/UPSTREAM#L3-L4`, whose revision changed; the paragraph names no revision).
* `scripts/provenance.py check --strict`: 1 558 citations, all exact at con-ron `de06320f`, no
  markers before or after. `scripts/bump-con-ron.sh --check`: ok.
* `scripts/asm_file.py --check`: `checker.s` and `pins.bin` up to date (no L change, `pins/`
  did not move).
* `scripts/diff-e2e.py --parallel 16`: 740 agree (441 accepted, 299 not), 0 unsound, 0
  incomplete, 0 crash, 0 timeout.
* No `sorry` and no axiom guard touched (only `vendor/` changed).

## Follow-ups (not in this lane)

* Upstream's motivation for #158 was the arena test `perf/gf3-matrix-product`: con-ron 269.7 G
  instructions, con-leche 18.5 G, con-agua 146.8 G; con-ron now 50.9 G. L's own limb
  multiplication and division (`Arena/NatMul.lean`, `Arena/NatDiv.lean`) are candidates for the
  same algorithms (Karatsuba, Knuth D), and decimal literal reading for #159's split.
