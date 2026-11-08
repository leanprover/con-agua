# Lane ronsync2: con-ron 97eead2d → 01ecb31c, con-leche 0d2f467b → 210a580e

The protocol of PLAN.md, "Bumping the twin". Toolchain unchanged (upstream v4.35.0, ours
nightly-2026-10-20).

## 1. The report (step 1, run by the coordinator)

`_tmp/bump-01ecb31c/report.{txt,md,json}`: con-ron 414 commits, con-leche 211. Definitions:
con-ron 156 changed, 333 new, 90 removed; con-leche 176 changed, 455 new, 111 removed. Types:
con-ron 12 changed, 26 new, 7 removed. L items to re-check: **431** (306 citations changed, 135
gone, 110 through a changed helper below a cited declaration). Declarations of ours that mention
a changed item: 2178 (1483 theorems) in 548 files. Patches: con-leche 0001–0003 and con-ron 0002
CONFLICT, con-ron 0001 applies.

## 2. What changed upstream, and what L takes

| upstream | what | L |
|---|---|---|
| #139 (con-leche #386/#410/#411/#430/#431) | stored recursors checked against the generated ones up to defeq; `RecShape.rhss` → `rules`; `classRecTyCheck`, `classRuleCheck` | mirror |
| #139 (con-leche #452) | `CheckMode` is `verified \| trusted`, `eager : Bool` beside it | mirror |
| #139 (con-leche #450) | observable command line (`--`, `--help`, non-regular input exit 3, `u8` exit codes) | harness (`main.c`) where it applies |
| #140 | proof-only (Theorem 1 loses `μ`/`hμ`) | statements follow where they mention it |
| #141 | stored install + block jobs, two-tier environment | superseded by #143 (only its final state is mirrored) |
| #142, #145, #146 | the `.olean` reader and its memory | **excluded** (deviation, §6) |
| #143 (con-leche #480/#481/#484) | **the install phase goes**: parse, prepare, pins, the stream index (`buildIndex`, records read off once, no inference), then every record's check is a job at the index's view of its position; derived data at use (`formerSortLoop`, `iotaCase3At`, `etaRescueOk`, `projGuardRows`, `litShapeOk`, …); `BlockParts` → `BlockShape`, `StoredRecs` → `StreamRecs`; promotion and the persistent-intern family deleted; the environment a layer over the frozen index | mirror (non-olean path) |
| #144 (con-leche #488/#490/#491/#489) | the `meta` header exactly as line 0; a failed final flush is exit 3; reads through a handle (olean side); flat `uses` (olean, skipped upstream too) | #488 in L's frontend, #490 in the harness |
| #148 | key-free cons tables: 8-byte slot (16-bit stamp, 16-bit hash fragment, handle) | mirror in the generic cons library (helper ronsync2-kf, §7) |

## 3. Plan (stages)

1. **Vendor** (step 2): re-vendor, re-make the conflicting patches (helper ronsync2-vendor for the
   Theorem-1 toolchain fixes).
2. **L code, no proofs**: the data layout first (environment records: `RecRule` without
   `ctorParams`/`k`/`eta`, `IndCaps` without `ruleK`/`sortZ` with `nIdx`, `ProjTable` without
   `structSort`/`guards`, `recInfo`'s `isK`, no `basisDecl`; the environment as an own layer over
   the frozen stream index), then the functions by area (core, inductives, declarations and
   the pipeline, frontend and ROM), then the program, `checker.s`, and verdicts (`diff-e2e`).
3. **Proofs**: the `@[refines]` theorems, then the relations, then the end-to-end chain and the
   Final statements; by file across helpers.
4. **Gates, perf, landing.**

## 4. Progress log

* 2026-11-08 15:27 start. Bump run (`_tmp/ronsync2/bump.log`); con-leche 0001 re-applied without
  its `ParInstall.lean` hunk (file gone); 0002/0003 re-made at the new signatures (`eager`);
  con-ron 0002 re-applied without `Split.lean` (gone), conflicts taken from upstream, the
  toolchain fixes re-done where the build fails (helper ronsync2-vendor).
