# Lane consync: keeping in sync with con-ron

## Phase 1: the sync machinery (2026-10-25)

What con-ron does for its con-leche syncs (its CLAUDE.md, DESIGN.md §3.7 and §7 "Bumping
con-leche", `scripts/bump-con-leche.sh`, `pin-last.py`, `sync-shared-con-leche.sh`, `gates.sh`),
and what we took:

* **Read upstream's task sections first.** Their sync starts by reading the upstream task log
  between the two pins; ours now prints the headings (`bump-con-ron.sh --report`).
* **The classifier** (`provenance.py update --auto`): doc-only, moved, moved-doc,
  moved-changed, moved-by-name, changed, deleted. Our `update` already had moved, comment-only,
  changed and gone (a move to another file is found by name). Taken: their EXACT-name rule. Our
  `locate` fell back to every prefix of the cited name, so a gone `Expr.beqGo` would have been
  relocated onto the `Expr` inductive (their task #98 found eleven such). Now a parent is
  accepted only if the citation sat on it at the old revision (a `where` child).
* **Staleness** (their `progress.py` "stale (CHANGED marker)" count): `provenance.py check` now
  prints the marked L items and the `@[refines]` theorems of their twin targets.
* **Work order before the porting**: their `start` prints a work order. Ours is the report,
  which runs before anything moves (`--report`, also the first step of a bump): it is computed
  from the citations at `vendor/UPSTREAM` against the target revision, so it needs no bump.
* **Not taken: "pin last"** (`pin-last.py`: the pin commit is the branch's last, so every
  earlier commit reproduces `update` without `--old`). Our `vendor/` must equal the pristine
  files at `vendor/UPSTREAM` plus the patches at every commit (`--check`, a landing gate), so the
  pin moves in the first commit with the vendored files, and `bump-con-ron.sh` passes `--old`.
* **Not taken: the shared-checkout move** (`sync-shared-con-leche.sh`): we vendor the files, so
  there is no shared package checkout to move.
* **Gates**: their `gates.sh` (build, tests, lint, provenance, pin-last, link gate, pins,
  extract) maps onto `land.sh` plus the sync-specific list now in PLAN.md step 4.

What `provenance.py report` adds over `update --dry-run`: changed twin declarations are matched
by qualified name across all changed files (a declaration moved between files with its code
unchanged is no longer "changed"; `changed_decls` also reports removed ones), the `@[refines]`
theorems of each affected twin target (`Item.refines`, parsed from the attributes), and textual
mentions: the declarations of ours whose code contains a spelling that exactly one twin
declaration owns (a dotted suffix of its qualified name, unique over both revisions' indexes, not
starting with a Lean library namespace, at least five characters when one component), or the
affected L item's name. Mentions of changed types are counted apart: a new structure field
(`IFEnv.tbls`) touches every declaration that names `IFEnv`, which is a measure of how far a
relation change can reach, not of work.

The patch rehearsal runs in a throwaway repository with the old pristine trees committed and the
new ones in the index, so `git apply --3way` there is the bump's own merge. (A first version ran
`git apply --check` in a directory under `_tmp/`, inside our repository: git then silently skips
every path outside that directory and reports success.)

### The report at con-ron ed864140 (con-leche 0d2f467b)

`scripts/bump-con-ron.sh --report origin/master` at master 89538f50: 42 con-ron commits
(tasks #128 to #131), 25 con-leche commits (tasks #362 to #365), same toolchain v4.35.0.

| upstream | kind | changed | new | removed |
|---|---|---:|---:|---:|
| con-ron | definitions | 64 | 20 | 8 |
| con-ron | types | 6 | 0 | 1 |
| con-ron | theorems | 1 | 6 | 0 |
| con-leche | definitions | 58 | 26 | 5 |
| con-leche | types | 9 | 1 | 0 |

* L items to re-check: 102 (100 citations changed, 2 gone, 15 through a changed helper).
  Mechanical: 130 citations moved, 187 comment-only.
* Our declarations that mention a changed twin function or an affected L item, or are its
  `@[refines]` theorem: 526 (354 theorems) in 151 files; 2014 more mention only a changed type
  (`IFEnv` alone 1849).
* Changed twin definitions nothing of ours cites or reaches: 126 (38 new, 13 removed).
* Patches: all apply except `con-ron/0002-bridge-toolchain.patch`, which conflicts in 7
  `ConRon/Bridge` files.
* con-leche `pins/` changed (type pins: 728 lines added), so `pins.bin` and the ROM's
  `INatOpPinSet` record (24 words today) change.
