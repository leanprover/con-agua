# dedup2: the remaining duplicate lemmas

Lane dedup2 of 2026-11-10 (Opus), from master `52f1aaf0c`. Follow-up of lane dedup
(`syncvocab.md`, "Follow-up: duplicate names"). Pure renames and deletions: no L change, no
statement of a final or refinement theorem changed.

## 1. The scan

An elaboration-time scan of the environment (`_tmp/dedup2/Scan.lean`, run with `scripts/lake env
lean`): it imports every built `ConAgua` module (minus the bench/emit executables, which redefine
`main` or each other's helpers), and groups every theorem of a `ConAgua` module (not generated
`Checker.Asm*`/`Checker.Prog*`, not auxiliary `eq_*`/`match_*`/`_proof_*` declarations) by its type
with binder names and binder kinds erased and universe parameters renamed by position (`Expr`
equality, so instances and implicit arguments must agree). A second pass compares the types
after reducible unfolding (`whnfR` at every subterm): it merges statements that differ only in
`≠` vs `¬ … = …`, `Word` vs `UInt64`, `ArrId` vs `Nat`. Uses come from the `.ilean` reference
index (every `.ilean` under `.lake/build`: module, line, columns), so a rename touches exactly the
references Lean resolved, not text that happens to match.

On master `52f1aaf0c`: 33 612 theorems, 256 groups of the same statement (406 removable names),
16 more groups after reducible unfolding (8 merged, §3).

Tooling (`_tmp/dedup2/`): `Scan.lean` (groups, declaration ranges, binder kinds, simp flag),
`idx.py` (the `.ilean` index), `plan.py` + `decisions.py` (which member stays, under which name,
in which module, and which files need an import), `apply.py` (deletes the other members, puts an
`attribute [...] K` line where one carried attributes, rewrites every reference, adapts the
arguments where the binder kinds differ: `D h` → `K _ _ h` where `K`'s leading binders are
explicit, `D x h` → `K h` where they became implicit and `h` names them, `@K x (by omega)`
otherwise, and adds `import <home>` where the kept module was not visible).

## 2. Batch 1: word arithmetic and word lists, into `L/WordOff.lean`

## 3. Batch 2: the rest

## 4. `finish [erec_grind]`

## 5. Left, and why
