# Lane `notneeded`: a "not needed" census status

## Decision (2026-10-23)

Census status `n/a`: the L checker deliberately implements nothing for the target. The list is
`docs/not-needed.md` (target, reason, deviation id), read by `scripts/census.py`, which fails on a
listed target that is not a census target or has its own L function, refinement or part. Shares are
over the targets and Lean/Rust lines minus n/a. A target that is only covered through proven callers
may be listed (nothing implements it, so counting it proven would be wrong): `internProjTable` (D29)
and `movedNames` (D30) were such, they dropped from proven to n/a.

"Pending" (informational): `todo` targets every path to which from the entry passes through a target
with its own link, so they become covered when those callers are proven.

## Classification of the 114 todo targets (master `0095e90`-ish census, 2026-10-23)

* n/a (17 of the todo ones, plus the 2 covered above): the readback cluster (D13: `readLevelM`,
  `readNameM`, `denoteL(Aux)`, `denoteN(Aux)`, and the table/store counts only they use) and the error
  path of unresolved constants (D16: `unresolvedConstsError(L)`, `hasStrLitGo`).
* pending (77): tags, `Idx.*`, store/table accessors, `fail*`, `view*`, `intern*E` wrappers,
  `unwrapOr`, `Go` loops inlined in linked callers, `orElse*`, etc.
* real gaps (9 + 0): initial states `Memos.empty`, `AState.init`, `ModeMemos.empty`, `Caches.empty`,
  `Pins.empty`, `IEnv.empty`, `mkIFEnv(Go)`, `IConstantInfo.name` (relate to `arenaD_init` / `EnvR.init`).
* Doubtful, left todo: the `orElseAttempt` cluster (D4 is a Temporary row; deliberate only with the
  1-variant pin set, D5); `opt2` (reached from the n/a `denoteLAux` and from the proven `denoteLList`);
  `fail`, `failDanglingE/Ls` (error primitives L replaces by `abort`: pending, covered by callers).
