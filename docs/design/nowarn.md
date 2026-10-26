# Lane nowarn: a warning-free build, and CI with warnings as errors

## Starting point (master 9f037d26)

`lake build` printed no warnings, but only because 619 of the 1227 `ConAgua` modules switched the
linters off, file by file: `set_option linter.unusedSimpArgs false` (466 files),
`linter.deprecated false` (387), `linter.unusedVariables false` (64), `linter.unusedSectionVars false`
(36). The vendored con-leche / con-ron files carry their own upstream suppressions and are not
touched (they are `vendor/` plus patches; a warning there would be an upstream matter).

Census with the file-level suppressions deleted (cold build of the whole project, 23 min at
`LEAN_NUM_THREADS=8`; log `_tmp/nowarn/build1.log`), unique warnings:

| kind | count |
|---|---|
| deprecated (`if_pos`, `if_neg`, `if_true`, `if_false`, `dif_pos`, `dif_neg`, `List.take_succ`, `ite_cond_eq_*`) | 5856 |
| unused simp argument | 2931 |
| unused variable | 258 |
| unused section variable (included hypotheses) | 83 |
| redundant `grind` parameter | 15 |
| `structure S extends P : T` syntax | 10 |
| experimental `vcgen` acknowledgement missing | 8 |
| `simpa` where `simp` closes the goal | 5 |

By module group: Arena 6800, Verdict 1113, Front 717, Scan 246, Checker 189, Final 50, Rom 39.
`vendor/` produces none. Kraken (a Lake dependency, not ours) has 12.

## Tool

`scripts/fix-lean-warnings.py LOG` (from con-ron's script, with Mathlib's
`fix_unused_simp_args.py` vendored next to it, Apache-2.0, attribution in its header). Beyond con-ron's
version it handles what this tree needed:

* deprecations raised inside a macro (the position is the call site, not the identifier): the name is
  renamed file-wide;
* a variable renamed to `_x` has its later uses in the declaration renamed too (`decreasing_by`,
  `simp ... at x` are not seen by the linter);
* a `by` block whose line got longer (a longer lemma name) moves its continuation lines along, or the
  tactic block's column rule no longer parses;
* an unused `← h` for a local hypothesis is dropped (Mathlib's `- h` only works for constants);
* columns of later warnings on a line are shifted by the renames before them.

The tool is deterministic: it is always run from a clean checkout of the baseline sources and the
baseline log, so a tool bug is fixed by rerunning, not by patching its output.

## Batch 1: the tool alone

Baseline sources (file-level suppressions deleted) -> tool run on the baseline log -> full build:
green. 609 files changed (about 6350 lines each way). Of the 9168 baseline warnings, 152 remain
(`_tmp/nowarn/build9.log`): 74 unused section variables, 42 unused simp arguments the first pass
exposed or could not place, 10 `structure ... extends` syntax, 9 redundant `grind` parameters, 8
deprecations the macros hid, 4 `vcgen` acknowledgements, 3 `simpa`, and Kraken's own.

The iterations cost a full rebuild each (about 20 min), because a rename can break a proof in ways
only elaboration shows (column of a `by` block, a variable the linter calls unused but a
`decreasing_by` names). Every such case became a rule of the tool, and the tool was rerun from the
baseline instead of patching the output.
