# Lane sectionvars: drop unused section hypotheses instead of silencing the linter

## Starting point (master 5f27024c)

71 `ConAgua` modules had `set_option linter.unusedSectionVars false` (nowarn kept it on purpose:
`omit … in` changes the statement). With the option deleted, a build that compiled those modules
itself reported 122 theorems in 54 of them (the other 17 files had no `variable`s left to warn on;
the option was dead).

## Method

Tooling under `_tmp/sectionvars/bin/` (not committed; one-off):

* `omit.py WARN.json`: for each warned theorem, drop the unused names from an attached
  `include … in`, else put `omit … in` before the declaration (before its doc comment and
  attributes). The names are also dropped from `clear` lists in the theorem's own proof.
* `fixcalls.py WARN.json`: at every use `thm a b c …` in `ConAgua`, drop the leading arguments
  that are the omitted hypotheses' names, and `(hL.get "name")` arguments whose lookup belongs to an
  omitted hypothesis. Uses through dot notation with a common name (`hI.mem.only hG`, a different
  `only`) were false positives and reverted by hand.
* By hand: positional `rfl` arguments (`frontRun_refines`, `frontLineK_spec`, `scanLine_spec`),
  data variables that disappear with the hypothesis (`rom` in `lvNode_ok`, `b` in
  `succ_toUInt64`/`declCode_spec`/`hexVal_spec`, `m₀` in `u8PutW_eq`, `n m0` in `foundU_keep`), and
  a `vcgen` lemma list that named a dropped hypothesis it never used (`noNode_step`'s
  `slContains_spec p hc n`).

Each round: build, read the new warnings, apply both scripts. Dropping a hypothesis from a callee
often makes the caller's hypothesis unused too, so the linter reported the next layer upward;
17 rounds until no warning was left (the longest chains: `Scan/RecordsSpec` loop specs → record
specs → `Scan/Line` → `Front/Line` → `Front/FrontRun`; `Scan/Str` byte/hex specs →
`Front/Unescape` → `Front/UnescapeLink`; `Verdict/WhnfM2CE`'s `hpi` through seven `m2c*` lemmas to
`majorToCtorE_of`). Explicit (non-section) hypotheses that became unused were removed too
(`nodeLitStr_spec`'s `hb`, `frontLine_refines`'s `hps`).

`Scan/RecordsSpec` had one `include` of all 55 lookup hypotheses and, after the rounds, an `omit`
of 20 to 40 of them on every one of its 42 theorems; it now has no section-wide `include` and each
theorem `include`s what it uses (6 to 30 names).

## Result

* 176 theorems lost section variables: 1677 hypotheses in all (about 1400 of them program-lookup
  hypotheses of the `Scan/RecordsSpec` and `Scan/Line` scanners, which were included wholesale)
  and 36 unused instance arguments (`[Host]`, `[LawfulHashable κ]`, …).
* Callers: 350 proof lines edited, 7928 → 5873 whitespace-separated tokens (2055 argument
  tokens gone: hypotheses no longer passed, `(hL.get "…")` lookups no longer fetched); no proof
  had established a hypothesis only to pass it along (the unused-variable linter would have flagged
  the `have`; it flagged two theorem parameters, both removed).
* Diff over `ConAgua`: 92 files, +526 −428 lines (68 suppression lines out, 169 `omit … in` and
  `include … in` lines in, the rest shortened calls).
* No statement under `ConAgua/Final/` changed (one helper there, `qwrs_facts`, lost an unused
  `[Host]`); no L program text, `checker.s`, `pins.bin` or `main.c` change; axiom guards unchanged.

Batch 1 landed as master b640df6e. Before it landed, a merge brought in buildtime's faster `Scan`
proofs; its new lemmas (`lineDisp_spec`, the eight `lineArm*_spec` of `Scan/Line`) again included
all 60 lookup hypotheses and lost most of them in three more rounds.

## Batch 2: `Verdict/IndBGrp`, `IndBSum2`

Held back while buildtime reworked them. `grpCE_claim` loses `hIlpf`; `checkSumTeleSlow_claim` and,
one level up, `checkSumTele_claim` lose `hV hApd hCrk`. Their one caller outside, `checkSumTeleE_of`
(`Verdict/IndArmE`), no longer passes them; the three are still binders there because
`CheckSumTeleE` is generated (`err_stmt`) from the refinement theorem's statement, so they are named
`_hV _hApd _hCrk`.

Left: `Verdict/IndBCtor` (one theorem, `cxoE_claim`, loses `hIlpf`), still being reworked by
buildtime; it keeps its suppression until then.
