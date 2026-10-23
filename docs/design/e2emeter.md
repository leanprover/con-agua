# Lane `e2emeter`: critical-path metrics in the progress report

Three metrics (census exe + `scripts/census.py`, columns appended to `docs/progress.csv`, header table and
trend chart in `scripts/gist_report.py`):

* `stagec_pct`: lane indstaget's migration. `docs/stagec-targets.txt` (59 census targets, fixed list). A
  target is done when it is proven, or its `local:` sorry sources contain none of `L.Ind.inferTypeCore_spec`,
  `ensureSortCore_spec`, `isDefEqCore_spec`, `whnf_spec`. Blank when the file is missing.
* `cone_pct`: of the theorems/defs (owner constants, no `proof_N`/`match_N`, types, ctors, recursors) in
  ConAgua/ConRon/ConLeche that `checkerAsm_accepts_remaining` transitively mentions, the share whose axioms
  do not include `sorryAx` (`A cone total clean` line of the census exe, reusing `axiomsOf`'s memo; no
  measurable extra time, census total about 70 s). First value 99.8% (42076/42144): the sorry cone is small
  in absolute terms, so the line sits near the top; the sorry-source count is the sensitive one.
* `sorry_sources`: number of `A src` lines. Trend shows `(1 - n/n0)*100`, n0 the first recorded value.
Older csv rows lack the columns; the chart skips missing points.
