# perfplot: L vs con-ron performance in the progress report

* `scripts/e2e.py` writes `_tmp/e2e/latest/results.json` (git-ignored) after every full run that measures perf:
  `{date, rev, fixtures, seconds, rows: [{id, size, class, words, perf: {L, con-ron, e2e-ref}}]}`, instructions:u, one run each.
  `words` is the `CA_WORDS` of the accepting run (null: default capacity); L is measured at that capacity.
  Bug fixed on the way: perf originally ran L at the default capacity, so capacity-retry fixtures measured the failing run (bogus ratios < 1).
* `scripts/gist_report.py` reads it: "Performance" section and `perf.svg` (instructions scatter log-log + ratio by size).
* Cost: `python3 scripts/e2e.py --perf-only` (no tracing / interpreter / diff; verdicts from caches) took 9 min wall with a warm
  build and warm reference cache (26 min CPU). It now builds only the e2e targets, not the whole proof tree.
* First numbers (master 8799da8c): 406 fixtures both accept, geometric mean L/con-ron 1.46, median 1.38, range 1.30 to 3.15
  (app-lam); total 263.6 G vs 103.9 G instructions (2.54). Ratio grows with input size (about 1.3 on small inputs, about 3 on the large perf fixtures).
