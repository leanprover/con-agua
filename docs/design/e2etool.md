# Lane `e2etool`: e2e-ref "crash" report, provenance findings

* derb reported `scripts/e2e.py` showing e2e-ref as "crash" on every fixture. Not reproducible on master
  (f418b4bf): a fresh worktree, `lake build` of the e2e targets only, full run: 407 agree-accept, con-ron and
  e2e-ref disagree on 0, all three agree on accept/not on 672 of 675 (the rest are timeouts/memout).
  The build target list is complete and `e2e-ref FILE --pins=1` prints `verdict N ...` as the parser expects.
* The one fragile spot: a run whose output had no `verdict` line was classed `crash` AND stored in
  `refcache.json` (keyed by the reference's sources, not the binary), so one transient failure (binary
  mid-rebuild, memory kill) stayed for every later run. Fixed: crashes are never cached, are logged with exit
  code and output tail, and the verdict is read from the first `verdict ` line of stdout+stderr.
* `provenance.py check` clean: `inst1W` cites `instantiate1Fast` (as `inst1A`), `internAllPins_pins`
  cites `ConRon.Bridge.internAllPins_run` with its range (499-620) and qualified name.
