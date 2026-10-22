# censusfix

## 1. Cache-free build verdict removed
`scripts/buildstats.py` no longer writes `_tmp/buildcheck.json` (it still builds in its private worktree to
measure file sizes and elaboration time); `census.py` and `gist_report.py` no longer print "last cache-free
build of master"; PLAN.md no longer asks anyone to run it as a safety net.

## 2. Phase 1 split
Phase ids stay as in ROADMAP.md; phase 1 becomes `1a scanner (lexing)`, `1b records (line to record)`,
`1c frontend: intern, prelude, export`, ordered by `phase_key` in `scripts/census.py`.
* 1a: `ConLeche.Frontend.Scan.Fast` names matching `SCANNER_NAMES` (byte classes, number/string/name
  tokens, literal matching, `skipBraced`): 43 targets.
* 1b: the rest of `ConLeche.Frontend.Scan.*` (`scanXxxExpr/Decl`, `scanInd*`, `scanRule(s)`, `scanHints`,
  `scanLine*`, error and id-table types): 50 targets.
* 1c: all of `ConRon.Arena.Frontend.*` (and any other `ConLeche.Frontend.*`): 73 targets.
Totals are unchanged (1352 targets, 816 proven, Lean 6088/9436/11918), `docs/progress.csv` holds totals only,
so history stays comparable. Also fixed: `scripts/dashboard_data.py` parsed the old table without the
"proven locally" column, so `_tmp/dash/phases.json` was `[]` (and `gist_report.py` could not draw the chart);
it now parses the current table and accepts suffixed phase ids. The phase chart label column is wider.

## 3. Census speed
Baseline (idle-ish machine, `--no-build`, standalone): 7 min 57 s wall. Stage times from the new log lines:
targets child 0.8 s; the big link group (438 modules) 331 s; one single-module group 126 s; the rest <10 s.
Cause: `collectAxioms` was called once per linked theorem (about 1900 links), each walking the whole
dependency cone again (the `sorryAx` source search was already memoized). Fix: `axiomsOf` in
`ConAgua/Census/Main.lean`, one memo table per child process, every constant's type and value scanned once
through `Expr.getUsedConstants` (memoized per subterm), axiom sets as small arrays; inductive blocks are
computed as a unit because they are the only cycles. After: 50 s wall (big group 18 s, the single module
10.9 s), output byte-identical to before. Under the coordinator's load the old run needed more than the
600 s guard of `run_guarded` for the exe alone.
Not done, because 50 s is far under the 10 min target: parallel link groups and a per-module olean-hash
result cache. Both would only help the 18 s + 11 s of link work. New: per-stage timing lines on stderr
(lake build, exe total, each link child and its import/links split, analyse, write), and
`CENSUS_TIMEOUT` (seconds, default 600) overrides the exe's guard.
The lake build stage (`lake build census` + 445 modules in census-run) is not measured here (my worktree
is already built); its time is now in the census log. If the next coordinator run is still slow, look there:
a module missing from the shared cache is a real build.
