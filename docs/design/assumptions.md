# Lane `assumptions`: "What the end-to-end theorem still assumes" in the report

- `ConAgua/Census/Main.lean` `asmLines`: for `checkerAsm_accepts_remaining` prints `A` lines (binders pretty-printed, axioms, sorry sources), reusing the axiom and sorry-source memos of `links`; ~0 extra time (one constant).
- `scripts/census.py`: `asm_data`/`write_asm` add a progress.md section and a `<!-- assumptions-json ... -->` comment (the watcher copies only progress.md/csv, so no separate file).
- `scripts/dashboard_data.py` extracts it to `_tmp/dash/assumptions.json`; `scripts/gist_report.py` `assumptions_section` renders it, owners from `docs/assumption-owners.json` (edit it when hypotheses change).
- Checked: census exe on Twin+Remaining (47 s), gist_report without --publish. Full `census.py --write` not run (watcher does).
