# Design journal, one file per lane

Each lane writes its journal to `docs/design/<lane>.md`, created by the coordinator when the lane starts;
only that lane edits it, so landings never conflict on the journal. `DESIGN.md` at the top level is the
history up to 2026-10-22 and is no longer extended. Shared tables live in their own files with one rule each:
`docs/deviations.md` (rows added/changed only by the lane owning the deviation), the memory map (in
`DESIGN.md`, section "The memory map": change it only in a landing of its own). Parked work and known
limits: `docs/ROADMAP.md`.

**Journals of finished lanes are deleted** once their lasting content is in `OVERVIEW.md`, `DESIGN.md`,
`docs/ROADMAP.md` or the code. Code comments and `DESIGN.md` still cite some of them (e.g.
`docs/design/tierarr.md`), and `DESIGN.md` cites the old `docs/ROADMAP.md` by section, `docs/survey.md` and
`docs/proof-review.md`: read those at the last commit before the prune, e.g. `git show
4f9bfff9:docs/design/tierarr.md` (`git log --diff-filter=D -- docs/` lists every deleted file).
