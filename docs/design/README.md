# Design journal, one file per lane

Each lane writes its journal to `docs/design/<lane>.md`, created by the coordinator when the lane starts;
only that lane edits it, so landings never conflict on the journal. `DESIGN.md` at the top level is the
history up to 2026-10-22 and is no longer extended. Shared tables live in their own files with one rule each:
`docs/deviations.md` (rows added/changed only by the lane owning the deviation), `docs/ROADMAP.md`
(coordinator), the memory map (in `DESIGN.md`, section "The memory map": change it only in a landing of
its own).
