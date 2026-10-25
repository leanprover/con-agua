# Targets the L checker does not need (census status `n/a`)

`scripts/census.py` reads the table below. A listed target is excluded from the denominators of every
share (proven / proven locally / L written), so 100% is reachable, and is reported in its own `n/a`
column. A row needs a reason and either a `Deliberate` row id of `docs/deviations.md` or `-` (a reason
that is not a deviation, e.g. a function that exists only for the proof).

**Strict rule.** A target belongs here only if the L checker will never need code or a refinement for it:
a deliberate deviation, error text, a mode L does not run, or a pure-proof helper. A target that is
merely covered once its callers are proven (accessors, tags, the hash cluster) is *not* n/a: it stays
`todo` and is counted in the informational "pending" column.

**Staleness.** `census.py` fails if a listed target is not a census target, or has an L function
(`@[l_impl]`), a refinement or a part of its own. A target that is only "covered" through proven callers
may be listed (it is then n/a, not proven), because nothing implements it.

Reviewed by the coordinator, like `docs/deviations.md`.

| target | reason | deviation |
|---|---|---|
| `ConRon.Arena.readLevelM` | readback: the monadic read of a level/name handle back into a value. L works on handles and never reads back | D13 |
| `ConRon.Arena.readNameM` | readback: the monadic read of a level/name handle back into a value. L works on handles and never reads back | D13 |
| `ConRon.Arena.denoteL` | readback: the monadic read of a level/name handle back into a value. L works on handles and never reads back | D13 |
| `ConRon.Arena.denoteLAux` | readback: the monadic read of a level/name handle back into a value. L works on handles and never reads back | D13 |
| `ConRon.Arena.denoteN` | readback: the monadic read of a level/name handle back into a value. L works on handles and never reads back | D13 |
| `ConRon.Arena.denoteNAux` | readback: the monadic read of a level/name handle back into a value. L works on handles and never reads back | D13 |
| `ConRon.Arena.NTables.count` | table sizes used only by the readback functions `denoteN`/`denoteL` (D13); no other caller | D13 |
| `ConRon.Arena.NStore.persCount` | table sizes used only by the readback functions `denoteN`/`denoteL` (D13); no other caller | D13 |
| `ConRon.Arena.NStore.scrCount` | table sizes used only by the readback functions `denoteN`/`denoteL` (D13); no other caller | D13 |
| `ConRon.Arena.NStore.nodeCount` | table sizes used only by the readback functions `denoteN`/`denoteL` (D13); no other caller | D13 |
| `ConRon.Arena.LTables.count` | table sizes used only by the readback functions `denoteN`/`denoteL` (D13); no other caller | D13 |
| `ConRon.Arena.LStore.persCount` | table sizes used only by the readback functions `denoteN`/`denoteL` (D13); no other caller | D13 |
| `ConRon.Arena.LStore.scrCount` | table sizes used only by the readback functions `denoteN`/`denoteL` (D13); no other caller | D13 |
| `ConRon.Arena.LStore.nodeCount` | table sizes used only by the readback functions `denoteN`/`denoteL` (D13); no other caller | D13 |
| `ConRon.Arena.unresolvedConstsError` | error path only: builds the declining/rejecting `CheckError` for an unresolved constant (or a string literal before the String support); L aborts, only `ACCEPT` is read | D16 |
| `ConRon.Arena.unresolvedConstsErrorL` | error path only: builds the declining/rejecting `CheckError` for an unresolved constant (or a string literal before the String support); L aborts, only `ACCEPT` is read | D16 |
| `ConRon.Arena.hasStrLitGo` | error path only: builds the declining/rejecting `CheckError` for an unresolved constant (or a string literal before the String support); L aborts, only `ACCEPT` is read | D16 |
| `ConRon.Arena.Frontend.internProjTable` | the ROM data holds no projection table; `rci_ci` refuses kind 6 | D29 |
| `ConRon.Arena.Frontend.movedNames` | the hoist's receipt of moved records; `preparePrelude` drops it, so L does not compute it | D30 |
