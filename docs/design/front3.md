# Lane `front3`: the frontend phases (0, 1) of the census

## Audit (2026-10-22, master `f960919b`)

Every phase-0 and phase-1 census target with status `todo` or `written` (236: phase 0 123,
phase 1 113), with its non-proven callers from the census graph (`census --targets`), classified:

* **a** L code mirrors it but is not linked (mostly an inlined `⟪…Loop⟫` block or a cited but
  untagged function): link it.
* **b** L covers it with another structure: a `docs/deviations.md` row.
* **c** no L code, the L checker needs it: write it (close twin).
* **d** nothing to write: an accessor, tag constant, error primitive or error text that L inlines
  (`h >> 28`, `E[i].f`, `mk_*`, `abort`); the census already counts such a target proven
  ("covered") once every caller is (as it does for `viewApp`, `inst1Get`, `ETables.get`, …), so
  these move with their callers' proofs in phases 2, 4, 5, 8. No census exclusion needed.
* **w** already `written` and linked (mostly validity-only `refines_part`); what is missing is the
  full refinement proof.

| class | targets | Lean lines | phase 0 (targets/lines) | phase 1 (targets/lines) |
|---|---:|---:|---:|---:|
| a | 40 | 1561 | 4 / 6 | 36 / 1555 |
| b | 28 | 117 | 21 / 80 | 7 / 37 |
| c | 20 | 136 | 0 / 0 | 20 / 136 |
| d | 102 | 274 | 98 / 247 | 4 / 27 |
| w | 46 | 456 | 0 / 0 | 46 / 456 |

Findings:

* The "missing" 1555 phase-1 lines are almost all the scanner loops (`scanXxxLoop`,
  `scanXxxListLoop`, 23 targets, ~1450 lines): con-leche splits each record scanner into a wrapper
  and a loop; L inlines the loop as a `Stmt` block (`⟪appLoop⟫`) in the function tagged with the
  wrapper. Linking them moves phase 1 from 1164 to ~2700 Lean lines with L.
* The one real gap with e2e impact is the ground hoist (`hoistNatOpGround` and its 19 helpers,
  class c): `hoist_ok` aborts where the twin reorders (D18/D24, fixtures `natop_order`,
  `natop_before_ble`, `l-error`).
* The chunked driver (`parseChunks`, `chunkStep`, …) is b: L parses the one buffer at once
  (`front_run` = `parseBytes`, proven). One arena-level lemma `parseChunks [b] = parseBytes b`
  (con-leche has `parseChunks_eq_parseBytes`) would cover the cluster and the error-text targets
  under it.
* Phase 0 is almost all d (accessors, tags, readback D13): nothing to write; it moves with phase
  4/5/8 proofs. `EStore.empty` can be tagged on `arenaD_init` (the initial L memory relates to
  `AState.init EStore.empty`; store only, not the memos).

| target | phase | status | Lean | class | note |
|---|---:|---|---:|---|---|
| `ConRon.Arena.internExpr` | 0 | todo | 1 | a | `L.Rom.romExprsTo` / `romPinsTo` (cited, untagged) |
| `ConRon.Arena.internExprList` | 0 | todo | 2 | a | `L.Rom.romExprsTo` / `romPinsTo` (cited, untagged) |
| `ConRon.Arena.internCIList` | 0 | written | 2 | a | already `rciBlock`; nothing to do |
| `ConRon.Arena.EStore.empty` | 0 | todo | 1 | a | `arenaD_init`: the initial L memory relates to `AState.init EStore.empty` — tag `@[refines]` (store only) |
| `ConLeche.Frontend.isWs` | 1 | todo | 1 | a | inlined; `L.Scan.Leaves.skipWs` / `skipDigits` |
| `ConLeche.Frontend.isDigit` | 1 | todo | 1 | a | inlined; `L.Scan.Leaves.skipWs` / `skipDigits` |
| `ConLeche.Frontend.readNat` | 1 | todo | 8 | a | `L.Front.natDec` (`nat_dec`, any length into the limb pool) |
| `ConLeche.Frontend.utf8Of` | 1 | todo | 1 | a | `L.Front.Unescape.utf8Put` / `escOne`, `escSur` |
| `ConLeche.Frontend.replacementChar` | 1 | todo | 1 | a | `L.Front.Unescape.utf8Put` / `escOne`, `escSur` |
| `ConLeche.Frontend.scanNatListLoop` | 1 | todo | 26 | a | list loop inlined in `scanRules`/`scanIndRecs`/`scanIndTypes`/`scanIndCtors`/`scanNatList`: add to `l_impl` |
| `ConLeche.Frontend.scanStrNameLoop` | 1 | todo | 49 | a | loop inlined (`⟪…Loop⟫` Stmt) in the L scanner tagged with the wrapper: add to its `l_impl` |
| `ConLeche.Frontend.scanNumNameLoop` | 1 | todo | 48 | a | loop inlined (`⟪…Loop⟫` Stmt) in the L scanner tagged with the wrapper: add to its `l_impl` |
| `ConLeche.Frontend.scanAppExprLoop` | 1 | todo | 48 | a | loop inlined (`⟪…Loop⟫` Stmt) in the L scanner tagged with the wrapper: add to its `l_impl` |
| `ConLeche.Frontend.scanLamExprLoop` | 1 | todo | 64 | a | loop inlined (`⟪…Loop⟫` Stmt) in the L scanner tagged with the wrapper: add to its `l_impl` |
| `ConLeche.Frontend.scanForallExprLoop` | 1 | todo | 64 | a | loop inlined (`⟪…Loop⟫` Stmt) in the L scanner tagged with the wrapper: add to its `l_impl` |
| `ConLeche.Frontend.scanLetExprLoop` | 1 | todo | 74 | a | loop inlined (`⟪…Loop⟫` Stmt) in the L scanner tagged with the wrapper: add to its `l_impl` |
| `ConLeche.Frontend.scanConstExprLoop` | 1 | todo | 49 | a | loop inlined (`⟪…Loop⟫` Stmt) in the L scanner tagged with the wrapper: add to its `l_impl` |
| `ConLeche.Frontend.scanProjExprLoop` | 1 | todo | 57 | a | loop inlined (`⟪…Loop⟫` Stmt) in the L scanner tagged with the wrapper: add to its `l_impl` |
| `ConLeche.Frontend.scanRuleLoop` | 1 | todo | 57 | a | loop inlined (`⟪…Loop⟫` Stmt) in the L scanner tagged with the wrapper: add to its `l_impl` |
| `ConLeche.Frontend.scanRuleListLoop` | 1 | todo | 27 | a | list loop inlined in `scanRules`/`scanIndRecs`/`scanIndTypes`/`scanIndCtors`/`scanNatList`: add to `l_impl` |
| `ConLeche.Frontend.scanIndRecLoop` | 1 | todo | 133 | a | loop inlined (`⟪…Loop⟫` Stmt) in the L scanner tagged with the wrapper: add to its `l_impl` |
| `ConLeche.Frontend.scanIndRecListLoop` | 1 | todo | 27 | a | list loop inlined in `scanRules`/`scanIndRecs`/`scanIndTypes`/`scanIndCtors`/`scanNatList`: add to `l_impl` |
| `ConLeche.Frontend.scanIndTypeLoop` | 1 | todo | 134 | a | loop inlined (`⟪…Loop⟫` Stmt) in the L scanner tagged with the wrapper: add to its `l_impl` |
| `ConLeche.Frontend.scanIndTypeListLoop` | 1 | todo | 27 | a | list loop inlined in `scanRules`/`scanIndRecs`/`scanIndTypes`/`scanIndCtors`/`scanNatList`: add to `l_impl` |
| `ConLeche.Frontend.scanIndCtorLoop` | 1 | todo | 106 | a | loop inlined (`⟪…Loop⟫` Stmt) in the L scanner tagged with the wrapper: add to its `l_impl` |
| `ConLeche.Frontend.scanIndCtorListLoop` | 1 | todo | 27 | a | list loop inlined in `scanRules`/`scanIndRecs`/`scanIndTypes`/`scanIndCtors`/`scanNatList`: add to `l_impl` |
| `ConLeche.Frontend.scanAxiomDeclLoop` | 1 | todo | 68 | a | loop inlined (`⟪…Loop⟫` Stmt) in the L scanner tagged with the wrapper: add to its `l_impl` |
| `ConLeche.Frontend.scanDefDeclLoop` | 1 | todo | 96 | a | loop inlined (`⟪…Loop⟫` Stmt) in the L scanner tagged with the wrapper: add to its `l_impl` |
| `ConLeche.Frontend.scanThmDeclLoop` | 1 | todo | 76 | a | loop inlined (`⟪…Loop⟫` Stmt) in the L scanner tagged with the wrapper: add to its `l_impl` |
| `ConLeche.Frontend.scanOpaqueDeclLoop` | 1 | todo | 86 | a | loop inlined (`⟪…Loop⟫` Stmt) in the L scanner tagged with the wrapper: add to its `l_impl` |
| `ConLeche.Frontend.scanQuotDeclLoop` | 1 | todo | 68 | a | loop inlined (`⟪…Loop⟫` Stmt) in the L scanner tagged with the wrapper: add to its `l_impl` |
| `ConLeche.Frontend.scanIndDeclLoop` | 1 | todo | 78 | a | loop inlined (`⟪…Loop⟫` Stmt) in the L scanner tagged with the wrapper: add to its `l_impl` |
| `ConLeche.Frontend.LinePayload.isAbsent` | 1 | todo | 3 | a | `pl != 0` in `L.Scan.Line.scanLineLoop` |
| `ConRon.Arena.Frontend.applyFinalLine` | 1 | todo | 8 | a | `L.Front.frontRun`'s `runLoop` (DriverRefine relates it to `feedChunk`); add to `l_impl` |
| `ConRon.Arena.Frontend.feedChunk` | 1 | todo | 20 | a | `L.Front.frontRun`'s `runLoop` (DriverRefine relates it to `feedChunk`); add to `l_impl` |
| `ConRon.Arena.Frontend.pick` | 1 | todo | 4 | a | inlined in `L.Checker.preparePreludeL` (marks instead of `eraseIdx`) |
| `ConRon.Arena.Frontend.frontOf` | 1 | todo | 7 | a | inlined in `L.Checker.preparePreludeL` (marks instead of `eraseIdx`) |
| `ConRon.Arena.Frontend.prepareD` | 1 | todo | 4 | a | inlined in `L.Checker.preparePreludeL` (marks instead of `eraseIdx`) |
| `ConRon.Arena.Frontend.internExpr` | 1 | todo | 2 | a | `L.Rom.romExprsTo` / `romPinsTo` (cited, untagged) |
| `ConRon.Arena.Frontend.internExprList` | 1 | todo | 6 | a | `L.Rom.romExprsTo` / `romPinsTo` (cited, untagged) |
| `ConRon.Arena.opt2` | 0 | todo | 5 | b | readback: L never reads back (D13 Deliberate); covered once callers (phases 2, 4, 8) are proven |
| `ConRon.Arena.denoteNAux` | 0 | todo | 8 | b | readback: L never reads back (D13 Deliberate); covered once callers (phases 2, 4, 8) are proven |
| `ConRon.Arena.denoteN` | 0 | todo | 2 | b | readback: L never reads back (D13 Deliberate); covered once callers (phases 2, 4, 8) are proven |
| `ConRon.Arena.denoteLAux` | 0 | todo | 10 | b | readback: L never reads back (D13 Deliberate); covered once callers (phases 2, 4, 8) are proven |
| `ConRon.Arena.denoteL` | 0 | todo | 2 | b | readback: L never reads back (D13 Deliberate); covered once callers (phases 2, 4, 8) are proven |
| `ConRon.Arena.readLevelM` | 0 | todo | 12 | b | readback: L never reads back (D13 Deliberate); covered once callers (phases 2, 4, 8) are proven |
| `ConRon.Arena.readNameM` | 0 | todo | 12 | b | readback: L never reads back (D13 Deliberate); covered once callers (phases 2, 4, 8) are proven |
| `ConRon.Arena.NTables.count` | 0 | todo | 1 | b | readback: L never reads back (D13 Deliberate); covered once callers (phases 2, 4, 8) are proven |
| `ConRon.Arena.NTables.get` | 0 | todo | 5 | b | readback: L never reads back (D13 Deliberate); covered once callers (phases 2, 4, 8) are proven |
| `ConRon.Arena.NStore.persCount` | 0 | todo | 1 | b | readback: L never reads back (D13 Deliberate); covered once callers (phases 2, 4, 8) are proven |
| `ConRon.Arena.NStore.scrCount` | 0 | todo | 1 | b | readback: L never reads back (D13 Deliberate); covered once callers (phases 2, 4, 8) are proven |
| `ConRon.Arena.NStore.nodeCount` | 0 | todo | 1 | b | readback: L never reads back (D13 Deliberate); covered once callers (phases 2, 4, 8) are proven |
| `ConRon.Arena.NStore.view` | 0 | todo | 3 | b | readback: L never reads back (D13 Deliberate); covered once callers (phases 2, 4, 8) are proven |
| `ConRon.Arena.LTables.count` | 0 | todo | 2 | b | readback: L never reads back (D13 Deliberate); covered once callers (phases 2, 4, 8) are proven |
| `ConRon.Arena.LTables.get` | 0 | todo | 7 | b | readback: L never reads back (D13 Deliberate); covered once callers (phases 2, 4, 8) are proven |
| `ConRon.Arena.LStore.persCount` | 0 | todo | 1 | b | readback: L never reads back (D13 Deliberate); covered once callers (phases 2, 4, 8) are proven |
| `ConRon.Arena.LStore.scrCount` | 0 | todo | 1 | b | readback: L never reads back (D13 Deliberate); covered once callers (phases 2, 4, 8) are proven |
| `ConRon.Arena.LStore.nodeCount` | 0 | todo | 1 | b | readback: L never reads back (D13 Deliberate); covered once callers (phases 2, 4, 8) are proven |
| `ConRon.Arena.LStore.view` | 0 | todo | 3 | b | readback: L never reads back (D13 Deliberate); covered once callers (phases 2, 4, 8) are proven |
| `ConRon.Arena.EStore.ls` | 0 | todo | 1 | b | readback: L never reads back (D13 Deliberate); covered once callers (phases 2, 4, 8) are proven |
| `ConRon.Arena.EStore.ns` | 0 | todo | 1 | b | readback: L never reads back (D13 Deliberate); covered once callers (phases 2, 4, 8) are proven |
| `ConRon.Arena.Frontend.ParseResultD.ofState` | 1 | todo | 2 | b | L parses the one buffer at once (`front_run` = `parseBytes`, proven); the statement is `parseChunks [b]`. Deliberate row; a proof `parseChunks [b] = parseBytes b` (arena) would cover the cluster |
| `ConRon.Arena.Frontend.sizeError` | 1 | todo | 2 | b | L parses the one buffer at once (`front_run` = `parseBytes`, proven); the statement is `parseChunks [b]`. Deliberate row; a proof `parseChunks [b] = parseBytes b` (arena) would cover the cluster |
| `ConRon.Arena.Frontend.chunkStep` | 1 | todo | 9 | b | L parses the one buffer at once (`front_run` = `parseBytes`, proven); the statement is `parseChunks [b]`. Deliberate row; a proof `parseChunks [b] = parseBytes b` (arena) would cover the cluster |
| `ConRon.Arena.Frontend.chunkFinish` | 1 | todo | 6 | b | L parses the one buffer at once (`front_run` = `parseBytes`, proven); the statement is `parseChunks [b]`. Deliberate row; a proof `parseChunks [b] = parseBytes b` (arena) would cover the cluster |
| `ConRon.Arena.Frontend.parseChunksGo` | 1 | todo | 7 | b | L parses the one buffer at once (`front_run` = `parseBytes`, proven); the statement is `parseChunks [b]`. Deliberate row; a proof `parseChunks [b] = parseBytes b` (arena) would cover the cluster |
| `ConRon.Arena.Frontend.parseChunks` | 1 | todo | 2 | b | L parses the one buffer at once (`front_run` = `parseBytes`, proven); the statement is `parseChunks [b]`. Deliberate row; a proof `parseChunks [b] = parseBytes b` (arena) would cover the cluster |
| `ConRon.Arena.Frontend.internProjTable` | 1 | todo | 9 | b | ROM data never holds a projection table: `rci_ci` refuses kind 6 (Deliberate row) |
| `ConRon.Arena.Frontend.usedConstsGo` | 1 | todo | 21 | c | the ground hoist (D18/D24 Temporary; e2e `natop_order`, `natop_before_ble`) |
| `ConRon.Arena.Frontend.usedConstsRules` | 1 | todo | 6 | c | the ground hoist (D18/D24 Temporary; e2e `natop_order`, `natop_before_ble`) |
| `ConRon.Arena.Frontend.usedConstsBlock` | 1 | todo | 10 | c | the ground hoist (D18/D24 Temporary; e2e `natop_order`, `natop_before_ble`) |
| `ConRon.Arena.Frontend.IDeclaration.usedConsts` | 1 | todo | 7 | c | the ground hoist (D18/D24 Temporary; e2e `natop_order`, `natop_before_ble`) |
| `ConRon.Arena.Frontend.insertNames` | 1 | todo | 5 | c | now `first_declaring` (a linear scan per lookup; cited, untagged): replaced by a real name index with the hoist |
| `ConRon.Arena.Frontend.nameIndex` | 1 | todo | 6 | c | now `first_declaring` (a linear scan per lookup; cited, untagged): replaced by a real name index with the hoist |
| `ConRon.Arena.Frontend.hoistDone` | 1 | todo | 4 | c | the ground hoist (D18/D24 Temporary; e2e `natop_order`, `natop_before_ble`) |
| `ConRon.Arena.Frontend.hoistDropDone` | 1 | todo | 3 | c | the ground hoist (D18/D24 Temporary; e2e `natop_order`, `natop_before_ble`) |
| `ConRon.Arena.Frontend.hoistClosure` | 1 | todo | 11 | c | the ground hoist (D18/D24 Temporary; e2e `natop_order`, `natop_before_ble`) |
| `ConRon.Arena.Frontend.hoistClosure.pushDeps` | 1 | todo | 5 | c | the ground hoist (D18/D24 Temporary; e2e `natop_order`, `natop_before_ble`) |
| `ConRon.Arena.Frontend.hoistClosure.pushOne` | 1 | todo | 6 | c | the ground hoist (D18/D24 Temporary; e2e `natop_order`, `natop_before_ble`) |
| `ConRon.Arena.Frontend.hoistTargetsGo` | 1 | written | 12 | c | the ground hoist (D18/D24 Temporary; e2e `natop_order`, `natop_before_ble`) |
| `ConRon.Arena.Frontend.hoistTargetsGo.hoistDeps` | 1 | todo | 12 | c | the ground hoist (D18/D24 Temporary; e2e `natop_order`, `natop_before_ble`) |
| `ConRon.Arena.Frontend.hoistTargets` | 1 | todo | 2 | c | the ground hoist (D18/D24 Temporary; e2e `natop_order`, `natop_before_ble`) |
| `ConRon.Arena.Frontend.hoistKey` | 1 | todo | 4 | c | the ground hoist (D18/D24 Temporary; e2e `natop_order`, `natop_before_ble`) |
| `ConRon.Arena.Frontend.hoistLt` | 1 | todo | 5 | c | the ground hoist (D18/D24 Temporary; e2e `natop_order`, `natop_before_ble`) |
| `ConRon.Arena.Frontend.movedNames` | 1 | todo | 7 | c | the ground hoist (D18/D24 Temporary; e2e `natop_order`, `natop_before_ble`) |
| `ConRon.Arena.Frontend.reorder` | 1 | todo | 2 | c | the ground hoist (D18/D24 Temporary; e2e `natop_order`, `natop_before_ble`) |
| `ConRon.Arena.Frontend.applyHoist` | 1 | todo | 4 | c | the ground hoist (D18/D24 Temporary; e2e `natop_order`, `natop_before_ble`) |
| `ConRon.Arena.Frontend.hoistNatOpGround` | 1 | todo | 4 | c | the ground hoist (D18/D24 Temporary; e2e `natop_order`, `natop_before_ble`) |
| `ConLeche.Level.hashData` | 0 | todo | 14 | d | con-leche `Expr` hash/beq: keys of the twin`s ROM memo (`EMemo`); L reads the ROM without hashing con-leche values. Covered once `internExpr*`/`internCIList` are proven |
| `ConLeche.levelHasParam` | 0 | todo | 5 | d | con-leche `Expr` hash/beq: keys of the twin`s ROM memo (`EMemo`); L reads the ROM without hashing con-leche values. Covered once `internExpr*`/`internCIList` are proven |
| `ConLeche.levelsHaveParam` | 0 | todo | 3 | d | con-leche `Expr` hash/beq: keys of the twin`s ROM memo (`EMemo`); L reads the ROM without hashing con-leche values. Covered once `internExpr*`/`internCIList` are proven |
| `ConLeche.levelHash` | 0 | todo | 1 | d | con-leche `Expr` hash/beq: keys of the twin`s ROM memo (`EMemo`); L reads the ROM without hashing con-leche values. Covered once `internExpr*`/`internCIList` are proven |
| `ConLeche.levelsHash` | 0 | todo | 3 | d | con-leche `Expr` hash/beq: keys of the twin`s ROM memo (`EMemo`); L reads the ROM without hashing con-leche values. Covered once `internExpr*`/`internCIList` are proven |
| `ConLeche.satRange` | 0 | todo | 1 | d | con-leche `Expr` hash/beq: keys of the twin`s ROM memo (`EMemo`); L reads the ROM without hashing con-leche values. Covered once `internExpr*`/`internCIList` are proven |
| `ConLeche.packData` | 0 | todo | 2 | d | con-leche `Expr` hash/beq: keys of the twin`s ROM memo (`EMemo`); L reads the ROM without hashing con-leche values. Covered once `internExpr*`/`internCIList` are proven |
| `ConLeche.hashOfData` | 0 | todo | 1 | d | con-leche `Expr` hash/beq: keys of the twin`s ROM memo (`EMemo`); L reads the ROM without hashing con-leche values. Covered once `internExpr*`/`internCIList` are proven |
| `ConLeche.bvarOfData` | 0 | todo | 1 | d | con-leche `Expr` hash/beq: keys of the twin`s ROM memo (`EMemo`); L reads the ROM without hashing con-leche values. Covered once `internExpr*`/`internCIList` are proven |
| `ConLeche.fvarOfData` | 0 | todo | 1 | d | con-leche `Expr` hash/beq: keys of the twin`s ROM memo (`EMemo`); L reads the ROM without hashing con-leche values. Covered once `internExpr*`/`internCIList` are proven |
| `ConLeche.lpOfData` | 0 | todo | 1 | d | con-leche `Expr` hash/beq: keys of the twin`s ROM memo (`EMemo`); L reads the ROM without hashing con-leche values. Covered once `internExpr*`/`internCIList` are proven |
| `ConLeche.hash32` | 0 | todo | 1 | d | con-leche `Expr` hash/beq: keys of the twin`s ROM memo (`EMemo`); L reads the ROM without hashing con-leche values. Covered once `internExpr*`/`internCIList` are proven |
| `ConLeche.satSucc` | 0 | todo | 1 | d | con-leche `Expr` hash/beq: keys of the twin`s ROM memo (`EMemo`); L reads the ROM without hashing con-leche values. Covered once `internExpr*`/`internCIList` are proven |
| `ConLeche.satPred` | 0 | todo | 2 | d | con-leche `Expr` hash/beq: keys of the twin`s ROM memo (`EMemo`); L reads the ROM without hashing con-leche values. Covered once `internExpr*`/`internCIList` are proven |
| `ConLeche.Expr.data` | 0 | todo | 59 | d | con-leche `Expr` hash/beq: keys of the twin`s ROM memo (`EMemo`); L reads the ROM without hashing con-leche values. Covered once `internExpr*`/`internCIList` are proven |
| `ConLeche.Expr.hash` | 0 | todo | 1 | d | con-leche `Expr` hash/beq: keys of the twin`s ROM memo (`EMemo`); L reads the ROM without hashing con-leche values. Covered once `internExpr*`/`internCIList` are proven |
| `ConLeche.Expr.beq` | 0 | todo | 1 | d | con-leche `Expr` hash/beq: keys of the twin`s ROM memo (`EMemo`); L reads the ROM without hashing con-leche values. Covered once `internExpr*`/`internCIList` are proven |
| `ConLeche.Name.hashData` | 0 | todo | 10 | d | con-leche `Expr` hash/beq: keys of the twin`s ROM memo (`EMemo`); L reads the ROM without hashing con-leche values. Covered once `internExpr*`/`internCIList` are proven |
| `ConRon.Arena.Idx.tag` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.Idx.tier` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.Idx.index` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.Idx.isPersistent` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.Idx.idxNat` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.ETag.bvar` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.ETag.fvar` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.ETag.sort` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.ETag.const` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.ETag.app` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.ETag.lam` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.ETag.forallE` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.ETag.letE` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.ETag.lit` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.ETag.proj` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.NTag.anonymous` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.NTag.str` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.NTag.num` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.LTag.zero` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.LTag.succ` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.LTag.max` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.LTag.imax` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.LTag.param` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.LsTag.list` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.Memos.empty` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.AState.init` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.fail` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.failDanglingE` | 0 | todo | 2 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.failDanglingLs` | 0 | todo | 2 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.viewSort` | 0 | todo | 2 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.viewConst` | 0 | todo | 2 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.viewFVarIdx` | 0 | todo | 2 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.viewFVarTy` | 0 | todo | 2 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.viewBind` | 0 | todo | 2 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.internFVarE` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.internSortE` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.internConstE` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.internAppE` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.internLetEE` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.internProjE` | 0 | todo | 2 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.viewN` | 0 | written | 5 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.viewLs` | 0 | todo | 5 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.viewLsLen` | 0 | todo | 2 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.inst1LGet` | 0 | todo | 2 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.inst1LSet` | 0 | todo | 5 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.inst1LClear` | 0 | todo | 3 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.Tbl.empty` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.Tbl.size` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.Tbl.node?` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.NTables.empty` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.NStore.empty` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.NStore.dropScratch` | 0 | todo | 2 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.LTables.empty` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.LStore.empty` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.LStore.dropScratch` | 0 | todo | 2 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.LsTables.empty` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.LsTables.get` | 0 | todo | 3 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.LsTables.getLen` | 0 | todo | 3 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.LsStore.empty` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.LsStore.view` | 0 | todo | 3 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.LsStore.persGetLen` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.LsStore.viewLen` | 0 | todo | 3 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.LsStore.dropScratch` | 0 | todo | 2 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.ETables.empty` | 0 | todo | 2 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.ETables.getSort` | 0 | todo | 2 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.ETables.getConst` | 0 | todo | 2 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.ETables.getFVarIdx` | 0 | todo | 2 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.ETables.getFVarTy` | 0 | todo | 2 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.ETables.getBind` | 0 | todo | 5 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.EStore.persGetSort` | 0 | todo | 1 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.EStore.viewSort` | 0 | todo | 3 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.EStore.persGetConst` | 0 | todo | 2 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.EStore.viewConst` | 0 | todo | 3 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.EStore.persGetFVarIdx` | 0 | todo | 2 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.EStore.viewFVarIdx` | 0 | todo | 3 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.EStore.persGetFVarTy` | 0 | todo | 2 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.EStore.viewFVarTy` | 0 | todo | 3 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.EStore.persGetBind` | 0 | todo | 2 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.EStore.viewBind` | 0 | todo | 3 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConRon.Arena.EStore.dropScratch` | 0 | written | 2 | d | accessor / tag constant / error primitive inlined in L (`h >> 28`, `E[i].f`, `mk_*`, `abort`); covered once its callers are proven (as `viewApp`, `inst1Get`, … already are) |
| `ConLeche.Frontend.byteAt` | 1 | todo | 2 | d | `IN.u8[i]` everywhere; covered once its callers (the scanners) are proven |
| `ConLeche.Frontend.ErrTag.describe` | 1 | todo | 20 | d | error text; L only reads ACCEPT (D16). Covered once the driver cluster is |
| `ConLeche.Frontend.ScanErr.render` | 1 | todo | 2 | d | error text; L only reads ACCEPT (D16). Covered once the driver cluster is |
| `ConRon.Arena.Frontend.RecordVerdict.toError` | 1 | todo | 3 | d | error text; L only reads ACCEPT (D16). Covered once the driver cluster is |
| `ConLeche.Frontend.readNat64` | 1 | written | 9 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConLeche.Frontend.readNatAt` | 1 | written | 2 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConLeche.Frontend.hex4` | 1 | written | 6 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConLeche.Frontend.hex3` | 1 | written | 5 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConLeche.Frontend.unescape` | 1 | written | 55 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConLeche.Frontend.scanString` | 1 | written | 14 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConLeche.Frontend.scanQuotedNat` | 1 | written | 6 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConLeche.Frontend.scanBinderInfo` | 1 | written | 7 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConLeche.Frontend.scanNatList` | 1 | written | 3 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConLeche.Frontend.scanHints` | 1 | written | 25 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConLeche.Frontend.scanStrName` | 1 | written | 4 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConLeche.Frontend.scanNumName` | 1 | written | 4 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConLeche.Frontend.scanAppExpr` | 1 | written | 4 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConLeche.Frontend.scanLamExpr` | 1 | written | 4 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConLeche.Frontend.scanForallExpr` | 1 | written | 4 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConLeche.Frontend.scanLetExpr` | 1 | written | 4 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConLeche.Frontend.scanConstExpr` | 1 | written | 4 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConLeche.Frontend.scanProjExpr` | 1 | written | 4 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConLeche.Frontend.scanRule` | 1 | written | 4 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConLeche.Frontend.scanRules` | 1 | written | 4 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConLeche.Frontend.scanIndRec` | 1 | written | 4 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConLeche.Frontend.scanIndRecs` | 1 | written | 4 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConLeche.Frontend.scanIndType` | 1 | written | 4 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConLeche.Frontend.scanIndTypes` | 1 | written | 4 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConLeche.Frontend.scanIndCtor` | 1 | written | 4 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConLeche.Frontend.scanIndCtors` | 1 | written | 4 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConLeche.Frontend.scanAxiomDecl` | 1 | written | 4 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConLeche.Frontend.scanDefDecl` | 1 | written | 4 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConLeche.Frontend.scanThmDecl` | 1 | written | 4 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConLeche.Frontend.scanOpaqueDecl` | 1 | written | 4 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConLeche.Frontend.scanQuotDecl` | 1 | written | 4 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConLeche.Frontend.scanIndDecl` | 1 | written | 4 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConLeche.Frontend.scanLineLoop` | 1 | written | 146 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConLeche.Frontend.scanLineFwd` | 1 | written | 13 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConRon.Arena.Frontend.isNatOpRecord` | 1 | written | 6 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConRon.Arena.Frontend.builtinPreludeE` | 1 | written | 4 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConRon.Arena.Frontend.preludeKey` | 1 | written | 4 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConRon.Arena.Frontend.declares` | 1 | written | 1 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConRon.Arena.Frontend.preparePrelude` | 1 | written | 3 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConRon.Arena.Frontend.internCV` | 1 | written | 5 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConRon.Arena.Frontend.internFire` | 1 | written | 6 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConRon.Arena.Frontend.internRule` | 1 | written | 5 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConRon.Arena.Frontend.internRules` | 1 | written | 6 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConRon.Arena.Frontend.internCaps` | 1 | written | 6 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConRon.Arena.Frontend.internCI` | 1 | written | 25 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |
| `ConRon.Arena.Frontend.internCIList` | 1 | written | 6 | w | already linked (`l_impl`, mostly validity parts); full refinement proof missing |

## Landing 1 (links and the chunk bridge)

* Links (class a): the 23 scanner loops onto their wrappers' L functions; `readNat` → `nat_dec`;
  `LinePayload.isAbsent` → `scan_line_loop`; `utf8Of` → `utf8_put`; `replacementChar` → `esc_one`;
  `isWs`/`isDigit` → `skip_ws`/`skip_digits`; `pick`/`frontOf`/`prepareD` → `prepare_prelude`;
  `feedChunk`/`applyFinalLine` → `front_run`; `internExpr`/`internExprList` (both namespaces)
  and `internPinSet` → `rom_pins_to`/`rom_exprs_to`/`rom_lists_to`. `provenance.py annotate`
  cited `ConRon.Arena.internExprList` at a `private def` of the same name in `CoreTest.lean`
  (fixed by hand: `Intern.lean:50-52`); `locate` should skip private declarations.
* `Front/ChunkBridge.lean`: `parseChunks_single : b.size < USize.size → parseChunks [b] =
  parseBytes b` (as functions of the arena state), by `applyFinalLine_tail` (the final line
  reads only `tailAt b i`: con-leche's `scanLineFwd_eq` and `scanLineSpec`, error offsets
  relative to the line start) and `bytes_extract_tail`. `frontAll_refines_chunks`
  (`@[refines parseChunks]`) is `frontAll_refines` rewritten with it. With the root
  `parseChunks` proven, everything below it that only `parseBytes` and `parseChunks` reach is
  covered: phase 1a (scanner) and 1b (records) are 100 % proven.
* `Arena/InitLink.lean`: `estoreEmpty_refines` (`@[refines EStore.empty]`) = `arenaD_init`.
* Census (in the worktree, after merging master `fd3650c9`): phase 0 177 proven / 5 written /
  114 todo (976 / 988 / 1305 Lean lines); phase 1 (1a+1b+1c) 128 / 18 / 20 (2662 / 2774 / 2907).
  Before (master `f960919b`, docs/progress.md): phase 0 173 / 3 / 120 (972 / 981 / 1305), phase 1
  53 / 47 / 66 (696 / 1164 / 2907).
