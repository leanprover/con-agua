# Lane ronsync3: the con-ron sync 01ecb31c → 4ca283d1

Lane of 2026-11-11 (Opus), from master `b4ce0391e`. con-ron `01ecb31c → 4ca283d1`, con-leche
`210a580e → eb2c5939`, upstream tasks #149, #150, #151. Starting kit: docs/design/presync3.md §4;
rules: `scripts/sync-rules/ronsync3.txt`. Decided before the lane: `--olean` stays out (D44); the
`IIndCaps` record keeps its 15-word `EREC` layout (the five dropped fields' words unwritten and
unread), the ROM's `encCaps` drops them; every new or rewritten function gets a generated model and
a declarative refinement (exceptions: `pow_nat`, `size_bytes`); no walk tactic.

## 1. Progress log

* 2026-11-11 23:55 start. Report (`_tmp/bump-4ca283d1/report.{txt,md}`): as presync3 §1 (173 L
  items, 698 mentioners / 404 theorems in 213 files; patches con-leche/0001 and con-ron/0002
  conflict in con-leche's `Kernel/Expr.lean`, `Kernel/Name.lean`). Sent to the coordinator.
* 2026-11-12 00:10–00:50 bump (`55d97287a`). `bump-con-ron.sh 4ca283d1` stopped at the two
  conflicts. con-leche/0001 (the `withPtrEq` shim) is still needed: upstream's pointer-first
  equalities (#551, #554) still use `Init.Util`'s `withPtrEq`/`withPtrEqDecEq`, whose shapes our
  toolchain changed; re-made on the pristine `Kernel/Expr.lean`/`Kernel/Name.lean` (the import,
  `ConLeche.withPtrEq`, `withPtrEqDecEq ConLeche.withPtrEq (fun _ _ _ _ => rfl)` at its six call
  sites). con-ron/0002 had not been applied at all (its `Bridge/Core/Arms/DefeqPeel.lean` hunk
  names a file upstream deleted, which makes `git apply` refuse the whole patch): applied
  without that file; its seven conflicts taken from upstream, then the two toolchain fixes the
  build asked for re-done (`IotaMajor`'s `dsimp +instances`, `StructInstall`'s `try replace`).
  ConLeche, ConRonArena, ConRonBridge build (12 threads, ~25 min with the cache).
* 00:50–01:20 stage 3a (`cad634eb6`): the caps (`decCaps` reads `eta`, `nIdx`, `all`,
  `nparams`, `ctors`; the 15-word record and its offsets kept; `encCaps` and `rci_caps` drop the
  five fields), the maximum `Nat` size (`PinsFull.maxNatSize`: `PINS[72]`, the table 73 words
  and frozen so; `intern_reserved_pins` and `intern_all_pins` write `maxNatSizeDefault`), the
  reader's `Except` (`Arena/ExceptOpt.lean`), the size in bytes (`NatCmpFacts.sizeBytes_pv`:
  `8 * ((pv p o l).log2 / 64 + 1) = 8 * max l 1` for a normalised slice). The projection
  table's words for the η readers already have one lemma, `WhnfCoreProj.decTbl_words` (ctor,
  numParams, numFields): no new one.
* 01:20 stage 3b, first part: the rules file's renames applied to the whole tree (statements
  and proofs, citation lines left alone; 33 files), incl. `internAllPins pins
  maxNatSizeDefault` in the final definitions (see §3).
