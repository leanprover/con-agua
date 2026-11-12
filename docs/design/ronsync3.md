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
* 2026-11-11 23:57–00:06 bump (`55d97287a`). `bump-con-ron.sh 4ca283d1` stopped at the two
  conflicts. con-leche/0001 (the `withPtrEq` shim) is still needed: upstream's pointer-first
  equalities (#551, #554) still use `Init.Util`'s `withPtrEq`/`withPtrEqDecEq`, whose shapes our
  toolchain changed; re-made on the pristine `Kernel/Expr.lean`/`Kernel/Name.lean` (the import,
  `ConLeche.withPtrEq`, `withPtrEqDecEq ConLeche.withPtrEq (fun _ _ _ _ => rfl)` at its six call
  sites). con-ron/0002 had not been applied at all (its `Bridge/Core/Arms/DefeqPeel.lean` hunk
  names a file upstream deleted, which makes `git apply` refuse the whole patch): applied
  without that file; its seven conflicts taken from upstream, then the two toolchain fixes the
  build asked for re-done (`IotaMajor`'s `dsimp +instances`, `StructInstall`'s `try replace`).
  ConLeche, ConRonArena, ConRonBridge build (12 threads, a few minutes with the cache).
* 00:06–00:15 stage 3a (`cad634eb6`): the caps (`decCaps` reads `eta`, `nIdx`, `all`,
  `nparams`, `ctors`; the 15-word record and its offsets kept; `encCaps` and `rci_caps` drop the
  five fields), the maximum `Nat` size (`PinsFull.maxNatSize`: `PINS[72]`, the table 73 words
  and frozen so; `intern_reserved_pins` and `intern_all_pins` write `maxNatSizeDefault`), the
  reader's `Except` (`Arena/ExceptOpt.lean`), the size in bytes (`NatCmpFacts.sizeBytes_pv`:
  `8 * ((pv p o l).log2 / 64 + 1) = 8 * max l 1` for a normalised slice). The projection
  table's words for the η readers already have one lemma, `WhnfCoreProj.decTbl_words` (ctor,
  numParams, numFields): no new one.
* 00:16 stage 3b, first part: the rules file's renames applied to the whole tree (statements
  and proofs, citation lines left alone; 33 files), incl. `internAllPins pins
  maxNatSizeDefault` in the final definitions (see §3).
* 00:17–00:40 stage 3b/3c on the partial tree, three build rounds. The pipeline at the default
  maximum: `PinsReadyP` also says `a.pins.maxNatSize = maxNatSizeDefault`
  (`internReservedPins_maxNatSize`), so the twin's first write in `internAllPins` is a no-op on
  every state we run it from (`SimZ.getSet`; `internAllPins_steps`/`_pins`/`_tail`/`_u` take it as
  `hmax`, `prefix4_facts` exports it) and `intern_all_pins` writes nothing (`PINS[72]` holds the
  default since `intern_reserved_pins`). Theorem 1's lemmas lost the set theory (#521):
  `view_foldOK`, `job_spec`, `pooledAccepts_bridge` are called without it. The theorems about
  removed twin functions deleted: the `instantiate1Lift` walk's (`WalkLiftRefine`), the
  `towerSlotsAll` ones (`WhnfProjRefine3` whole, `WhnfIotaRefine2`, the knot's `StuckCallees`
  field). Ladder: 2 rounds, 28 failing theorems, **0 closed** at rungs (i)–(iii), 28 tickets
  (`_tmp/ronsync3/tickets-r1.tsv`). Why so few: of 4 388 modules all but 8 elaborate after the
  bump with the old L code — the old proofs still hold of the old L code against the twin's
  unchanged callees; what breaks is where a proof unfolds a changed twin definition (8 modules) —
  and the ladder's rungs only help a theorem whose statement we restated (none of these). The
  real work is the L port of the changed functions, which then breaks their refinements: that
  goes with the fan-out (below), since each helper owns the L code and the proofs of its area.
  Blocked still: 18 modules behind `WhnfM2CRefine` (the old η models) and `KnotMono1` (the store
  monotonicity list: removed twin functions).
* 00:43 fan-out: helpers ronsync3-decl (#493, #494), ronsync3-ind (#495, closers, opener, the
  projection guard), ronsync3-core (#515, #519, #520, KnotMono), on presync3 §4's file sets,
  brief `_tmp/ronsync3/brief-common.md`, 3 build threads each (lead 3).
  **Deviation from presync3 §4's order:** the L code of the rewritten functions is ported by the
  helpers, not before the ladder by the lead: the new L functions do not exist before the port,
  so their statements cannot be restated earlier, and the ladder has nothing to try on them.
