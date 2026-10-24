# Lane `kstp-proof`: the KSTP cons tables, proved (journal)

Lane `kstp` prototyped the KSTP slot layout in the cons-table library (`docs/design/conslib.md`,
step 4) with the template specs `sorry`. This lane proves it and lands it (branch `kstp`).

## What changed in the L code

* **The growth's loops count down** (`kzeroL`, `kwalkL` in `ConsLib.lean`): `e := n >> 1; while e
  != 0 { …; x += 8; e -= 1 }` and `e := n; while e != 0 { …; x += 2; e -= 1 }` instead of `while x <
  e`. An address loop against a bound wraps when the bound is near `2^64` and then never exits;
  its model would need a non-termination argument. A counter loop runs exactly `e` times, so its
  model (`kzeroW`, `kwalkW`, `SlotGrowSpec.lean`) is structural recursion on a `Nat`. Cold path
  (the growth), same instruction count per step.
* `kgrowB` is three named sub-blocks (`kgrowH1` … `kgrowH3`) plus the two loops, and `cpSlot`'s
  renaming is written `gO C + (x - 3)`: the same statements, nested so that each piece has its own
  spec (one `vcgen` over the whole head blew up).
* **The entry stub** checks `len ≥ consMinWords = 40` for the slot arrays (was 17).

## The proof

* **Models** (`SlotGrowSpec.lean`): the layout's reads `knW`, `koW`, `krW`; the growth `kgrowM` with
  its probe `kprobeW`, zero loop `kzeroW`, walk `kwalkW`, all generic in the key word's hash `G`.
* **Template specs** (`ConsLibSpec.lean`): the find returns `cprobeW` (reads the value word, then
  the key word; the match only on a fingerprint table), the push writes value and key word and
  grows through `kgrowIf`, `intern_X` returns `consInternM` (which now aborts on an oversized exact
  key, `bigK`). New obligations per table (`ConsOK`): `ihashG` (`ihash` spliced at `gO + 14`, for the
  exact tables and the ones that recompute the hash in the push), `qpure`, `mloc`, `exnk`. The
  record-driven growth hash (`GrowSch`, `ghash`, `HashOK`, `growBlkG`, `growM`) is gone.
* **The relation** (`StoreLib.lean`): `TierR`/`StoreR` are parametric in a key-word predicate `KP`
  (which key words a slot of node `i` may hold); `SlotsOKG` adds "every live slot's key word is
  admissible"; `GrowR` is the layout (`TierLay` per tier, the array below `2^62` words). The
  layout's arithmetic is `lay`/`kslot_toNat`/`kslot_eq_iff`; `pushG` writes two slot words; the hit,
  miss and append lemmas take a `QKeyOK` (a matching node's admissible key word is the query's,
  and on an exact table the converse).
* **The growth** (`StoreGrow.lean`, new): `grow_nat` (the room check as numbers: the new table in
  the tier's half, apart from the old one), `kwalkW_inv` (the walk's invariant, after
  `gnodesW_inv`), `tierR_keep` (the other tier), `storeR_kgrow`.
* **Per table** (`ConsLibRel.lean`): `C.KP` (an exact table: the packed key words `kwQ` of the
  record, both below `2^32`; else the node's hash), `ExactOK` (a new `ConsSch.WF` field: the match is
  key-word equality, the node hash is `qhM` of the key words, …), `qkey_of`, `ghC_kp`,
  `newOK_of`. Users' obligations (`ConsKeyOK`, `RFrame`, `ColFree`) are unchanged.

## Constants

`consMinWords` (40), `consTestWords` (`2 * consMinWords`, the `#guard` memories that do not grow)
and `consGrowWords` (room for two doublings of tier 0) in `SlotGrow.lean`; the entry check
(`capLo`, `capMin`), `CapsOK`, `consR_init`, `arenaR_init` and the test memories use them. The
benches that intern many nodes (`WalkBench`, `LiftBenchComp`) need more room per table than
before (the ping-pong layout keeps a tier's table within its half at offset `0` or `4 n`).

## Measurements

* `bench.py --set all --reps 0` (new asm against master's): 675 fixtures, 0 verdict disagreements.
* Census unchanged (1352 targets, 1328 proven, 0 `sorry`); `checkerFile_accepts_remaining` keeps
  its axioms (`propext`, `Classical.choice`, `Quot.sound`).
* Diff (ConAgua): +3370 / −2091 lines (StoreGrow.lean new, ~720 lines; the old growth proofs and
  the 19 tables' `HashOK` proofs gone).
* Elaboration (`lake env lean`, loaded machine): ConsLibSpec 52 s (master 12 s; the growth block's
  and the push's specs), StoreLib 6.3 s (5.8), StoreGrow 6.9 s (new), ConsLibRel 4.3 s (1.5),
  SlotGrowSpec 0.6 s (6.6). Net about +45 s on the critical path through ConsLibSpec.
