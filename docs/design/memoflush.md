# Lane memoflush: growable memo tables

## Task and scoping (2026-10-23)

Lane compopt found that L's wall time is dominated by page faults and cache misses in the ~40 memo
tables. Each table used its whole `CA_WORDS`-sized array (`n := len >> 2`), and random probes touch
every page. compopt's prototype flushed a table at half load (stamp + 1) instead of aborting, and
gave the memo arrays 2^16 words: wall time 0.73× (geometric mean).

Scoping (reported to the coordinator before any refactor) showed that flushing is the wrong design:

* **Not every `MemoSch` table is a cache.** The prototype flushed all 43 puts, including the
  hoist's name index (array 76, `hnSch`, "first position declaring `n`", con-ron `insertNames`),
  the hoist's visited set (75), `fvarLeavesGo`'s `seen` set (152; a flush duplicates leaves) and
  `RSET` (150, part of the pin-data argument). For these, a flush changes the result.
* **The relations are exact.** `MemoRV` puts L's live slots in bijection with the twin's HashMap,
  and a miss is proved to be the twin's miss (`memoRV_miss`): 246 uses in 43 files, including the
  per-declaration caches in `CoreS`. With "L ⊆ twin", an L miss can meet a twin hit. L would then
  run the miss path while the twin does not. Proving that sound needs a twin-side theorem per
  cached walk: the recomputation gives the cached handle and interns nothing new. Thousands of
  lines.

The design I took instead, which the coordinator approved: **growable tables**, which mirror the
twin's unbounded `Std.HashMap` exactly. No deviation, and the relation keeps its statement.

## Design

* **Header.** Slot `0` of each memo array is a header: word 0 is the stamp the header was written
  at, word 1 the region's first slot `b`, word 2 its slot count `n`. If word 0 is not the live
  stamp, the region is the default one: slot `1`, `MN0 = 2^14` slots (`dfltN`: fewer if the
  array is smaller). `clear` (a new stamp) therefore returns to the default region without
  touching the array, and all-zero memory is still the empty memo.
* **Find.** It reads the header, then probes from `b + home(n)` within `[b, b + n)` and reports
  array slots, as before.
* **Put on a miss** past half load (`n < 2 (count + 1)`) grows the table:
  * It moves every live non-tombstone slot into the fresh region `[b + n, b + 3n)`, by probing for
    a free slot there; a live slot with the same key aborts, which cannot happen.
  * It writes the header (stamp, `b + n`, `2n`) and the moved count, then probes for the new key's
    free slot.
  * Regions only move up within one stamp, so the fresh region holds no live slot: the invariant
    `RegOK` says no slot above the region is live. The only abort is a really full array: the
    region would pass `len / 4`.
* **Hash.** It uses rfhash's `kh` (`k1 ^ (k2 << 32) ^ (k2 >> 32) * golden`), in find, in the rehash
  and in the new key's probe.
* **Tombstones and banks.** A rehash drops tombstones; the map has no entry for them, so this
  matches the twin. Bank-tagged keys (`genW`) are ordinary keys to the table and move like any
  other.

## Proof

* `MemoLib.lean`: the L code is split into named blocks with their own specs: `mslotLoopG`,
  `mslotBlkG` (free-slot probe), `mmoveG` (move one slot), `mstepG`, `mrehashLoopG`, `mgrowBlkG`.
  Models: `mrehashG`, `mgrowAt`, `mputMemE`. `memoFindG_spec`, `memoPutG_spec`,
  `memoClearG_spec` and `memoEraseG_spec` keep their statements. There is no `sorry`.
* `MemoLibRel.lean`:
  * `MemoAt S K VR e b n m f` is the old per-slot relation for an explicit region and lookup
    function `f`. Its run clause also says `(ek x).1 ≠ TOMB`, so a rehash moves exactly the map.
  * `MemoRV` is `CTL` bound ∧ stamp ≠ 0 ∧ `RegOK` ∧ `MemoAt` (own region, `mp[·]?`). The first
    conjunct is still the `CTL` bound, which `RecFireCore` reads as `.1`.
  * `memoRV_grow` keeps the same map, by induction over the rehash with the invariant `RInv`. The
    new region represents `rfun i`, the map restricted to the keys of the old live slots below `i`.
  * `memoRV_set`, `memoRV_clear`, `memoRV_frame`, `memoRV_zero`, `memoRV_erase` and the `MemoRG`
    versions keep their statements.
  * `mputG_frame`, `msetG_frame` and `mclearG_frame` are unchanged: growth writes only `S.arr` and
    `CTL[cs + 1]`.

## Measurements

The prototype was the same L code, spliced into master's `checker.prog`
(`_tmp/memoflush/subst.py`). `bench.py --set default`, 3 interleaved rounds, base = master:

| | base | grow |
|---|---:|---:|
| wall (geomean) | 1 | **0.692** (compopt flush+2^16: 0.732) |
| instructions (geomean) | 1 | 1.029 (header read) |
| c04a | 6.88 s, 2.2 GB | 4.62 s, 1.1 GB |
| beta-ladder | 5.21 s | 3.42 s |
| let-ladder | 2.80 s | 1.80 s |
| irrel_commit | 0.056 s, 89 MB | 0.042 s, 56 MB |
| Init (v4.35.0) | 69.1 s, 6.35 GB, accept | 64.5 s, 2.95 GB, accept |
