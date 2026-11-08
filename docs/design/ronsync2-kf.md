# Lane ronsync2, helper kf: key-free cons tables (con-ron task #148) in L

Base: master 25e13127. Upstream: con-ron 01ecb31c, `DESIGN.md` "Task #148",
`crates/con-ron-core/src/arena/cons_map.rs`. The twin model (`ConRon.Arena`) does not change with
#148, so no citation changes: this is L's data layout, its library and its refinement.

## 1. The layout

**Upstream** (`ConsMap<I>`): a slot is `CSlot { g: u16, f: u16, h: I }`, 8 bytes; `g` the epoch
stamp (live iff `g` is the table's epoch, at least 1), `f = frag_of(hash)` (the top 16 bits of
`hash * golden`), `h` the handle; the key is `rows[h.row()].0`. A probe reads the row only on a
slot of the current epoch whose fragment matches. `clear` bumps the epoch and vacates every slot
(`O(capacity)`) when it reaches `EPOCH_MAX = 65535`. A push writes the row, then binds the
handle (the fragment recomputed from the row's hash); a resize rehashes every entry from its row.

**Before** (KSTP, `ConsLib.lean`): two words per slot, the value word `B t + i + 1` (`0` free, `B`
the scratch tier's slot base `CTL[62]`, a multiple of `2^32`, raised by `2^32` per
`scratch_reset`) and a key word: an exact table's key itself (a probe that meets it has found
the node and reads no record), else the key's 64-bit hash.

**After**: one word per slot, three fields:

    bits 63…48   f      the key's fragment: bits 31…16 of hash · golden (`fragW`)
    bits 47…0    V      the value: `B t + i + 1` for node i, as before
                        (bits 46…32 the stamp B t / 2^32, bit 47 the growth's mark,
                         bits 31…0 i + 1)

* **Free / live**: `V ≤ B t` free (`0`, or a stamp older than the tier's), else live. Tier 0's
  base is `0`. This is the old test on the low 48 bits (`slotRd`), so the scratch tier still
  empties in O(1) per reset by raising `B` by `2^32`.
* **The stamp is 15 bits**, not 16: bit 47 is the in-place growth's mark (`MARK = 2^47`: a live
  value word plus `MARK`), which our in-place doubling (D38) needs and upstream's
  allocate-and-move resize does not. `V` of a live node is below `2^47 - 2^32 + 2^30 + 1`, so
  the mark never carries into the fragment. `scratch_reset` vacates the 19 scratch tables and
  restarts `B` at `0` when `B ≥ SCBLIM = 2^47 - 2^33` (before: `2^62`), i.e. once every 32 766
  resets (two per declaration), where upstream wraps every 65 535 clears of one table. Every
  scratch table is cleared together with all others here (one base, `CTL[62]`), so per table
  the wrap comes twice as often as upstream's. Deviation D43 (deliberate, verdict-neutral).
* **The fragment**: `fragW h = ((h · golden) >>> 16) &&& 0xffff`. Upstream takes the top 16 bits
  of `h · golden` because its home is the mask of `x = m ^ (m >> 32)` (`m = h · golden`), i.e.
  the low bits of `m` and of `m >> 32`, and the top bits of `m` are those it uses least. Our
  home is `mulhi(x, n)` (D36): the top `log₂ n` bits of `x`, i.e. of `m`. The bits our home uses
  least are the low half of `m`; bits 31…16 are disjoint from the home's for every table up to
  `2^32` slots and depend on all of `h`'s low 32 bits (bits 15…0 of `m` depend only on `h`'s
  low 16). So: the same idea, transposed to our home function.
* **The key** is read from the record: a probe that meets a live slot of its tier whose fragment
  is the query's runs the table's match on the node (`mc`, as the fingerprint tables did
  before). The `exact` fast path (key in the slot) goes: no key in the slot. So `ConsSch.exact`,
  `ExactOK`, `kwE`/`kwQ`/`unpackK` and the exact arms of the find/intern specs are removed.
* **The push** writes the record, then the slot word `(B t + c + 1) ||| fragW h <<< 48`; `h` is
  the push's hash input (tables that store it) or `ihash` recomputed from the key (all others,
  now including the formerly exact ones), as upstream's `insert_at` recomputes it from the row.
* **The growth** (`kgrowB`, in place) moves one word per slot; an entry's new home comes from
  its node's hash, recomputed from its record (`ConsSch.hrec`, a new per-table expression: the
  node's hash from tier `t` and node index `i`; the stored hash word for `lit`/`ls`/`nstr`,
  the FNV hash of the record's key words for the others), as upstream's `move_slots` rehashes
  `rows[s.h.row()].0`. The fragment moves with the value word.

A table of `n` slots is `n` words from word `2 + o` (before `2 n`); the count and offset words,
the minimum `SN0 = 8` slots, growth at load 3/4 and the doubling in place are unchanged. The
frozen image copies `2 + n` slot words per table (before `2 + 2 n`).

**Memory**: every slot halves (16 → 8 bytes) for every table, which is upstream's whole win
(for its `app` table 20 → 8 bytes; ours was already 16).

**Instructions**: a probe now masks the slot word (`V := w &&& 0xffffffffffff`) and shifts out
the fragment instead of loading the key word (same cache line before, so no miss saved); a
formerly exact table reads the record on a fragment hit (as the fingerprint tables did); the
push of a formerly exact table recomputes `ihash` (two multiplies); the growth recomputes each
entry's hash from its record. §4 has the measurements.

## 2. The abstraction

The library's relation keeps its shape (`StoreLib.lean`): `slotW S m t j` is still `0` (free) or
`i + 1` (node `i`), now from the low 48 bits of the slot's one word, and `slotK S m t j` is its
fragment (the top 16 bits) where it was the key word. The key-word predicate `KP` becomes the
same for every table, `K = fragW (hs m t i)` (the node's hash's fragment), and the query's key
word is the query hash's fragment. `TierR`, `SlotsOKG`, `StoreR`, `ConsR` and the user lemmas
keep their statements; the scratch base bound in `StoreR` changes from `2^62 + 2^32` to
`2^47 - 2^32`.

## 3. What changed

* **L code** (`ConsLib.lean`): `kfHead` computes the query's fragment (`fragE`) beside the home;
  `kfLoad` masks the slot word to its value, `kfKey` compares the fragment (`x >> 48 == q`) and
  no longer loads a key word; `kfMatch` always runs the table's match (no exact hit);
  `cpKey` stores the fragment of the stored or recomputed hash; `cpSlot` writes one word; the
  growth (`kgrowH*`, `kupL`, `ktopP/Q`, `kpickB`, `kprobeL`, `kplaceB`, `krehashS`) moves one word
  per slot and hashes an entry from its record (`khashB`, the schema's new `hrec`); `ciChk` checks
  only packed records (`kpk`). `Scratch.lean`: `SCBLIM = 2^47 - 2^33`, the wrap zeroes `n` words.
  `ConsPresize.lean`: room `n + 2`. `Freeze.lean`: the frozen slot extent `2 + n`.
* **Schemas** (`*Store.lean`, `Store.lean`): `exact` removed, `hrec` added (the node's hash from
  its record, the expression of `hsM`), its obligation `ConsOK.hrec` (one `simp`), `exnk` removed,
  `ihashG`/`qpure` now for every table without a stored hash.
* **Models and library proofs**: `SlotGrowSpec` (`vwd`, `kwd`, `pk` and their lemmas; the growth
  models with one word per slot; `G` takes the node, not the key word), `ConsLibSpecBase/Find/
  Grow/Spec` (no `exact` arms; `HRecOK`; `pval_mapE`), `StoreLib` (`slotW`/`slotK` from one word,
  `pushG` one write, no `ex` in the probe; `slotW_pushG`/`slotK_pushG`/`tierR_push`/`tierR_other`
  take the fragment's bound `q < 2^16`; `tierR_hit` no longer needs `QKeyOK`), `SlotRehash`,
  `SlotTop`, `StoreGrow` (one-word slot writes `VW_set`/`KW_set`; `hGh` is "G of a node is its
  hash"), `ConsLibRel` (`KP` is the fragment of the node's hash; `ExactOK`, `kfld`, `fieldsL`,
  `recK`, `kwQ_inj`, `small_of_bigK`, the `list_*` helpers removed; `ghC_eq` replaces `ghC_kp`),
  `ScratchRefine`, `FreezeTruncStore`, `FreezeTruncBase`.
* **Outside the library**: the `ex` field of each table's `C.WF` proof (`*Refine.lean`, 19 files)
  is gone; no statement there changed. `ConsR.congr` lost its three defaulted arguments (its one
  user, `LitRefine`, passes none). The scratch base bound in `StoreR`/`ConsR.resetG` and the head's
  post in `scratchReset_spec`/`scratchEnter_spec`/`scratchDrop_spec` (`< 2^62` → `< 2^47 - 2^33`):
  their users (`Checker`, `CheckerT`, `PhaseBT`) destructure them with `-`, unchanged. The test
  `#guard`s of `Store.lean` (growth abort: `consMinWords` now, since a 36-word array holds two
  doublings) and `ScratchRefine.lean` (the wrap: the new limit, `n` words zeroed).
* `pins.bin` was not regenerated here: linking `romgen` fails in this sandbox (the toolchain's
  `ld` wrapper points into a missing nix store path); the change does not touch the pin data.

## 4. Measurements

Master 25e13127's binary (`make` of its `checker.s`, `_tmp/ronsync2-kf/perf/base`) against this
branch's; `perf stat -e instructions:u`, peak RSS from GNU `time` (`%M`); two alternated runs
each, identical to within 0.02 % (instructions) and 0.2 % (RSS); all accept.

| | instructions:u master | this | Δ | peak RSS master | this | Δ |
|---|---:|---:|---:|---:|---:|---:|
| Init (`init435.ndjson`), default jobs | 221.70 G | 223.85 G | +0.97 % | 732 MB | 643 MB | **−12.1 %** |
| Init, `--jobs=16` | 223.48 G | 225.48 G | +0.90 % | 976 MB | 808 MB | **−17.2 %** |
| `complete_c04a_restart_70` (largest e2e fixture, 9 MB) | 16.500 G | 16.512 G | +0.07 % | 379 MB | 260 MB | **−31.2 %** |

Upstream measured +1.5 % instructions and −23 % peak on `Init` (its peak includes no mapped
input); ours is −89 MB on `Init`, of which the input mapping (346 MB) is not touched by the change.

Wall (`_tmp/bce/wb2.py` interleaved paired rounds, `wstats.py`; data in `_tmp/ronsync2-kf/perf/`):

| | master median | this | rounds, load |
|---|---:|---:|---|
| Init, one thread (CPUs 44,92) | 17.55 s | −0.0 % (Wilcoxon p = 0.54; mean 95 % CI [−1.6, +0.7]) | 14, load 3–5 |
| Init, `--jobs=16` (CPUs 24–39) | 3.71 s | −1.7 % (p = 0.097; mean −4.8 % [−9.8, +0.5]) | 20, load 4–11 |

So: about +1 % instructions, no measurable wall cost, 12–31 % less peak memory.

## 5. Checks

`scripts/diff-e2e.py --parallel 16`: 634/634 agree (0 UNSOUND/INCOMPLETE/CRASH/TIMEOUT).
`scripts/gates.sh`: green (14 OK, `checker-prog` skipped). Not run here, because linking a Lean
executable (`romgen`, `e2e-ref`, `e2e-l`) fails in this sandbox: `asm_file.py`'s `pins.bin`
step and `--check`, and `scripts/e2e.py --latest ''`; `checker.s` was written with
`scripts/lake env lean --run ConAgua/Checker/AsmEmit.lean`, which is `asm_file.py`'s own step,
and `checkerFile_eq` (the `build` gate) accepts it.
