# Lane `slotgrow`: growable intern slot tables (journal)

Branch `slotgrow`, worktree `_tmp/wt/slotgrow`. Context: lane compopt's memory analysis
(`docs/design/compopt.md` on branch `compopt`, "The memory side"): L's wall time is dominated by
page faults and cache misses in hash tables that span their whole array; an oracle that sizes each
intern slot table minimally gives default-set wall 0.71× → 0.505× on top of small memos. The
memo side is lane memoflush (`MemoLib`); this lane does the cons (intern) tables.

## Design (prototype, 2026-10-23)

con-ron's cons tables are `HashMap2`s (`ron/hashmap2.rs`): `insert_at` writes the entry, then
past the load threshold `try_resize` doubles the slot count and rehashes the live entries. L's
were fixed: a tier had `len(XSLOT) / 2` slots and `X_push` aborted at 3/4 load. Now:

* **Slot count** of a tier: `SN0 << G` with `SN0 = 8` and `G`, the **growth exponent**, the
  slot array's last word (zero at the start, so no initialisation). `X_find` reads it instead of
  `len(XSLOT) >> 1`; nothing else changes in the probe. (First prototype: a global per table.
  Dropped: `MemFrame` and every relation frame ignore globals, so a relation reading one would
  need a new frame notion everywhere; and `CTL` has no free words below 64, the store tier's
  range. The slot array is the table's own, already in every frame.)
* **Growth**: `X_push` drops its 3/4-load abort; it reads the exponent before its first store
  and, after its last store, runs the **growth block** when the tier's count passes half the slot
  count (`(c + 1) * 2 > n`). The block is spliced into the push (`⟪growBlkG XGS o⟫`, its nine
  variables shifted past the push's own by `shiftS o`), not a function of its own: a call would
  add a `p.lookup "X_grow"` hypothesis to every spec that runs a push (~30 files, among them
  `ExprMk.lean` and the program-shape lists `WriteSets`, `LeafFns`, `PreLoopWS*`, `CoreErec`).
  The two tiers share the slot array (interleaved), so they share `n`; each tier is at most half
  full.
* **The growth block** (`growB S`, generic in `GrowSch` = slot array, record array, record
  width, count index, hash block): `n' = 2n` (abort unless `2 n' < len(XSLOT)`, the last word
  stays clear), `G += 1`, zero the old table's words `[0, 2n)` eight at a time (the words above
  are zero by invariant), then for both tiers and every node `i < CTL[ca + t]`: the node's hash
  (the schema's hash block: FNV-1a over the record's words written out, or the stored hash word
  for `lit`, `ls`, `nstr`), its home slot, linear probing to the first zero slot, write
  `B t + i + 1`. The records are dense and are the source: the old slots are never read, so the
  table grows in place (no second region, no extra memory, no tombstones).
* All 19 tables use it (`zero` and `anonymous` hold one node per tier and never grow; one code
  path keeps one relation).
* Twin: closer than before (con-ron grows at 3/4 load from 32 slots; L at 1/2 from 8 per tier).
  The fixed tables were covered by the capacity rule, so `docs/deviations.md` has no row for them.
* The frontend tables `esp`/`lsp`/`nsp` (arrays 72–74) are `MemoLib` instances (`memoPutG`): they
  grow with lane memoflush's MemoLib change, not here.

## Prototype measurement

Tooling: `scripts/bench.py` (lane compopt's, branch `compopt`), the program file of master
(`e2e.write_checker`) with the 53 changed functions spliced in from the built store modules
(`_tmp/slotgrow/`), assembled with master's compiler. Variants: `master`, `grow`; `masterF`/`growF`
add lane compopt's memo flush (`compopt_progedit.py flush`) with memo arrays at 2^16 words
(`CA_SMALL`, the compopt harness) to stand in for lane memoflush.

### Results

`bench.py --set default --reps 3` (13 fixtures, load 60–80, cpus 70–73; geometric means of the
ratio to `master`):

| system | instructions | wall |
|---|---:|---:|
| master | 1.000 | 1.000 |
| grow (this lane alone) | 1.078 | 0.804 |
| masterF (memo flush + 2^16-word memos) | 1.031 | 0.692 |
| growF (both) | 1.109 | **0.519** |
| con-ron | 0.435 | 0.363 |

So on top of small memos the cons-table growth gives 0.692 → 0.519 (compopt's oracle: 0.714 →
0.505). Small fixtures reach con-ron (irrel_commit 53 → 24 ms, con-ron 23 ms; RSS 89 → 26 MB).
The big ones gain little or lose a bit on wall (c04a 4.31 → 4.73 s, beta-ladder 3.35 → 3.92 s in
that run; noisy): `bench.py` already picks `CA_WORDS = 2^25` for them, where master's tables are
near the oracle size, and the growth pays its rehashes (one random slot write per node and
doubling; ~2 per node in all). Init (`init435`, 2 rounds, load 105): master 113.6 s → grow 91.3
s; masterF 82.8 → growF 81.9 s, RSS 2.9 → 1.2 GB; instructions +0.4 %.

Instructions: +8 % alone. `asmprof` on c03d: the growths cost 1.0 G of 7.3 G at first (zeroing
one word per loop iteration, ~40 instructions each in the naive compiler, and an FNV loop per
record); unrolling the zero loop by 8, zeroing only the old table and writing each table's hash
out (no loop, no `hk < w` test) brought them to 0.65 G (app 18 growths, 2.2 M re-registrations).
Load 1/4 or growth by 4 instead of 2: no wall gain, more instructions (growth by 4: −0.5..1.5 G
instructions, wall within noise); kept 1/2 and doubling (con-ron doubles, at 3/4).

Verdicts: `bench.py --set all --reps 0` (675 fixtures, the g4 prototype, alone and with the memo
flush): 0 disagreements with master.

## Proof structure

* `SlotGrow.lean`: constants, `rdW`, the slot words (moved from `Store.lean`), `GrowSch`,
  `shiftE/C/S`, the loops and `growB`, `growBlkG` (irreducible, so a push's `vcgen` sees it
  through its spec only).
* `SlotGrowSpec.lean`: the models (`gprobeW`, `gnodesW`, `gtiersW`, `gzeroW`, `growM`,
  `growIf`), `growBlkG_spec` (one spec per loop, plain `vcgen` + normalising `simp` + `grind`;
  helper `slotgrow-blk`), `growIf_frame`, `growIf_set64` (the growth commutes with a column write).
* `StoreLib.lean`: `nSl` reads the exponent; `GrowR` (exponent < 59, table and last word fit,
  the words between are zero, size < 2^63) is a fifth conjunct of `StoreR`; `pushM` = append then
  `growIf`; `internM` takes the node hash; `storeR_growIf` (helper `slotgrow-rel`: zeroing,
  then a per-tier invariant over the re-registration: only zero slots are written, so every
  earlier node's run stays valid).
* Per table: the hash block's spec (`Xhash_ok`, the hash function moved from `XRefine.lean` to
  `XStore.lean`), the push spec posts `growIf … (XpushMem …) c = some s'.mem`, the intern model
  matches on it; `LpColRel.internMD` likewise (column write, then growth; `internMD_mkK` by
  `growIf_set64`).
* `cap_check` also requires every word array to have at least 17 words (`GrowR` at the start:
  2 × 8 slots and the exponent word); `arenaR_init` takes it.
