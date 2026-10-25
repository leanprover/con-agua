# Lane `memlay`: memory layout of the store tables (journal)

Branch `memlay`, worktree `_tmp/wt/memlay` (based on `tierswitch`'s phase-1 prototype, fcfe133c:
one array per tier, KSTP slot tables one per tier array). Goal: bring the checker's memory
toward con-ron's. Reference: con-ron's **Rust** (`_tmp/ref/con-ron/crates/con-ron-core/src`):
`ron/hashmap2.rs` (open addressing, linear probing, `home = mix(h) & (n - 1)`, load 3/4,
epoch-stamped slots `Live(u32 stamp, K, V)`, resize = new table of twice the size, old `Vec`
freed), `arena/store.rs` (`Tbl { rows: Vec<(A, D)>, cons: HashMap2<A, I> }`, `AppNode` = two
`u32` handles, derived word `u64`).

## Phase 1: prototypes (unproved)

### How the prototypes are built

Not by `sorry`-rounds over the library (each L change in `ConsLib` rebuilds ~300 proof modules,
an hour per round), but by **rewriting the built program**: `_tmp/memlay/Proto.lean` imports
`ConAgua.Checker.Prog` (the tierswitch prototype, built once), replaces the cons tables'
`X_find`/`X_push` (`ConsLib` generators with the changes below, for all 20 schemas), rewrites
the other functions' record accesses on the AST, and compiles and prints the assembler as
`AsmEmit` does (5 s per variant):

    cd _tmp/wt/memlay && scripts/lake env lean --run ../../memlay/Proto.lean OUT.s LEVERS

With no lever the output is byte-identical to tierswitch's `tier.s`. Every rewrite fails loudly
on a shape it does not know (an address that is not `i * w + f` on a packed array, a block copy
of one, a plain `ld64` of one); none occurred. Harnesses: `_tmp/memlay/main_pages.c`
(tierarr's page counter, plus `CA_PROBE=1`: probe statistics of the `probe` lever, array 250;
`CA_CTL=1`: `CTL[62]`), `_tmp/memlay/main_mm.c` (`CA_MMAP=1`: the input mapped).

### The levers

* **`lf`: load 3/4, `home = mix(h) & (n - 1)`** (cons tables). The twin's choice (hashmap2.rs
  `LOAD_NUM/LOAD_DEN`, `home_index`); ours was 1/2 and `mulhi(mix(h), n)`. The push grows when
  `4 (c + 1) > 3 n`.
* **`gip`: grow in place.** The table stays at word 2 of its tier array (word 1, the offset,
  stays 0); a growth zeroes the upper half (`n` new slots) and rehashes in place: mark every
  live slot of the lower half (bit 63 of the value word), then for `i = 0 ‥ n-1`, while slot `i`
  is marked: unmark, probe from the entry's new home past live *unmarked* slots to the first slot
  that is free, marked, or `i` itself; if it is `i`, leave the entry; if free, move it there and
  free `i`; if marked, swap (the displaced marked entry lands in `i` and is processed next).
  (absl's in-place rehash, specialised to linear probing.) Each step unmarks one entry, so it
  ends after `#entries` steps. Invariant: every unmarked entry is reachable from its home through
  unmarked live slots only; marked slots only turn into unmarked or free ones, so no path ever
  crosses a slot that later becomes free. No wrap-around special case (the earlier idea, "start
  after an empty slot and process cyclically", breaks when an upper-half probe wraps past `2n-1`
  into the unprocessed lower half). Stale scratch slots (value ≤ `B 1`) count as free throughout.
* **`pk`: 32-bit handle fields in records.** `app`, `max`, `imax`, `const`, `lam`, `forallE`:
  2 words → 1 (`f | a << 32`); `letE` 3 → 2 (`ty | v << 32`, `b`); `proj` 3 → 2 (`n | e << 32`,
  `i`). Loads `x & 0xFFFFFFFF` / `x >> 32`; the push writes the combined word (records are
  written once, by the push only); room tests see the doubled capacity.
* **`spk`: one-word slots** (on top of `lf` + `gip`): `fp:16 | mark:1 | stamp:19 | index+1:28`.
  The fingerprint is the hash's top 16 bits; the scratch stamp moves from bit 32 to bit 28
  (`scratch_reset` adds `2^28`, aborts from stamp `2^19 - 1`); every table becomes a fingerprint
  table (the `exact` tables' 64-bit key word does not fit): a fingerprint hit runs the schema's
  match on the record. The growth recomputes each node's hash from its record (the stored hash
  word for `lit`/`nstr`/`ls`, else `ihash` of the key fields).
* **`mlf`: memo tables at load 3/4** (the growth test of every `X_put`; home unchanged).
* **`eid`: `EID` (export id → handle) at 32 bits per entry** (read: shift/mask; write:
  read-modify-write, abort if the value is not below `2^32`).
* **`mmap`** (harness only): map the input `MAP_PRIVATE`, `PROT_READ` instead of reading it.

### Init: touched pages per array (THP off) and peak RSS

`main_pages.c`, `CA_NOTHP=1`, all 318 arrays; MB = resident 4 KB pages.

| array | base (tierswitch) | lf | lf+gip | pk | lf+gip+pk | spk (+lf+gip) | spk+pk | spk+pk+mlf+eid |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| ASLOT (app cons) | 448 | 192 | 128 | 448 | 128 | 64 | 64 | 64 |
| AREC (app rows) | 79.4 | 79.4 | 79.4 | 39.7 | 39.7 | 79.4 | 39.7 | 39.7 |
| LASLOT | 48 | 28 | 16 | 48 | 16 | 8 | 8 | 8 |
| EID | 46.5 | | | | | | | 23.3 |
| FASLOT | 28 | 12 | 8 | 28 | 8 | 4 | 4 | 4 |
| ASLOT⟨1⟩ | 28 | 12 | 8 | 28 | 8 | 4 | 4 | 4 |
| NSSLOT | 12 | 7 | 4 | 12 | 4 | 2 | 2 | 2 |
| **all arrays** | **1003** | 690 | 574 | 953 | 548 | 512 | 462 | **430** |
| **peak RSS** | **1311** | 1025 | 915 | 1292 | 879 | 851 | 801 | **770** |

(POOL 138 MB, ADER 40 MB, EREC 14 MB unchanged; POOL read 114 MB once, noise of the counter.)
The rest of the RSS is the input buffer (346 MB). All variants accept Init.

**`lf` alone** gives most of the slot-table cut on Init: 5.2 M `app` nodes need 2^24 slots at
load 1/2 and 2^23 at 3/4. **`gip`** removes the old copies: with ping-pong a table of `n` slots
keeps the copies of `n/2` (and `n/4`, …, wherever the offsets overlap) resident.

### Probe lengths (Init, cons tables, slots inspected per find)

| | tier 0 | tier 1 |
|---|---:|---:|
| base (1/2, `mulhi`) | 1.231 | 1.019 |
| lf (3/4, mask, ping-pong) | 1.728 | 1.040 |
| lf + gip | 1.726 | 1.040 |
| 7/8 + gip | 2.135 | 1.048 |
| spk (3/4, gip, one-word slots) | 1.726 | 1.040 |

76.8 M finds in tier 0, 158.9 M in tier 1. 7/8 gives no memory on Init (the counts do not cross
the 3/4 boundary at these sizes) and costs probe length: stay at the twin's 3/4.

### mmap of the input (harness only)

Init, THP on, `/proc/self/status` at the end:

| | VmHWM | RssAnon | RssFile |
|---|---:|---:|---:|
| read (now) | 1404 MB | 1402 MB | 2.5 MB |
| mmap | 1357 MB | 1025 MB | 325 MB |
| mmap + `MADV_SEQUENTIAL` | 1378 MB | 1016 MB | 333 MB |

Peak RSS barely moves (−3 %): the mapped file's pages count in RSS once touched, and nothing
unmaps them (the user ruled out a release hook). What mmap saves is the second copy: the anon
buffer (377 MB less anonymous memory) next to the page cache; on a machine where the export is
in the page cache anyway that is real memory, but not what `ru_maxrss` reports.

### Scratch resets

Init: `CTL[62]` ends at 230 425 · 2^32, i.e. 230 425 scratch resets. A 19-bit stamp (lever
`spk`) holds 524 287: enough for Init, not for a larger library. The twin's answer (hashmap2.rs
`clear`): at `EPOCH_MAX` vacate the slots the hard way and restart the epoch. The one-word slot
needs that wrap arm.

### Speed (`bench.py --set full --reps 3`, 18 fixtures, load ~37; `_tmp/memlay/bench_full.{log,json}`)

Geometric means of the ratio to base (tierswitch prototype):

| system | instructions | cycles | wall |
|---|---:|---:|---:|
| lf + gip | 1.044 | 1.024 | 1.013 |
| pk | 1.000 | 0.976 | 0.974 |
| lf + gip + pk | 1.043 | 0.995 | 0.975 |
| spk + pk | 1.028 | 0.991 | 0.977 |
| spk + pk + mlf + eid | 1.031 | 1.018 | 1.005 |

Peak RSS (MB), base → lf+gip → lf+gip+pk → spk+pk → spk+pk+mlf+eid:

| fixture | base | lf+gip | lf+gip+pk | spk+pk | all |
|---|---:|---:|---:|---:|---:|
| app-lam | 3199 | 2235 | 1930 | 1289 | 1280 (−60 %) |
| beta-ladder | 932 | 682 | 582 | 387 | 388 (−58 %) |
| let-ladder | 481 | 365 | 321 | 219 | 213 (−56 %) |
| eager_open_nat_control | 1194 | 656 | 569 | 420 | 419 (−65 %) |
| c04a_restart_70 | 564 | 446 | 400 | 280 | 281 (−50 %) |
| c05b | 822 | 675 | 651 | 614 | 625 (−24 %) |
| c03d_pi_depth_1030 | 305 | 156 | 140 | 108 | 108 (−65 %) |
| Init (init435) | 1383 | 972 | 922 | 825 | 801 (−42 %) |
| small fixtures | 27 | 27 | 27 | 27 | 27 |

Cycles and wall are within the noise of this machine (spreads 20–180 %); the instruction
counts are exact. Where the instructions go (let-ladder, 9.77 G base):

* **The home function.** With our hashes, `mix(h) & (n - 1)` clusters: tier 1 of let-ladder
  probes 1.30 slots per find at 1/2 with `mulhi`, 1.81 at 1/2 with the mask, 1.82 at 3/4 with
  `mulhi`, 3.30 at 3/4 with the mask. Lever **`hi`** keeps `mulhi(mix(h), n)` (top bits) with
  the in-place growth: the marked rehash above works for *any* home function (it never uses
  "`i` or `i + n`"), so the twin's mask is not needed for growing in place. With `hi`: 1.82.
  The home is verdict-neutral (hashmap2.rs says so itself); keeping `mulhi` would be a
  deliberate deviation (`docs/deviations.md`), with this measurement as the reason.
* **The in-place growth** costs about +0.4 G on let-ladder (1/2 + mask: 10.28 → 10.71 G with
  `gip`): ~35 instructions per slot of the 12.6 M slots its tier-1 tables grow through (mark
  pass, rehash pass, hashing every live key again; naive code, every access bounds-checked).
* **Load 3/4** costs +0.5 G there (1/2 → 3/4 with `mulhi`: 10.00 → 10.54 G, the longer probes).
* **pk** is instruction-neutral (the shift/mask per field read against one record word instead
  of two) and cycle-positive.
* **spk** is cheaper than two-word slots (one load per probe step; the record read on a
  fingerprint hit replaces the 64-bit key compare).

## What fits in 32 bits (user decision 1)

Handles are `u32` in con-ron (bits 31–28 tag, 27 tier, 26–0 index). Record fields:

| store | 32-bit (handles) | 32-bit with a check | 64-bit |
|---|---|---|---|
| app | f, a | | |
| succ / sort | u | | |
| max / imax | u, v | | |
| param | n | | |
| const | n, us | | |
| letE | ty, v, b | | |
| fvar | ty | i (fvar counter) | |
| lam / forallE | ty, b | | |
| proj | n, e | i (field index) | |
| bvar | | i (de Bruijn index) | |
| name str | p | l (length) | o (pool offset, tier tag bit 40), h (hash) |
| name num | p | | i (the number) |
| lit | | kind, l | o, h |
| level list | | l | o, h |
| derived columns (DER) | | | the derived word (twin: `u64`) |
| HP / LP columns | | one bit each | |
| slots | index + 1 (28 bits), scratch stamp (twin: `u32`) | | |
| id tables NID / LID / EID (dense) | the handle | | |

The prototype packs only the handle fields of the multi-field stores (`app`, `max`, `imax`,
`const`, `lam`, `forallE`: one word; `letE`, `proj`: two). The single-handle stores (`succ`,
`sort`, `param`, `bvar`, `zero`, `name anon`) would need two nodes per word (a dynamic shift and a
read-modify-write in the push); they are small on every fixture measured.

### (a) packing in the accessors vs (b) a `u32` array kind

**(a)** is library-local: `TRec.ld`/`TRec.st`/`TRec.ad`, `tfld`'s definition and its lemmas,
the push's record write (one combined word: records are written once, whole, by the push only),
the schemas' `mc`/`room`; proofs outside the library state everything with `tfld` and do not
change. It needs the fields below `2^32` at the push: `intern_X` of the `exact` two-key tables
already aborts otherwise (`ciChk`); `letE`/`proj` need the same check (or an invariant that
handle words are below `2^32`). Cost: one `and`/`shr` per field read (measured: neutral).

**(b)** adds a third array kind to `Mem` (`arr32`), the semantics (`ld32`/`st32`/`len32`, tiered
too), the frame lemmas and write sets, the compiler and its simulation proof (32-bit `mov`
forms against Kraken's semantics), the ABI layout (`ca_slot` per kind), the capacity check —
every proof that mentions `Mem`'s fields. It saves the shift/mask, which costs nothing
measurable, and it does not help the slot words (`spk` packs three fields into 64 bits). It
would help only tables written at random in 32-bit units (the id tables: (a) does those with a
read-modify-write, prototyped as `eid`). Recommendation: **(a)**; no compiler work for lane
tiercost.

## Against the twin (con-ron's Rust), Init

| structure | con-ron | ours, base | lf+gip | lf+gip+pk | spk+pk |
|---|---|---|---|---|---|
| app cons table | 2^23 slots × 20 B = 160 MB | 448 MB tier 0 + 28 MB tier 1 (16 B slots, ≤ 1/2, old copies resident) | 128 + 8 | 128 + 8 | 64 + 4 |
| bytes per app cons entry | 20 / load ≥ 26.7 | ≥ 32, plus copies | ≥ 21.3 | ≥ 21.3 | ≥ 10.7 |
| app rows (5.2 M nodes) | 16 B (8 node + 8 derived) = 83 MB | 16 B node + 8 B derived = 119 MB | 119 | 80 | 80 |
| EID (5.8 M ids) | `u32` handles | 8 B: 46.5 MB | | | 23.3 (with `eid`) |
