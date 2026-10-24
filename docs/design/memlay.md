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
