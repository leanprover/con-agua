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

* **Slot count** of a tier: `SN0 << G` with `SN0 = 16` and `G` a **global** per table
  (`SLOT_G` … `LSSLOT_G`, globals 100–116, `SlotGrow.lean`; zero at the start, so no
  initialisation). `X_find` reads it instead of `len(XSLOT) >> 1`; nothing else changes in the
  probe.
* **Growth**: `X_push` drops its 3/4-load abort; after writing the record, the slot and the count
  it calls `X_grow()` when the tier's count passes half the slot count (`(c + 1) * 2 > n`).
  The two tiers share the slot array (interleaved), so they share `n`; each tier is at most half
  full.
* **`X_grow()`** (`slotGrowG S`, one generic L function, `GrowSch` = slot array, record array,
  record width, count index, global, hash rule): `n' = 2n` (abort if `2 n' > len(XSLOT)`),
  `G += 1`, zero the slot words `[0, 2 n')`, then for both tiers and every node `i < CTL[ca + t]`:
  the node's hash from its record (FNV-1a over its `w` words, or the stored hash word for `lit`,
  `ls`, `nstr`), its home slot, linear probing to the first zero slot, write `B t + i + 1`. The
  records are dense and are the source: the old slots are never read, so the rehash is in place
  (no second region, no extra memory) and needs no tombstones or old-slot walk.
* `zero` and `anonymous` hold at most one node per tier (one slot touched): unchanged.
* Twin: closer than before (con-ron grows at 3/4 load from 32 slots; L at 1/2 from 16 per tier).
  The fixed tables were covered by the capacity rule, so `docs/deviations.md` has no row for them.
* The frontend tables `esp`/`lsp`/`nsp` (arrays 72–74) are `MemoLib` instances (`memoPutG`): they
  grow with lane memoflush's MemoLib change, not here.

## Prototype measurement

Tooling: `scripts/bench.py` (lane compopt's, branch `compopt`), the program file of master
(`e2e.write_checker`) with the 53 changed functions spliced in from the built store modules
(`_tmp/slotgrow/`), assembled with master's compiler. Variants: `master`, `grow`; `masterF`/`growF`
add lane compopt's memo flush (`compopt_progedit.py flush`) with memo arrays at 2^16 words
(`CA_SMALL`, the compopt harness) to stand in for lane memoflush.
