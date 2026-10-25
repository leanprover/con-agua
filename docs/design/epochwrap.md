# Lane epochwrap: the slot base's wrap (D39) and a capacity audit

Goal (user, 2026-10-25): inputs of 10–100× Mathlib must work. Where L aborts on a capacity limit
and con-ron keeps going, follow con-ron.

## Task 1: D39, `scratch_reset`'s wrap

**Before.** The scratch tier of the 19 cons tables is emptied in O(1): a tier-1 slot holds
`B + i + 1` (node `i`) against the slot base `B = CTL[62]`, and reads free at or below `B`;
`scratch_reset` adds `2^32` to `B` (every old slot holds at most `B + 2^27`) and aborted at
`B ≥ 2^62`, i.e. after `2^30` resets (two per declaration: `scratch_enter`, `scratch_drop`).

**Twin.** `ron/hashmap2.rs` `clear`: a `u32` epoch; at `EPOCH_MAX` the slots are vacated by a walk
and the epoch restarts at 1. con-ron does this per table; L shares one base between the 19
tables, so it vacates all 19 scratch tables at once.

**Now.** `scratch_reset` is a head and a tail (`Scratch.lean`):

* `scrHead`: `b := CTL[62]; if b >= SCBLIM { scrVac; CTL[62] := 0 }` with `SCBLIM = 2^62`.
  `scrVac` vacates tier 1 of the 19 slot arrays (`scrSlots`), each with `vacB sa`: `t := 1;
  x := sa⟨t⟩[1] + 2; e := (sa⟨t⟩[0] + SN0) >> 2` and then the growth's own zero loop, now
  `kzeroLs sa` (`ConsLib.lean`; `kzeroL C := kzeroLs C.sa`), which zeroes `8 e = 2 n` words: the
  table's `n` slots. The words beyond the table (old smaller tables of an in-place growth) need no
  zeroing: the growth zeroes the upper half it takes over.
* `scrTail`: the old body (minus the abort): `B += 2^32`, flag, counts, tops.

Only the slot tables carry `B`: the memos (`memoClearG`) have their own stamps (`CTL[cs]`, abort
at `2^64 - 2` clears: unreachable). Nothing else reads `CTL[62]` (grep: `ConsLib.lean`'s find, push
and growth only).

**Model and proof.** `preMem m` (the memory the tail starts from: at the limit `vacL scrSlots m`
with `CTL[62] := 0`, else `m`); `scratch_reset(f)` leaves `resetMem (preMem m) f`.

* `kzeroLs_spec` (ConsLibSpec): `kzeroL_spec` generalised to any renaming (the wrap runs the loop
  with its variables shifted past `f`); `kzeroL_spec` is now an instance.
* `vacB_spec`, `vacS_spec` (by induction on the list), `scrHead_spec`, `scrTail_spec`,
  `scratchReset_spec` (Scratch).
* `storeR_resetG` (StoreLib) replaces `storeR_reset`: tier 1's slot array may change, provided its
  size, count word and offset word stay and every slot of its table reads free; with
  `slotW_free_raise` (the old argument: the base rose past every slot) and `slotW_free_zero` (the
  table's words are zero). Tier 0's records/hashes are carried by the caller (`hR0`, `hh0`), so a
  table no longer needs every other array unchanged (`RFrame`'s `OutEq`): the wrap writes the
  other 18 tables' slot arrays too. `ConsR.resetG`, `ConsR.free_raise`, `ConsR.free_zero`,
  `ConsR.lay1` (ConsLibRel) are its `ConsR` face.
* `consR_resetP` (ScratchRefine): one table across the wrap and the counts, by the table's
  locality (`RLocal`, the `*Local` lemmas of `ArenaRel`) instead of `RFrame`. `vacL_rd`: the wrap
  zeroes exactly the table's words of tier 1 of each slot array. `preMem_frame`: the wrap writes
  `slot1Arrs` (the 19 tier-1 slot arrays) and `CTL[62]`.
* The bracket's frame grows from `[PT0]` to `scrArrs = PT0 :: slot1Arrs`: `enterMem_frame`,
  `resetMemP_frame`, `CheckR.of_bracket` (arrays below 64 or in 256‥319, `AvoidA.of_low`),
  `LoopR.of_lo`, `PendR.frameLo` (Checker), `TwinOK.frameLo` (TwinStep: any `A` of `PT0` and
  arrays from 256).

`StoreR`'s clause `CTL[62] < 2^62 + 2^32` holds as before: after the head `B < 2^62` (below the
limit, or `0`), and the tail adds `2^32`. `@[refines ConRon.Arena.EStore.dropScratch]` on
`scratchReset_dropScratch` now holds without the abort caveat.

**Tests.**
* `#guard` (ScratchRefine, end): from `B = 2^62 - 2^32`, `scratch_enter` raises `B` to `2^62`
  writing no slot, then `scratch_drop` wraps: `B = 2^32`, every scratch table zeroed (a grown one,
  16 slots at offset 2, keeps its count and offset words and the two words before its table).
</content>
</invoke>

## Task 2: capacity audit

**Method.** The Init435 export (346 MB, accepted, 34 s) run with a measuring copy of the harness
(`_tmp/epochwrap/main_usage.c`, not committed: after the run it prints every non-zero `CTL` word
and, by `mincore`, each word array's resident extent). Scale: Mathlib ≈ 10–20× Init in
declarations, so 100× Mathlib ≈ 1000–2000× Init; I extrapolate linearly with 2000×. Init at the
end: 230 422 scratch resets (`CTL[62] = 230422 · 2^32`); persistent nodes `app` 5 206 369,
`lam` 538 774, `forall` 301 043, `nstr` 172 696, `nnum` 123 711, `const` 56 965, `let` 11 346
(`CTL[ca]`); pool top 1 526 310 words; environment record top `CTL[129]` 1 838 633 words; 57 292
pending checks; `replace_fvars` bank generations `CTL[218]` 8 017 (never reset), its memo 19 838
live entries; `inst_list` memo stamp `CTL[50]` 52 150 678 clears. Largest arrays: `ASLOT` 130 MB
(app slots, 2^23), `AREC`/`ADER` 40 MB, `EID` 24 MB, `LASLOT` 18 MB, `EREC` 16 MB, pool 12 MB.

| limit (L) | where | Init use | at 2000× Init | con-ron | verdict |
|---|---|---|---|---|---|
| scratch resets `2^30` (D39) | `scratch_reset` | 230 422 | 4.6·10^8 (43%) | `u32` epoch, wraps | **fixed** (this lane): wraps as the twin |
| nodes per table and tier `2^27` (handle `tag·2^28 + tier·2^27 + i`) | `X_push` `c >= 134217728` | app 5.2·10^6 (3.9%) | app 1.0·10^10 (78× over); lam 1.1·10^9 (8× over), forall 6·10^8 (4.5× over) | same `IDX_CAP = 2^27` (`arena/handle.rs:77`, `Native`) | matches the twin; **but reached at ~26× Init (≈ 1.3–2.6× Mathlib) by both**: the binding limit of the project. Expensive (handle width: u32 → u64 handles in both twins, or more tag bits); for the coordinator/user |
| words per array `2^32` (ABI slot `2^35` bytes, `Compiler/Abi.lean`) | every array (OOB → abort) | pool 1.5·10^6, `EREC` 1.8·10^6, `ASLOT` 1.7·10^7 | pool 3.1·10^9 (71%), `EREC` 3.7·10^9 (86%), `ASLOT` 3.4·10^10 (but bounded by the node cap: 2^27 nodes need ≤ 2^30 words) | `Vec`, unbounded | not reached before the node cap; reached soon after it (EREC at ~2300× Init). Expensive: the region is `318 · 2^35` bytes = 10.9 TB of address space; a uniform `2^38`-byte slot is 87 TB (x86-64 user space 128 TB), so it needs per-array slot sizes (ABI, compiler proof, harness) |
| pool `2^40` words per tier (address tag bit 40, `cap_check`) | `Pool.lean` | 1.5·10^6 | 3.1·10^9 | unbounded | far (2^40); the `2^32` slot comes first |
| memo region `≤ 2^29` slots per stamp (`mgrowBlkG`) | MemoLib | per-declaration caches small; `RFM` 19 838 live | `RFM` 4·10^7 (7%) | grows | fine. Note: `rf_clear` is never called (the twin uses a fresh map per `replace_fvars`): memory, not capacity |
| bank generations `2^32` (`bankEnterG`), `CTL[218]` never reset | `rf_bank_enter` | 8 017 | 1.6·10^7 (0.4%) | fresh map per call | fine |
| memo stamps `2^64 - 2` (`memoClearG`) | MemoLib | 5.2·10^7 (`inst_list`) | 1.0·10^11 | – | fine |
| front id tables: dense `2 · len` = `2^33` ids, then the sparse memo (D9) | `IdTable.lean` | `EID` 3.1·10^6 words | 6.3·10^9 words: dense part full at ~1400× Init, sparse memo takes ≤ 4·10^8 more | unbounded | behind the node cap; would need the `2^32` slot raised too |
| declarations: `DECL` 8 words each (≈ 5·10^8), `prepare_prelude` `2^59`, `pend_push` `2^62` (PEND 3 words: 1.4·10^9) | Checker | 57 292 pending; `DECL` 0.5 MB | 1.1·10^8 pending (8%) | `Vec` | fine |
| D32 (`nPc + nF` wraps), D33 (`i ≥ 2^63`), D34 (key words `< 2^32`), `x + 1 == 0` counters, `>= 2^60` rule counts, `>= 2^32` block counts | Ind*, ConsLib, walks | per declaration, not per run | unchanged | overflow-checks / `u32` | fine: per-declaration sizes do not grow with the input |
| walk fuel `CWF = 4·10^9`, L call stack `2^30` bytes, spine/binder stacks (array length) | Abi, walks | per declaration | unchanged | same fuel, `STACK_BYTES = 2^30` | matches the twin; per declaration |

**Cheap fixes made:** D39 (Task 1). No other limit that 100× Mathlib reaches is cheap: the two
that are reached (the node cap and the `2^32`-word arrays) are listed above for the coordinator.
