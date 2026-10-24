# Lane `tierpool`: the limb pool as a tiered array (journal)

Branches: `tierpool` (L code, worktree `_tmp/wt/tierpool`), `tierpool-acc` (the proof-side
accessor refactor on master's layout, worktree `_tmp/wt/tierpool-acc`; lands first, in batches).

## Inventory (master `6b186593`)

L code: 76 functions and named blocks touch the pool: 47 reads, 61 stores, 46 length checks, 56
reads/writes of the top `CTL[0]`.

| family | functions / blocks |
|---|---|
| bignum (`Nat*.lean`) | `nat_trim`, `nat_limb`, add/sub/and/or/xor/mul/shl/shr loops and wrappers, `nat_cmp`, `nat_pow`, `nat_divmod` (`div_shl1`, `div_sub`, `div_add`, limb/zero loops), `nat_pred_lit`, `nat_pow_lit`, `nat_succ_lit`, `raw_nat_lit` (top as an empty slice) |
| literal / level-list / name store keys | `lit_hash`/`limbs_eq` loops (`Store.lean`), `hp_loop_ls` (`LpCol`), `alpd_ls`, `lv_equivs`, `lp_lookup`, `sls_go`, `spn_pool`, `spn_ls`, `promote_l_pool`, `pls_arm`, `pool_copy` |
| strings / names | `str_put`, `str_put_esc`, `utf8_put`, `esc_loop`, `str_ls1`, `str_utf8_char`, `pool_room`, `name_rec`, `name_rec_i` (+ digit loop), `iw_pool`, `proj_table_name`, `is_proj_fn_shape`, `name_rec_pre` |
| frontend | `nat_dec` (`nat_mad`, `dec_loop`), `ls_put`, `node_lit`, `node_lit_str`, `apply_str` |
| ROM / pins | `rom_put`, `rom_put_pb`, `stk_pool`, `rom_lit` |

**Method note (missed once):** besides `POOL.u64[…]`/`len(POOL…)` in L text, grep `checkerProg`
(`Checker/Prog.lean` and the sub-programs) for every *template* instantiated with the pool (or
any tiered array) as an argument: `lv_lookup = lvLookupG EREC POOL` reads its value array with a
plain `VA.u64[vo]`; it slipped through the text inventory and broke the scratch-flag version on 7
fixtures (natop_*, k_major_raw, init-prelude, Init). It now reads `VA⦃vo⦄`; no other entry of
`checkerProg` passes the pool to a template.

Proof side: 1474 mentions of `POOL` in 119 files (`pv (m.arr64 POOL) o l`, `Norm`, `sliceL`,
`hashN`, frames `m'.arr64 POOL = m.arr64 POOL`, `Grows`, `PoolOK`, `SliceOK`).

Promotion paths that hand a scratch slice to a persistent record (master): `pi_lit`,
`pi_lit_str` (via `pe_lit`) and `pi_nstr` (via `pn_arm`) pass `(o, l)` straight on; level lists
are already copied (`pls_arm` → `promote_l_pool`).

## Decisions

1. **Tier = phase** (first approved design): implemented in L and benchmarked (below), then
   superseded.
2. **Tier = the arena's scratch flag, copy-on-promote** (coordinator, 2026-10-24): fixes D10
   across declarations (the scratch tier's limbs are dropped with it) and serves entry 2 (which is
   scratch-only). In L:
   * slices are named by tier-tagged addresses (bit 40 = tier; `⦃x⦄.tier/.idx/.base`, `POOL⦃x⦄`,
     `L/Notation.lean`); every store takes the tier and base of its writer's top, decoded once;
   * `CTL[0]` is the *current* tier's top; `scratch_reset` saves the tier-0 top in the global
     `PTOP0` when it leaves tier 0, starts tier 1 at `2^40`, and restores tier 0's top when it drops
     the scratch tier; so no pool writer changes;
   * `pool_alloc0`/`pool_copy0` allocate/copy into tier 0 (at `CTL[0]` or `PTOP0`); `pi_lit`,
     `pi_lit_str`, `pi_nstr` copy a tier-1 slice, `pls_arm` allocates its promoted list there;
   * `cap_check` bounds the pool by `2^40` words.
3. **Proof side first** (coordinator): the pool goes behind library accessors and abstract
   predicates on today's layout, so that the switch stays inside `Arena/Pool.lean`:
   * `prd m x` (the word an L load at address `x` reads), `vpool m` (an array with a word for every
     word address: `Array.ofFn` over a *sealed* `2^64` — `vsz`, an `opaque` — because a kernel check
     that reduces `(vpool m).size` would otherwise build the array; a first version without the seal
     was killed at 16 GB), `pcap m` (capacity);
   * access lemmas `vpool_ld` (an in-bounds L load reads `vpool`), `vpool_set64`, `vpool_set64_ne`,
     `vpool_agree` (below `pcap`, `vpool` is the array), `pcap_set64`;
   * `PoolOK`, `Grows` stated over `pcap`/`vpool`; users read slices as `pv (vpool m) o l`,
     `Norm (vpool m) …`, and loop invariants carry a ghost capacity `C` beside the ghost pool
     (`Pg.size = 2^64` replaces the old `Pg.size < 2^6x`).

## Coordination with lane `tierswitch` (records → tiered arrays)

Shared files: `Checker/Entry.lean`, `Checker/CapCheck.lean`, `Checker/RomProgInit.lean`, the L
text of `Store.lean`/`LsStore.lean`/`NStrStore.lean` (the matchers' `limbs_eq(REC…, o, l)` lines:
tierswitch changes the record reads, tierpool nothing there since `limbs_eq` reads through tags),
and the record relations in `LitRefine`/`LsRefine`/`NStrRefine` (tierpool adds one conjunct: a
tier-0 node's slice is a tier-0 address; `NatRec`/`StrRec`/`NsRec`/the level-list record).

Split (proposed by tierpool, 2026-10-24):
* **tierswitch owns** `wordArrays`, `slotArrs` and the per-array loop of `cap_check`
  (`capCheckBody`'s `foldr`, `CapsOK`'s first conjunct). Its `wordArrays = 318` covers the pool's
  tier-1 array `256`; until it lands, tierpool uses `257`.
* **tierpool owns** the tail of `cap_check` (`capTail`: the pool bounds `len(POOL) < 2^40`,
  `len(POOL1) < 2^40`), the matching conjuncts at the end of `CapsOK`/`CapsW`, `CapsOK.pool`, and
  the pool part of `arenaR_loadMem` (`RomProgInit.lean`).
* Whoever lands second merges (union of both; `wordArrays` = the larger).

## Benchmarks

`bench.py --set full --reps 3`, interleaved, baseline the branch base `6b186593` (machine load
~84, so cycles/wall are noisy; instructions are the measure).

| version | instructions | cycles | wall |
|---|---:|---:|---:|
| tier = phase, per-store `- base` | 1.015 | 1.012 | 1.010 |
| tier = phase, per-loop base | 1.015 | 0.989 | 1.002 |
| tier = scratch flag, per-loop base (+ `lv_lookup` fix) | 1.014 | 1.003 | 0.996 |

Scratch-flag version: `long_line_5mib` +8.5 %, small fixtures +1.3–2.5 %, big kernel runs
+0.01–0.03 %, Init +0.26 %; Init's peak RSS 1507 → 1388 MB (−8 %): the scratch tier's limbs are
dropped with it (D10 across declarations).

Big kernel runs +0.01–0.03 % (app-lam, beta/let-ladder, c04a, c05b, c03d), Init v4.35 +0.26 %,
the 8 small fixtures +1.3–3 % (ROM/pin byte copies into the pool), `long_line_5mib` +9.5 % (string
copy loops: ~6 instructions more per byte). Peak RSS unchanged.

Remaining cost: ~4 instructions per pool store for the tier descriptor lookup (`and`, `shl`,
`add r15`, the descriptor load). Candidate for a later compiler optimisation (a loop-invariant
tier local → descriptor address hoisted out of the loop), not this lane's job; lane `blkcopy`'s
copy primitive would also cover the byte loops.

## Log

* 2026-10-24: inventory; prototype (Prog→Prog transform, 0/675 verdict disagreements); L code for
  tier = phase; benchmark; switch to tier = scratch flag decided; L code for it; per-loop store
  base; library `vpool`/`prd`/`pcap` on master's layout; Nat family converted.
* 2026-10-24 (evening): proof side converted (batch 1 of `tierpool-acc`): 83 Lean files
  (+3101/−1598 lines; most of it the `NAMEv`/`NAMEc` companions and the interface bridges), every
  value-function position over `vpool`, every capacity over `pcap`; refinement interfaces bridged
  with `sliceL_vpool`/`pv_vpool`/`Norm_vpool`/`Agree.vpool`. No L change (asm unchanged), zero new
  `sorry`, the axiom guards unchanged. Merging master (tieracc's `tfld` fields) was a token-level
  3-way merge (`_tmp/tierpool/tokmerge.py`); it once put an edit into master's new twin
  `NatRec_raw` instead of `NatRec`, so check its output by building.
