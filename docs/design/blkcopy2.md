# Lane `blkcopy2`: block primitives on the tierpool path (journal)

Branch `blkcopy2`, worktree `_tmp/wt/blkcopy2`, base master `7d5b6afc` (tierpool landed).
Scratch: `_tmp/blkcopy2/` (prototype `Proto.lean`, profiles, bench logs).

## 1. Where tierpool's cost is (asmprof, exact instruction counts)

Pre-tierpool master (`7d5b6afc^1`) against master (`7d5b6afc`), per-function delta as a share of
the old total (`_tmp/blkcopy2/fndiff.py`):

| fixture | old → new | biggest deltas |
|---|---:|---|
| `long_line_5mib` | 560 → 625 M (+11.5 %) | `lit_hash` +7.56, `str_put_esc` +3.74, `limbs_eq` +0.14 |
| `irrel_commit` | 76 → 77 M (+2.1 %) | `limbs_eq` +1.07, `lit_hash` +0.56, `rom_put` +0.33, `stk_pool` +0.12 |
| `delta_chain` | 89 → 91 M (+1.9 %) | `limbs_eq` +0.91, `lit_hash` +0.49, `rom_put` +0.28 |
| `pinstall_ok` | 183 → 185 M (+1.2 %) | `limbs_eq` +0.44, `lit_hash` +0.29, `scratch_reset` +0.17, `rom_put` +0.14 |
| `init435` | 358.44 → 359.16 G (+0.20 %) | `limbs_eq` +0.07, `lit_hash` +0.04 |
| kernel fixtures | +0.00 … +0.18 % | `limbs_eq`, `lit_hash` |

So most of tierpool's cost is not in the writers but in the two **readers** `lit_hash` and
`limbs_eq` (`Arena/Store.lean`): every `POOL⦃o + i⦄` decodes the tag again (shift, mask, tier
`& 1`, descriptor length and base: ~20 instructions per limb; `limbs_eq` 42 per iteration). Of
the writers only `str_put_esc` (long strings) and `rom_put` (every run's ROM names) matter.

Shares on master (`fnshare.py`): `rom_put` 3.6 % of `irrel_commit` (239 instructions per call,
names of 4.3 bytes), `iw_copy` 1.5 % of `complete_c03d`, 1.2 % of `complete_c04a`;
`str_put_esc` 31 % of `long_line_5mib`. `pool_copy0`, `pool_copy`, `spn_pool`, `iw_pool`,
`ek_copy`, `ik_copy`, … are each below 0.1 % everywhere (Init: `spn_pool` 0.06, `ek_copy` 0.08).
`str_close`, `has_escape`, `utf8_valid` already run at 7 instructions per byte (blkcopy).

## 2. Prototype (unproved)

`_tmp/blkcopy2/Proto.lean` (`scripts/lake env lean --run …/Proto.lean OUT.s [FNS|all]`):
replaces functions of `checkerProg` by versions with `copy!`/`scan!` and compiles with the real
compiler (with no function selected the output is byte-identical to `asm/checker.s`).

* copies: `pool_copy0`, `pool_copy` (tiered source, tier decoded once), `iw_copy`, `er_copy`,
  `ek_copy`, `ik_copy`, `lh_er_copy`, `er_from_iw_go`, `block_caps_at_er_copy_go`, `spn_pool`,
  `iw_pool` (tiered destination);
* `rom_put`: `scan!(PB.u8, i, e, hiC)` + `copy!(POOL.u64⟨pt⟩, pb, PB.u8, i, l)`;
* `str_put_esc`: per run, `scan!(IN.u8, j, ve, bslashC)` then one `copy!` of the run;
* readers `lit_hash`, `limbs_eq`: the tier and index decoded once per slice, then
  `POOL⟨t⟩[x + i]` (plain L, no primitive);
* dropped: `stk_pool` (k is 1–2 levels: 56 → 81 instructions per call, a loss), `str_close`
  (already a scan).
