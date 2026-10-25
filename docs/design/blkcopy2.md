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

### Results (prototype `best`: every conversion above except `stk_pool`, `str_close`)

`bench.py --set full --reps 3`, interleaved, master `7d5b6afc` against `best` (load ~20; the
`full` set includes `init435`). Instructions exact, wall noisy:

| fixture | master | best | ratio |
|---|---:|---:|---:|
| `irrel_commit` | 77 M | 76 M | 0.986 |
| `delta_chain` | 91 M | 90 M | 0.988 |
| `pinstall_ok` | 186 M | 184 M | 0.993 |
| `long_line_5mib` | 625 M | 466 M | 0.746 (wall 0.041 → 0.039 s) |
| `complete_c03d` | 4 452 M | 4 393 M | 0.987 |
| `complete_c04a` | 27 524 M | 27 245 M | 0.990 |
| `complete_c05b` | 20 697 M | 20 631 M | 0.997 |
| `init-prelude` | 2 033 M | 2 026 M | 0.997 |
| `init435` | 359.157 G | 358.824 G | 0.9991 (wall 24.06 → 23.98 s) |
| kernel ladders, `app-lam`, `eager_open_nat_control` | | | 1.000 |
| **geomean (18)** | | | **0.977** instructions, 0.980 cycles, 1.008 wall |

Verdicts: `bench.py --set all --reps 0`, 675 fixtures, 0 disagreements.

Per conversion (asmprof deltas, share of master's total):

| conversion | gain | proof cost |
|---|---|---|
| `str_put_esc` | `long_line_5mib` −20.2 %, `pinstall_ok` −0.08 % | small: bridge `escLoopW_skip`, a block `escRun` with its own spec (done, §3) |
| `lit_hash`/`limbs_eq` (tier once) | `long_line_5mib` −5.1 %, small fixtures −0.3 … −0.5 %, Init −0.05 % | moderate: `limbsEq_spec` needs `pcap < 2^64` (in-bounds tier reads lie below `2^40`), callers supply it |
| `rom_put` | small fixtures −0.5 … −1.15 %, nothing on big runs | small (bridge `rputW` = `copy8w`, ASCII loop = scan) |
| `iw_copy` | `complete_c03d` −1.3 %, `complete_c04a` −1.0 %, Init 0 | large: `copyW` is fuel-indexed, 16 files depend on it |
| `er_copy`, `pool_copy0`, `pool_copy`, `spn_pool`, `iw_pool`, `ek_copy`, `ik_copy`, `lh_er_copy`, `er_from_iw_go`, `block_caps_at_er_copy_go` | each < 0.03 % everywhere (Init: `ek_copy` −0.02, `spn_pool` −0.02) | small each, not worth it |
| `stk_pool` | a loss (+0.2 % on small fixtures: 1–2 levels per call) | — |

## 3. `str_put_esc` (proved)

The loop body starts with a named block `escRun`: `jn := scan!(IN.u8, j, ve, bslashC)`, then
`copy!(POOL.u64⟨pt⟩, pb + k, IN.u8, j, jn - j)`, guarded by two word checks (`len < d`,
`len - d < n`) so that the old model's per-byte word bound follows without a hypothesis on the
array size (the block's own bound is on naturals). The model `escLoopW` and every spec statement
are unchanged; new lemmas `escLoopW_skip` (a backslash-free run is one `copy8w`, by induction),
`escLoopW_run`, `escLoopW_hit` (after a scan that stops early the loop is at a backslash);
`escRun_spec` by plain `vcgen` + `simp_all`; `escLoop_spec`'s `finish` unchanged otherwise. The
file elaborates in 7 s. `long_line_5mib`: 625 M → 499 M instructions (−20.2 %), others unchanged.

## 4. Decisions (coordinator, after the prototype numbers)

(a) `str_put_esc`: land (landed as `b24fafff`). (b) the readers: go ahead, as a library accessor
with no side condition for callers. (c) `rom_put`: go ahead. (d) `iw_copy`: **parked** (it saves
1.3 % on `complete_c03d` and 1.0 % on `complete_c04a`, nothing on Init; `copyW` is indexed by fuel
and 16 files depend on it, so a fuel-free `copyW` comes first). (e) the small copies and
`stk_pool`: skipped.

## 5. The readers: a slice resolved once (`Arena/PoolRes.lean`)

The library accessor is `⟪sliceRes o l t x⟫` (a statement template over variable numbers):
`t := ⦃o⦄.tier; x := ⦃o⦄.idx`, then `abort` unless `x + l ≤ 2^40`. After it, the reader loads
`POOL⟨t⟩[x + i]`. Lemmas: `sliceRes_spec` (the step: two `setLoc`s and the bound),
`prd_res`/`prd_res_get` (an in-bounds load `POOL⟨⦃o⦄.tier⟩[⦃o⦄.idx + i]` with `x + i < 2^40` is the
tagged read `prd m (o + i)`; `grind` pattern on the load), and `tpool_res` (the same for
`tpool`, for models indexed by `Nat` positions such as `hashN`).

The coordinator asked for the `pcap < 2^64` side condition to come from the library's abstract
predicate. The accessor goes one step further and needs none: the bound check `x + l ≤ 2^40` makes
the equivalence of the resolved load and the tagged read hold for *any* memory. Without it, a tier
array longer than `2^40` would let `POOL⟨t⟩[x + i]` read past the tier boundary where `POOL⦃o + i⦄`
reads the next tier. So `limbsEq_spec`, `lsMatch_spec`, `nsMatch_spec`, `litMatch(Str)_spec` and
`litEq_spec` keep their statements and their callers are untouched. `litHash_spec` keeps its two
hypotheses (now unused, renamed `_hs`, `_hb`) so that its callers are unchanged too. The check
never fires: `cap_check` keeps both tiers below `2^40` words, and a slice in use lies in one tier
(`SliceOK`). So it is a capacity check, not a deviation. Cost: 4 instructions per slice.

`limbs_eq`: `⟪sliceRes 0 2 4 5⟫; ⟪sliceRes 1 2 6 7⟫; ⟪eqLoop⟫` (the loop precondition `EqRes`),
`lit_hash`: `⟪sliceRes 0 1 4 5⟫; ⟪hashLoop⟫` (`HashRes`, `hashN_tstep`). Both loop proofs keep their
`sym … finish` form. The module was first called `PoolSlice`, but that name was taken (a re-export
of `LitRefine`), hence `PoolRes`.

## 6. `rom_put` (both versions, ROM bytes and pin data)

`e := i + l; j := scan!(rom.c8, i, e, hiC); if j != e { abort }` replaces the ASCII loop, and
`copy!(POOL.u64⟨pt⟩, pb, rom.c8, i, l)` replaces the copy loop. `romPutPB` is the same text over
`PB.u8`, and `romPutPB_subPB` is still `rfl`. Bridges `asciiW_scan` and `rputW_copy` (by
induction) keep the models `asciiW`/`rputW` and `romPut_specW`'s statement. The spec proof is a
plain `vcgen`, then the `simp only` set from PLAN.md, then `grind` with the two bridges
instantiated. The old loop specs are deleted.

## 7. Final numbers (proved versions, branch against master `9fb94bff`, asmprof, exact)

| fixture | master | branch | ratio |
|---|---:|---:|---:|
| `long_line_5mib` | 625 M | 466 M | 0.746 (`str_put_esc` −20.2, `lit_hash` −5.1, `rom_put` −0.1) |
| `irrel_commit` | 77 M | 76 M | 0.986 (`rom_put` −1.15, `limbs_eq` −0.11, `lit_hash` −0.09) |
| `delta_chain` | 91 M | 90 M | 0.989 |
| `pinstall_ok` | 185 M | 184 M | 0.994 |
| `init435` | 359.157 G | 359.037 G | 0.9997 |
| kernel fixtures | | | 0.9998 … 1.0001 (`eager_open_nat_control` +0.01 %: `limbs_eq` on short slices) |

The proved readers save less on small fixtures than the prototype did (`limbs_eq` −0.11 % against
−0.31 % on `irrel_commit`): two bound checks and four more locals per call, and most compared
slices are a few limbs long.
