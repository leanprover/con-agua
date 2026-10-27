# Lane mgen: the model generator's coverage

Rank 2 of `docs/design/lrecords.md` §2: close the gaps of `l_model` (`ConAgua/L/ModelGen.lean`), so
that hand-written word models and specs can be replaced by generated ones. Same rules as every
lane: no change to L program text, `checker.s`, `pins.bin`, `main.c`; no new axioms; no heartbeats
or timeouts raised.

## 1. Inventory (master 386bf921)

`_tmp/mgen/inventory.py` (outside the repository) repeats the classification of
`_tmp/lrecords/measure.py`: a function of `checkerProg` is *generated* if an `l_model` names it,
*hand-specified* if a theorem with a triple names it, *plain* if it is not a template instance. It
then reads each hand-specified function's `lfn` text, with spliced named blocks expanded, and looks
for the constructs `l_model` did not translate.

| plain functions | `l_model` | hand-specified | of these: `lfn` found | neither |
|---:|---:|---:|---:|---:|
| 1 526 | 537 | 930 | 882 | 59 |

(lrecords counted 533 / 993 a day earlier; the difference is the hand-spec test, which here
excludes functions an `l_model` also names.)

### 1.1 Hand-specified functions with constructs `l_model` lacked

57 functions, not 9: the lrecords count missed the pool slices (`A⦃x⦄`, `⦃x⦄.tier/.idx/.base`,
lane tieracc's 40-bit slice handles). By construct:

| construct | L semantics | functions |
|---|---|---|
| nested loops | a `while` in a `while` body | `nat_divmod`, `nat_mul` (also pool slices), `classes_nfs`, `basis_pin_hit` |
| `copy!` | `Stmt.copy64`/`copy8w` (`Mem.copy64`, `Mem.copy8w`) | `check_b`, `str_put_esc`, `rom_put` |
| `scan!` | `Stmt.scan8` (`scanN`) | `str_put_esc`, `rom_put`, `str_close`, `has_escape`, `key_end`, `skip_digits`, `skip_ws`, `utf8_valid` |
| `le64!` | `Expr.ld8x8` (`le64`) | `rom_u64` |
| pool slices only | `Expr.ld64t` of tier `x >> 40` at `x & (2^40-1)`, and the shifts | 42 (below) |

The pool-slice-only functions: `alpd_ls`, `pool_copy`, `sls_go`, `spn_ls`, `spn_pool`,
`lv_equivs`, `lp_lookup`, `nat_add`, `nat_limb`, `nat_trim`, `nat_pow_lit`, `nat_pred_lit`,
`nat_land`, `nat_lor`, `nat_xor`, `nat_cmp`, `div_add`, `div_shl1`, `div_sub`, `nat_pow`,
`nat_shl`, `nat_shr`, `nat_sub`, `pls_arm`, `pool_copy0`, `promote_l_pool`, `rom_lit`,
`stk_pool`, `str_ls1`, `str_utf8_char`, `iw_pool`, `name_rec`, `name_rec_i`, `pool_room`,
`nat_succ_lit`, `ls_put`, `node_lit`, `node_lit_str`, `name_rec_pre`, `apply_str`, `nat_dec`,
`nat_mad`, `utf8_put` (most in `Arena/Nat*`, `Promote`, `StubNames`, `Front/`).

Constructs the generator also lacked but no hand-specified function uses: byte stores
`A.u8[i] := e`, `R⟨t, i⟩.f := e`, global updates `g += e`. A memory-only function (no `return`)
was listed as unsupported but works (test `tMem`).

A generator bug found on the way: a loop followed by `abort` was always *fused* (its model returns
the function's result), and its spec claimed `r ≠ Sig.normal`, which only holds for a loop that
never exits normally (`while 0 == 0`). Any other such loop made the generated spec fail. Sequential
loops in one function got the same name (`loop1` twice: the number was taken before the code after
the loop, which holds the second loop, was translated).

### 1.2 Hand-written error models (`Except`, lane verdicts-b)

29 definitions in 11 files, 592 lines, for 16 functions. Why each is by hand, from the module
docs:

| function | file | lines | reason |
|---|---|---:|---|
| `classes_nfs` | `Verdict/IndBNfs.lean` | 45 | nested loops (generator) |
| `target_k53_args` | `Verdict/IndBTka.lean` | 61 | the generated step proof's `grind` fails (proof) |
| `infer_proj_at` | `Verdict/InferLeavesE.lean` | 40 | the generated step proof's `finish` fails (proof) |
| `infer_proj` | `Verdict/InferLeavesE.lean` | 80 | `l_model … errors` times out (proof) |
| `nest_ctors`, `nest_fields` | `Verdict/PosE3Cm.lean`, `PosE3Fm.lean` | 55, 80 | the generated model is used (pasted from `trace`), the spec by hand: the recursive call is through `callE_spec`, so the spec is the step without the induction |
| `iota_rec_vck`, `iota_rec_fire2` | `Verdict/WhnfModels4E.lean` | 51 | the step proof fails on the index words' arithmetic (proof) |
| `iota_certs_full` (5 helpers) | `Verdict/WhnfModels5E.lean` | 71 | hand ok models (`WhnfIotaRefine5`) copied with `callE`; a failing store's bound as `abort 0` |
| `iota_index_ok`, `iota_rec_cmp` | `Verdict/WhnfIdxE.lean` | 36 | hand ok models (`ioW`, `irCmpW`) copied with `callE` |
| `m2c_and2` | `Verdict/WhnfM2CE.lean` | 21 | the ok model's pushes as `and2Push` (a fold the generator cannot express) |
| `prop_irrel` | `Verdict/WhnfStuckE.lean` | 19 | hand ok model `piK1` copied |
| `struct_unit_head` | `Verdict/WhnfUnitE.lean` | 33 | the store of the spine's top checked in bounds (the generated `suhE` drops it) |

So one is a missing construct (nested loops, now generated); the others are proof failures or
copies of hand ok models, which go away only with the ok model (§3).
