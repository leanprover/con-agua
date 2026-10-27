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

## 2. Generator changes (landed, #59, master e2f3ea22)

`ConAgua/L/ModelGen.lean`, tests in `ConAgua/L/ModelGenTest.lean` (one small function per
feature, each with its `l_model`; the module takes about 2 s):

* **Pool slices**: `A⦃x⦄` is `rdW (m.arr64 (tierA A (x >>> 40))) (x &&& 1099511627775)`;
  `⦃x⦄.tier`, `.idx`, `.base` the same words (each through the `fold` rules).
* **Block operations**: `le64!(A.u8, i)` is `le64 (m.src8 (.arr A)) i.toNat`;
  `x := scan!(A.u8, i, e, C)` is `UInt64.ofNat (scanN (m.src8 (.arr A)) C i.toNat e.toNat)`;
  `copy!(…)` is `Mem.copy64`/`Mem.copy8w` (tiered operands through `tierA`). The byte source is
  kept as `Mem.src8 m s`, the shape `step` produces, so no unfolding is needed. The step proofs get
  `L.ld8x8` / `L.warr` / `L.st8` in `vcgen` only when the code has them (no change for the
  existing 172 `l_model` modules).
* **Byte stores** `A.u8[i] := e`: `Mem.set8`.
* **Nested loops**: a loop in a loop body is a loop model of its own (`fW.loopᵢ`, numbered in
  source order), applied by the enclosing loop's body at `n + 1` as at the top level; the code
  after it in the enclosing body is a continuation whose result is the enclosing loop's; a
  `return` inside passes `Sig.ret` on (or is the function's result in a fused loop). The enclosing
  loop's spec gets the inner loop's spec in `vcgen`. A `while` written in the `lfn` inside another
  becomes the named block `fW.loopᵢ.stmt` inside the outer one's; named blocks may splice named
  blocks. Termination: the inner loop is called at the same fuel as the outer one and is lower in
  the depth order (the second component of `(fuel, depth)`).
* **Fixes**: loops are numbered by a counter (two loops in one function no longer both get
  `loop1`); a loop followed by `abort` is fused only for `while k == k` (the other case made the
  generated spec unprovable); the named blocks spliced in a loop body count for the loop's
  analysis (the locals they assign, their `return`s; before, the loop's spec claimed a frame for a
  local the block assigns).

Not supported still: `FunDecl`s with parameters (the 311 template instances, `memoFindG S`; they
share generic hand specs), a loop calling a member of its own group, global updates `g += e`,
stores `R⟨t, i⟩.f := e` (no hand-specified function uses the last two).

The gate build after the change (every `l_model` module rebuilt) took 365–400 s and passed
unchanged: no existing model changed its names or shape.

## 3. Pilot conversions

Three functions in files without array or tier reasoning, outside the absarrays-switch's set:

| function | file(s) | what changed | lines | elaboration |
|---|---|---|---:|---|
| `basis_pin_hit` (nested loops) | `Arena/IndRealBph.lean`, `IndRealBph2.lean` | 2 named blocks, 3 hand models, 3 continuations, 9 arm lemmas, 5 patterns, 3 specs → one `l_model` (`bphW`, `bphW.loop1`, `bphW.loop2`); the refinement (`bphW_loop2_iff`, `bphW_loop1_ok`) rewritten against the generated arms, same structure | −212 +53 = **−159** | 1.69 s → 1.77 s in declarations over 20 ms (both modules; noise level) |
| `class_read_minor`, `class_read_minor_tail` | `Arena/RecClassSpec/CrW.lean` | 2 models, 8 continuations, 15 arm lemmas, 14 patterns, 2 specs → two `l_model`s; the refinements `tailW_sim`, `minorW_sim` only renamed (`mK2_ok` → `minorW.k_open_pis_at_fvars_f.arm2`, `(K := mK1 n nP mo ml d cR dom)` → `(K := minorW.k_pi_binders cR n nP mo ml d dom)`) | −180 +57 = **−123** | the two specs 4.07 s → 1.28 s (`trace.profiler`, the generated step proofs; the `l_model` commands under 0.11 s) |

Per function about 60–160 lines, as lrecords estimated (50–70 for a typical function, more for
loops). Time: where the hand spec used `sym … finish`, the generated `simp` recipe with loads as
`rdW` (`extra [ld64_rd_spec] simp []`) is 3× faster; elsewhere neutral. The statements callers use
kept their names and shapes (`bph_specW` now at fuel `n` with `bphW.arm1` unfolding it; the CrW
specs unchanged), so no file outside the converted ones changed.

What a conversion takes: the generator's continuation names (`fW.k_<callee>`) and argument
order (the models' Lean parameters first, then the fuel, then the captured locals in declaration
order) replace the hand names; arm lemmas become `fW.k_….armᵢ` with the hypothesis `hc1`; zero
fuel is `fW.eq_1`. When the hand model had the generator's shape (CrW) this is a rename (15 min);
when it was shaped differently (bph: the inner loop inlined into the outer model, a continuation
taking "the rest" as an argument) the refinement's case split needs re-threading (1 h).

## 4. Roll-out (after absarrays-switch lands)

`_tmp/mgen/rollout.json` (from `inventory.py`): 241 of the 412 files with hand specs have no array
or tier vocabulary (`tier1`, `tierOff`, `words.size`, `HasW`, `SameShape`, `Frame`, `tierA`) and
are outside the switch's current branches; their hand specs name 1 122 functions (with repeats
across files). Largest first by hand `…W` definitions: `Arena/PromoteCI.lean` (36),
`Front/IndApplySpec.lean` (30), `Rom/CIReadRefW.lean` (21), `Arena/WhnfM2CRefine.lean` (14),
`Front/IndFieldsSpec.lean` (13), `Arena/Abs1.lean` (13), `Arena/InstLPWalk.lean`,
`Arena/PropReadW.lean`, `Front/IndApplySpec2.lean` (11 each), `Arena/DefEqLeaves.lean` (10). The
list is recomputed once the switch has landed (its final file set is larger than its branches
today). Order: files where the hand model already has the generator's shape (continuations named
after callees, arm lemmas used by `rw`) first, since there the refinement only needs renames.

## 5. What stays hand-written, and why

* the 311 template instances (`memoFindG S`, …): generic specs over the schema, one per template;
  the generator would need `FunDecl`s with parameters;
* hand ok models whose refinements need bounds or shapes the generator does not produce:
  `classes_nfs` (`cnsW` checks every store in bounds, the refinement uses it), `struct_unit_head`'s
  error model (the same), `m2c_and2` (the pushes as `and2Push`), models over `prd` and other
  named readers until a `fold` for loads exists;
* the error models of §1.2 that copy hand ok models: they go with their ok model;
* the error models whose generated proof fails or times out (`target_k53_args`, `infer_proj_at`,
  `infer_proj`, `iota_rec_vck`, `iota_rec_fire2`): proof work, not coverage;
* the scanners (`skip_ws`, `key_end`, …): their specs state pure models (`skipWsN`) the twin
  bridge uses, not word models, so a generated word model would add a layer, not remove one.
