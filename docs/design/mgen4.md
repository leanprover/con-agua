# Lane mgen4: generator gaps of `l_model`, and the conversions they open

Fourth lane on `l_model` (`ConAgua/L/ModelGen.lean`, tests in `L/ModelGenTest.lean`; the earlier
lanes: `docs/design/mgen.md`, `docs/design/mgen3.md`). mgen3 (§5 there) converted about 250
hand-written models and listed the generator gaps it worked around. This lane closes the gaps
that a small change covers, then converts what they open. Same constraints as every lane: no L
program change (`checker.s`, `pins.bin` identical), no final statement change, no new axiom, no
heartbeats raised. Every generator change is an option that is off by default, or applies only
where the generator raised an error before, so no existing `l_model` changes its output (the
gate build rebuilds every `l_model` module, all unchanged).

## 1. Generator changes (round 1)

### `share`: a join point over a duplicated memory term

A total memory callee (`G ∧ s'.mem = F`, `erec_put`) is inlined: the memory after it is the term
`F m …`, and the next statement reads that term wherever it reads the memory. `rule_copy`'s
eleven `erec_put(b + i, EREC⦃old + i⦄)` each mention the memory before them three times (the
callee's memory argument, the read `EREC⦃old + i⦄`, the guard `erec_put` checks), so the model
held `3 ^ 11` copies (mgen3 kept the hand model). With `share`, a statement that writes the
memory (a store, `setG`, `set8`/`set32`, `copy!`, a total memory callee) and mentions a memory
term that is not a variable more than once (`dupMem`: occurrences of the term's syntax in the
statement's new memory and guards) starts a join point `fW.jᵢ` over the memory: the code from
that statement on becomes a definition (the join point machinery of an `if` whose branches fall
through, `mkJoin`), applied to the memory term. Inside it the memory is the variable `m`, so the
statement mentions only that. `rule_copy`'s model is ten join points, linear in size.

Test `tSh` (four calls of a callee with a guard over the memory). A twelve-call version proved
in 80 s, a ten-call one in 6 s, eight calls in 1.5 s: on that toy the steps' `grind` (not
E-matching, not the model's size; few heartbeats) grows fast with the number of calls, so the
test uses four. On the real `rule_copy` (eleven calls, `EREC` pool slices) the whole `l_model`
takes about a second.

### A binder named `L`

The generated proof text writes the library's names root-qualified (`_root_.L.exec`, `rootL`), so
that a binder `L` does not capture them; that also rooted the binder's own fields (`L.rc` →
`_root_.L.rc`, unknown), and mgen3's helpers renamed such binders to `hL`. Now the command renames
a binder `L` to `L'`, and every `L` / `L.x` after it (`renameBinderL`): after the binder, `L.x`
can only mean the binder's field (a local comes first in name resolution). The spec's binder is
then named `L'`. Test `tPfL_spec`.

### Implicit binders as model parameters

An implicit binder (`{C : …}`) that a callee's model mentions became an unknown identifier in the
generated definitions (only explicit binders were collected as the models' parameters, `mps`).
Implicit and strict-implicit binders are collected too; the models take them explicitly. Test
`tPfL_spec` (its `C` is implicit).

### `fold` with memory readers

`fold [erRd]` failed ("unsupported term"): fold patterns were word arithmetic only, so generated
models read `rdW (m.arr64 (tierA EREC (x >>> 40))) (x &&& …)` and users bridged by `rfl` lemmas
(`erRd_foldN`, `prd_rdW`). A fold function whose body is a word read `rdW (m.arr64 A) i` (`i` a
pattern over its other parameters: `cnt m t = rdW (m.arr64 CTL) (2 + t)`) or a pool slice word
`rdW (m.arr64 (tierA A (x >>> 40))) (x &&& 1099511627775)` (`erRd`, `prd`) is a reader
(`Fold.reader`): `A.u64[i]` and `A⦃x⦄` become `f m …` where they match. Test `tRd`. A reader
stated as `rdW`'s body, `(m.arr64 A)[i.toNat]?.getD 0` (`prd`; helper mgen4-levels met it), is
read the same way (round 2).

### `mixed` callee posts

Posts that state some results as values beside the call's effect were rejected: `str_put_esc`
(`r.headD 0 = s₀.mem.top ∧ strPutEscW … = some (r.tail.headD 0, s'.mem)`: "unsupported post
conjunct"), `ls_put` (`r = [s₀.mem.top, lsPutL b v] ∧ lsPutW b s₀.mem v = some s'.mem`:
"ambiguous post"), `stk_pool` / `rom_put` (`G ∧ r = [s₀.mem.top] ∧ s'.mem = F`: ambiguous). Now
such a post is `CKind.mixed`: the stated results are the values (over the memory before the
call), and the effect (`F = some (r.ⱼ, s'.mem)` giving result `j`, `F = some s'.mem`, or the
total `s'.mem = F` with its guards) is handled as before. Only these shapes, which raised errors
before, are read so; a pure result beside `F = some (r.headD 0, s'.mem)` or a memory model stays
ignored as it was. Test `tMx`.

### `pfuel k` (round 2)

`pfuel` stated the spec at `exec p (n + 1)` with the model at `n`. Hand models stated at `n + 2`,
`n + 3` (`block_shape_fin`, `block_shape_tail`: their callees run at `n + 1`, `n + 2`) did not fit.
`pfuel k` states the spec at `exec p (n + k)`; the callee specs are given at the fuel the body
runs at (`g_spec p (n + k - 1)`), the model is still the body at `n`. Test `tPf2_spec` (`pfuel 2`
over `tPf`: its model is `tPfW` at `n + 1` by `rfl`).

### Not changed: literals and instances in generated `if`s

mgen3 met `rw [ite_eq_left h]` and `split` failing on generated `if`s where `simp only [h,
↓reduceIte]` works. A generated `if k = 0` is `@ite _ (@Eq Word k (@OfNat.ofNat Word 0 _))
(instDecidableEqUInt64 …)`, a hand-stated one over `UInt64` the same with `UInt64` for `Word`
(reducible); the instances are the same. No case in the current tree reproduced the failure
where the generated form could be changed without changing every model's output, so the
generator is unchanged here.

Tests: `L/ModelGenTest` 86.1 G (mgen3's last measurement) → 92.8 G, 21.9 user s, with the five
new tests (`tSh`, `tPfL_spec`, `tRd`, `tMx`). The gate build rebuilt every module importing
`ModelGen` and all of them elaborated unchanged.

## 2. Conversions

### Batch 1: `rule_copy` (`share`)

`rc_spec` is generated (`fns [hL.rc ↦ rcpW list] … share`): the hand model `rcpW` (`some ([0],
cpMem m b old)`) and its hand spec are gone. The generated `rcpW` checks `erec_put`'s bound at each
copy (`none` otherwise), so the two walks over `rules_to_erec_go` (`rteGoW_mem`, `rteGoW_afr`)
case on its result and take the memory from `rcpW_some` (`rcpW m b old = some (r, m') → m' =
cpMem m b old`, one `split` per join point); `cpMem` stays as the users' description of the copy.

| module | instructions | user s | RSS MB |
|---|---|---|---|
| `Arena/IndSumSpec/ConsBlockRecsTF` | 68.2 → 75.5 G | 10.6 → 11.4 | 1230 → 1290 |

### Batch 2: `block_shape_fin`, `block_shape_tail` (`pfuel 2`, `pfuel 3`)

mgen3 kept them: their models feed `bbW` (`block_shape_build`, `IndPartsProg5.lean`), which sat
below the lookups structure `IndPartsProg5` their specs need, and they are stated at `n + 2` /
`n + 3`. Now `bf_spec` and `bt_spec` are `l_model`s in `IndPartsProg5.lean` right after the
structure, with the hand recipe's callee specs (`pfuel 2`; `pfuel 3` with `fold [erRd]`), and
`bbH1`–`bbH4` and `bbW` moved there after them. Both generated models are the hand ones by `rfl`.
Gone: `bbK8`–`bbK13'`, `bfW`, `btK1`–`btK3`, `btW` and their arm lemmas (`Bsp.lean`), the hand
`bf_spec`, `bt_spec` (each at `maxHeartbeats 20000000`). The two walks in `BrsW.lean` (`bfW_sim`,
`btW_sim`) only renamed (`bbK8_some` → `bfW.k_block_shape_ctors_of.arm1`, `rw [bbK9]` →
`rw [bfW.k_param_levels]`, …).

| module | instructions | user s | RSS MB |
|---|---|---|---|
| `Arena/IndPartsSpec/Bsp` | 28.8 → 27.9 G | 4.5 → 4.2 | 1074 → 1066 |
| `Arena/IndPartsSpec/IndPartsProg5` | 2.1 → 7.9 G | 0.4 → 1.4 | 940 → 1043 |
| `Arena/IndPartsSpec/Bf` | 78.2 → 41.3 G | 16.2 → 7.5 | 1394 → 1142 |
| `Arena/IndPartsSpec/BrsW` | 17.1 → 17.1 G | 3.7 → 3.2 | 1098 → 1097 |

Lines: +84 −191 (**−107**).

### Batch 3: `nest_root_canon`, `nest_uniform_ok` (`pfuel 3`, `pfuel 4`)

mgen3 listed them under "fuel offsets" (`CallM` fuel-offset models, stated at `k + 3`, `k + 4`).
Both are now `l_model`s in `IndPosSpec/NestHoles.lean` where their hand models were
(`nestRootCanon_spec`: `pfuel 3`, callee specs at `n + 2`; `nestUniformOk_spec`: `pfuel 4`, over
the former), both with `fold [erRd]`; the generated models are the hand ones by `rfl`. Gone: the
hand continuations `nrcK1`–`nrcK3`, `nuK1`–`nuK3`, their arm lemmas, and the two hand specs in
`NuW.lean`. The walks `nrcW_ok`, `nuW_ok` only renamed (`nrcK1_some` → `nrcW.k_cv_lps.arm1`,
`nuK1_ok (h := …)` → `nuW.k_pi_doms_occ.arm2 (hc1 := …)`, …).

| module | instructions | user s | RSS MB |
|---|---|---|---|
| `Arena/IndPosSpec/NestHoles` | 10.8 → 16.4 G | 2.0 → 3.3 | 1043 → 1056 |
| `Arena/IndPosSpec/NuW` | 19.3 → 11.5 G | 4.4 → 2.6 | 1054 → 1047 |

Lines: +28 −88 (**−60**).

### Batch 4: `nest_canon_crest`, `whnf_walk_fuel` (`pfuel 2`), `nest_crest` (`pfuel 3`)

The rest of mgen3's "fuel offsets" (`pfuel` callers at the same fuel). `nestCanonCrest_spec`
and `whnfWalkFuel_spec` are `l_model`s in `IndPosSpec/DepthGo.lean` where the hand models were;
`nestCrest_spec` is one in `IndPosSpec/PcrW.lean` (with `CrLook`'s binder named `L`, now
allowed). Gone: `pccA`, `pccB`, `pccC` (`DpGoW.lean`) and their arms, the hand `wfW` (a `match`),
`pcrK1`–`pcrK3` with their files `PcrK1.lean`, `PcrK3.lean`, and `NestCrest2.lean` (only the
hand spec and `pcrK1`'s arms; its two importers import `PcrW`). The walks (`pccW_ok`, `wfW_ok`,
`NestCrest`'s `nest_crest` walk) and the frame lemmas (`pccW_mfr`, `pccW_afr`, `wfW_afr`,
`pcrW_mfr`, `pcrW_afr`) only renamed the continuations (`pccB_ok … hz` →
`pccW.k_inst_pis_with.arm2 (hc1 := hz)`, `unfold pcrW pcrK1 pcrK2 pcrK3` → `simp only [pcrW,
pcrW.k_nest_canon_crest.eq_def, …]`).

| module | instructions |
|---|---|
| `IndPosSpec/DepthGo` | 30.5 → 29.6 G |
| `IndPosSpec/DpGoW` | 17.7 → 17.7 G |
| `IndPosSpec/PcrW` (+ `PcrK1`, `PcrK3`, `NestCrest2`, gone) | 1.8 + 1.8 + 1.0 + 4.5 → 3.3 G |
| `IndPosSpec/NestCrest` | 32.7 → 32.6 G |
| `IndRealAbsPos` | 41.3 → 41.3 G |

Lines: +58 −230 (**−172**), three files fewer.

### Batch 5: helper `mgen4-romfront` (#263)

18 functions; 15 files, +841 −1298 (**−457**). Opened by `mixed` and `guards`: `node_lit_str`
(`str_put_esc`), `node_const` (`ls_put`; a `grind_pattern` `lsPut_room` for its room fact),
`apply_str` (`void`; bridge `applyStrW_kn`), `rom_levels` (`tuple`, `guards ["rom_u64"]`,
`stk_pool` as a `mixed` callee, `fold [stkTop]`), `rom_ex_leaf`, `rom_ex_ref` (inversions
`romLeafW_kb_inv`, `romLeafW_ks_inv` replace `exLeafK_inv`), `IndFieldsSpec`'s `if_reset`,
`fld_alloc`, `ind_num`, `ind_bool`, `ind_nlist`, and the eight ROM pin readers of
`Rom/PinReadSpec` (`pre`/`keep`; `erec_put`'s bound bridged by `erecGuard_lo`/`_put` and short
step lemmas; about 25 hand continuations and 8 hand specs gone). Kept: `rom_names_to` (the `PINS`
bound), `rom_name` (`romName rom` is a `FunDecl` with a parameter: "the function is not a
constant"), `lp_put`, `ifl_ids` (fuel-free loop models over the input, walked by position).
Largest change: `Front/Line` 12.8 → 17.1 G; `PinReadSpec` 51.6 → 54.7 G, `PinSets` 60.4 →
64.2 G; the others within ±2 %.

### Batch 6: helper `mgen4-levels` (#265)

19 functions; 15 files, +429 −1060 (**−631**). `lv_eq`; `lv_subst`, `lv_subsimp`, `lv_dist1`,
`lv_dist2`; the seven-function comparison group `lv_leq`, `lv_rest`, `lv_imax`, `lv_imax_l`,
`lv_imax_r`, `lv_cases`, `lv_cases_at` (one `l_model leqSpecs`, `defs` in `LevelLeq`, `nodefs` in
`LevelLeqSpec`; the 7-step hand induction gone); `lv_apd`, `alpd_ls`; `lp_app`, `lp_lam`,
`lp_forall`, `lp_let` (`pfuel`; the shared hand model `ilwBinW` replaced by the plain shapes
`ilwBinS`/`ilwLetS` the refinement uses and one bridge each, `ilwAppW_eq` …). Hand specs at
`maxHeartbeats` 1 000 000 – 4 000 000 gone. Kept: `lh_push` (its `CTL` size bound). Largest
slowdown: `LevelLeqSpec` 36.7 → 96.5 G (6.8 → 17.3 s, 2.6×; `simp []` recipes do not apply);
gains in `LevelSubst` 16.0 → 8.3 G, `LevelApd` 14.2 → 7.8 G, `DeclApdSpec` 52.0 → 40.4 G,
`InstLPWalkArms` 23.9 → 15.2 G.

### Batch 7: helper `mgen4-rx` (#266): the RxMapW memo walk

The largest family mgen3 left ("memo walks whose hand models fold find + put into `msetG` and
merge kinds"). No generator change was needed: one `l_model rxSpec_all` over the eight functions
of the block (`fv_map_at`, `nest_hole_img`, `_frame`, `_ds` as tuples, `_ds_go` void,
`replace_fvars_go`, `replace_fvars_node`, `replace_fvars`) and `rxRoot_spec` for
`nest_hole_img_root`, default recipe, same names and conjunction order (callers' `.2.2…`
projections unchanged). The hand shape is kept where users want it by six bridges in `Rx.lean`:
`rxGoW_kNode` (the `rf_find`/`rf_put` continuation after the node is the `msetG` form, via
`msetG_eq`), `rxGoW_kMap` (the fvar arm), `rxGoW_leaf`/`rxGoW_fvar` (the merged kind
disjunction over the generated separate `if`s), `rxMapW_kImg`, `rxDsGoW_kGo` (identity
continuations). `MapOKStep` walks the generated arms. Kept: `hiW`, `kmW` (total word models).
Gone: the hand mutual block, about 50 continuations' arms, `RxSpec`, `rxSpec_zero`, 8 step
proofs. 14 files, +347 −702 (**−355**). `RxMapW` 41.9 → 2.5 G, `Rx` 39.8 → 70.6 G (1.8×),
`PosmemoRxMfr` 10.2 → 14.4 G (its `split` over the whole generated term was 5.3×; `by_cases`
through the arms instead), 14 modules 245 → 263 G.

### Round 3 generator changes: functions with parameters, constant bytes

`fns [hL.rom_name ↦ …]` with `rom_name = romName rom` failed: "the function is not a constant"
(helper mgen4-romfront). A `FunDecl` with parameters is now accepted when its arguments are the
command's binders of the parameters' names (`(rom : List UInt8)`); they become parameters of
the models (the L text reads `rom.c8[pos]`). A constant byte read now adds `L.ldc` to the steps'
`vcgen` lemmas. Test `tParm_spec`. `rom_name` itself is still hand-written: a first try (`pre`,
`keep`, `guards ["rom_u64"]`, `rom_put` as a `mixed` callee) generates a model of the hand
shape, but one step goal after `rom_put` does not close with the default recipe, and its model
`romNameW` is walked in ten files (all ROM readers, no ronsync churn); not pursued.
