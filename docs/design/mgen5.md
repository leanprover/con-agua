# Lane mgen5: family conversions of wide-reach hand models

Fifth lane on `l_model` (`ConAgua/L/ModelGen.lean`; earlier: `docs/design/mgen.md`,
`docs/design/mgen3.md`, `docs/design/mgen4.md`). mgen4 §4 listed the hand models that are
unfolded by name in many files and called each a family conversion like its batch 7 (RxMapW:
generate, bridge to the hand shape the users walk, simplify the users where cheap), with no
generator change needed. This lane does those, `rom_name`, and the two bounds cases, and samples
the specs without a model. Same constraints as every lane: no L program change, no final
statement change, no new axiom, no heartbeats raised. Rule (user, 2026-11-10): a slower module is
accepted; only > ~3× or > ~60 s per module blocks.

## 1. Inventory (master b7003b70)

mgen4's script, rerun as `_tmp/mgen5/inv.py` (outside the repository): 252 hand-specified
functions, 1 073 `l_model` commands; 185 hand specs have no model in their post. The families
the task names, with the files that mention the model (besides its own):

| model | function(s) | files | owner |
|---|---|---:|---|
| `nIdxsW` | `block_shape_n_idxs` | 4 | helper `mgen5-parts` |
| `lpsW` | `block_shape_lps` | 6 | `mgen5-parts` |
| `psGoW` | (`IndSumSpec/StructElimLevel`) | 4 | `mgen5-parts` |
| `tmdW` | `target_major_default` | 4 | helper `mgen5-rec` |
| `stripTW`, `stripF` | `strip_lams`, `strip_pis` | 1 | `mgen5-rec` |
| `bvbW` | `bvar_b` | 10 | `mgen5-rec` |
| `eftW`, `eftF`, `eeW`, `tteW` | the `erase_fvar_tys` family | 2–3 | `mgen5-rec` |
| `romNameW` | `rom_name` | 9 | helper `mgen5-rom` |
| `romNamesToW` | `rom_names_to` (`PINS` bound) | 0 | `mgen5-rom` |
| `getDW` | `sl_getd` | 4 | lead |
| `selW` | `reduce_op_cv_a`, `of_reduce_pin_a`, `reduce_decl_pin` | 0 | lead |
| `lhPushW` | `lh_push` (`CTL` size bound) | 2 | lead |

## 2. Lead conversions

### `selW`: three pin-selected ROM readers

`reduce_op_cv_a`, `of_reduce_pin_a` and `reduce_decl_pin` shared one hand model `selW p n m c k f i
j` (`pin_at(k)`, then `f(i)` or `f(j)`) and one relational lemma `selW_ok`. Each is now an
`l_model` (default recipe, callee specs `pinAt_specW`, `callW_spec`); the generated models
`rocaW`, `orpaW`, `rdpW` are `selW` at their constants by a four-line bridge each
(`rocaW_selW`: `cases` on the fuel, the pin read and the callee), so `selW_ok` and the three
refinements stay as they were. Gone: the three hand specs, `selK`'s and `selK2`'s arm lemmas and
their patterns. `DeclReduceSpec.lean` +49 −57; 10.9 → 12.1 G instructions, 2.2 → 2.3 s, 1051 →
1055 MB.

### `getDW` (`sl_getd`): kept

`getDW m o l i d` is a total word (`if l ≤ i then d else IW.u64[o + i]`), the pure post `r.headD 0
= getDW …` of `slGetD_specW`, and five `l_model`s take that spec as a callee, so the word is
inlined in their generated models. A generated `ro` model is `Option Word`: the five callers'
models would get a continuation per call instead of the word, and the four files that reason
about `getDW` (`getDW_handle'`, `getDW_nat`, `getDW_head`, `MapOKStep`) would need a bridge back
to the word. The hand spec is ten lines; nothing to gain. mgen4 §4 already counts it among the
total word models kept as vocabulary.

### `lh_push`: kept (the `CTL` size bound)

`lhPushW` returns `none` when `(m.arr64 CTL).size ≤ 192`. L has no such test (the store
`CTL.u64[192] := o + 1` aborts out of bounds); a generated model treats an out-of-bounds store as
no change, so it drops the case. Its user `lhPushW_ext` needs it: the heap top advances by one
(`(htop m').toNat = (htop m).toNat + 1`) only if `CTL[192]` is in bounds. Neither generator
option covers it:
* `guards` reads guards off a *callee's* post; `lh_push` has no callee;
* `pre [192 < (s₀.mem.arr64 CTL).size]` makes the fact a hypothesis of the spec, which
  `lh_push`'s callers must then discharge: `lv_zero`'s hand spec and `lp_substl`'s (they pass
  `lhPush_spec` to `vcgen`), and through `zeroW_ok` the refinements that call `lv_zero`
  (`FormerNZRef`, `ProjGuardRef` three times, `PropReadRefine`, `LevelSubstL`), whose states
  (`CoreS`, `LvR`) carry no `CTL` size (`IWOK.ctl : 200 < (m.arr64 CTL).size` lives in the
  inductive stage relation, not in `CoreS`).
`rom_names_to`'s bound (#281) could move into its refinement because its one caller has the
bound at hand; here no caller has it. Threading a `CTL`-size hypothesis through `zeroW_ok` and its
six callers to save a ten-line spec is no win. The same holds for `lh_mk` (`lhMkW`, the same guard). This is a case for a generator
option that models a store's bound as a guard (`none` out of bounds), not for a lane.

### The Front install records: `ind_cv`, `parse_rule_d`, `decl_cv`

Hand models `cvW`, `ruleW` (`IndApplySpec2`, written with the continuations `wK`/`mK` over
`lkW`, the table lookup) and `ApplyDecl`'s `cvW` with its hand spec over `decl_cv`'s results
(churn: `IndApplySpec2`'s family carries 610 ronsync2 lines, the fifth in the inventory). All three
are `l_model`s now (default recipe; `guards ["name_get", "expr_get"]` turns the lookups' `tblOK`
conjuncts into guards, `lp_put` is a `mixed` callee, `pre [s₀.mem.arr8 IN = b]`, `keep`). The users
keep their shape through one bridge each: `cvW_eq` and `ruleW_eq` restate the generated models in
the `wK`/`lkW` form (`IndInstallRefine`, `IndInstallRefine3`: `unfold` → `rw`), `dcvW_cv` gives
`decl_cv`'s four result words and the memory `cvW` (kept as `apply_decl`'s vocabulary; one use in
`ApplyDLineRef`). Gone: three hand specs (39 lines) and the two hand models. 5 files +54 −58.

| module | instructions | user s | RSS MB |
|---|---|---|---|
| `Front/IndApplySpec2` | 38.0 → 38.6 G | 6.8 → 6.8 | 1054 → 1051 |
| `Front/IndInstallRefine` | 10.2 → 10.2 G | 1.4 → 1.5 | 959 → 950 |
| `Front/IndInstallRefine3` | 40.1 → 40.1 G | 4.8 → 4.7 | 1135 → 1171 |
| `Front/ApplyDecl` | 16.3 → 16.4 G | 3.2 → 3.2 | 921 → 953 |
| `Front/ApplyDLineRef` (three lines) | → 20.0 G | → 3.5 | → 1049 |

### The nest frame walks: `nest_frame_grp`, `nest_frame_holes`, `nest_cont_new_active`

Hand mutual blocks `fgW` (with `fgK1`, `fgKb`, `fgK2`–`fgK4`), `fhW` (`fhK1`, `fhK2`), `caW`
(`caK1`, `caK2`) in `IndPosSpec/FgW2.lean`, their hand specs in `GgW2.lean` (each an induction
with `finish (gen := 20) (instances := 5000)`). All three are `l_model`s in `FgW2.lean` now (the
hand recipe: `grind [arena_grind, ind_grind] finish [rdW_eq, Locals.init_cons_zero, …] gen 20
instances 5000`; `fgW`'s callee `pi_binders` needs `import IndPartsSpec.BlockCounts`). The
generated models are the hand ones but for one step: the recursive call's result goes through
`fW.k_<self>` (`some ([r.headD 0, r.tail.headD 0, …], m)`, the `return (r0, r1)`), where the hand
model passed it on. A bridge per model, `fgW_kId`/`fhW_kId`/`caW_kId` (that step is the identity
on the model's own results: every leaf is a list literal of that length), lets the hand arm
lemmas stay under their names as one-line restatements of the generated arms (`fgW_cons`,
`fgK1_some` … `fgK4_some`, `fhK1_ok`, `caK2_some`, …), so the walks `fgW_ok`, `fhW_ok`, `caW_ok`
only rename the continuations in their `none` cases; the frame lemmas (`…_mfr`, `…_afr`) unfold
the generated equations with the bridge. The callers `PosFrame`, `PosNew` take the results list
directly (the hand post's `[r.headD 0, …]` and its `generalize` blocks are gone). Gone: the three
mutual blocks, the hand specs. 6 files +167 −198 (−31).

| module | instructions | user s | RSS MB |
|---|---|---|---|
| `IndPosSpec/FgW2` | 69.3 → 28.6 G | 10.2 → 4.8 | 1046 → 1085 |
| `IndPosSpec/GgW2` | 24.7 → 9.1 G | 4.8 → 1.7 | 1120 → 1020 |
| `IndPosSpec/FgW` | 18.2 → 18.0 G | 3.1 → 3.1 | 1097 → 1095 |
| `IndRealAbsPos` | 43.0 → 42.9 G | 8.6 → 8.6 | 1230 → 1229 |
| `IndT/PosFrame` | 9.1 → 8.9 G | 1.3 → 1.2 | 1114 → 1105 |
| `IndT/PosNew` | 11.9 → 11.8 G | 1.7 → 1.7 | 1125 → 1121 |

## 3. Helper batches

### `mgen5-parts` (#272, #273, #275): `nIdxsW`, `lpsW`, `psGoW`

* **#272** `block_shape_n_idxs` (`nIdxsW`, list), `n_idxs_copy` (`nIdxsCopyW`, void),
  `block_shape_num_ctors` (`numCtorsOfW`, ro) and `block_shape_member_names` (`memberNamesW`,
  `nIdxsW`'s twin: allocate, copy): default recipe. Bridges `nIdxsW_inv`, `memberNamesW_inv`
  (the allocation, the copy and the result's shape) and `nIdxsCopyW_step`; the walks (`_dec`,
  `_room`, `_afr`, `_mfr`, `ClassNPcOf`'s room proof) use them. 8 files +125 −244 (−119); every
  module within 0.1 G (`RulePrefixAt` 30.0, `NestCtx` 14.8 → 14.7, `MemberNames` 14.5 → 14.6).
* **#273** `block_shape_lps` (`lpsW`, `fold [erRd]`): bridges `lpsW_nil`, `lpsW_cons` keep the
  hand arms, so `EqW`, `NestCtx` and `lpsW_dec` are unchanged; the two frame lemmas walk the
  bridges. 3 files +21 −35 (−14); the 11 dependent modules within 0.1 G.
* **#275** `struct_ps_at_go` (`psGoW`), `struct_ps_at` (`psAtW`), `struct_proj_ps` (`projPsW`; the
  last two shared `psGoW`'s hand continuation `psK3`): gone `psK0`–`psK3`, arms, three hand specs;
  `psGoW_ok`, `psGoW_stage`, `psAtW_ok`, `structProjPs_refines` and the frame lemmas walk the
  generated arms. 6 files +72 −174 (−102). `StructElimLevel` 21.3 → 9.1 G (3.4 → 1.6 s),
  `StructProjArgP` 33.3 → 33.9 G, the rest unchanged.

### `mgen5-rec` (#269, #271, #276, #279, #280, #282): `tmdW`, `stripTW`, `bvbW`, the `erase_fvar_tys` family, `tmaW`

* **#269** `target_major_default` (`tmdW`): the generated model is the hand one up to the
  continuations' names (`tmdK1`–`tmdK3` → `tmdW.k_intern_nanon`, `k_pin_word`,
  `k_mk_target_major`); its spec holds at every fuel, so two callers pass `n + 1`. 6 files +21 −54
  (−33); all modules within 0.2 G.
* **#271** `strip_pis`, `strip_lams` (`extra [evalE_tagE, evalE_idxAE, evalE_idxGE]`): the two
  generated loops are bridged (`stripPisW_loop1`, `stripLamsW_loop1`, by induction over the
  arms) to the tag-parametric loop model `stripGoW` that the relational, fuel and frame lemmas
  keep walking (two generated loops cannot share one lemma otherwise); `stripF` is `stripGoW` at
  `k + 2`. Gone: `stripTW`, its arms, two hand loop specs, two hand specs. 3 files +99 −125 (−26).
  `StripTeleSpec` 31.3 → 17.3 G (4.7 → 3.1 s).
* **#276** `bvar_b` (`bvbW`), `loose_bvars_bounded_fast` (`lbbW`): the generated `bvbW` takes the
  L argument order `(f, e)`, so its users state `bvbW n m f h` and use `bvbW.arm1`/`arm2` for the
  hand `bvbW_sat`/`bvbW_pk`. 11 files +47 −74 (−27). `BvarB` 4.9 → 6.3 G (0.8 → 1.0 s), the rest
  within 0.1 G.
* **#279** `erase_fvar_tys` (`eftF`), `erase_each` (`eeW`), `target_k53_tele` (`tteW`),
  `target_canon_params` (`tcpF`), default recipe: `eftF` and `tcpF` are the generated models at
  every fuel, so the hand body-fuel models `eftW`, `tcpW`, their continuations and the at-fuel
  wrappers are gone; one bridge `tcpF_succ`. Gone: 9 hand continuations, 6 hand specs. 15 files
  +93 −249 (−156). `EeW` 7.6 → 5.3 G, `Tka` 4.9 → 1.9 G, `EraseFVarTys` 6.2 → 6.8 G.
* **#280** `target_major_at` (`tmaW`): fuel-free now (`tmdW`'s spec holds at every fuel, so the
  hand `fuelW n (tmdW m)` wrapper goes); the simulations over it (`tmaW_sim`, `rec2SimTMA`,
  `rec3TMA_sim`) and the unified model of `IndBRec1` lose their fuel argument (and `rg_ref` its
  zero case). Gone: the hand model, its continuation, arms, `targetMajorAt_spec`,
  `targetMajorDefault_specF`, `tmdW_sim`. 11 files +69 −142 (−73); all within 0.1 G.

* **#282** `nest_ctors_u4` (`u4W`), `nest_ctors_res_ok` (`roW`), with the lead's `fW_kId` bridge
  for the recursive call's result step and the hand arm names kept as restatements;
  `structUsedLater_spec'` moved to `U4W`; three re-exporting imports allowlisted for `shake`.
  9 files +88 −100 (−12). `U4W` 14.1 → 6.0 G, `GgW2` 9.1 → 3.2 G, `P2ctK1` 1.9 → 4.0 G (the
  `l_model`), the rest within 0.4 G.

Kept by this helper: `bbN` (the at-fuel wrapper of `bb_memo`'s spec, a callee spec) and
`stripGoW` (above).

### `mgen5-rom` (#278, #281): `rom_name`, `rom_names_to`

* **#278** (`--wide`) **Generator**: a `fold` function whose body is a constant byte read
  `(D[i.toNat]?.getD c).toUInt64` (`romB rom pos`, `getD 255`: past the ROM's end the hand models
  read 255, no tag) is folded where the L code reads `rom.c8[pos]` (`Fold.byteSrc`); before, the
  generated read was `(rom[pos.toNat]?.getD 0).toUInt64`, a position past the end read as tag
  `0`, and `romNameW_dec` was false for the generated model (`rom = []`, `pos = 0` gave
  `anonymous`). Without such a fold the output is as before; the gate build rebuilt every
  `l_model` module unchanged. Test `tParmB_spec`. **Conversion**: `romName_specW` is an `l_model`
  (`pre`, `keep`, `guards ["rom_u64"]`, `fold [romB]`, `defs`, then `romNameW_top` over the
  generated arms (the pool top stays in a tier after the recursive call: the step goal mgen4 could
  not close), then `nodefs`). Gone: the hand model, its five continuations, `romPutW`, their arms,
  the hand spec, the `nm*_inv` lemmas in `Dec`; `romNameW_ok`, `romNameW_dec` walk the generated
  arms; the other eight ROM files are unchanged (they use only those lemmas). 4 files +174 −258
  (−84). `Rom` 40.1 → 39.4 G, `Dec` 13.1 G, the others within 1 %; `ModelGenTest` 95.9 G.

* **#281** `rom_names_to` (`defs`, `romNamesToW_topK` over the generated arms, `nodefs`) and
  `intern_reserved_pins` (default recipe; `irpW rom off n m`). The `PINS` bound: the store
  `PINS[d] := h` is inline, not a callee, so neither `guards` nor `pre` carries it into the model;
  it moved to the refinement instead, `romNamesToW_ok` takes `d + |ns| ≤ |PINS|`, and its one
  caller `irpW_ok` has it from the function's own `len(PINS) ≥ 72` test and the frames. Gone: the
  hand mutual model, `namesToK`, `irp1K`–`irp6K`, their arms, both hand specs. +31 −94 (−63);
  `RomPins` 21.3 → 19.2 G (3.6 → 3.3 s).

## 4. The 185 specs without a model in their post

Classified by their posts (script over `_tmp/mgen5/inv.json`), and 22 read by hand (random
sample, seed 5: `scan_opaque`, `nat_mod_lit`, `class_gen_major`, `class_key_of`, `utf8_char`,
`key_at_g2`, `caps_eq_a`, `str_code`, `nat_add`, `class_rules_ok`, `ci_eq_rest`,
`check_block_idx_sorts`, `nest_accept_group`, `class_minor_slot_go`, `hints_val`,
`class_recs_rules_ok`, `stk_push`, `key_at_g6`, `block_shape_major_idx_at`, `match_lit`,
`scan_binder_info`, `install_basis_decls`):

| kind | count | example | could a generated spec replace the hand proof? |
|---|---:|---|---|
| refinement triples (`AM.ok …`, `@[refines]`) | 61 | `install_basis_decls`, `check_block_idx_sorts` | no: these are the refinement layer itself, 6–7-line proofs that chain the callees' refinements through `vcgen`; a generated model would be a new intermediate plus a simulation lemma, more text than now |
| a value over the input bytes (`r = [fN b i]`) | 48 | `scan_opaque`, `key_at_g2`, `match_lit` | no: `fN` is the twin-shaped spec over `List UInt8` (`refines_part`), not a word model; a generated `ro` model needs a bridge `fW m i = some (fN (m.arr8 IN) i)` whose proof is the hand proof (8–20 lines) |
| a total memory effect (`G ∧ s'.mem = F`) | 32 | `stk_push`, `nat_mul`, `tbl_own_set` | no: callers' `l_model`s read this shape as a total callee (inlined, `G` a guard); a generated `Option` model would put a continuation into every caller's model |
| other value/relation posts | 33 | `nat_add` (`PFrame`, `Agree`, `pv … = pv … + pv …`), `nat_trim`, `skip_digits` | no: the post is the relation the callers need, over `Nat` values of limb slices |
| a Boolean predicate (`r.headD 0 = if PB … then 1 else 0`) | 10 | `caps_eq_a`, `ci_eq_rest` | no: as for the byte values (the predicate is the spec; 9-line proofs) |
| a model under `∃` | 1 | `class_minor_slot_go` (`∃ x y z w, classMinorSlotGoW … = some (x, y, z, w)`) | its model checks `(m.arr64 IW).size` (two out-of-bounds arms that its users take): a bounds case |

Yield: none of the 22 sampled, and by the classification at most the one `∃` case of the 185,
which is a bounds case. These hand proofs are short (median about 10 lines) and their posts are
the vocabulary the callers' generated models and the refinements use; a generated spec would add
a bridge per function at least as long as the proof it replaces. Not converted.

## 5. Totals (master b7003b70 → this landing)

* **Functions**: 35 converted. Lead 9 (`reduce_op_cv_a`, `of_reduce_pin_a`, `reduce_decl_pin`,
  `ind_cv`, `parse_rule_d`, `decl_cv`, `nest_frame_grp`, `nest_frame_holes`,
  `nest_cont_new_active`); `mgen5-parts` 11; `mgen5-rec` 12; `mgen5-rom` 3. The inventory
  script counts 237 hand-specified functions now (252 at the start; it counts a function as
  hand-specified while any triple over it is hand-proved, so wrapper specs such as `bbN` keep
  some converted functions in), 188 of them with no model in their post.
* **Lines** (`git diff --shortstat b7003b703 -- ConAgua`): 78 files, +1 152 −1 939, **−787**, the
  generator change (`ModelGen.lean`, `ModelGenTest.lean`: +36 −2) included.
* **Build time**, the modules each batch changed, measured alone before and after
  (`LEAN_NUM_THREADS=1`): about −95 G instructions in all. Gains: `FgW2` 69.3 → 28.6 G, `GgW2`
  24.7 → 3.2 G (two batches), `StripTeleSpec` 31.3 → 17.3 G, `StructElimLevel` 21.3 → 9.1 G,
  `U4W` 14.1 → 6.0 G, `Tka` 4.9 → 1.9 G. Slowdowns: `P2ctK1` 1.9 → 4.0 G (2.1×, 0.8 s), `BvarB`
  4.9 → 6.3 G (1.3×), `DeclReduceSpec` 10.9 → 12.1 G (1.1×), `ModelGenTest` 92.8 → 95.9 G (one
  test more). No module above 3× or 60 s (the slowest touched, `IndRealAbsPos`, 8.6 s). Peak RSS
  0.9–1.5 GB throughout. No heartbeats raised.
* **Generator**: one change (#278, `--wide`): `fold` of constant byte readers
  (`(D[i.toNat]?.getD c).toUInt64`, `Fold.byteSrc`), off unless such a fold is given; every
  `l_model` module rebuilt unchanged.

## 6. What stays hand-written, and whether more model work is worth a lane

The 49 hand specs with a model in their post, by kind:

* **Vocabulary** (models named in more than 40 files, or the decoders): `rdW`, `allocW`
  (`ifr_alloc`, `ifl_alloc`, `dind_alloc`), `decHL`, `decPL`, `decCVp`, `res`; the total word
  models `getDW` (§2), `hiW`, `kmW`; the shared readers `cntW` (27 files), `slotW` (9). Not models to replace.
* **Templates** (`consInternG zeroCS`, memo schemas: no `lfn` text): `intern_zero`, `intern_max`,
  `intern_lit_str`, `fr_memo`.
* **Fuel-free loop models over the input**, walked by position (mgen4 §4): `lp_put`, `ls_put`,
  `ifl_ids`, `nat_dec`, `sub_rec`, `scan_bool`.
* **Bounds of a store** (the L code aborts out of bounds, the generated store does not): `lh_push`,
  `lh_mk` (§2), `name_put`/`level_put`/`expr_put` (`tblPutW`'s size checks). A generator option
  that models an inline store's bound as a guard (`none` when the index is past the array's
  length, as L does) would open all five; `rom_names_to` (#281) shows the alternative, moving the
  bound into the refinement, which works only where the caller has it.
* **Small remaining families**, each convertible by the pattern of this lane: `lp_lookup` /
  `lp_substl` with `lv_lookup`, `lv_substl`, `lv_spw` (`LevelSubstL`: one hand model generic in the
  key read `KR`, shared by the `lv_` functions over `EREC` and the `lp_` ones over `SPN`; the
  generated models would be one per function and need a bridge each to the generic one the
  refinements use; ronsync2 churn 332), `mentions_any_const` (`maConstW`, 156), `class_gen_rule`
  (`ruW`, 64), and a handful with churn under 30 (`ctors_have_name`, `class_key_of_closed`,
  `class_key_canon`, `target_abs`, `lvl_eq_rec`, `block_shape_build`, `and_pin_ok`, `nat_cmp`,
  `proof_pw`, `apply_nnum`, `apply_level`, `ifl_push`).
* The 188 without a model: §4 (no yield).

**Is more worth a lane?** Not a full one. What is left with a model is mostly vocabulary,
templates and fuel-free input loops, none of which a generated spec replaces. The convertible
rest carries about 600 ronsync2 lines of churn (`LevelSubstL` the bulk), against 3 000–11 000
for the vocabulary models a sync touches anyway. Worth doing: the store-bound guard option in
the generator (five functions, and future code), and `LevelSubstL` as one small batch, both of
which fit a short follow-up rather than a lane.
