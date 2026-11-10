# Lane mgen3: resuming the conversion to `l_model`

Third lane on `l_model` (`ConAgua/L/ModelGen.lean`; `docs/design/mgen.md` for the first two).
The rule changed on 2026-11-10 (user, PLAN.md "Generated over hand-written models"): a conversion
that makes a module slower is no longer blocked; fewer hand models and proofs win over build time,
since a twin sync re-walks every hand model it touches (`docs/design/reproof.md` §2.4: 208 of the
last sync's long manual proofs walked a hand `…W` model call by call). Only an egregious regression
(~3× or above ~60 s per module) blocks a conversion, and then the generated model or the proofs
about it get fixed. Same constraints as every lane: no L program change (`checker.s`, `pins.bin`
identical), no change to a final statement, no new axiom, no heartbeats raised.

## 1. Inventory (master b91d1604)

Script `_tmp/mgen3/inv.py` (outside the repository), with `_tmp/mgen3/fam.py` for the family
table. Classification, stricter than mgen's (§1 there counted every triple that names `"f"`,
including callee premises `p.lookup "f" = …`):

* the program `checkerProg` has 1 775 functions, 289 of them template instances (`FunDecl`s
  with parameters: `memoFindG S`, …; generic hand specs, out of scope here);
* a function is *generated* if an `l_model` names it: **765**;
* it is *hand-specified* if it is not generated and some theorem's triple has it as its
  program (`invoke p … "f"` or `f.body` between the pre and the post): **591**;
* a hand spec's *models* are the heads of its post's conjuncts `F … = some …` and `r… = F …`;
  a model named in more than 40 files is vocabulary (`rdW`, `pinW`, `decPL`, `allocW`, …), not
  a hand model.

**Churn weight.** For each hand model, the changed lines (`difflib`, by declaration name,
reproof's `decls.py` on `09a78343a` → `86737151d`, ronsync2) summed over every declaration
of that sync that is the model, one of its `_`/`.` lemmas, or mentions it: what the sync cost
around that model. A family is the file that defines the models. 237 families, 23 603 lines
in all; the first 32 carry 70 %:

| family (models' file) | fns | reach | ronsync2 lines | cum. |
|---|---:|---:|---:|---:|
| `Arena/IndIface.lean` | 16 | 22 | 2835 | 12 % |
| `Front/IndApplySpec.lean` | 12 | 13 | 2057 | 20 % |
| `Rom/CIReadRefW.lean` | 18 | 9 | 1815 | 28 % |
| `Arena/IndInstallSpec/IcaW.lean` | 5 | 0 | 604 | 30 % |
| `Arena/DeclAndPinIndCopy.lean` | 3 | 1 | 600 | 33 % |
| `Arena/DeclHeader.lean` | 2 | 7 | 573 | 35 % |
| `Arena/IndInstallSpec/BlockRawRec.lean` | 5 | 4 | 546 | 38 % |
| `Arena/IndSumSpec/ConsBlockRecsTF.lean` | 4 | 2 | 521 | 40 % |
| `Arena/DeclCanonInfo.lean` | 4 | 1 | 475 | 42 % |
| `Front/IndApplySpec2.lean` | 9 | 4 | 440 | 44 % |
| `Arena/DeclCanonConst.lean` | 2 | 1 | 386 | 45 % |
| `Arena/IndDeclConstsDrop.lean` | 2 | 1 | 369 | 47 % |
| `Arena/IndSumSpec/TblProg.lean` | 2 | 2 | 334 | 48 % |
| `Arena/LevelSubstL.lean` | 2 | 5 | 332 | 50 % |
| `Arena/IndInstallSpec/PartsShapeFacts.lean` | 1 | 3 | 326 | 51 % |
| `Arena/IndPartsSpec/Bsp.lean` | 3 | 2 | 326 | 53 % |
| `Arena/StripTeleSpec.lean` | 1 | 9 | 322 | 54 % |
| `Arena/IndDeclConstsTable.lean` | 2 | 0 | 303 | 55 % |
| `Arena/WhnfIotaRefine.lean` | 1 | 1 | 302 | 57 % |
| `Arena/IndPosSpec/NcGoW.lean` | 2 | 7 | 298 | 58 % |
| `Arena/RecGenSpec/ClassFeR.lean` | 2 | 0 | 288 | 59 % |
| `Arena/IndPosSpec/RxMapW.lean` | 10 | 14 | 265 | 60 % |
| `Arena/RomPins.lean` | 2 | 0 | 254 | 61 % |
| `Arena/IndSumSpec/SumRules.lean` | 1 | 1 | 250 | 62 % |
| `Arena/DeclRec.lean` | 2 | 2 | 239 | 63 % |
| `Front/ApplyExpr.lean` | 9 | 2 | 239 | 64 % |
| `Arena/IndPosSpec/Pos2CvLpsWStage.lean` | 1 | 3 | 238 | 65 % |
| `Arena/IndDeclConstsRefire.lean` | 1 | 1 | 235 | 66 % |
| `Arena/IndLibSpec.lean` | 1 | 7 | 232 | 67 % |
| `Arena/RecClassSpec/CloseLams.lean` | 3 | 10 | 228 | 68 % |
| `Arena/WhnfIotaRefine6.lean` | 1 | 1 | 228 | 69 % |
| `Arena/IndPosSpec/U4W.lean` | 2 | 4 | 215 | 70 % |

("reach": the most other files any one of the family's models is named in.)

**By blocker** (first match in this order; syntactic, from the model's text and the spec's
hypotheses; "time" no longer blocks):

| blocker | functions | ronsync2 lines |
|---|---:|---:|
| reach (a model named in > 2 other files) | 141 | 12 815 |
| shape (`match` / `bind` / `do` in the hand model) | 48 | 1 826 |
| a precondition over `s₀.mem` (`pre`, `keep`) | 47 | 968 |
| bounds (`.size`, `ldE`, `136 <` in the model) | 5 | 77 |
| none of these (rejected for time or size, or never tried) | 147 | 8 644 |
| no model in the post (`r = [..]`, a pure or relational post) | 203 | 0 |

The 203 without a model are specs whose post is already a value (`r.headD 0 = …` over twin
values, a relation): nothing to convert. So the work is the 388 others, and by the sync's cost
the order is: the three big reach families (`IndIface`, `IndApplySpec`, `CIReadRefW`), then
the low-reach families above (most of them are "none of these": small files whose conversion
the old time rule rejected or nobody tried).

**Split.** The lead takes the reach families (`Front/IndApplySpec`, `Rom/CIReadRefW`,
`Arena/IndIface`'s models) and `Front/ApplyExpr`; three helpers take disjoint groups of the
low-reach families (§2).

## 2. Measuring

`_tmp/mgen3/measure.sh WORKTREE F.lean…`: `perf stat -e instructions:u` and `/usr/bin/time` around
`scripts/lake env lean F.lean` with `LEAN_NUM_THREADS=1`; instructions (G), user seconds, peak
RSS. Before and after on the same worktree, the changed modules and the users that changed.

## 3. Batches

### Batch 1: `Front/IndApplySpec` (lead)

No generator change. Generated now: `store_fuel`, `ind_pi_tele_len`, `pi_sort_tele_len`,
`name_rec_pre`, `ifl_contains`, `ifl_nodup`, `ifl_find_last`, `vi_map_go`, `vi_map`,
`vi_listed`, `vi_nested` (11). Their hand models, the continuations `sfK`, `teleK`, `stK`,
`nodupK`, `restK`, `listedK`, `nrpStr`, the hand `mapW`, and their eleven hand specs are gone;
`exprGetL_spec` moved here from `Verdict/FrontViE` (it is `nameGetL_spec`'s twin, now needed by
`vi_map_go`'s generated spec), and `IndRealIpo`'s copy of the `pi_sort_tele_len` spec
(`sortTele_specI`) is gone: the generated `sortTele_spec` takes just the two lookups it needs.

The refinements changed little: renames (`teleK` → `teleW.k_ind_pi_tele_len`, `stK` →
`sortTeleW.k_pi_sort_tele_len`, `nodupK` → `nodupW.k_ifl_contains`), the continuation chains
`storeFuelW.k_ctl_sum{,_2,_3}` walked by their arms, a generated recursive call wrapped in its
identity continuation (`findLastW.k_ifl_find_last`), `vi_map`/`vi_listed` as flat tuples (so
`validateE`'s proofs lose their `flat3` steps), and two bridges: `mapLk` (the lookup chosen by
`f`) and `mapGoW_step` (the two generated arms that call `name_get` / `expr_get` share one
continuation), and `prd_rdW` (the generated `name_rec_pre` reads the pool by `rdW`; the
refinement states it with `prd`). `split` does not split the generated `if` on a three-way `∧` in
`nrpW_ok` (the instances differ from the ones `by_cases` builds); `simp only [hrec, ↓reduceIte]`
does.

Left in the file: the continuation combinators `lK`, `lkPushK`, `sliceK`, `allocK`, `mK`, `wK`,
`pmK` and `lkW` (used by `IndApplySpec2` and `IndInstallRefine*`, helper mgen3-consts's files).

| module | instructions | user s | RSS MB |
|---|---|---|---|
| `Front/IndApplySpec` | 34.4 → 52.6 G | 8.6 → 8.8 | 1013 → 1056 |
| `Front/IndApplyRefine` | 23.4 → 28.9 G | 3.5 → 3.4 | 1074 → 1109 |
| `Front/IndApplyRefine2` | 10.1 → 10.2 G | 2.1 → 1.6 | 943 → 953 |
| `Front/IndApplyRefine3` | 9.4 → 9.4 G | 1.7 → 1.3 | 935 → 928 |
| `Front/IndApplyRefine7` | 15.0 → 15.8 G | 3.5 → 2.9 | 996 → 1015 |
| `Front/IndApplyRefine9` | 31.8 → 31.9 G | 5.3 → 4.3 | 1141 → 1164 |
| `Verdict/FrontViE` | 25.2 → 25.5 G | 5.9 → 4.5 | 1048 → 1103 |
| `Arena/IndRealIpo` | 14.6 → 13.3 G | 3.2 → 2.5 | 1028 → 1017 |
| total | 163.9 → 187.6 G (+14 %) | | |

Lines: 7 files, +137 −413 (**−276**); `IndApplySpec` 519 → 245.

### Batch 2: generator `pfuel`; `Rom/CIReadRefW` (lead)

**Generator: `pfuel`** (`ModelGen.lean`, test `tPf` in `ModelGenTest.lean`). 61 hand-specified
functions have models in lane whnf's "a call as a function of the memory" style: every callee
through `callW p n "f"` (its own recursive call too), so the model is not recursive and takes the
fuel `n` as a parameter, and the spec is at `exec p (n + 1)` with the model at `n`
(`Rom/CIReadRefW` 15, `PropReadW` 9, `InstLPWalk` 4, `IcaW`, `IndT/BlockPD`, the `IndDeclConsts*`
files 1–2 each, …). `l_model` could generate their bodies (`specs [callW_spec p n "f", …]` with
`bind ntBW`, as `DeclNatGate`'s `depsStoredW` does), but only as a fuel-indexed model (`match n
with | 0 => none | n + 1 => …`), one off from the hand one, so every refinement would have
shifted its fuel. With `pfuel` (one function that does not call itself as its model) the model
is the body at `n`, its arms are stated at `n`, and the spec is `∀ s₀ args, ⦃s = s₀⦄ invoke p
(exec p (n + 1)) "f" args ⦃… fW … n s₀.mem args = some …⦄`, proved by the one step (no
induction). On `CIReadRefW` the generated model **is** the hand one: `slotG p n m s = slotW p n m s`
by `rfl` for 15 of its 17 functions.

**`Rom/CIReadRefW`**: `rci_slot`, `rci_fresh`, `rci_names_to`, `rci_lvls_to`, `rci_name_sl`,
`rci_cv`, `rci_caps`, `rci_rules_to`, `rci_block_to`, `rci_block`, `rom_basis_decls`,
`rom_and_pin`, `rom_ci`, `rom_cv`, `rom_expr_pin` generated (15 models and specs, same names, same
statements). The users needed three kinds of edit: a word read through `rom_u64_c` in a generated
model is a continuation over the result list (`fun ρ μ => … ρ.headD 0 …`), which the hand `rdU`
abbreviation's lemma `rdU_some` cannot match (its continuation is not a pattern), so a lemma over
the `ntBW` chain itself, `u64_some` (`k [u64W rom i] m`), and a `simp only [List.headD_cons]`
after it; `capsW`'s `where` part `capsTailW` is gone, so `CIReadRefCaps` names the rest of the
chain by `change ntBW (callW p k "rom_name_c" …) _ = …`; one `simp only [putE]` and one `dsimp`
had nothing left to do. `rci_rule` and `rci_ci` are not converted yet: their hand models are cut
into named parts (`ruleTailW`, `ruleLvlW`, `rulePinW`, `ciTailW`, `ciDefnW`, …) that the long
walks in `CIReadRefRule`/`CIReadRefCI` take apart by name; the generated ones are one body with
join points.

| module | instructions | user s | RSS MB |
|---|---|---|---|
| `L/ModelGenTest` | 83.9 → 84.9 G | 17.6 → 18.0 | 1075 → 1070 |
| `Rom/CIReadRefW` | 100.3 → 90.3 G | 20.0 → 16.9 | 1178 → 1144 |
| `Rom/CIReadRefCaps` | 25.1 → 25.3 G | 3.6 → 3.4 | 1034 → 1029 |
| `Rom/CIReadRefCV` | 7.5 → 7.5 G | 1.1 → 1.0 | 945 → 976 |
| `Rom/CIReadRefLayout` | 18.8 → 18.8 G | 3.2 → 2.9 | 1465 → 1500 |
| `Rom/CIReadRefs` | 6.8 → 6.8 G | 1.2 → 1.2 | 946 → 954 |

Lines: `CIReadRefW` +99 −241 (−142), users +22 −12; the generator +38 −5 and its test +30. The
gate build after the change rebuilt every `l_model` module and none changed (the option is off
by default).

### Batches 3–5: helpers, round 1

Three Opus helpers (brief `_tmp/mgen3/helper-brief.md`), one file group each, from master
3b4845e9; each branch merged with master, gated and submitted on its own. Module numbers are
instructions / user s (`measure.sh`, before → after), peak RSS 0.9–1.5 GB throughout.

**Batch 3, `mgen3-install`** (#243): 28 functions; 17 files, +576 −1362 (**−786**).
`IndInstallSpec/IcaW` (`block_caps_head/one/fin/at`, `er_put5`, `ind_info_rec`: 99.1 G / 21.2 s →
40.7 G / 7.0 s), `WhnfIotaRefine` (`is_ctor_app`, `const_ty_at`, `rule_rhs_at`, `pi_residual`
with its loop: 32.9 → 30.9 G), `DeclHeader`, `IndInstallSpec/BlockRawRec` (35.1 → 20.9 G),
`PartsShapeFacts`, `IndPartsSpec/Bsp` (`block_shape_large`; 17.2 → 28.7 G), `RecGenSpec/ClassFeR`
(53.3 → 61.6 G), `nest_holes_go` (21.2 → 8.3 G), `IndT/BlockPD` (23.4 → 9.9 G), `IndT/PosMc`,
`IndT/BlockWM`, `IndDeclConstsDeclared`. Bridges: `erPut5W_wrER`, `cfrRecW_some`,
`nhGoW_three`, `fieldCopyW_step`, `ctorsCopyW_step` (a generated loop ends in a continuation that
only passes the memory on), `resFromW_step`/`resContW_step`. Kept: `block_shape_fin/tail`
(their models feed `bbW` in `IndPartsProg5`, which sits below their callee specs), `rom_names_to`
(the `PINS` bounds check the refinement uses), `intern_reserved_pins` (a template),
`mentions_any_const`, `is_str_lit`, `find_rule` (structural `fun_induction` users elsewhere).
The lead removed `iirK5` (dead once `ind_info_rec` is generated) and the imports the generated
proofs no longer need (`shake`; `ClassFeR`'s `LdRd` allowlisted: `ld64_rd_spec` is named only
in the generated proofs).

**Batch 4, `mgen3-decl`** (#244): 24 functions; 15 files, +555 −1226 (**−671**).
`DeclAndPinIndCopy(2)` (4), `DeclCanonInfo`'s `canon_eq_list` (55.0 → 44.2 G), `DeclCanonConst`
(14.1 → 19.6 G), `DeclRec`, `WhnfIotaRefine6`, `DeclBasisSpec`, `LevelIntern` (+`lv_sub_int`;
`fold [lvG, lvA, lvB]`), `DeclReduceSpec`, `StubNamesRefine` (5; 21.2 → 27.5 G, the largest
relative slowdown of round 1). `erecPut_specW`'s size fact is a guard in the generated models
(extra `none` leaves), bridged by `dindCopyW_succ`, `ircW_kdc2`, `icgW_krc`, `dlpCopyW_succ`,
`erecCiW_some`; `pinAtW` moved from `DeclBasisSpec` to `DeclRec` (an import cycle). Kept:
`lp_lookup`/`lp_substl` (their models are generic over the key reader, shared with the
template `lvLookupTG`), `LevelEquiv` (walked structurally in `LevelEquivRel`, `LevelArena`,
`IndRealLvlT`), `ci_canon_*` (retried in round 2: the clash the helper met came from naming the
program binder `pr`; the generated spec needs `p`).

**Batch 5, `mgen3-consts`** (#245): about 30 functions; 21 files, +633 −1610 (**−977**).
`ConsBlockRecsTF` (`check_struct_proj_table_scoped` with its `CallM` parameter,
`rules_to_erec_go`, `rec_info_rec`: 75.4 → 68.2 G), `Front/IndApplySpec2` (the nine that lane
mgen rejected for 7.4 → 14.5 s, plus `install_ind_d`: now 39.4 → 38.0 G, i.e. no slower: the
generator's recipes improved since), the `IndDeclConsts*` files (Drop 27.2 → 8.7 G, Table 44.5 →
24.1 G, Formers 23.8 → 7.7 G, Ctors 16.4 → 7.0 G, Ref 130.2 → 125.2 G, …), `TblProg`,
`SumRules`, `TsrW`. Kept: `rule_copy`: its generated model copies the memory term after each of
its 11 `erec_put`s into both places that read it, about 2^11 copies (definition 4.3 s, arm 4.9 s);
a `let` for the memory in the generator would fix it.

Generator gaps the helpers met (none patched by them): `fold` takes no memory readers (`fold
[erRd]`: "unsupported term"; bridged by `rfl` lemmas); implicit binders do not become model
parameters; the memory-term blow-up above.

### Batch 6: `rci_rule` (lead)

`rci_rule`'s model generated with `pfuel` (the hand `ruleW` with its parts `ruleTailW`,
`ruleLvlW`, `rulePinW` and the 13-line hand spec at `maxHeartbeats 4000000` gone). The generated
model is one `ntBW` chain whose two `if`s on the fire word end in join points (`ruleW.j1` after
the level slice, `ruleW.j2` after the pin slice), where the hand model nested `ntBW (if … then
ruleLvlW … else some ([q], m)) fun r2 m2 => …`. The two walks in `CIReadRefRule` (`rule_relP`,
`rule_relL`) re-threaded: the `change` that named the hand tail now names the `if` and the join
point (`change (if (0 : Word) = 1 ∨ … then _ else ruleW.j1 p k … (putERs m1 [...])) = … at hw`),
`unfold ruleW.j1`/`ruleW.j2` take the place of `unfold ruleW.ruleTailW`/`ruleLvlW`, the
`rdU_ntBW`/`putE_ntBW` steps (a read inside a nested `ntBW`) became the flat `u64_some`/
`putE_some`. `rci_ci` stays hand-written for now: `ciPre` states the rest of the hand chain
(`ntBW (ciTailW …) …`) as its post for four kind lemmas; the generated `ciW` has that rest inline
in a join point's body, so `ciPre` needs restating first.

| module | instructions | user s | RSS MB |
|---|---|---|---|
| `Rom/CIReadRefW` | 90.3 → 70.1 G | 15.6 → 11.6 | 1199 → 1206 |
| `Rom/CIReadRefRule` | 43.0 → 43.1 G | 5.0 → 5.1 | 1119 → 1152 |

Lines: `CIReadRefW` +5 −51, `CIReadRefRule` +24 −19 (**−41**).

### Batch 7: `rci_ci` (lead); `CIReadRefW` all generated

`rci_ci`'s model generated (`pfuel`); gone: the hand `ciW` and its parts `ciTailW`, `ciDefnW`,
`ciCtorW`, `ciRecW`, the hand spec (`maxHeartbeats 4000000`), and with them the last users of
the `rdU` abbreviation and its lemmas `rdU_some`, `rdU_ntBW`, `putE_ntBW`. `ciSize` stays: it is
the refinements' table of record sizes by kind. The generated model reads the kind word and
dispatches on it to one join point `ciW.j1 … q k size m` (allocation, kind word, constant value,
then the kind's part inline). So `CIReadRefCI`'s common lemma split in two: `ciHead` (the kind
word read, the dispatch reduced against `ciSize`: one `by_cases` per kind) and `ciPre`, now over
the rest of the chain `K` as a parameter: its hypothesis is the join point's body up to the
constant value, `ntBW (erec_alloc) fun ρ₂ μ₂ => … ntBW (rci_cv …) (K ρ₂)`, and its post
`K rA r2 m2 = some (r, m')`. A kind lemma unfolds `ciW.j1` in `ciHead`'s result and passes it;
`K` is found by unification (a pattern: `K` applied to the bound `ρ₂`). The kind lemmas then
read their part as before, with `u64_some`/`putE_some` for the hand `rdU_ntBW`/`putE_ntBW`.

`rw [ite_eq_left h]` does not find a generated `if (k) = 0 then …` when `h : UInt64.ofNat kn =
0` is stated by hand (the literal's instance differs; seen before in batch 1's `split`);
`simp only [h, ↓reduceIte]` does.

| module | instructions | user s | RSS MB |
|---|---|---|---|
| `Rom/CIReadRefW` | 70.0 → 51.0 G | 11.6 → 8.2 | 1209 → 1364 |
| `Rom/CIReadRefCI` | 39.5 → 50.6 G | 4.9 → 6.6 | 1155 → 1127 |
| `Rom/CIReadRefCaps` | 25.2 → 25.1 G | 3.3 → 3.2 | 1080 → 1074 |

Lines: +102 −189 (**−87**). Over batches 2, 6 and 7 `CIReadRefW` went from 430 to 150 lines and
100.3 → 51.0 G; all 17 of its functions are generated.

### Batch 8: `Arena/LevelEquiv` (lead)

`lv_leq_top`, `lv_equiv`, `lv_equivs`, `lvl_eq`, `lvls_eq` generated (helper mgen3-decl had left
them: their models are walked in `LevelEquivRel`, `CoreLevels`, `IndRealLvlT`, outside its
files). The hand models already had the generator's shape: `evK₁ … evK₅` are
`equivW.k_lv_eq`, `k_lv_simp`, `k_lv_simp_2`, `k_lv_eq_2`, `k_lv_leq` (their captured words in
another order), `esK` is `equivsW.k_lv_equiv`, `lvlEqW` is the hand one exactly. So the walks
only renamed (`evK₁_zero` → `equivW.k_lv_eq.arm2 (hc1 := rfl)`, …); two differences needed a
step: `lv_equivs`' `some (if ln = k then 2 else 1, m)` is generated as an `if` of two `some`s,
and `lvls_eq`'s one `∨` guard as two guards (`lvlsEqW.abort1/2`). `ls_node` stays: its model
`lsNodeW` is a list (`r ≠ [] ∧ r = lsNodeW …`) the callers test against `[]`; the generated one
would be an `Option`.

| module | instructions | user s |
|---|---|---|
| `Arena/LevelEquiv` | 12.2 → 13.5 G | 2.9 → 3.2 |
| `Arena/LevelEquivRel` | 2.7 → 2.7 G | 0.6 → 0.6 |
| `Arena/CoreLevels` | 15.0 → 15.0 G | 3.5 → 3.5 |
| `Arena/IndRealLvlT` | 21.5 → 21.6 G | 3.2 → 3.3 |

Lines: +66 −237 (**−171**). `LevelEquiv` also holds the L code of these functions, so the change
rebuilt the program modules (`Checker/ProgI*`) once.

### Batch 9: generator `guards`; `node_bin`, `node_let`, `node_proj` (lead)

**Generator: `guards ["f", …]`** (test `tGd`). A table lookup's spec (`name_get`, `expr_get`,
`level_get`: `tblOK s₀.mem NID i = true ∧ r = [tblW s₀.mem NID i]`) was read as a list model
with its other conjunct ignored (the rule for `i < 51`), so a generated caller would lose the
check the refinements read the table with. For a callee listed in `guards`, those conjuncts are
guards of the model (as for a total memory model: `¬ g` is `none`), and a list literal gives its
elements (`tblW m NID i`, not `List.headD [tblW m NID i] 0`). Off by default: no existing model
changed (the gate build rebuilt every `l_model` module).

`Front/ApplyExpr`'s `node_bin`, `node_let`, `node_proj` generated with it (mgen's batch 4 had
rejected `ApplyExpr` for time). The generated models check the lookups one at a time where the
hand ones checked their conjunction (`if tblOK … ∧ tblOK … then … else none`), so the three
refinements' `split` became a `by_cases` on the conjunction and a `simp` through the generated
`if`s; `node_bin`'s three constructor calls join in `binW.k_mk_app` (one identity lemma,
`binW_k`). `nodeW`/`applyExprW` (hand) moved below the generated models they call. The other
`ApplyExpr` functions stay for now (`ls_put` is a fuel-free model over the input buffer `b`;
`node_lit`/`node_lit_str`/`node_const`/`expr_node`/`apply_expr` carry the buffer and pool
preconditions through their callees).

| module | instructions | user s |
|---|---|---|
| `L/ModelGenTest` | 85.0 → 86.1 G | 21.4 → 20.7 |
| `Front/ApplyExpr` | 33.3 → 33.8 G | 7.1 → 7.3 |
| `Front/ApplyExprRefine` | 11.3 → 11.4 G | 2.4 → 2.6 |
| `Front/FrontPreOK1` | 14.9 → 15.5 G | 2.7 → 2.6 |

Lines: `ApplyExpr` and users +74 −100; the generator +46 −13, its test +24.

### Batch 10: helper `mgen3-parts` (round 2)

36 functions; 30 files, +655 −2162 (**−1507**), #250. `DeclCanonInfo`'s `ci_canon_defn/rec/eq`
(the round-1 skip: the program binder must be `p`); `close_lams`, `class_rec_of`, `expr_get_d`;
`IhW` (4, one with `pfuel`; 91.6 → 77.7 G); `CrW`/`Classes` (`class_read_slots` with its
`_next`, `class_read_finish`, `class_read_rec_cls`; 126.3 → 103.4 G); `MnW` (66.3 → 41.3 G);
`Verdict/IndBRec4` (30.7 → 16.3 G); `BpcW`'s four `block_shape_pins_*` (`pfuel`; `Bf` 97.1 →
78.2 G); `BmoW`, `RecTW`'s `rec_target_of`, `BmgW` (38.9 → 20.0 G), `BlockRecNameSetOk`,
`SetEqW`, `BsoK2`, `Icp`, `TpsW`, `RpLook`. The slowest module after is `CrW` at 22 s (before
23 s); none got worse than 3×. Kept: functions whose models other helpers' files take apart
(`mentions_any_const`, `ptr_names_copy`, `class_gen_rule`, `erase_fvar_tys` and its family,
`ctors_have_name`, the `RulePrefixAt` family), `block_shape_fin/tail` and
`block_rec_name_set_ok` (callees at several fuels), pure specs with nothing to generate
(`class_read_n_slots`, `class_gen_minor_ci`), `rule_copy`. The lead fixed the imports `shake`
found (one allowlisted: `NestCtx` names `blockShapeLps_spec2` in a `vcgen` list only).

Generator observations from this round: a pure callee tested in an `if` elaborates its
`if … then 1 else 0` at `Nat` (arms carry `(1 : Nat)`); a pure post `r = [a, b, c, d]` is
inlined as `List.headD [a, b, c, d] 0` (batch 9's literal rule applies only under `guards`);
a continuation sometimes carries a model parameter it does not use; `EREC` loads are
`rdW (… tierA EREC …)` (`simp only [erRd_foldN]` bridges).

### Batch 11: `node_lit`, `expr_node` (lead)

`node_lit` generated with `pre [s₀.mem.arr8 IN = b ∧ pcap s₀.mem < 2 ^ 63 ∧ s₀.mem.top.toNat ≤
pcap s₀.mem]` and `keep [hE.no_st8]` (the hand proof's `Triple.keep` around `nat_dec`): the
generated model is the hand one (`litK` is `litW.k_nat_dec b`). `expr_node` generated over the
others' specs, with `guards ["level_get"]`: its model is the hand `nodeW` but for the sort
case's guard, now `¬ tblOK … = true` first. The hand `applyExpr_spec` proof goes through as it
was over the generated `exprNode_spec` (its precondition a side goal the `finish` closes).
Not generated: `node_lit_str` (`str_put_esc`'s post `r.headD 0 = s₀.mem.top ∧ strPutEscW … =
some (r.tail.headD 0, s'.mem)` is not a model shape), `node_const` (`ls_put`'s post is a list
and a memory model at once: "ambiguous post"), `ls_put` (fuel-free over `b`), `apply_expr`
(its model's `putK` is `Front/IdTable`'s, shared with the other `apply_*`).

| module | instructions (batch 9 → 11) | user s |
|---|---|---|
| `Front/ApplyExpr` | 33.8 → 37.7 G | 7.3 → 7.2 |
| `Front/ApplyExprRefine` | 11.4 → 11.5 G | 2.6 → 2.1 |
| `Front/FrontPreOK1` | 15.5 → 15.5 G | 2.6 → 2.3 |

Lines: +48 −87 (**−39**).

### Batch 12: helper `mgen3-misc` (round 2)

36 functions; 30 files, +515 −1547 (**−1032**). `canon_expr_eq` (`DeclCanonExpr` 115.2 → 29.2 G,
18.4 → 4.4 s), `DeclCanonLvl` (3; 58.9 → 38.6 G), `canon_rules_eq` (31.4 → 15.0 G),
`DeclCanonNames` (2), `PropReadW`'s nine `callW`-style models (`pfuel`, tuples; 84.5 → 58.9 G),
`IndRealOpf` (3, `pfuel`, the hand models by `rfl`), `IndRealNames` (4), `IndRealSpine` (4),
`has_fvar_fast`, `abstract1_fast`'s adapter, `bb_memo`, `fvar_b` (all `pfuel`), `cv_new`,
`struct_proj_bodies`, `InstLPSpec` (2; 48.2 → 36.1 G), `WhnfCoreProj` (2; 38.1 → 49.9 G),
`rom_lvls_go` (the first ROM reader: `pre`, `keep`, `defs`/`nodefs`). Bridges: `cvNewW_some`,
`spnPoolW_cons`, `slpW_cons_some`, `hffW_eq`, `recBytes_eq`. Kept: `sl_getd` (a total word
model used in 7 other files), `intern_zero`/`intern_ls` (templates), `ls_match` (its post is the
shape `ConsOK.match_` consumes), `has_loose_b_var_b_*` (unfolded by name in `NestCrest`),
`bvar_b` (its model's argument order differs from L's, used in 8 files), `head_type_const`/
`head_proof_const` (one hand model with a callee parameter, `cArmK1`), `type_sort_pw`/`proof_pw`
(they splice loop blocks whose hand models live in `PropReadLoops`; "not a call: step p …"),
`stk_push`/`stk_pool`/`rom_levels` (posts that are not model shapes; `rom_u64`'s `u64OK ∧ r =
[u64W …]`), `Front/Apply`'s lookups (templates) and `apply_*` (their users are elsewhere).
`PropReadW` keeps two imports the `shake` gate flags (allowlisted: `ld64_rdW_spec` named in the
`l_model`s' `extra` only; `KnotSlot` re-exported to two importers).

### Batch 13: helper `mgen3-pos` (round 2)

26 functions; 42 files, +685 −1603 (**−918**), #253. 41 modules 1 097 → 580 G instructions,
the largest single gain of the lane: `IndPosSpec/NcGoW` 389.2 → 24.0 G (37.4 → 3.5 s; the
hand spec's `sym … finish` over a long memo walk). Generated: `nest_container_ctors(_go)`,
`nest_container`, `NkcW` (3), `nest_cont_new_finish`, `nest_ds_closed(_go)`,
`nest_cont_params_closed`, `nest_ctx_root_holes_go`, `NestBlockOfKey` (3), `nest_hole_at`,
`nest_pos_hole_kind`, `nest_occ_any`, `nest_phs_go`, `nest_walk_stack` (its file `NbPosW`
emptied and deleted), `nest_seed_of_go`, `nest_seeds_fuel`, `block_nested_bit_go`,
`class_key_canon_go`, `NestKeyMap` (3). All with the default recipe (`fold`/`finish [tierW,
idxW]`). The largest increase: `NestGroupCtors` 13.1 → 24.3 G (it now holds `nt_spec'`). Two
workarounds: `attribute [local irreducible] findRes` around `nest_container`'s `l_model`
(`grind` unfolded it comparing record reads: a `whnf` timeout), and a binder renamed from `L`
to `hL` (the generated proof text roots every `L.x` as `_root_.L.x`, so a binder `L` breaks
it). Left: the RxMapW family (10, about 118 uses in `MapOKStep`), `depth_go` and its family,
`replace_apps(_go)`, `pi_doms_occ`, the models that live in files other helpers held
(`nest_occ(_go)`, `mentions_any_go`, `class_key_canon`, `target_canon_params`), the `CallM`
fuel-offset models (`nest_root_canon`, `nest_uniform_ok`, `nest_crest`), the total word model
`nest_field_kind_flat`. The lead removed four imports `shake` flagged and allowlisted six
(re-exports other modules reach names through, and names used only in tactic lists).

### Batch 14: helper `mgen3-parts2` (round 3)

18 functions; 18 files, +661 −1236 (**−575**). `block_counts_pure`/`_head`/`block_counts`
(`RecTW` 34 → 30 G), `block_rec_names_unreserved`, `block_rec_lps_one`/`_ok_go`/`_ok` (`EqW`
3.1 → 1.0 s), `class_n_pc_of` (`simp [] locals`; 100 → 76 G, and its hand spec's
`maxHeartbeats 1000000` gone), `ptr_list_names`, `ptr_names_copy` with `member_names_copy`,
`nest_out_kinds`, `target_abs_const` (43 → 25 G), `target_abs` (`pfuel`), `target_abs_go` with
`target_abs_node` (one mutual model). Bridges: `nameCopyW_step`, `ptrCopyW_eq` (the two copy
functions have the same code), `ptrNamesW_some`, `encONN_three`, `taGoW_leaf`, `taGoW_kNode`,
`taGoW_some` (what a returning step did; the frame lemmas use it instead of a `repeat' split`
that was 4× slower). The `IndIface` models this helper was given turned out to live elsewhere
(`lpsW` in `MemberNames`, `nIdxsW` in `RulePrefixAt`, `tmdW` in `PtrNamesWDec`, `psGoW` in
`StructElimLevel`) and to be unfolded by name in other files (`NestCtx`, `TcmLook`,
`TabSimSpg`, `CfaFv`, …): kept. `generated_rules`, `check_sum_tele`, `aux_rule_fire`,
`class_rules_ok`, `target_major_nfs` were already generated (their remaining hand lemmas are
refinements).

### Batch 15: helper `mgen3-pos2` (round 3)

11 functions; 25 files, +264 −522 (**−258**), #255. `nest_frame_mates(_go)`, `nest_phs`
(`pfuel`), `nest_ctx_root_holes` (fuel-indexed; `rhW k` is now `rhWf (k + 1)`), `nest_ctor_nf`
(`pfuel`), `depth`, `replace_apps`, `nest_occ` (`pfuel`, each with a 2-line triple wrapper for a
`DpGoSpec`-style definition, which `vcgen` does not unfold), `pi_doms_occ`,
`has_loose_b_var_b_ins` (bridge `hbInsW_eq` to the `msetG` form), `has_loose_b_var_b_fast`.
No module more than 1.7× slower (`NcnW` 0.36 → 0.60 s); `MatesW` 13.3 → 8.2 G.

## 4. Totals (master b91d1604 → a0b2b92d)

* **Functions**: hand-specified (§1's count) 591 → 340; named by an `l_model` 765 → 1 002. About
  250 functions converted: lead 52 (batches 1, 2, 6–9, 11), helpers 199 (round 1: 82, round 2:
  98, round 3: 29).
* **Lines** (`git diff --shortstat b91d1604b master -- ConAgua`): 204 files, +5 205 −12 601,
  **−7 396** net, the generator's two options and their tests included.
* **Build time**, every module the lane changed, measured alone (`LEAN_NUM_THREADS=1`,
  `measure.sh`) at both ends: 204 modules, **5 329 → 4 213 G instructions (−21 %)**, 835 →
  665 user s. The slowest module after is `Verdict/UnresolvedE`, 18 s. Above 3×: only `RecCheckSpec/RpLook` (2.2 → 6.8 G, 0.4 → 1.2 s: the generated spec
  now lives there; the modules the hand specs left shrank by more). The largest slowdowns in
  absolute terms: `Front/IndApplySpec` 34 → 53 G, `Rom/CIReadRefCI` 40 → 51 G, `WhnfCoreProj`
  38 → 50 G, `IndPartsSpec/Bsp` 17 → 29 G, `NestGroupCtors` 13 → 22 G; the largest gains:
  `IndPosSpec/NcGoW` 389 → 24 G, `DeclCanonExpr` 115 → 29 G, `IndInstallSpec/IcaW` 99 → 41 G,
  `Rom/CIReadRefW` 100 → 51 G. Peak RSS 0.8–1.6 GB throughout.
* **Generator**: `pfuel` (batch 2), `guards` (batch 9), both off by default; no existing model
  changed.

## 5. What stays hand-written, and why

By kind, with the main examples (the per-batch sections name the rest):

* **No model to generate** (≈ 196 of the 340): specs whose post is a value, a relation or a
  list the callers test (`ls_match`, `lsNodeW`, `class_read_n_slots`, `sl_getd`'s total word
  model, `nest_field_kind_flat`).
* **Templates** (`FunDecl`s with parameters: the table lookups, `intern_zero`, `intern_ls`,
  `intern_reserved_pins`, `pb_check`): generic hand specs; the generator takes no parameters.
* **Shape**:
  * memo walks whose hand models fold *find + put* into `msetG` and merge kinds
    (`replace_fvars` and the RxMapW family, `depth_go`, `mentions_any_go`,
    `has_loose_b_var_b_go`, `replace_apps_go`; ~800 lines of `MapOKStep` on that shape);
  * models shared by several functions or with a callee/`CallM` parameter (`stripTW tg` for
    `strip_lams`/`strip_pis`, `cArmK1`, `selW`, `lookupW`/`substLW` shared with a template,
    `nameCopyW`-style sharing where users are elsewhere);
  * fuel offsets: models stated at `k + 2`, `k + 3` with callees at several fuels
    (`block_shape_fin/tail`, `block_rec_name_set_ok`, `nest_root_canon`, `nest_uniform_ok`,
    `nest_crest`), and callers of `pfuel` models at the same fuel (`whnf_walk_fuel`,
    `nest_canon_crest`: a `pfuel` spec is at `exec p (n + 1)`);
  * callee posts that are no model shape: `str_put_esc` (`r.headD 0 = top ∧ F = some (r.tail
    …)`), `ls_put` (a list and a memory model at once), `rom_u64` (`u64OK ∧ r = [u64W …]`),
    `stk_pool`, `rom_put`;
  * loop blocks whose hand models live elsewhere (`type_sort_pw`, `proof_pw`: "not a call:
    step p …");
  * fuel-free models over the input buffer used as total functions (`Front/`: `ls_put`,
    `nat_dec`, `Unescape`, `Line`; zero ronsync2 churn).
* **Reach**: models unfolded by name in many files (`lpsW`, `nIdxsW`, `tmdW`, `psGoW`,
  `bvbW`, `chnW`, `ruK1/2`, the `erase_fvar_tys` family's continuations, `getDW`).
* **Bounds**: `rom_names_to` (the `PINS` check the refinement uses).
* **Memory blow-up**: `rule_copy`, whose generated model copies the memory term after each of
  its 11 `erec_put`s (a total memory callee is inlined, not bound); a continuation per total
  memory call (opt-in) would fix it.

Generator gaps the lane met and left: `fold` takes no memory readers (bridged by `rfl` lemmas:
`erRd_foldN`, `prd_rdW`); implicit binders are no model parameters; a binder named `L` breaks
the generated proof text (every `L.x` is rooted); generated literals and `Decidable` instances
differ from hand-stated ones, so `rw [ite_eq_left h]`/`split` can fail where `simp only [h,
↓reduceIte]` works; a pure callee tested in an `if` elaborates at `Nat`.
