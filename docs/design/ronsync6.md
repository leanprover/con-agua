# Lane ronsync6: the con-ron sync 42a08640 → 8b088905

Lane of 2026-11-16 (Opus), from master `1b5dce12c`. con-ron `42a08640 → 8b088905`, con-leche
`6810492c → 600d3b58`, upstream tasks #155 (#582 a `Nat.succ` major goes to whnf; #579 the literal
flags as fields of the index), #156 (#583 the β peel from the spine range; #585 the ι step peels
the stored rule's λs, `ruleBinds`: a new rejection, `stored_rule_lams_short`), #157 (#591 the ι
step looks each record up once, `MajorView`; #592 the constructor shortcut, `defeqLazy`).
Standing decisions: no new driver/CLI option; generated models and declarative refinements for
every new or rewritten function (exception: limb arithmetic); `EREC` offsets stable.

## 0. Stage 0: footprint and stage plan

`scripts/bump-con-ron.sh --report origin/master` (`_tmp/bump-8b088905/report.{txt,md,json}`), then
ronsync4's classifier (`_tmp/ronsync6/fp.py`, outside the repository).

**Upstream.** con-ron definitions: 47 changed, 38 new, 12 removed; types `IFEnv` (`natLit`,
`strLit`), `IFBase` (`lits`), `IStreamIndex` (`natFrom`, `strFrom`), `Caches` (`ruleRhsC` →
`ruleBodyC`), `MajorView` (new). con-leche: 43 changed, 31 new, 10 removed. `pins/` did not move.
Patches: con-leche/0002 and con-ron/0002 conflict (`DiscC3`, `Checker/Base`, `Arms/WhnfCore`).

**L items** to re-check: **94** in 18 files (89 citations changed, 7 gone, 33 through a changed
helper): `InstList` 13 (+`InstListSpec` 1), `WhnfM2C` 12, `DefEq` 9, `WhnfIotaRec` 9,
`WhnfDelta` 9, `Infer` 7, `RecGen` 7, `WhnfIota` 6, `WhnfCore` 5, `DeclArms*` 5, `Env` 3,
`CheckerL` 2, `IndStream` 2, `IndInstall` 2, `StrLit` 1, `WhnfCoreApp` 1. 127 changed twin
definitions nothing cites (55 new): the new ones to port are `isNatSuccApp`, `prepareMajorWhnf`,
the literal-flag kit (`litFrom`, `fromLe`, `litNameAt`, `litsStored`, `natLitStoredBy`,
`strLitStoredBy`, `setFlags`, `IStreamIndex.freeze`, `natLitNames`/`strLitNames`),
`instantiateRevRange`, `lamBody`, `ruleBodyAt`, `iotaVals`, `ruleBinds`,
`MajorView`/`ctorView`/`majorToCtorRescue`, `whnfAppIota`, `ctorTarget`/`ctorTargetFor`/
`ctorHeadAgainst`, `defeqLazy`.

**Proof declarations** (the report's mentions plus the mentioners of `IStreamIndex`, `IFBase`,
`Caches`, `SameView`, `IndexDenotes`; `IFEnv`'s 2 041 type-only mentioners left out: only 10
sites in 5 files build an `IFEnv` positionally or with `with`): **630 in 203 files, 466
theorems**.

| form (theorems) | count | lines |
|---|---:|---:|
| call-by-call walks (`callW`) | 88 | 9 538 |
| model-arm walks | 15 | 530 |
| declarative, ≤ 12 lines | 6 | 85 |
| declarative, longer | 12 | 558 |
| manual, > 12 lines | 124 | 8 253 |
| manual, ≤ 12 lines | 221 | 1 839 |

Hand specs in the footprint: 11 (`env_push`, `env_pop_temp`, `env_push_table`, `nat_succ_lit`,
`m2c_const_view`, `intern_lit`, `head_and_args`, …); those of rewritten functions become
generated models.

**Final statements**: none of `Final/*`, `Audit/*` names a changed signature (they use
`buildIndex`, `checkJobList`, `internAllPins`, whose signatures did not change). The test harness
`E2E/Diff.lean` uses the removed `mkIFEnv` (now `mkIFEnvLits`, an `AM` action).

**The ROM**: not touched (the literal names are pin handles; the constructor record and the caps
did not change). The ROM relations stay where they are.

**Kind of sync**: an L-code sync (about 20 new twin functions ported, about 45 rewritten) plus
one type change (the index's flags and names), handled by the interface. Ladder estimate: low
yield (5–15 % of the failing theorems, the rename rules); otherwise the compile-pass tool.

## 1. Stage 3a: the interface

* **The literal flags and names** (`Arena/Tiers.lean`, `EnvR`): `CTL[160]` is `fe.natLit`,
  `CTL[161]` `fe.strLit` (`≠ 0`), `CTL[162‥171]` the frozen index's literal names
  (`fe.base.lits`, `strLitNames`' order; `litWords`), all in `envCtl`. One copy of the flags for the
  job, as con-ron's in-place index: a temporary push that recomputes them is followed by its pops
  and `IFEnv.setFlags` (the L function writes the saved words back). Frame hypotheses that freed
  every `CTL` word from 136 or 137 up now leave out `160‥171` (`not_mem_envCtl`,
  `CheckR.frame_hi`, `CoreS.frameSM*`, `CoreS.frameM`, `quotPc`).
* `EnvR.congrF` (the flags read off the new memory), `EnvR.setFlags`, `IFEnv.setFlags_self`;
  `pushRows` (the push's flag-keeping branch; `IFEnv.push_eq`: the push is `pushRows` and, at a
  literal name before strings are expandable, the recomputation as two `setFlags`);
  `EnvR.push` is now about `pushRows`.
* **The frozen index** (`Arena/IndexRel.lean`, `FrozenR`): the names `CTL[162‥171]`, the
  thresholds `natFrom`/`strFrom` as `CTL[172]`, `CTL[173]` (`optW`: `0` none, `k + 1` some `k`).
  `EnvR.ofIndex` takes `FrozenR` and the flags `fromLe` of the thresholds at the record's counter.
* **The major's view** (`Arena/MajorViewDec.lean`, `decMV`, `MVOk`): five words `[t, e, c, us,
  q]`, `q` the constructor's record in `EREC` (by address: records are immutable; the twin copies
  the `IConstantVal`, con-leche shares it).
* **Renames**: `ruleRhs*`/`RuleRhs*`/`rule_rhs*` → `ruleBody*` (as upstream), over the whole
  tree and as rules in `scripts/sync-rules/ronsync6.txt`.
* **Statements restated** (3b, so that the tree elaborates): `IotaRecAtOK` at the caller's
  record (`c`, `us`, `q` and the redex's `mI + 1` arguments), `MajorToCtorOK` (the view),
  `RuleBodyAtOK` (`k`), `betaPeel_refines` (the range start `s`), the gates' environment after
  `setFlags` (`DeclKindEnvOne`); deleted: the theorems of `natLitStored`, `strLitStored`
  (`StrLitStoredOK`, `SupKeep`, `vmono_*`), `peelFull_ref` (the old peel's walk).

## 2. Progress log

* 16:37 start; 16:39 report; 16:45 stage 0 sent.
* 16:40 bump (`0af7f88b2`): three conflicts resolved (DiscC3: upstream's `ruleBodyAtM_spec` with
  our `finish [Expr.WScoped.of_not_hasFvar]`; `Checker/Base`: the shorter guard chain with our
  `try replace`; `Arms/WhnfCore`: `iotaTarget_spec` deleted upstream). ConLeche, ConRonArena,
  ConRonBridge build.
* 16:45–17:00 stage 3a and the compile passes (build, ladder on the failing modules, hand fixes
  of definitions and statements).
* 17:00 fan-out: helpers `ronsync6-lit` (#579), `ronsync6-iota` (#582, #583, #585 ι side, #591),
  `ronsync6-rec` (#592, #585 `ruleBinds`, the inductive tier's flags); briefs
  `_tmp/ronsync6/brief-{common,lit,iota,rec}.md`, 3 build threads each.
* 17:05–17:40 the helpers' "elaborate first" milestones merged (statements restated, the removed
  functions' theorems deleted). The new reason `R_THE_RECURSOR_S_RULE_FOR_IS_NOT` (`ruleBinds`,
  appended row). The interface grew by the helpers' requests: `envPush_refines` over generated
  models (`Arena/EnvFlags.lean`, `flagsSet`, `envSetFlags_refines`), `StageR.of_flags`
  (`Arena/StageFlags.lean`), `IndexR.rows` (the base rows' counters below `2^32`, for `lit_from`).
  More frame hypotheses that freed every `CTL` word from 136 up now leave out `160‥171`.
* 17:40 the program regenerated (`Checker/Prog*`, the function lists, `preloop_ws`, `checker.s`).
  `diff-e2e --tests` at con-leche 600d3b58 with that binary: **740/740 agree**
  (`stored_rule_lams_short` rejected with the new reason, `strict_succ_counter` accepted).
  `Init` instructions (one run each, CPU 44, `--jobs=1`): master 217 223 M, branch 202 873 M
  (**−6.6 %**; upstream measured −0.18 %, −4.17 %, −3.91 % for the three tasks on con-ron).
* 17:50–18:30 helper `ronsync6-lit` ran out of context (hand-over `_tmp/ronsync6/ronsync6-lit-handoff.md`);
  `ronsync6-lit2` continues. One layout decision on the way: `str_lit_names` writes the ten
  literal names into `CTL[162‥171]` before the stream index is built rather than in the freeze:
  in the twin's proofs the builder's environment already holds them (`driverFE`, as
  `mkIFEnvLits` for the spec fold), and the pins do not change during the build, so the freeze
  reads the same names; `index_freeze` keeps only the two thresholds (`litFrom`). `pin_at`
  cannot abort there (the pin table is filled before the build), so the order is not observable:
  no deviation row.
* 18:30–18:45 `ronsync6-iota` finished (all but `appLoop_ref`; hand-over), `ronsync6-iota2` proved
  `appLoop_ref` (and the missing `whnf_app_iota` refinement, `appIota_ref`), `ronsync6-rec` and
  `ronsync6-lit2` finished. 18:45 the program regenerated once more; **the whole library builds,
  zero `sorry`**.
* 18:48–19:10 gates: OVERVIEW's links at the new revisions (three anchors moved:
  `foldlM_checkDecl_envWF`, `lvlEq?`, `buildStage_checker`), the new warnings fixed (deprecated
  names, an unused section variable), the unused imports `lake shake` found dropped (the shake
  tool itself had to be rebuilt: its glibc had been collected from the Nix store), two census
  links to `mkIFEnvLits` (no census target) dropped. `gates.sh`: 15 OK.

## 3. What was mirrored (by upstream item)

| upstream | L |
|---|---|
| #579 the literal flags as index fields | `CTL[160]`/`CTL[161]` (flags), `CTL[162‥171]` (names), `CTL[172‥173]` (thresholds); new `str_lit_names`, `lit_from`, `index_freeze`, `from_le`, `lit_name_at`, `lits_stored`, `env_set_flags`; `env_push` recomputes at a literal name while `strLit` is false; `record_job` sets the flags by `from_le`; the three pin gates, `gen_rec_check` and `check_block_tail_stream` set the flags back after their pops; every reader reads the word; `nat_lit_stored`, `str_lit_stored` gone |
| #582 a `Nat.succ` major goes to whnf | `is_nat_succ_app`, `prepare_major_whnf` |
| #583 the β peel from the spine range | `beta_peel(t, s, ao, an, i)` substitutes the stack slice `args[s:i]` in place (no copy); `inst_list`'s walks restated over the twin's range (`vs n k`) |
| #585 the ι step peels the rule's λs | `lam_body`, `rule_body_at(…, k, us)` (the memo renamed `ruleBody*`), `eidx_copy_upto` (`iotaVals`), one `inst_list` for the reduct; `rule_binds` and `stream_rules_check(…, rP, …)`: the new rejection (reason `R_THE_RECURSOR_S_RULE_FOR_IS_NOT`) |
| #591 one lookup per ι step | the view `[t, e, c, us, q]` (`decMV`), `ctor_view`, `major_to_ctor_rescue`, `major_to_ctor`/`prepare_major(_whnf)` answer the view; `iota_rec_at(mode, vis, d, c, us, q, so, sn)` at the caller's record and exactly `mI + 1` arguments (con-ron's deviation (1)); `whnf_app_iota`, `whnf_stuck` do the lookup; `iota_target`, `is_ctor_app`, `iota_rec_c`, `iota_rec_head` gone |
| #592 the constructor shortcut | `ctor_target`, `ctor_target_for`, `ctor_head_against`, `defeq_lazy` (the old body past the shortcut), `defeq_body`; `is_bool_true`, `bool_true_shortcut` gone |

con-ron's "Deviations kept" mirrored: #156's empty-range walk (the entry walks it, the memo
cleared alike: L's `inst_list` at a zero-length slice); #157's (1) exactly `mI + 1` arguments,
(2) the rescue answers a term and the view is made at the end, (3) the record by reference in L
(con-ron copies it). Every new function has a generated model (`l_model`); no new hand `…W`
model. New aborts: the `rP + nfields` word overflow (`rule_binds`, `iota_rec_fire2`) and the
stack bounds: fixed capacities, no deviation row. **Deviation rows added: none.**

## 4. The ladder's yield against the estimate

Estimate (stage 0): low, 5–15 %, an L-code sync. Measured: the lead's compile passes ran the
ladder 11 times on 58 failing-theorem instances (with repeats across passes) and **closed none**
at any rung (master, codemod, vocab); the `ruleRhs` → `ruleBody` rename went over the whole tree
before the first build, so it never failed. As in ronsync3/4 the ladder was the compile-pass
tool: it turned failing proofs into `sorry` tickets so the modules behind them elaborate. What it
cannot do — statements and definitions that no longer elaborate (removed twin functions, changed
signatures) — the lead and then each helper restated by hand ("elaborate first" milestones).

## 5. Statement changes

None in `Final/*`, `Audit/*` (their text and the twin signatures they name are unchanged). The
test harness `E2E/Diff.lean` builds its empty environment with `mkIFEnvLits` (the removed
`mkIFEnv`'s replacement). Internal statements restated: listed in §1 and in the helpers' reports
(e.g. `IotaRecAtOK`, `MajorToCtorOK`, `RuleBodyAtOK`, `betaPeel_refines'`, `envPush_refines`,
`buildIndex_refines` with `FrozenR`, `JobM.frozen`, `AppG.nv`, `CoreCallees.instRange`).

## 6. Checks

* `gates.sh`: 15 OK. `provenance.py check --strict`: every citation exact at con-ron 8b088905,
  con-leche 600d3b58, no marker left (94 L items re-checked). `bump-con-ron.sh --check` ok.
  `asm_file.py --check`: `checker.s`, `pins.bin` up to date (`pins/` did not move: `pins.bin`
  unchanged).
* `diff-e2e --tests` at con-leche 600d3b58 with `--refs` (con-ron 8b088905 built in
  `_tmp/ref/con-ron-8b08`, e2e-ref): **740/740 agree**, UNSOUND/INCOMPLETE/CRASH/TIMEOUT/REFDIFF 0;
  7 skipped (`--max-nat-size` fixtures, D49). `stored_rule_lams_short` rejected (the new reason),
  `strict_succ_counter` accepted.
* `e2e.py --latest ''` with that con-ron: 794 fixtures, all agree (2 time out in all three, as
  before).
* Census: 100 %, zero `sorry` sources (the 2 bad links of `topLitS` were there before).

## 7. Performance

Against master `1b5dce12c`, both binaries `make` from the committed files, `Init`
(`_tmp/fixtures/init/init435.ndjson`), CPU 44 (one thread) or 24–39 (`--jobs=16`).

| | master | ronsync6 | Δ |
|---|---:|---:|---:|
| `Init`, `instructions:u`, one thread (`perf stat`, 2 runs each, ±0.00 %) | 217 223 M | 202 881 M | **−6.60 %** |
| `Init`, peak RSS, one thread | 621 MB | 627 MB | +1.0 % |
| `Init`, peak RSS, `--jobs=16` | 764 MB | 764 MB | 0 % |
| `Init` wall, one thread (22 kept paired rounds of 24, load ≤ 12, Wilcoxon) | 16.85 s | 14.74 s | mean −12.1 % [−12.9, −11.3], p < 0.001 |
| `Init` wall, `--jobs=16` (same rounds) | 2.84 s | 2.74 s | mean −7.1 % [−19.0, +4.8], p = 0.006 |

Upstream measured −0.18 % (#155), −4.17 % (#156), −3.91 % (#157) on con-ron's binary: together
about −8.1 %; L's −6.6 % instructions are in that range. The wall time drops more than the
instruction count (one thread −12 %): the β peel no longer copies the arguments onto the stack
and the ι step substitutes once, which saves memory traffic beyond instructions. The literal
flags (#579) make each literal read one word load instead of up to ten index probes. No regression
in instructions, memory or wall time.

## 8. What went wrong

* The first lit helper ran out of context after most of #579 (the L code, `EnvFlags`, the freeze);
  a second one finished it from the hand-over (IndexBuild, Jobs, the gates' flag step). The iota
  helper likewise left `appLoop_ref` to a fresh helper. Hand-overs worked; earlier splits of the
  #579 area (the env/index half and the readers half) would have avoided one restart.
* Merging during the helpers' fast commits: twice a helper reported failures against an older
  head of another helper (iota's elaborating head had not been merged yet). Merging every helper
  branch at each announcement, as later done, fixed it.
* The frame hypotheses that freed "every `CTL` word from 136 up" had to be narrowed in about ten
  places (`not_mem_envCtl`, `CheckR.frame_hi`, `CoreS.frame*`, `quotPc`, `hCenv`): any new word an
  existing relation owns meets them; the free range `160‥173` kept the change to those lemmas.
* The shake tool's binary had lost its interpreter (glibc collected from the Nix store), so the
  `shake` gate reported every allowlist line as stale until `scripts/shake-setup.sh` rebuilt it.
