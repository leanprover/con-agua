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
