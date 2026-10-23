# Lane `e2efix`: the remaining e2e bugs (B1, B3) and a fast `scripts/e2e.py`

Journal of lane `e2efix` (decisions, measurements, findings, open ends). Only this lane edits this
file. Starting point: lane `stubs`' e2e run (`docs/design/stubs.md`, "e2e with no stubs").

## B1: `lv_node` abort #2 in ι-reduction of a nested inductive's recursor

(Found and fixed here; lane indproofs3-rec found the same bug at the same time and landed the same
fix first, `5093af56`, with the copies in fresh locals `elo, ell, epo, epl`. The merge takes
master's version; the analysis below stands, and the e2e numbers below are on master's fix.)

**Cause: an `IW` slice stored in an `EREC` record.** The twin's `tgtStoredRules`
(`Inductives/RecCheck.lean:498-509`) gives every rule of a recursor at an OUTSIDE major the fire
`auxRuleFire M rP = .nested lvls pins`. In L, `aux_rule_fire` returns the two lists as `IW`
slices (`view_ls` copies the level list's pool slice into `IW`; `abstract_prefix_list` builds the
pins with `sl_cons`, in `IW`; its refinement `auxRuleFire_refines` says so: `decHL`, the `IW`
decoder), and `tgt_stored_rules_remap` wrote those offsets into the 11-word rule records as they
were. Every reader of a rule record takes words 4‥7 as `EREC` slices (`decRule`; `rec_fire_levels`
→ `sle_go` reads `EREC[fvo + j]` as level handles; `erec_push` copies the pins from `EREC`;
`promote_fire` promotes `EREC` slices). So ι-reduction of such a recursor read whatever `EREC`
words sat at the `IW` offset as levels: `lv_node` abort #2 (`CTL[8 + t] <= i`, not a live level).
`IW` is scratch besides, so even the right array would have been overwritten later.

Not an L-vs-twin discrepancy in the twin's own data (the twin's rule holds the lists as values),
but in L's representation: the producer's convention (`IW`) and the record's (`EREC`) did not
meet, and `tgt_stored_rules` had no spec that would have caught it (nothing proved about it yet;
`auxRuleFire_refines` and the readers' specs are each right on their own).

**Fix** (`ConAgua/Arena/RecCheck.lean`): `tgt_stored_rules` copies both slices into fresh `EREC`
words once (`er_from_iw`, `IndSum.lean`), shared by every rule of the recursor, as the twin shares
the one `f`. `er_from_iw` added to `recCheckForeign` (the module's closure check). No proven
theorem mentions `tgt_stored_rules`/`tgt_stored_rules_remap`, so nothing breaks; whoever proves
`tgtStoredRules` states the remap's slices through `decRule` (`EREC`).

Reproducers `nested_rec`, `nested_struct_proj`, `inmodel_nested` (`check_np`), `nest_rose_tree`,
`inmodel_groups` (both entries): all five `agree-accept` in both entries after the fix
(`scripts/e2e.py --only 'nested_rec|nest_rose_tree|inmodel_groups|nested_struct_proj|inmodel_nested'`).

## Aborts where the reference rejects: sound, and the twin's error paths

**Soundness.** `PipelineRefines p` (`ConAgua/Final/Statement.lean`) claims something only of a run
`L.run p N "check" [] … = .ok (rs, m')` with `rs.headD 0 = ACCEPT`; an `abort` is an `.error`
outcome of `L.run`, and `checker_x64_accepts` closes that case: `compile_correct`'s `OutcomeRel`
for an error outcome forces `rdx ≠ 0`, so the conclusion `rdx = 0 → rax = ACCEPT → TwinAccepts [b]`
holds vacuously (the `rcases e with _ | _ | _ | _ <;> simp_all [OutcomeRel]` arm). Abort, fuel
exhaustion and capacity errors all read as "not accepted". Nothing to change.

**Where the aborts are.** The 262 (`check`) / 278 (`check_np`) `agree-reject (L aborts)` rows of
lane `stubs`' run (traced then, all of them) sit at about 70 distinct `abort` sites. The 23 most
frequent sites, about 200 of the rows (counts below from the run's `check_np` table where it has
the site), and the one twin `error` were checked by
hand against the cited twin code (L function → k-th `abort` in pre-order → twin line): **all 23 are
the twin's own error exit**, the convention "every twin error becomes `abort`":

| site | fixtures | L | twin | twin's error |
|---|---:|---|---|---|
| `check_value_group` #1 | 27 | `Arena/DeclStep.lean:292` | `CheckerSplit.lean:111-112` | `isDefEqCore` false: "type mismatch" |
| `check_div_mod_pin_loop` #0 | 22 | `Arena/DeclArmsNat.lean:1145` | `DeclCheck.lean:615-616` | no pin variant left: `notImplemented` (decline; D4/D5) |
| `nest_uniform` #0 | 19 | `Arena/IndPos2.lean:788` | `Inductives/Positivity.lean:1166` | invalid occurrence |
| `install_header` #7 | 18 | `Arena/DeclStep.lean:129` | `CheckerSplit.lean:78-79` | unresolved constants (invalid or decline) |
| `infer_spine_arg` #0 | 16 | `Arena/Infer.lean:279` | `Core.lean:2635-2647` | application type mismatch |
| `vi_rec` #1 | 12 | `Front/IndApply.lean:377` | `Frontend/ExportC.lean:353-355` | `numMotives ≠ nTypes` (frontend verdict) |
| `nest_pos_bind` #0 | 9 | `Arena/IndPos2.lean:656` | `Inductives/Positivity.lean:1063-1064` | non-positive occurrence |
| `check_decl_axiom` #5 | 9 | `Arena/DeclArms.lean:457` | `CheckDecl.lean:184` | non-standard axiom (decline) |
| `class_fields_of_go` #0 | 7 | `Arena/RecGen.lean:118` | `Inductives/GenRec.lean:359-361` | IHs not the recursive fields |
| `infer_proj` #3 | 7 | `Arena/Infer.lean:452` | `Core.lean:2729-2733` | `findProj?` none (`projMissError`) |
| `vi_ctor` #3 | 6 | `Front/IndApply.lean:299` | `Frontend/ExportC.lean:327-330` | field count |
| `class_rec_ty_ok` #1 | 5 | `Arena/RecGen.lean:404` | `Inductives/GenRec.lean:545-547` | generated recursor type differs |
| `nest_cont_checks` #0 | 5 | `Arena/IndPos2.lean:557` | `Inductives/Positivity.lean:1016` | index mentions a member |
| `vi_rec` #3 | 5 | `Front/IndApply.lean:379` | `Frontend/ExportC.lean:358-362` | wrong `k` |
| `infer_proj_at` #3 | 5 | `Arena/Infer.lean:429` | `Core.lean:2724-2726` | Prop structure, non-Prop field |
| `target_rec_pins` #2 | 4 | `Arena/RecCheck.lean:561` | `Inductives/RecCheck.lean:375-377` | recursor names not the generated ones |
| `install_header` #1 | 4 | `Arena/DeclStep.lean:116` | `CheckerSplit.lean:65-66` | reserved basis name |
| `infer_let` #0 | 4 | `Arena/Infer.lean:467` | `Core.lean:2794-2795` | let value type mismatch |
| `ensure_sort` #0 | 4 | `Arena/Infer.lean:42` | `Core.lean:2441-2446` | expected a sort |
| `install_value_guards` #3 | 4 | `Arena/DeclStep.lean:145` | `CheckerSplit.lean:92-93` | unresolved constants (decline) |
| `target_major_of_outside` #4 | 3 | `Arena/RecCheck.lean:392` | `Inductives/RecCheck.lean:320-324` | outside inductive, no auxiliary type |
| `install_decl_step` #0 | 3 | `Arena/Checker.lean:598` | `Checker.lean:234-235` | non-standard `And` |
| `expr_get` #1 | 1 | `Front/IdTable.lean:102` | `Frontend/ExportC.lean:132` | undefined expr index (twin `error`) |

(twin paths under `vendor/con-ron/ConRon/Arena/`, L paths under `ConAgua/`.) None is a capacity
or fuel check, none an L abort where the twin continues; the only `docs/deviations.md` rows naming
these functions are D4/D5 (`check_div_mod_pin_loop`: the decline is the twin's at one pin variant)
and D18 (`class_fields_of_go`, performance). The reference's stage agrees as well (`line` for the
`vi_*` sites, `decl` for the rest). The rest (about 50 sites, mostly 1–2 fixtures each) is not
checked one by one. So these aborts are agreements,
not uncovered error handling. (The error design itself, aborting instead of returning the twin's
error kind, is unchanged; reject vs decline is not distinguished by `check`'s result.)

## B3: the untraced errors and the timeouts: capacity and harness, no L bug

After B1, `check` had 4 `l-error`s and 2 `l-timeout`s (`check_np` 2 and 2), and 1 `ref-memout`:

| fixture | entries | class before | what it is |
|---|---|---|---|
| `natop_order`, `natop_before_ble` | `check` | l-error, `hoist_ok` #0 | B2, lane front3 (the ground hoist), not touched here |
| `eager_open_nat_control` (67 KB) | both | l-error, untraced (tracer > 400 s) | **capacity**: `AREC` (array 4, the application records) full; accepts at `CA_WORDS = 2^27` (5.8 s, 5.3 GB), not at `2^25`; ~10.2 M application nodes (40.8 M words); con-ron accepts in 2 s |
| `arena/good/perf/app-lam` (1.2 MB) | both | l-error, untraced (> `TRACE_MAX_BYTES`) | **capacity**, the same: `AREC` full at `2^26`, accepts at `2^27` (18.6 s, 5.4 GB) |
| `whnf_core_loop`, `whnf_delta_loop` | both | l-timeout | **harness**: con-leche expects these to time out (expected exit 124); `e2e-ref` and con-ron time out too. Now `agree-timeout` |
| `stack_fuel_offset` | both | ref-memout | **harness, reference side**: con-leche expects exit 134 (the ~3M-deep recursion, PLAN "Things to settle early"); L errors, the reference runs out of memory |

Found with a new opt-in diagnostic of `harness/e2e.c`: `CA_HWM=N` prints, per word array, the
highest touched page and the number of touched words (`mincore`) for arrays above `N` words. A
bump-allocated array whose touched words equal its capacity is the one that ran out (hash-slot
arrays such as `ASLOT`, `LASLOT`, `ILMEMO` are touched all over at any load and say nothing).

`scripts/e2e.py` now retries once more at `HUGE_WORDS = 2^27` words per array when the `2^25` retry
still errors **and the reference accepts** (two fixtures today; each such run ~5.4 GB, under
`PER_RUN_GB`), so the capacity cases show as `agree-accept` with the capacity note, not as
`l-error`. Whether 10 M application nodes for a 67 KB file is the twin's own count (the twin
interns the same nodes, no GC; con-ron's run is 2 s) or an L-only excess was not measured: an
item for whoever owns the store capacities (a node count from `e2e-ref` would settle it).

## A fast `scripts/e2e.py`

Lane `stubs`' full run took 9756 s (162 min, `--jobs 12`): the tracing interpreter (`e2e-l trace`,
the L interpreter with a call stack, timeout 400 s) ran on every L error, ~270 of them, nearly all
the agreeing aborts. Changes:

* **Trace only disagreements** (`--trace disagree`, the default): L errors where the reference
  accepts (`l-error`) and `DISAGREE-*`; `--trace-sample N` adds N evenly spread agreeing aborts,
  `--trace all` the old behaviour (the "Where L aborts" table then lists every abort; by default it
  says how many of them are traced).
* **Trace cache** `tracecache.json` keyed by (sha of `checker.prog`, fixture sha, entry, words): a
  second run on the same program traces nothing again; an untraced result (timeout) is cached and
  reported as `untraced (timeout)` instead of `–`.
* **`--rerun-failing [RESULTS]`**: only the fixtures not passing (`agree-accept`, `agree-reject*`,
  `agree-timeout`) in either entry of a previous `results.json` (default: this checkout's), merged
  back into it, so the report stays whole. 3 fixtures, 99 s.
* **8 jobs** by default (was `cpu_count // 4`, capped at 16), and fixtures **started largest first**
  (`as_completed`, results put back in fixture order), so the big runs do not form the tail.
* `agree-timeout`: L and the reference both time out (the two `whnf_*_loop` fixtures, which
  con-leche expects to time out); and the second capacity retry (B3).

**Full run now: 8 min 46 s** (`--no-diff --no-perf --no-interp`, 8 jobs, reference cache warm;
2 traces, both `hoist_ok`). With a cold reference cache (a new `e2e-ref`/vendor revision) the
references run once more per fixture: they were ~4 min of the 13.6 min first run here.

## e2e after this lane (`2b7c8bfa`: master with B1 fixed, before front3's hoist)

| class | `check` | `check_np` |
|---|---:|---:|
| agree-accept | **405** | **391** |
| agree-reject | 3 | 3 |
| agree-reject (L aborts) | 262 | 278 |
| agree-timeout | 2 | 2 |
| l-error | 2 (`natop_order`, `natop_before_ble`: B2, front3) | 0 |
| ref-memout | 1 (`stack_fuel_offset`) | 1 |

Against both references (`check`): 405 accept/accept/accept, 206 reject, 55 decline, 4 error, 2
accept/accept/no (B2), 2 timeout, 1 exit -6/memout; con-ron and `e2e-ref` disagree on none, L
accepts nowhere a reference does not. 9 fixtures need the larger capacities (7 at `2^25`, 2 at
`2^27`). Before (lane `stubs`): 399 / 385 agree-accept, 7 / 6 l-error, 3 / 2 l-timeout.
