# Lane `e2efix`: the remaining e2e bugs (B1, B3) and a fast `scripts/e2e.py`

Journal of lane `e2efix` (decisions, measurements, findings, open ends). Only this lane edits this
file. Starting point: lane `stubs`' e2e run (`docs/design/stubs.md`, "e2e with no stubs").

## B1: `lv_node` abort #2 in ι-reduction of a nested inductive's recursor

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
