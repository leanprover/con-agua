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
