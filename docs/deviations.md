# Deviations of L from its twin

L is a close twin of con-ron (and through it con-leche). This file lists every place where L
does something else than its twin, beyond fuel and fixed capacities (an array or memo table
that is full aborts by design). **Rule (PLAN.md):** a lane that introduces a deviation adds
its row to `## Temporary` or `## Deliberate` in the same commit; the coordinator reviews the
list.

Three sections. **Temporary**: L currently does something else and we intend to fix it
(missing code, aborts "for now", stubs, unported arms, harness-only limits meant to go away);
rows whose intent is unclear are listed here too. **Deliberate**: by design and staying; the
fix column says why. **Fixed**: history, one line each.

Effect: **completeness** = L aborts (declines) on inputs the twin accepts; **performance** =
same verdicts, more work or memory; **none** = representation only. A deviation never may be a
soundness loss; one that could become one is marked **(!)**.

Audit: 2026-10-22, lane `twinaudit`, restructured by classification (some ids are used twice:
D18, D21).

## Temporary

| id | where (L) | twin | L | effect | owner | proposed fix |
|---|---|---|---|---|---|---|
| D2 | `Front/Fields.lean:28,71` (`read_nat` → `NONE`); its users in `Line.lean`, `ApplyExpr.lean`, `ApplyDecl.lean`, `IndFields.lean` | con-leche's `readNatAt` reads any `Nat` | an id, a name's `num` part, a `bvar`/`proj` index or a hint height of more than 18 digits aborts (`NONE`); the id tables refuse `NONE = TOMB` (`IdTable.lean`) | completeness (exotic exports) | front (done) → unassigned | read long numbers into the limb pool (as `nat_dec`), or prove they cannot name a bound id |
| D3 | `Front/FieldsDecl.lean:73,103` `str_code`; `ApplyDecl.lean:23` | the `safety` / quotient `kind` strings are compared after unescaping | a backslash in these strings reads as "not `safe`" and aborts | completeness (lean4export never escapes them) | front2 (done) → unassigned | compare after `str_put_esc` |
| D4 | `Arena/DeclArmsNat.lean:23-29,995` `check_div_mod_pin_loop` | `orElseAttempt` (`CheckerBase.lean:102`) restores the state after a failed attempt and tries the next pin variant | aborts on any error inside an attempt | completeness (only with ≥ 2 pin variants loaded) | decls3 | a state snapshot in L, or con-leche returning "error" vs "not defeq" (ROADMAP §3(c)) With a 1-variant pin set nothing remains (decls3): the twin's `.recovered` then hits `[]` and fails, `.failed` fails, so every error inside the one attempt is a non-accept in both (D16); the gap is only for ≥ 2 variants (D5). |
| D6 | `Arena/Rom.lean:220-266` (`ascii_loop`, `rom_put`, `rom_lit`, `memo_push`) | `internPinSets` takes any con-leche value | pin data aborts on non-ASCII names, `natVal ≥ 2^64`, string literals, non-canonical back references | completeness (unusual pin data only) | romload (done) → unassigned | add the readers when a toolchain needs them |
| D8 | `Front/IdTable.lean` `tbl_fresh` | `IdTable.bound` skips the hash when `sparse.isEmpty` | probes the sparse memo (one slot when empty): one hash per line | performance (constant) | twinaudit (done) → unassigned | relate the memo's live count to the map's emptiness (`MemoRV` does not), then test it first |
| D10 | ROADMAP "Known costs" 1 | Rust frees transient `Nat`s | the limb and string pool is append-only | performance (memory) | unassigned | a per-declaration scratch region |
| D11 | ROADMAP "Known costs" 2; DESIGN.md (strings) | packed bytes | strings one byte per word | performance (memory, 8×) | unassigned | packed strings if it matters |
| D12 | ROADMAP "Known costs" 3 | hash maps delete and grow | memo generations and tombstones stay until the next clear | performance (load, probe length) | unassigned | resize/compaction (layout only; `MemoRG` unchanged) |
| D13 | DESIGN.md (`readLC`/`readNC`/`readLsC`) | readback caches | not mirrored: L never reads back (the level algorithms work on handles) | none | – | – |
| D14 | `lv_equiv`, DESIGN.md (levels) | con-leche's `leq` simplifies again | simplifies each side once (proved equal) | none | – | – |
| D15 | DESIGN.md (lane `induct`); ROADMAP §3(b) | every `CheckMode`, `checkFuel` | the `.verified` mode only, no `checkFuel` | none | – | – |
| D16 | ROADMAP §3(c),(h); `ApplyDecl.lean:23`, `IndApply.lean:15` | declines (unsafe, non-`safe`), invalid and `fail` are separate verdicts | all are `abort`; only `ACCEPT` is read | none | – | – |
| D17 | Stage B `validate` / `scan_string` (DESIGN.md, lane `stageb`) | `feed_chunk` asks `newline_from`; con-leche decodes a whole string, then checks UTF-8 | does not ask (same error, same line); checks each raw run between escapes (proved equivalent) | none | – | – |
| D18 | `Arena/RecGen.lean` `class_fields_of_go`, `class_rec_tys_ok`, `class_rules_ok`, `class_recs_rules_ok_go`; `Arena/RecClass.lean` `class_gen_minor_ty_ihs_go` | `classFieldsOf`, `classRecTysOk`, `classRulesOk`, `classRecsRulesOk` build their result lists by `::` | the loops became self-recursions that `sl_cons` each element onto the rest's slice (a copy per element, so that every written word lies above the old pool top and the decodings stay stable) | performance (quadratic in a constructor's fields / a block's recursors; small) | rec2 | preallocate and prove the in-place writes (a frame lemma for writes above a slice) if it ever matters |
| D18 | `Arena/RecCheck.lean` `target_major_nfs`, `erase_each`, `block_rec_split_own_aux`, `block_rec_want_aux_names`, `tgt_stored_rules_remap` | `targetMajorNfs`, `targetK53`'s `mapM`s, `targetRecPins`' `filter`s and `mapM`, `tgtStoredRules`' `map` build lists by `::` | self-recursion as the twin's, each element `sl_cons`ed onto the rest's `IW` slice (a copy): quadratic in the list's length | performance (small lists) | indproofs3 (rec) | an in-place slice writer with a frame lemma, if it matters |
| D18 | `Arena/IndSum.lean` `check_sum_ctors` | `checkSumCtors` builds its two result lists by `::` | self-recursion that `sl_cons`es the head's `[cv, nF]` and sorts-header pointers onto the rest's slices (as above) | performance (quadratic in a block's constructors; small) | indproofs2 | as above |
| D18 | `Checker/Prelude.lean` `hoist_ok` (`prepare_prelude`) | `hoistNatOpGround` reorders the stream when a pinned `Nat` operation precedes its ground | checks that the hoist is the identity and aborts otherwise (`e2e/natop_order`, `natop_before_ble`) | completeness | integrate | `hoistClosure` + `applyHoist` in L (a stable sort of record indices by `hoistKey`) |
| D19 | `Rom/CIRead.lean` (the ROM constant readers) | `internCI` keeps a `sortZ` name as a value | interns it (only `Quot`'s `u`, already interned as a level parameter) | none | integrate | – |
| D20 | `Checker/Entry.lean` adapters `abstract1_fast`, `instantiate1_fast`, `inst1` | the walks take `coreWalkFuel` | the fuel argument is dropped; lane exprops4's walks count their own | none (the twin's fuel is never exhausted below `2^62`; ROADMAP §3(b)) | integrate | – |
| D18 | `Arena/IndParts.lean` `block_split*`, `block_groups*`, `block_rec_want`/`_got`, `block_member_counts_go`, `block_shape_names_of`/`_ctors_of`/`_members_of`/`_rhss_of`/`_recs_of` | lists built by `::` (constant time per element) | recursion as the twin's, each element consed onto the rest's `IW` slice with `sl_cons` (a copy): quadratic in the list's length (block members, constructors, recursors, rules) | performance (small lists) | indproofs2 (parts) | an in-place slice writer with a frame lemma, if blocks get large |
| D18 | `Arena/IndInstall.lean` `check_block_teles`, `check_block_inds_cv_tas(_go)`, `check_block_idx_sorts`, `check_block_ctors_go` | `checkBlockTeles`, `checkBlockInds`, `checkBlockIdxSorts`, `checkBlockCtors` build their lists by `::` | recursion as the twin's, each `[cvTa, s]` record consed onto the rest's `IW` slice with `sl_cons` (a copy): quadratic in the block's member count | performance (small lists) | indproofs2 (install) | an in-place slice writer with a frame lemma, if blocks get large |
| D21 | `Arena/StrLit.lean` `str_ls1`, `str_cons_spine` (via `rom_lit`) | `internLsNode [u]`, `internE (.lit (.natVal c))` take the key as a value | the one-element list / one-limb literal is pushed at the pool top first and stays there even when the node already exists (one word per call) | performance (memory: two pool words per string-literal unfolding, a few per `List` test) | defeq2 | intern from a scratch word, or pop the top on a hit |
| D11 | ROADMAP "Known costs" 2; DESIGN.md (strings) | packed bytes | strings one byte per word | performance (memory, 8×) | unassigned | intent unclear: packed strings if it matters |
| D12 | ROADMAP "Known costs" 3 | hash maps delete and grow | memo generations and tombstones stay until the next clear | performance (load, probe length) | unassigned | intent unclear: resize/compaction (layout only; `MemoRG` unchanged) |
| D18 | `Arena/RecGen.lean` `class_fields_of_go`, `class_rec_tys_ok`; `Arena/RecClass.lean` `class_gen_minor_ty_ihs_go` | `classFieldsOf`, `classRecTysOk` build their result lists by `::` | the loops became self-recursions that `sl_cons` each element onto the rest's slice (a copy per element, so that every written word lies above the old pool top and the decodings stay stable) | performance (quadratic in a constructor's fields / a block's recursors; small) | rec2 | intent unclear: preallocate and prove the in-place writes (a frame lemma for writes above a slice) if it ever matters |
| D24 | `Checker/Prelude.lean` `hoist_ok` (`prepare_prelude`) | `hoistNatOpGround` reorders the stream when a pinned `Nat` operation precedes its ground | checks that the hoist is the identity and aborts otherwise (`e2e/natop_order`, `natop_before_ble`) | completeness | integrate | `hoistClosure` + `applyHoist` in L (a stable sort of record indices by `hoistKey`) |
| D21 | `Arena/WhnfProj.lean` `proj_table_name` | `projTableName` interns `str T "projTable"`: no allocation when the name exists | writes the nine bytes of `"projTable"` at the pool top and raises the top before `intern_nstr` (whose refinement needs the slice below the top), on every call (`find_proj`) | performance (memory: nine pool words per projection-table lookup; the pool is append-only, D10) | whnf3 | keep one persistent `"projTable"` slice (a `CTL` word holding its offset, an invariant of `CoreS`), or roll the top back when the node existed |
| D22 | `Arena/WhnfProj.lean` `proj_table_name` | interns the prefix `T` without a check | aborts unless `T` is a name handle of the store (tag, tier, index below its count) | none (the twin's store is well formed: every name it holds is valid) | – | – |
| D18 | `Arena/IndParts.lean` `block_split*`, `block_groups*`, `block_rec_want`/`_got`, `block_member_counts_go`, `block_shape_names_of`/`_ctors_of`/`_members_of`/`_rhss_of`/`_recs_of` | lists built by `::` (constant time per element) | recursion as the twin's, each element consed onto the rest's `IW` slice with `sl_cons` (a copy): quadratic in the list's length (block members, constructors, recursors, rules) | performance (small lists) | indproofs2 (parts) | an in-place slice writer with a frame lemma, if blocks get large |
| D24 | `Arena/StrLit.lean` `str_ls1`, `str_cons_spine` (via `rom_lit`) | `internLsNode [u]`, `internE (.lit (.natVal c))` take the key as a value | the one-element list / one-limb literal is pushed at the pool top first and stays there even when the node already exists (one word per call) | performance (memory: two pool words per string-literal unfolding, a few per `List` test) | defeq2 | intern from a scratch word, or pop the top on a hit |
| D26 | `Arena/StrLit.lean` `str_ls1`, `str_cons_spine` (via `rom_lit`) | `internLsNode [u]`, `internE (.lit (.natVal c))` take the key as a value | the one-element list / one-limb literal is pushed at the pool top first and stays there even when the node already exists (one word per call) | performance (memory: two pool words per string-literal unfolding, a few per `List` test) | defeq2 | intern from a scratch word, or pop the top on a hit |
| D28 | `Arena/StubNames.lean` `name_rec`, `name_rec_i`, `intern_ls_iw` | `internNNode (.str n "rec")`, `.str n s!"rec_{i}"`, `internLsNode us` take the key as a value | the string (3, or 4 + digits words) / the level list is written at the pool top (`pool_room`) and stays there even when the node exists | performance (memory: a few pool words per block member / recursor / level list built) | stubs | as D21/D24: pop the top on a hit |

## Deliberate

| id | where (L) | twin | L | effect | owner | proposed fix |
|---|---|---|---|---|---|---|
| D5 | `scripts/e2e.py` (`romgen … 1`, `con-ron --pins` of the same list); DESIGN.md "End-to-end runs" | the twin runs with all of con-leche's `natOpPinSets` | the harness loads a 1-variant pin buffer (the latest toolchain's, the user's decision); all three references run at that list | completeness (harness only; the theorem holds for every buffer) | integrate | by design: one pin variant is the user's decision (latest toolchain); loads all variants only if D4 lands recovery |
| D9 | `Front/IdTable.lean` `tbl_put` | `IdTable.insert` pushes at the frontier without bound (`Array.push` reallocates) | the dense array stops at its fixed capacity; later ids go to the sparse memo (aborting at its 3/4 load) | none within capacity (the capacity rule) | – | by design: the capacity rule (a full array aborts by design) |
| D13 | DESIGN.md (`readLC`/`readNC`/`readLsC`) | readback caches | not mirrored: L never reads back (the level algorithms work on handles) | none | – | by design: L works on handles and never reads back |
| D14 | `lv_equiv`, DESIGN.md (levels) | con-leche's `leq` simplifies again | simplifies each side once (proved equal) | none | – | by design: proved equal; simplifying once suffices |
| D15 | DESIGN.md (lane `induct`); ROADMAP §3(b) | every `CheckMode`, `checkFuel` | the `.verified` mode only, no `checkFuel` | none | – | by design: only the `.verified` mode is checked |
| D16 | ROADMAP §3(c),(h); `ApplyDecl.lean:23`, `IndApply.lean:15` | declines (unsafe, non-`safe`), invalid and `fail` are separate verdicts | all are `abort`; only `ACCEPT` is read | none | – | by design: only `ACCEPT` is read, so the verdicts coincide |
| D17 | Stage B `validate` / `scan_string` (DESIGN.md, lane `stageb`) | `feed_chunk` asks `newline_from`; con-leche decodes a whole string, then checks UTF-8 | does not ask (same error, same line); checks each raw run between escapes (proved equivalent) | none | – | by design: proved equivalent |
| D19 | `Rom/CIRead.lean` (the ROM constant readers) | `internCI` keeps a `sortZ` name as a value | interns it (only `Quot`'s `u`, already interned as a level parameter) | none | integrate | by design: representation only |
| D20 | `Checker/Entry.lean` adapters `abstract1_fast`, `instantiate1_fast`, `inst1` | the walks take `coreWalkFuel` | the fuel argument is dropped; lane exprops4's walks count their own | none (the twin's fuel is never exhausted below `2^62`; ROADMAP §3(b)) | integrate | by design: the twin's fuel is never exhausted; the walks count their own |
| D22 | `Arena/WhnfProj.lean` `proj_table_name` | interns the prefix `T` without a check | aborts unless `T` is a name handle of the store (tag, tier, index below its count) | none (the twin's store is well formed: every name it holds is valid) | – | by design: the twin's store is well formed; the check is defensive |
| D27 | `Arena/DeclStep.lean` `dind_copy` (via `ind_block_to_erec`) | copies the block's constants by value | aborts on a non-empty copy starting at word 0 of `DLP` (word 0 is the pool's top) | none (the front writes every record and slice at `1 + top`; decls4-andpin) | – | by design: defensive; makes the copy agree with `IndDeclAt`'s cut pool |

## Fixed

- **D1** (fixed by decls3 landing 4 and lane integrate): `and_pin_ok`'s inductive arm landed (kind `6`) and `rom_and_pin` got L code, so the real `And` block is accepted.
- **F1** (fixed by lane twinaudit): id tables dense + sparse (`IdTable`); ids past the end no longer abort (`e2e/rounds_huge_gaps`).
- **F2** (fixed by lane front2): strings with escapes (`Unescape.lean`, `str_put_esc`).
- **F3** (fixed by lane strlit): `strVal` lines.
- **F4** (fixed by `nat_dec`, `ApplyExpr.lean`): `natVal` past 18 digits.
- **F5** (fixed by lane front2): expression and declaration lines.
- **F6** (fixed by lanes indproofs/indproofs2, landing 6): inductive lines in the front.
- **F7** (fixed by lane romload): pin data as an input.
- **F8** (fixed by lane decls): the readback's `EMemo` mirrored with back references.
- **F9** (fixed by lane decls3): uncached `lvl_eq` in lane induct's code, now `lvl_eq_c`.
- **F10** (fixed by lane whnf): the eager mode-memo take/put banks, via the eager key bit.
- **F11** (fixed by lane libs): dropping the scratch tier cost O(capacity); epoch slots.
- **F12** (fixed in place by lanes indproofs, decls2, indproofs2): `sl_get` out of range, `check_block_agree` on an empty rest, `pin_in` on an empty table, `class_read` wrapping.
- **F13** (fixed by lane whnf2): uncached `lvls_eq` in `iota_rec_at`, now `lvls_eq_c`.
- **F14** (fixed by lane indproofs2): uncached `lvls_eq` in `target_class_match` (was D7), now `lvls_eq_c`.
- **F15** (fixed by helper whnf4-d23): D23, `lp_go`/`inst_lp_core` could not cut off at a parameter-free node (L's derived words kept only the two ranges), so the walk descended into parameter-free subterms and `inst_lp_core` read `ls_node(us)` for a parameter-free `e`. Now the level-parameter bit is mirrored per node (`LpCol.lean`: bit 30 of the five `XDER` words; columns 55‥61 for `succ`/`max`/`imax`/level lists/`sort`/`const`/`fvar`, written when the node is pushed; `ArenaR`'s `*Hp`/`*Lp` fields, `DerR`'s `bvP`/`zlP`), read by `der_b`'s third result (`derLW_ok`), and `lp_go`/`inst_lp_core` test it first, as `instLPGo`/`instLPFast`.
- **F16** (fixed by lane defeq2): D25, `lvl_live` checked `imax` arguments with `lv_node` (a level read before a knot call was not known to read back after it). Now `PoolGrew.lvl` (the level tables only grow) rides in `CoreAfter` and `lvl_den_later` reads the level back; L mirrors the twin again.
