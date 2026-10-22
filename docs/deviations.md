# Deviations of L from its twin

L is a close twin of con-ron (and through it con-leche). This file lists every place where L
deliberately does something else than its twin, beyond fuel and fixed capacities (an array or
memo table that is full aborts by design). **Rule (PLAN.md):** a lane that introduces a
deviation adds its row here in the same commit; the coordinator reviews the list.

Effect: **completeness** = L aborts (declines) on inputs the twin accepts; **performance** =
same verdicts, more work or memory; **none** = representation only. A deviation never may be a
soundness loss; one that could become one is marked **(!)**.

First audit: 2026-10-22, lane `twinaudit` (sources: DESIGN.md, `docs/progress.md`'s partial
refinements, the L code's comments, `docs/e2e.md`). Fixed rows move to the end.

## Open

| id | where (L) | twin | L | effect | owner | proposed fix |
|---|---|---|---|---|---|---|
| D1 | `Arena/DeclAndPin.lean` `and_pin_ok`, `and_block_named` | `andPinOk`'s `.indDecl` arm (`ConRon/Arena/Basis.lean:130`): a block naming `And`/`And.intro`/`And.rec` must have 2 parameters and be `canonEqList`-equal to the pinned block | **fixed** (decls3 landing 4): the same arm (kind `6`: `and_block_named` over the block, `nP == 2`, `canon_eq_list` of the block copied into `EREC` against `rom_and_pin()`). Until lane romload gives `rom_and_pin` its L body it is an `abortStub`: the real `And` block aborts (a decline where the twin accepts) | completeness only, until `rom_and_pin` is read from the ROM; the proof is `refines_part` until `LoopR` holds the front's `DeclsF` | decls3 (proof), romload (`rom_and_pin`) | `rom_and_pin` from the ROM (`romAndPin_spec`); the inductive arm's proof |
| D2 | `Front/Fields.lean:28,71` (`read_nat` → `NONE`); its users in `Line.lean`, `ApplyExpr.lean`, `ApplyDecl.lean`, `IndFields.lean` | con-leche's `readNatAt` reads any `Nat` | an id, a name's `num` part, a `bvar`/`proj` index or a hint height of more than 18 digits aborts (`NONE`); the id tables refuse `NONE = TOMB` (`IdTable.lean`) | completeness (exotic exports) | front (done) → unassigned | read long numbers into the limb pool (as `nat_dec`), or prove they cannot name a bound id |
| D3 | `Front/FieldsDecl.lean:73,103` `str_code`; `ApplyDecl.lean:23` | the `safety` / quotient `kind` strings are compared after unescaping | a backslash in these strings reads as "not `safe`" and aborts | completeness (lean4export never escapes them) | front2 (done) → unassigned | compare after `str_put_esc` |
| D4 | `Arena/DeclArmsNat.lean:23-29,995` `check_div_mod_pin_loop` | `orElseAttempt` (`CheckerBase.lean:102`) restores the state after a failed attempt and tries the next pin variant | aborts on any error inside an attempt | completeness (only with ≥ 2 pin variants loaded) | decls3 | a state snapshot in L, or con-leche returning "error" vs "not defeq" (ROADMAP §3(c)) With a 1-variant pin set nothing remains (decls3): the twin's `.recovered` then hits `[]` and fails, `.failed` fails, so every error inside the one attempt is a non-accept in both (D16); the gap is only for ≥ 2 variants (D5). |
| D5 | `scripts/e2e.py` (`romgen … 1`); DESIGN.md "End-to-end runs" | the twin runs with all of con-leche's `natOpPinSets` | the harness loads a 1-variant pin buffer: 17 older-toolchain fixtures decline (296/313) | completeness (harness only; the theorem holds for every buffer) | integrate | load the 3-variant buffer once D4 is fixed |
| D6 | `Arena/Rom.lean:220-266` (`ascii_loop`, `rom_put`, `rom_lit`, `memo_push`) | `internPinSets` takes any con-leche value | pin data aborts on non-ASCII names, `natVal ≥ 2^64`, string literals, non-canonical back references | completeness (unusual pin data only) | romload (done) → unassigned | add the readers when a toolchain needs them |
| D8 | `Front/IdTable.lean` `tbl_fresh` | `IdTable.bound` skips the hash when `sparse.isEmpty` | probes the sparse memo (one slot when empty): one hash per line | performance (constant) | twinaudit (done) → unassigned | relate the memo's live count to the map's emptiness (`MemoRV` does not), then test it first |
| D9 | `Front/IdTable.lean` `tbl_put` | `IdTable.insert` pushes at the frontier without bound (`Array.push` reallocates) | the dense array stops at its fixed capacity; later ids go to the sparse memo (aborting at its 3/4 load) | none within capacity (the capacity rule) | – | – |
| D10 | ROADMAP "Known costs" 1 | Rust frees transient `Nat`s | the limb and string pool is append-only | performance (memory) | unassigned | a per-declaration scratch region |
| D11 | ROADMAP "Known costs" 2; DESIGN.md (strings) | packed bytes | strings one byte per word | performance (memory, 8×) | unassigned | packed strings if it matters |
| D12 | ROADMAP "Known costs" 3 | hash maps delete and grow | memo generations and tombstones stay until the next clear | performance (load, probe length) | unassigned | resize/compaction (layout only; `MemoRG` unchanged) |
| D13 | DESIGN.md (`readLC`/`readNC`/`readLsC`) | readback caches | not mirrored: L never reads back (the level algorithms work on handles) | none | – | – |
| D14 | `lv_equiv`, DESIGN.md (levels) | con-leche's `leq` simplifies again | simplifies each side once (proved equal) | none | – | – |
| D15 | DESIGN.md (lane `induct`); ROADMAP §3(b) | every `CheckMode`, `checkFuel` | the `.verified` mode only, no `checkFuel` | none | – | – |
| D16 | ROADMAP §3(c),(h); `ApplyDecl.lean:23`, `IndApply.lean:15` | declines (unsafe, non-`safe`), invalid and `fail` are separate verdicts | all are `abort`; only `ACCEPT` is read | none | – | – |
| D17 | Stage B `validate` / `scan_string` (DESIGN.md, lane `stageb`) | `feed_chunk` asks `newline_from`; con-leche decodes a whole string, then checks UTF-8 | does not ask (same error, same line); checks each raw run between escapes (proved equivalent) | none | – | – |

## Fixed

| id | was | fixed by |
|---|---|---|
| F1 | the id tables were dense arrays; an id past the end aborted (`e2e/rounds_huge_gaps`) | lane `twinaudit`: `Front/IdTable.lean`, dense + sparse as `IdTable` |
| F2 | strings with escapes aborted | lane `front2`: `Unescape.lean`, `str_put_esc` |
| F3 | `strVal` lines aborted | lane `strlit` |
| F4 | `natVal` past 18 digits aborted | `nat_dec` (`ApplyExpr.lean`) |
| F5 | expression and declaration lines aborted | lane `front2` |
| F6 | inductive lines aborted in the front | lanes `indproofs`/`indproofs2` (landing 6) |
| F7 | no `Nat`-operation pin variant in the ROM | lane `romload`: pin data as an input |
| F8 | the readback's `EMemo` was not mirrored | mirrored with back references (DESIGN.md, lane `decls`) |
| F9 | uncached `lvl_eq` in lane `induct`'s code | lane `decls3`: `lvl_eq_c` (the front's `IndApply.lean` `lvl_eq` is the twin's uncached `Level.isEquiv`, not a deviation) |
| F10 | the eager mode-memo take/put banks | the eager key bit (DESIGN.md, lane `whnf`) |
| F11 | dropping the scratch tier cost O(capacity) | epoch slots (lane `libs`) |
| F13 | uncached `lvls_eq` in `iota_rec_at` (twin: cached `lvlsEq?`) | lane `whnf2` (`WhnfIotaRec.lean:90` calls `lvls_eq_c`) |
| F12 | L aborts where the twin did not: `sl_get` out of range, `check_block_agree` on an empty rest, `pin_in` on an empty table, `class_read` wrapping | fixed in place (DESIGN.md, lanes `indproofs`, `decls2`, `indproofs2`) |
| F14 | uncached `lvls_eq` in `target_class_match` (D7; twin: cached `lvlsEq?`) | lane `indproofs2` (`RecCheck.lean` calls `lvls_eq_c`) |
