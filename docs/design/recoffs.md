# Lane recoffs: named record offsets

**Question** (the user, 2026-11-13): instead of the compiler-owned record layout (lrecords
R1/R2), the cheaper middle ground: "never use literals in the code/proof, but defs, so that to
change the layout you just need to change a few lines". The test: compact `IIndCaps` (15 words, 7
of them dead since ronsync3/ronsync4) and count the lines that change outside the layout files.

## 1. Inventory (master 8ea7eccbf)

Script `_tmp/recoffs/inv.py` (comment-stripped; generated `Checker/Prog*`/`Asm*` excluded; L text =
inside `lfn`/`lblk` blocks). Line counts.

**L code.**

| what | lines | files | largest |
|---|---:|---:|---|
| `EREC⦃e + N⦄` reads | 339 | 29 | DeclArmsCanon 42, WhnfIotaRec 28, BasisL 26, DefEq 25 |
| `EREC⦃q⦄` (offset 0: kind, name, eta) | 119 | 28 | |
| `erec_put`/`er_put5`/`er_copy_er(d + N, …)` writes | 169 | 13 | RecCheck 30, CIRead 27, BasisL 23 |
| record sizes `erec_alloc(N)`, size tables `n := 20` | 14 + 4 | 11 | |
| `IW.u64[x + N]` (inductive-stage scratch records) | 563 | 13 | DeclArmsNat 129, RecGen 82 |
| front `DECL`/`DLP`/`DIND[q + N]` | 45 | 6 | IndApply 17 |

Offsets by value (EREC reads): `+3` 122, `+5` 68, `+2` 61, `+1` 53, `+6` 39, `+4` 32, `+7` 28,
`+8` 19, `+9` 13, `+10‥19` 26.

**Proofs.**

| what | lines | files |
|---|---:|---:|
| `erRd m (x + N)` | 524 | 87 |
| `erecP`/`erA m (x.toNat + N)` | 156 | 52 |
| decoder words `nat?/hd?/hlist? a (q + N)` | 106 | 21 |
| `callW … "erec_put" [x + N, …]` | 26 | 4 |
| decoder unfolds (`simp/unfold [… decCI/decCV/decCaps/decRule/decTbl …]`) | 187 | 86 |
| `set64 IW (… + N)` / `rdW (arr64 IW) (… + N)` | 672 | 139 |

**How proofs use them.** (1) Decoder equations: the same extraction fact re-proved in several
files by unfolding the decoder and fixing the offset (`PosFt.decCaps_counts`,
`FormerNZRef.decCI_ind_nz`, `InferProj2.decCI_indNC`, `NcGoW.decCaps_ctors`,
`NestBlockOfKey` (`q + 15`/`q + 16`), `ClassNPcOf.decCI_ind_cases`, `QuotCiT.decCaps_sh`,
`DeclAndPinIndDec.decCaps_reloc`, `IndRecRead.decCI_indCaps`). (2) Syntactic matching: a model
or a hand-written statement must say `q + 12` where the L text does. (3) Omega bounds and frames
(`(q + k).toNat = q.toNat + k`, `EKeep`/`Holds` ranges `c ≤ i < c + 15`, `wd_set_ne … omega`
chains). (4) Hand-written comparison models (`capsEqBB`, `ciEqRestB`).

## 2. Named offsets: design

* `ConAgua/Arena/RecLayout/Caps.lean` (`L.Caps.eta`, `nIdx`, `neverZero`, `allOff`, `allLen`,
  `nparams`, `ctorsOff`, `ctorsLen`, `size`), `RecLayout/CI.lean` (`L.CI.kind`, `cv`, `indCaps`,
  `indSize`): one `Word` def per field, the layout facts (`f.toNat < size.toNat`, slice length
  word after offset word) next to them.
* `RecLayout/CapsDec.lean`: the decoder's facts once: `decCaps_eq_some` (word by word),
  `decCaps_of`, `decCaps_rd` (at L's word addresses, any `RdOK` reader), `decCaps_congr`
  (record carried to another reader), `decCI_indInfo`, `decCI_indInfo_rd` (an `indInfo`
  record's caps at `q + (CI.indCaps + Caps.f)`).
* L text: `EREC⦃q + ⟪Caps.nparams⟫⦄`, `EREC⦃p + ⟪CI.indCaps + Caps.nIdx⟫⦄`,
  `erec_alloc(⟪CI.indSize⟫)`. The compiler evaluates the constant: `checker.s` unchanged.
* A field at offset 0 (`eta`, the kind word) stays `EREC⦃q⦄`: `q + ⟪Caps.eta⟫` compiles to an
  extra `add` (the compiler folds no `+ 0`).

**Finding: the defs must be `@[reducible]`.** With a plain or `@[irreducible]` def the generated
`l_model` proofs slow down by 2–3× and time out (ClassNPcOf's `step1`: 200 000 heartbeats; 21.7 s
for the module with 2 000 000 vs 8.9 s with numerals): `grind` meets `UInt64.toNat Caps.nparams`
atoms where it would have seen numerals (a `grind`-attribute of value equations did not help).
With `@[reducible]` the generated proofs evaluate the names as before (8.9 s), and statements keep
the names where they are written. The cost: a proof that still says `q + 17` keeps working
(reducible defeq), so a leftover literal is only found by changing the layout: step 3.

### Batch 1: the caps record's reads by name (this landing)

* The decoder (`decCaps`, `decCI`'s `indInfo` arm) reads at `q + Caps.f.toNat`,
  `p + CI.indCaps.toNat`.
* L: every read of a caps field (`IndPos`, `IndPos2`, `RecClass`, `WhnfIota`, `Infer`, `DefEq`'s
  three η reads, `DeclArmsCanon`'s `caps_eq_*`), `rci_caps`' field writes, the copy
  `er_copy_er(r + ⟪CI.indCaps⟫, p + ⟪CI.indCaps⟫, ⟪Caps.size⟫)`, the record sizes
  `⟪CI.indSize⟫` (`rci_ci`, `ci_at_lps`, `ind_rec_copy`, `ind_info_rec`, `ind_type`).
  Construction code that writes a whole record positionally (`block_caps_fin`'s three `rec5`s,
  `ind_info_rec`'s three `er_put5`s, the front's `ind_caps`) is left for batch 3 (builders).
* Deleted duplicates, now `CapsDec` lemmas: `PosFt.decCaps_counts`, `FormerNZRef.decCI_ind_nz`,
  `decCI_ind_n`, `QuotCiT.decCaps_sh`, `NestBlockOfKey.decCI_indInfo_bound` (and its 15/16-word
  arithmetic in `nestBlockOf_key`); restated over names: `InferProj2.decCI_indNC`,
  `IndRecRead.decCI_indCaps`, `ClassNPcOf.decCI_ind_cases`, `DeclAndPinIndDec.decCaps_reloc`
  (and `relocK`'s size), `QuotCiT.ciCopy` (any offset `o ≥ 5`).
* `checker.s`, `pins.bin` unchanged (`asm_file.py --check`), the `Prog*` files unchanged
  (`checker_prog.py --check`).
* Unfold sites left outside `RecLayout/`: 8, all in the whole-record writers' proofs
  (`IcaW` 3, `IndInstallRefine2` 3, `CIReadRefCaps` 1, `CIReadRefCI` 1), which batch 3 rewrites.
* 45 files, +514/−312 lines (with the three new `RecLayout` files, about 280 lines).

## 3. The test: `IIndCaps` compacted from 15 to 8 words

### Batch 2a: the whole-record writers by name (code change)

Before the compaction could be a layout-file change, the code that writes a whole caps record had
to stop being positional:

* `block_caps_fin` (`Arena/IndInstall.lean`): `iw_alloc(⟪Caps.size⟫)` and one `IW` store per
  field (it was three `rec5`s of 15 positional words); `ind_info_rec` copies the record with the
  existing loop `block_caps_at_er_copy_go(q + ⟪CI.indCaps⟫, caps, ⟪Caps.size⟫)` (it was three
  `er_put5`s); the front's `ind_caps` (`Front/IndApply.lean`) stores the eight fields by name (it
  stored ten words, two of them dead); `rci_caps`' and `caps_eq_a`'s `eta` read/write at
  `+ ⟪Caps.eta⟫` (an extra `add`; they are not hot).
* One lemma per writer shape in `CapsDec.lean`: `CapsRecW` (a record's field words in a reader),
  `CapsRecW.shift`, `decCaps_of_words`, `capsRecW_set64` (eight stores in field order hold the
  fields), `Caps.order` (the fields' order: the facts `omega` needs to keep two fields apart; a
  layout that keeps the order keeps every user). The writer proofs use these:
  `IcaW.capsFin_rec`/`icfW_ok`/`installCapsTail`, `iirK_eq`/`iirW_stage` (the record is
  `header ++ ieWords … Caps.size …`), `IndInstallRefine2.capsM_*`, `CIReadRefCaps.caps_rel`,
  `DeclCanonEq.capsEqAll_ok`; deleted: `installRec5`, `installDecCaps`, the list form of
  `CapsWords`, `CapsProg.rec5`.
* 13 files, +358/−316 lines (without `checker.s`).

### Batch 2b: the compaction

`RecLayout/Caps.lean`: `eta 0, nIdx 1, neverZero 2, allOff 3, allLen 4, nparams 5, ctorsOff 6,
ctorsLen 7, size 8` (8 lines). The build then failed in four proof files, each a literal that the
reducible names had tolerated until the values changed:

| file | what | lines |
|---|---|---:|
| `IndPosSpec/NestGroupCtors.lean` | `nest_container`'s proof read the ctors slice at `ciq + 5 + 13`/`+ 14`, `nparams` at `+ 12`, through a local copy of the caps decoder (`NcGoW.decCaps_ctors`, deleted) | +16/−15, −8 |
| `DeclAndPinIndCopy2.lean` | `irc_fin`'s size table `if kk = 3 then 20 …` | +3/−2 |
| `Rom/CIReadRefW.lean` | the hand model `ciSize`'s `some 20` | 1 |
| `QuotCiT.lean` | a `cases h4 : callW … "er_copy_er" [r + 5, c + 5, 15]` | 1 |

plus 7 comment/test lines that still said 15 or 20 (`IndPos2`, `IndApply`, `DeclStep`, `IcaW`,
the `#guard` in `IndTest`). So: **8 layout lines + 21 proof lines in 4 files** (and the
regenerated `checker.s`).

**A second layout change after those fixes** (fields spread with gaps: `nIdx 2, neverZero 3,
allOff 5, allLen 6, nparams 7, ctorsOff 9, ctorsLen 10, size 12`; not landed): the whole library
built with only `Caps.lean` changed; only `AsmFileEq` failed, as it must until `checker.s` is
regenerated (`checker_prog.py`, `asm_file.py`). That is the user's target: a layout change is the
layout file.

**What would have caught the leftovers earlier**: the names are `@[reducible]` (§2), so a literal
in proof text keeps checking against the named L text; only a changed value finds it. A cheap
check for the remaining records is the same perturbation (shift every offset by a gap, build,
revert): about one world rebuild (35 min at 2 threads on this machine).

**Performance** (`scripts/bench.py --set init --reps 3`, master b12763a4f vs the branch, load
19–108, so wall time is not meaningful): `init435` 217 197 M → 217 196 M instructions, peak RSS
620 MB both; `init-prelude` 1 160 M both, 27 MB both. `checker.s` 230 932 → 230 857 → 230 821
lines (builders, compaction). Verdicts: `diff-e2e.py --refs` with the branch's binary: no
UNSOUND/INCOMPLETE/CRASH/TIMEOUT; the same 8 REFDIFF (e2e-ref) as master's binary.

### Batch 3: recursor rules and projection tables by name (helper `recoffs-rule`)

* `RecLayout/Rule.lean` (`L.Rule`: `ctor`, `nfields`, `fire`, `lvlsOff`, `lvlsLen`, `pinsOff`,
  `pinsLen`, `rhs`, `size` 11), `RecLayout/Tbl.lean` (`L.ProjTbl`, not `L.Tbl`: that name is the
  twin's hash table, open in the arena proofs; `size` 13), and `RuleDec.lean`/`TblDec.lean`.
  `decRules` strides by `Rule.size`. `find_table` hands out the table's address plus one, so L
  reads `EREC⦃tq + ⟪ProjTbl.ctor - 1⟫⦄`.
* About 140 L lines; about 20 duplicated decoder lemmas deleted, about 15 restated over the names
  (62 files, +1194/−1219). `checker.s` unchanged.
* Left: writes to the dead words keep their numbers (rule words 2, 9, 10; table words 8, 11, 12);
  the whole-record writer proofs (`rule_copy`, `rules_to_erec`, `rmRec_stage`, `ruleM_*`,
  `rules_at_lps_go`) are still 11-word positional, as the caps writers were before batch 2a; a
  few `11 * j` strides in `CIReadRefCI`, `HoistDecode`/`HoistWalkRef`, `DeclAndPinIndCopy2` still
  say 11 (reducible defeq lets them check). A compaction of these records would find them, as
  batch 2b found the caps leftovers.
* Dead words: the rule record 3 of 11; the table 3 of 13 plus the two words nothing reads (kind
  and name, kept so the table looked like a constant record), 5 of 13.

## 4. lrecords after named offsets: recommendation

**Where things stand (master 0120575b02).** The caps, rule and table records are named; the
constant record and the constant value are in progress (helper `recoffs-ci`). Unfold sites left
outside `RecLayout/` that state an offset's number: 0 for the caps record; 4 for rules and tables
(`IndDeclConstsTable`'s `block_table`, `TsrW.rmRec_stage` ×2, `ConsBlockRecsTF`'s stride), all in
whole-record writer proofs; plus 13 offset-free `unfold decRules`/`simp [decRules]` (slices). The
caps test (§3): one layout change cost 8 layout lines + 21 proof lines (leftover literals); the
next one cost the layout file alone.

**What the compiler-owned layout (lrecords S, with R1–R3) would still add.**

* Not the user's goal any more: with named offsets a layout change is already the layout file.
* Structural frames instead of address reasoning: `Caps.order`, `capsRecW_set64`,
  `decCaps_congr` and the writer lemmas (≈200 lines per record kind in `…Dec.lean`, written once)
  exist because fields are words of one array; field arrays would make them frame lemmas of the
  memory model. The saving is those files, not their users.
* 32-bit loads of packed fields and capacity hints (performance), and one primitive for the
  frozen images.
* Not EREC's records at all. lrecords §3 designs fixed-stride tiered store records (`TRec`:
  `APP`, `LIT`, …), which already have named fields (`R⟨t, i⟩.f`, `StoreFields` rows). The
  records this lane named live in a bump-allocated pool (`erec_alloc(n)`), vary by kind (the kind
  word picks the layout), nest (`indInfo` embeds the caps record) and hold slices. Owning that
  layout in the compiler needs a tagged-union record construct and pool allocation in L's
  semantics: a new design, not R1/R2/S.

**Cost and saving.** Named offsets: caps (both batches, with the tooling and the two writer
rewrites) about 3 agent-hours; rules and tables about 2 h (helper); the constant record and value
about 3–4 h (helper, in progress). lrecords S: 90–150 h (§4.2), for structural frames and
packed loads on the store records. R1 (counts out of `CTL`) and R2 (masked packed pushes) stay as
§7.2/§7.3 found: no proof saving on their own.

**Recommendation.** Do not start R1/R2/S for the layout-change goal: named offsets meet it at
about a twentieth of the cost. Next steps, in order of value:

1. Land the constant record and value (`recoffs-ci`).
2. One perturbation build per record kind (shift every offset by a gap, build, revert; about one
   world rebuild each, or all kinds at once) to flush the literals the reducible names tolerate;
   the caps run found 4 files.
3. The rule writers by name as batch 2a did for caps (`rule_copy`, `rules_to_erec`,
   `rules_at_lps_go`, `parse_rule_d`; `rmRec_stage`, `ruleM_*`), then compact the rule record
   (3 dead words of 11) and the projection table (5 unused of 13) the way §3 did: install-time
   memory only, no measurable `Init` change expected (the caps compaction changed `Init` by
   −1 M of 217 197 M instructions).
4. Optional: `IW` scratch records, only where one layout is shared by several functions (the
   positivity context `ctx`, `NestState`); the `rec5`/`rec6` tuples private to one function gain
   little.

Revisit S only for its performance side (32-bit packed loads on the hot store records), measured
first with a prototype of batch O (lrecords §4.2).

### Batch 4: the constant record and the constant value by name (helper `recoffs-ci`)

* `RecLayout/CV.lean` (`L.CV`: `name` 0, `lpsOff`, `lpsLen`, `type`, `size`), `RecLayout/CI.lean`
  extended to every kind (`defnValue`, `defnHint`, `defnSize`, `Hint.*`, `ctorNparams`,
  `ctorNfields`, `ctorInduct`, `ctorSize`, `recMajor`, `recPrefix`, `recRulesOff`, `recRulesLen`,
  `recIsK`, `recSize`, `axiomSize`, `thmSize`); `CVDec.lean` (word facts, one iff per kind) and
  `CIDec.lean` (at L's word addresses). `decCV`, `decHint`, `decCI` read at the names.
* About 390 L lines (every constant-record and constant-value read and write, the builders
  `erec_ci`, `cv_new`, `ind_rec_copy`, the ROM reader, the front's `DIND` records); about 20
  duplicated decoder lemmas deleted (`ErecRdCV.lean` entirely), the rest restated through
  `CVDec`/`CIDec`. 149 files, +2252/−2113. `checker.s` unchanged.
* Left: 152 lines in 17 files use the simp set `rec_unfold` (the names back to numerals), all in
  proofs about code that writes or copies a whole record (`erec_ci`, `cv_new`, `cv_at_lps`,
  `ci_at_lps`, `ind_rec_copy`, `ctor_info_rec`, `rec_info_rec`, the front's and the ROM's
  writers), and `PropReadW`; some of those statements and a few readers (`CloseLams.decCV_some`
  and its callers, `DeclReduceSpec2.decCI_kind*`, parts of `DeclValsE`) still say numbers.
* Finding: a proof that says a number still matches L text with a single reducible name
  (`CV.lpsOff` against `1`) but not with a sum (`CI.cv + CV.lpsLen` against `3`): `rw`'s
  matching does not evaluate `UInt64` addition. Most of the fallout was of this kind.

## 5. `scripts/layout_perturb.py`

The leftover literals are found only by changing values (§3), so the perturbation is a script:
every nonzero offset of the chosen layout files gets a gap of `--gap` words (order and slice
adjacency kept; offset-0 fields, sums and stored values (`…Val`) stay), then `scripts/lake build`,
then the files are restored; it lists the failing modules (clean: only `Checker.AsmFileEq`, whose
`checker.s` is stale by design). Not a gate (a world rebuild, about 35–50 min at 2 threads here).

First run, `Rule.lean` and `Tbl.lean` (gap 3, master fd45c48b2): 7 modules besides `AsmFileEq`
still depend on an offset's number: `DeclAndPinIndCopy2`, `IndSumSpec/SumRules`, `IndexLoops`,
`PropReadRefine4`, `Checker/HoistDecode`, `Front/IndApplySpec2`, `Rom/CIReadRefRule` (the rule
writers' 11-word lists and the `11 * j` strides helper B listed, and a few readers it did not
reach). The caps record (after batch 2b) is clean: a gap perturbation (§3) built with only
`Caps.lean` changed.

## 6. A verdict note: the REFDIFFs in §3

§3's `diff-e2e.py --refs` runs (branch and master binaries, about 14:25) reported the same 8
REFDIFF: `unitlike_wide`, `unitlike_fieldless`, `unitlike_lean4_match4`, `unitlike_lean4_13371`,
`eta_partial_ctor`, `arena/bad/tutorial/115_etaCtor` (e2e-ref rejects, con-leche accepts) and
`nat_size_ok`, `nat_shift_over_max_size` (`maxNatSize`). These are the behaviours ronsync3/ronsync4
changed (unit-like/η-ctor caps removed, the maximum `Nat` size), and the main checkout's
`.lake/build/bin/e2e-ref` was then still the build from before ronsync4's con-leche bump: it was
rebuilt at 14:29 (by `bench.py`, which builds it). Rerun with the rebuilt e2e-ref (the cache is
keyed by the reference binary's hash): REFDIFF 0 for both the master and the compacted binary, on
the 8 fixtures and on the full set (no UNSOUND/INCOMPLETE/CRASH/TIMEOUT). Nothing on master
changed; `diff-e2e.py --refs` does not rebuild e2e-ref, so a stale reference can show REFDIFF
after a twin bump.

## recoffs2

Lane `recoffs2` continues §4's next steps: the perturbation of the remaining layouts, the whole-record
writers by name, the two compactions, and the stale-reference trap of §6. Helpers `recoffs2-front`
(the front's writers, `ci_at_lps`, the rule and table writers, the `Decl*` cluster) and
`recoffs2-rom` (the ROM reader, then the files the whole-library perturbation found).

### The perturbation: `--scale`

A gap cannot perturb a record that embeds another (§5): the constant record embeds the constant
value, the hint and the caps record, so `CI.cv + CV.size` grows by the gap while the fields after it
move by the gap only, and they overlap. `layout_perturb.py --scale K` multiplies every offset by
`K` instead (a slice's length word stays right after its offset word): linear, so the embedded
records still end where the next field starts. Also new: `--target` (build only some modules and
their imports), `--keep` (leave the perturbed files for `lake env lean`), no cache writes (the
perturbed artifacts are of no use), the log kept in `.lake/layout_perturb.log`.

### Writers of a whole record: the record's image

A positional writer model (`wrER m q [w0, …, w7]`) cannot survive a layout with gaps, and the dead
words of the rule and table records are gaps. The writers are now modelled by the record's *image*:
`L.recImg size fields : List (Option Word)` (`RecLayout/Img.lean`), the value at each field's
offset and `none` elsewhere, and `L.Ind.wrERo` (`IndMaster.lean`), which stores the `some`s and
skips the `none`s. Each layout defines its images (`CV.img`, `CI.defnImg`, `CI.indHdImg`,
`CI.axImg`, `CI.recInfoImg`, `Rule.img`); the one proof per writer that
its stores are the image is computational (`simp [wrERo, …Img, recImg, rec_unfold, UInt64.add_assoc]`:
it re-evaluates for every layout), everything after it goes through `erRecO_stage`/`wrERo_fresh`
(`QuotFns.lean`), the image's get lemmas and the `…RecW` field-word lemma sets (`CVRecW`,
`RuleRecW`, `CapsRecW`). `erRecO_words`: every word of the record's region can be read (the words
between the fields included), for the `RuleWordsIn` facts. Shared writer modules: `RecInfoW.lean`
(the `.recInfo` records of `rec_info_rec` and `class_fe_r_rec`), `axRec_core` in `DeclValsE.lean`
(the fresh `axiomInfo` records of `check_constant_val` and `class_const_ok_lit`).

### L changes (`checker.s` regenerated; verdicts identical)

* `ind_info_rec`'s header: `er_put5(q, 3, EREC⦃cv⦄, EREC⦃cv + 1⦄, …)` (five consecutive words) is
  `er_put_ci(q, 3, cv)`, the kind word and the constant value's fields by name.
* The rule record's dead words are no longer stored by `parse_rule_d`, `rules_at_lps_go`,
  `generated_rule_nested` and `rule_copy` (8 fields, not 11 words).
* Literal offsets left in L text: the constant's name read in `hoist_names_go`, `decl_declares_go`,
  `decl_key` (`+ 1` → `+ ⟪CI.cv⟫`), `idx_tables`' `EREC⦃q + 2⦄` (`ProjTbl.structName`).
* The rule-count guards of `ind_rec_copy` and `ci_at_lps` are `2^57`, not `2^60`: `Rule.size * n`
  must not wrap for any `Rule.size ≤ 64` (the layout's only stated bound), as the ROM reader's.
  Unreachable counts either way (2^57 rule records do not fit in memory).

### `diff-e2e.py --refs` and stale references (§6)

`diff-e2e.py --refs` now builds `e2e-ref` (`scripts/lake build e2e-ref`) when it is missing or older
than `vendor/UPSTREAM` or `pins.bin` (every twin bump rewrites both), and refuses a con-ron whose
build tree (a git checkout, the default `_tmp/ref/con-ron-integrate`) is not at `vendor/UPSTREAM`'s
con-ron revision or whose binary is older than that commit (no cargo here to rebuild it). The main
checkout's `e2e-ref` was in fact stale again when this landed (built 14:29, ronsync5 at 15:29).
