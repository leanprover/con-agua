# Lane syncvocab: the vocabulary files (reproof.md rec. 2)

Lane of 2026-11-10 (Opus), the brief of `docs/design/syncproc.md` §5, from master `86737151d`
(ronsync2 landed as #235). A proof refactor: no L change, and no statement of a final or
refinement theorem changed. Lemmas moved with their names unchanged; two new lemmas
(`IWOK.frameG`, `IWGrow.of_keepG`, grind forms beside the old ones) and four aliases deleted.

## 1. What moved where

**`ConAgua/Arena/ErecVocab.lean`** (new, 32 declarations): the two-tier record pool. It imports
`ErecRd` (so `Env`, `Tiers`) and is imported publicly by `IndIface`, so every file that sees `IWOK`
sees it. Definitions moved in (they could: no cycle): `erA` (`IndIface`), `erTop` (`IndIface`),
`erRd` (`IndLibSpec`), `erecPutMem`, `erOff`, `erTier`, `erTopOf` (`IndIface`). Lemmas:

| from | lemmas |
|---|---|
| `IndIface` | `mask40_toNat`, `tierA_EREC`, `nat_and40`, `erecPutMem_arr`, `ctl_ne_erTier`, `erecPutMem_ctl`, `erecPutMem_grow`, `erecP_putMem_self`, `erecP_putMem_other` |
| `IndLibSpec` | `erRd_of_erecP`, `erRd_of_erA` |
| `IndPosSpec/NestBlockOfKey` | `erRd_get` |
| `DeclNatGate`, `IndPartsSpec/Bs` | `erRd_foldN`, `erRd_fold` (the same fact under two names; both kept) |
| `DeclRec` | `erecP_getE`, `erecP_lt` |
| `IndMaster` | `erecPutMem_frame`, `erRd_add`, `erRd_erecPutMem_ne` |
| `IndT/StreamRecsRules`, `RecCheckSpec/ErToIwWStage`, `IndRealIpo` | `erRd_natA`, `erRd_nat`, `erRd_of_nat?` (the last two are one fact) |
| `DeclDivModSpec/DivModTypePins` | `erecTop_lt` |
| `Rom/PinSets` | `erecPutMem_lo` (namespace `L.Rom` kept) |
| `ErecRd` | `ld64_rdT_spec` |

Left where they are: `aread`/`aread_apply` (`EnvRec`: `ErecRd` and `InitLink`, below the
vocabulary, use them), `erecP` and its tops (`Tiers`), `erecP_lt64`, `erecP_ownSet`, `erecP_tblSet`
(`Env`), `erRdT` and the `RdOK` readers (`ErecRd`): the definitions' own files. Lemmas about a
particular writer (`erRd_wrER_ne`, `ownC_erecPutMem`, `erRd_allocMem`, the `PinReadSpec`
`erecPutMem_*`) stay with the writer. `erRd` and `erRdT` are one read under two names, as are
`erTop`/`erecTop`; a later rename is one `rename` rule.

The brief's test, "no file outside the vocabulary and the definitions' files proves a fact about
`arr64 EREC`": 312 occurrences in 92 files before, 297 in 84 after. What is left is mostly not
pool vocabulary but statements over the tier-0 array: the ROM's relations (`Rom/PinSets` 71,
`DivModTypePins` 12, `CIReadRefBase` 10, `BlockRecLpsOk` 11) state `PinSetR`, `SliceR`, … over
`m.arr64 EREC`. Moving them behind `erecP` changes those relations' statements (out of scope
here; it is the reader-API half of reproof.md (a) for the ROM).

**`ConAgua/Arena/IWFrame.lean`** (new, 15 declarations), imported publicly by the files the
lemmas came from: `IWOK.frame` (`DeclBase`, namespace `L.Arena` kept), `IWOK.of_iw`,
`IWOK.of_keep`, `IWGrow.set_iw`, `IWGrow.set_top` (`IndLibSpec`), `IWOK.frameC` (`HbMemoRel`),
`IWOK.of_er` (`IndMaster`), `IWGrow.of_frame` (`StructElimLevel`), `IWGrow.put` (`QuotFns`),
`iwGrow_of_frame` (`IndCopy2`; both helpers asked for it), `erRd_lo` (`DivModTypePins`),
`erRd_set_iw` (`IndCopy2`), `erecPutMem_iw` (`SumRules`). `IWOK`, `IWOK_iff`, `IWGrow.refl`,
`.trans`, `.erecGrow`, `.ext`, `.of_keep` stay beside the structures in `IndIface` (used there).

**Aliases deleted**: `IWGrow.erecExt` (`DeclCvg`), `IWGrow.erecPExt` (`DeclStepSpec`),
`IWGrow.erecPExtR` (`DeclRec`), `IWGrow.erExt` (`IndDecStab`); their 58 uses are now
`L.Ind.IWGrow.ext`. `IWGrow.of_keep` and `IWGrow.of_frame` are one fact (the `C` premises in
another order) and both stay; so are `iwOK_reset` (`DeclCvg`) and `IWOK.reset` (`Jobs`), the same
statement (helper B).

## 2. Positional `IWOK`/`IWGrow` outside their files

Found by scanning the compiled proofs (all 1400 built modules loaded at the private level) for
the constants `IWOK.mk`, `IWOK.casesOn`, `IWGrow.mk`, `IWGrow.casesOn` and `IWOK_iff`: 65
declarations in 47 files on master. A text grep (`IWOK|IWGrow` with `⟨`) gives 344 lines, nearly
all tuples that merely contain `IWGrow.refl _`. Two helpers (disjoint file lists, branches
`syncvocab-a`/`-b`) and the lead rewrote them:

* 21 `obtain ⟨h1, …⟩ := hS.iw` became field projections (`hS.iw.iwSize`, `.ctl`); about 30
  destructured facts nothing used were dropped;
* 18 constructions became structure instances with field names (`{ iw := …, er := …, … }`);
* 15 became an IWFrame lemma: `IWOK.of_iw` (the resets), `IWOK.frameC` (`pPrepCore_ok`'s three
  nine-field blocks, `HEnv.frame`, `iwok_frame`), `IWOK.of_er`, `IWOK.of_keep`/`IWGrow.of_keep`
  (`iwKeep`, `StageT.of_heap`, `iw_of_hbFrame`, `StageT.ctl136`), `IWGrow.of_keepG`,
  `IWGrow.set_iw`, `IWGrow.put`;
* 1 by `grind [IWOK_iff, iwTop, erTop, erecTop1, …]` (`IWOK.set130`).

Left: `IWOK.fresh`, `IWOK.trunc`, `PEnv.frame` go through `IWOK_iff` as a whole conjunction
(`simp … at h ⊢; exact h`), name no position, and no frame lemma fits (`freshMem` writes tier 1,
`truncFrozen` changes `EREC`'s size, `PFr` is not a `MemFrame`). The rescan after the merge finds
`IWOK.mk`/`IWGrow.mk` only in those structure instances.

Helpers' parser notes for structure instances: a field `iw := by tac,` needs parentheses,
`iw := (by tac)`, and continuation lines must start at or right of the first field's column.

## 3. Attributes

**Does `vcgen` read a spec attribute set?** (toolchain `nightly-2026-10-20`, read in
`Lean/Elab/Tactic/VCGen/Frontend.lean` and `Lean/Elab/Tactic/Do/Attr.lean`, ~20 min.) Yes, one:
the global `@[spec]` set (`getSpecTheorems`, a `SimpleScopedEnvExtension`), seeded into every
`vcgen` call; an equation or definition tagged `@[spec]` becomes a rewrite spec. There are no named
sets, but a *scoped* `@[spec]` is one: `attribute [scoped spec] …` in a namespace is active only
under `open scoped` that namespace. Measured on `headTypeConst_spec` (`PropReadW`), with
`ld64_rdT_spec, evalE_tld, tld, evalE_tagE, evalE_idxAE, evalE_idxGE` dropped from its `vcgen`
list: "No spec found for program ld64"; with `open scoped L.Arena.ErecSpec`: closes. Tactic level
works too (`open scoped L.Arena.ErecSpec in vcgen [...]`), but not inside a `sym … =>` block (grind
mode does not parse `open … in`): there it goes before the `sym` line. A global `@[spec]` on
`ld64_rdT_spec` was not taken: it would reach every `vcgen` in ~800 importers (and `ld64` is also
passed for unfolding in many of them). So the vocabulary exports the scoped set
`L.Arena.ErecSpec` (in `ErecVocab`) instead of a macro list.

**Grind sets** (all in the vocabulary files; `finish`'s default set untouched, no `@[grind]`):

| set | members | note |
|---|---|---|
| `arena_grind` | `erRd_get`, `erecPutMem_ctl`, `aread_apply` (`=`) | `erRd_get` closes `brw_spec`, `brg_spec` at rung (i) |
| `erec_grind` (new, `ErecGrindAttr.lean`) | `erRd` (its definition) | opt-in: costly in `arena_grind` (§4) |
| — | `erRd_foldN` in no set | costly in `arena_grind` (§4) |
| `ind_grind` | `IWOK.frameG`, `IWGrow.of_keepG` (`grind_pattern` on `MemFrame A C m m'`, with `IWOK m`), `IWOK.of_iw` (on `MemFrame [IW] [200] m m'`, `IWOK m`), `IWGrow.refl`, `IWGrow.trans` (on `IWGrow m₁ m₂, IWGrow m₂ m₃`), `List.mem_cons`, `List.not_mem_nil` | `grind` cannot run `by decide`, so the grind forms take the side conditions `IW ∉ A`, … as hypotheses, which grind decides on a literal list with the two `List` lemmas |

`IWOK.frame` (defaulted `:= by decide` premises) and `IWGrow.of_keep` (one conjunction) keep their
statements; the grind forms are new lemmas beside them. Checked: `grind only [ind_grind]` closes
reproof's frame goals (`IWOK` across `MemFrame [DECL] [0]`, `IWGrow` across a three-word frame, a
three-step `IWGrow` chain, `IWOK` across `MemFrame [IW] [200]` with the room, `IWGrow m m`), the
file in 0.8 s. The attribute modules are public imports of the vocabulary files, so a proof that
names a set needs no import of its own (the hook's variants failed with "Unknown constant
`ind_grind`" in `StripTeleSpec` and `PrepRef` before).

## 4. Cost

The 20 modules with the longest elaboration (this branch's build log) among those that import
the vocabulary and use `vcgen` and a grind set (`arena_grind`/`ind_grind` in a `grind`/`sym`/
`finish`); `perf stat -e instructions:u` of `scripts/lake env lean -DautoImplicit=false
-DrelaxedAutoImplicit=false F.lean`, `LEAN_NUM_THREADS=1`, 3 runs, median, in G instructions.
"before" is master `86737151d`; "first" the branch with `erRd` and `erRd_foldN` in `arena_grind`
(`7f12175fc`); "after" the final sets (`1cf466dfc`, the call-site cleanup merged). Run-to-run
spread below 0.4 G except NcGoW (2.8 G).

| module | before | first | after | after vs before |
|---|---:|---:|---:|---:|
| `Verdict.IndBGrpM` | 198.9 | 198.9 (+0.0 %) | 198.9 | +0.0 % |
| `Arena.IndPosSpec.NcGoW` | 392.0 | 391.4 (−0.2 %) | 390.6 | −0.4 % |
| `Checker.Prelude` | 149.8 | 149.8 (+0.0 %) | 149.8 | −0.0 % |
| `Arena.DeclCanonSpec` | 231.5 | 250.2 (+8.1 %) | 231.5 | +0.0 % |
| `Arena.DefEqModels` | 112.8 | 112.8 (+0.1 %) | 112.8 | +0.0 % |
| `Arena.DeclCanonExpr` | 115.2 | 115.2 (+0.0 %) | 115.2 | −0.0 % |
| `Verdict.WhnfModels7E` | 111.8 | 112.7 (+0.8 %) | 111.9 | +0.0 % |
| `Arena.DeclNatOpEq` | 117.6 | 117.6 (+0.0 %) | 117.6 | +0.0 % |
| `Arena.RecClassSpec.ClassNPcOf` | 100.2 | 192.0 (+91.5 %) | 100.4 | +0.2 % |
| `Arena.DeclNatDeps` | 121.4 | 121.3 (−0.0 %) | 121.3 | −0.0 % |
| `Checker.Hoist` | 160.2 | 160.2 (+0.0 %) | 160.2 | +0.0 % |
| `Arena.InstLPWalkGo` | 76.7 | 76.7 (+0.0 %) | 76.7 | +0.0 % |
| `Arena.RecClassSpec.CrW` | 127.8 | 135.9 (+6.3 %) | 127.9 | +0.1 % |
| `Arena.InferBodyBindPiModels` | 68.3 | 68.3 (+0.0 %) | 68.3 | +0.0 % |
| `Arena.QuotRecW` | 116.3 | 116.8 (+0.4 %) | 116.3 | −0.0 % |
| `Arena.IndSumSpec.McGoStep` | 91.9 | 91.9 (+0.0 %) | 91.9 | +0.0 % |
| `Arena.IndPosSpec.FgW2` | 79.4 | 79.4 (+0.0 %) | 79.4 | +0.0 % |
| `Verdict.WhnfModels2E` | 80.6 | 80.6 (+0.1 %) | 80.6 | +0.0 % |
| `Verdict.UnresolvedE` | 119.7 | 119.6 (−0.0 %) | 119.6 | −0.0 % |
| `Verdict.DeclValsE` | 68.3 | 68.9 (+0.8 %) | 68.3 | +0.0 % |
| **total** | **2640.3** | **2760.3 (+4.55 %)** | **2639.3** | **−0.04 %** |

The first sets broke both limits (total +4.55 %, ClassNPcOf +91.5 %). Bisected by erasing one
rule at a time in a scratch copy of the module (`attribute [-arena_grind] …`): ClassNPcOf 191.9 →
100.1 G without `erRd`'s unfolding (every `erRd` term unfolds into the tier read, on which the
`rdW` rules then fire); DeclCanonSpec 250.1 → 231.5 G without `erRd_foldN` (its `rdW (… tierA EREC
…)` pattern matches every tagged read, which DeclCanonSpec has in bulk through `erRdT`); CrW
needed both out. Narrowed: `erRd`'s unfolding is its own set `erec_grind`, named only by the proofs
that compare a model's `erRd` with loads (`finish [erec_grind]`, the hook's `sets+` variant), and
`erRd_foldN` is in no set (it stays a lemma to name). The `ind_grind` frame patterns cost nothing
measurable here.

## 5. The ladder hook and the sample

`scripts/sync-rules/vocab_attr.py` (`candidates(proof, ctx)`), variants in order: `sets`
(`arena_grind` added to every `grind`/`sym`/`finish` list that lacks it, and to a bare `finish`),
`sets+` (also `erec_grind`), `specs` (`sets+`, and `open scoped L.Arena.ErecSpec in` before every
tactic line that starts with `vcgen` or `sym`, not inside a `sym` block), `iwok` (a positional
`obtain ⟨h1, …⟩ := X.iw`/`.ok`/`.iwok` becomes `have hIWOK := X.iw`; the k-th destructured name
becomes `hIWOK.<k-th field>`, which is right as long as new fields are appended, as ronsync2's
were; an all-holes `refine ⟨?_, …⟩` with its bullets or an `exact ⟨…⟩` that builds the `IWOK`
becomes `grind [IWOK_iff, ind_grind, iwTop, erTop, erecTop1]`), then the rules file's own `[vocab]`
sections (a hook replaces them in the ladder, so the hook runs them last). PLAN.md, "Bumping the
twin" 3c, now says to name it.

Sample line (reproof.md §3's 64 theorems, replay mode, base `09a78343a`, ronsync2's codemod,
`--jobs 4`), on master and on this branch:

| rung | master `86737151d` (ronsync2's `[vocab]` text rules) | this branch (the hook) |
|---|---:|---:|
| (i) master | 19 | 26 |
| (ii) codemod | 11 | 11 |
| (iii) vocab | 5 | SAMPLE_VOCAB |
| cumulative | 19 / 30 / 35 | SAMPLE_LINE |

RESULT_PROSE

## 6. The next sync's rules file

`scripts/sync-rules/<sync>.txt` names `vocab_hook vocab_attr.py`. Its `[codemod]` keeps the
sync's own renames; its `[vocab]` sections only what the sets cannot say (a dropped premise,
`rw` → `simp only` at a fold). A sync that moves another encoding first gives it a vocabulary file
with its sets (as `ErecVocab`/`IWFrame`), then adds the set to `SETS` (cheap) or `SETS_PLUS`
(unfoldings) and its scoped spec set to `SPEC_SCOPES` in the hook, and measures the 20 largest
importers as in §4 before landing. The rename rules for the duplicate names this lane left
(`erRd_fold` → `erRd_foldN`, `erRd_of_nat?` → `erRd_nat`, `IWGrow.of_frame` → `IWGrow.of_keep`,
`iwOK_reset` → `IWOK.reset`, `erRdT` → `erRd`, `erecTop` → `erTop`) are candidates for that
sync's `[names]`.
