# Lane `cleanup`: dead code and the last `sorry`s

Journal of lane `cleanup` (decisions, measurements, findings). Only this lane edits this file.
Start: master `f9f965b6` (2026-10-24). Goal: no `sorry` in the built modules and the migration's
dead code removed, without changing `ConAgua.Final.checkerFile_accepts_remaining` or the census
(1328 proven, 0 sorry, 1352 targets).

## Method

* **The cone.** A scratch Lean program (`lean --run`, not committed) imports the built modules
  (in groups: the emitters, benches and exe roots each define `main`, so each is imported alone)
  and walks types and values of every `ConAgua` constant from the roots:
  * every constant of `ConAgua.Final.*`, `ConAgua.Checker.AsmFinal`, `ConAguaAsm.*`;
  * every census link (`@[l_impl]`, `@[refines]`, `@[refines_part]`) except the 33 sorry-dependent
    ones (below);
  * every constant of a tool or test module (names containing `Bench`, `Emit`, `Test`, `E2E`,
    `Census`, `Spike`, `Rom.Gen`, `CrossCheck`, `Examples`);
  * every non-theorem whose type mentions elaborator types (`Lean.Elab`, `Lean.Meta`,
    `Lean.Syntax`, `Lean.ParserDescr`, …): syntax, macros, attributes.
  An auxiliary constant (`proof_N`, `match_N`, `eq_N`, `_auto_N`, …) makes its owner live.
  Everything else is dead. A declaration is deleted by its declaration range (doc comment and
  attributes included) only when every owned constant in the range is dead.
* **The 33 sorry-dependent links.** Before the cleanup, 33 `@[refines]`/`@[refines_part]` theorems
  (StageR versions in IndInstallSpec*, IndPartsSpec4, IndPos2Spec*, RecClassSpec*, RecGenSpec*,
  RecCheckSpec*, DeclDivMod5/6/9, DeclCvg, DeclHeader, DeclReduceSpec) had census status
  `local:` (sorry through `stubM_spec` and the other stub contracts). Their targets count as proven
  through the sorry-free StageC links of their callers, so dropping them changes nothing: replaying
  the census report (`census.py --from-output`) on the exe output without these 33 lines gives the
  same table (1328 proven, 0 sorry), only the link count drops (2108 to 2075, parts 181 to 179).

## Log

### Batch 1: the sorry cone (2026-10-24)

* Deleted every dead declaration that depends on `sorryAx` (transitively, over `ConAgua`
  constants): **300 declarations in 102 files, 15032 lines.** Among them the 18 `sorry`'d stub
  contracts (`IndStubs`: `stubM_spec`, `stubM_absOK`, `stubM_memoFrame`, `openPisAtFvarsF_spec`,
  `instLPFast_spec`, `lvlEqStub_spec`, `lvLeqTopStub_spec`, `lvZeroCaps_spec`, `nameRecI_spec`,
  `allLevelParamsDefined_spec`, `constsResolveFFast_spec`, `checkConstantVal_spec`, the four core
  contracts `inferTypeCore_spec`/`ensureSortCore_spec`/`isDefEqCore_spec`/`whnf_spec`;
  `IndInstallSpec39`'s `blockLargeElimAllowed_spec`, `RecCheckSpec12`'s `lvlsEqStub_spec`), the 33
  sorry-dependent census links, and the StageR theorems above them (`cidW_ok`,
  `checkBlock*_refines`, `genRecCheck_refines`, `classRead_refines`, `blockNestCtx_refines`,
  `ctbW_sim`/`ctoW_sim`, …).
* `sorry` outside comments and strings in `ConAgua/`, `ConAguaAsm/`: 18 → **0** (a scanner that
  strips `/- -/`, `--` and string literals).
* Full `ConAgua` rebuild: 25 min wall, `LEAN_NUM_THREADS=4`, no failures (nothing live used a
  deleted declaration as a `dsimp`/`decide` fact). `#print axioms checkerFile_accepts_remaining`:
  [propext, Classical.choice, Quot.sound]. Census: same table, same targets/edges (`T`/`E`/`R`
  lines identical), links = the old ones minus the 33. `asm_file.py --check`, `modules_check.py`,
  `provenance.py check` pass.
* `scripts/census.py`: `e2e_metrics` read `ASM["src"]`, which is absent when the end-to-end theorem
  has no sorry sources (a `KeyError` after the table); now `ASM.get("src", [])`.
