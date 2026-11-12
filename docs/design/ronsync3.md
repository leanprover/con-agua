# Lane ronsync3: the con-ron sync 01ecb31c → 4ca283d1

Lane of 2026-11-11 (Opus), from master `b4ce0391e`. con-ron `01ecb31c → 4ca283d1`, con-leche
`210a580e → eb2c5939`, upstream tasks #149, #150, #151. Starting kit: docs/design/presync3.md §4;
rules: `scripts/sync-rules/ronsync3.txt`. Decided before the lane: `--olean` stays out (D44); the
`IIndCaps` record keeps its 15-word `EREC` layout (the five dropped fields' words unwritten and
unread), the ROM's `encCaps` drops them; every new or rewritten function gets a generated model and
a declarative refinement (exceptions: `pow_nat`, `size_bytes`); no walk tactic.

## 1. Progress log

* 2026-11-11 23:55 start. Report (`_tmp/bump-4ca283d1/report.{txt,md}`): as presync3 §1 (173 L
  items, 698 mentioners / 404 theorems in 213 files; patches con-leche/0001 and con-ron/0002
  conflict in con-leche's `Kernel/Expr.lean`, `Kernel/Name.lean`). Sent to the coordinator.
* 2026-11-11 23:57–00:06 bump (`55d97287a`). `bump-con-ron.sh 4ca283d1` stopped at the two
  conflicts. con-leche/0001 (the `withPtrEq` shim) is still needed: upstream's pointer-first
  equalities (#551, #554) still use `Init.Util`'s `withPtrEq`/`withPtrEqDecEq`, whose shapes our
  toolchain changed; re-made on the pristine `Kernel/Expr.lean`/`Kernel/Name.lean` (the import,
  `ConLeche.withPtrEq`, `withPtrEqDecEq ConLeche.withPtrEq (fun _ _ _ _ => rfl)` at its six call
  sites). con-ron/0002 had not been applied at all (its `Bridge/Core/Arms/DefeqPeel.lean` hunk
  names a file upstream deleted, which makes `git apply` refuse the whole patch): applied
  without that file; its seven conflicts taken from upstream, then the two toolchain fixes the
  build asked for re-done (`IotaMajor`'s `dsimp +instances`, `StructInstall`'s `try replace`).
  ConLeche, ConRonArena, ConRonBridge build (12 threads, a few minutes with the cache).
* 00:06–00:15 stage 3a (`cad634eb6`): the caps (`decCaps` reads `eta`, `nIdx`, `all`,
  `nparams`, `ctors`; the 15-word record and its offsets kept; `encCaps` and `rci_caps` drop the
  five fields), the maximum `Nat` size (`PinsFull.maxNatSize`: `PINS[72]`, the table 73 words
  and frozen so; `intern_reserved_pins` and `intern_all_pins` write `maxNatSizeDefault`), the
  reader's `Except` (`Arena/ExceptOpt.lean`), the size in bytes (`NatCmpFacts.sizeBytes_pv`:
  `8 * ((pv p o l).log2 / 64 + 1) = 8 * max l 1` for a normalised slice). The projection
  table's words for the η readers already have one lemma, `WhnfCoreProj.decTbl_words` (ctor,
  numParams, numFields): no new one.
* 00:16 stage 3b, first part: the rules file's renames applied to the whole tree (statements
  and proofs, citation lines left alone; 33 files), incl. `internAllPins pins
  maxNatSizeDefault` in the final definitions (see §3).
* 00:17–00:40 stage 3b/3c on the partial tree, three build rounds. The pipeline at the default
  maximum: `PinsReadyP` also says `a.pins.maxNatSize = maxNatSizeDefault`
  (`internReservedPins_maxNatSize`), so the twin's first write in `internAllPins` is a no-op on
  every state we run it from (`SimZ.getSet`; `internAllPins_steps`/`_pins`/`_tail`/`_u` take it as
  `hmax`, `prefix4_facts` exports it) and `intern_all_pins` writes nothing (`PINS[72]` holds the
  default since `intern_reserved_pins`). Theorem 1's lemmas lost the set theory (#521):
  `view_foldOK`, `job_spec`, `pooledAccepts_bridge` are called without it. The theorems about
  removed twin functions deleted: the `instantiate1Lift` walk's (`WalkLiftRefine`), the
  `towerSlotsAll` ones (`WhnfProjRefine3` whole, `WhnfIotaRefine2`, the knot's `StuckCallees`
  field). Ladder: 2 rounds, 28 failing theorems, **0 closed** at rungs (i)–(iii), 28 tickets
  (`_tmp/ronsync3/tickets-r1.tsv`). Why so few: of 4 388 modules all but 8 elaborate after the
  bump with the old L code — the old proofs still hold of the old L code against the twin's
  unchanged callees; what breaks is where a proof unfolds a changed twin definition (8 modules) —
  and the ladder's rungs only help a theorem whose statement we restated (none of these). The
  real work is the L port of the changed functions, which then breaks their refinements: that
  goes with the fan-out (below), since each helper owns the L code and the proofs of its area.
  Blocked still: 18 modules behind `WhnfM2CRefine` (the old η models) and `KnotMono1` (the store
  monotonicity list: removed twin functions).
* 00:43 fan-out: helpers ronsync3-decl (#493, #494), ronsync3-ind (#495, closers, opener, the
  projection guard), ronsync3-core (#515, #519, #520, KnotMono), on presync3 §4's file sets,
  brief `_tmp/ronsync3/brief-common.md`, 3 build threads each (lead 3).
  **Deviation from presync3 §4's order:** the L code of the rewritten functions is ported by the
  helpers, not before the ladder by the lead: the new L functions do not exist before the port,
  so their statements cannot be restated earlier, and the ladder has nothing to try on them.

## 3. Statement changes of the final theorems

1. **The maximum `Nat` size** (upstream #519: `internAllPins` takes the run's maximum). The
   definitions `TwinAccepts` (Final/Twin.lean), `TwinAcceptsPooled` (Final/TwinPooled.lean),
   `twinRun`, `TwinVerdict`'s and `TwinVerdictPooled`'s stage lists (Final/TwinVerdict.lean).
   Before: `internAllPins pins sD = .ok (ipins, sE)` (and `internAllPins pins >>= …` in
   `twinRun`). After: `internAllPins pins maxNatSizeDefault sD = .ok (ipins, sE)`. Pending the
   user's `--max-nat-size` decision (coordinator): if the flag is ported the maximum becomes a
   parameter of these definitions instead.
2. **No set theory in the accept and verdict theorems** (upstream #521: con-ron's Theorem 1 for
   the pool, `Arena.pooledAccepts_bridge`, and `view_foldOK`/`job_spec` became model-free; approved
   by the coordinator 2026-11-12). Removed `(V : Type w) [ConLeche.SetTheory V]` (`Vt`/`Type u`
   alike) from: `checkerFile_accepts`, `checkerFile_accepts_regs`, `checkerFile_threads_accept`,
   `checkerFile_threads_regs`, `checkerFile_threads_verdict` (Final/EndToEnd.lean),
   `threadsRun_twinAcceptsPooled`, `threadsRun_twinAcceptsPooled_regs` (Final/ThreadsFinal.lean),
   `checkerFile_threads_verdict_of`, `threadFail_twin` and the claim `ThreadEVerdict`
   (Final/ThreadsVerdict.lean), `checkerFile_drv_accepts_regs`, `drvAccepts_twin`
   (Final/DrvFinal.lean), `twinAccepts_pure`, `twinAcceptsPooled_pure`; internal:
   `seqVerdicts_proved`, `entry2Verdict_of`, `checkJobs_seqE`, `checkB_seqE`, `checkMode2_seqE`,
   `threads_twinVerdictPooled`, `threads_twinAcceptsPooled`, `checkJobs_seq(T)`, `checkB_seq`,
   `checkMode2_seq`, `drv_twinAccepts`, `worker_foldOK`, `pool_walk`, `pool_prefix`, `pool_twin`.
   Before, e.g.: `theorem checkerFile_accepts [Host] (V : Type w) [ConLeche.SetTheory V] (k0 : Nat)
   (hcode : Code checkerFile k0) (b pb : ByteArray) … : Ev (…) dm (label abiStartL)`. After: the
   same without `(V : Type w) [ConLeche.SetTheory V]`, the conclusion unchanged. Kept (their
   proofs build the model): `twinAccepts_model`, `twinAccepts_no_False`, `twinAcceptsPooled_model`,
   `twinAcceptsPooled_no_False`, `checkerFile_model_exists`, `checkerFile_no_False`,
   `checkerFile_threads_model`, `checkerFile_threads_no_False`, `twinAccepts_not_trivial`. This
   undoes ronsync2's statement change 1, 2 and 5 (docs/design/ronsync2.md §6).
* 00:45–01:45 the helpers port their areas; the lead merges their building milestones into
  `ronsync3` and runs compile passes (build, then the ladder `--write` on every failing file, so a
  failing theorem becomes a ticket for its owner and the modules behind it unblock; positional
  `decCaps` destructurings fixed in 9 files; `rci_caps`' refinement (`CIReadRefCaps`) at the
  five-field caps by the lead). A lesson for the ladder: run it only after a build of the merged
  tree — at stale imports it elaborates against old `.olean`s, finds the merged proofs failing
  and writes `sorry` over them (round 4 did, reverted).
  Decisions: the Nat refusals travel from the `nvFns` arms as masked sentinel handles to
  `reduce_nat_op`/`reduce_nat_succ`, which fail with the twin's message (core, D45);
  `check_decl`'s reserved-names half: mirrors the twin's order (`check_decl_kind`, the flush,
  `basis_names_ok`), the twin-side facts after `checkDeclKind` come from upstream's
  `checkDeclKind_bridge` (`DeclKindSpec`), the L-side relation at the end state is rebuilt at
  `cd_ref` with the environment clauses of `StoreDen` from a twin-level lemma per arm
  (`DeclKindEnv`; the `.indDecl` arm's, `IndKindEnv`, by the lead). Reason rows for the 16 new
  twin messages (`reasons.py --add`).
* 01:45–02:15 compile passes on `ronsync3` (the ladder's sorries plus crude deletions of the
  theorems about removed twin functions in core's files, which `ronsync3-core` then replaced by
  its own versions at merge), and `IndKindEnv` proved by the lead
  (`Arena/IndKindEnvProof.lean`, 470 lines: the growth algebra over `EnvGrowDen`, the stages'
  returned environments by peeling their runs (`checkBlockPass_env`, `genRecCheck_env`,
  `checkBlockTail_env`: the generated recursors' temporary pushes popped, upstream's
  `classFeR_pop`/`consBlockRecsTemp_pop`), then con-ron's `checkBlock_bridge` steps repeated with
  the environment kept (`checkBlock_grow`)). Helper milestones merged: ind 2 (all L code of its
  area mirrors the twin), core 748d0feab (all L ports; ~25 sorries left), decl (the reader, the
  basis names' models, the one-constant arms at `checkDeclKind`).
* 02:20–02:35 the first core and ind helpers ran out of context (core: all L ported, 19 sorries
  and the new certificates' refinements left; ind: all L ported, `cb_ref`, the projection guard's
  `pgr_okH`, `IndT/TailRef` left). Second sessions started on the same branches and worktrees
  with written hand-overs (`_tmp/ronsync3/{core,ind}-handoff.md`). The generated program
  (`Checker/Prog*.lean`) waits for core's `DefEqBaseE`/`DefEqKnot` to build (`checker_prog.py`
  needs every module).
* 02:35–02:50 program regenerated (`checker_prog.py`: 1790 functions, 0 stubs; two name clashes
  between modules had to go first, the dump imports every module together), the generated
  function lists (nv/core/loop/leaf/phaseb, preloop-ws), `import all ConAgua.Arena.NatSized` in
  the six closure checks that unfold the program (a missing `import all` of a module with
  `@[no_expose]` functions shows only as a kernel "application type mismatch" in `prog_all`),
  `checker.s`/`pins.bin`. **First verdicts** (`diff-e2e --tests` at con-leche eb2c5939,
  sequential): 725 of 730 agree; the 5 others are the `nat_size_limit_*` fixtures that con-leche's
  `E2E_FLAGS` run at `--max-nat-size=16` — at the default maximum con-ron 4ca283d1 accepts them
  too, so every verdict is the twin's at the default.
* 02:50–03:10 milestones merged: core (the whole Nat area at 0 sorry; left: the binders' and
  stuck certificates' four refinements and the new certificates'), ind (its area at 0 sorry: the
  projection guard `pgr_okH`, `cb_ref`, `TailRef`; L: `proj_guard_rows_at` aborts where `np + i`
  wraps (deviation row), a capacity check in `proj_guard_rows`), decl (`cd_ref`/`cdk_ref` at the
  twin's order with `DeclKindSpec` and `indKindEnv`, the basis names' refinements; `check_decl`'s
  computed abort replaced by one `fail` per reason code, since `l_model` cannot take the
  `abort (.var k)` splice). The per-function write-set checks found the new guard calling the
  `hb` memo walks directly (they write `CTL[214‥215]`, which the inductive memos' and the core
  stage's frames exclude): ind makes them leaves, with their frame lemmas.
* 03:10–04:00 the helpers finished (decl, ind 2, core 2: zero sorry in their areas) and stopped;
  their worktrees removed. Integration by the lead: two more name clashes for the program dump
  (`pgP`/`pgA`/`pgFns`/`pgC`), the program, lists and `checker.s` regenerated again, the
  write-set lists closed under the new callees (found per function with `#eval
  (checkerProg.filter (! CHK ·)).map (·.1)` against each `prog_all`, then the callees outside
  the tree): `IndArmFns` (the closers' `…_go`, `nat_*_at_cv`, the reader's three tests,
  `strip_pis`, `sl_snoc`, the guard's functions), `biFns`, `declExtFns`, `litShapeFns`, `cdFns`;
  the `hb` memo's two queries as leaves of the arms that reach the core (`ArmMemos.hlLeaf_*`,
  `usLeaves`), the dead `reserved_contains_w` program fields removed, `FreezeTrunc` at the
  73-word pin table, `ThreadEVerdict` without its universe. **04:00: the whole library builds,
  zero `sorry`, the axiom guards unchanged; `provenance.py check --strict` clean.**
