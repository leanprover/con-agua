# Lane `pipeline`: `PipelineRefines checkerProg`, the top-level glue

Goal: prove `PipelineRefines checkerProg` (`Final/Statement.lean`), so that `checker_x64_accepts`
holds for the real checker. Scope (coordinator, 2026-10-23): items 1–6 and 13 of loopt2's list
("`PipelineRefines checkerProg`: remaining obligations", `docs/design/loopt2.md`); items 7–12 are
loopt2's, item 14 the stub owners'.

## The composition (landing 1)

`ConAgua/Checker/Pipeline.lean`, `ConAgua/Checker/PipelineProg.lean`.

* `StageSpec p f Pre Post`: a returning call of `f` keeps the caller's locals and takes memory
  satisfying `Pre` to memory satisfying `Post r` (an implication inside the post, both sides
  predicates on the memory only). `check_of_stages`: from the eight stage specs, a run of `check`
  from `Q0` that returns `ACCEPT` gives `T`. One `vcgen` over `checkL`, posts are implications
  between named predicates; `grind` chains them, the `return 1` path is closed by `simp` on
  `Sig.retVal`. Elaborates in about a second.
* The stages proper are stated relationally (`RelSpec`: a precondition on the memory before the
  call, `∃` the twin's step and the next relation after it), over the five relations between the
  stages (`PipeRels b pb s8 s64`: `R1` after `cap_check`, `R2` after `pb_check`, `R3`‥`R7` after
  each twin stage, carrying the twin's state and the values later stages read: the prelude index,
  the parse result, the prepared records, the interned pin list). Named hypotheses: `CapStage`,
  `PbStage`, `IrpStage`, `PreludeStage`, `FrontStage`, `PrepareStage`, `PinsStage`, `LoopStage`.
* `Q3`‥`Q7` thread the twin's prefix (`∃` the earlier states and values, the stages so far ran
  from `AState.init EStore.empty`); `StageSpec.of_rel` turns each relational stage into a
  `StageSpec` between them. `pipelineRefines_of_stages`: the eight stages, at any `ρ`, give
  `PipelineRefines p` for a `p` with `check ↦ checkL`; `pipelineRefines_checkerProg` at
  `checkerProg`.
* `LoopStage` asks for `SeqAccepts` (phase B on the phase-A state's *worker*), not
  `installThenCheck` (phase B on the phase-A state itself): the gap is loopt2's item 12a.

## The prelude on the shared parse state (landing 2)

`builtin_prelude` used to run a renamed copy of the frontend on arrays of its own (`PRE` for the
bytes, `PNID`‥`PESP` = 208‥213 for the id tables, `CTL[241‥249]` for their words, renamed by
`preA64`/`preIx`/`preCtl`), with its records left in `DECL[0‥P)`. Proving that copy refines
`parseBytes preludeText` would have needed a simulation under a permutation of arrays *and* of
words inside `CTL` (shared with every store), with a side condition on every dynamic `CTL` index;
and `front_run`'s refinement assumes an empty `DECL`. Also `PNID` = 208 collided with `MCM` = 208
(the inductive walks' memo, `IndIface.lean`), which `LoopT` requires zero at the loop's start.

Now (`Checker/Prelude.lean`):

* `preFn` renames only the input: `ld8 0 i` → `ldc preludeBytes i`, `len8 0` → `preludeLenW`. The
  copies are the functions reachable from `front_run` that read the input or call one that does
  (110, `preNames`); the others (`preShared`, generated) are called unrenamed. No `PRE` array, no
  copy loop.
* `builtin_prelude`: `pre_front_run` on the stream's own (still empty) parse state, then the
  prelude's records `DECL[0‥1+8P)` copied to the new array `PDECL` (209), then `front_reset`
  (`DECL[0] := 0`, the id tables' dense sizes `CTL[70‥72] := 0`, their sparse maps cleared by
  `memoClearG (spS b)`). So `front_run` starts from `StateD.blank` as in `frontAll_refines`.
* `prepare_prelude` starts with `prelude_join` (the stream's records shifted up by `P`, `PDECL`'s
  copied below them, `DECL[0] := P + ns`), then the old algorithm.
* The simulation (`Checker/PreludeSim.lean`, `preSim`, statement only): a returning run of
  `pre_f` from `s` is a returning run of `f` from `s.setIn preIn` (byte array 0 := the prelude's
  bytes), same results, final state `setIn` the same; `preSim_triple` turns `front_run`'s spec
  into `pre_front_run`'s. Program shape `PreSimProg p preTree S`.
* e2e (`_tmp/e2e/pipeline`, not written to `docs/e2e.md`): `check` 407 agree-accept, 3
  agree-reject, 262 agree-reject (L aborts), 2 agree-timeout, 1 ref-memout, no disagreement
  (master's last report: 405 and two `hoist_ok` l-errors, which master had already fixed).
  `nb 2` (no `PRE` byte array any more).

## Prelude records stay in `DECL` (landing 3)

Landing 2's `PDECL` (records moved out after the prelude's parse) left one gap: `front_run`
appends to the pool `DLP`, which the prelude's records in `PDECL` point into, and nothing in the
frontend's refinement says it keeps `DLP` below the old top. So, second version:

* `builtin_prelude`: `pre_front_run`; `CTL[240] := DECL[0]` (the prelude's count, as before
  landing 2); `front_reset` resets only the id tables. `DECL[0‥P)` keeps the prelude's records,
  the stream's parse appends after them. `PDECL`, `prelude_join` (and front4's recursive
  `prep_shift`/`prep_join`, `PrepJoinRef.lean`) are gone; `prepare_prelude` reads
  `np := CTL[240]`. Deviation D31 rewritten. Memory map: `CTL[240]` row instead of `PDECL`.
* Twin side, `Front/DeclsPre.lean`: con-ron's parse only pushes to `decls`, so
  `applyLine (st.pre D) r = preL D <$> applyLine st r` (`applyLine_pre`; by `rfl` for the readers,
  `simp` for the arms; `StateD.pre D st` prefixes `decls` by `D`).
* `Front/FrontPre.lean`: `frontAll_refines_pre` / `frontAll_refines_chunks_pre`: `front_run` from
  `StateDR m (StateD.blank.pre D)` ends in `StateDR m' (st'.pre D)` with the twin's
  `parseChunks [b]` from its own blank state. The driver framework (`runI_refines`) is generic in
  its invariant; the invariant is `FrontInv` with `StateDR` on the prefixed state and `TwinOK` on
  the twin's own; `front_init`'s refinement repeated with `decls := D`.
* front4's `preparePrelude_refines` (`PrepRef.lean`) adapted: its core (`pPrepCore_ok`) already
  worked on `DECL` = prelude ++ stream; it now reads `np` from `CTL[240]` (hypotheses: `DECL`
  holds `pre.decls ++ ds`, `CTL[240] = pre.decls.size`).

Helpers (merged): `preSim` proved (`PreludeSim.lean`; `PreSimProg` gained a `defined` field: a
copy's original must be bound) and `checkerProg_preSim` (`PreludeSimProg.lean`, per-function
`simChk` over `prog_all`, copy bindings found by evaluation and checked by one `rfl` each, 18 s,
3 GB). `front_run` at `checkerProg`: the bundles do not hold at `checkerProg` (it binds no
`validate`, `str_put`, `apply_ind_line`: unreachable), so instead `checkerProg` agrees with
`frontAllProg` on the 267 functions reachable from `front_run` (`FrontProgAgree.lean`, 23 chunks
of 12 `rfl` lookups, `Elab.async false`: 264 s, 4.2 GB; in parallel it passed 7.8 GB) and they are
call-closed, so `invoke checkerProg … "front_run" = invoke frontAllProg …`
(`checkerProg_front_run`, `FrontProg.lean`). ROM side (`RomProg*.lean`): `checkerProg_irp`,
`checkerProg_pinProg` (∀ buffers), `noSt8`, `noSt8PB`, the stage theorems at `checkerProg`;
loaded memory (`RomProgInit.lean`): `arenaD_loadMem`, `stateDR_loadMem`, `rsetR_loadMem`;
`capCheck_spec` (`CapCheck.lean`, by induction over the `foldr`).

`cap_check` now bounds every word array by `2^62` (the inductive lines' scratch arrays need it)
and requires `DECL`, `DLP` non-empty (`StateDR`'s count words). `len64` is the size mod `2^64`,
so `PipelineRefines` gained the premise `∀ n ∈ s64, n < 2 ^ 64`; `checker_x64_accepts` derives it
from `Layout.Ok.end64` and `MemRel` (its own statement is unchanged).

`LoopStage` now also gets the twin's prefix (`TwinPrefix`), so `stages_frame` gives the fold's
start invariant there.

## The stages assembled (landing 4)

`pipelineRefines_checker (h8 : LoopStage checkerProg checkerRels) : PipelineRefines checkerProg`
(`Checker/PipeFinal.lean`). The seven stages before the loop are proved at `checkerProg`
(`PipeStages.lean`: cap/pb/irp; `PipePrelude.lean`: `builtin_prelude`; `PipeRest.lean`:
prelude, front, prepare, pins), **sorry-free** (`#print axioms pipelineRefines_checker`: propext,
Classical.choice, Quot.sound). `front_run` also keeps `RecOK` of every record and
`WalkableDecl` of every parsed record, which `prepare_prelude`'s refinement needs
(`L.Front.frontRunOK_checker`, `Front/FrontPreOK*.lean`, helper `pipeline-recok`: the invariant
`FrontInvOK`; one line changes `DECL`/`DLP` only above the old count/top (`DGrow`), its handle
words are table reads below `2^32`, a block's pointers decode to non-axioms so are nonzero;
walkability is twin-only, `applyLine_decls`).

The relations (`checkerRels`), all over `l = loadMem b pb s8 s64`:

* `Since l m pb`: `Keep l m` (bytes and sizes; the program has no byte store), `CapsOK l`,
  `PbPre pb`, `MemFrame preLoopA preLoopC l m` (everything else is still `l`'s zeros: what
  loopt2 needs for the loop's zero memos).
* `R1`/`R2`: `m = l` and the capacities / pin-data prefix.
* `R3` (after irp): `Since`, `ArenaD`, `StateDR m blank`, `RsetR`, `stkTop = 0`, `PinsFull`,
  `pinW m 0 ≠ 0`, `TwinFacts` (StateOK, scratch off, PinsOK, PersPins, PinsReadyP), caches
  empty, `HZ` (the hoist's memos and `CTL[129]`, `CTL[200]` still zero).
* `R4` (after builtin_prelude): `StateDR m (StateD.blank.pre pre.decls)`, `CTL[240]` =
  `pre.decls.size`, `PinFacts` (rset, stk, PinsFull, pin0 together), `TwinFacts`, `HZ`,
  `RecsOK m pre.decls`.
* `R5` (after front_run): `DeclsF DECL DLP (pre.decls ++ rc.decls)`, the rest as `R4`.
* `R6` (after prepare_prelude): `ArenaD`, `DeclsF … ds`, `PinFacts`.
* `R7` (after intern_all_pins): `Since`, `ArenaD`, `DeclsF … ds`, `PinSetsR m ipins`, `RsetR`,
  `pinW m 0 ≠ 0`. `LoopStage` and `PinsStage` also get the twin's prefix (`TwinPrefix`,
  `TwinPrefix4`): the twin's own facts at the state they start from come from con-ron's run lemmas
  (`prefix4_facts`, `stages_frame`), not through the relations.

Pieces:

* `builtin_of_parts`: `builtin_prelude` = `pre_front_run`; `CTL[240] := DECL[0]`; `front_reset`,
  by one `vcgen` over implications between memory predicates (`BP0`‥`BP3`), as `check_of_stages`.
* `frontReset_spec`/`frontReset_stateDR` (`FrontReset.lean`): `StateDR m st` → `StateDR (resetM m)
  (StateD.blank.pre st.decls)` (the sparse memos by `memoRV_clear`, framed through the other
  clears).
* Per-stage write sets (`PreLoopWSStages.lean`, generated by `scripts/preloop_ws.py`; `--check`
  after changing the program): the pin table, `RSET`'s memo, `CTL[131]`, `CTL[240]`, the hoist's
  memos ride along the stages that do not write them.
* `PrepRef.lean` (front4's) now also concludes that the twin's expression tiers and pins are
  unchanged (only the name store changes: `preludeKey` interns the anonymous name) and
  `ds'.size ≤ (pre.decls ++ ds).size` (the room for `DeclsF`), so `DerR` and `DeclsF` hold after.
* `PrepProgChecker.lean`: `PrepProg`/`PrepExt`/`HoistProg`/`HoistExt checkerProg` by `ProgHas.cons rfl`,
  one lookup at a time (`Elab.async false`, 40 s, 4.5 GB).
* Note: `scripts/lake env lean F.lean` does not apply the lakefile's options (`autoImplicit` is
  on there): a file that elaborates that way can still fail `lake build`. Check with
  `lake build`.

## Fuel bound in the stage specs (landing 5)

`StageSpec` and `RelSpec` now quantify only over fuels `n ≤ 2^62` (loopt3: the core's
simulations need it, and fuel only transfers upward). `check_of_stages` takes `n ≤ 2^62`; the
stages run at `n - 1`; `PipelineRefines` already has `N < 2^62`. The stage proofs before the loop
ignore the bound.

## Obligations

| # | Stage / obligation | Status |
|---|---|---|
| 1 | composition | **done** (landing 1), modulo the stages below |
| — | `CapStage` | pieces proved (`capCheck_spec`, `CapCheck.lean`) |
| — | `PbStage` | pieces proved (`checkerProg_pbCheck_PB`) |
| 2 | `IrpStage` | pieces proved (`checkerProg_internReservedPins_PB`, `arenaD_loadMem`) |
| 3 | `PreludeStage` | pieces proved (`preSim`, `checkerProg_preSim`, `frontRun_checker`); `front_reset` open |
| 4 | `FrontStage` | pieces proved (`frontAll_refines_chunks_pre`, `checkerProg_front_run`) |
| 5 | `PrepareStage` | pieces proved (front4's `preparePrelude_refines`, adapted) |
| 6 | `PinsStage` | pieces proved (`checkerProg_internAllPins_PB`) |
| — | `LoopStage` | loopt2's (`installThenCheck_refines` + 12a) |
| 13 | program hypotheses at `checkerProg` | ROM, front, prelude copies, write set before the loop done; loop's are loopt2's |
| — | relations `ρ` and the stage assembly | **done** (landing 4): `pipelineRefines_checker`, modulo `LoopStage` (loopt2) only |

## `sorry`s

None of this lane's.
