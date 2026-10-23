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

## Obligations

| # | Stage / obligation | Status |
|---|---|---|
| 1 | composition | **done** (landing 1), modulo the stages below |
| — | `CapStage` | open |
| — | `PbStage` | open (`L.Rom.pbCheck_PB`) |
| 2 | `IrpStage` | open (`L.Rom.internReservedPins_PB`) |
| 3 | `PreludeStage` | open: L code reworked (landing 2); `preSim` stated (`sorry`) |
| 4 | `FrontStage` | open (`frontAll_refines_chunks`, over `frontAllProg`, empty `DECL`) |
| 5 | `PrepareStage` | open (no theorem; hoist's refinement as a hypothesis) |
| 6 | `PinsStage` | open (`L.Rom.internAllPins_PB`) |
| — | `LoopStage` | loopt2's (`installThenCheck_refines` + 12a) |
| 13 | program hypotheses at `checkerProg` | open |

## `sorry`s

* `L.Checker.preSim` (`Checker/PreludeSim.lean`): the input-renaming simulation (in progress).
