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

## Obligations

| # | Stage / obligation | Status |
|---|---|---|
| 1 | composition | **done** (landing 1), modulo the stages below |
| — | `CapStage` | open |
| — | `PbStage` | open (`L.Rom.pbCheck_PB`) |
| 2 | `IrpStage` | open (`L.Rom.internReservedPins_PB`) |
| 3 | `PreludeStage` | open (no theorem) |
| 4 | `FrontStage` | open (`frontAll_refines_chunks`, over `frontAllProg`, empty `DECL`) |
| 5 | `PrepareStage` | open (no theorem; hoist's refinement as a hypothesis) |
| 6 | `PinsStage` | open (`L.Rom.internAllPins_PB`) |
| — | `LoopStage` | loopt2's (`installThenCheck_refines` + 12a) |
| 13 | program hypotheses at `checkerProg` | open |
