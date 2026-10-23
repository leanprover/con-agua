# Lane `indstaget`: the inductive stage from `StageR` to `StageT`

Journal of lane `indstaget` (decisions, measurements, findings, open ends). Only this lane edits
this file. Start: master `4114f77c`. Goal: replace the core-entry stub contracts
(`L.Ind.inferTypeCore_spec`, `ensureSortCore_spec`, `isDefEqCore_spec`, `whnf_spec`, and with them
`stubM_spec`/`stubM_memoFrame` for the core names) in the inductive stage by the knot's `StageT`
sims (`KnotEntry.lean`'s `KnotStageProg`).

## Scope (measured at the start)

Reverse closure of the four core contracts over the built environment (a scratch `#eval` over
`getUsedConstantsAsSet`, the stage's modules imported): **115 stage theorems** (outside the
`Decl*` files) depend on them, 20 levels deep; tops `checkBlock_refines` (level 16) and
`classesCtors_refines` (level 20). Direct users (level 1): `domsW_ok` (IndInstallSpec),
`p2ctW_ok` (IndPos2SpecM), `frameOK_step`/`posOK_step` (IndPos2SpecS), `csfW_ok` (IndSumSpec11),
`wtW_ok` (IndSumSpec2A), `tptW_ok` (RecCheckSpec), `pdsR_ok` (RecCheckSpec11), `ccoW_sim`
(RecGenSpec3), `cruleW_ok` (RecGenSpec4), `tmpW_ok` (RecCheckSpec5), `rtoW_sim` (RecGenSpec7).
Their proofs use 118 further `StageR`-producing callee lemmas, each needing a `StageT` companion.

Models with a core call through `stubM` live in 15 files (IndInstallSpec, IndInstallSpec33,
IndPos2SpecM/N/S, IndSumSpec2A/11, RecCheckSpec/5/10/11, RecGenSpec3/4/7/19); models above them
call their callees through triples, so a `CallM` parameter (lane `loopt2`'s pattern) stays local.

## Route: `StageT`, not `StageC`

con-ron's `KnotSpec` (the twin-side `CheckOK` after a core call) needs the input's denotation and
`Expr.WScoped` at every core call: the `StageC` route would replay con-ron's inductive bridge in
every theorem. The `StageT` route needs no con-ron fact: keep-ops by `StageT.lift_keep`, the
interns through master's `CoreS` refinements (`StageT.of_coreRef`, `internSort_stageT`), the pool
writers by `StageT.of_iw`, the core calls by the knot's sims. Only the level/level-list interns
need validity side conditions (`internSort_core`'s readback of the level).
