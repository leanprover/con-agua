# Lane `loopt`: LoopT: the core's invariants through the declaration loop

Journal of lane `loopt` (decisions, measurements, findings, open ends). Only this lane edits this file.

Lane `indproofs3`'s open end 1: `StageT` (`StageR` + `TwinOK` + the pin flag) must hold at the
stage's entries, so the declaration loop must carry the core's invariants. `LoopR` keeps its shape
(112 uses); **`LoopT`** (`ConAgua/Arena/LoopT.lean`) is a separate relation by named components:
`loop : LoopR`, `twin : TwinOK dn m a fe`, `flag : pinW m 0 ≠ 0`. `LoopT.stageT` gives `StageT`
(and with it `CoreS`), so every `StageT` theorem applies at a state in `LoopT`.

Against lane `indproofs3`'s plan (`docs/design/indproofs3.md`, "The plan for `LoopT`"): (b)'s
bracket opening, `pendPush`, the view restriction and the core calls are done; (c) the start is
reduced to `LoopT.of_fold`'s hypotheses (open end 5 below); the promotion, `drop`, the arms and
(a) are blocked by `StoreDen.proj` (below), which the plan did not account for.

## Landing 1: what is proved (sorry-free; axioms `propext`, `Classical.choice`, `Quot.sound`)

* **`TwinOK` frames**: `TwinOK.frame` (a writer that leaves `EREC` and the core memos — arrays 49,
  50, 151‥153, `CTL` 48, 50, 152, 154, 156 — alone), `TwinOK.frameLo` (the bracket's `CTL` words).
* **The bracket's opening**: `flush_loopT` (`flush_caches`: the caches emptied, so the readback
  clauses hold trivially) and `enter_loopT` (`scratch_enter`). The twin's `enterScratch` needs no
  persistence argument: at a loop head the store is well formed with the scratch tier off, so its
  scratch tables are empty (`scrOff`) and `enableScratch` only turns the four flags on: every view
  and every denotation is unchanged (`enable_views`, `enable_denote`, `denote*Aux_congr_view`).
  Hypotheses: `StoreWF a.store` (`TwinFold.stateOK`) and `a.store.scratchOn = false` (the last
  `dropScratch`; at the start, the pipeline's state).
* **The inductive stage's per-call memos** (lane `indproofs3`'s request): `LoopT` has a fourth,
  memory-only component `memo : StageMemos m`: the eight stage memos (arrays 201‥208, `CTL`
  202‥219: `PosMR` — `nest_occ`, `depth`, `replace_apps`, `has_loose_bvar_b`, the banked
  `replace_fvars` — and `maMR`, `mcMR`, `taMR`) hold some well-formed memo, and every epoch word
  `x` has `CTL[x] + 2 ≠ 0` (what `memoRV_clear` needs). `StageMemos.frame` (any writer outside
  arrays 201‥208 and `CTL` 202‥219), `StageMemos.zero` (zeroed memory: empty memos, epoch `0`; local
  version of `memoRV_zero`, `memoRV_zeroAt`, which needs only the memo's own words zero). The bracket,
  the pending push, the view restriction and core calls keep it (the core's write set now also
  excludes arrays 201‥208 and `CTL` 202‥219, decided again). Across the stage itself, the stage's
  theorems return `PosMR`/`maMR`/… afterwards; the epoch bound is theirs to return too.
* `LoopT.pendPush`, `LoopT.restrict` / `TwinOK.restrict` (phase B's smaller view; a restricted
  hit is a hit, con-ron's `IFEnv.restrictTo_find?_le`).
* **A core call keeps `LoopT`**: `CoreLoopClosed p` (no function the core entry points reach
  writes the pools, the pins, the pending checks, the declaration records, the promotion memos or
  `CTL` 130, 140‥147, 150, 151) is decided for `checkerProg` (`ConAgua/Checker/LoopCore.lean`,
  `decide +kernel`, ~100 s). `LoopT.of_core`: `CoreS` after the call and the write set give
  `LoopT` after (through `LoopR.of_step`); `LoopT.sim_core`; and the entry points as `Sim` facts
  under `LoopT`: `whnfTop_simL`, `inferTypeCore_simL`, `isDefEqCore_simL`, `ensureSortCore_simL`,
  `lvlEqC_simL` (the `LoopT` twins of `IndTwin`'s `_simT`).
* **The twin's half of `TwinOK` from con-ron's fold invariant**: `TwinOK.of_fold` (`FoldOK` +
  `TwinMem` ⇒ `TwinOK`) and `LoopT.of_fold` (`LoopR` + decls4's `TwinFold` + `TwinMem` + flag ⇒
  `LoopT`). The readback caches come from `CacheOK`, the name store from `StateOK`, every stored
  level and level list from the store's well-formedness (con-ron's `denoteL_of_view`: a handle
  with a view denotes), the pins from `PinsOK`, the environment's level parameters and recursor
  levels from `IFEnvOK.hit`. **`TwinMem`** is what is left: the sizes of `EREC`, `SPN`, array 145,
  `CoreMemos m`, `StoreDen.proj` (over `EREC`) and `dnN` (the record decoder agrees with the
  name store). So `LoopT` need not be carried through the arms: at every loop head it is
  `LoopR` + `TwinFold` (both carried already) + `TwinMem`.

## The blocker: `StoreDen.proj` cannot be kept by a record-pool writer

`StoreDen.proj` (lane `defeq2`, `StoreDen.lean`) says: for **every** offset `q` of `EREC` at which
`decTbl` decodes, the table's sort, guards and level parameters read back. `decTbl` has no tag
check (`hd?` accepts any word below `2^32`, `hlist?` any in-bounds slice), so it decodes at many
offsets inside other records and in the unused part of the array. Every `EREC` writer (`erec_ci`,
`env_push`, `cv_new`, `ind_block_to_erec`, `promote_*`, the ROM readers' `rci_block`) chooses
words that then sit under some offset's `structSort`/`guards` reading; nothing makes them read
back as levels. Restricting `q` to below `CTL[129]` (indproofs3's suggestion) does not help: the
new records are below the new top. Whether it holds in reachable states is data-dependent; it is
not an invariant any writer can keep. Consequences: `TwinOK` (hence `StageT`, `CoreS`, `LoopT`)
cannot be re-established after the first `EREC` write of a step, and `TwinMem` cannot be carried
across a step. The step writes `EREC` before or between core calls (`install_value` starts with
`erec_ci`; `check_decl` runs `ind_block_to_erec` before `check_ind_decl`; `and_pin_ok`'s inductive
arm copies the block before the bracket), and every step ends with `env_push`/promotion writes.
**Proposed fix** (owner: the core's lanes, `whnf4`; files `StoreDen.lean`, `StoreDenIntern.lean`,
`StrLitList.lean`, `InferProj.lean`, `InferProj2.lean`, `WhnfCore.lean`, `WhnfProjRefine2/3.lean`):
state `proj` over the environment's tables, `∀ c tbl, fe.find? c = some (.projInfo tbl) → …`
(con-ron's `IFEnvOK.proj`/`.hit` give it from `FoldOK`, so it moves to the twin's half and
`TwinOK.of_fold` covers it), and let `ProjFound` also return that the decoded table is the
environment's (`find_proj` reads the record `EnvR` relates to `fe.find? T`). The consumers
(`cv_lps` already has `fe` membership; `inferProjAt_refines`, `ProjSortDen`, `FireDen`,
`FireOkOK` take it from `ProjFound`) change by one hypothesis each. Then `StoreDen` no longer
reads memory and every `EREC` writer keeps `TwinOK` by `TwinOK.frame`-style lemmas without the
`EREC` side condition.

## Further open ends, in the order a successor meets them

1. **The arms' models (`stubM` → `callW`)**: not switched. Besides the blocker, the arms' text
   frames are unsatisfiable for the real program: `CvgProg p` (and `IvProg`, `ArmProg`, …) asks
   `p` to agree with `cvgProg` on `cvgFns`, which lists `infer_type_core`, `ensure_sort_core`,
   `is_def_eq_core` and the walk entries, and `cvgProg` has lane `induct`'s stubs there;
   `checkerProg` has the real core. So `DeclCallees checkerProg` is false today. The fix is the
   one `LoopT.of_core` uses: drop the core entry points from the agreement lists and take their
   frames from `CoreLoopClosed` (decided) and their results from the `_simL` facts above; the walk
   entries (`loose_bvars_bounded_fast`, `has_fvar_fast`, `all_level_params_defined`) need
   `TwinOK`-keeping specs from their refinements' write sets (`consts_resolve_ffast` has no L code:
   lane `stubs`).
2. **`lvlEqStub_spec`** (decls4's use in `DeclCvg`): `lvlEqC_simL` is its replacement once
   `check_value_group` runs under `LoopT`; it does not yet (phase B's `LoopT` at a pending check
   needs `TwinMem` after phase A, i.e. the blocker). Not discharged.
3. **`romBasisRef_quot`, `romBasisARef_quot`** (`Rom/CIReadRefs.lean`): not discharged, and not
   provable from `StageT` alone. `decCaps` decodes `Quot`'s `sortZ = .ifAllZero [u]` through `dn`,
   and `TwinOK.den.dnN` only gives `dn k = some x → denoteN k = some x`; the statement needs the
   converse at `u`'s handle. That handle is persistent (`internAllPins` interned the quotient block
   at startup with the scratch tier off; the reader's re-intern hits it), so the missing hypothesis
   is "`dn` covers the startup store's persistent names" (`∀ k x, denoteN a₀.ns k = some x → dn k
   = some x` at the startup state) plus "re-interning the quotient block returns the startup
   handles" (store hash-consing: a persistent hit). Neither is in any relation today.
4. **The defn arm's callees without L code** (lane `stubs`): `consts_resolve_ffast`,
   `open_pis_at_fvars_f`, `fvar_b`, `intern_ls_iw`, … abort in `checkerProg`; under `LoopT` a
   stub's `KeepPost` gives `StageR` only, so `TwinOK` is lost across it (indproofs3's open end 2).
5. **`LoopT` at the loop's start** (from the pipeline's stage theorems), by `LoopT.of_fold`:
   `LoopR` at the start (the loop's existing obligation), `TwinFold` (lane `decls4`: `FoldOK` at
   the start, `NodupNames Env.empty`, `PinsDenote`, `PersPinSets`, `PersDecl`, `denoteDecls`, from
   `stages_frame`), the flag (`intern_reserved_pins`' `PinsFull`), `scratchOn = false` (the startup
   interns run with the scratch tier off), `StageMemos` (`StageMemos.zero` on the loaded memory), and `TwinMem`: the three sizes (constant: every
   frame keeps array sizes, so the loaded memory's), `CoreMemos` of the loaded memory (zero counts:
   needs a lemma "a memo with count `0` is `MemoRG` of the empty map"), `dnN` (by the choice of `dn`
   as the startup store's `denoteN`), and `proj` on the startup `EREC` (the pin records of
   `intern_all_pins`; the blocker again, unless restated).
6. **`LoopT` across a step's end** (promotion, `dropScratch`): by `LoopT.of_fold` from decls4's
   `TwinFold.step` once `TwinMem` survives the step (the blocker; `CoreMemos` across the step's
   non-core writers also needs their write sets to avoid arrays 49, 50, 151‥153).

Census: unchanged by this landing (no `@[refines]` changed; the new theorems are relations and
frames).
