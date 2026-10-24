# Lane `shrink`: a smaller proof

Journal of lane `shrink` (decisions, measurements, findings). Only this lane edits this file.
Start: master `9409753c` (2026-10-24). Goal: fewer proof lines, with
`ConAgua.Final.checkerFile_accepts_remaining` sorry-free (axioms `propext`, `Classical.choice`,
`Quot.sound`) and the census unchanged (1328 proven / 0 sorry, same targets).

## 1. Measurement (master `9409753c`)

`scripts/loc.py`: **15849 L lines, 323943 proof lines** (non-blank). Two things counted as proof
that are not: ~2.8k lines of L code in named blocks (`def … : Stmt := lblk …`, 190 blocks; `loc.py`
counts only `lfn`), and ~5.8k lines of generated files (`CoreErec`, `LeafFns`, `LoopFns`,
`WalkLift`, `Checker.Prog`, `PreLoopWS*`, `Prelude*`, `Asm*`, …). Neither is a target here.

### By category

A scratch classifier (not committed) splits every file into top-level declarations (doc comment and
attributes attached) and classifies each by name and statement: an L spec has `invoke … ⦃` in its
statement; a census theorem carries `@[refines…]`; a model is a `def` named `…W`/`…Kᵢ`; a model
equation is a short theorem named after a model; a frame lemma is named `…frame/afr/keep/grow…`
or states `MemFrame`/`AFr`; a relational lemma states a relation (`StageR`, `StageC`, `CoreS`,
`ArenaR`, `Sim`, …) or a twin (`ConRon.`, `.run`). Heuristic: ±10 % per row.

| category | lines | share | notes |
|---|---:|---:|---|
| relational lemmas (`_ok`/`_ref`/`_sim`/`_okC`…) | 102.2k | 30 % | the refinements proper |
| census theorems (`@[refines]`) | 22.7k | 7 % | ~800 are ≤25-line glue (9.5k), the rest full proofs |
| **model/spec layer** | **55.9k** | **17 %** | L specs 22.2k, model eqs 11.9k, models 9.4k, continuations 7.9k, `_some` 3.0k, `grind_pattern`s 1.6k |
| other unfoldings/guarded eqs/dispatch steps | 17.8k | 5 % | twin unfoldings, `_step`/`_succ` dispatchers |
| frame/footprint lemmas | 13.5k | 4 % | per-model `_frame` 2.0k, `_afr` 2.2k, `grow` 2.2k, `keep` 0.5k, rest in statements |
| decoding/arithmetic | 7.9k | 2 % | |
| program bundles + lookups | 4.8k | 1.5 % | 5227 `lookup "…"` lines in all (2.5k bundle fields, 2.7k explicit hypotheses) |
| doc comments | 32.9k | 10 % | not a target |
| imports, `open`, `set_option`, module docs | 17.3k | 5 % | not a target |
| other theorems/defs (compiler, scanner, ROM, tooling, L library) | ~52k | 16 % | compiler proof ~8.8k, scanner/front ~32k |

### By area (non-blank lines)

Arena 268.6k (IndPos 19.7k, RecGen 14.0k, DefEq 13.4k, RecClass 10.6k, RecCheck 10.2k,
IndParts 10.1k, WhnfIota 9.8k, IndInstall 9.5k, IndReal 9.1k, IndSum 7.8k, DeclNat 6.8k, …),
Front 21.9k, Checker 16.2k, Scan 10.5k, Compiler 8.8k, Rom 6.8k, L 3.1k.

### What the review's patterns look like now

* **`Sim`** is already the form of the newer StageC code (`IndT/*`, 60 files, 17k lines). The old
  per-callee `Option` split (`cases h : callee … | none => … | some …`) remains outside it: 6221
  `cases h… :` in all, ~2700 of them callee splits in non-`Sim` files (IndPos, DefEq, DeclNat,
  IndParts, IndReal, Checker, RecCheck, RecClass, WhnfIota/Delta, Front, Scan, Rom).
* **P5 duplication** (one function under two relations) is mostly gone: lane `cleanup` deleted the
  StageR copies whose StageC transcriptions replaced them (e.g. `newOK_step`).
* **`l_model`** is used by 8 files (`Lift*`, `Inst1*`, `LevelSimp`, `Hoist`, `Prelude`). 1214 hand
  models `…W`; 349 are read only in their own file, 411 in one other, 454 in two or more.
  Of ~1560 L functions, 207 contain a `while` (not supported by `l_model`), 30 are parameterized.
* **Copy-paste inside proofs**: 12.2k lines are a second (or later) copy of a 6-line window in the
  same file (digits normalized); 14.7k lines lie in 8-line windows that also occur in another file.
  Examples: `DeclNatDeps.natOpDeps_ref` (15 identical arms, 325 of 595 lines), `IndDecStab`,
  `ConstsResolveFRefine2`, `DeclNatEq`, `PromoteRecRef`, `RomExprRef`, `IndRealAbsPos` ↔
  `IndPosSpec5`, `InferBodyBind` ↔ `InferBodyBindPi`.
* **Dead code**: only 89 declarations (~570 lines) are textually unreferenced now; the cone of lane
  `cleanup` was not rerun after `conslib2` landed (chains may add 1–3k).
* **`UpTo`**: 234 mentions in ~50 files, 2 definitions; mostly hypotheses and `hk j (by omega)`
  arguments. The review's ~1k lines is high; ~0.2–0.4k.
* **CTL slots**: 2149 `rdW (m.arr64 CTL) k` reads with a literal `k`, dominated by `200` (IW top,
  508), `1` (scratch flag, 395), `136` (spine top, 270), `129` (EREC top, 123). Proofs mostly read
  them through named functions already (`iwTop`, `erTop`); `MemFrame [IW] [200]` etc. name the
  slot once per frame (640 frame sites). 392 lines mention `CTL).size`.
* **`cR`**: 1536 mentions, all now `realCall p` (430 `realCall p` terms).

## 2. Levers: estimated saving now, cost, risk

| # | lever | est. saving | cost | risk |
|---|---|---:|---|---|
| A | **Retrofit `l_model`** on the model/spec layer, family by family (models, continuations, `_some`, equations, patterns, spec proofs) | 15–20k | high: refinements renamed to `fW.armᵢ`/`fW.kᵢ` (the pilot: model/spec files −63 %, refinements ±0); models read by other files cascade; `while` support needed for ~13 % | medium (generated arms carry every path condition; build time was neutral in the pilot) |
| B | **Factor copy-paste inside proofs** (a local helper lemma per repeated arm, `all_goals`/`<;>` over uniform cases, shared lemma for cross-file twins) | 6–10k | low-medium, file-local, no statement changes, parallel | low |
| C | **`Sim` in the old relational proofs** (bodies only; statements kept, `Sim.run` at the boundary) | 6–9k | medium: a `Sim` adapter per callee lemma (or a generic one like `sumSim_of_relW`) | medium |
| D | **Program bundles from the text** (`ProgHas`, field `hp.f` → `hp.get "f"`; the `checkerProg_*Prog` constructions become one line) | 3–4k | low, largely mechanical | elaboration time of `rfl` lookups on long lists: measure |
| E | **Frames from write sets** (a generic "model frame from spec + `closedA`/`closedG`" bridge instead of per-model `_frame`/`_afr`/grow lemmas) | 3–4k | medium | medium |
| F | **Footprint relations** (§5 of the review) | 2–4k now (P5 copies already deleted) | high | high |
| G | **Tag `switch` over one verified `expr_view`** (L change) | 3–4k | medium-high: L + asm + perf (an extra call per node) + rewriting each dispatcher proof | medium |
| H | **Named globals for CTL slots** (L change) | 0.5–1.5k | high: every model/spec/proof touching the slot, L text, asm, e2e | medium; worthwhile only for code regenerated by A anyway |
| I | small: dead-code cone rerun (0.6–3k), `UpTo` → `exec_mono` (0.2–0.4k), drop `cR` (~0.3k; changes statements), merge AFr duplicates (~0.2k), Capstone/DriverLink (784 lines: decision for the user) | 1.5–4k | low | low |

Realistic total: **~40–55k lines (12–17 %)**. The review's 40–55k for A alone assumed every function
retrofits and every model is internal; the modelgen pilot showed refinements do not shrink and shared
models cascade.

## 3. Proposed order

1. **B** (copy-paste factoring) and **I** (dead code, UpTo, AFr merge) first: cheap, local, no
   statement changes; pilot on `DeclNatDeps` + `DeclNatEq`, then helpers in disjoint batches.
2. **A** pilot on one self-contained family whose models are read by ≤1 other file (candidate:
   a `DefEq*` or `WhnfIota*` family), measuring lines and build time, before deciding the rollout.
3. **D** (bundles) as a mechanical batch, after measuring `rfl`-lookup cost on the largest bundle.
4. **C** and **E** per area, together (both touch the same relational lemmas).
5. **G/H** only if the user wants the L changes; H only together with A on the same code.

## Log

(empty: waiting for the user's choice of plan)
