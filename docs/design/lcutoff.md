# Lane lcutoff: L-function edits cut off early

Task: modconv.md §5. After modconv an edit inside a proof rebuilds one module, but an edit of an L
function's body (`whnf_walk_fuel`) still rebuilt 632 modules plus the `ProgI` chain: the
`FunDecl`'s body is in its module's public `.olean`, and every module that reaches that module
through `public import`s hashes it. Plan: the L functions `@[no_expose]`, and the modules that
unfold one `import all` of its module.

Result: every L function (1,639 `FunDecl`s in 155 files) is `@[no_expose]`; 449 files got
`import all` of the modules whose L functions they unfold (6,206 lines, scripted from the build
errors; 43 whole-program checks import all ~142 body modules). modconv's L edit (`whnf_walk_fuel`)
now rebuilds **231 modules, 1,356 module-s, 446 s** (with `asm_file.py`) instead of 632 + the
`ProgI` chain, 3,480 module-s, 92 + 952 s. Proof edits outside the code modules are unchanged (2
modules); **a proof edit inside a code module now rebuilds ~54 modules** (~500 module-s, 165 s)
instead of 2, the price of the whole-program checks' `import all` (§2, §4). The cut is weaker than
the ~120 lnext3.md hoped for: Lean exports the equation lemma a proof realizes for an imported
non-exposed definition, with the body in its statement (§3), so every spec that `simp`s with an L
function republishes the body. No statement changed; `Audit/Final.lean` is unchanged.

## 1. Lake's rules, measured on a toy (nightly-2026-10-20)

modconv.md §1 had the public-closure rule. Three more, from a toy project
(`_tmp/lcutoff/toy/`: `A` with a non-exposed `def f : Nat`; `B` = `import all A`; `C` imports `B`;
`D` = `import all B`; `E` = `meta import A`; `E2`, `E3` = `meta import` of a module that imports
`A` publicly resp. privately; `F`, `G` = public resp. plain import of `A`; `H`, `K` = `import all`
of `G` resp. `F`):

* **A non-exposed body** (`f := 6` → `7`): rebuilds `A`, its `import all`-ers (`B`) and their
  `import all`-ers (`D`), and **every module with a `meta import` whose closure contains `A`,
  through private imports too** (`E`, `E2`, `E3`): a meta import hashes the compiled code (IR) of
  the whole closure. Plain and public importers (`F`, `G`, `C`) and `import all` of a module that
  only imports `A` (`H`, `K`) do not rebuild.
* **A proof edit** (`by omega` → `by (omega)`, same axioms): rebuilds `A` and the chain of
  `import all`s above it (`B`, `D`), not `H`/`K`, not the meta importers.
* **A `theorem … := rfl`** is exported as a definitional (`rfl`) theorem, and Lean checks it in
  the public view: over a non-exposed definition it fails ("Not a definitional equality"), even in
  the defining module. `by rfl` is an ordinary theorem and passes. (An edit `:= rfl` → `:= by rfl`
  also changes the public `.olean`: `C` rebuilt.)

So a module `C` rebuilds when one of its direct imports `n` has, in `n`'s public closure, a module
whose public `.olean` changed; or `n` is `import all` and a module of `n`'s `import all` closure
changed its private part; or `n` is `meta` and a module of `n`'s full closure changed its code.

## 2. Measured before changing anything (simulation)

`_tmp/lcutoff/sim.py` implements these rules on the import graph read from the headers
(`graph.py`, 1,366 built ConAgua modules). On master (every body exposed) it predicts 717 modules
for modconv's `whnf_walk_fuel` edit (seeded with `ConAguaAsm.Checker` and `AsmStub`, which read
`checker.s`); the measured set was 632 plus the code modules and `ProgI` chain that
`asm_file.py` built first (630 of the 632 are in the prediction, the two missing ones are the
`checker.s` readers).

**The `import all` count.** 1,620 `def X : FunDecl` in 147 modules (plus 19 schema-generic ones,
`memoFindG`, `consInternG`, …). 995 modules mention an L function of another file, mostly in
statements (`p.lookup "f" = some fL`), which need no body. Estimates of the modules that unfold one:
308 modules mention one in a tactic line (369 module pairs; "low"), all 995 (2,498 pairs, "high").
The whole-program kernel checks import all of every code module: at least the 13 inliner parts
(`ProgIPart*`, `ProgIRef`; "Wmin"), at most the 100 modules that mention `checkerProg` ("Wmax").

| plan variant | L edit `whnf_walk_fuel` | proof edit in a code module (mean / median / max) |
|---|---|---|
| master today | 717 | 2 |
| low, Wmin | 164 (116 outside the `ProgI` chain) | 17.7 / 15 / 82 |
| low, Wmax | 185 | 90.4 / 94 / 171 |
| high, Wmin | 235 | 36.2 / 26 / 386 |
| high, Wmax | 236 | 104.5 / 100 / 468 |

Over all 1,620 functions (low, Wmin): today mean 659 / median 719 / p90 916 modules per L edit;
planned mean 138 / median 122 / p90 153; if every `l_model` spec that names the function changes
its public face too (its generated model and arm statements follow the L text, so they cannot be
cut off), mean 188 / median 142 / p90 347. Of the plan's 164 for `whnf_walk_fuel`, 93 are the
`meta` importers (`prog_wf`, `#guard`, `chk_lk`, …: they rebuild on any code change below them,
today too), 48 the `ProgI` chain, 23 the `import all`-ers. In cold-build module-seconds: 3,008 →
1,683.

**The trade-off.** A proof edit in a code module (99 of the 147 have theorems, 1,752 in all)
rebuilds today the module and `Audit/Final`; under the plan also every whole-program check
(~13–25 modules, ~20–30 s each) and the module's specs that `import all` it. History (master's
4,514 non-merge commits since 2026-10-18 that touch `ConAgua/`, `_tmp/lcutoff/hist.py`): 565
change an L body, 477 change only other lines of code modules (proofs, models, docs), 3,472 touch
no code module. Estimated: an L edit saves ~550 modules, a code-module proof edit costs ~15
more, mostly the whole-program checks. Clear win: implemented. (Both estimates were optimistic:
the leak of §3 adds ~70 to the L edit, and 43 whole-program checks, not 13, need every body, so a
code-module proof edit costs ~52 more, §4. Weighted by the history the trade still saves: per two
weeks 565 × ~490 modules (~1,700 module-s) against 477 × ~52 (~490 module-s), and most of the
477 are not proof-only.)

## 3. The change

* **`@[no_expose]`** on every `def f : FunDecl` and the 19 schema-generic L functions
  (`memoFindG`, `consInternG`, `tblGetG`, …; not the compiler's transforms or the stubs), merged
  into the attribute block (`_tmp/lcutoff/noexpose.py`). The non-L definitions of the code modules
  (word models, schemas, `l_model` output, program lists) stay exposed.
* **`import all`**, in waves of full builds (21 builds, ~4 h at 4 jobs and load 10–100; each wave
  only reaches the modules whose imports built): up front for every module that names an L
  function of another module in a rewriting tactic or an `l_model` command (`preadd.py`, 431 lines),
  and for `l_model` hypotheses that are structure fields (`P.cm ↦ …`, resolved through the
  structure and its `extends`, `prelm.py`); then from the errors (`fixall.py`: the names in
  "Invalid simp theorem `X`: … exposed body", "No spec found for … X.body", "Unknown constant
  `X.eq_def`", and for `decide`/kernel failures the L functions the failing declaration reaches
  through definitions). A whole-program check (`prog_all checkerProg …`, the closure and write-set
  checks, `RomProg*`, the knot's `prog_bundle` over `Prog.subPB`) imports all the body modules of its
  closure (`allbodies.py`).
* **Generated files**: `lean_module.body_modules(roots)` (new) lists the modules of a closure that
  declare an `@[no_expose]` definition; `checker_prog.py` gives them to the inliner's parts
  (`ProgIPart*`, which unfold every function) and the name tree (`ProgTree`: `progTree` reads each
  function's parameter count), `preloop_ws.py` to `PreLoopWSPart*`. Their `--check`s pass.
  `e2e.imports_of` read `import all X` as an import of `all` (fixed).
* **The inliner's literal** (`Compiler/InlineLit.lean`) was the source term (`memoClearG abSch`)
  when a function's round changed nothing; now it is always the literal, so the checks over
  `checkerProgI` (`ProgNrt`, `ProgSkt*`, `ProgTreeI`, `ProgWf*`, the asm parts) need no body
  module. No statement changed (`checkerProgI.f<i>_eq : inlFn env F = checkerProgI.f<i>` as before).
* **`:= rfl` → `:= by rfl`** for 86 theorems whose statement names an L function (equations
  `fooL = lfn …`, `romName.subPB …`, `betaPeelL = betaPeelL'`, `l_model`'s generated `fW.lfn_eq`):
  an exported `rfl` theorem is checked in the public view (§1). No other proof changed.
* **The final theorems' `checkL.nparams = 0` by `decide`** (`DrvFinal`, `EndToEnd`,
  `ThreadsFinal`, `ThreadsVerdict`, `VerdictFinal`): `import all ConAgua.Checker.Entry`.
  `Audit/Final.lean` unchanged.

**The leak** (found measuring (b), confirmed on the toy): `simp only [f]` in a module that
`import all`s `f`'s module realizes `f.eq_1 : f = <body>` there, under a private name
(`Meta/Eqns.lean`, `mkEqLikeNameFor`), and this Lean version exports private constants into the
public `.olean` (`Environment.lean`, `addDeclCore`: `if true /- !isPrivateName n-/`, a TODO). So the
spec that unfolds `whnfWalkFuel` (`IndPosSpec/DepthGo`, `Nb`) changes its public `.olean` with the
body, and its public closure rebuilds (85 of the 231). Realizing the lemma in the defining module
instead puts it into that module's public `.olean` (the toy: worse). It goes away when Lean stops
exporting private constants; no workaround short of not unfolding with `simp` (`delta`).

## 4. Measurements after

Same protocol as modconv.md §3 (fully built worktree, the edit, `scripts/lake build` with
`LAKE_ARTIFACT_CACHE=false`, 4 jobs, `_tmp/lcutoff/mbuild.py`), load 6–15 (modconv's "after" ran at
load ~50: compare modules and module-s, not wall). Each edit also reverted and rebuilt (the second
number, where it differs).

| edit | modconv (master) | lcutoff |
|---|---|---|
| (a) proof only: one line in `ctl_ref`'s proof, `Arena/IndT/Sum4` | 2 modules, 15 module-s, 17 s | 2, 6 module-s, 7 s |
| (a′) proof only, deeper: `decHL_grow`, `Arena/IndInstallSpec/DomsW` | 2, 3 module-s, 6 s | 2, 1 module-s, 2 s |
| (b) L function: `whnf_walk_fuel`'s `d + 1024` → `1024 + d` (`Arena/IndPos`), the build, `asm_file.py`, the build | 632 + `ProgI` chain, 3,480 module-s (load 50), 92 + 952 s | **231 / 227**, 1,356 / 1,199 module-s, 446 / 366 s (`asm_file.py` 16 s) |
| (c) vendored twin, proof only: `NStore.persCount_le`, `ConRon/Arena/WFProofs` | 2, 40 module-s, 42 s | 2, 9 module-s, 10 s |
| (d) proof only in a code module: `pinsReady_true`, `Arena/Pins` | 2 (the rule, as (a)) | **55 / 54**, 488 / 501 module-s, 162 / 170 s |

(The edit lines are `have _lcutoff : True := trivial` as the proof's first line, `measure.py`;
`run-b2.sh` for (b).) Peak RSS 13.6 GB for (b), 7.5 GB for (d). The model of §1 on the landed
headers (`pred.py`, `perfn2.py`, with the leaked equation lemmas: a module that rewrites with the
function changes its public face) predicts 232 for (b) and 54 for (d).

Of (b)'s 231: 62 `import all`-ers of `IndPos` (its specs, the whole-program checks), 54 `meta`
importers with `IndPos` below them, 85 the public closure of the two specs with the leaked
equation lemma, 7 the `ProgI`/asm chain (one inliner part, one asm part, the `checker.s` readers),
23 `import all` chains (`DeclArms`, `DeclStep` and their spec files). Over all 1,620 L functions
(the model): mean 272 / median 160 / p90 734 modules per body edit, against 659 / 719 / 916 today;
without the leak it would be the §2 plan's 138 / 122 / 153.

(d)'s 55: the module, `Audit/Final`, the 12 inliner parts and `ProgTree`, 25 whole-program
checks (each with `import all` of ≥ 100 body modules), 15 specs that `import all` `Pins` or a
module that does. Over the 147 code modules: mean 42, median 42,
max 102 modules.

**Cold build** (fresh worktree, `LAKE_COLD=1`, 4 jobs, 2,103 modules both, the same morning):
lcutoff 4,244 module-s, 1,136 s, peak 12.4 GB (load 7–11); master 73a6605a 5,079 module-s,
1,370 s, peak 12.4 GB (load 15–21). The unchanged vendored and Kraken modules took 653 vs 839
module-s (the load), ConAgua's 3,590 vs 4,240: no measurable cost of the `import all`s; the
inliner's parts with full literals 155 vs 180 module-s.

## 5. Side task: `phaseb_fns.py --check`

`phaseBFns` (`Checker/PhaseBReads.lean`) had the right 582 names, but `ilm_fit` was inserted by
hand in lane d37 (c22035d3, "clear_fit's fast path in inst_list", which added `ilm_fit` to the
closure) after `ilm_clear` rather than in the script's order, and the docstring still said 581.
Regenerated (`scripts/phaseb_fns.py`). The check takes 1 s (`lake env lean` of a small file
against the built `Checker.Prog`), so it is a gate now: `phaseb-fns` in `scripts/gates.sh` and
`scripts/gate_select.py` (selected like the other closure checks: its scripts, and every module in
the closure of `Checker.Prog` or of `PhaseBReads`).

## 6. Left for later

* **The leak** (§3): Lean exporting private constants. When the TODO in `addDeclCore` is fixed,
  an L edit drops to the §2 numbers with no change here.
* **Proof edits in code modules** (54 modules instead of 2): the whole-program kernel checks need
  every body. Either move the theorems of the code modules into spec files (the code modules keep
  only L code and exposed models; 1,752 theorems in 99 modules), or give the whole-program checks
  one exposed literal of `checkerProg` with its kernel-checked equation (as `checkerProgI` is for
  the inlined program), so that only that literal's parts `import all` the code.
* The generic L libraries' bodies (`MemoLib`, `ConsLib`) are `@[no_expose]` too; an edit there
  rebuilds all their instances' unfolders (most specs).
