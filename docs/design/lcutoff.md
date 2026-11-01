# Lane lcutoff: L-function edits cut off early

Task: modconv.md §5. After modconv an edit inside a proof rebuilds one module, but an edit of an L
function's body (`whnf_walk_fuel`) still rebuilt 632 modules plus the `ProgI` chain: the
`FunDecl`'s body is in its module's public `.olean`, and every module that reaches that module
through `public import`s hashes it. Plan: the L functions `@[no_expose]`, and the modules that
unfold one `import all` of its module.

Result: TBD

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
no code module. An L edit saves ~550 modules; a code-module proof edit costs ~15 more, mostly
the whole-program checks. Clear win: implemented.

## 3. The change

TBD

## 4. Measurements after

TBD

## 5. Side task: `phaseb_fns.py --check`

TBD
