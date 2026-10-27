# Lane shake: every module imports what it uses

Goal: remove unused imports across `ConAgua` and `ConAguaAsm` (not `vendor/`), so that a proof edit
rebuilds fewer modules and the cold build's critical path shortens; then keep it that way with a
gate. Theorem statements, L program text, `checker.s`, `pins.bin` and `main.c` stay unchanged.

## The tool

The toolchain (nightly-2026-10-20) ships Lean's import minimizer as `lake shake`
(`Lake/CLI/Shake.lean`). It reads each module's `.olean`: the modules of the constants its
declarations mention, and what elaboration recorded with `recordExtraModUse` (the simp lemmas a
`simp` used, `rfl` lemmas included; the modules of the macros, elaborators and attributes used; for
a used constant, the module that put an attribute on it, `recordIndirectModUse`). For every module
it computes the imports it needs, transitively reduced against the new imports of the modules below
it, and proposes removals and additions; `--fix` writes them. It is a minimizer: an import a module
reaches only through one that goes away is added directly.

`lake shake` refuses a closure with a non-`module` file, and most of `ConAgua` is classic (everything
above con-ron's arena). con-leche had the same problem (its task #223) and patches the tool for
classic files in three places (`scripts/shake-setup.sh`, copied from con-leche): no guard, a classic
`import X` reads as exported, `--fix` writes `import X` in a classic file. The patches apply
unchanged to this toolchain's `Shake.lean`.

The tool loads all roots into one environment. Two kinds of top modules cannot be loaded with the
rest: the executables' `main` modules that the default build compiles (`Arena.LiftEmit`,
`Arena.Inst1Emit`, …), and `Compiler.WFAllBench` (its closure declares `L.Arena.bv` a second time,
in `Arena/LiftBench.lean`; `NatBits` has the other). They and the five modules only
`WFAllBench` reaches were not minimized. The 14 modules only executables reach (`Census.Main`,
`E2E.*`, `Rom.Gen`, …) were not minimized either; their imports were fixed where the build needed it.

## What the tool does not see, and what was done about it

Each item was found by building (`scripts/lake build`, nine rounds, then every executable). The
pipeline (in `_tmp/shake/bin/`, not committed) resets the sources to master, runs the patched tool
with `--fix` against master's build, then repairs:

* **`meta import`s and `public` on attribute modules.** The tool rewrote
  `public meta import Lean.Meta.Tactic.Grind.Attr` in the `*GrindAttr` modules to a meta import of
  `…Grind.Extension`, and demoted `public import ConAgua.L.GrindAttr` to `import`; then every
  importer failed with "(interpreter) unknown declaration `Lean.Meta.Grind.registerAttr`" (the
  attribute's initializer runs at import and needs its code loaded). Every `meta import` of master
  is kept (and the tool's added ones dropped in those files), and a `public import X` the tool
  demoted to `import X` in a `module` file is `public` again (116 files).
* **Names inside syntax quotations.** `L/Notation.lean`'s macros expand to
  `` `(L.TRec.cntE …) ``; the tool cut `Notation`'s import of `L.TRec`, so the quotation's name was
  not resolved when `Notation` was compiled and every user failed with "Unknown identifier
  `L.TRec.cntE✝`". The 44 modules that declare a global `macro`, `syntax`, `notation`, `elab` or
  `infix` are not minimized (`scripts/shake-keep.txt`). Local macros (`local macro "mfr_auto"`) are
  used only in their own module, where the build catches a missing name.
* **`open N`** needs the namespace to exist. For every `open` (resolved against the enclosing
  namespaces), if master's closure declared it and the new one does not, the module imports the
  provider with the smallest closure (e.g. an emptied `IndSumSpec/Bnums.lean` opens
  `ConRon.Arena`, `Std.WP`, `L.Arena`).
* **Commands, `#guard`, `example`, `#print`** leave no constant. `Audit.Final`
  (`#guard_msgs in #print axioms` of imported theorems), `Compiler.WFAll` (`#guard`s),
  `Arena.WalkBench` (`#guard`s that run imported programs: they need the programs' code, `meta
  import`), and the import-only aggregators `Arena.DeclAll`, `Arena.IndAll` are not minimized.
  Names read by `err_stmt X := name` (`Verdict.IndBE`, `Verdict.IndsE2`) got their modules back from
  the build errors.
* **Auxiliaries realized in several modules** (`_sparseCasesOn_N.else_eq`, equation lemmas): in the
  joint environment one copy wins, so the tool attributes a use to whichever module realized it
  first, sometimes one the module never reached. The same for a name declared twice (`L.St.setLocs_mem'`
  in `L/GKeep.lean` and `Front/Preserve.lean`): the tool added `import ConAgua.Front.Preserve` to
  `L/GKeep.lean` (then "already declared"). An added import of a module outside master's closure is
  dropped and the imports the tool removed from that module come back (25 modules); and every
  module imports again any module whose constants it used in master's build and that it no longer
  reaches (constants from restructure's `DepsAll.lean`). This check and the `open` check together
  add imports to 72 modules.
* **A statement with a proof in it.** `Rom.CIReadRefData`'s `basisDecls_fit` states
  `basisKinds[i]'(by simp [basisKinds]; omega)`: with a smaller simp set the proof term inside the
  type differs. The module keeps its imports.
* **Generated files** (`Checker/{Prog,ProgWf,Asm,AsmPart*}`, `Arena/{CoreErec,LoopFns,LeafFns}`,
  `Checker/PreLoopWS*`): their generators write the imports, so they keep master's text.
* **Modules left empty**: `Arena/DeclCanonView.lean` (content moved earlier, now imported by
  nobody, so unbuilt), `Arena/PoolSlice.lean` (a re-export of `LitRefine`; its importers import
  `LitRefine`) and `Checker/IndRealNames.lean` (an empty namespace) are deleted; the prose that
  named `PoolSlice` names `LitRefine`.
* The remaining build errors (unknown identifiers in 13 modules) got the declaring module as an
  import (`_tmp/shake/extra.txt`).

Checks besides the build: every executable builds; `asm_file.py --check` and the four closure
`--check`s pass; the type of every `ConAgua` constant (and the value of every definition), 49 892
of them without auxiliaries, has the same hash as on master (`StmtHash.lean`); the census still
reaches every module with an `@[l_impl]`/`@[refines]` tag; a cold build (`LAKE_COLD=1`) has no
warning outside Kraken and `vendor/`.

## Result

1059 files change imports. 896 imports are gone (778 of `ConAgua` modules, 77 of the attribute
modules `*GrindAttr`/`Census.Attr`, 30 of con-ron, …); 2965 are added: 1125 of the attribute
modules and 776 of `Std` (the simp lemma modules a `simp` used and the `grind`/`vcgen` attributes,
which used to come in through a broad import), 948 of `ConAgua` modules the module uses itself.
In-tree, `ConAgua` modules have 5487 direct imports instead of 4214, but import closures shrink:
the sum over modules of the closure sizes goes from 739 001 to 573 925 (-22 %), a module has on
average 264 instead of 323 transitive importers in `ConAgua`, and the median closure has 402
modules instead of 448.

Measured as restructure did: same machine, back to back, otherwise idle, `LAKE_COLD=1 scripts/lake
build` from an empty `.lake/build`, all cores (logs `_tmp/shake/{before,final}-cold.log`):

| | master fe7d4d1f (before) | after (76a14780) |
|---|---:|---:|
| modules compiled | 2107 | 2104 |
| wall | 751 s | **582 s** |
| CPU | 12 087 s | 13 730 s |
| sum of module times | 8048 s | 8980 s |
| critical path (from the module times) | 740 s | **574 s** |

More modules run at the same time now, so each is slower (median +4 % over the modules above 5 s:
`IndBGrpM` 287 → 331 s, `Checker.Prog` 70 → 79 s, `ProgWf` 58 → 75 s), and CPU time grows with
it. With the old module times the new graph's critical path is 555 s. Restructure's simulation
expected only about 20 s here; it modelled precise imports for the constants only, and the old
critical path ran through imports that nothing used (`Checker.LoopDecl*` waited for
`DeclDivModSpec`): the path now runs `DeclNatDeps` (31 s) → `IndPartsSpec`/`RecClassSpec`
(`PrefixBinders` 37 s, `MnW` 27 s) → `RecGenSpec.Rec3TmdWDecB` (37 s) → `Verdict.IndBTmn` (63 s) →
`IndBTka` (37 s) → `Verdict.IndArmTopE` (32 s) → `Final.EndToEnd`.

Proof-only edit (restructure's four probes: one `have _touch : True := trivial` inserted, then
`LAKE_COLD=1 scripts/lake build` on a fully built tree; wall, modules compiled):

| edited proof | before | after |
|---|---|---|
| `sim_ite` (`Compiler/SimStmt.lean`) | 45 modules, 113 s | **15 modules, 58 s** |
| `piDomsMentionAny_refines` (`IndInstallSpec/BlockRawRec`) | 48 modules, 196 s | **39 modules, 103 s** |
| `caps_rel` (`PromoteCIRef/Caps`) | 113 modules, 242 s | **91 modules, 208 s** |
| `rec3TmdW_decB` (`RecGenSpec/Rec3TmdWDecB`) | 141 modules, 250 s | **122 modules, 180 s** |

## The gate: `scripts/shake.py`

`scripts/shake.py` (gate step `shake`, after `build`, selected by any change to a `ConAgua` or
`ConAguaAsm` source or to the shake files; also a CI step) builds the patched tool once per
toolchain into `_tmp/shake-tool/` (`scripts/shake-setup.sh`, ~10 s), runs it on the default build
(~10 s on 25 cores) and fails if it proposes to remove an import that `scripts/shake-allowlist.txt`
does not list, or if a listed line is no longer proposed. It judges plain and `public` imports of
`ConAgua`/`ConAguaAsm` modules, not `meta` imports, not imports of the attribute modules (an
unused one is a leaf every proof reaches anyway) and not a `public import X` the tool would demote
to `import X`. `scripts/shake-keep.txt` lists the modules it does not minimize (above). The
allowlist has 98 lines, each with its reason: an `open`, a constant the tool attributes elsewhere,
a build error, or (6 lines) kept from master because the first run did not propose it. Probed: an
unused `import ConAgua.Scan.Utf8` added to `IndPosSpec/CloseTelescope.lean` fails the gate with
that line named.

The tool is not idempotent: run again on the result it proposes 724 more removals (most of the
attribute and `Std` imports it just added, and `meta` imports); the gate ignores those classes.
A second round over the rest is left (below).

## Left for the next build-time round

* **The critical path (574 s)** is now proof families plus the `Verdict` top: `Verdict.IndBTmn`
  (63 s), `IndBTka` (37 s), `IndArmTopE` (32 s), `RecClassSpec.PrefixBinders` (37 s), `MnW` (27 s),
  `RecGenSpec.Rec3TmdWDecB` (37 s), `Arena.DeclNatDeps` (31 s). `Checker.Prog` (79 s) and the
  whole-program proofs (`Checker.LoopDecl*`, `IndArm`, `IndArmClosed` 108 s, `ProgWf` 75 s) are
  next to it, no longer on it.
* A second shake round over the modules the gate does not judge (the 724 proposals) and over
  `shake-keep.txt`'s macro modules (a macro module needs the modules its quotations name, which
  the tool does not record; the others could shrink).
* The executables' modules and `WFAllBench`'s closure are not minimized.
