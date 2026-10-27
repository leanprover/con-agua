# Lane restructure: faster, more incremental builds

Goal: shorter cold builds (critical path) and smaller rebuilds after a proof-only edit, by
restructuring proof modules. Theorem statements, L program text, `checker.s`, `pins.bin` and
`main.c` stay unchanged.

## What the module system can and cannot do here

Lake (nightly-2026-10-20, `Lake/Build/Module.lean`, `fetchTransImportArts`, `addImport`) traces
imports by their output artifacts, so a module whose rebuilt `.olean` is byte-identical does not
rebuild its importers (early cutoff). What an importer depends on:

* a `module` file importing a `module` file depends on its public `.olean` (and, through `public
  import`, on the public part of what that re-exports). Proof bodies of theorems are not in the
  public `.olean`, so a proof-only edit there stops at the edited module;
* a **non-`module` file depends on every artifact of its whole import closure** (`importAll` is
  forced for non-modules: `.olean`, `.olean.server`, `.olean.private`), so any edit anywhere below
  it rebuilds it.

A `module` file cannot import a non-`module` one. con-ron's arena model and bridge
(`vendor/con-ron`, 303 of 328 files) are not `module` files, so every proof that mentions the
twin (all of `Arena` above the L libraries, `Checker`, `Front` refinements, `Verdict`, `Final`) is
a non-`module` file and gets no early cutoff. At master 5b9bde54: 729 of 2119 modules in the
build are `module` files (L, Compiler, Scan, con-leche, part of Arena's L libraries).

So in this tree the levers are:

1. **Cut imports** that make large non-`module` subtrees depend on frequently edited modules.
2. **Shape the import graph** of the big proof families (linear chains `Foo2 → Foo3 → …`, split by
   size) after the call graph, so that the critical path shortens and an edit rebuilds only the
   callers' modules.
3. Where the chain is `module` all the way (L, Compiler, Scan), keep proofs out of the public
   interface so early cutoff applies.

## Measuring

Tools (in `_tmp/restructure/bin/`, not committed): `graph.py` (the import graph from the sources),
`cp.py` (critical path from Lake's `Built X (t)` lines: every module starts when its last import
is done, unlimited cores; with `--touch M`, the modules a change to `M` rebuilds when no early
cutoff applies, i.e. all of `M`'s importers, transitively, and the critical path among them).

Baseline: master 5b9bde54, cold build (no cache hits), 29 min wall, 224 CPU-min (coordinator's
measurement, log `_tmp/nowarn/cold-master-5b9bde54.log`). Lake timed 1929 modules, 10 266
module-seconds. **Critical path 1710 s**, so the cold build is bound by it (1740 s wall). It runs
through Scan (190 s), the ROM and declaration setup (to 330 s), the inductive-proof families
`IndPartsSpec`/`IndPos2Spec`/`IndPosSpec`/`IndInstallSpec`/`DeclDivMod` (to 720 s),
`Arena.Checker` and `Checker.Prog` (99 s, to 820 s), `Checker.NoVerdictClosed`, and then the
linear chain of `Verdict.IndB*` error models (`IndBSum1`…`IndBTbl`, with `IndBGrpM` alone 406 s)
to `Verdict.IndArmTopE` and `Final.EndToEnd`. With every `Verdict` module at zero the path would
still be 1276 s, through the `RecGenSpec`/`RecCheckSpec`/`IndInstallSpec` chains and
`Checker.IndArmClosed` (162 s).

Rebuild after a proof-only edit (no early cutoff, so all importers):

| edited module | rebuilt modules | module-s | critical path |
|---|---:|---:|---:|
| `Compiler.SimStmt` | 718 | 7339 | 1480 s |
| `Arena.IndInstallSpec5` | 409 | 5328 | 1105 s |
| `Arena.IndInstallSpec20` | 183 | 2383 | 995 s |
| `Arena.PromoteCIRef10` | 252 | 4139 | 1030 s |
| `Arena.RecGenSpec10` | 204 | 2726 | 1030 s |

## Batch 1: `Checker.Entry` no longer imports `Final.Statement`

`Checker.Entry` (the checker's entry and glue, imported by 699 modules: nearly all of Arena,
Checker, Verdict) imported `Final.Statement` only for one `example` checking that `check_b`'s
literal return word is `ConAgua.Final.ACCEPT`. `Final.Statement` imports `Compiler.Main`, so every
compiler-proof edit rebuilt those 699 modules. The `example` moved to `Checker.ParDriverL` (the
first module that states `check_b`'s result as `ACCEPT`), which imports `Final.Statement`
itself. Five modules used the twin's bridge lemmas (`ConRon.Bridge.*`) that came in through
`Final.Statement → Final.Twin`, and `Checker.Pipeline` uses `loadMem`; they import `Final.Twin`
(`DeclCvgT`, `IndRealSortDn`, `IndRealSctC`, `IndRealCapsC`) or `Final.Statement` (`Pipeline`)
directly. `Final.Statement` itself is unchanged.

Modules that depend on `Compiler.Main`: 710 → 47; on `Final.Statement`: 708 → 45. Rebuild after an edit in a compiler proof,
estimated as above (all importers, no early cutoff):

| edited module | before | after |
|---|---|---|
| `Compiler.SimStmt` | 718 modules, 1480 s critical path | 55 modules, 219 s |
| `Compiler.Correct` | 712 modules | 49 modules, 203 s |
| `Final.Statement` | 709 modules | 46 modules, 193 s |

(Module counts here include the edited module itself.)

## Batch 2: `Verdict` imports what it uses

The `Verdict` modules (154; the error refinements, one `l_model`/`err_stmt` group per L function
already) were written as chains: each imports the one before it (`IndBSum1 → … → IndBCcs →
IndBGrpM → IndBGrp → … → IndBTbl`), so `IndBGrpM` (406 s, one `l_model` command) could start
only at 1142 s. Now each imports the modules whose constants it uses (a list from the elaborated
environment: every constant of every `ConAgua` module and the modules of the constants its type
and value mention, equation lemmas and other realizable auxiliaries counted at their parent),
plus the modules defining the tactics, commands and `grind` attributes its text uses, plus the
modules declaring names its text mentions that only a command reads (`err_stmt X := name`,
`l_model … extra [name]`), keeping the imports of non-`Verdict` modules; then imports another
import already reaches are dropped. 104 of 154 modules changed imports.

What constant lists miss (found by building): global `@[simp]` lemmas a `simp` used without the
proof term naming them — `exc_ok_bind` (`Arena/Checker.lean`) in `IndsE4` and `IndBRecPins`, and
`open` of a namespace (`IndBTmm` opens `ConRon.Bridge.Inductives`). Those import the providing
module directly.

`IndBGrpM` now starts at 197 s (finishes at 603 s). Estimated critical path 1710 s → 1353 s; it
now runs through the `Arena` proof families and `Checker.IndArmClosed`, and `Verdict` contributes
only its last three modules (`FrontStageE`, `TopE`, `IndArmTopE`).

## Batch 4: the declaration loop's L functions apart from their proofs

`Checker.Prog` (the assembled program, 99 s, imported by every whole-program proof:
`ProgWf`, the asm parts, the loop and inductive-arm closures) imports the module of every L
function it binds (`scripts/checker_prog.py`). All of them were done by 410 s except
`Arena.Checker`, done at 721 s: it holds the declaration loop's ten `FunDecl`s
(`install_step` … `check_pending_next`) and their refinements, and imports the proofs those
need (`DeclCheckLoop`, `DeclDivMod*`, `PromoteCIRef31`, …). The `FunDecl`s (text unchanged, with
their citations and `@[l_impl]` tags) moved to `Arena/CheckerL.lean`, which imports only
`DeclBase`, `Reasons` and `Census.Attr`; `Arena.Checker` imports it. The regenerated
`Checker/Prog.lean` differs in that one import; `checker.s` and `pins.bin` are unchanged
(`asm_file.py --check`). Three `Verdict` modules (`WhnfProjE`, `DeclBasisE`, `InferArmsE`) used
`Arena.Checker`'s lemmas (and its `@[simp] exc_ok_bind`) through `Checker.Prog` and import it
directly now.

`Checker.Prog` can start at 410 s instead of 721 s. On its own this does not shorten the critical
path (other paths reach 1353 s), together with batch 3 it does (below).

## Batch 3: the `Arena` proof families import what they use

Same tool as batch 2 (`shake_fam.py`), over the 277 modules of the numbered and lettered
inductive-proof families (`IndInstallSpec*`, `RecGenSpec*`, `RecCheckSpec*`, `IndSumSpec*`,
`IndPartsSpec*`, `IndPosSpec*`, `IndPos2Spec*`, `RecClassSpec*`, `DeclDivMod*`, `IndReal*`,
`IndT/*`): each imports the family modules whose constants it uses instead of the previous link
of its chain; imports of other modules stay. 242 of the 277 changed. Every other module is then
checked to still reach every module it used before (a module two links down a chain may have
been reached only through the link that went away); 9 got direct imports back. Two lessons for
the tool: only add a module that the importer reached before (constants re-attributed by the
environment otherwise create cycles), and repeat the reachability check to a fixpoint (the
modules were processed in an order where a later change could cut an earlier module's path).

Estimated critical path (same module times) 1353 s → 1160 s, with batch 4 1118 s; it now runs
`IndPos2SpecA…M` (a chain of real uses between the files) → `DeclDivMod5…9` → `Arena.Checker` →
`Checker.LoopDecl*` → `Checker.IndArm` → `Verdict.TopE`.
