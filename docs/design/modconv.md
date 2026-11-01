# Lane modconv: ConAgua's files as `module`s

Task: make the build use Lean's module system so incremental rebuilds get early cutoff
(lnext3.md §2, rank 2; con-ron's arena and bridge became modules in lane ronsync, ronsync.md §6).
Result: every ConAgua file but `ConAgua/Audit/Final.lean` is a `module`. An edit inside a proof
now rebuilds one module (plus `Audit/Final`, 1 s) instead of its whole import closure. An L
change still rebuilds about as much as before (§3); a changed statement rebuilds a third less on
average (§4). No statement changed; `Audit/Final.lean` is unchanged.

## 1. How Lake's cutoff works (measured on a three-module toy, then on the tree)

A toy project `A ← B ← C` (`B` imports `A`, `C` imports `B`, all `module`, nightly-2026-10-20):

* **A proof edit** in `A` (`omega` → `(omega)`, or one more line): Lake rebuilds `A` only. The
  public `.olean` has no proof bodies and no declaration ranges (those are in `.olean.server`) and
  no docstrings' effect on it either: a moved line or an edited docstring rebuilds nothing else.
  It does record the axioms a theorem uses: `omega` → `simp` added `Classical.choice` and rebuilt
  `B` and `C`.
* **An exposed definition's body** (`n + 1` → `1 + n`): `A`, `B` **and `C`** rebuild, although `B`'s
  `.olean` came out byte-identical. `C`'s trace records "`B` transitive imports (public)": the
  hash of every public `.olean` in `B`'s *public* import closure. So a change propagates to every
  module that reaches the changed one through `public import`s, not just to its direct importers.
  lnext3.md's "with cutoff" column assumed direct importers; the real rule is the public closure.
* **A private import stops it**: with `B` importing `A` by plain `import`, a change of `A` rebuilds
  `B` but not `C`. `import all A` makes `B` depend on `A`'s private part too (its proofs).
* **Non-exposed definitions** (plain `public section`): a body change rebuilds only the modules
  that `import all` the module. This is the lever for L changes (§5), not taken here.

## 2. The conversion

Scripted (`_tmp/modconv/convert.py`, not committed): for every non-module file, `module` before
the first import, `import X` → `public import X`, `@[expose] public section` after the imports
(1,189 files; `ConAgua/Audit/Final.lean` left out as the task says; it is a classic file that
imports modules, which Lake allows with `allowNonModules`). Then the fallout, each kind fixed by a
script or by hand, iterating full builds (`_tmp/modconv/fix*.py`):

* **Meta code.** Elaborators and their helpers became `meta def` (`Compiler/WFSplit`, `AsmLit`,
  `InlineLit`, `WriteSetSplit`, `Checker/LoopProgTac`, `FrontProgAgree`, `Sources`, `E2E/Dump`,
  `AsmFile/Include`, `Eq`, `ListEq`; `register_option` → `meta register_option`), with `public
  meta import` of their imports. `AsmFile/Include` (trusted) changed only by these `meta`
  markers and imports. Files that evaluate code at elaboration time — `#guard`/`#eval` (36 files),
  every user of `prog_wf`, `asm_lit`, `inl_round_fns`, `names_tree`, `prog_all`, `chk_lk`,
  `prog_bundle`, `front_agree`, `copy_facts`, `include_asm`, … (97 files), and the `lean --run`
  drivers (`Checker/AsmEmit`, `AsmFile/CrossCheck`, the `Emit*` files) — got `meta import X` for
  each import `X`: in a module, compiled code may run on a definition only if its module is
  imported at the meta level (the error is "`tbl` is not accessible here", or at run time "IR of
  declaration … not available").
* **Definitions made by elaborators** (`addDecl`/`addAndCompile` of a `defnDecl`: `names_tree`,
  `nrt_lit`, `prog_tree`, the inliner's and the assembler's literals, `chunk_checker_prog`) are
  exported as axioms unless the environment is exporting: wrapped in `withExporting`.
* **`l_model`** read an imported L function's text through its declaration range, which a
  module's importers do not get (server data). `L/ModelGen.lean`'s `declSyntax` now finds the
  declaration in the module's source by name (`declText?`; the current file still uses the range).
* **`asm_file_eq`** required its equation to be a `thmInfo`; an imported theorem is seen as an
  axiom (statement only): it now accepts both (`AsmFile/Eq.lean`).
* **Names reached through con-ron's private imports** (ronsync.md §6's "explicit imports", one
  layer further: our modules no longer see a module's private imports): 60-odd `public import`s
  of bridge modules added (`fixunknown.py`, from "Unknown identifier").
* **Definitions their module does not expose.** con-ron's bridge and con-leche are `public
  section` without `@[expose]` in most files; Lean's core library exposes little. A proof that
  unfolds one gets `import all` of its module (51 lines, from the elaborator's note "not unfolded
  because their definition is not exposed", "Invalid simp theorem … exposed body", "Function
  expected", "Invalid ⟨…⟩"): 13× `Init.Data.List.Control` (`List.allM`, `anyM`, `filterM`,
  `findM?`, `mapM`), 15× `Init.Data.Repr` (`Nat.repr`: `toString` in the `fz_<i>` names, which the
  kernel checks over the program unfold), `Init.Data.Array.Basic`, and 14 bridge modules
  (`Bridge/Frontend/Prepare`, `Shared`, `Lines`, `Checker/DivMod`, `Inv`, `Inductives/Positivity`,
  `RecCheck`, `GenRec`, `BlockTail`). No vendor patch, no `@[expose]` asked of con-ron.
  `L/Arrays.lean` and `Compiler/Tests.lean` (modules already, `public section`) got
  `@[expose]`: their bodies are unfolded downstream (`ArrTable.wordSlots`).
* **Matchers.** A `match` in a proof is a different auxiliary from the same `match` in the
  statement, so a `rw` with a restated lambda stopped matching (`RecClassSpec/IhW`:
  `simp only [Function.comp_def, List.getElem?_cons_succ]` instead; `RecGenSpec/ClassMinorSlot`:
  `erw`) and a `simp only` no longer closed by `rfl` (`DefEqMidSpine`: `; rfl`). `IndT/GenRec2`:
  `rw [dClassGen]` before the `simp only` (with `import all`, the linter called four needed simp
  arguments unused). These four are the only proof edits.

**Generated files** get their header from `scripts/lean_module.py` (`modularize`), called by
`scripts/checker_prog.py` (meta imports for every file but `Prog.lean`; `import all
Init.Data.Repr` for the inliner's parts), `preloop_ws.py` and `nv_fns.py`; each `--check` passes.
`core_fns.py`, `leaf_fns.py`, `loop_fns.py` only rewrite lists (pass; `phaseb_fns.py --check` fails on
master already: a 582nd function and an order change, not touched here).

**The demotions** (`lake shake`, as con-ron #137): the tool proposed 2,106 `public import X` →
`import X` (the file's statements and exposed definitions do not need `X`) in 808 files, applied
by `_tmp/modconv/demote2.py`, plus the imports that then must be direct because they are no
longer visible through a public chain (3,127 lines, many of them the grind-attribute modules,
`ModelGen`, `Std.WP.*`). Fallout: the tool's "add" sometimes names a module with a clashing
declaration (`St.setLocs_mem'` in `Front/Preserve` and `L/GKeep`): dropped; `open N` needs `N`'s
module; a few statements needed a re-promotion ("a public declaration … is imported privately").
The generated files keep the generator's all-`public` header (added to `scripts/shake-keep.txt`).
Now 4,300 `public import` and 4,861 `import` lines.

**Tooling.** `scripts/shake.py`: the allowlist lost 40 stale lines and gained 7 (with reasons:
`open`, `prog_bundle`'s names, a `finish` list, a `#guard`); the gate passes. Its docstring says
what a demotion is (not judged). `scripts/modules_check.py`, `simp_scope.py` and
`gate_select.py` already read `public`/`meta`/`all` imports. PLAN.md: "New files are modules".

## 3. Measurements

Each edit applied to a fully built worktree, then `scripts/lake build` with
`LAKE_ARTIFACT_CACHE=false` (reads the shared cache, writes nothing), `LEAN_NUM_THREADS=4` (4
jobs), summed RSS of the build's process tree sampled every second (`_tmp/modconv/mbuild.py`).
"Before" is master 7d1169fc (machine load ~10); "after" the branch with the demotions (load ~50
during (b): the same 632 modules took 2,564 module-s before and 3,480 after, so compare the
module counts and module-s of (a)/(c), not (b)'s wall time).

| edit | before | after |
|---|---|---|
| (a) proof only: one line in `ctl_ref`'s proof, `Arena/IndT/Sum4` | 24 modules, 79 module-s, 61 s | 2, 15 module-s, 17 s |
| (a′) proof only, deeper: `decHL_grow`, `Arena/IndInstallSpec/DomsW` | 430, 1,031 module-s, 305 s | 2, 3 module-s, 6 s |
| (b) L function: `whnf_walk_fuel`'s `d + 1024` → `1024 + d` (`Arena/IndPos`), then `asm_file.py` and the build | 697 + ProgI chain, 2,751 module-s, 132 + 734 s | 632 + ProgI chain, 3,480 module-s (load 50), 92 + 952 s |
| (c) vendored twin, proof only: `NStore.persCount_le`, `ConRon/Arena/WFProofs` | 937, 5,636 module-s, 1,505 s | 2, 40 module-s, 42 s |

The two modules "after" are the edited one and `Audit/Final` (classic, so it rebuilds whenever
anything below it does: 1 s). Peak RSS: 13.9 / 13.5 / 17.8 / 17.7 GB before, 3.3 / 3.5 / 10.0 /
2.7 GB after. Before demoting (all imports `public`), (a), (a′), (c) were the same 2 modules and
(b) 686 (+ the chain).

**(b) does not shrink**: 614 modules have `IndPos` in their public closure. An L function's spec
states `p.lookup "f" = some fL`, so it imports the function's module publicly, and every module
whose statements mention that spec's models imports the spec publicly, and so on up: the
statement-level dependencies of the refinement proofs reach almost everything above the code.
A model of the rule (the public-closure rule of §1 on the current headers) predicts 650 for this
edit; the build rebuilt 632.

**Cold build** (fresh worktree, `LAKE_COLD=1`, 4 jobs): before 2,103 modules, 6,247 module-s,
1,664 s, peak 17.2 GB; after: see §3.1.

### 3.1 Cold build after

(filled in below)

## 4. Statement changes

A changed statement or exposed definition rebuilds the modules that reach it through public
imports (§1). Over all 1,380 modules, the rebuild sets sum to 352,681 with every import public and
to 242,724 after the demotions (−31 %). Examples (modules rebuilt by a statement change):
`IndInstallSpec/DomsW` 430 → 71, `IndPosSpec/DepthGo` 271 → 94, `L/ModelGen` 990 → 209,
`Compiler/Compile` 863 → 358, `DerRel` 1,047 → 684; `MemoLib`, `ExprMk`, `CoreRefine` unchanged
(~1,100: the code itself). A helper lemma that no other file uses can be `private`: adding one
changes no public `.olean` (checked on the toy).

## 5. Left for later: L changes

To cut off L changes, an L function's body must not be in its module's public `.olean`: the
`FunDecl`s outside `@[expose]`, and every module that unfolds one (`simp only [callFn, fooL]` in
its spec, the `l_model` equations, the whole-program checks that evaluate the program in the
kernel) `import all` of the function's module. An L change would then rebuild the function's
module, those `import all`-ers (its specs, the generated `Checker/Prog*` chain) and nothing above
them, which is lnext3.md's ~120. The models `l_model` generates from the L text are definitions
too: if they stay exposed, an L change that changes a model still propagates through the public
closure; they would need the same treatment. Unknown: how many proof modules unfold a function
of another file (the `import all` count), and the whole-program chain's `import all` of all 136
code modules (it then also rebuilds on proof edits there).

## 6. Process notes

* The header fixers ran in a loop (build, parse the errors, fix, commit): 9 full builds before
  the demotions, 7 after, 15 to 30 minutes each at 4 jobs while most of the tree rebuilt.
* `lean --run` on a module needs `meta import` of what `main` runs; compiled executables (`lake
  exe romgen`, `census`, …) are unaffected.
