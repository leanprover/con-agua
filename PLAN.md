# con-agua: a Lean checker in x64 with an end-to-end proof

## Goal and proof chain

```
machine code (x64)     ⊑  L (deep syntax)            verified compiler, proved once, against Kraken's x64 semantics
L                      ⊑  con-ron's arena model      per function: data refinement, by vcgen + grind
con-ron arena model    ⊑  con-leche's pure checker   con-ron's Theorem 1 (exists)
pure checker accepts   ⇒  consistency                con-leche (exists)
```
Plus an input statement: "the byte buffer holds this stream", connected to con-leche's frontend proofs.

L is a small purpose-built language. Its semantics is a Lean denotation into a `StateT Mem (Except Err)`-style
monad with fuel, friendly to `vcgen`. It has words, integers, a fixed set of growable word arrays in disjoint
regions, loops, calls and structured control flow. It has no pointers, no closures, and no allocation beyond
growing the arrays. con-ron's Rust is translated into L by hand (agents); the refinement proof catches mistakes.
The compiler is *verified*, not certifying: it is naive and non-optimising, and its correctness is a forward
simulation against Kraken's x64 semantics.

Data refinement (later milestones): `Vec<u64>` limbs become slices of a limb pool; `Vec` fields become slices of
per-type pools; hash tables become open addressing over fixed arrays; names become string-pool indices. The only
memory fact should be "these N regions are disjoint and in bounds", proved once in the compiler. Avoid
per-function separation logic.

## Things to settle early
- **Recursion and the stack.** The checker recurses millions deep (con-leche's e2e fixture `stack_fuel_offset`
  needs about 3M levels). L needs either calls with a caller-provided stack region and a defined
  "resources exhausted" error, or explicit work stacks. **Exhaustion must never read as accept.**
- **Totality.** Use fuel, as con-leche does.
- **Toolchain.** One build. We use Kraken's nightly (nightly-2026-09-21 or newer). We vendor con-ron (and with it
  con-leche), or just the modules we need, and make them build on that nightly. `withPtrEq` may need vendoring,
  because upstream removed it.
- **Performance.** Measure with `perf stat -e instructions:u`, one run. Wall time is not a measurement on this
  shared machine.
- **Trusted base at the end:** Kraken's x64 semantics (fuzzed against hardware), the assembler and loader, the
  calling harness, and the buffer-to-stream statement.

## Milestones
1. **Spike (Stage A).** Define L: syntax, denotation, and a compiler for a subset (words, arrays, loops, calls).
   Translate con-ron's `skip_braced` and `str_close` (`frontend/scan_fast.rs`) into L. Prove they refine
   con-leche's `skipBraced` and `strClose` (`ConLeche/Frontend/Scan/Fast.lean`). Spike the compiler simulation
   against Kraken. Measure: L lines per Rust line, proof effort per function, compiler-proof size, and run time
   against con-ron. See `docs/survey.md`.
2. **Stage B.** Validate NDJSON line by line, without storing anything.
3. A limb-pool `Nat.add`/`mul` (con-ron `ron/nat.rs`, `proof/ConRon/Refine/Nat.lean`).
4. One store walk with a hash lookup (`ron/hashmap2.rs`, `Refine/HashMap2*.lean`, `proof/ConRon/Arena/Store.lean`).

## Proof-style lessons (from con-leche task #356; see con-leche CLAUDE.md "The cached simulation proofs")
- Triples are `Std.WP` (`⦃P⦄ x ⦃Q; E⦄`), not `Std.Do`. `vcgen` reads only `Std.WP`; outside con-leche it needs
  `set_option experimental.vcgen true`.
- Proofs take the form `sym only [<own grind attr>, …] => vcgen [f, callee specs and IHs as terms] <;> finish`,
  one per arm or induction case. No custom tactics. Declare the attribute with `register_grind_attr`; in a
  `module` file this needs `public meta import Lean.Meta.Tactic.Grind.Attr`.
- Facts are equations about NAMED functions. Postconditions contain no `∃`, no disjunction and no `fun`. The pure
  side's nested `match` must not reach grind: give one guarded equation per reachable arm. Name the blocks between
  arms, name every `fun`, and name every mode gate.
- Loop IHs and memo bodies go in as named predicates, not as `∀`-triples in the context.
- State callee-spec posts over the program's own arguments. Leave out the initial-state hypothesis. Pin implicits.
- Pass a recursive function to `vcgen` as `f.eq_def`. Keep the case splits that make IHs apply. Prove recursive
  triples by `induction`, not by recursive pattern matching.
- A raised `finish (gen := N)` sets depth, not search; comment it. Failing runs cost far more than passing ones.
- Concrete checks by `decide +kernel` never compare `String`s in bulk: each comparison unfolds to UTF-8
  byte lists, and `List.Nodup`'s instance is slow even on `Nat`s. Program well-formedness goes through
  `Prog.wf_of_wfFast (by decide +kernel)` (names as `Nat` codes in a search tree; DESIGN.md, "Slow
  declarations").
- Every variable of a `grind_pattern` is bound by a term specific to the goal. A multi-pattern with a
  generic piece (`pv P o l`, `R * S`) instantiates once per matching term and splits on each instance's
  hypotheses (600 instances, 52 s in `natShr_spec`); state the lemma in the shape of the callee's post.
- Do not `simp` the condition of a `dite` whose branches hold proofs that use the hypothesis (a
  `Char`'s validity, a `Fin` bound): the casts it leaves cost the kernel seconds. Step through it with
  `dite_eq_left`/`dite_eq_right` and an `iff` for the condition.
- A long `&&`/`||` chain in an `if` costs `vcgen` one path per exit, and consecutive chains multiply.
  Pass `L.evalC_spec`/`L.evalE_spec` (`L/PureEval.lean`) instead of `evalC`/`evalE`, then
  `simp only [Cond.pval, Expr.pval, …] at *` before `grind`.
- Known vcgen gaps: no `eq_def` fallback; `ite` equations are ignored; an over-applied `ite` doesn't split; specs
  aren't found through projections; precondition-only arguments stay metavariables; pattern lambdas from another
  module don't match; equation generation fails for structural recursion that matches under a bind. Kraken's
  `Program.wp` is new. Record each gap you find as a minimal standalone reproducer in `docs/gaps/` (plain Lean,
  with an expected/observed header).

## Progress census
- **Links.** Tag L code and proofs with the twin function they stand for (`import ConAgua.Census.Attr`; names
  fully qualified, e.g. `ConRon.Arena.bvarBoundMemo`, `ConLeche.Frontend.skipWs`):
  `@[l_impl T]` on the L `FunDecl`; `@[refines T]` on the theorem that proves the L code refines the whole of
  `T` (if the proof is a chain, L ⊑ model and model = `T`, tag every link); `@[refines_part T "label"]` when it
  covers only part of `T` (one arm, the validity half of a scanner, or L code that aborts on cases the twin
  handles, such as `frontRun` on declaration lines). Use `@[refines]` only when the L code aborts nowhere the
  twin does not throw (capacities and the L fuel aside). Arms that together make up a dispatcher are listed in
  `COMPLETE_BY_PARTS` in `scripts/census.py`. Tag in the same commit that lands the code.
- **Census.** `scripts/census.py` builds what it needs (`--no-build` to skip) and prints, per roadmap phase,
  how many targets are proven / proven with `sorry` / have L code / have nothing, by count and weighted by
  Lean and Rust lines (~30 s). `--list [REGEX]` lists targets with their status and links. The exe runs under a memory guard
  (killed above 6 GB; it peaks at about 2.8 GB). Targets: the
  `ConRon`/`ConLeche` definitions `ConAgua.Final.TwinAccepts` reaches (no instances, auxiliaries, types,
  predicates, ROM data). Proven means every `@[refines T]` theorem uses only `propext`, `Classical.choice`,
  `Quot.sound`; a target reached only through proven targets counts as proven (only sorry-free ones
  cover: a refinement proved modulo `sorry` counts as `sorry` itself and covers none of its callees).
- **Who runs it.** Lanes add links and may run the census to check their own numbers; only the coordinator
  runs `scripts/census.py --write` (regenerates `docs/progress.md`, appends a line to `docs/progress.csv`),
  on master after each batch of landings, so the time series has one line per master state and lanes never
  conflict on these files.

## Build statistics (file size, elaboration time)
- `scripts/buildstats.py` measures lines per `.lean` file under `ConAgua/`, elaboration seconds per module, and
  every elaboration step above 1 s (Lean profiler, with `file:line`), in its own worktree
  `_tmp/wt/buildstats-run` built without the shared Lake cache, niced, on 16 cores, killed above 20 GB (PSS).
  Default is incremental (only modules changed since the last run are re-measured); `--full` re-measures
  everything (~20 CPU-minutes); `--lines-only` needs no build; `--write` regenerates `docs/buildstats.md`
  and appends to `docs/buildstats.csv` (measurements live in `docs/buildstats.json`). Thresholds are
  constants at the top of the script.
- **Who runs it.** Only the coordinator, a few times a day in the background, on master. Files on the
  watch list (over 1500 lines or 60 s) get split by a lane; a split keeps statements and names stable.
  Declarations on it (a step over 20 s) are investigated by a separate lane off the critical path.
  **No lane adds time gates to merging**; this report is advisory.
- **It is also the safety net under the shared Lake cache** (DESIGN.md, "Cache incident"): each run records
  its verdict on master in `_tmp/buildcheck.json`, and `census.py` and `gist_report.py` print "last cache-free
  build of master: <commit>, OK/FAILED". A FAILED there means some cached build accepted code that does not
  build: stop landing, find the module, purge the cache (`rm -rf _tmp/lake-cache-v2`, then reseed it from a cache-free build). Run it (at least
  incrementally) after every few landings; `--full` once a day.

## Bumping the twin (con-ron, and the con-leche it pins)
- **State.** `vendor/UPSTREAM` names the two vendored revisions; `vendor/` is exactly those upstream
  files plus the patch series `vendor/patches/{con-leche,con-ron}/NNNN-*.patch`, applied in order
  (`scripts/bump-con-ron.sh --check`). Never edit a vendored file without putting the edit in a
  patch: edit, then `scripts/bump-con-ron.sh --refresh-patches` (an edit outside every patch lands in
  `NNNN-new.patch`: rename it and give it a description), and commit both.
- **Citations** (DESIGN.md, "Provenance: citations instead of fingerprints"). Every L `FunDecl` carries
  a line in its declaration block naming the twin code it stands for, at the upstream revision in
  `vendor/UPSTREAM`: `/-- con-ron: ConRon/Arena/Core.lean:3682-3688 ConRon.Arena.flushCaches -/` (path
  relative to con-ron's `proof/`, the block's line range, the qualified name; `con-leche:
  ConLeche/...` for code ported from con-leche; several lines for an L function that merges several
  twin functions; `con-ron: none — <reason>` for L plumbing with no twin). New code: write
  `@[l_impl T]`, run `scripts/provenance.py annotate` (inserts the citation of `T`), or `locate T`
  for the line. `scripts/provenance.py check` (a second, no build) must pass before landing.
- **The bump.** In a worktree on its own branch: `scripts/bump-con-ron.sh <rev>` (e.g. `origin/HEAD`)
  re-vendors con-ron at `<rev>` and con-leche at the rev con-ron's `proof/lake-manifest.json` pins,
  re-applies the patches with `git apply --3way` (conflicts are reported and left with markers),
  regenerates `scripts/census-rust.tsv`, runs `scripts/provenance.py update --old <old rev>`
  (relocates moved citations, inserts a `-- con-ron: CHANGED since …` marker under every citation
  whose twin code, or a helper right below it, changed, and prints the diffs), builds, runs the
  census, and lists the changed upstream files. Fix what the build breaks (vendored files: in a
  patch; our files: small fixes now, otherwise `sorry` + DESIGN.md), land it with the markers, and
  announce it in DESIGN.md: what changed upstream, the marked items, which lanes own them. The
  owning lane checks (and if needed fixes) the L code and proofs against the new twin and deletes
  the marker; `check` lists the markers left (the queue; `check --strict` fails on them).
  Never bump the toolchain and the twin in the same step.

## Process rules
- Worktrees and large files go in `_tmp/` (tmpfs and a memory cap). Use `git -C <dir>` and stage by explicit
  path. Create a worktree with `scripts/new-worktree.sh <path-under-_tmp/wt> [<rev>]`: it symlinks `_tmp`
  and `.lake/packages` in from the main tree, so the worktree shares the Kraken checkout and the project-wide
  Lake artifact cache (DESIGN.md, "The shared Lake artifact cache"). **Build with `scripts/lake build …`, never
  plain `lake`**: the wrapper points `LAKE_CACHE_DIR` at the shared cache; plain `lake` falls back to the
  toolchain's own cache directory, a different mount in the sandbox that copies instead of hard-linking. Start
  a fresh worktree with no `.lake/build` and let the cache restore it (seconds, ~0 bytes of disk) — do not copy
  a built `.lake/build` in by hand, that was last resort before the cache existed. The wrapper also WRITES every build to the cache (default since 2026-10-22), so each module elaborates once for the whole project; no separate reseeding step is needed. **Do not edit, check out, merge or regenerate `.lean` files in a worktree while a build runs in it** (DESIGN.md, "Cache incident"): Lake hashes a source when the build starts and compiles it later, so the result can be an olean of a different text. The wrapper detects it, publishes nothing, deletes the affected modules' build state and exits non-zero (3 if Lake itself succeeded) — then just rerun. It also serialises builds within one worktree. To keep a build out of the cache use `LAKE_ARTIFACT_CACHE=false scripts/lake`, not plain `lake`. Remove your worktree when done.
- Every checker run gets a `timeout`. Never use `ulimit -v`. Never wait on or kill processes by name pattern.
- Never push. Commits end with `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`.
- This is the full project now, built top-down: `sorry` on master is fine (e.g. stubs for callees not yet
  proved), but list each one in DESIGN.md. No new axioms, no dead code, and no reference copies of old code
  proved equal to new.
- **Speed over ceremony.** Green field: an occasionally broken master is acceptable if it is noticed and fixed
  quickly. Before merging, build the targets you touched and their direct dependents, not everything.
- **Fan-out.** A lane may hand sub-tasks to helper agents when the split is clean, for example proving theorems
  whose statements are already fixed. Keep it shallow: at most about 3 helpers at a time. Larger independent
  work should become a top-level lane, so the coordinator and the dashboard can see it. Name helper worktrees
  `<lane>-<suffix>`.
- **Commit work in progress often.** Commit to your own branch at least every ~30 minutes and before every long build, even if it doesn't build yet (WIP commits are fine; squash nothing). Machine restarts and rate limits have lost uncommitted work twice. Landing on master can stay less frequent, but keep landings small: one function family or one fix per landing.
- **Landing is sequential: always land with `scripts/land.sh <branch> [targets]`.** It takes a lock, so only one lane merges into master at a time; it merges, builds the given targets, and on conflict or build failure resets master and exits non-zero (then merge master into your branch in your worktree and retry). Never run `git merge` in the main checkout by hand, and never edit files there. `docs/velocity.csv` uses git's union merge driver (`.gitattributes`), so appended lines never conflict: just append your line, don't reorder or rewrite the file.
- **Program well-formedness:** prove every `Prog.wf … = true` with `L.Compiler.Prog.wf_of_wfFast` (Compiler/WFFast.lean), never with `decide +kernel` on `Prog.wf` directly: on a large program the slow check takes tens of GB of memory.
- **Globals and records (lane lfeat).** New L code uses named globals (not new `CTL` slots) for counters, tops, flags and epochs, and record syntax `R[i].f` for struct-of-arrays fields. Existing code migrates only opportunistically: when a lane touches `StoreLib`/`MemoLib` anyway, let the schema's count/stamp slot be a global as well as a `CTL` index, then move tables/memos one at a time. The cross-cutting slots (`CTL[0]` pool top, `CTL[1]` scratch flag, `CTL[62]` scratch epoch, `CTL[136]` spine top) stay as they are.
- **Velocity log.** Every lane, at every landing, appends one line to `docs/velocity.csv`:
  `date,lane,model,work_min,overhead_min,note`. `work_min` is time spent on the actual task (design, code,
  proofs). `overhead_min` is the merge red tape: merging master, waiting on builds, re-running tests, fixing
  merge fallout, cleanup. Measure with `date` timestamps, not guesses. The note says what landed.
- Parallel lanes each own explicit files. Before adding a lemma, grep for an existing one. A lane that started
  before others landed merges `master` into itself before landing.
- **Deviations from the twin.** L is a close twin of con-ron. Any place where L does something else
  than its twin (aborts where the twin continues, other than fuel and fixed capacities; a
  simplified algorithm; a missing arm; an unmirrored cache; a "for now") gets a row in
  `docs/deviations.md`, under `## Temporary` (we intend to fix it) or `## Deliberate` (by design,
  stays; say why) (where, what the twin does, what L does, effect, owner, proposed fix) in the
  commit that introduces it, and when a Temporary row is fixed it moves to `## Fixed` as a one-line bullet. The
  coordinator reviews the list at each batch of landings and assigns the open rows.
- Write in DESIGN.md (a journal: decisions, measurements, findings). Never use "load-bearing" or "licenses" in
  prose.
