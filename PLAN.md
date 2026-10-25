# con-agua: a Lean checker in x64 with an end-to-end proof

## Goal and proof chain

```
machine code (x64)     ⊑  L (deep syntax)            verified compiler, proved once, against Kraken's x64 semantics
L                      ⊑  con-ron's arena model      per function: data refinement, by vcgen + grind
con-ron arena model    ⊑  con-leche's pure checker   con-ron's Theorem 1 (exists)
pure checker accepts   ⇒  consistency                con-leche (exists)
```
Plus an input statement: "the byte buffer holds this stream", connected to con-leche's frontend proofs.

`OVERVIEW.md` describes the result (L, the verified compiler, the final theorem, the trusted base);
`docs/ROADMAP.md` lists parked work and the known capacity limits. Two rules from the start still hold:
**resource exhaustion never reads as accept**, and **no per-function separation logic** (the one memory
fact is that the regions are disjoint and in bounds, proved once in the compiler).

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
- **No `sym only […] => vcgen … <;> finish` on a function with many paths** (an `if t == k { … }`
  dispatch, a run of loads and calls). After `sym` every goal keeps the locals as `setLoc`/`setLocs`
  chains and `finish` crawls through them; the cost grows with each arm (DeclCanonExpr: 1 s for the
  first arm, 58 s for the last, 442 s in all). Use a plain `vcgen [exec, step, …, callee specs]`, then
  `all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
  List.headD_cons, List.headD_nil, List.tail_cons, List.tail_nil, Locals.init_nil,
  Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval, Nat.reduceEqDiff, reduceIte,
  beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at *)`, then `all_goals grind [lang_grind,
  arena_grind, …, model defs]` (26 s). Often faster still, and without
  `grind`: `vcgen [exec, step, L.evalE_spec, evalC, evalArgs, setLoc, setLocs, …]` (loads come out
  as `rd64`, with no bound proofs inside terms) and `all_goals simp_all [LocEq, Expr.pval, ipf_rd64,
  BinOp.eval, Cmp.eval, St.setLoc*, Locals.init_cons_*, Sig.retVal, Sig.retOr, model def, its
  `*_some` continuation lemmas]` (RecGenSpec16 241 s -> 11 s, IndInstallSpec28 209 s -> 6 s).
  Before writing a spec of an L function, grep for an existing one (ProjFnShapeRef re-proved
  IndRealIpf's, 290 s). A lookup `bigProg.lookup "f" = …` by `rfl` compares `String`s with every
  name before it, in the elaborator and the kernel: use positions (`chk_lk`/`prog_bundle`,
  `LoopProgTac.lean`; `front_agree`, `FrontProgAgree.lean`).
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
  The `sorry` columns (and `sorry`/`lean_sorry` in the CSV) count every target depending on `sorryAx`;
  of these, **proven locally** (`local`, CSV `local`/`lean_local`, appended at the end of the row) are those
  whose own proof term (and generated `proof_N`/`match_N`/`eq_N` auxiliaries) has no `sorryAx`: it comes
  only through other constants. The report lists the nearest such constants ("sorry sources", by number
  of targets blocked) as a work queue. Locally proven targets still cover none of their callees.
- **Not needed (`n/a`).** A target the L checker deliberately never implements (a deliberate deviation, error
  text, an unused mode, a pure-proof helper) is listed with its reason and deviation id in
  `docs/not-needed.md`, a reviewed table `census.py` reads; it fails if a listed target does not exist or has
  an L function or refinement of its own. n/a targets have their own column and are left out of the
  denominator of every share (proven / locally / L written), so 100% is reachable. Strict: a target that
  is merely covered once its callers are proven stays `todo` and shows in the informational "pending"
  column. CSV: new columns `na, lean_na, rust_na, pending, lean_pending` at the end; `lean_all` stays the
  total, the shares use `lean_all - lean_na` (older rows have no n/a). Add a row to
  `docs/not-needed.md` in the commit that makes the decision; when L later gets code for it, delete the row.
- **Who runs it.** Anyone may run `scripts/census.py` to check the numbers; it is not run routinely any more
  (the end-to-end theorem is sorry-free). `--write` puts its report under `_tmp/census/`.

## Build statistics (file size, elaboration time)
- `scripts/buildstats.py` measures lines per `.lean` file under `ConAgua/`, elaboration seconds per module, and
  every elaboration step above 1 s (Lean profiler, with `file:line`), in its own worktree
  `_tmp/wt/buildstats-run` built without the shared Lake cache, niced, on 16 cores, killed above 20 GB (PSS).
  Default is incremental (only modules changed since the last run are re-measured); `--full` re-measures
  everything (~20 CPU-minutes); `--lines-only` needs no build; `--write` regenerates `_tmp/buildstats/buildstats.md`
  and appends to `_tmp/buildstats/buildstats.csv` (measurements live in `_tmp/buildstats/buildstats.json`). Thresholds are
  constants at the top of the script.
- **Who runs it.** Only the coordinator, a few times a day in the background, on master. Files on the
  watch list (over 1500 lines or 60 s) get split by a lane; a split keeps statements and names stable.
  Declarations on it (a step over 20 s) are investigated by a separate lane off the critical path.
  **No lane adds time gates to merging**; this report is advisory.

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
  work should become a top-level lane, so the coordinator can see it. Name helper worktrees
  `<lane>-<suffix>`.
- **Commit work in progress often.** Commit to your own branch at least every ~30 minutes and before every long build, even if it doesn't build yet (WIP commits are fine; squash nothing). Machine restarts and rate limits have lost uncommitted work twice. Landing on master can stay less frequent, but keep landings small: one function family or one fix per landing.
- **Worktrees and disk:** every worktree carries a ~2.5 GB `.lake` build. A lane keeps at most one worktree of its own plus one per running helper; remove a helper's worktree (`git worktree remove`; the branch may stay) as soon as the helper has landed or stopped, and scratch/base worktrees as soon as their measurement is done. The project must stay well under 60 GB (the disk is shared).
- **Waiting on background work:** wait on the job you started (run the job itself with `run_in_background`, or `wait $PID`, or a sentinel/output file it writes at the end). Never wait with `until ! pgrep -f "<pattern>"`: the waiting shell's own command line contains the pattern, so it never ends (and other lanes run the same scripts). Lane tierarr idled 2 h this way (2026-10-24).
- **Memory hygiene for new modules:** first elaborate a new or heavily changed module alone (`lake env lean F.lean`) under an RSS guard of ~6 GB, then `lake build`. Never pass `by decide +kernel` (or `decide` on string/list lookups) inline as an argument over program-sized data: state it as its own small lemma (`simp only [defs]; decide`) or use per-function lookups (ProgHas, prog_wf). Past offenders: whole-program Prog.wf (19 GB), CoreErec (20 GB), LoopCore (16 GB), StageInst1 (17 GB, inline `∀ b ∈ instA, b < 64`). Also: many chained `(c + k).toNat = c.toNat + k` hypotheses in context make every later `omega` exponential (CIReadRefCaps, >15 GB): rewrite with them and `clear` them before `omega` (see its `comega` macro), or keep one `∀` fact.
- **e2e in a worktree:** run `scripts/e2e.py --latest ''` (or `--no-perf`), so a branch run does not overwrite the shared baseline `_tmp/e2e/latest/results.json` (only the census watcher refreshes it, from master).
- **Emergency fixes: when the coordinator says a fix landed (e.g. a memory hog, like erecfix: IndCore/CoreErec from ~22 GB to ~3 GB), merge master before your next build.** Otherwise merging only before landing is fine. A coordinator watchdog (`_tmp/memwatch.sh`) kills any single `lean` process above 16 GB.
- **Landing is sequential: always land with `scripts/land.sh <branch> [targets]`.** Before calling it, merge master into your branch and build `ConAgua` in your worktree (a branch that is behind master is still landed if it merges cleanly; the build under the lock then decides, so merging master first just keeps the lock short): the build under the lock is then a cache hit. It takes a lock, so only one lane merges into master at a time; it merges, builds the given targets, and on conflict or build failure resets master and exits non-zero (then merge master into your branch in your worktree and retry). Never run `git merge` in the main checkout by hand, and never edit files there. `docs/velocity.csv` uses git's union merge driver (`.gitattributes`), so appended lines never conflict: just append your line, don't reorder or rewrite the file.
- **Program well-formedness:** prove every `Prog.wf … = true` with `L.Compiler.Prog.wf_of_wfFast` (Compiler/WFFast.lean), never with `decide +kernel` on `Prog.wf` directly: on a large program the slow check takes tens of GB of memory.
- **The committed assembler file `checker.s`** (lane asmfile, docs/design/asmfile.md): the final theorems are about this file as the trusted parser reads it (`include_asm`, `ConAguaAsm/Checker.lean`), and `checkerFile_eq` checks it against the compiler's output. After changing L code of the checker (and `scripts/checker_prog.py`), the compiler or the entry stub: build, run `python3 scripts/asm_file.py` (4 s) and commit `checker.s` with the change. A stale file fails the build at `checkerFile_eq` (naming the first differing function), so `land.sh` rejects it; `asm_file.py --check` also reports it without rewriting the file (`land.sh` does not run it). A merge conflict in `checker.s` is resolved by regenerating it, never by hand. `asm_file.py` also writes (and `--check` compares) `pins.bin`, the pin data `main.c` embeds (`romgen pins.bin 3`); regenerate it after a change to the startup data or a twin bump. The binary itself is `make` (`Makefile`: `main.c` + `checker.s` + `pins.bin`, plain `cc`, no Lean).
- **Globals and records (lane lfeat).** New L code uses named globals (not new `CTL` slots) for counters, tops, flags and epochs, and record syntax `R[i].f` for struct-of-arrays fields. Existing code migrates only opportunistically: when a lane touches `StoreLib`/`MemoLib` anyway, let the schema's count/stamp slot be a global as well as a `CTL` index, then move tables/memos one at a time. The cross-cutting slots (`CTL[0]` pool top, `CTL[1]` scratch flag, `CTL[62]` scratch epoch, `CTL[136]` spine top) stay as they are.
- **Design journal: one file per lane.** Write your decisions, measurements and findings to `docs/design/<lane>.md` (the coordinator creates it before you branch); never edit other lanes' journal files, and do not extend the top-level `DESIGN.md` (frozen history). Shared tables (`docs/deviations.md`, the memory map) are edited only for your own rows.
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

## Documents
- **`README.md` is the maintainer's**, human-written. An agent may turn an existing code name into a
  link and repoint a link that rotted; no other character of it changes. Anything it should say
  differently is reported, not written.
- **`OVERVIEW.md` and `README.md` state current facts**: no task numbers, no lane names, no history,
  no "now"/"since". History belongs in DESIGN.md and the lane journals (`docs/design/`). OVERVIEW.md
  does not mention the progress gist or other coordinator infrastructure.
- **User-facing files** (OVERVIEW.md, README.md, `main.c`'s usage text, the Makefile) **never refer
  to PLAN.md, DESIGN.md, the lane journals (`docs/design/*`) or lane names**, neither in prose nor in
  links. State the fact itself, link code, tests or committed data instead, and put measurements in
  the document itself (with date, revision and conditions). `docs/deviations.md` may be linked: it
  is a reference list, not a plan or journal.
- **Every nontrivial claim is linked to the exact lines** that back it:
  `https://github.com/leanprover/con-agua/blob/master/<path>#L<a>-L<b>` (the prefix is `BASE` at the
  top of `scripts/overview-links.sh`; change it there and in the documents together). Files without
  a line range are relative links (`[docs/deviations.md](docs/deviations.md)`). Numbers come from a
  measurement or the code, never from memory.
- **The link gate** `scripts/overview-links.sh` (no build, milliseconds; `scripts/land.sh` runs it
  after merging) copies every line-anchored link's lines into `scripts/overview-links-expected.txt`
  and fails when they move or change. When it fails on your landing: merge master, re-read each
  paragraph that cites a changed range, fix the anchor (moved) or the prose (changed), run
  `scripts/overview-links.sh --update`, and commit the expectation with your change. Never update
  the expectation without reading the paragraphs.
- Spots marked `<!-- update after <lane> -->` in OVERVIEW.md describe code a running lane is about to
  change; that lane (or the coordinator) refreshes them when it lands.
