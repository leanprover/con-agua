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
- Known vcgen gaps: no `eq_def` fallback; `ite` equations are ignored; an over-applied `ite` doesn't split; specs
  aren't found through projections; precondition-only arguments stay metavariables; pattern lambdas from another
  module don't match; equation generation fails for structural recursion that matches under a bind. Kraken's
  `Program.wp` is new. Record each gap you find as a minimal standalone reproducer in `docs/gaps/` (plain Lean,
  with an expected/observed header).

## Process rules
- Worktrees and large files go in `_tmp/` (tmpfs and a memory cap). Use `git -C <dir>` and stage by explicit
  path. Copying a built `.lake` into a fresh worktree avoids a rebuild. Remove your worktree when done.
- Every checker run gets a `timeout`. Never use `ulimit -v`. Never wait on or kill processes by name pattern.
- Never push. Commits end with `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`.
- This is the full project now, built top-down: `sorry` on master is fine (e.g. stubs for callees not yet
  proved), but list each one in DESIGN.md. No new axioms, no dead code, and no reference copies of old code
  proved equal to new.
- **Speed over ceremony.** Green field: an occasionally broken master is acceptable if it is noticed and fixed
  quickly. Before merging, build the targets you touched and their direct dependents, not everything.
- **Velocity log.** Every lane, at every landing, appends one line to `docs/velocity.csv`:
  `date,lane,model,work_min,overhead_min,note`. `work_min` is time spent on the actual task (design, code,
  proofs). `overhead_min` is the merge red tape: merging master, waiting on builds, re-running tests, fixing
  merge fallout, cleanup. Measure with `date` timestamps, not guesses. The note says what landed.
- Parallel lanes each own explicit files. Before adding a lemma, grep for an existing one. A lane that started
  before others landed merges `master` into itself before landing.
- Write in DESIGN.md (a journal: decisions, measurements, findings). Never use "load-bearing" or "licenses" in
  prose.
